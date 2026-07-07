"""
Читає нові повідомлення з переліку Telegram-каналів, розпізнає тип загрози
та населений пункт, геокодує його і додає подію у events.json.

Запускається за розкладом (cron) через GitHub Actions.
Стан (останній прочитаний message_id по кожному каналу) зберігається
у state.json, кеш геокодування — у geocode_cache.json. Обидва файли
коммітяться назад у репозиторій після кожного запуску.

Змінні середовища (беруться з GitHub Secrets):
  TG_API_ID, TG_API_HASH, TG_SESSION
"""

import os
import re
import io
import json
import time
import asyncio
from datetime import datetime, timedelta, timezone

import requests
from PIL import Image
import pytesseract
from telethon.sync import TelegramClient
from telethon.sessions import StringSession

CHANNELS = [
    "locatorru",
    "radarrussiia",
    "LPRalarm",
    "kupolrussia",
    "vrv_radar",
]

STATE_FILE = "state.json"
EVENTS_FILE = "events.json"
GEOCODE_CACHE_FILE = "geocode_cache.json"
REGION_STATUS_FILE = "region_status.json"
MAX_EVENTS_KEPT = 2000
MESSAGES_PER_CHANNEL_PER_RUN = 200

# Скільки МАКСИМУМ тримаємо підсвітку регіону активною, якщо так і не
# прийшов явний "отбой" від каналу. Це підстраховка на випадок, коли канал
# просто перестав писати про цей регіон, а не тому що загроза минула.
# Головний тригер зняття підсвітки — повідомлення типу "all_clear" (відбій).
REGION_BACKSTOP_HOURS = 4

# --- ключові слова для визначення типу загрози ---
# ПРИМІТКА: це стартовий, приблизний набір. Реальний формат повідомлень
# у кожному каналі може відрізнятись — після перших запусків краще
# звірити результати з оригінальними постами і скоригувати список.
TYPE_KEYWORDS = [
    ("missile", ["ракет", "баллистич", "калибр", "искандер", "х-101", "х-22", "х-59", "фламинго", "крылат"]),
    ("drone", ["бпла", "дрон", "шахед", "shahed", "герань"]),
    ("aviation", ["авиац", "ил-76", "миг-31", "миг-29", "су-34", "су-35", "взлет", "взлёт"]),
    ("shelling", ["обстрел", "артобстрел", "минометн"]),
    ("all_clear", ["отбой", "угроза миновала"]),
    ("alert", ["тревога", "угроза атаки", "опасност"]),
]

# Регіон (область/край/республіка) — зазвичай йде ПІСЛЯ переліку районів/міст,
# а вже після нього — опис події ("Фиксация БПЛА", "- ракетная опасность...")
REGION_PATTERN = re.compile(
    r"((?:[А-ЯЁ][а-яё\-]+\s+)?(?:область|край|автономный округ)|Республика\s+[А-ЯЁа-яё\-]+)"
)

# фрази-шум, які потрапляють у "хвіст" переліку локацій, але самі не є місцем
LOCATION_STOPWORDS = [
    "и близлежащие населенные пункты",
    "и близлежащие населённые пункты",
    "и далее в тыл",
    "и последующие",
]


def extract_location_candidates(text: str):
    region_match = REGION_PATTERN.search(text)
    loc_segment = text[: region_match.start()] if region_match else text
    region = region_match.group(0).strip() if region_match else None

    # 1) райони: "Ленинский район", "Тепло-Огаревский район" и т.д.
    # (можуть йти підряд без ком; дозволяємо великі літери всередині для
    # складених назв через дефіс типу "Тепло-Огаревский")
    districts = re.findall(r"([А-ЯЁ][а-яёА-ЯЁ\-]+)\s+район", loc_segment)

    # 2) прибираємо знайдені "Х район" з рядка, щоб не заважали розбору міст
    remainder = re.sub(r"[А-ЯЁ][а-яёА-ЯЁ\-]+\s+район", "", loc_segment)

    # 3) міста, перелічені через кому: "Зеленодольск, Казань, Елабуга, ..."
    cities = []
    for part in remainder.split(","):
        part = part.strip(" .")
        if not part:
            continue
        # прибираємо стоп-фразу з сегмента, а не весь сегмент, бо перед нею
        # часто стоїть остання назва міста в переліку ("Бугульма и близлежащие...")
        low = part.lower()
        for sw in LOCATION_STOPWORDS:
            idx = low.find(sw)
            if idx != -1:
                part = part[:idx].strip(" .")
                break
        if not part:
            continue
        m = re.search(r"([А-ЯЁ][а-яё\-]+(?:\s+[А-ЯЁ][а-яё\-]+)*)$", part)
        if m:
            candidate = m.group(1).strip()
            if len(candidate) > 2:
                cities.append(candidate)

    candidates = districts + cities
    seen, result = set(), []
    for c in candidates:
        if c not in seen:
            seen.add(c)
            result.append(c)
    return result, region


def update_region_status(region_status: dict, region: str, alert_type: str, text: str, channel: str, now):
    """Оновлює статус регіону для підсвітки на карті.

    Головне правило: коли приходить повідомлення типу "all_clear" (відбій,
    "угроза миновала") — підсвітка регіону ЗНІМАЄТЬСЯ одразу.
    В іншому разі — оновлюється активний тип загрози й причина (текст
    повідомлення), з підстраховкою по часу (REGION_BACKSTOP_HOURS) на
    випадок, якщо канал просто замовк, а не дав явний відбій.
    """
    if not region:
        return

    if alert_type == "all_clear":
        region_status.pop(region, None)
        return

    expires_at = now + timedelta(hours=REGION_BACKSTOP_HOURS)
    region_status[region] = {
        "type": alert_type,
        "text": text[:300],
        "channel": channel,
        "updated_at": now.isoformat(),
        "expires_at": expires_at.isoformat(),
    }


def prune_expired_regions(region_status: dict, now):
    expired = [
        r for r, s in region_status.items()
        if datetime.fromisoformat(s["expires_at"]) < now
    ]
    for r in expired:
        del region_status[r]
    low = text.lower()
    for label, keywords in TYPE_KEYWORDS:
        if any(kw in low for kw in keywords):
            return label
    return "unknown"


def ocr_image_bytes(data: bytes) -> str:
    try:
        img = Image.open(io.BytesIO(data))
        # 'rus' — мовний пакет tesseract, встановлюється окремо в CI
        text = pytesseract.image_to_string(img, lang="rus")
        return text.strip()
    except Exception as e:
        print(f"OCR error: {e}")
        return ""


def load_json(path, default):
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return default


def save_json(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def geocode(name: str, region: str, cache: dict):
    cache_key = f"{name}|{region or ''}"
    if cache_key in cache:
        return cache[cache_key]
    query = f"{name}, {region}, Russia" if region else f"{name}, Russia"
    try:
        # Nominatim (OpenStreetMap) — безкоштовний, але ліміт ~1 запит/сек
        resp = requests.get(
            "https://nominatim.openstreetmap.org/search",
            params={"q": query, "format": "json", "limit": 1},
            headers={"User-Agent": "nahr-map-clone/1.0"},
            timeout=10,
        )
        data = resp.json()
        time.sleep(1.1)  # поважаємо rate limit Nominatim
        if data:
            coords = [float(data[0]["lat"]), float(data[0]["lon"])]
            cache[cache_key] = coords
            return coords
    except Exception as e:
        print(f"Geocode error for '{query}': {e}")
    cache[cache_key] = None
    return None


def main():
    api_id = int(os.environ["TG_API_ID"])
    api_hash = os.environ["TG_API_HASH"]
    session = os.environ["TG_SESSION"]

    state = load_json(STATE_FILE, {})
    events = load_json(EVENTS_FILE, [])
    geocode_cache = load_json(GEOCODE_CACHE_FILE, {})
    region_status = load_json(REGION_STATUS_FILE, {})
    now = datetime.now(timezone.utc)

    with TelegramClient(StringSession(session), api_id, api_hash) as client:
        for channel in CHANNELS:
            last_id = state.get(channel, 0)
            print(f"Reading @{channel} since id={last_id}")
            try:
                messages = list(
                    client.iter_messages(
                        channel, min_id=last_id, limit=MESSAGES_PER_CHANNEL_PER_RUN
                    )
                )
            except Exception as e:
                print(f"Failed to read {channel}: {e}")
                continue

            if not messages:
                continue

            # найновіше id для наступного запуску
            state[channel] = max(m.id for m in messages)

            for m in reversed(messages):  # у хронологічному порядку
                text = (m.message or "").strip()

                # деякі канали (напр. kupolrussia) публікують текст ЯК КАРТИНКУ,
                # а не як звичайний текст повідомлення — тоді m.message порожній,
                # але є фото. Розпізнаємо текст через OCR (tesseract, мова 'rus').
                ocr_used = False
                if not text and m.photo:
                    try:
                        photo_bytes = client.download_media(m, file=bytes)
                        if photo_bytes:
                            text = ocr_image_bytes(photo_bytes)
                            ocr_used = True
                    except Exception as e:
                        print(f"Failed to download/OCR photo for {channel}/{m.id}: {e}")

                if not text.strip():
                    continue

                alert_type = detect_type(text)
                locations, region = extract_location_candidates(text)

                update_region_status(region_status, region, alert_type, text, channel, now)

                # для кожної знайденої локації створюємо ОКРЕМУ подію —
                # в повідомленнях часто перелічено кілька районів/міст одразу
                any_added = False
                for loc in locations:
                    coords = geocode(loc, region, geocode_cache)
                    if not coords:
                        continue
                    lat, lon = coords
                    events.append(
                        {
                            "id": f"{channel}_{m.id}_{loc}",
                            "channel": channel,
                            "date": m.date.astimezone(timezone.utc).isoformat(),
                            "text": text[:500],
                            "type": alert_type,
                            "location_name": loc,
                            "region": region,
                            "lat": lat,
                            "lon": lon,
                            "ocr": ocr_used,
                        }
                    )
                    any_added = True

                if not any_added:
                    # жодну локацію не вдалось геокодувати — все одно зберігаємо
                    # подію без координат, щоб текст не загубився
                    events.append(
                        {
                            "id": f"{channel}_{m.id}",
                            "channel": channel,
                            "date": m.date.astimezone(timezone.utc).isoformat(),
                            "text": text[:500],
                            "type": alert_type,
                            "location_name": None,
                            "region": region,
                            "lat": None,
                            "lon": None,
                            "ocr": ocr_used,
                        }
                    )

    # тримаємо тільки останні N подій, щоб JSON не розростався нескінченно
    events = events[-MAX_EVENTS_KEPT:]

    # знімаємо підсвітку з регіонів, де давно не було жодних новин
    # (підстраховка на випадок, якщо явного "відбою" так і не було)
    prune_expired_regions(region_status, now)

    save_json(STATE_FILE, state)
    save_json(EVENTS_FILE, events)
    save_json(GEOCODE_CACHE_FILE, geocode_cache)
    save_json(REGION_STATUS_FILE, region_status)
    print(f"Done. Total events stored: {len(events)}, active regions: {len(region_status)}")


if __name__ == "__main__":
    main()
