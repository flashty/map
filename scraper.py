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
import math
import asyncio
from datetime import datetime, timedelta, timezone

import requests
from PIL import Image, ImageOps
import pytesseract
from telethon.sync import TelegramClient
from telethon.sessions import StringSession

CHANNELS = [
    "locatorru",
    "radarrussiia",
    "LPRalarm",
    "vrv_radar",
    "kupolrussia",
    "radar_plus_bpla",
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
REGION_BACKSTOP_HOURS = 1

# --- побудова "маршрутів" руху БПЛА/ракет ---
# Канали не дають явного ID групи цілі, тому маршрут — це ЕВРИСТИКА:
# послідовні повідомлення ОДНОГО типу (дрон/ракета) поєднуються в один
# маршрут, якщо відстань між точками правдоподібна для часу між ними.
ROUTES_STATE_FILE = "routes_state.json"
TRACK_MAX_AGE_HOURS = 1            # маршрут "закривається" (зникає), якщо давно без нових точок
MAX_POINTS_PER_TRACK = 6         # далі краще почати новий трек, ніж тягнути один нескінченно

# Параметри навмисно жорсткі: краще пропустити реальний зв'язок між точками,
# ніж намалювати абсурдний "маршрут" через півкраїни між двома різними,
# просто одночасними дронами/ракетами. Це все одно евристика (канали не
# дають ID цілі), тому консервативність тут важливіша за повноту.
DRONE_MAX_SPEED_KMH = 150
DRONE_MAX_GAP_MINUTES = 40
DRONE_MAX_HOP_KM = 120            # жорсткий ліміт на один "стрибок", незалежно від швидкості

MISSILE_MAX_SPEED_KMH = 2500
MISSILE_MAX_GAP_MINUTES = 15
MISSILE_MAX_HOP_KM = 250

# --- ключові слова для визначення типу загрози ---
# ПРИМІТКА: це стартовий, приблизний набір. Реальний формат повідомлень
# у кожному каналі може відрізнятись — після перших запусків краще
# звірити результати з оригінальними постами і скоригувати список.
TYPE_KEYWORDS = [
    ("all_clear", [
        "отбой", "угроза миновала",
        "опасности нет", "опасности никакой нет", "угрозы нет",
        "всё хорошо", "все хорошо", "всё спокойно", "все спокойно",
        "ничего страшного",
    ]),
    ("ballistic", ["баллистич", "искандер", "кинжал", "циркон"]),
    ("missile", ["ракет", "калибр", "х-101", "х-22", "х-59", "фламинго", "крылат"]),
    ("drone", ["бпла", "дрон", "шахед", "shahed", "герань"]),
    ("aviation", ["авиац", "ил-76", "миг-31", "миг-29", "су-34", "су-35", "взлет", "взлёт"]),
    ("shelling", ["обстрел", "артобстрел", "минометн"]),
    ("alert", ["тревога", "угроза атаки", "опасност"]),
]

# Регіон (область/край/республіка) — зазвичай йде ПІСЛЯ переліку районів/міст,
# а вже після нього — опис події ("Фиксация БПЛА", "- ракетная опасность...")
REGION_PATTERN = re.compile(
    r"((?:[А-ЯЁ][а-яёА-ЯЁ\-]+\s+)?(?:облас(?:ть|ти|тью|тей)|кра(?:й|я|ю|ем|е)|автономн\w*\s+округ\w*)|Республик\w*\s+[А-ЯЁа-яё\-]+)"
)

# канали іноді пишуть скорочення замість повної назви області/республіки —
# розгортаємо їх у повну форму ще ДО пошуку REGION_PATTERN
REGION_ABBREVIATIONS = {
    r"\bДНР\b": "Донецкая область",
    r"\bЛНР\b": "Луганская область",
}


def expand_region_abbreviations(text: str) -> str:
    for pattern, full_name in REGION_ABBREVIATIONS.items():
        text = re.sub(pattern, full_name, text, flags=re.IGNORECASE)
    return text


# "через Калужскую, Тульскую область и далее..." — типова конструкція, де
# слово "область" стоїть лише раз в кінці, але стосується ВСІХ прикметників
# у переліку через кому. Розгортаємо в "Калужскую область, Тульскую область".
#
# ВАЖЛИВО: спрацьовує ТІЛЬКИ якщо кожне попереднє слово схоже на прикметник
# області за закінченням (-ая/-ую/-ой/-ий/...). Інакше на кшталт
# "Тула, Щекино, Алексин, Тульская область" (перелік МІСТ, а не областей)
# кожне місто помилково перетвориться на фейковий "регіон".
ELIDED_SUFFIX_PATTERN = re.compile(
    r"((?:[А-ЯЁ][а-яёА-ЯЁ\-]+,\s*)+)([А-ЯЁ][а-яёА-ЯЁ\-]+)\s+(облас(?:ть|ти|тью|тей)|кра(?:й|я|ю|ем|е))"
)
ADJECTIVE_ENDINGS = ("ая", "яя", "ое", "ее", "ый", "ий", "ую", "юю", "ой", "ей")


def expand_elided_region_suffix(text: str) -> str:
    def repl(m):
        leading_words = [w.strip() for w in m.group(1).split(",") if w.strip()]
        suffix = m.group(3)
        # якщо хоч ОДНЕ слово в переліку не схоже на прикметник області —
        # не чіпаємо цей збіг взагалі (безпечніше недорозгорнути, ніж
        # хибно перетворити назви міст на "регіони")
        if not leading_words or not all(w.lower().endswith(ADJECTIVE_ENDINGS) for w in leading_words):
            return m.group(0)
        expanded = ", ".join(f"{w} {suffix}" for w in leading_words)
        return f"{expanded}, {m.group(2)} {suffix}"

    return ELIDED_SUFFIX_PATTERN.sub(repl, text)

# фрази-шум, які потрапляють у "хвіст" переліку локацій, але самі не є місцем
LOCATION_STOPWORDS = [
    "и близлежащие населенные пункты",
    "и близлежащие населённые пункты",
    "и далее в тыл",
    "и последующие",
]


def extract_locations_and_regions(text: str):
    """Повертає (locations, regions) — список локацій (районів/міст) і
    список ОДНІЄЇ АБО КІЛЬКОХ областей.

    Два формати повідомлень:
    1) "Район1 Район2 Область Опис" — один регіон, з районами/містами
       всередині нього (стандартний випадок).
    2) "Область1, Область2, Область3 - опис" — ОДРАЗУ кілька областей
       через кому в одному повідомленні (без деталізації по районах).
       Розпізнаємо це за тим, що в тексті знайдено 2+ згадки області/
       республіки — тоді трактуємо кожну як окремий уражений регіон.
    """
    text = expand_region_abbreviations(text)
    text = expand_elided_region_suffix(text)
    region_matches = list(REGION_PATTERN.finditer(text))

    if len(region_matches) >= 2:
        regions, seen = [], set()
        for m in region_matches:
            r = m.group(0).strip()
            if r not in seen:
                seen.add(r)
                regions.append(r)
        return [], regions

    region_match = region_matches[0] if region_matches else None
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
    return result, ([region] if region else [])


COUNT_PATTERN = re.compile(r"(\d+)\s*(?:бпла|дрон\w*|ракет\w*|шахед\w*)", re.IGNORECASE)

# коли канал не дав точну цифру, а написав словом — беремо приблизну оцінку
# з позначкою "це не точне число" (approx=True), а не просто ігноруємо
WORD_COUNT_PATTERN = re.compile(
    r"(сотн\w*|десятк\w*|единичн\w*)\s*(?:бпла|дрон\w*|ракет\w*|шахед\w*)", re.IGNORECASE
)
WORD_COUNT_VALUES = {"сотн": 100, "десятк": 10, "единичн": 1}


def extract_unit_count(text: str):
    """Витягує кількість дронів/ракет з тексту.

    Повертає (count, approx):
    - (число, False) — якщо канал вказав точну цифру ("Фиксация от 4 БПЛА")
    - (число, True) — якщо канал написав приблизно словом ("сотни БПЛА" -> 100)
    - (None, False) — якщо кількість взагалі не згадана
    """
    m = COUNT_PATTERN.search(text)
    if m:
        return int(m.group(1)), False

    m = WORD_COUNT_PATTERN.search(text)
    if m:
        word = m.group(1).lower()
        for stem, value in WORD_COUNT_VALUES.items():
            if word.startswith(stem):
                return value, True

    return None, False


def update_region_status(region_status: dict, region: str, alert_type: str, text: str, channel: str, msg_time):
    """Оновлює статус регіону для підсвітки на карті.

    ВАЖЛИВО: msg_time — це час САМОГО повідомлення в Telegram (m.date),
    а НЕ час запуску скрипта. Інакше при читанні пачки старих повідомлень
    підсвітка показувала б час запуску скрипта замість реального часу тривоги.

    Головне правило: коли приходить повідомлення типу "all_clear" (відбій,
    "угроза миновала") — підсвітка регіону ЗНІМАЄТЬСЯ одразу.
    В іншому разі — оновлюється активний тип загрози й причина (текст
    повідомлення), з підстраховкою по часу (REGION_BACKSTOP_HOURS) на
    випадок, якщо канал просто замовк, а не дав явний відбій.
    """
    if not region:
        return

    key = normalize_region_for_match(region)
    if not key:
        return

    if alert_type == "all_clear":
        region_status.pop(key, None)
        return

    expires_at = msg_time + timedelta(hours=REGION_BACKSTOP_HOURS)
    count, count_approx = extract_unit_count(text)
    region_status[key] = {
        "display_name": region,
        "type": alert_type,
        "text": text[:300],
        "channel": channel,
        "updated_at": msg_time.isoformat(),
        "expires_at": expires_at.isoformat(),
        "count": count,
        "count_approx": count_approx,
    }


def prune_expired_regions(region_status: dict, now):
    expired = [
        r for r, s in region_status.items()
        if datetime.fromisoformat(s["expires_at"]) < now
    ]
    for r in expired:
        del region_status[r]


def haversine_km(lat1, lon1, lat2, lon2):
    R = 6371
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlambda = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(dlambda / 2) ** 2
    return 2 * R * math.asin(math.sqrt(a))


def try_extend_or_create_track(tracks, event_type, lat, lon, time_dt, location_name, region):
    """Додає точку до існуючого маршруту (якщо стрибок правдоподібний за
    відстанню/часом) або починає новий маршрут. Маршрути будуємо тільки
    для дронів і ракет — для інших типів це не має сенсу."""
    if event_type not in ("drone", "missile", "ballistic"):
        return

    max_speed = DRONE_MAX_SPEED_KMH if event_type == "drone" else MISSILE_MAX_SPEED_KMH
    max_gap = DRONE_MAX_GAP_MINUTES if event_type == "drone" else MISSILE_MAX_GAP_MINUTES
    max_hop_km = DRONE_MAX_HOP_KM if event_type == "drone" else MISSILE_MAX_HOP_KM

    best_track, best_dist = None, None
    for tr in tracks:
        if tr["type"] != event_type:
            continue
        if len(tr["points"]) >= MAX_POINTS_PER_TRACK:
            continue  # цей трек уже досить довгий — хай далі росте новий
        last = tr["points"][-1]
        last_time = datetime.fromisoformat(tr["last_time"])
        gap_min = (time_dt - last_time).total_seconds() / 60
        if gap_min <= 0 or gap_min > max_gap:
            continue
        dist = haversine_km(last["lat"], last["lon"], lat, lon)
        if dist > max_hop_km:
            continue
        implied_speed = dist / (gap_min / 60) if gap_min > 0 else 0
        if dist <= 15 or implied_speed <= max_speed:
            if best_dist is None or dist < best_dist:
                best_dist = dist
                best_track = tr

    point = {
        "lat": lat, "lon": lon, "time": time_dt.isoformat(),
        "location_name": location_name, "region": region,
    }

    if best_track is not None:
        last = best_track["points"][-1]
        # не додаємо точку, якщо вона фактично та сама, що й попередня
        # (та сама назва локації й практично той самий стрибок) — це не
        # рух, а просто повторна згадка того самого місця
        if location_name and location_name == last.get("location_name") and best_dist is not None and best_dist <= 5:
            best_track["last_time"] = time_dt.isoformat()
            return
        best_track["points"].append(point)
        best_track["last_time"] = time_dt.isoformat()
    else:
        tracks.append({
            "id": f"{event_type}_{time_dt.timestamp()}_{location_name or region or 'x'}",
            "type": event_type,
            "points": [point],
            "last_time": time_dt.isoformat(),
        })


def prune_tracks(tracks, now):
    return [
        tr for tr in tracks
        if (now - datetime.fromisoformat(tr["last_time"])) <= timedelta(hours=TRACK_MAX_AGE_HOURS)
    ]


def tracks_to_geojson(tracks):
    features = []
    for tr in tracks:
        if len(tr["points"]) < 2:
            continue  # маршрут малюємо тільки якщо є хоча б 2 точки

        # відкидаємо "маршрути", де всі точки фактично в одному місці
        # (напр. дві згадки тієї самої області без конкретного міста/району
        # геокодувались в один і той самий центр — це не рух, а шум)
        total_km = sum(
            haversine_km(p1["lat"], p1["lon"], p2["lat"], p2["lon"])
            for p1, p2 in zip(tr["points"], tr["points"][1:])
        )
        if total_km < 20:
            continue

        coords = [[p["lon"], p["lat"]] for p in tr["points"]]
        def label_for(p):
            loc = p.get("location_name")
            reg = p.get("region")
            if loc and reg and reg not in loc:
                return f"{loc} ({reg})"
            return loc or reg or "?"

        labels = [label_for(p) for p in tr["points"]]
        features.append({
            "type": "Feature",
            "properties": {
                "type": tr["type"],
                "started_at": tr["points"][0]["time"],
                "last_updated": tr["last_time"],
                "path_labels": labels,
            },
            "geometry": {"type": "LineString", "coordinates": coords},
        })
    return {"type": "FeatureCollection", "features": features}


# фрази, які явно вказують на РУХ через кілька регіонів в ОДНОМУ повідомленні
# (на відміну від простого переліку "Область1, Область2, Область3 - опис",
# де порядок нічого не означає) — напр. "через Калужскую, Тульскую и далее
# на Московскую область". Тут порядок згадки регіонів = напрямок руху.
MOVEMENT_KEYWORDS = [
    "через", "и далее на", "и далее в", "далее на", "далее в тыл",
    "движется в направлении", "движется на", "летит через", "продолжает движение",
]


def load_region_centroids():
    """Рахує приблизний центр кожного регіону (з уже наявних geojson-файлів
    карти) — потрібно, щоб малювати явний маршрут по регіонах з одного
    повідомлення, де немає конкретного міста/району, тільки назви областей."""
    from shapely.geometry import shape

    centroids = {}
    for path, name_field in (
        ("docs/russia_regions.geojson", "region"),
        ("docs/occupied_territories.geojson", "match_key"),
    ):
        try:
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
            for feat in data.get("features", []):
                raw_name = feat["properties"].get(name_field, "")
                key = (
                    normalize_region_for_match(raw_name)
                    if name_field == "region"
                    else raw_name
                )
                if key and key not in centroids:
                    c = shape(feat["geometry"]).centroid
                    centroids[key] = [c.y, c.x]
        except Exception as e:
            print(f"Failed to load centroids from {path}: {e}")
    return centroids


# якщо в "явному" маршруті раптом трапляється стрибок на неправдоподібну
# відстань (напр. Москва -> Кримський міст в одному повідомленні) —
# обрізаємо ланцюжок саме на цьому місці, а не малюємо абсурдну лінію
EXPLICIT_ROUTE_MAX_HOP_KM = 500


def build_explicit_route(tracks, alert_type, regions, region_centroids, msg_time, channel):
    """Будує маршрут напряму з ОДНОГО повідомлення, де канал явно перелічив
    регіони в порядку руху (напр. "через Калужскую, Тульскую и далее на
    Московскую область"). На відміну від try_extend_or_create_track, тут не
    треба вгадувати зв'язок між окремими повідомленнями — порядок вже дано."""
    if alert_type not in ("drone", "missile", "ballistic"):
        return
    raw_points = []
    for r in regions:
        key = normalize_region_for_match(r)
        c = region_centroids.get(key)
        if c:
            raw_points.append({
                "lat": c[0], "lon": c[1], "time": msg_time.isoformat(),
                "location_name": r, "region": r,
            })
    if len(raw_points) < 2:
        return

    # обрізаємо ланцюжок на першому неправдоподібному стрибку
    points = [raw_points[0]]
    for p in raw_points[1:]:
        prev = points[-1]
        dist = haversine_km(prev["lat"], prev["lon"], p["lat"], p["lon"])
        if dist > EXPLICIT_ROUTE_MAX_HOP_KM:
            break
        points.append(p)
    if len(points) < 2:
        return

    tracks.append({
        "id": f"{alert_type}_{msg_time.timestamp()}_explicit_{channel}",
        "type": alert_type,
        "points": points,
        "last_time": msg_time.isoformat(),
    })


def detect_type(text: str) -> str:
    low = text.lower()
    for label, keywords in TYPE_KEYWORDS:
        if any(kw in low for kw in keywords):
            return label
    return "unknown"


OCR_BOILERPLATE_PATTERNS = [
    r"вниман\w*", r"объявлен\w*", r"уровень\w*", r"опасност\w*",
    r"желтый", r"жёлтый", r"красный", r"зелен\w*", r"ракетн\w*",
    r"купол\s*росс\w*", r"по\s+бпла", r"отбой",
]


def clean_ocr_text_for_location(text: str) -> str:
    """Прибирає стандартні шаблонні фрази купола ("ВНИМАНИЕ", "ОБЪЯВЛЕН
    ЖЕЛТЫЙ УРОВЕНЬ" тощо), щоб вони не заважали розпізнаванню
    районів/міст/областей у решті тексту."""
    cleaned = text
    for pat in OCR_BOILERPLATE_PATTERNS:
        cleaned = re.sub(pat, " ", cleaned, flags=re.IGNORECASE)
    # переноси рядків у картинці = фактично роздільники, як кома
    cleaned = re.sub(r"[\n\r]+", ", ", cleaned)
    cleaned = re.sub(r"!{1,}", " ", cleaned)
    cleaned = re.sub(r"\s{2,}", " ", cleaned).strip(" ,")
    return cleaned


def is_plausible_ocr_text(text: str) -> bool:
    """Груба перевірка "чи це взагалі схоже на нормальний текст", а не
    сміття типу '© > 7& Я'. Дивимось частку кириличних літер серед усіх
    літер у розпізнаному тексті."""
    letters = [c for c in text if c.isalpha()]
    if len(letters) < 3:
        return False
    cyrillic = sum(1 for c in letters if "а" <= c.lower() <= "я" or c.lower() in "ёї")
    return (cyrillic / len(letters)) >= 0.6


def ocr_image_bytes(data: bytes) -> str:
    try:
        img = Image.open(io.BytesIO(data)).convert("L")  # у відтінки сірого
        img = ImageOps.autocontrast(img)

        # усі ключові слова, які ми взагалі розпізнаємо — якщо результат
        # OCR містить хоч одне з них, вважаємо спробу вдалою
        all_keywords = [kw for _, kws in TYPE_KEYWORDS for kw in kws]

        attempts = []
        for scale in (2, 3):
            resized = img.resize((img.width * scale, img.height * scale))
            for psm in (6, 4):
                try:
                    txt = pytesseract.image_to_string(
                        resized, lang="rus", config=f"--psm {psm}"
                    ).strip()
                except Exception:
                    continue
                # сміттєві результати (нечитабельна абракадабра) відкидаємо
                # одразу — вони не потрапляють навіть у запасний варіант
                if txt and is_plausible_ocr_text(txt):
                    attempts.append(txt)
                    if any(kw in txt.lower() for kw in all_keywords):
                        return txt  # знайшли впізнаване слово — цього досить

        # жоден варіант не дав впізнаваного слова, але хоч якийсь був
        # правдоподібним текстом — повертаємо найдовший з них
        if attempts:
            return max(attempts, key=len)

        # усі спроби виявились сміттям — краще НІЧОГО не повертати,
        # ніж показати на карті нерозбірливу абракадабру
        return ""
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


def normalize_region_for_match(name: str) -> str:
    """Спрощує назву регіону до "кореня" для порівняння (те саме, що робить
    normalizeRegion() на фронтенді, лише в Python) — щоб звірити, чи
    результат геокодування дійсно в очікуваному регіоні."""
    if not name:
        return ""
    n = name.lower()
    n = re.sub(r"\(.*?\)", "", n)
    n = re.sub(r"облас(?:ть|ти|тью|тей)|обл\.?|кра(?:й|я|ю|ем|е)|республик\w*|автономн\w*\s*округ\w*", "", n)
    n = re.sub(r"[^а-яё\- ]", "", n)
    n = re.sub(r"\s+", " ", n).strip()
    root = n.split(" ")[0] if n else ""
    # прибираємо закінчення відмінка (останні 2 літери), щоб "Калужскую"
    # (знахідний відмінок, напр. "через Калужскую область") і "Калужская"
    # (називний, офіційна назва в geojson) зводились до одного кореня
    if len(root) > 6:
        root = root[:-2]
    return root


def geocode(name: str, region: str, cache: dict):
    cache_key = f"{name}|{region or ''}"
    if cache_key in cache:
        return cache[cache_key]
    query = f"{name}, {region}, Russia" if region else f"{name}, Russia"
    try:
        # Nominatim (OpenStreetMap) — безкоштовний, але ліміт ~1 запит/сек
        resp = requests.get(
            "https://nominatim.openstreetmap.org/search",
            params={
                "q": query, "format": "jsonv2", "limit": 1,
                "addressdetails": 1, "countrycodes": "ru",
            },
            headers={"User-Agent": "nahr-map-clone/1.0"},
            timeout=10,
        )
        data = resp.json()
        time.sleep(1.1)  # поважаємо rate limit Nominatim
        if data:
            result = data[0]
            coords = [float(result["lat"]), float(result["lon"])]

            # ВАЖЛИВО: Nominatim іноді "притягує" схожу назву в зовсім
            # іншому регіоні (напр. район з такою ж назвою біля Москви
            # замість Тульської області). Звіряємо, що знайдене місце
            # дійсно в очікуваному регіоні, перш ніж довіряти координатам.
            if region:
                expected_root = normalize_region_for_match(region)
                address = result.get("address", {})
                actual_region_raw = (
                    address.get("state") or address.get("region")
                    or address.get("county") or ""
                )
                actual_root = normalize_region_for_match(actual_region_raw)
                if expected_root and actual_root and expected_root not in actual_root and actual_root not in expected_root:
                    print(f"Geocode region mismatch: '{name}' expected '{region}' but got '{actual_region_raw}' — відкидаю")
                    cache[cache_key] = None
                    return None

            cache[cache_key] = coords
            return coords
    except Exception as e:
        print(f"Geocode error for '{query}': {e}")
    cache[cache_key] = None
    return None


def fetch_occupied_line():
    """Підтягує актуальний контур окупованої території з DeepStateMap
    (проєкт cyterat/deepstate-map-data, оновлюється щодня о 03:00 UTC).
    Файл великий (~90к вузлів), тому спрощуємо геометрію перед збереженням.
    """
    try:
        from shapely.geometry import shape, mapping

        today = datetime.now(timezone.utc)
        for days_back in range(4):  # якщо сьогоднішній файл ще не залили — беремо вчорашній і т.д.
            d = (today - timedelta(days=days_back)).strftime("%Y%m%d")
            url = f"https://raw.githubusercontent.com/cyterat/deepstate-map-data/main/data/deepstatemap_data_{d}.geojson"
            resp = requests.get(url, headers={"User-Agent": "telegram-monitor"}, timeout=20)
            if resp.status_code == 200:
                data = resp.json()
                feat = data["features"][0]
                geom = shape(feat["geometry"]).simplify(0.005, preserve_topology=True)
                out = {
                    "type": "FeatureCollection",
                    "features": [{"type": "Feature", "properties": {}, "geometry": mapping(geom)}],
                }
                save_json("docs/occupied_line.geojson", out)
                print(f"Occupied line updated from {d}")
                return
        print("Could not find recent DeepState file")
    except Exception as e:
        print(f"Failed to update occupied line: {e}")


def main():
    api_id = int(os.environ["TG_API_ID"])
    api_hash = os.environ["TG_API_HASH"]
    session = os.environ["TG_SESSION"]

    state = load_json(STATE_FILE, {})
    events = load_json(EVENTS_FILE, [])
    geocode_cache = load_json(GEOCODE_CACHE_FILE, {})
    region_status = load_json(REGION_STATUS_FILE, {})
    tracks = load_json(ROUTES_STATE_FILE, {"tracks": []}).get("tracks", [])
    region_centroids = load_region_centroids()
    now = datetime.now(timezone.utc)

    fetch_occupied_line()

    all_messages = []  # (message, channel) — зберемо з усіх каналів, потім відсортуємо за часом

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
            for m in messages:
                all_messages.append((m, channel))

        # ВАЖЛИВО: обробляємо повідомлення з УСІХ каналів разом, у порядку
        # реального часу (а не канал-за-каналом) — інакше старіше повідомлення
        # з одного каналу могло б перезаписати підсвітку регіону новішим
        # повідомленням з іншого каналу.
        all_messages.sort(key=lambda pair: pair[0].date)

        for m, channel in all_messages:
            text = (m.message or "").strip()

            # деякі канали (напр. kupolrussia) публікують текст ЯК КАРТИНКУ,
            # а не як звичайний текст повідомлення — тоді m.message порожній,
            # але є фото. Розпізнаємо текст через OCR (tesseract, мова 'rus').
            ocr_used = False
            if m.photo:
                # ВАЖЛИВО: навіть якщо в повідомленні вже є якийсь текст-підпис
                # (напр. LPRalarm додає власне "Lpr 1" поверх пересланої
                # картинки купола) — все одно розпізнаємо саму картинку,
                # інакше реальна інформація (тип загрози, регіон) губиться,
                # а лишається лише беззмістовний підпис.
                try:
                    photo_bytes = client.download_media(m, file=bytes)
                    if photo_bytes:
                        ocr_text = ocr_image_bytes(photo_bytes)
                        if ocr_text:
                            text = (text + "\n" + ocr_text).strip() if text else ocr_text
                            ocr_used = True
                except Exception as e:
                    print(f"Failed to download/OCR photo for {channel}/{m.id}: {e}")

            if not text:
                continue

            msg_time = m.date.astimezone(timezone.utc)
            alert_type = detect_type(text)
            # для OCR-тексту прибираємо шаблонні фрази ("ВНИМАНИЕ", "ОБЪЯВЛЕН
            # ЖЕЛТЫЙ УРОВЕНЬ" тощо) перед пошуком районів/областей — вони
            # тільки заважають; для звичайного тексту каналів це не потрібно
            parse_text = clean_ocr_text_for_location(text) if ocr_used else text
            locations, regions = extract_locations_and_regions(parse_text)

            # оновлюємо підсвітку для КОЖНОГО згаданого регіону — повідомлення
            # може стосуватися відразу кількох областей ("Область1, Область2,
            # Область3 - опасность по БПЛА")
            # ВАЖЛИВО: якщо тип загрози взагалі не розпізнано (unknown),
            # НЕ чіпаємо підсвітку регіонів. Інакше повідомлення, яке просто
            # ЗГАДУЄ назви кількох областей (скарги, офтоп, підписи каналу
            # тощо) без жодного реального ключового слова тривоги, може
            # хибно "запалити" підсвітку одразу в купі регіонів.
            if alert_type != "unknown":
                for region in regions:
                    update_region_status(region_status, region, alert_type, text, channel, msg_time)

            # якщо канал явно описав напрямок руху через кілька регіонів в
            # одному повідомленні — малюємо це як готовий маршрут одразу,
            # без евристики між окремими повідомленнями
            if len(regions) >= 2 and any(kw in text.lower() for kw in MOVEMENT_KEYWORDS):
                build_explicit_route(tracks, alert_type, regions, region_centroids, msg_time, channel)

            primary_region = regions[0] if regions else None

            # для кожної знайденої локації створюємо ОКРЕМУ подію —
            # в повідомленнях часто перелічено кілька районів/міст одразу
            any_added = False
            for loc in locations:
                coords = geocode(loc, primary_region, geocode_cache)
                if not coords:
                    continue
                lat, lon = coords
                try_extend_or_create_track(tracks, alert_type, lat, lon, msg_time, loc, primary_region)
                events.append(
                    {
                        "id": f"{channel}_{m.id}_{loc}",
                        "channel": channel,
                        "date": msg_time.isoformat(),
                        "text": text[:500],
                        "type": alert_type,
                        "location_name": loc,
                        "region": primary_region,
                        "lat": lat,
                        "lon": lon,
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
                        "date": msg_time.isoformat(),
                        "text": text[:500],
                        "type": alert_type,
                        "location_name": None,
                        "region": primary_region,
                        "lat": None,
                        "lon": None,
                    }
                )

    # тримаємо тільки останні N подій, щоб JSON не розростався нескінченно
    events = events[-MAX_EVENTS_KEPT:]

    # знімаємо підсвітку з регіонів, де давно не було жодних новин
    # (підстраховка на випадок, якщо явного "відбою" так і не було)
    prune_expired_regions(region_status, now)
    tracks = prune_tracks(tracks, now)

    save_json(STATE_FILE, state)
    save_json(EVENTS_FILE, events)
    save_json(GEOCODE_CACHE_FILE, geocode_cache)
    save_json(REGION_STATUS_FILE, region_status)
    save_json(ROUTES_STATE_FILE, {"tracks": tracks})
    save_json("docs/routes.geojson", tracks_to_geojson(tracks))
    print(f"Done. Total events stored: {len(events)}, active regions: {len(region_status)}, active tracks: {len(tracks)}")


if __name__ == "__main__":
    main()
