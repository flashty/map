"""
ОДНОРАЗОВИЙ скрипт: логінить тебе в Telegram і видає StringSession,
яку потім кладеш у GitHub Secrets. Запускати ЛОКАЛЬНО у себе на комп'ютері
(не в GitHub Actions), бо треба буде ввести код підтвердження з Telegram.

Перед запуском:
1. Зайди на https://my.telegram.org -> API development tools
2. Створи застосунок, скопіюй api_id та api_hash
3. pip install telethon
4. python generate_session.py

В кінці скрипт виведе рядок session_string — його треба зберегти
як секрет TG_SESSION у налаштуваннях GitHub-репозиторію.
НІКОМУ НЕ ПОКАЗУЙ ЦЕЙ РЯДОК — він дає повний доступ до твого акаунту.
"""

from telethon.sync import TelegramClient
from telethon.sessions import StringSession

api_id = int(input("API ID: ").strip())
api_hash = input("API Hash: ").strip()

with TelegramClient(StringSession(), api_id, api_hash) as client:
    session_string = client.session.save()
    print("\n=== ЗБЕРЕЖИ ЦЕЙ РЯДОК ЯК GitHub Secret TG_SESSION ===\n")
    print(session_string)
    print("\n=====================================================")
