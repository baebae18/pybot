#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
디스코드 봇 (discord.py 2.x) - 기존 Node.js(discord.js) 봇을 파이썬으로 옮긴 버전

설치:   pip install -U "discord.py[voice]" aiohttp
설정:   bot.py 와 같은 폴더(또는 한 단계 위 폴더)에 config.json 을 둡니다.
        { "token": "봇토큰", "stdictKey": "표준국어대사전 API 키(선택)" }
        (환경변수 DISCORD_TOKEN 이 있으면 그 값을 우선 사용)
실행:   python bot.py

데이터 파일(points.json, chat.json 등)은 기존 Node.js 버전과 같은 형식이라 그대로 이어서 쓸 수 있어요.
"""
from __future__ import annotations

import asyncio
import calendar
import importlib.util
import json
import logging
import os
import random
import re
import time
import unicodedata
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Callable, Optional
from urllib.parse import quote

import aiohttp
import discord
from discord import app_commands

logging.basicConfig(level=logging.INFO, format='%(asctime)s %(levelname)s %(name)s: %(message)s')
log = logging.getLogger('bot')

BASE_DIR = Path(__file__).resolve().parent


# =====================================================================
#  설정 / 상수
# =====================================================================
def load_config() -> dict:
    for p in (BASE_DIR / 'config.json', BASE_DIR.parent / 'config.json'):
        if p.exists():
            return json.loads(p.read_text(encoding='utf-8'))
    raise SystemExit('config.json 을 찾을 수 없어요. {"token": "봇토큰"} 형식으로 만들어주세요.')


_CONFIG_FILE = load_config()
TOKEN = os.environ.get('DISCORD_TOKEN') or _CONFIG_FILE.get('token')
STDICT_KEY: Optional[str] = _CONFIG_FILE.get('stdictKey') or None

# 소유자 디스코드 ID
OWNER_IDS = {1550921230008324097, 1558550236643856407}


def is_owner_id(i) -> bool:
    try:
        return int(i) in OWNER_IDS
    except (TypeError, ValueError):
        return False


# 소유자만 쓸 수 있는 명령어 (허용된 사람도 못 씀)
OWNER_ONLY = {'!허용', '!허용해제', '!허용목록', '!디엠', '!관리', '!서버나가기', '!서버목록',
              '!정복메세지허용', '!정복메세지허용해제', '!정복메세지허용목록'}


class CFG:
    EVERYONE = True                 # True: 출석/송금/도박/끝말잇기 등을 누구나 사용 / False: 허용된 사람만

    # --- 출석 ---
    DAILY_BASE = 100
    DAILY_STREAK_BONUS = 20
    DAILY_STREAK_MAX = 6
    DAILY_WEEK_BONUS = 300

    # --- 송금 ---
    TRANSFER_MIN = 1
    TRANSFER_FEE_RATE = 0.1
    DONATE_RECEIVER_IDS: list[int] = []   # /후원 받을 사람 ID 목록 (비어 있으면 /후원 사용 불가, !출금은 모두 후원 로그로 기록)

    # --- 도박 ---
    MIN_BET = 1
    MAX_BET = 100_000_000_000
    GAMBLE_COOLDOWN_MS = 3000
    COIN_WIN_RATE = 0.5
    RPS_WIN_MULT = 1

    # --- 끝말잇기 ---
    CHAIN_TIMEOUT_MS = 60 * 1000
    CHAIN_ALLOW_SAME_USER = False
    CHAIN_LIVES = 3
    CHAIN_LOSE_LIFE_ON_WRONG_LETTER = True
    CHAIN_STRICT_DICT = True
    CHAIN_REWARD_PER_WORD = 3
    CHAIN_REWARD_MAX_WORDS = 30
    CHAIN_BANNED_ENDINGS = ['늄', '듐', '륨', '슘', '튬', '븀', '뮴', '릇', '즘', '쯤', '녘']
    CHAIN_BOT_DELAY_MS = 800
    CHAIN_BOT_WIN_REWARD = 50
    CHAIN_BOT_WIN_MIN_WORDS = 3

    # --- 로그 ---
    LOG_VOICE = True
    VOICE_LIVE_INTERVAL_MS = 60 * 1000

    # --- 생일 ---
    BIRTHDAY_HOUR = 0
    BIRTHDAY_REWARD = 0
    BIRTHDAY_MAX_ENTRIES = 500

    # --- 레벨링 ---
    LEVEL_CHAT_XP_MIN = 15
    LEVEL_CHAT_XP_MAX = 25
    LEVEL_CHAT_COOLDOWN_MS = 60 * 1000
    LEVEL_VOICE_XP = 10
    LEVEL_UP_POINTS = 0
    LEVEL_NICK_FORMAT = '[Lv.{level}]'

    # --- 포인트 수거 ---
    COLLECT_GIVE_TO_COLLECTOR = False


class PCFG:
    CHAT_POINT = 1
    CHAT_COOLDOWN_MS = 10 * 1000
    VOICE_POINT = 2
    VOICE_INTERVAL_MS = 60 * 1000
    MAX_MANUAL = 1_000_000_000


TYPING_TIMEOUT_MS = 30 * 1000
TYPING_REWARD = 50
VERIFY_EMOJI = '✅'
VERIFY_REMOVE_ON_UNREACT = True
INCIDENT_STATUSES = ['접수', '검토중', '기관 전달', '종결']

KST_OFFSET_MS = 9 * 60 * 60 * 1000
DAY_MS = 24 * 60 * 60 * 1000
WEEK_MS = 7 * DAY_MS
MEDALS = ['🥇', '🥈', '🥉']
NO_MENTIONS = discord.AllowedMentions.none()


# =====================================================================
#  공용 유틸
# =====================================================================
def now_ms() -> int:
    return int(time.time() * 1000)


def unix(ms: float) -> int:
    return int(ms // 1000)


def fmt(n) -> str:
    return f'{int(n):,}'


def clip(s: Optional[str], n: int = 1000) -> str:
    if not s:
        return ''
    return s if len(s) <= n else s[:n] + '…'


def day_key(t: Optional[int] = None) -> str:
    """한국 날짜 'YYYY-MM-DD'"""
    t = now_ms() if t is None else t
    return datetime.fromtimestamp((t + KST_OFFSET_MS) / 1000, tz=timezone.utc).strftime('%Y-%m-%d')


def get_week_start(now: Optional[int] = None) -> int:
    """이번 주 월요일 00:00 (한국 시간)의 timestamp(ms)"""
    now = now_ms() if now is None else now
    t = datetime.fromtimestamp((now + KST_OFFSET_MS) / 1000, tz=timezone.utc)
    day0 = datetime(t.year, t.month, t.day, tzinfo=timezone.utc) - timedelta(days=t.weekday())
    return int(day0.timestamp() * 1000) - KST_OFFSET_MS


def parse_id(text: Optional[str]) -> Optional[int]:
    """'@멘션' 또는 숫자 ID 문자열에서 ID만 뽑기"""
    s = re.sub(r'[<@!>]', '', text or '')
    return int(s) if re.fullmatch(r'\d{17,20}', s) else None


def mk_embed(color: int = 0x5865F2, title: Optional[str] = None, description: Optional[str] = None,
             ts: bool = False) -> discord.Embed:
    e = discord.Embed(color=color, title=title, description=description)
    if ts:
        e.timestamp = discord.utils.utcnow()
    return e


def users_only(*ids) -> discord.AllowedMentions:
    return discord.AllowedMentions(users=[discord.Object(id=int(i)) for i in ids], everyone=False,
                                   roles=False, replied_user=False)


def avatar_url(user, size: int = 256) -> str:
    return user.display_avatar.with_size(size).url


def is_text_channel(ch) -> bool:
    return isinstance(ch, discord.TextChannel)


def bot_can_send(guild: discord.Guild, ch) -> bool:
    p = ch.permissions_for(guild.me)
    return p.view_channel and p.send_messages and p.embed_links


async def fetch_json(url: str, timeout: float = 8):
    async with client.http_session.get(url, timeout=aiohttp.ClientTimeout(total=timeout)) as res:
        if res.status != 200:
            raise RuntimeError(f'HTTP {res.status}')
        return await res.json(content_type=None)


# =====================================================================
#  JSON 저장소: 변경하면 몇 초 뒤 모아서 저장, 임시파일 -> 교체 방식이라 저장 도중 꺼져도 파일이 안 깨짐
# =====================================================================
ALL_STORES: list['Store'] = []


class Store:
    def __init__(self, filename: str, defaults: Callable[[], Any]):
        self.name = filename
        self.path = BASE_DIR / filename
        data = defaults()
        try:
            if self.path.exists():
                loaded = json.loads(self.path.read_text(encoding='utf-8'))
                if isinstance(data, dict) and isinstance(loaded, dict):
                    data.update(loaded)
                elif isinstance(data, type(loaded)):
                    data = loaded
        except Exception as err:  # 파일이 깨졌을 때: 백업해 두고 빈 데이터로 시작 (다음 저장에서 덮어써 날아가는 것 방지)
            log.error('%s 읽기 실패: %s', filename, err)
            try:
                self.path.replace(self.path.with_suffix(self.path.suffix + f'.corrupt-{now_ms()}'))
            except OSError:
                pass
        self.data = data
        self.dirty = False
        ALL_STORES.append(self)

    def save(self) -> None:
        self.dirty = True

    def flush(self) -> None:
        if not self.dirty:
            return
        self.dirty = False
        try:
            tmp = self.path.with_suffix(self.path.suffix + '.tmp')
            tmp.write_text(json.dumps(self.data, ensure_ascii=False, indent=2), encoding='utf-8')
            tmp.replace(self.path)
        except Exception as err:
            self.dirty = True
            log.error('%s 저장 실패: %s', self.name, err)


def flush_all() -> None:
    for s in ALL_STORES:
        s.flush()


ALLOWED = Store('allowed.json', list)                                         # ["유저ID", ...]
INCIDENTS = Store('incident-response.json', lambda: {'channels': {}, 'cases': []})
LYRICS = Store('lyrics.json', dict)
TYPING = Store('typing.json', lambda: {'weekStart': 0, 'records': {}, 'lastWeek': []})
CHAT = Store('chat.json', lambda: {'weekStart': 0, 'guilds': {}})
POINTS = Store('points.json', lambda: {'guilds': {}})
ECONOMY = Store('economy.json', lambda: {'guilds': {}})
SETTINGS = Store('settings.json', lambda: {'guilds': {}})
VOICETIME = Store('voicetime.json', lambda: {'guilds': {}})
BIRTHDAYS = Store('birthdays.json', lambda: {'guilds': {}})
LEVELS = Store('levels.json', lambda: {'guilds': {}})
TPL = Store('template-data.json', lambda: {'guilds': {}, 'reactionRoles': [], 'modLogs': [], 'seq': 0})


# ---- 허용 사용자 ----
def allowed_has(uid) -> bool:
    return str(uid) in ALLOWED.data


def can_use(uid) -> bool:
    """CONFIG.EVERYONE 설정을 따르는 '누구나 쓰는' 기능 권한"""
    return CFG.EVERYONE or is_owner_id(uid) or allowed_has(uid)


# ---- 서버 설정 ----
def get_set(gid) -> dict:
    return SETTINGS.data['guilds'].setdefault(str(gid), {})


def peek_set(gid) -> dict:
    return SETTINGS.data['guilds'].get(str(gid), {})


# ---- 이전 형식(주간 구분 없는 typing.json) 이어받기 + 가사 중복 정리 ----
def _migrate_stores() -> None:
    d = TYPING.data
    legacy = {k: v for k, v in d.items() if k not in ('weekStart', 'records', 'lastWeek')}
    if legacy:
        if not d['records']:
            d['records'] = legacy
            d['weekStart'] = get_week_start()
        for k in legacy:
            del d[k]
        TYPING.save()


# ---- 관리 행동 기록 ----
def log_action(guild_id, moderator_id, target_id, action: str, reason: Optional[str] = None,
               amount: Optional[int] = None) -> None:
    d = TPL.data
    d['seq'] += 1
    d['modLogs'].append({
        'id': d['seq'], 'guildId': str(guild_id), 'moderatorId': str(moderator_id), 'targetId': str(target_id),
        'action': action, 'reason': reason or None, 'amount': amount,
        'createdAt': datetime.now(timezone.utc).isoformat(),
    })
    if len(d['modLogs']) > 5000:          # 파일이 끝없이 커지지 않게 최근 5000건만 유지
        del d['modLogs'][:len(d['modLogs']) - 5000]
    TPL.save()


# =====================================================================
#  ! 명령어 / / 명령어가 같은 코드를 쓰도록 감싸는 공통 컨텍스트
# =====================================================================
class Ctx:
    is_slash = False
    user: Any
    guild: Optional[discord.Guild]
    channel: Any
    member: Optional[discord.Member]
    message: Optional[discord.Message] = None
    created_ms: int = 0
    mention_ids: list[int]

    @property
    def first_mention(self) -> Optional[int]:
        return self.mention_ids[0] if self.mention_ids else None

    async def reply(self, content=None, *, embed=None, embeds=None, mentions=None, ephemeral=False):
        raise NotImplementedError

    async def send(self, content=None, *, embed=None, embeds=None, mentions=None):
        raise NotImplementedError

    async def react(self, emoji: str):
        raise NotImplementedError


def _kw(content, embed, embeds, mentions) -> dict:
    kw: dict = {}
    if content is not None:
        kw['content'] = content
    if embed is not None:
        kw['embed'] = embed
    if embeds is not None:
        kw['embeds'] = embeds
    if mentions is not None:
        kw['allowed_mentions'] = mentions
    return kw


class PrefixCtx(Ctx):
    def __init__(self, message: discord.Message):
        self.message = message
        self.user = message.author
        self.guild = message.guild
        self.channel = message.channel
        self.member = message.author if isinstance(message.author, discord.Member) else None
        self.created_ms = int(message.created_at.timestamp() * 1000)
        self.mention_ids = [m.id for m in message.mentions]

    async def reply(self, content=None, *, embed=None, embeds=None, mentions=None, ephemeral=False):
        return await self.message.reply(**_kw(content, embed, embeds, mentions))

    async def send(self, content=None, *, embed=None, embeds=None, mentions=None):
        return await self.channel.send(**_kw(content, embed, embeds, mentions))

    async def react(self, emoji: str):
        try:
            await self.message.add_reaction(emoji)
        except discord.HTTPException:
            pass


class SlashCtx(Ctx):
    is_slash = True

    def __init__(self, interaction: discord.Interaction):
        self.i = interaction
        self.user = interaction.user
        self.guild = interaction.guild
        self.channel = interaction.channel
        self.member = interaction.user if isinstance(interaction.user, discord.Member) else None
        self.created_ms = int(interaction.created_at.timestamp() * 1000)
        self.mention_ids = []
        self.replied = False
        # 봇이 그 채널에 직접 메시지를 보낼 수 있는 곳(봇이 설치된 서버)인지
        self.bot_access = interaction.guild is not None and interaction.channel is not None

    async def reply(self, content=None, *, embed=None, embeds=None, mentions=None, ephemeral=False):
        kw = _kw(content, embed, embeds, mentions)
        self.replied = True
        if not self.i.response.is_done():
            await self.i.response.send_message(ephemeral=ephemeral, **kw)
            return await self.i.original_response()
        return await self.i.followup.send(ephemeral=ephemeral, wait=True, **kw)

    async def send(self, content=None, *, embed=None, embeds=None, mentions=None):
        if self.bot_access and self.replied:
            return await self.channel.send(**_kw(content, embed, embeds, mentions))
        return await self.reply(content, embed=embed, embeds=embeds, mentions=mentions)

    async def react(self, emoji: str):
        # 반응은 슬래시에서 쓸 수 없으니 본인에게만 보이는 안내로 대신함 (예: 도박 쿨타임 ⏳)
        if self.replied:
            return
        text = '⏳ 잠깐만요! 잠시 후에 다시 시도해주세요. (쿨타임)' if emoji == '⏳' else str(emoji)
        await self.reply(text, ephemeral=True)


# =====================================================================
#  봇 클라이언트
# =====================================================================
class Bot(discord.Client):
    def __init__(self):
        intents = discord.Intents.default()
        intents.message_content = True
        intents.members = True
        intents.presences = True
        intents.voice_states = True
        intents.reactions = True
        super().__init__(intents=intents, max_messages=5000)
        self.tree = app_commands.CommandTree(self)
        self.http_session: Optional[aiohttp.ClientSession] = None
        self._ready_once = False

    async def setup_hook(self) -> None:
        self.http_session = aiohttp.ClientSession()
        asyncio.create_task(flush_loop())
        asyncio.create_task(voice_tick_loop())
        asyncio.create_task(birthday_loop())
        asyncio.create_task(voice_live_loop())
        try:
            synced = await self.tree.sync()
            log.info('슬래시 명령어 %d개 등록 완료 (전역)', len(synced))
        except Exception as err:
            log.error('슬래시 명령어 등록 실패: %s (봇 초대 시 "applications.commands" 스코프가 필요해요)', err)

    async def close(self) -> None:
        try:
            voice_flush()
        finally:
            flush_all()
        if self.http_session:
            await self.http_session.close()
        await super().close()


client = Bot()
tree = client.tree


async def flush_loop() -> None:
    while True:
        await asyncio.sleep(2)
        flush_all()


# ---- 명령어 등록 장치 ----
MAIN_CMDS: dict[str, Callable] = {}      # 소유자·허용된 사람만
EXTRA_CMDS: dict[str, Callable] = {}     # CFG.EVERYONE 설정을 따름
SETTING_CMDS: dict[str, Callable] = {}   # 서버 관리 권한 필요
TEMPLATE_CMDS: dict[str, Callable] = {}  # 디스코드 권한으로 직접 검사


def _register(table: dict, names):
    def deco(fn):
        for n in names:
            table[n] = fn
        return fn
    return deco


def main_cmd(*names):
    return _register(MAIN_CMDS, names)


def extra_cmd(*names):
    return _register(EXTRA_CMDS, names)


def setting_cmd(*names):
    return _register(SETTING_CMDS, names)


def template_cmd(*names):
    return _register(TEMPLATE_CMDS, names)


def is_manager(ctx: Ctx) -> bool:
    if is_owner_id(ctx.user.id):
        return True
    m = ctx.member
    return bool(m and m.guild_permissions.manage_guild)


def can_manage(guild: discord.Guild, target: discord.Member) -> bool:
    """봇이 이 멤버를 건드릴 수 있는지 (서버 주인이 아니고, 봇의 최상위 역할이 더 높음)"""
    me = guild.me
    return target.id != guild.owner_id and target.id != me.id and me.top_role > target.top_role

def pint(s) -> Optional[int]:
    """JS parseInt 처럼 앞쪽 숫자만 읽기 (없으면 None)"""
    m = re.match(r'\s*([-+]?\d+)', str(s or ''))
    return int(m.group(1)) if m else None


# =====================================================================
#  포인트
# =====================================================================
def get_point_user(gid, uid) -> dict:
    users = POINTS.data['guilds'].setdefault(str(gid), {})
    return users.setdefault(str(uid), {'points': 0, 'chat': 0, 'voice': 0})


def add_points(gid, uid, amount: int, source: str = 'manual') -> None:
    u = get_point_user(gid, uid)
    u['points'] = max(0, u['points'] + amount)
    if source == 'chat':
        u['chat'] += amount
    if source == 'voice':
        u['voice'] += amount
    POINTS.save()


_chat_point_cd: dict[str, int] = {}


def give_point_for_chat(gid, uid) -> None:
    key = f'{gid}-{uid}'
    t = now_ms()
    if t - _chat_point_cd.get(key, 0) < PCFG.CHAT_COOLDOWN_MS:
        return
    _chat_point_cd[key] = t
    add_points(gid, uid, PCFG.CHAT_POINT, 'chat')


# =====================================================================
#  채팅 순위 (주간 / 전체)
# =====================================================================
def ensure_chat_week() -> None:
    cur = get_week_start()
    if CHAT.data['weekStart'] == cur:
        return
    for users in CHAT.data['guilds'].values():
        for u in users.values():
            u['week'] = 0
    CHAT.data['weekStart'] = cur
    CHAT.save()


def count_chat(gid, uid) -> None:
    ensure_chat_week()
    users = CHAT.data['guilds'].setdefault(str(gid), {})
    u = users.setdefault(str(uid), {'total': 0, 'week': 0})
    u['total'] += 1
    u['week'] += 1
    CHAT.save()


# =====================================================================
#  타자 게임
# =====================================================================
TYPING_SENTENCES = [
    '오늘도 좋은 하루 보내세요',
    '느리더라도 꾸준히 걷는 사람이 결국 멀리 간다',
    '가는 말이 고우면 오는 말이 곱다',
    '천 리 길도 한 걸음부터 시작된다',
    '아침 햇살이 창문 너머로 따뜻하게 들어왔다',
    '비가 그친 뒤 하늘에 선명한 무지개가 떴다',
    '작은 습관 하나가 내일의 나를 바꾼다',
    '시작이 반이라는 말은 정말 맞는 말이다',
    '친구와 함께 먹는 라면은 언제나 맛있다',
    '주말에는 늦잠을 자고 느긋하게 커피를 마시고 싶다',
    '빠르고 정확하게 타자를 치는 연습을 해보자',
    '삶은 선택의 연속이다',
    '책을 읽는 것은 마음의 양식을 쌓는 일이다',
    '자연 속에서 걷는 것은 스트레스를 해소하는 좋은 방법이다',
    '하늘을 바라보며 깊게 숨을 쉬면 마음이 편안해진다',
    '오늘의 날씨는 맑고 화창하다',
    '작은 친절이 큰 행복을 만든다',
    '노력은 배신하지 않는다',
    '웃음은 최고의 약이다',
    '인생은 한 번뿐이다. 후회 없는 선택을 하자',
    '행복은 멀리 있는 것이 아니라 가까이에 있다',
    '성공은 준비된 사람에게 찾아온다',
]
ZWSP = '\u200b'
typing_games: dict[int, dict] = {}   # channel_id -> {started, text, startAt, task}


def count_strokes(text: str) -> int:
    """한글은 자모 단위로 풀어서 '타수'로 계산 (공백 포함)"""
    return len(unicodedata.normalize('NFD', text))


def anti_copy(text: str) -> str:
    """복사-붙여넣기 방지용: 글자 사이에 보이지 않는 문자를 끼워 넣음"""
    return ZWSP.join(text)


def ensure_typing_week() -> None:
    d = TYPING.data
    cur = get_week_start()
    if d['weekStart'] == cur:
        return
    if d['weekStart'] and d['records']:
        top = sorted(d['records'].items(), key=lambda kv: kv[1]['best'], reverse=True)[:3]
        d['lastWeek'] = [{'id': uid, 'best': r['best']} for uid, r in top]
    elif d['weekStart']:
        d['lastWeek'] = []
    d['records'] = {}
    d['weekStart'] = cur
    TYPING.save()


async def typing_timeout(channel, ch_id: int, state: dict) -> None:
    await asyncio.sleep(TYPING_TIMEOUT_MS / 1000)
    if typing_games.get(ch_id) is state:
        typing_games.pop(ch_id, None)
        try:
            await channel.send('⏰ 시간 초과! 아무도 성공하지 못했어요.')
        except discord.HTTPException:
            pass


async def check_typing_answer(message: discord.Message, content: str) -> bool:
    """진행 중인 타자 게임의 정답이면 처리하고 True"""
    game = typing_games.get(message.channel.id)
    if not (game and game['started'] and not content.startswith('!') and content == game['text']):
        return False
    game['task'].cancel()
    typing_games.pop(message.channel.id, None)

    sec = max((message.created_at.timestamp() * 1000 - game['startAt']) / 1000, 0.1)
    spm = round(count_strokes(game['text']) / sec * 60)  # 분당 타수

    ensure_typing_week()
    uid = str(message.author.id)
    rec = TYPING.data['records'].get(uid) or {'best': 0, 'wins': 0}
    is_new_best = spm > rec['best']
    if is_new_best:
        rec['best'] = spm
    rec['wins'] += 1
    TYPING.data['records'][uid] = rec
    TYPING.save()
    if message.guild:
        add_points(message.guild.id, message.author.id, TYPING_REWARD, 'manual')

    e = mk_embed(0xF1C40F, '🏆 타자 게임 우승!', f'<@{message.author.id}> 님이 가장 먼저 정확히 입력했어요!')
    e.add_field(name='⏱️ 걸린 시간', value=f'{sec:.2f}초', inline=True)
    e.add_field(name='⌨️ 속도', value=f'{spm}타/분', inline=True)
    e.add_field(name='🥇 이번 주 최고 기록', value=f"{rec['best']}타/분{' 🎉 신기록!' if is_new_best else ''}", inline=True)
    e.set_footer(text=f"이번 주 우승 {rec['wins']}회 · !타자순위로 순위 확인")
    if message.guild:
        e.add_field(name='💰 보상', value=f'+{TYPING_REWARD}P', inline=True)
    await message.reply(embed=e, allowed_mentions=users_only(message.author.id))
    return True


# =====================================================================
#  가사
# =====================================================================
def norm_title(t: Optional[str]) -> str:
    """띄어쓰기/대소문자/기호 무시용 키"""
    return ''.join(c for c in (t or '').lower() if not (c.isspace() or unicodedata.category(c)[0] in 'PS'))


def _clean_lyrics() -> None:
    raw = LYRICS.data
    cleaned: dict = {}
    for v in raw.values():
        key = norm_title(v.get('title'))
        if not key:
            continue
        if key not in cleaned or (v.get('createdAt') or 0) >= (cleaned[key].get('createdAt') or 0):
            cleaned[key] = v
    if len(cleaned) != len(raw):
        LYRICS.data = cleaned
        LYRICS.save()


def find_lyrics(query: str) -> Optional[dict]:
    q = norm_title(query)
    if not q:
        return None
    if q in LYRICS.data:
        return LYRICS.data[q]
    for key, v in LYRICS.data.items():
        if q in key or (len(q) >= 2 and key in q) is False and False:
            return v
        if key in q or (len(q) >= 2 and q in key):
            return v
    return None


def parse_lyrics_input(text: str) -> Optional[dict]:
    q = re.match(r'^["“”\'‘’]([^"“”\'‘’]+)["“”\'‘’]\s*([\s\S]+)$', text)
    if q:
        return {'title': q.group(1).strip(), 'lyrics': q.group(2).strip()}
    nl = text.find('\n')
    if nl != -1:
        return {'title': text[:nl].strip(), 'lyrics': text[nl + 1:].strip()}
    m = re.search(r'\s', text)
    if not m:
        return None
    return {'title': text[:m.start()], 'lyrics': text[m.start():].strip()}


# =====================================================================
#  타이머
# =====================================================================
timers: dict[int, dict] = {}
_timer_seq = 1
MAX_TIMER_MS = 24 * 60 * 60 * 1000


def parse_duration(text: str) -> Optional[dict]:
    """'10분', '1시간30분 라면', '30초', '5m', '10'(숫자만 쓰면 분) -> {ms, label}"""
    m = re.match(r'^((?:\d+\s*(?:시간|분|초|h|m|s)\s*)+)(.*)$', text, re.I | re.S)
    if m:
        ms = 0
        for n, unit in re.findall(r'(\d+)\s*(시간|분|초|h|m|s)', m.group(1), re.I):
            v = int(n)
            u = unit.lower()
            if u in ('시간', 'h'):
                ms += v * 3600000
            elif u in ('분', 'm'):
                ms += v * 60000
            else:
                ms += v * 1000
        return {'ms': ms, 'label': m.group(2).strip()}
    p = re.match(r'^(\d+)\s*(.*)$', text, re.S)
    if p:
        return {'ms': int(p.group(1)) * 60000, 'label': p.group(2).strip()}
    return None


def format_duration(ms: float) -> str:
    total = max(0, math.ceil(ms / 1000))
    h, m, s = total // 3600, (total % 3600) // 60, total % 60
    parts = []
    if h:
        parts.append(f'{h}시간')
    if m:
        parts.append(f'{m}분')
    if s or not parts:
        parts.append(f'{s}초')
    return ' '.join(parts)


def pick_update_interval(ms: float) -> float:
    """타이머 길이에 따라 메시지 갱신 주기(초)를 다르게 (너무 자주 수정하면 레이트리밋)"""
    if ms <= 60_000:
        return 1
    if ms <= 600_000:
        return 5
    if ms <= 3_600_000:
        return 15
    return 60


async def timer_run(tid: int) -> None:
    t = timers[tid]
    sent, label, uid, channel = t['message'], t['label'], t['userId'], t['channel']
    interval = pick_update_interval(t['total'])
    while True:
        remaining = t['endAt'] - now_ms()
        if remaining <= 0:
            break
        await asyncio.sleep(max(0.05, min(interval, remaining / 1000)))
        remaining = t['endAt'] - now_ms()
        if remaining > 0:
            try:
                await sent.edit(content=f'⏱️ **#{tid}** 남은 시간 **{format_duration(remaining)}** / {label}')
            except Exception:
                pass
    timers.pop(tid, None)
    try:
        await sent.edit(content=f'⏰ **#{tid}** **{label}** 타이머가 끝났어요!')
    except Exception:
        pass
    try:
        if channel is None:
            raise RuntimeError('no channel')
        await channel.send(f'⏰ <@{uid}> **{label}** 타이머가 끝났어요!', allowed_mentions=users_only(uid))
    except Exception:
        # 개인챗(사용자 설치 앱)에서 보낼 수 없다면 DM으로 알림을 시도
        try:
            u = await client.fetch_user(uid)
            await u.send(f'⏰ **{label}** 타이머가 끝났어요!')
        except Exception as err2:
            log.error('타이머 알림 실패: %s', err2)


# =====================================================================
#  날씨 / 노래 검색
# =====================================================================
WEATHER_CODES = {
    0: ('맑음', '☀️'), 1: ('대체로 맑음', '🌤️'), 2: ('구름 조금', '⛅'), 3: ('흐림', '☁️'),
    45: ('안개', '🌫️'), 48: ('짙은 안개', '🌫️'),
    51: ('약한 이슬비', '🌦️'), 53: ('이슬비', '🌦️'), 55: ('강한 이슬비', '🌦️'),
    56: ('약한 어는 이슬비', '🌧️'), 57: ('강한 어는 이슬비', '🌧️'),
    61: ('약한 비', '🌧️'), 63: ('비', '🌧️'), 65: ('강한 비', '🌧️'),
    66: ('약한 어는 비', '🌧️'), 67: ('강한 어는 비', '🌧️'),
    71: ('약한 눈', '🌨️'), 73: ('눈', '🌨️'), 75: ('강한 눈', '❄️'), 77: ('싸락눈', '🌨️'),
    80: ('약한 소나기', '🌦️'), 81: ('소나기', '🌦️'), 82: ('강한 소나기', '⛈️'),
    85: ('약한 눈소나기', '🌨️'), 86: ('강한 눈소나기', '❄️'),
    95: ('뇌우', '⛈️'), 96: ('우박 동반 뇌우', '⛈️'), 99: ('강한 우박 동반 뇌우', '⛈️'),
}


def grade_pm25(v):
    if v is None:
        return ('정보 없음', '⚪', 0x99AAB5)
    if v <= 15:
        return ('좋음', '🔵', 0x3498DB)
    if v <= 35:
        return ('보통', '🟢', 0x2ECC71)
    if v <= 75:
        return ('나쁨', '🟠', 0xE67E22)
    return ('매우 나쁨', '🔴', 0xE74C3C)


def grade_pm10(v):
    if v is None:
        return ('정보 없음', '⚪', 0x99AAB5)
    if v <= 30:
        return ('좋음', '🔵', 0x3498DB)
    if v <= 80:
        return ('보통', '🟢', 0x2ECC71)
    if v <= 150:
        return ('나쁨', '🟠', 0xE67E22)
    return ('매우 나쁨', '🔴', 0xE74C3C)


def wind_dir(deg: float) -> str:
    dirs = ['북', '북동', '동', '남동', '남', '남서', '서', '북서']
    return dirs[round(deg / 45) % 8] + '풍'


async def geocode(name: str) -> Optional[dict]:
    url = f'https://geocoding-api.open-meteo.com/v1/search?name={quote(name)}&count=10&language=ko&format=json'
    data = await fetch_json(url)
    results = data.get('results') or []
    for r in results:
        if r.get('country_code') == 'KR':
            return r
    return results[0] if results else None


async def search_song(query: str) -> Optional[dict]:
    url = f'https://itunes.apple.com/search?term={quote(query)}&media=music&entity=song&limit=1&country=KR'
    data = await fetch_json(url)
    res = data.get('results') or []
    return res[0] if res else None


# =====================================================================
#  ! 명령어 처리 (소유자·허용된 사람 전용 묶음)
# =====================================================================
async def handle_main(message: discord.Message) -> None:
    content = message.content.strip()

    # 💬 채팅 수 집계 + 포인트 (서버 채팅만, 봇 명령어는 제외)
    if message.guild and not content.startswith('!'):
        count_chat(message.guild.id, message.author.id)
        give_point_for_chat(message.guild.id, message.author.id)

    # ⌨️ 진행 중인 타자 게임 정답 확인 (누구나 참여 가능)
    if await check_typing_answer(message, content):
        return

    if not content.startswith('!'):
        return
    uid = message.author.id
    is_owner = is_owner_id(uid)
    if not (is_owner or allowed_has(uid)):   # 소유자도, 허용된 사람도 아니면 무시
        return
    args = content.split()
    cmd = args[0]
    if cmd in OWNER_ONLY and not is_owner:
        await message.reply('이 명령어는 봇 소유자만 사용할 수 있습니다.')
        return
    fn = MAIN_CMDS.get(cmd)
    if fn:
        await fn(PrefixCtx(message), args, content)


@main_cmd('!ping')
async def cmd_ping(ctx: Ctx, args, content):
    sent = await ctx.reply('🏓 측정 중...')
    msg_latency = int(sent.created_at.timestamp() * 1000) - ctx.created_ms
    lat = client.latency
    ws = f'{round(lat * 1000)}ms' if lat == lat else '측정 중'   # NaN 이면 아직 측정 전
    await sent.edit(content=f'🏓 **Pong!**\n📨 메시지 응답 속도: `{msg_latency}ms`\n🌐 디스코드 연결 핑: `{ws}`')


@main_cmd('!목록')
async def cmd_list(ctx: Ctx, args, content):
    e = mk_embed(0x5865F2, '📋 명령어 목록', '`[ ]`는 직접 입력하는 값이에요. 자세한 설명은 **`!설명서`** 를 확인하세요.')
    fields = [
        ('🎮 기본', '`!ping` `!목록` `!설명서`\n`!올멘 [메세지]` `!환영 [@멘션]`'),
        ('💰 포인트', '`!출석` `!잔액 [@멘션]` `!포인트 [@멘션]` `!포인트순위 [채팅/통화]`\n`!출금 [@멘션] [포인트]` `!송금 [후원/송금] [액수] [메세지]`\n`!오늘의운세 [@멘션]`'),
        ('🎰 배팅 게임', '`!동전 [앞/뒤] [포인트]` `!슬롯 [포인트]`\n`!가위바위보 [가위/바위/보] [포인트]` (`!가바보`)'),
        ('🕹️ 게임', '`!타자` `!타자순위`\n`!끝말잇기` `!끝말잇기 봇` `!끝말잇기종료`'),
        ('🏅 레벨', '`!레벨 [@멘션]` `!레벨순위`'),
        ('🎂 생일', '`!생일등록 [닉네임] [월] [일]` `!생일삭제 [닉네임]` `!생일목록 [월]`'),
        ('🔧 편의', '`!아이디 [@멘션]` `!날씨 [지역명]` `!채팅순위` `!서버구성`\n`!가사 [제목]` `!가사등록 [제목] [가사]` `!가사삭제 [제목]` `!가사목록`'),
        ('⏱️ 타이머', '`!타이머 [시간] [메모]` `!타이머목록` `!타이머취소 [번호]`'),
        ('🛡️ 서버 관리', '`!타임아웃 [@멘션] [분]` `!타임아웃해제 [@멘션]`\n`!추방 [@멘션] [사유]` `!차단 [@멘션/ID] [삭제일수] [사유]` `!차단해제 [ID]`\n`!청소 [개수] [@멘션]` `!관리기록 [@멘션/ID]`'),
        ('🎭 반응 역할 · 퇴장 (역할 관리 / 서버 관리)', '`!반응역할패널` `!반응역할추가` `!반응역할제거` `!반응역할목록`\n`!퇴장채널` `!퇴장메시지` `!퇴장테스트` (`!관리도움` 참고)'),
        ('⚙️ 서버 설정 (서버 관리 권한)',
         '`!로그채널` `!환영채널` `!환영메시지` `!환영테스트`\n`!생일채널` `!레벨채널` `!레벨닉네임`\n'
         '`!입금채널` `!출금채널` `!통화입장` `!통화퇴장`\n`!인증역할` `!인증채널` `!인증채널해제` `!함정채널`\n'
         '(채널 설정은 `[#채널]`, 끄려면 뒤에 `해제`)'),
        ('🔐 소유자 전용',
         '`!허용` `!허용해제` `!허용목록`\n`!포인트 추가/제거 [@멘션] [수]` `!포인트수거 [@멘션] [포인트/반/전부]`\n'
         '`!디엠 [사용자ID]` `!관리` `!서버나가기 [서버ID]` `!서버목록 [페이지]`'),
        ('⚡ 슬래시 (/) 명령어',
         '`/ping` `/타이머` `/타이머목록` `/타이머취소` `/타자` `/타자순위`\n`/동전` `/슬롯` `/가위바위보` `/오늘의운세` `/끝말잇기` `/후원`\n`/서버인원` `/서버구성` `/초대링크`'),
        ('🛡️ 돌격대 | 조직 대응', '`/신고` `/신고채널설정` `/사건기록` `/경보` `/대응현황`\n자세한 절차는 `!설명서` 3번째 페이지를 확인하세요.'),
    ]
    for n, v in fields:
        e.add_field(name=n, value=v, inline=False)
    e.set_footer(text='명령어는 ! 로 시작해요 · 자세한 설명은 !설명서')
    await ctx.reply(embed=e)


@main_cmd('!설명서')
async def cmd_manual(ctx: Ctx, args, content):
    rate = round(CFG.TRANSFER_FEE_RATE * 1000) / 10
    bday = '밤 12시(자정)' if CFG.BIRTHDAY_HOUR == 0 else f'낮 {CFG.BIRTHDAY_HOUR}시'

    e1 = mk_embed(0x5865F2, '📖 사용 설명서 (1/3) - 기본 · 포인트 · 게임',
                  '`[ ]`는 직접 입력하는 값, `@멘션`은 멘션 또는 유저 ID예요.\n' +
                  ('💡 **출석·잔액·송금·출금·운세·배팅·끝말잇기·생일·레벨**은 누구나, 나머지는 소유자와 허용된 사람만 쓸 수 있어요.'
                   if CFG.EVERYONE else '💡 소유자와 허용된 사람만 사용할 수 있어요.'))
    e1.add_field(name='🎮 기본', inline=False, value=(
        '`!ping` 반응 속도 확인\n`!올멘 [메세지]` @everyone과 함께 전송 (**서버 관리자** 필요)\n`!환영 @멘션` 환영 인사 보내기'))
    e1.add_field(name='💰 포인트 모으기', inline=False, value=(
        f'• 채팅 {PCFG.CHAT_POINT}P ({PCFG.CHAT_COOLDOWN_MS // 1000}초 쿨타임)\n'
        f'• 통화방 1분당 {PCFG.VOICE_POINT}P (2명 이상, 헤드셋 켠 상태, 잠수방 제외)\n'
        f'• 타자 게임 우승 +{TYPING_REWARD}P\n'
        '`!잔액 [@멘션]` 잔액 확인 · `!포인트 [@멘션]` 순위와 획득 내역\n`!포인트순위 [채팅/통화]` TOP 10'))
    e1.add_field(name='🪙 출석 · 송금 · 출금 · 운세', inline=False, value=(
        f'`!출석` 하루 1번 (한국 시간 자정 기준). 기본 {fmt(CFG.DAILY_BASE)}P + 연속 출석 하루당 +{fmt(CFG.DAILY_STREAK_BONUS)}P '
        f'(최대 {CFG.DAILY_STREAK_MAX}일), 7일 연속마다 +{fmt(CFG.DAILY_WEEK_BONUS)}P\n'
        f'`!출금 @멘션 [포인트]` 상대에게 포인트 전달, 수수료 {rate}% (최소 {fmt(CFG.TRANSFER_MIN)}P) · 내역은 출금 채널에 기록\n'
        '`!송금 [후원/송금] [액수] [메세지]` 내 포인트를 차감하고 입금 채널에 `출금자 ID · 출금액 · 메세지`로 기록\n'
        '`!오늘의운세 [@멘션]` 사람마다, 날마다 다른 운세'))
    e1.add_field(name='🎰 배팅 게임', inline=False, value=(
        '`!동전 [앞/뒤] [포인트]` 맞히면 +배팅액, 틀리면 -배팅액\n'
        '`!슬롯 [포인트]` 3개 일치 x8 (7️⃣ 3개는 x20), 2개 일치 본전, 꽝은 -배팅액\n'
        '`!가위바위보 [가위/바위/보] [포인트]` (`!가바보`) 이기면 +배팅액, 비기면 본전\n'
        f'배팅 {fmt(CFG.MIN_BET)}P ~ {fmt(CFG.MAX_BET)}P · `올인` `반` 가능 · 쿨타임 {CFG.GAMBLE_COOLDOWN_MS // 1000}초'))
    e1.add_field(name='🕹️ 타자 · 끝말잇기', inline=False, value=(
        '`!타자` 나온 문장을 가장 먼저 똑같이 입력하면 우승 (복사 붙여넣기는 인식 안 돼요)\n'
        '`!타자순위` 이번 주 TOP 10 (매주 월요일 0시 초기화)\n'
        '`!끝말잇기` 여럿이 함께 · `!끝말잇기 봇` 봇과 1:1 · `!끝말잇기종료` 시작한 사람/관리자가 종료\n'
        f"• 두음법칙 적용, 한방 단어 금지 ({' '.join(CFG.CHAIN_BANNED_ENDINGS)} 로 끝나는 단어)\n"
        '• 표준국어대사전에 있는 명사만 인정\n'
        f'• ❤️ 목숨 {CFG.CHAIN_LIVES}개: 틀리면 -1, 0개면 탈락\n'
        '• ✅ 성공 · ❌ 글자 불일치 · 🔁 이미 쓴 단어 · ⛔ 연속 입력 · ❓ 사전에 없음 · 🚫 한방 단어 · ⚠️ 사전 확인 실패'))

    e2 = mk_embed(0x5865F2, '📖 사용 설명서 (2/3) - 레벨 · 생일 · 편의 · 타이머')
    e2.add_field(name='🏅 레벨', inline=False, value=(
        f'채팅 {CFG.LEVEL_CHAT_XP_MIN}~{CFG.LEVEL_CHAT_XP_MAX}XP ({CFG.LEVEL_CHAT_COOLDOWN_MS // 1000}초 쿨타임), 통화방 1분당 {CFG.LEVEL_VOICE_XP}XP\n'
        '`!레벨 [@멘션]` 레벨 · 경험치 · 순위 / `!레벨순위` TOP 10\n레벨업 알림 채널은 `!레벨채널`로 지정해요.'))
    e2.add_field(name='🎂 생일', inline=False, value=(
        '`!생일등록 [닉네임] [월] [일]` 예) `!생일등록 철수 3 15`, `!생일등록 @멘션 3 15`, 본인은 `!생일등록 3 15`\n'
        '`!생일삭제 [닉네임]` · `!생일목록 [월]`\n'
        f'생일 당일 {bday}(한국 시간)에 축하 메시지를 보내요. (채널은 `!생일채널`)'))
    e2.add_field(name='🔧 편의', inline=False, value=(
        '`!아이디 [@멘션]` ID 확인 · `!날씨 [지역명]` 날씨와 미세먼지\n'
        '`!채팅순위` 이번 주/전체 TOP 10 · `!서버구성` 인원, 온라인, 봇, 통화방별 인원\n'
        '`!가사 [제목]` 등록된 가사 또는 유튜브 검색 링크\n'
        '`!가사등록 [제목] [가사]` (제목에 띄어쓰기가 있으면 "따옴표") · `!가사삭제 [제목]` · `!가사목록 [페이지]`'))
    e2.add_field(name='⏱️ 타이머', inline=False, value=(
        '`!타이머 [시간] [메모]` 예) `10분`, `1시간30분 라면`, `30초` (숫자만 쓰면 분)\n'
        '`!타이머목록` 내 타이머 확인 · `!타이머취소 [번호]`\n최대 24시간, 한 사람당 5개까지'))

    e3 = mk_embed(0x5865F2, '📖 사용 설명서 (3/3) - 관리 · 슬래시 · 조직 대응')
    e3.add_field(name='🛡️ 서버 관리 (봇에게 권한 필요)', inline=False, value=(
        '`!타임아웃 @멘션 [분] [사유]` 채팅 금지 (생략 시 10분) · `!타임아웃해제 @멘션`\n'
        '`!추방 @멘션 [사유]` · `!차단 @멘션/ID [삭제일수 0~7] [사유]` · `!차단해제 [ID]`\n'
        '`!청소 [개수] [@멘션]` 메시지 삭제 (1~100개) · `!관리기록 [@멘션/ID]` 관리 행동 기록 조회'))
    e3.add_field(name='🎭 반응 역할 · 퇴장 메시지', inline=False, value=(
        '`!반응역할패널 제목 | 설명` → `!반응역할추가 [메시지ID/링크] [이모지] @역할`\n'
        '`!반응역할제거` · `!반응역할목록` (역할 관리 권한)\n'
        '`!퇴장채널 #채널` · `!퇴장메시지 [내용]` · `!퇴장테스트` (서버 관리 권한) 변수 `{유저}` `{유저명}` `{서버명}` `{인원}`'))
    e3.add_field(name='⚙️ 서버 설정 (서버 관리 권한 필요)', inline=False, value=(
        '`!로그채널` 입퇴장, 메시지 삭제·수정, 역할·타임아웃, 통화 시간 기록\n'
        '`!환영채널` 새 멤버 자동 환영 · `!환영메시지 [내용]` 변수 `{유저}` `{서버명}` `{인원}` · `!환영테스트`\n'
        '`!생일채널` 생일 축하 · `!레벨채널` 레벨업 알림\n'
        '`!입금채널` 송금·후원 내역 · `!출금채널` `!출금` 내역 (미설정 시 입금채널로 전송)\n'
        '`!레벨닉네임 켜기/끄기/갱신/제거 [@멘션]` 닉네임 앞에 `[Lv.N]` (봇에게 닉네임 관리 권한 필요)\n'
        '`!통화입장 [#음성채널]` · `!통화퇴장` 봇이 통화방에 계속 상주\n'
        '`!인증역할 @역할` 반응하면 지급할 역할 지정\n'
        '`!인증채널 #채널` 그 채널에 인증 메시지를 보내고 ✅ 반응 달기 · `!인증채널해제`\n'
        '`!함정채널 #채널` 그 채널에 글을 쓰면 즉시 추방 · `!함정채널해제`\n채널 설정은 `!○○채널 #채널`, 끄기는 `!○○채널해제`'))
    e3.add_field(name='⚡ 슬래시 (/) 명령어', inline=False, value=(
        '`/ping` `/타이머` `/타이머목록` `/타이머취소` `/타자` `/타자순위`\n'
        '`/동전` `/슬롯` `/가위바위보` `/오늘의운세` `/끝말잇기` `/후원`\n'
        '`/서버인원` `/서버구성` `/초대링크`\n디스코드 입력창에 `/`를 입력해 선택하세요.'))
    e3.add_field(name='🛡️ 돌격대 | 조직 운영 지침', inline=False, value=(
        '**목적** 테러 활동을 예방하고 관련 위협에 대응하여 구성원의 안전을 지킨다.\n'
        '**절차** `/신고`로 접수 → 관리자 검토·사실 확인 → 필요 시 증거 보존 후 관계 기관 전달 → `/사건기록`으로 상태 갱신 → `/대응현황`으로 확인\n'
        '**관리자 전용** `/신고채널설정` `/사건기록` `/경보` `/대응현황`\n'
        '**긴급 상황** 즉각적인 위험이 있으면 현지 긴급 신고 기관에 먼저 연락한다.\n'
        '**원칙** 확인되지 않은 혐의를 단정하지 않고, 개인정보와 기록을 보호하며, 합법적인 신고와 기관 협력을 우선한다.'))
    e3.add_field(name='🔐 소유자 전용', inline=False, value=(
        '`!허용 @멘션/ID` `!허용해제 @멘션/ID` `!허용목록` 봇 사용 권한 관리\n'
        '`!포인트 추가/제거 @멘션 [수]` · `!포인트수거 @멘션 [포인트/반/전부]`\n'
        '`!디엠 [사용자ID]` `!관리` `!서버나가기 [서버ID]` `!서버목록 [페이지]`'))
    e3.set_footer(text='명령어만 빠르게 보려면 !목록')

    await ctx.reply(embed=e1)
    await ctx.channel.send(embed=e2)
    await ctx.channel.send(embed=e3)


@main_cmd('!올멘')
async def cmd_everyone(ctx: Ctx, args, content):
    if not (ctx.member and ctx.member.guild_permissions.administrator):
        return await ctx.reply('이 명령어는 **관리자 권한**이 있는 사람만 사용할 수 있어요.')
    text = content[len(args[0]):].strip()
    if not text:
        return await ctx.reply('보낼 메세지를 입력해주세요! 예: `!올멘 오늘 8시에 모여요`')
    if len(text) > 1900:
        return await ctx.reply('메세지는 1900자 이내로 입력해주세요.')
    await ctx.channel.send(f'@everyone {text}', allowed_mentions=discord.AllowedMentions(everyone=True))


@main_cmd('!환영')
async def cmd_welcome_user(ctx: Ctx, args, content):
    tid = ctx.first_mention or parse_id(args[1] if len(args) > 1 else None)
    target = None
    if tid:
        try:
            target = await client.fetch_user(tid)
        except discord.HTTPException:
            target = None
    if not target:
        return await ctx.reply('환영할 사람을 멘션해주세요! 예: `!환영 @닉네임`')
    if target.bot:
        return await ctx.reply('봇은 환영하지 않아도 괜찮아요 🤖')
    server = ctx.guild.name if ctx.guild else '이곳'
    greeting = random.choice([
        '와주셔서 정말 반가워요! 편하게 즐겨주세요 😊',
        '함께하게 되어 기뻐요! 많이 놀아주세요 🎉',
        '오신 걸 진심으로 환영합니다! 자주 놀러 와주세요 🙌',
        '새로운 얼굴이네요! 같이 재밌게 지내봐요 ✨',
    ])
    e = mk_embed(0xFF9FF3, f'🎉 {server}에 오신 것을 환영합니다!', f'<@{target.id}> 님, {greeting}', ts=True)
    e.set_thumbnail(url=avatar_url(target))
    e.set_footer(text=f'{ctx.user.name} 님이 환영 인사를 보냈어요')
    await ctx.channel.send(f'<@{target.id}>', embed=e, allowed_mentions=users_only(target.id))


@main_cmd('!날씨')
async def cmd_weather(ctx: Ctx, args, content):
    region = content[len(args[0]):].strip()
    if not region:
        return await ctx.reply('지역명을 입력해주세요! 예: `!날씨 서울`, `!날씨 여수`')
    try:
        async with ctx.channel.typing():
            # "여수시" 처럼 검색이 안 되면 끝의 시/군/구/도를 떼고 한 번 더 시도
            place = await geocode(region)
            if not place and re.search(r'[시군구도]$', region) and len(region) > 2:
                place = await geocode(region[:-1])
            if not place:
                return await ctx.reply(f"'{region}' 지역을 찾을 수 없어요. 다른 이름으로 시도해보세요.")
            lat, lon = place['latitude'], place['longitude']
            weather_url = (f'https://api.open-meteo.com/v1/forecast?latitude={lat}&longitude={lon}'
                           '&current=temperature_2m,apparent_temperature,relative_humidity_2m,precipitation,weather_code,wind_speed_10m,wind_direction_10m'
                           '&daily=temperature_2m_max,temperature_2m_min,precipitation_probability_max'
                           '&wind_speed_unit=ms&timezone=auto&forecast_days=1')
            air_url = f'https://air-quality-api.open-meteo.com/v1/air-quality?latitude={lat}&longitude={lon}&current=pm10,pm2_5&timezone=auto'

            async def safe_air():
                try:
                    return await fetch_json(air_url)
                except Exception:
                    return None   # 미세먼지 실패해도 날씨는 표시

            weather, air = await asyncio.gather(fetch_json(weather_url), safe_air())
        cur, day = weather['current'], weather['daily']
        desc, icon = WEATHER_CODES.get(cur['weather_code'], ('알 수 없음', '❔'))
        pm25 = (air or {}).get('current', {}).get('pm2_5')
        pm10 = (air or {}).get('current', {}).get('pm10')
        g25, g10 = grade_pm25(pm25), grade_pm10(pm10)
        place_name = ', '.join(x for x in (place.get('name'), place.get('admin1'), place.get('country')) if x)
        pop = day['precipitation_probability_max'][0]
        e = mk_embed(g25[2] if air else 0x5865F2, f"{icon} {place['name']} 날씨", f'{place_name}\n**{desc}**', ts=True)
        e.add_field(name='🌡️ 현재 기온', value=f"{cur['temperature_2m']}°C (체감 {cur['apparent_temperature']}°C)", inline=True)
        e.add_field(name='📊 오늘 최저/최고', value=f"{day['temperature_2m_min'][0]}°C / {day['temperature_2m_max'][0]}°C", inline=True)
        e.add_field(name='☔ 강수확률', value=f"{pop if pop is not None else 0}%", inline=True)
        e.add_field(name='💧 습도', value=f"{cur['relative_humidity_2m']}%", inline=True)
        e.add_field(name='🌬️ 바람', value=f"{wind_dir(cur['wind_direction_10m'])} {cur['wind_speed_10m']}m/s", inline=True)
        e.add_field(name='🌧️ 강수량', value=f"{cur['precipitation']}mm", inline=True)
        e.add_field(name='😷 미세먼지 (PM10)', inline=True,
                    value=f'{g10[1]} {g10[0]} ({round(pm10)}㎍/㎥)' if pm10 is not None else '정보 없음')
        e.add_field(name='😷 초미세먼지 (PM2.5)', inline=True,
                    value=f'{g25[1]} {g25[0]} ({round(pm25)}㎍/㎥)' if pm25 is not None else '정보 없음')
        e.set_footer(text='데이터: Open-Meteo · 미세먼지는 모델 추정값이라 에어코리아와 다를 수 있어요')
        await ctx.reply(embed=e)
    except Exception as err:
        log.error('날씨 조회 실패: %s', err)
        await ctx.reply('날씨 정보를 가져오지 못했어요. 잠시 후 다시 시도해주세요.')


@main_cmd('!타자')
async def cmd_typing(ctx: Ctx, args, content):
    ch_id = ctx.channel.id
    if ch_id in typing_games:
        return await ctx.reply('이 채널에서 이미 타자 게임이 진행 중이에요!')
    state = {'started': False, 'text': '', 'startAt': 0, 'task': None}
    typing_games[ch_id] = state
    try:
        await ctx.reply('⌨️ **타자 게임 시작!** 3초 뒤 문장이 나와요. 나온 문장을 **그대로 입력**하세요! (복사 붙여넣기는 인식되지 않아요)')
        await asyncio.sleep(3)
        text = random.choice(TYPING_SENTENCES)
        sent = await ctx.send(f'```\n{anti_copy(text)}\n```')
        state['text'] = text
        state['startAt'] = sent.created_at.timestamp() * 1000
        state['started'] = True
        state['task'] = asyncio.create_task(typing_timeout(ctx.channel, ch_id, state))
    except Exception as err:
        log.error('타자 게임 시작 실패: %s', err)
        typing_games.pop(ch_id, None)
        try:
            await ctx.channel.send('타자 게임을 시작하지 못했어요. (봇 권한을 확인해주세요)')
        except Exception:
            pass


@main_cmd('!타자순위')
async def cmd_typing_rank(ctx: Ctx, args, content):
    ensure_typing_week()
    d = TYPING.data
    next_reset = unix(d['weekStart'] + WEEK_MS)
    ranking = sorted(d['records'].items(), key=lambda kv: kv[1]['best'], reverse=True)[:10]
    lines = [f"{MEDALS[i] if i < 3 else f'**{i + 1}.**'} <@{uid}> - {r['best']}타/분 (우승 {r['wins']}회)"
             for i, (uid, r) in enumerate(ranking)] or ['이번 주 기록이 아직 없어요. `!타자`로 게임을 시작해보세요!']
    e = mk_embed(0xF1C40F, '🏆 이번 주 타자 게임 순위 TOP 10',
                 '\n'.join(lines) + f'\n\n🔄 다음 초기화: <t:{next_reset}:R> (매주 월요일 0시)')
    if d['lastWeek']:
        e.add_field(name='📅 지난주 TOP 3', inline=False,
                    value='\n'.join(f"{MEDALS[i]} <@{r['id']}> - {r['best']}타/분" for i, r in enumerate(d['lastWeek'])))
    await ctx.reply(embed=e, mentions=NO_MENTIONS)


@main_cmd('!포인트')
async def cmd_points(ctx: Ctx, args, content):
    if not ctx.guild:
        return await ctx.reply('서버 안에서만 사용할 수 있습니다.')
    gid = ctx.guild.id
    sub = args[1] if len(args) > 1 else None
    if sub in ('추가', '제거'):
        if not is_owner_id(ctx.user.id):
            return await ctx.reply('포인트 추가/제거는 봇 소유자만 사용할 수 있습니다.')
        tid = ctx.first_mention or parse_id(args[2] if len(args) > 2 else None)
        amount = pint(args[3] if len(args) > 3 else None)
        if not tid or amount is None or amount < 1 or amount > PCFG.MAX_MANUAL:
            return await ctx.reply(f'사용법: `!포인트 {sub} @멘션 [포인트]` (1 ~ {PCFG.MAX_MANUAL:,})')
        u = get_point_user(gid, tid)
        before = u['points']
        add_points(gid, tid, amount if sub == '추가' else -amount, 'manual')
        return await ctx.reply(
            f"{'➕' if sub == '추가' else '➖'} <@{tid}> 님의 포인트를 {amount:,}P {sub}했어요.\n💰 {before:,}P → **{u['points']:,}P**",
            mentions=NO_MENTIONS)
    tid = ctx.first_mention or parse_id(sub) or ctx.user.id
    u = get_point_user(gid, tid)
    ranking = sorted(((k, v) for k, v in POINTS.data['guilds'].get(str(gid), {}).items() if v['points'] > 0),
                     key=lambda kv: kv[1]['points'], reverse=True)
    rank = next((i for i, (k, _) in enumerate(ranking) if k == str(tid)), -1)
    e = mk_embed(0xF1C40F, '💰 포인트', f'<@{tid}> 님의 포인트')
    e.add_field(name='💰 보유 포인트', value=f"{u['points']:,}P", inline=True)
    e.add_field(name='🏆 순위', value=f'{rank + 1}위' if rank >= 0 else '순위 없음', inline=True)
    e.add_field(name='\u200b', value='\u200b', inline=True)
    e.add_field(name='💬 채팅으로 얻은 포인트', value=f"{u['chat']:,}P", inline=True)
    e.add_field(name='🔊 통화로 얻은 포인트', value=f"{u['voice']:,}P", inline=True)
    e.set_footer(text=f'채팅 {PCFG.CHAT_POINT}P ({PCFG.CHAT_COOLDOWN_MS // 1000}초 쿨타임) · 통화 1분당 {PCFG.VOICE_POINT}P')
    await ctx.reply(embed=e, mentions=NO_MENTIONS)


@main_cmd('!포인트순위')
async def cmd_points_rank(ctx: Ctx, args, content):
    if not ctx.guild:
        return await ctx.reply('서버 안에서만 사용할 수 있습니다.')
    kind = args[1] if len(args) > 1 else None
    key, title = {'채팅': ('chat', '💬 채팅 포인트 순위'), '통화': ('voice', '🔊 통화 포인트 순위')}.get(
        kind, ('points', '💰 전체 포인트 순위'))
    users = POINTS.data['guilds'].get(str(ctx.guild.id), {})
    lst = sorted(((k, v) for k, v in users.items() if v[key] > 0), key=lambda kv: kv[1][key], reverse=True)
    lines = '\n'.join(f"{MEDALS[i] if i < 3 else f'**{i + 1}.**'} <@{k}> - {v[key]:,}P"
                      for i, (k, v) in enumerate(lst[:10])) or '아직 기록이 없어요.'
    my = next((i for i, (k, _) in enumerate(lst) if k == str(ctx.user.id)), -1)
    e = mk_embed(0xF1C40F, f'{title} TOP 10', lines)
    e.set_footer(text=f"내 순위 - {f'{my + 1}위 ({lst[my][1][key]:,}P)' if my >= 0 else '기록 없음'} · !포인트순위 [채팅/통화]")
    await ctx.reply(embed=e, mentions=NO_MENTIONS)


@main_cmd('!채팅순위')
async def cmd_chat_rank(ctx: Ctx, args, content):
    if not ctx.guild:
        return await ctx.reply('서버 안에서만 사용할 수 있습니다.')
    ensure_chat_week()
    users = CHAT.data['guilds'].get(str(ctx.guild.id), {})

    def rank(key):
        return sorted(((k, v) for k, v in users.items() if v[key] > 0), key=lambda kv: kv[1][key], reverse=True)

    def fmt_list(lst, key):
        return '\n'.join(f"{MEDALS[i] if i < 3 else f'**{i + 1}.**'} <@{k}> - {v[key]:,}개"
                         for i, (k, v) in enumerate(lst[:10])) or '아직 기록이 없어요.'

    total, week = rank('total'), rank('week')
    my_t = next((i for i, (k, _) in enumerate(total) if k == str(ctx.user.id)), -1)
    my_w = next((i for i, (k, _) in enumerate(week) if k == str(ctx.user.id)), -1)
    me = users.get(str(ctx.user.id), {})
    e = mk_embed(0x5865F2, f'💬 {ctx.guild.name} 채팅 순위',
                 f"🔄 주간 순위 초기화: <t:{unix(CHAT.data['weekStart'] + WEEK_MS)}:R> (매주 월요일 0시)")
    e.add_field(name='🔥 이번 주 TOP 10', value=fmt_list(week, 'week'), inline=False)
    e.add_field(name='🏆 전체 TOP 10', value=fmt_list(total, 'total'), inline=False)
    e.set_footer(text='내 순위 - 이번 주 ' + (f"{my_w + 1}위 ({me['week']:,}개)" if my_w >= 0 else '기록 없음') +
                 ' · 전체 ' + (f"{my_t + 1}위 ({me['total']:,}개)" if my_t >= 0 else '기록 없음'))
    await ctx.reply(embed=e, mentions=NO_MENTIONS)


@main_cmd('!서버구성')
async def cmd_server_info(ctx: Ctx, args, content):
    g = ctx.guild
    if not g:
        return await ctx.reply('서버 안에서만 사용할 수 있습니다.')
    try:
        if not g.chunked:
            await g.chunk()   # 전체 멤버 캐시 확보 (멤버/프레즌스 인텐트 필요)
        members = g.members
        total = len(members)
        bots = sum(1 for m in members if m.bot)
        online = sum(1 for m in members if not m.bot and m.status != discord.Status.offline)
        vcs = sorted(g.voice_channels, key=lambda c: c.position)
        voice_total = sum(len(c.members) for c in vcs)
        voice_lines = '\n'.join(f'🔊 {c.name} - **{len(c.members)}**명' for c in vcs) or '음성 채널이 없어요.'
        e = mk_embed(0x5865F2, f'🧩 {g.name} 서버 구성', ts=True)
        e.add_field(name='👥 전체 인원', value=f'{total}명', inline=True)
        e.add_field(name='🙋 유저', value=f'{total - bots}명', inline=True)
        e.add_field(name='🤖 봇', value=f'{bots}명', inline=True)
        e.add_field(name='🟢 온라인', value=f'{online}명', inline=True)
        e.add_field(name='🔊 통화 중', value=f'{voice_total}명', inline=True)
        e.add_field(name='\u200b', value='\u200b', inline=True)
        e.add_field(name='🔊 통화방별 인원', value=clip(voice_lines, 1000), inline=False)
        if g.icon:
            e.set_thumbnail(url=g.icon.with_size(256).url)
        await ctx.reply(embed=e)
    except Exception as err:
        log.error('서버구성 조회 실패: %s', err)
        await ctx.reply('서버 정보를 가져오지 못했어요.\n디스코드 개발자 포털 > Bot 탭에서 **SERVER MEMBERS INTENT**와 **PRESENCE INTENT**가 켜져 있는지 확인해주세요.')


# ---------- 가사 ----------
@main_cmd('!가사등록')
async def cmd_lyrics_add(ctx: Ctx, args, content):
    parsed = parse_lyrics_input(content[len(args[0]):].strip())
    if not parsed or not parsed['title'] or not parsed['lyrics']:
        return await ctx.reply('사용법: `!가사등록 노래제목 가사내용`\n제목에 띄어쓰기가 있으면 따옴표로 묶어주세요. 예: `!가사등록 "노래 제목" 가사...`\n또는 첫 줄에 제목, 다음 줄부터 가사를 써도 돼요.')
    if len(parsed['title']) > 100:
        return await ctx.reply('제목은 100자 이내로 입력해주세요.')
    key = norm_title(parsed['title'])
    if not key:
        return await ctx.reply('제목에 글자나 숫자가 하나 이상 있어야 해요.')
    existing = LYRICS.data.get(key)
    LYRICS.data[key] = {'title': parsed['title'], 'lyrics': parsed['lyrics'], 'userId': str(ctx.user.id), 'createdAt': now_ms()}
    LYRICS.save()
    await ctx.reply(f"♻️ 이미 있던 **{parsed['title']}** 가사를 새 내용으로 교체했어요. (중복 없이 1개만 유지돼요)" if existing
                    else f"✅ **{parsed['title']}** 가사를 등록했어요! `!가사 {parsed['title']}`로 확인할 수 있어요.")


@main_cmd('!가사목록')
async def cmd_lyrics_list(ctx: Ctx, args, content):
    entries = sorted(LYRICS.data.values(), key=lambda v: v['title'])
    if not entries:
        return await ctx.reply('등록된 가사가 없어요. `!가사등록 노래제목 가사내용`으로 등록해보세요!')
    per = 15
    pages = math.ceil(len(entries) / per)
    page = min(max(pint(args[1] if len(args) > 1 else None) or 1, 1), pages)
    start = (page - 1) * per
    lines = [f"**{start + i + 1}.** {v['title']}  ·  <@{v['userId']}>" for i, v in enumerate(entries[start:start + per])]
    e = mk_embed(0x1DB954, f'📚 등록된 가사 목록 ({len(entries)}곡)', '\n'.join(lines))
    e.set_footer(text=f'{page}/{pages} 페이지' + (' · !가사목록 [페이지]' if pages > 1 else '') + ' · !가사 [제목]으로 보기')
    await ctx.reply(embed=e, mentions=NO_MENTIONS)


@main_cmd('!가사삭제')
async def cmd_lyrics_del(ctx: Ctx, args, content):
    title = re.sub(r'^["“”\'‘’]|["“”\'‘’]$', '', content[len(args[0]):].strip())
    if not title:
        return await ctx.reply('삭제할 노래 제목을 입력해주세요! 예: `!가사삭제 노래제목`')
    key = norm_title(title)
    entry = LYRICS.data.get(key)
    if not entry:
        return await ctx.reply('등록된 가사가 없어요. 제목을 정확히 입력해주세요.')
    if entry['userId'] != str(ctx.user.id) and not is_owner_id(ctx.user.id):
        return await ctx.reply('다른 사람이 등록한 가사는 삭제할 수 없어요.')
    del LYRICS.data[key]
    LYRICS.save()
    await ctx.reply(f"🗑️ **{entry['title']}** 가사를 삭제했어요.")


@main_cmd('!가사')
async def cmd_lyrics(ctx: Ctx, args, content):
    query = content[len(args[0]):].strip()
    if not query:
        return await ctx.reply('노래 제목을 입력해주세요! 예: `!가사 봄날 방탄소년단`')
    saved = find_lyrics(query)
    if saved:
        e = mk_embed(0x1DB954, f"🎶 {saved['title']}", saved['lyrics'][:4000])
        e.set_footer(text='사용자가 등록한 가사예요')
        e.timestamp = datetime.fromtimestamp((saved.get('createdAt') or now_ms()) / 1000, tz=timezone.utc)
        return await ctx.reply(embed=e)
    try:
        async with ctx.channel.typing():
            song = await search_song(query)
        title = f"{song['artistName']} {song['trackName']}" if song else query
        links = (f"[▶️ 유튜브에서 가사 영상 검색](https://www.youtube.com/results?search_query={quote(title + ' 가사')})\n"
                 f"[🎬 유튜브에서 MV 검색](https://www.youtube.com/results?search_query={quote(title + ' MV')})")
        e = mk_embed(0x1DB954, ts=True)
        if song:
            e.title = f"🎶 {song['trackName']}"
            e.description = f"**{song['artistName']}**\n💿 {song.get('collectionName') or '-'}"
            art = (song.get('artworkUrl100') or '').replace('100x100', '300x300')
            if art:
                e.set_thumbnail(url=art)
            e.add_field(name='📅 발매일', value=(song.get('releaseDate') or '')[:10] or '정보 없음', inline=True)
            e.add_field(name='📄 가사 보기 (유튜브)', value=links, inline=False)
            if song.get('trackViewUrl'):
                e.url = song['trackViewUrl']
        else:
            e.title = f"🔎 '{query}'"
            e.description = '곡 정보를 찾지 못했어요. 아래 링크로 유튜브에서 직접 검색해보세요.'
            e.add_field(name='📄 가사 보기 (유튜브)', value=links, inline=False)
        e.set_footer(text='가사는 저작권 보호 대상이라 유튜브 검색 링크로 안내해요')
        await ctx.reply(embed=e)
    except Exception as err:
        log.error('가사 검색 실패: %s', err)
        await ctx.reply('노래 정보를 가져오지 못했어요. 잠시 후 다시 시도해주세요.')


# ---------- 타이머 ----------
@main_cmd('!타이머')
async def cmd_timer(ctx: Ctx, args, content):
    global _timer_seq
    parsed = parse_duration(content[len(args[0]):].strip())
    if not parsed or parsed['ms'] <= 0:
        return await ctx.reply('시간을 입력해주세요! 예: `!타이머 10분`, `!타이머 1시간30분 라면`, `!타이머 30초`')
    if parsed['ms'] > MAX_TIMER_MS:
        return await ctx.reply('타이머는 최대 24시간까지 설정할 수 있어요.')
    if sum(1 for t in timers.values() if t['userId'] == ctx.user.id) >= 5:
        return await ctx.reply('타이머는 한 사람당 최대 5개까지 만들 수 있어요. `!타이머취소 [번호]`로 정리해주세요.')
    tid = _timer_seq
    _timer_seq += 1
    label = parsed['label'] or '타이머'
    sent = await ctx.reply(f"⏱️ **#{tid}** 타이머 시작! 남은 시간 **{format_duration(parsed['ms'])}** / {label}")
    t = {'userId': ctx.user.id, 'channel': ctx.channel, 'endAt': now_ms() + parsed['ms'], 'total': parsed['ms'],
         'label': label, 'message': sent}
    timers[tid] = t
    t['task'] = asyncio.create_task(timer_run(tid))


@main_cmd('!타이머목록')
async def cmd_timer_list(ctx: Ctx, args, content):
    mine = [(i, t) for i, t in timers.items() if t['userId'] == ctx.user.id]
    if not mine:
        return await ctx.reply('진행 중인 타이머가 없어요.')
    lines = [f"**#{i}** {t['label']} - 남은 시간 {format_duration(t['endAt'] - now_ms())}" for i, t in mine]
    await ctx.reply(f'**내 타이머 {len(mine)}개**\n' + '\n'.join(lines))


@main_cmd('!타이머취소')
async def cmd_timer_cancel(ctx: Ctx, args, content):
    tid = pint(args[1] if len(args) > 1 else None)
    if tid is None:
        return await ctx.reply('취소할 타이머 번호를 입력해주세요! 예: `!타이머취소 1` (번호는 `!타이머목록`에서 확인)')
    t = timers.get(tid)
    if not t:
        return await ctx.reply('그런 번호의 타이머가 없어요.')
    if t['userId'] != ctx.user.id and not is_owner_id(ctx.user.id):
        return await ctx.reply('다른 사람의 타이머는 취소할 수 없어요.')
    t['task'].cancel()
    timers.pop(tid, None)
    try:
        await t['message'].edit(content=f"🗑️ **#{tid}** {t['label']} 타이머가 취소되었어요.")
    except Exception:
        pass
    await ctx.reply(f'🗑️ **#{tid}** 타이머를 취소했어요.')


# ---------- 허용 관리 (소유자 전용) ----------
@main_cmd('!허용')
async def cmd_allow(ctx: Ctx, args, content):
    i = parse_id(args[1] if len(args) > 1 else None)
    if not i:
        return await ctx.reply('허용할 사람을 멘션하거나 ID를 입력해주세요! 예: !허용 123456789012345678')
    if is_owner_id(i):
        return await ctx.reply('소유자는 이미 모든 권한이 있어요.')
    if allowed_has(i):
        return await ctx.reply('이미 허용된 사용자입니다.')
    ALLOWED.data.append(str(i))
    ALLOWED.save()
    await ctx.reply(f'✅ <@{i}> (`{i}`) 님을 허용 목록에 추가했습니다.')


@main_cmd('!허용해제')
async def cmd_disallow(ctx: Ctx, args, content):
    i = parse_id(args[1] if len(args) > 1 else None)
    if not i:
        return await ctx.reply('해제할 사람을 멘션하거나 ID를 입력해주세요! 예: !허용해제 123456789012345678')
    if not allowed_has(i):
        return await ctx.reply('허용 목록에 없는 사용자입니다.')
    ALLOWED.data.remove(str(i))
    ALLOWED.save()
    await ctx.reply(f'🚫 `{i}` 님을 허용 목록에서 제거했습니다.')


@main_cmd('!허용목록')
async def cmd_allow_list(ctx: Ctx, args, content):
    if not ALLOWED.data:
        return await ctx.reply('허용된 사용자가 없습니다.')
    lst = '\n'.join(f'{n + 1}. <@{i}> (`{i}`)' for n, i in enumerate(ALLOWED.data))
    await ctx.reply(f'**허용된 사용자 {len(ALLOWED.data)}명**\n{lst}', mentions=NO_MENTIONS)


# ---------- 서버 관리 ----------
@main_cmd('!청소')
async def cmd_purge(ctx: Ctx, args, content):
    if not ctx.guild:
        return await ctx.reply('서버 안에서만 사용할 수 있습니다.')
    rest = [a for a in args[1:] if not a.startswith('<@')]
    amount = pint(rest[0] if rest else None)
    target_id = ctx.first_mention
    if amount is None or amount < 1 or amount > 100:
        return await ctx.reply('삭제할 개수를 1~100 사이로 입력해주세요! 예: !청소 10  /  !청소 20 @닉네임')
    try:
        try:
            await ctx.message.delete()
        except discord.HTTPException:
            pass
        cutoff = discord.utils.utcnow() - timedelta(days=14)   # 14일 지난 메시지는 디스코드가 일괄 삭제를 못 해요
        if target_id:
            found = [m async for m in ctx.channel.history(limit=100) if m.author.id == target_id and m.created_at > cutoff][:amount]
            if found:
                await ctx.channel.delete_messages(found)
            count = len(found)
        else:
            count = len(await ctx.channel.purge(limit=amount, after=cutoff))
        log_action(ctx.guild.id, ctx.user.id, target_id or ctx.channel.id, '청소', None, count)
        notice = await ctx.channel.send(f'🧹 메시지 {count}개를 삭제했습니다.')
        await notice.delete(delay=3)
    except Exception as err:
        log.error('청소 실패: %s', err)
        await ctx.channel.send('메시지 삭제에 실패했습니다. (봇 권한을 확인해주세요)')


def _first_member(ctx: Ctx) -> Optional[discord.Member]:
    for m in ctx.message.mentions:
        if isinstance(m, discord.Member):
            return m
    return None


@main_cmd('!추방')
async def cmd_kick(ctx: Ctx, args, content):
    if not ctx.guild:
        return await ctx.reply('서버 안에서만 사용할 수 있습니다.')
    target = _first_member(ctx)
    if not target:
        return await ctx.reply('추방할 사람을 멘션해주세요! 예: !추방 @닉네임 사유')
    reason = ' '.join(a for a in args[1:] if not a.startswith('<@')) or '사유 없음'
    if target.id == ctx.user.id:
        return await ctx.reply('본인은 추방할 수 없어요 😅')
    if target.id == client.user.id:
        return await ctx.reply('저는 스스로를 추방할 수 없어요 😢')
    if is_owner_id(target.id):
        return await ctx.reply('소유자는 추방할 수 없습니다.')
    if not (can_manage(ctx.guild, target) and ctx.guild.me.guild_permissions.kick_members):
        return await ctx.reply('이 사람은 추방할 수 없습니다. (봇보다 높은 역할이거나 서버 소유자일 수 있어요)')
    try:
        await target.kick(reason=f'{reason} (by {ctx.user.name})'[:512])
        log_action(ctx.guild.id, ctx.user.id, target.id, '추방', reason)
        await ctx.reply(f'👢 {target} 님을 추방했습니다. (사유: {reason})')
    except Exception as err:
        log.error('추방 실패: %s', err)
        await ctx.reply('추방에 실패했습니다. (봇 권한을 확인해주세요)')


@main_cmd('!타임아웃해제')
async def cmd_untimeout(ctx: Ctx, args, content):
    target = _first_member(ctx) if ctx.guild else None
    if not target:
        return await ctx.reply('해제할 사람을 멘션해주세요! 예: !타임아웃해제 @닉네임')
    try:
        await target.timeout(None)
        log_action(ctx.guild.id, ctx.user.id, target.id, '타임아웃해제')
        await ctx.reply(f'{target} 님의 타임아웃을 해제했습니다.')
    except Exception as err:
        log.error('타임아웃 해제 실패: %s', err)
        await ctx.reply('타임아웃을 해제할 수 없습니다. (봇 권한을 확인해주세요)')


@main_cmd('!타임아웃')
async def cmd_timeout(ctx: Ctx, args, content):
    if not ctx.guild:
        return await ctx.reply('서버 안에서만 사용할 수 있습니다.')
    target = _first_member(ctx)
    if not target:
        return await ctx.reply('타임아웃할 사람을 멘션해주세요! 예: !타임아웃 @닉네임 10 도배')
    rest = [a for a in args[1:] if not a.startswith('<@')]
    minutes = pint(rest[0] if rest else None)
    if minutes is None:
        minutes, reason = 10, ' '.join(rest) or '사유 없음'
    else:
        reason = ' '.join(rest[1:]) or '사유 없음'
    if minutes < 1 or minutes > 40320:
        return await ctx.reply('시간은 1분 ~ 40320분(28일) 사이로 입력해주세요.')
    if target.id == ctx.user.id:
        return await ctx.reply('본인은 타임아웃할 수 없어요 😅')
    if is_owner_id(target.id):
        return await ctx.reply('소유자는 타임아웃할 수 없습니다.')
    moderatable = (can_manage(ctx.guild, target) and ctx.guild.me.guild_permissions.moderate_members
                   and not target.guild_permissions.administrator)
    if not moderatable:
        return await ctx.reply('이 사람은 타임아웃할 수 없습니다. (봇보다 높은 역할이거나 서버 관리자일 수 있어요)')
    try:
        await target.timeout(timedelta(minutes=minutes), reason=f'{reason} (by {ctx.user.name})'[:512])
        log_action(ctx.guild.id, ctx.user.id, target.id, '타임아웃', reason, minutes)
        await ctx.reply(f'⏱️ {target} 님을 {minutes}분 동안 타임아웃했습니다. (사유: {reason})')
    except Exception as err:
        log.error('타임아웃 실패: %s', err)
        await ctx.reply('타임아웃에 실패했습니다. (봇 권한을 확인해주세요)')


@main_cmd('!아이디')
async def cmd_id(ctx: Ctx, args, content):
    tid = ctx.first_mention
    if not tid:
        return await ctx.reply(f'당신의 ID는 `{ctx.user.id}` 입니다.')
    target = ctx.message.mentions[0]
    await ctx.reply(f'{target} 님의 ID는 `{target.id}` 입니다.')


@main_cmd('!디엠')
async def cmd_dm(ctx: Ctx, args, content):
    uid = pint(args[1]) if len(args) > 1 else None
    if uid is None:
        return await ctx.reply('사용자 ID를 함께 입력해주세요! 예: !디엠 123456789012345678')
    try:
        target = await client.fetch_user(uid)
        await target.send('안녕하세요! 활동 좀 많이 해주세요! 😊')
        await ctx.reply(f'{target} 님에게 메시지를 보냈습니다.')
    except Exception:
        await ctx.reply('메시지를 보낼 수 없습니다. (잘못된 ID이거나 상대방이 DM을 막아뒀을 수 있어요)')


@main_cmd('!관리')
async def cmd_admin(ctx: Ctx, args, content):
    await ctx.reply('관리자 명령어 실행!')


@main_cmd('!서버나가기')
async def cmd_leave_guild(ctx: Ctx, args, content):
    arg = args[1] if len(args) > 1 else None
    gid = pint(arg) if arg else (ctx.guild.id if ctx.guild else None)
    if not gid:
        return await ctx.reply('나갈 서버 ID를 입력해주세요! 예: `!서버나가기 123456789012345678`')
    g = client.get_guild(gid)
    if not g:
        return await ctx.reply('봇이 해당 서버에 들어가 있지 않거나 ID가 잘못되었습니다.')
    await ctx.reply(f'서버 "{g.name}"에서 나갑니다...')
    await g.leave()


@main_cmd('!서버목록')
async def cmd_guild_list(ctx: Ctx, args, content):
    guilds = sorted(client.guilds, key=lambda g: g.member_count or 0, reverse=True)
    if not guilds:
        return await ctx.reply('봇이 들어가 있는 서버가 없습니다.')
    per = 10
    pages = math.ceil(len(guilds) / per)
    page = min(max(pint(args[1] if len(args) > 1 else None) or 1, 1), pages)
    start = (page - 1) * per
    lines = [f'**{start + i + 1}.** {g.name} · 👥 {(g.member_count or 0):,}명 · `{g.id}`' for i, g in enumerate(guilds[start:start + per])]
    e = mk_embed(0x5865F2, f'🌐 봇이 들어가 있는 서버 ({len(guilds)}개)', '\n'.join(lines))
    e.set_footer(text=f'{page}/{pages} 페이지' + (' · !서버목록 [페이지]' if pages > 1 else '') + ' · !서버나가기 [서버ID]로 나가기')
    await ctx.reply(embed=e, mentions=NO_MENTIONS)
