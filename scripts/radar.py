#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
规范雷达 / Class Rules Radar
============================
监测 CCS / DNV / ABS / LR / BV 五家船级社与 IMO 的规范、规则改版与强制文件生效动态，
输出一期静态 HTML 报告，并维护跨期台账（新增 / 持续跟踪 / 生效倒计时）。

设计原则
- 零第三方依赖（只用标准库），GitHub Actions 上直接跑，不需要 pip install。
- 双通道取数：官方列表页（html）+ 新闻 RSS（rss）。官方页抓不到就降级，不影响整体出报。
- 全部条目保留原始链接，报告只做线索整理，不做法律判断。

用法
  python scripts/radar.py                  # 正常跑一期
  python scripts/radar.py --offline-test   # 用本地缓存/样例数据渲染，不联网
"""

import argparse
import hashlib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta, timezone
from html import unescape
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
CONFIG = ROOT / "config" / "sources.json"
DATA = ROOT / "data"
OUTPUT = ROOT / "output"
ARCHIVE = OUTPUT / "archive"
ITEMS_FILE = DATA / "items.json"
RUNLOG_FILE = DATA / "run_log.json"

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/120.0 Safari/537.36")
TODAY = date.today()
NOW = datetime.now(timezone.utc)

# ----------------------------------------------------------------------------
# 词表
# ----------------------------------------------------------------------------
REG_STRONG = [
    "rule", "rules", "rule set", "regulation", "regulations", "amendment", "amendments",
    "entry into force", "enters into force", "enter into force", "in force", "statutory", "resolution", "circular",
    "regulatory news", "compliance", "solas", "marpol", "msc", "mepc", "class rule",
    "规范", "规则", "修正案", "修正", "通函", "决议", "生效", "新规", "技术通告", "强制性",
]
REG_ASYNC = ["update", "revised", "revision", "draft", "consultation", "修订", "征求意见"]

# 噪声：导航文字、企业动态、会议/签约类，不算规范改版
NOISE_PAT = [
    "our ", "solutions", "learn more", "read more", "contact us", "book a", "get in touch",
    "战略合作", "签约", "签署", "备忘录", "交流会", "研讨会", "论坛", "峰会", "任命", "收购", "并购",
    "获奖", "荣获", "招聘", "股价", "财报", "业绩", "这场会议", "释放了哪些", "解读会", "发布会",
    "reject", "veto", "sanction", "geopolit", "tariff", "election",
    "增订", "订单", "交付", "封锁", "军事", "军演", "rugby", "cosmetic", "wake surf",
    "lake ", "county", "city council", "school district",
    "praises", "congratulat", "condemn", "sanctions", "state police", "constitutional amendment",
    "appoints", "appointed", "acquires", "acquisition", "partnership", "signs mou",
    "awarded", "wins award", "appointment", "recruit", "share price", "quarterly result",
]
NOISE_EXACT = {
    "rules and regulations", "statutory compliance", "regulatory news", "abs regulatory news",
    "class news", "latest news", "news", "media centre", "media center", "imo regulatory news & trends",
    "eu regulatory news", "shipping decarbonization regulations", "regulatory updates",
}
DOMAIN_TAGS = [
    ("氨燃料", ["ammonia", "氨"]),
    ("甲醇燃料", ["methanol", "甲醇"]),
    ("LNG", ["lng", "liquefied natural gas", "液化天然气"]),
    ("氢燃料", ["hydrogen", "氢"]),
    ("替代燃料", ["alternative fuel", "biofuel", "e-fuel", "替代燃料", "绿色燃料"]),
    ("散货船", ["bulk carrier", "bulker", "散货"]),
    ("油轮", ["tanker", "油轮"]),
    ("集装箱船", ["container", "集装箱"]),
    ("客船/邮轮", ["passenger", "cruise", "客船", "邮轮"]),
    ("消防", ["fire", "firefighting", "消防"]),
    ("救生", ["life-saving", "lifesaving", "救生"]),
    ("结构强度", ["structural", "strength", "hull", "结构", "强度"]),
    ("电气", ["electrical", "electric", "电气"]),
    ("防污染", ["pollution", "marpol", "防污染"]),
    ("温室气体", ["ghg", "eexi", "cii", "decarbon", "emission", "温室气体", "碳"]),
    ("压载水", ["ballast", "压载水"]),
    ("自主船", ["autonomous", "mass", "无人", "自主"]),
    ("网络安全", ["cyber", "网络安全"]),
]

# 生效日期正则
MONTHS = {m: i for i, m in enumerate(
    ["january", "february", "march", "april", "may", "june", "july",
     "august", "september", "october", "november", "december"], start=1)}
RE_ISO = re.compile(r"\b(20\d{2})-(\d{1,2})-(\d{1,2})\b")
RE_EN_DMY = re.compile(r"\b(\d{1,2})\s+(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\.?,?\s+(20\d{2})\b", re.I)
RE_EN_MDY = re.compile(r"\b(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\.?\s+(\d{1,2}),?\s+(20\d{2})\b", re.I)
RE_EN_MY = re.compile(r"\b(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\.?\s+(20\d{2})\b", re.I)
RE_CN = re.compile(r"(20\d{2})\s*年\s*(\d{1,2})\s*月(?:\s*(\d{1,2})\s*日)?")
RE_CN_MD = re.compile(r"(?<!\d)(\d{1,2})\s*月\s*(\d{1,2})\s*日")
RE_YEAR_CN = re.compile(r"(20\d{2})\s*年(?=[^。；;]{0,10}(?:生效|施行|实施))")
RE_EN_D = re.compile(r"(?<!\d)(\d{1,2})\s+(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\b", re.I)
MON_IDX = {m[:3]: i for m, i in MONTHS.items()}


def is_noise(title):
    t = title.strip().lower()
    if t in NOISE_EXACT:
        return True
    if len(title.strip()) < 16:
        return True
    return any(p in t for p in NOISE_PAT)


# ----------------------------------------------------------------------------
# 网络
# ----------------------------------------------------------------------------
def proxies():
    env = (os.environ.get("RADAR_PROXY") or os.environ.get("HTTPS_PROXY")
           or os.environ.get("https_proxy") or "").strip()
    if env:
        return {"http": env, "https": env}
    return {}


def fetch(url, timeout=25, retries=2):
    """返回 (status, bytes)。失败重试，最终返回 (0, b\"\")。"""
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
        "Accept-Encoding": "identity",
    })
    px = proxies()
    opener = urllib.request.build_opener(
        urllib.request.ProxyHandler(px) if px else urllib.request.ProxyHandler({}))
    last = ""
    for i in range(retries + 1):
        try:
            with opener.open(req, timeout=timeout) as r:
                return r.status, r.read()
        except urllib.error.HTTPError as e:
            last = f"HTTP {e.code}"
            if e.code in (403, 404, 410):
                break
        except Exception as e:  # noqa: BLE001
            last = type(e).__name__ + ": " + str(e)[:80]
        time.sleep(1.2 * (i + 1))
    print(f"    ! 抓取失败 {last} -> {url[:90]}")
    return 0, b""


# ----------------------------------------------------------------------------
# 解析
# ----------------------------------------------------------------------------
def parse_rss(raw):
    out = []
    try:
        root = ET.fromstring(raw)
    except ET.ParseError:
        return out
    for it in root.iter("item"):
        t = (it.findtext("title") or "").strip()
        l = (it.findtext("link") or "").strip()
        d = (it.findtext("pubDate") or "").strip()
        desc = re.sub(r"<[^>]+>", " ", it.findtext("description") or "")
        if t and l:
            out.append({"title": t, "link": l, "date_raw": d,
                        "summary": unescape(re.sub(r"\s+", " ", desc)).strip()[:300]})
    for it in root.iter("{http://www.w3.org/2005/Atom}entry"):
        t = (it.findtext("{http://www.w3.org/2005/Atom}title") or "").strip()
        lk = it.find("{http://www.w3.org/2005/Atom}link")
        l = (lk.get("href") if lk is not None else "") or ""
        d = (it.findtext("{http://www.w3.org/2005/Atom}updated") or "").strip()
        if t and l:
            out.append({"title": t, "link": l, "date_raw": d, "summary": ""})
    return out


RE_A = re.compile(r'<a\b[^>]*href="([^"]+)"[^>]*>(.*?)</a>', re.S | re.I)


def parse_html_listing(raw, cfg):
    html = raw.decode("utf-8", "ignore")
    out, seen = [], set()
    for href, inner in RE_A.findall(html):
        text = unescape(re.sub(r"<[^>]+>", " ", inner))
        text = re.sub(r"\s+", " ", text).strip()
        if len(text) < 18 or len(text) > 220:
            continue
        if cfg.get("href_include") and not any(k.lower() in href.lower() for k in cfg["href_include"]):
            continue
        gate = [k.lower() for k in cfg.get("keyword_gate", [])]
        if gate and not any(k in text.lower() for k in gate):
            continue
        if href.startswith("/"):
            href = "https://" + urllib.parse.urlparse(cfg["url"]).netloc + href
        if not href.startswith("http") or href in seen:
            continue
        seen.add(href)
        out.append({"title": text, "link": href, "date_raw": "", "summary": ""})
        if len(out) >= int(cfg.get("limit", 20)):
            break
    return out


def parse_pubdate(s):
    if not s:
        return None
    s = s.strip()
    for fmt in ("%a, %d %b %Y %H:%M:%S %z", "%a, %d %b %Y %H:%M:%S %Z",
                "%Y-%m-%dT%H:%M:%S%z", "%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%d"):
        try:
            dt = datetime.strptime(s.replace("GMT", "+0000"), fmt)
            return dt.date()
        except ValueError:
            continue
    m = RE_ISO.search(s)
    if m:
        try:
            return date(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        except ValueError:
            return None
    return None


def clean_title(t):
    """Google News 标题形如 'Title - Reuters'，拆出来源。"""
    t = unescape(t).strip()
    src = ""
    if " - " in t:
        head, tail = t.rsplit(" - ", 1)
        if 2 < len(tail) < 40 and len(head) > 15:
            t, src = head.strip(), tail.strip()
    return t, src


def find_eif(text, ref=None):
    """从标题+摘要里抽生效日期，返回 date 或 None。ref 为发布日期，用于补年份。"""
    low = text.lower()
    if not any(k in low for k in ("entry into force", "enters into force", "enter into force",
                                  "in force", "take effect", "takes effect", "effective",
                                  "生效", "施行", "applicable from")):
        if "生效" not in text:
            return None, ""
    ref_year = (ref or TODAY).year
    cands = []
    for m in RE_ISO.finditer(text):
        try:
            cands.append(date(int(m.group(1)), int(m.group(2)), int(m.group(3))))
        except ValueError:
            pass
    for m in RE_EN_DMY.finditer(text):
        mo = MON_IDX.get(m.group(2).lower()[:3])
        if mo:
            cands.append(date(int(m.group(3)), mo, int(m.group(1))))
    for m in RE_EN_MDY.finditer(text):
        mo = MON_IDX.get(m.group(1).lower()[:3])
        if mo:
            cands.append(date(int(m.group(3)), mo, int(m.group(2))))
    for m in RE_EN_MY.finditer(text):
        mo = MON_IDX.get(m.group(1).lower()[:3])
        if mo:
            cands.append(date(int(m.group(2)), mo, 1))
    for m in RE_CN.finditer(text):
        y, mo = int(m.group(1)), int(m.group(2))
        d = int(m.group(3)) if m.group(3) else 1
        try:
            cands.append(date(y, mo, d))
        except ValueError:
            pass
    # 不带年份的写法（"10月1日" / "31 August"）：用发布日期补年，若已过则顺延一年
    if not cands:
        for m in RE_CN_MD.finditer(text):
            try:
                c = date(ref_year, int(m.group(1)), int(m.group(2)))
                cands.append(c if c >= TODAY - timedelta(days=45) else c.replace(year=ref_year + 1))
            except ValueError:
                pass
        for m in RE_EN_D.finditer(text):
            mo = MON_IDX.get(m.group(2).lower()[:3])
            if mo:
                try:
                    c = date(ref_year, mo, int(m.group(1)))
                    cands.append(c if c >= TODAY - timedelta(days=45) else c.replace(year=ref_year + 1))
                except ValueError:
                    pass
    valid = [c for c in cands if TODAY - timedelta(days=400) <= c <= TODAY + timedelta(days=900)]
    if valid:
        d = max(valid)
        return d, eif_precision(text, d)
    m = RE_YEAR_CN.search(text)
    if m:
        y = int(m.group(1))
        if TODAY.year - 1 <= y <= TODAY.year + 3:
            return date(y, 1, 1), "year"
    return None, ""



def eif_precision(text, d):
    """判断生效日期的精度：日 / 月 / 年。"""
    y, m, dd = d.year, d.month, d.day
    if dd != 1:
        return "day"
    if re.search(rf"{y}\s*年\s*{m}\s*月\s*{dd}\s*日", text) or \
       re.search(rf"{m}\s*月\s*{dd}\s*日", text) or \
       re.search(rf"{dd}\s+(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)", text, re.I):
        return "day"
    if re.search(rf"{y}\s*年\s*{m}\s*月", text):
        return "month"
    if re.search(rf"{y}-{m:02d}-{dd:02d}", text):
        return "day"
    return "month"


def classify(title, summary):
    low = (title + " " + summary).lower()
    if any(k in low for k in ("entry into force", "enters into force", "takes effect", "生效", "施行")):
        return "生效提醒"
    if any(k in low for k in ("amendment", "amendments", "修正案")):
        return "修正案"
    if any(k in low for k in ("resolution", "circular", "决议", "通函")):
        return "决议/通函"
    if any(k in low for k in ("regulatory news", "statutory alert", "regulatory update", "通报", "技术通告")):
        return "法规通报"
    if any(k in low for k in ("requirements", "requirement", "convention", "code of", "公约", "要求", "指南")):
        return "要求/指南"
    if any(k in low for k in ("rule", "rules", "rule set", "规范", "规则")):
        return "规则改版"
    return "行业动态"


def domain_tags(text):
    low = text.lower()
    return [name for name, keys in DOMAIN_TAGS if any(k in low for k in keys)]


def score(item):
    s = 15
    low = (item["title"] + " " + item.get("summary", "")).lower()
    if any(k in low for k in REG_STRONG):
        s += 30
    if any(k in low for k in REG_ASYNC):
        s += 5
    if item["org"] in ("CCS", "DNV", "ABS", "LR", "BV", "IMO"):
        s += 12
    if item.get("official"):
        s += 8
    if item["tags"]:
        s += min(18, 6 * len(item["tags"]))
    if item.get("eif"):
        d = (item["eif"] - TODAY).days
        if 0 <= d <= 90:
            s += 22
        elif 0 <= d <= 365:
            s += 14
        elif d < 0:
            s += 4
    return min(100, s)


# ----------------------------------------------------------------------------
# 主流程
# ----------------------------------------------------------------------------
def load_json(p, default):
    try:
        return json.loads(Path(p).read_text(encoding="utf-8"))
    except Exception:  # noqa: BLE001
        return default


def key_of(org, title):
    norm = re.sub(r"[^0-9a-z\u4e00-\u9fa5]+", "", title.lower())[:90]
    return hashlib.md5((org + "|" + norm).encode()).hexdigest()[:16]


def _tokens(title):
    t = re.sub(r"(中国船级社|船级社|lloyd'?s register|bureau veritas|american bureau of shipping|"
               r"dnv|abs|lr|bv|ccs|imo)", " ", title.lower())
    t = re.sub(r"[^0-9a-z\u4e00-\u9fa5]+", " ", t)
    words = [w for w in t.split() if len(w) > 1]
    cjk = "".join(ch for ch in t if "\u4e00" <= ch <= "\u9fa5")
    grams = {cjk[i:i + 2] for i in range(max(0, len(cjk) - 1))}
    return set(words) | grams


def similar(a, b):
    ta, tb = _tokens(a), _tokens(b)
    if not ta or not tb:
        return False
    inter = len(ta & tb)
    return inter / len(ta | tb) >= 0.5


def collect(cfg, offline=False):
    items, health = [], []
    for src in cfg["sources"]:
        if not src.get("enabled", True):
            continue
        print(f"  · {src['id']:<16} {src['name']}")
        if offline:
            health.append({"id": src["id"], "name": src["name"], "status": "跳过",
                           "count": 0, "note": "离线测试"})
            continue
        status, raw = fetch(src["url"])
        rows = []
        if status == 200 and raw:
            rows = parse_rss(raw) if src["type"] == "rss" else parse_html_listing(raw, src)
        status_txt = "OK" if rows else ("空" if status == 200 else f"失败({status})")
        health.append({"id": src["id"], "name": src["name"], "status": status_txt,
                       "count": len(rows), "note": ""})
        print(f"    -> {status_txt} {len(rows)} 条")
        for r in rows[: int(src.get("limit", 20))]:
            title, rss_src = clean_title(r["title"])
            title = re.sub(r"\s*-\s*船级社\s*$", "", title).strip()
            title = re.sub(r"^(News Content Hub|News)\s*[-–—:]\s*", "", title).strip()
            low = (title + " " + r.get("summary", "")).lower()
            if src["type"] == "rss" and not any(k in low for k in REG_STRONG):
                continue
            if is_noise(title):
                continue
            pub = parse_pubdate(r.get("date_raw", ""))
            if pub and (TODAY - pub).days > 240:
                continue
            eif, eif_prec = find_eif(title + " " + r.get("summary", ""), ref=pub)
            if not is_maritime(title + " " + r.get("summary", "")):
                continue
            rec = {
                "org": src["org"], "org_cn": src["org_cn"],
                "title": title, "link": r["link"], "summary": r.get("summary", ""),
                "pub": pub.isoformat() if pub else "",
                "eif": eif.isoformat() if eif else "",
                "eif_prec": eif_prec,
                "type": classify(title, r.get("summary", "")),
                "tags": domain_tags(title + " " + r.get("summary", "")),
                "source": src["name"], "origin": rss_src or src["org"],
                "official": bool(src.get("official")),
                "favicon": "",
            }
            rec["score"] = score({**rec, "eif": eif})
            rec["key"] = key_of(rec["org"], rec["title"])
            items.append(rec)
        time.sleep(0.4)
    # 去重：先按规范化标题，再做同机构内近似标题合并（"launches new rules" / "released new rules"）
    best = {}
    for it in items:
        k = it["key"]
        if k not in best or it["score"] > best[k]["score"]:
            best[k] = it
    uniq = sorted(best.values(), key=lambda x: -x["score"])
    merged = []
    for it in uniq:
        dup = next((m for m in merged if m["org"] == it["org"] and similar(m["title"], it["title"])), None)
        if dup:
            dup["tags"] = sorted(set(dup["tags"]) | set(it["tags"]))
            if not dup.get("eif") and it.get("eif"):
                dup["eif"] = it["eif"]
            continue
        merged.append(it)
    return merged, health



def merge_ledger(fresh):
    ledger = load_json(ITEMS_FILE, {})
    today_s = TODAY.isoformat()
    for it in fresh:
        k = it["key"]
        if k in ledger:
            old = ledger[k]
            old["last_seen"] = today_s
            old["times_seen"] = old.get("times_seen", 1) + 1
            old["score"] = max(old.get("score", 0), it["score"])
            if it.get("eif") and not old.get("eif"):
                old["eif"] = it["eif"]
            old["tags"] = sorted(set(old.get("tags", [])) | set(it["tags"]))
            it["first_seen"] = old.get("first_seen", today_s)
            it["status"] = "持续跟踪" if old.get("first_seen") != today_s else "本期新增"
            it["times_seen"] = old["times_seen"]
        else:
            it["first_seen"] = today_s
            it["status"] = "本期新增"
            it["times_seen"] = 1
        ledger[k] = it
    # 清理 120 天没再出现的
    cut = (TODAY - timedelta(days=120)).isoformat()
    ledger = {k: v for k, v in ledger.items() if v.get("last_seen", today_s) >= cut}
    ITEMS_FILE.parent.mkdir(parents=True, exist_ok=True)
    ITEMS_FILE.write_text(json.dumps(ledger, ensure_ascii=False, indent=1), encoding="utf-8")
    return ledger, fresh


# ----------------------------------------------------------------------------
# AI 增强（DeepSeek）：中文映照标题 + 本期重点解读；失败不阻塞出报
# ----------------------------------------------------------------------------
AI_URL = "https://api.deepseek.com/chat/completions"
AI_MODEL = "deepseek-chat"


def ai_enhance(fresh, ledger):
    """返回 ai 字典（overall/points/model），失败或未配置时返回 None。"""
    key = (os.environ.get("DEEPSEEK_API_KEY") or "").strip()
    if not key:
        print("[AI] 未配置 DEEPSEEK_API_KEY，跳过 AI 增强")
        return None
    targets = sorted(fresh, key=lambda x: -x["score"])[:24]
    if not targets:
        return None

    lines = []
    for i, it in enumerate(targets):
        summ = (it.get("summary") or "")[:160]
        lines.append(f"[{i}] org={it['org']} | type={it['type']} | eif={it.get('eif') or '-'}\n"
                     f"title: {it['title']}\nsummary: {summ}")
    listing = "\n".join(lines)
    user_prompt = f"""以下是本期自动采集的船级社/IMO 规范动态条目（按相关度排序）。请完成两件事：

1. 给每个条目的英文标题写一个简洁的中文映照标题（zh）。要求：机构缩写（CCS/DNV/ABS/LR/BV/IMO）与文件编号保留原文；
   只翻译标题本身，不要加解释。
2. 从中挑出 3~6 条最值得船厂技术部门注意的条目（优先：即将生效的强制要求、影响船型广的规范改版、
   涉及新燃料/安全的修正案），写 1~2 句理由（落到具体条款、船型、时间点或影响面）。不要选纯新闻类条目。

条目列表：
{listing}

只输出 JSON，格式：
{{"overall": "2~3 句中文总述，概括本期规范动态主线",
 "highlights": [{{"i": 0, "why": "理由"}}],
 "translations": [{{"i": 0, "zh": "中文映照标题"}}]}}"""

    payload = {
        "model": AI_MODEL,
        "messages": [
            {"role": "system",
             "content": "你是船舶行业规范情报分析员，为船厂技术部门服务。输出必须是严格合法的 JSON，不要输出多余文字。"},
            {"role": "user", "content": user_prompt},
        ],
        "response_format": {"type": "json_object"},
        "temperature": 0.3,
        "max_tokens": 4000,
    }
    req = urllib.request.Request(
        AI_URL, data=json.dumps(payload).encode("utf-8"), method="POST",
        headers={"Content-Type": "application/json", "Authorization": f"Bearer {key}"})
    try:
        print(f"[AI] 调用 {AI_MODEL} 分析 {len(targets)} 条…")
        with urllib.request.urlopen(req, timeout=180) as r:
            resp = json.loads(r.read())
        content = resp["choices"][0]["message"]["content"].strip()
        m = re.search(r"\{.*\}", content, re.S)
        obj = json.loads(m.group(0) if m else content)
    except Exception as e:  # noqa: BLE001
        print(f"[AI] 调用失败，本期跳过：{type(e).__name__}: {str(e)[:120]}")
        return None

    zh_map = {}
    for tr in obj.get("translations", []):
        try:
            i, zh = int(tr.get("i")), (tr.get("zh") or "").strip()
        except (TypeError, ValueError):
            continue
        if 0 <= i < len(targets) and zh:
            zh_map[i] = zh
            it = targets[i]
            it["title_zh"] = zh
            k = it["key"]
            if k in ledger:
                ledger[k]["title_zh"] = zh
    if zh_map:
        ITEMS_FILE.write_text(json.dumps(ledger, ensure_ascii=False, indent=1), encoding="utf-8")
        print(f"[AI] 中文映照 {len(zh_map)}/{len(targets)} 条，已写入台账")

    points = []
    for h in obj.get("highlights", []):
        try:
            i, why = int(h.get("i")), (h.get("why") or "").strip()
        except (TypeError, ValueError):
            continue
        if 0 <= i < len(targets) and why:
            it = targets[i]
            points.append({"why": why, "title": it["title"], "title_zh": it.get("title_zh", ""),
                           "link": it["link"], "org": it["org"]})
    if not obj.get("overall") and not points:
        print("[AI] 返回内容为空，本期跳过")
        return None
    print(f"[AI] 完成：重点 {len(points)} 条")
    return {"model": AI_MODEL, "overall": (obj.get("overall") or "").strip(), "points": points}


# ----------------------------------------------------------------------------
# 渲染
# ----------------------------------------------------------------------------
def esc(s):
    return (s or "").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;")


TOPIC_WORDS = ["ship", "ships", "shipping", "vessel", "maritime", "marine", "imo", "msc", "mepc",
               "class society", "classification society", "classed", "flag state", "port state",
               "offshore", "yacht", "fleet", "naval", "seafarer", "solas", "marpol", "load line",
               "船", "舰", "海事", "航运", "船舶", "港", "船级社", "海工", "船员", "海上"]


def is_maritime(text):
    low = text.lower()
    return any(k in low for k in TOPIC_WORDS)


ORG_ORDER = ["CCS", "DNV", "ABS", "LR", "BV", "IMO", "行业"]
ORG_COLOR = {"CCS": "#b91c1c", "DNV": "#1d4ed8", "ABS": "#0f766e",
             "LR": "#7c3aed", "BV": "#c2410c", "IMO": "#0369a1", "行业": "#475569"}


def eta_class(days):
    if days is None:
        return "n"
    if days < 0:
        return "past"
    if days <= 30:
        return "hot"
    if days <= 90:
        return "warn"
    return "ok"


def item_row(it):
    tags = "".join(f'<span class="tag">{esc(t)}</span>' for t in it["tags"][:4])
    eif = ""
    if it.get("eif"):
        d = (date.fromisoformat(it["eif"]) - TODAY).days
        label = "已生效" if d < 0 else f"{d} 天后生效"
        eif = f'<span class="eif {eta_class(d)}">{label} · {it["eif"]}</span>'
    src = esc(it.get("origin") or "")
    srcline = esc(it["source"]) + (f" · {src}" if src and src != it["org"] else "")
    color = ORG_COLOR.get(it["org"], "#475569")
    zh = f'<div class="zh">{esc(it["title_zh"])}</div>' if it.get("title_zh") else ""
    return f"""        <div class="row" style="--c:{color}" data-org="{esc(it['org'])}" data-text="{esc((it['title'] + ' ' + ' '.join(it['tags'])).lower())}">
          <div class="row-main">
            <a class="row-title" href="{esc(it['link'])}" target="_blank" rel="noopener">{esc(it['title'])}</a>
            {zh}
            <div class="row-meta">
              <span class="badge" style="--c:{color}">{esc(it['org'])}</span>
              <span class="kind">{esc(it['type'])}</span>
              {eif}
              {tags}
              <span class="src">{srcline}</span>
            </div>
          </div>
          <div class="row-side">
            <span class="pub">{esc(it.get('pub') or it.get('first_seen') or '')}</span>
            <span class="st {'new' if it['status'] == '本期新增' else ''}">{esc(it['status'])}</span>
          </div>
        </div>"""


CSS = """
:root{--bg:#eef2f7;--panel:#fff;--ink:#0b1220;--ink2:#3d4a5c;--ink3:#7c8a9c;
--line:#e3e9f1;--line2:#eef2f7;--accent:#1d4ed8;--accent-bg:#eaf0fe;
--hot:#c2410c;--hotbg:#fff4ed;--warn:#a16207;--warnbg:#fffaeb;--okc:#0f766e;--okbg:#effcf8;
--sh-sm:0 1px 2px rgba(16,24,40,.05),0 1px 3px rgba(16,24,40,.05);
--sh-md:0 14px 34px -18px rgba(16,24,40,.3),0 2px 6px rgba(16,24,40,.05)}
*{box-sizing:border-box}
html{scroll-behavior:smooth}
body{margin:0;background:var(--bg);color:var(--ink);font-size:14px;line-height:1.65;
font-family:"Inter","Segoe UI",-apple-system,BlinkMacSystemFont,"PingFang SC","Hiragino Sans GB","Microsoft YaHei",sans-serif;
-webkit-font-smoothing:antialiased}
.wrap{max-width:1080px;margin:0 auto;padding:28px 20px 72px}

.hero{position:relative;overflow:hidden;border-radius:20px;padding:26px 28px 24px;color:#e8eefb;
background:radial-gradient(120% 150% at 6% 0%,#1e3a8a 0%,#111c33 44%,#0a1120 100%);box-shadow:var(--sh-md)}
.hero::after{content:"";position:absolute;right:-14%;top:-45%;width:70%;height:220%;pointer-events:none;
background:radial-gradient(closest-side,rgba(56,189,248,.22),transparent 72%)}
.hero-top{display:flex;align-items:center;gap:10px;font-size:11px;letter-spacing:.16em;text-transform:uppercase;color:rgba(232,238,251,.55)}
.hero-top .issue{margin-left:auto;letter-spacing:0;text-transform:none;font-size:11.5px;padding:2px 10px;
border:1px solid rgba(232,238,251,.22);border-radius:999px;color:rgba(232,238,251,.8)}
.hero h1{margin:12px 0 0;font-size:clamp(20px,2.6vw,27px);font-weight:600;line-height:1.35;letter-spacing:.01em}
.hero-sub{margin:6px 0 0;font-size:12.5px;color:rgba(232,238,251,.62);max-width:64ch}
.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;margin-top:20px}
.stat{padding:11px 14px;border-radius:12px;background:rgba(255,255,255,.07);border:1px solid rgba(255,255,255,.1)}
.stat i{display:block;font-style:normal;font-size:11px;color:rgba(232,238,251,.55);margin-bottom:3px}
.stat b{font-size:24px;font-weight:600;line-height:1.2;font-variant-numeric:tabular-nums}
.stat b small{font-size:11.5px;font-weight:400;color:rgba(232,238,251,.55);margin-left:3px}

.nav{position:sticky;top:12px;z-index:30;display:flex;align-items:center;gap:4px;margin-top:16px;padding:7px;
border-radius:13px;background:rgba(255,255,255,.9);border:1px solid var(--line);box-shadow:var(--sh-sm);
backdrop-filter:blur(10px) saturate(140%);overflow-x:auto}
.nav a{font-size:12.5px;color:var(--ink2);text-decoration:none;padding:6px 12px;border-radius:9px;white-space:nowrap;transition:.15s}
.nav a:hover{background:#f1f5fb;color:var(--ink)}
.nav-sp{flex:1}
.nav-meta{font-size:11.5px;color:var(--ink3);padding-right:8px;white-space:nowrap}

.sec{margin-top:32px;scroll-margin-top:78px}
.sec-h{display:flex;align-items:center;gap:10px;margin-bottom:6px}
.sec-h .num{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:11px;font-weight:600;letter-spacing:.1em;
color:var(--accent);background:var(--accent-bg);border:1px solid #d6e2fd;border-radius:6px;padding:3px 7px}
.sec-h h2{margin:0;font-size:16px;font-weight:600}
.sec-h .note{margin-left:auto;font-size:11.5px;color:var(--ink3)}
.lead{margin:0 0 14px;font-size:12.5px;color:var(--ink3);max-width:78ch}

.eif-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(272px,1fr));gap:12px}
.eif-card{display:flex;gap:14px;padding:14px;background:var(--panel);border:1px solid var(--line);border-radius:14px;
text-decoration:none;color:inherit;box-shadow:var(--sh-sm);transition:transform .16s ease,box-shadow .16s ease,border-color .16s ease}
.eif-card:hover{transform:translateY(-2px);box-shadow:var(--sh-md);border-color:#cfdcf0}
.dn{flex:none;width:64px;padding:8px 0;border-radius:10px;text-align:center;background:#f5f8fc}
.dn b{display:block;font-size:22px;font-weight:600;line-height:1.15;font-variant-numeric:tabular-nums}
.dn i{font-style:normal;font-size:10.5px;color:var(--ink3)}
.dn.hot{background:var(--hotbg)}.dn.hot b{color:var(--hot)}
.dn.warn{background:var(--warnbg)}.dn.warn b{color:var(--warn)}
.dn.ok{background:var(--okbg)}.dn.ok b{color:var(--okc)}
.dn.past b{font-size:15px;color:var(--ink3);padding:5px 0}
.eif-card .body{min-width:0;flex:1}
.eif-card .t{font-size:13px;font-weight:500;line-height:1.5;display:-webkit-box;-webkit-line-clamp:3;
-webkit-box-orient:vertical;overflow:hidden}
.eif-card .m{margin-top:7px;display:flex;align-items:center;gap:6px;flex-wrap:wrap;font-size:11px;color:var(--ink3)}

.card{background:var(--panel);border:1px solid var(--line);border-radius:16px;box-shadow:var(--sh-sm);overflow:hidden}
.tools{display:flex;flex-wrap:wrap;align-items:center;gap:8px;padding:12px 16px;border-bottom:1px solid var(--line);
background:linear-gradient(#fbfcff,#f7f9fd)}
.chip{font:inherit;font-size:12px;color:var(--ink2);background:#fff;border:1px solid var(--line);border-radius:999px;
padding:4px 12px;cursor:pointer;transition:.15s}
.chip:hover{border-color:#c9d6ea;color:var(--ink)}
.chip.on{background:var(--ink);border-color:var(--ink);color:#fff;box-shadow:0 6px 14px -8px rgba(11,18,32,.7)}
.search{flex:1;min-width:190px;font:inherit;font-size:12.5px;color:var(--ink);background:#fff;border:1px solid var(--line);
border-radius:9px;padding:6px 11px;outline:none;transition:.15s}
.search:focus{border-color:#b9cdf0;box-shadow:0 0 0 3px rgba(29,78,216,.09)}

.group+.group{border-top:1px solid var(--line)}
.group-h{display:flex;align-items:center;gap:8px;padding:10px 18px;background:#fafcff;border-bottom:1px solid var(--line2)}
.group-h .org{font-size:11.5px;font-weight:600;letter-spacing:.04em;color:#fff;padding:2px 9px;border-radius:7px}
.group-h .cn{font-size:12px;color:var(--ink2)}
.group-h .n{margin-left:auto;font-size:11.5px;color:var(--ink3);font-variant-numeric:tabular-nums}

.row{position:relative;display:flex;gap:14px;padding:13px 18px 13px 20px;border-top:1px solid var(--line2);
align-items:flex-start;transition:background .15s}
.group-h+.row,.card>.row:first-child{border-top:0}
.row::before{content:"";position:absolute;left:0;top:13px;bottom:13px;width:3px;border-radius:0 3px 3px 0;
background:var(--c,#cbd5e1);opacity:0;transition:opacity .15s}
.row:hover{background:#fafcff}
.row:hover::before{opacity:1}
.row-main{flex:1;min-width:0}
.row-title{display:block;font-size:13.5px;font-weight:500;line-height:1.55;color:var(--ink);text-decoration:none}
.row-title:hover{color:var(--accent)}
.row-meta{display:flex;flex-wrap:wrap;align-items:center;gap:6px;margin-top:6px}
.badge{font-size:10.5px;font-weight:600;letter-spacing:.04em;color:#fff;background:var(--c);padding:1px 7px;border-radius:6px}
.kind{font-size:11.5px;color:var(--ink2);background:#f4f7fb;border:1px solid var(--line);padding:0 7px;border-radius:6px}
.tag{font-size:11px;color:var(--ink3);border:1px solid var(--line);background:#fff;padding:0 7px;border-radius:6px}
.eif{font-size:11.5px;padding:0 7px;border-radius:6px;border:1px solid;font-variant-numeric:tabular-nums}
.eif.hot{background:var(--hotbg);color:var(--hot);border-color:#fbd7c2}
.eif.warn{background:var(--warnbg);color:var(--warn);border-color:#f6e3ab}
.eif.ok{background:var(--okbg);color:var(--okc);border-color:#b7ece0}
.eif.past,.eif.n{background:#f4f7fb;color:var(--ink3);border-color:var(--line)}
.src{font-size:11.5px;color:var(--ink3)}
.row-side{flex:none;width:112px;text-align:right}
.pub{display:block;font-size:11.5px;color:var(--ink3);font-variant-numeric:tabular-nums}
.st{display:inline-block;margin-top:4px;font-size:11px;color:var(--ink3);border:1px solid var(--line);
border-radius:6px;padding:0 6px;background:#fff}
.st.new{color:var(--accent);background:var(--accent-bg);border-color:#d6e2fd}

table{width:100%;border-collapse:collapse}
th{text-align:left;font-size:11px;font-weight:600;letter-spacing:.06em;text-transform:uppercase;color:var(--ink3);
background:#fafcff;padding:9px 18px;border-bottom:1px solid var(--line)}
td{padding:9px 18px;border-top:1px solid var(--line2);font-size:12.5px;color:var(--ink2)}
td:last-child{text-align:right;width:84px;color:var(--ink3);font-variant-numeric:tabular-nums}
.dot{display:inline-block;width:6px;height:6px;border-radius:50%;margin-right:6px;vertical-align:1px}
.dot.ok{background:#10b981}.dot.bad{background:#ef4444}.dot.mid{background:#f59e0b}
.ok-s{color:var(--okc)}.bad-s{color:#b91c1c}

.foot{margin-top:26px;display:grid;grid-template-columns:1.55fr 1fr;gap:12px}
.foot-box{background:var(--panel);border:1px solid var(--line);border-radius:14px;padding:16px 18px;
font-size:12px;color:var(--ink2);line-height:1.75;box-shadow:var(--sh-sm)}
.foot-box h3{margin:0 0 6px;font-size:12px;font-weight:600;color:var(--ink)}
.foot-box b{color:var(--ink)}
.foot-meta dl{margin:0;display:grid;grid-template-columns:auto 1fr;gap:5px 12px;font-size:12px}
.foot-meta dt{color:var(--ink3)}
.foot-meta dd{margin:0;text-align:right;font-variant-numeric:tabular-nums}
.empty{padding:30px;text-align:center;color:var(--ink3);font-size:13px}

.zh{margin-top:2px;font-size:12px;color:var(--ink2)}
.eif-card .tz{margin-top:2px;font-size:12px;color:var(--ink2)}
.eif-card .tz:empty{display:none}

.ai-card{padding:18px 20px}
.ai-overall{font-size:13.5px;line-height:1.8;color:var(--ink);border-left:3px solid var(--accent);
padding:2px 0 2px 14px;margin-bottom:14px}
.ai-points{display:grid;gap:10px}
.ai-point{display:flex;gap:12px;padding:12px 14px;border:1px solid var(--line);border-radius:12px;
background:#fbfcff;text-decoration:none;color:inherit;transition:border-color .15s,background .15s}
.ai-point:hover{border-color:#cfdcf0;background:#f6f9ff}
.ai-no{flex:none;width:24px;height:24px;border-radius:8px;background:var(--accent-bg);color:var(--accent);
font-size:12px;font-weight:600;display:flex;align-items:center;justify-content:center;margin-top:1px}
.ai-body{min-width:0;display:flex;flex-direction:column;gap:3px}
.ai-org{align-self:flex-start;font-size:10.5px;font-weight:600;letter-spacing:.04em;color:#fff;
padding:1px 7px;border-radius:6px}
.ai-zh{font-size:13px;font-weight:500;color:var(--ink)}
.ai-title{font-size:12px;color:var(--ink3);line-height:1.5}
.ai-why{font-size:12.5px;color:var(--ink2);line-height:1.7}
.ai-note{margin-top:12px;padding-top:10px;border-top:1px dashed var(--line);font-size:11.5px;color:var(--ink3)}

@media(max-width:760px){
  .wrap{padding:18px 14px 56px}
  .hero{padding:22px 18px;border-radius:16px}
  .stats{grid-template-columns:repeat(2,1fr)}
  .sec-h .note{display:none}
  .row-side{display:none}
  .foot{grid-template-columns:1fr}
  .nav{top:8px}
}
@media print{body{background:#fff}.nav{display:none}.hero{box-shadow:none}.card,.eif-card,.foot-box{box-shadow:none}}
"""

JS = """
(function(){
  var box=document.getElementById('fresh')||document;
  var chips=[].slice.call(box.querySelectorAll('.chip[data-org]'));
  var rows=[].slice.call(box.querySelectorAll('.row[data-org]'));
  var q=document.getElementById('q');
  var hint=document.getElementById('fempty');
  var cur='ALL';
  function apply(){
    var kw=(q&&q.value||'').trim().toLowerCase();
    var shown=0;
    rows.forEach(function(r){
      var okOrg = cur==='ALL' || r.dataset.org===cur;
      var okKw = !kw || (r.dataset.text||'').indexOf(kw)>=0;
      var vis = okOrg&&okKw;
      r.style.display = vis?'':'none';
      if(vis) shown++;
    });
    [].slice.call(box.querySelectorAll('.group')).forEach(function(g){
      var vis=[].slice.call(g.querySelectorAll('.row')).some(function(r){return r.style.display!=='none';});
      g.style.display=vis?'':'none';
    });
    if(hint) hint.style.display=(!shown&&rows.length)?'':'none';
  }
  chips.forEach(function(c){c.addEventListener('click',function(){
    chips.forEach(function(x){x.classList.remove('on')});c.classList.add('on');cur=c.dataset.org;apply();});});
  if(q){
    q.addEventListener('input',apply);
    document.addEventListener('keydown',function(e){
      if(e.key==='/'&&document.activeElement!==q){e.preventDefault();q.focus();}
      else if(e.key==='Escape'&&document.activeElement===q){q.value='';apply();q.blur();}
    });
  }
})();
"""

def render(ledger, fresh, health, ai=None):
    fresh.sort(key=lambda x: (-x["score"], x["pub"] or "", x["title"]))
    with_eif = [i for i in ledger.values() if i.get("eif")]
    with_eif.sort(key=lambda x: x["eif"])
    upcoming = [i for i in with_eif if 0 <= (date.fromisoformat(i["eif"]) - TODAY).days <= 365]
    soon90 = [i for i in upcoming if (date.fromisoformat(i["eif"]) - TODAY).days <= 90]
    tracked = [i for i in ledger.values() if i["status"] != "本期新增"]
    tracked.sort(key=lambda x: (-x["score"], x.get("last_seen", "")))

    by_org = {}
    for it in fresh:
        by_org.setdefault(it["org"], []).append(it)
    groups_html = ""
    for org in ORG_ORDER + [o for o in by_org if o not in ORG_ORDER]:
        if org not in by_org:
            continue
        rows = "".join(item_row(i) for i in by_org[org])
        label = by_org[org][0]["org_cn"]
        groups_html += f"""      <div class="group">
        <div class="group-h"><span class="org" style="background:{ORG_COLOR.get(org,'#475569')}">{esc(org)}</span>
          <span class="cn">{esc(label)}</span><span class="n">{len(by_org[org])} 条</span></div>
{rows}
      </div>
"""

    eif_html = ""
    for it in upcoming[:8]:
        d = (date.fromisoformat(it["eif"]) - TODAY).days
        prec = it.get("eif_prec")
        day_txt = it["eif"][:4] + " 年" if prec == "year" else (it["eif"][:7] if prec == "month" else it["eif"])
        color = ORG_COLOR.get(it["org"], "#475569")
        eif_html += f"""      <a class="eif-card" href="{esc(it['link'])}" target="_blank" rel="noopener">
        <div class="dn {eta_class(d)}"><b>{d}</b><i>天后</i></div>
        <div class="body">
          <div class="t">{esc(it['title'][:100])}</div>
          <div class="tz">{esc(it['title_zh'])}</div>
          <div class="m"><span class="badge" style="--c:{color}">{esc(it['org'])}</span><span>{esc(day_txt)}</span></div>
        </div>
      </a>
"""
    if not eif_html:
        eif_html = '<div class="empty">本期没有从公开信息中识别出明确的生效日期，见下方条目。</div>'

    rows_tracked = "".join(item_row(i) for i in tracked[:40])
    if not rows_tracked:
        rows_tracked = '<div class="empty">上期条目已全部在本期重复出现，暂无跨期跟踪对象。</div>'

    health_rows = ""
    for h in health:
        ok = h["status"] == "OK"
        cls = "ok-s" if ok else ("bad-s" if "失败" in h["status"] else "")
        dot = "ok" if ok else ("bad" if "失败" in h["status"] else "mid")
        health_rows += (f'<tr><td><span class="dot {dot}"></span>{esc(h["name"])}</td>'
                        f"<td class='{cls}'>{esc(h['status'])}</td>"
                        f"<td>{h['count']}</td></tr>")

    orgs = [o for o in ORG_ORDER if o in by_org]
    chips = "".join(f'<button class="chip" data-org="{o}">{o}</button>' for o in orgs)
    ok_src = sum(1 for h in health if h["status"] == "OK")

    ai_section = ""
    if ai:
        points_html = ""
        for n, p in enumerate(ai.get("points", []), 1):
            zh = f'<span class="ai-zh">{esc(p["title_zh"])}</span>' if p.get("title_zh") else ""
            points_html += f"""        <a class="ai-point" href="{esc(p['link'])}" target="_blank" rel="noopener">
          <span class="ai-no">{n}</span>
          <span class="ai-body"><span class="ai-org" style="background:{ORG_COLOR.get(p['org'], '#475569')}">{esc(p['org'])}</span>
            {zh}<span class="ai-title">{esc(p['title'])}</span>
            <span class="ai-why">{esc(p['why'])}</span></span>
        </a>
"""
        if not points_html:
            points_html = '<div class="empty">本期没有选出重点条目。</div>'
        overall = esc(ai.get("overall") or "")
        ai_section = f"""
  <section class="sec" id="ai">
    <div class="sec-h"><span class="num">02</span><h2>AI 本期解读</h2><span class="note">DeepSeek 生成 · 仅供参考</span></div>
    <p class="lead">由 AI 基于本期条目自动归纳主线并挑出值得注意的改动，帮助快速定位重点；结论务必回原文核对。</p>
    <div class="card ai-card">
      <div class="ai-overall">{overall}</div>
{points_html}      <div class="ai-note">解读由 DeepSeek（{esc(ai.get('model', ''))}）自动生成，可能存在误读，不构成规范解释或合规结论。</div>
    </div>
  </section>
"""

    return f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="color-scheme" content="light">
<title>规范雷达 · {TODAY.isoformat()} 期</title>
<style>{CSS}</style>
</head>
<body>
<div class="wrap" id="top">

  <header class="hero">
    <div class="hero-top">
      <span>Class Rules Radar</span>
      <span class="issue">第 {TODAY.isoformat()} 期</span>
    </div>
    <h1>规范雷达 · 船级社规范与强制文件改版动态</h1>
    <p class="hero-sub">覆盖 CCS / DNV / ABS / LR / BV / IMO 六方公开信息 · 自动采集 · 只做线索整理，不做法律判断</p>
    <div class="stats">
      <div class="stat"><i>本期新增</i><b>{len(fresh)}<small>条</small></b></div>
      <div class="stat"><i>90 天内生效</i><b>{len(soon90)}<small>条</small></b></div>
      <div class="stat"><i>一年内生效</i><b>{len(upcoming)}<small>条</small></b></div>
      <div class="stat"><i>台账累计</i><b>{len(ledger)}<small>条</small></b></div>
    </div>
  </header>

  <nav class="nav">
    <a href="#eif">生效倒计时</a>
    <a href="#ai">AI 解读</a>
    <a href="#fresh">本期新增</a>
    <a href="#track">持续跟踪</a>
    <a href="#health">抓取状态</a>
    <span class="nav-sp"></span>
    <span class="nav-meta">{ok_src}/{len(health)} 源正常</span>
  </nav>

  <section class="sec" id="eif">
    <div class="sec-h"><span class="num">01</span><h2>生效倒计时</h2><span class="note">按生效日期排序</span></div>
    <p class="lead">规范改版真正需要动作的是「哪天开始适用」。识别到生效日期的条目按剩余天数排开：30 天内标红、90 天内标黄。</p>
    <div class="eif-grid">
{eif_html}    </div>
  </section>
{ai_section}
  <section class="sec" id="fresh">
    <div class="sec-h"><span class="num">03</span><h2>本期新增</h2><span class="note">共 {len(fresh)} 条 · 按机构分组</span></div>
    <p class="lead">每条标注机构、类型、生效日与涉及领域；点标题跳原文。列表只做线索整理，具体条款需回原文核对。</p>
    <div class="card">
      <div class="tools">
        <button class="chip on" data-org="ALL">全部</button>
        {chips}
        <input class="search" id="q" placeholder="筛选关键词，例：ammonia / 消防 / entry into force">
      </div>
{groups_html if groups_html else '<div class="empty">本期未采到有效条目，见文末抓取状态。</div>'}
      <div class="empty" id="fempty" style="display:none">没有匹配的条目，换个关键词试试。</div>
    </div>
  </section>

  <section class="sec" id="track">
    <div class="sec-h"><span class="num">04</span><h2>持续跟踪</h2><span class="note">往期已收录 · 本期仍有回响</span></div>
    <p class="lead">同一事项在多期出现即留在台账里，直到 120 天不再出现才自动清理，避免「看过就丢」。</p>
    <div class="card">
{rows_tracked}
    </div>
  </section>

  <section class="sec" id="health">
    <div class="sec-h"><span class="num">05</span><h2>抓取状态</h2><span class="note">每期公开 · 失败不隐藏</span></div>
    <div class="card">
      <table>
        <thead><tr><th>数据源</th><th>状态</th><th>条目</th></tr></thead>
        <tbody>{health_rows}</tbody>
      </table>
    </div>
  </section>

  <footer class="foot">
    <div class="foot-box">
      <h3>使用说明</h3>
      本报告为<b>公开信息线索汇总</b>，自动采集自船级社官网与公开新闻源，不构成规范解释或合规结论。
      生效日期由标题/摘要正则识别，可能存在偏差，<b>执行前必须以船级社原文或通函为准</b>。
      不涉及任何公司内部资料；条目链接均指向公开发布页面。
    </div>
    <div class="foot-box foot-meta">
      <h3>本期信息</h3>
      <dl>
        <dt>期次</dt><dd>{TODAY.isoformat()}</dd>
        <dt>新增条目</dt><dd>{len(fresh)}</dd>
        <dt>台账累计</dt><dd>{len(ledger)}</dd>
        <dt>数据源</dt><dd>{ok_src}/{len(health)}</dd>
      </dl>
    </div>
  </footer>

</div>
<script>{JS}</script>
</body>
</html>
"""


def write_runlog(health, fresh):
    log = load_json(RUNLOG_FILE, [])
    log.append({"date": TODAY.isoformat(), "ts": NOW.isoformat(timespec="seconds"),
                "collected": len(fresh), "sources": health})
    RUNLOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    RUNLOG_FILE.write_text(json.dumps(log[-90:], ensure_ascii=False, indent=1), encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--offline-test", action="store_true")
    args = ap.parse_args()
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:  # noqa: BLE001
        pass

    cfg = load_json(CONFIG, {"sources": []})
    print(f"[规范雷达] {TODAY} 开始采集，{len(cfg['sources'])} 个数据源")
    fresh, health = collect(cfg, offline=args.offline_test)
    ledger, fresh = merge_ledger(fresh)
    ai = None if args.offline_test else ai_enhance(fresh, ledger)

    OUTPUT.mkdir(parents=True, exist_ok=True)
    ARCHIVE.mkdir(parents=True, exist_ok=True)
    html = render(ledger, fresh, health, ai)
    (OUTPUT / "index.html").write_text(html, encoding="utf-8")
    (ARCHIVE / f"{TODAY.isoformat()}.html").write_text(html, encoding="utf-8")
    write_runlog(health, fresh)

    ok = sum(1 for h in health if h["status"] == "OK")
    print(f"[规范雷达] 完成：有效源 {ok}/{len(health)}，本期 {len(fresh)} 条，台账 {len(ledger)} 条")
    print(f"  报告 -> {OUTPUT / 'index.html'}")


if __name__ == "__main__":
    main()
