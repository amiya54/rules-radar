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
    """返回 (status, bytes)。失败重试，最终返回 (0, b"")。"""
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
    return f"""        <div class="row" data-org="{esc(it['org'])}" data-text="{esc((it['title'] + ' ' + ' '.join(it['tags'])).lower())}">
          <div class="row-main">
            <a class="row-title" href="{esc(it['link'])}" target="_blank" rel="noopener">{esc(it['title'])}</a>
            <div class="row-meta">
              <span class="badge" style="--c:{ORG_COLOR.get(it['org'], '#475569')}">{esc(it['org'])}</span>
              <span class="kind">{esc(it['type'])}</span>
              {eif}
              {tags}
              <span class="src">{esc(it['source'])}{(' · ' + src) if src and src != it['org'] else ''}</span>
            </div>
          </div>
          <div class="row-side">
            <span class="pub">{esc(it.get('pub') or it.get('first_seen') or '')}</span>
            <span class="st {'new' if it['status'] == '本期新增' else ''}">{esc(it['status'])}</span>
          </div>
        </div>"""


CSS = """
:root{--bg:#f5f7fa;--card:#fff;--ink:#0f172a;--ink2:#475569;--ink3:#94a3b8;--line:#e6ebf2;--line2:#eff3f8;
--hot:#b91c1c;--hotbg:#fef2f2;--warn:#b45309;--warnbg:#fffbeb;--ok:#047857;--okbg:#ecfdf5;--blue:#1d4ed8;--bluebg:#eff6ff}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font-family:-apple-system,BlinkMacSystemFont,"Segoe UI","PingFang SC","Microsoft YaHei",sans-serif;font-size:14px;line-height:1.65}
.wrap{max-width:1120px;margin:0 auto;padding:26px 18px 64px}
.head{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:22px 24px}
.head h1{margin:0;font-size:21px;font-weight:500;letter-spacing:.2px}
.head .sub{margin-top:5px;font-size:12.5px;color:var(--ink3)}
.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:12px;margin-top:16px}
.stat{background:#f8fafc;border-radius:10px;padding:12px 14px}
.stat i{display:block;font-style:normal;font-size:11.5px;color:var(--ink3);margin-bottom:2px}
.stat b{font-size:22px;font-weight:500;line-height:1.3}
.stat b small{font-size:12px;color:var(--ink3);font-weight:400;margin-left:3px}
h2{font-size:15px;font-weight:500;margin:28px 0 4px;display:flex;align-items:center;gap:8px}
h2 em{font-style:normal;font-size:11.5px;color:var(--ink3);font-weight:400;margin-left:auto}
.lead{font-size:12.5px;color:var(--ink2);margin:0 0 12px}
.card{background:var(--card);border:1px solid var(--line);border-radius:14px;overflow:hidden}
.eif-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(250px,1fr));gap:10px}
.eif-card{border:1px solid var(--line);border-radius:12px;padding:12px 14px;background:var(--card)}
.eif-card .d{font-size:12px;color:var(--ink3)}
.eif-card .t{font-size:13px;margin:4px 0 8px;line-height:1.5}
.eif-card .n{font-size:12px;padding:1px 8px;border-radius:8px;display:inline-block}
.n.hot{background:var(--hotbg);color:var(--hot);border:1px solid #fecaca}
.n.warn{background:var(--warnbg);color:var(--warn);border:1px solid #fde68a}
.n.ok{background:var(--okbg);color:var(--ok);border:1px solid #a7f3d0}
.n.past{background:#f1f5f9;color:var(--ink3);border:1px solid var(--line)}
.group{border-top:1px solid var(--line)}
.group:first-child{border-top:0}
.group-h{display:flex;align-items:center;gap:8px;padding:11px 18px;background:#fafcff}
.group-h .org{font-size:12.5px;font-weight:500;padding:1px 9px;border-radius:8px;color:#fff}
.group-h .n{font-size:12px;color:var(--ink3)}
.row{display:flex;gap:14px;padding:12px 18px;border-top:1px solid var(--line2);align-items:flex-start}
.row:hover{background:#fcfdff}
.row-main{flex:1;min-width:0}
.row-title{color:var(--ink);text-decoration:none;font-size:13.5px;display:block;line-height:1.55}
.row-title:hover{color:var(--blue);text-decoration:underline}
.row-meta{display:flex;flex-wrap:wrap;gap:6px;align-items:center;margin-top:5px}
.badge{font-size:11px;color:#fff;background:var(--c);padding:0 7px;border-radius:6px;line-height:1.7}
.kind{font-size:11.5px;color:var(--ink2);background:#f1f5f9;border:1px solid var(--line);padding:0 7px;border-radius:6px}
.eif{font-size:11.5px;padding:0 7px;border-radius:6px;border:1px solid}
.eif.hot{background:var(--hotbg);color:var(--hot);border-color:#fecaca}
.eif.warn{background:var(--warnbg);color:var(--warn);border-color:#fde68a}
.eif.ok{background:var(--okbg);color:var(--ok);border-color:#a7f3d0}
.eif.past,.eif.n{background:#f1f5f9;color:var(--ink3);border-color:var(--line)}
.tag{font-size:11px;color:var(--ink2);border:1px solid var(--line);background:#fff;padding:0 7px;border-radius:6px}
.src{font-size:11.5px;color:var(--ink3)}
.row-side{width:118px;text-align:right;flex:none}
.pub{display:block;font-size:11.5px;color:var(--ink3)}
.st{display:inline-block;margin-top:3px;font-size:11px;color:var(--ink3);border:1px solid var(--line);border-radius:6px;padding:0 6px}
.st.new{color:var(--blue);background:var(--bluebg);border-color:#bfdbfe}
.tools{display:flex;flex-wrap:wrap;gap:8px;padding:12px 18px;background:#fafcff;border-bottom:1px solid var(--line)}
.chip{font-size:12px;color:var(--ink2);border:1px solid var(--line);background:#fff;border-radius:999px;padding:2px 11px;cursor:pointer}
.chip.on{background:#0f172a;color:#fff;border-color:#0f172a}
.search{flex:1;min-width:180px;border:1px solid var(--line);border-radius:8px;padding:4px 10px;font-size:12.5px;outline:none}
table{width:100%;border-collapse:collapse}
th{text-align:left;font-size:11.5px;color:var(--ink3);font-weight:500;background:#f8fafc;padding:8px 14px;border-bottom:1px solid var(--line)}
td{padding:8px 14px;border-top:1px solid var(--line2);font-size:12.5px}
.ok-s{color:var(--ok)}.bad-s{color:var(--hot)}
.foot{background:#f8fafc;border:1px solid var(--line);border-radius:12px;padding:13px 18px;font-size:12px;color:var(--ink2);line-height:1.7;margin-top:24px}
.empty{padding:26px;text-align:center;color:var(--ink3);font-size:13px}
@media(max-width:720px){.stats{grid-template-columns:repeat(2,1fr)}.row-side{display:none}}
"""

JS = """
(function(){
  var chips=[].slice.call(document.querySelectorAll('.chip[data-org]'));
  var rows=[].slice.call(document.querySelectorAll('.row'));
  var q=document.getElementById('q');
  var cur='ALL';
  function apply(){
    var kw=(q&&q.value||'').trim().toLowerCase();
    rows.forEach(function(r){
      var okOrg = cur==='ALL' || r.dataset.org===cur;
      var okKw = !kw || (r.dataset.text||'').indexOf(kw)>=0;
      r.style.display = (okOrg&&okKw)?'':'none';
    });
    document.querySelectorAll('.group').forEach(function(g){
      var vis=[].slice.call(g.querySelectorAll('.row')).some(function(r){return r.style.display!=='none';});
      g.style.display=vis?'':'none';
    });
  }
  chips.forEach(function(c){c.addEventListener('click',function(){
    chips.forEach(function(x){x.classList.remove('on')});c.classList.add('on');cur=c.dataset.org;apply();});});
  if(q) q.addEventListener('input',apply);
})();
"""


def render(ledger, fresh, health):
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
          <span>{esc(label)}</span><span class="n">{len(by_org[org])} 条</span></div>
{rows}
      </div>
"""

    eif_html = ""
    for it in upcoming[:8]:
        d = (date.fromisoformat(it["eif"]) - TODAY).days
        eif_html += f"""      <div class="eif-card">
        <div class="d">{esc(it['org'])} · {it['eif'][:4] + ' 年' if it.get('eif_prec') == 'year' else (it['eif'][:7] if it.get('eif_prec') == 'month' else it['eif'])}</div>
        <div class="t"><a href="{esc(it['link'])}" target="_blank" rel="noopener" style="color:inherit;text-decoration:none">{esc(it['title'][:92])}</a></div>
        <span class="n {eta_class(d)}">{'已生效' if d < 0 else str(d) + ' 天后生效'}</span>
      </div>
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
        health_rows += (f"<tr><td>{esc(h['name'])}</td><td class='{cls}'>{esc(h['status'])}</td>"
                        f"<td>{h['count']}</td></tr>")

    orgs = [o for o in ORG_ORDER if o in by_org]
    chips = "".join(f'<button class="chip" data-org="{o}">{o}</button>' for o in orgs)

    return f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>规范雷达 · {TODAY.isoformat()} 期</title>
<style>{CSS}</style>
</head>
<body>
<div class="wrap">

  <div class="head">
    <h1>规范雷达 · 船级社规范与强制文件改版动态</h1>
    <div class="sub">第 {TODAY.strftime('%Y-%m-%d')} 期 · 覆盖 CCS / DNV / ABS / LR / BV / IMO · 公开信息自动采集</div>
    <div class="stats">
      <div class="stat"><i>本期新增</i><b>{len(fresh)} <small>条</small></b></div>
      <div class="stat"><i>90 天内生效</i><b>{len(soon90)} <small>条</small></b></div>
      <div class="stat"><i>一年内生效</i><b>{len(upcoming)} <small>条</small></b></div>
      <div class="stat"><i>台账累计</i><b>{len(ledger)} <small>条</small></b></div>
    </div>
  </div>

  <h2>一、生效倒计时 <em>按生效日期排序，含已识别生效日的在跟踪条目</em></h2>
  <p class="lead">规范改版真正需要动作的是「哪天开始适用」，这一栏把识别到生效日期的条目按剩余天数排开，30 天内红、90 天内黄。</p>
  <div class="eif-grid">
{eif_html}
  </div>

  <h2>二、本期新增 <em>共 {len(fresh)} 条，按机构分组</em></h2>
  <p class="lead">每条标注机构、类型、生效日与涉及领域；点标题跳原文。列表只做线索整理，具体条款需回原文核对。</p>
  <div class="card">
    <div class="tools">
      <button class="chip on" data-org="ALL">全部</button>
      {chips}
      <input class="search" id="q" placeholder="按关键词筛选，例：ammonia / 消防 / entry into force">
    </div>
{groups_html if groups_html else '<div class="empty">本期未采到有效条目，见文末抓取状态。</div>'}
  </div>

  <h2>三、持续跟踪 <em>往期已收录、本期仍有余温</em></h2>
  <p class="lead">同一事项在多期出现即留在台账里，直到 120 天不再出现才自动清理，避免「看过就丢」。</p>
  <div class="card">
{rows_tracked}
  </div>

  <h2>四、抓取状态 <em>每期公开，失败不隐藏</em></h2>
  <div class="card">
    <table>
      <thead><tr><th>数据源</th><th>状态</th><th>条目</th></tr></thead>
      <tbody>{health_rows}</tbody>
    </table>
  </div>

  <div class="foot">
    <b>使用说明：</b>本报告为<b>公开信息线索汇总</b>，自动采集自船级社官网与公开新闻源，不构成规范解释或合规结论。
    生效日期由标题/摘要正则识别，可能存在偏差，<b>执行前必须以船级社原文或通函为准</b>。
    不涉及任何公司内部资料；条目链接均指向公开发布页面。
  </div>

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

    OUTPUT.mkdir(parents=True, exist_ok=True)
    ARCHIVE.mkdir(parents=True, exist_ok=True)
    html = render(ledger, fresh, health)
    (OUTPUT / "index.html").write_text(html, encoding="utf-8")
    (ARCHIVE / f"{TODAY.isoformat()}.html").write_text(html, encoding="utf-8")
    write_runlog(health, fresh)

    ok = sum(1 for h in health if h["status"] == "OK")
    print(f"[规范雷达] 完成：有效源 {ok}/{len(health)}，本期 {len(fresh)} 条，台账 {len(ledger)} 条")
    print(f"  报告 -> {OUTPUT / 'index.html'}")


if __name__ == "__main__":
    main()
