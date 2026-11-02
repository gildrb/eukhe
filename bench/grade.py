#!/usr/bin/env python3
"""Grade one turn of a classic task: grade.py <task> <repo> <turn> <outdir> <turn-stdout.jsonl>.

Prints {"checks": {name: bool}, "info": {...}}. Turn state (values the model
chose in turn 1) is kept in <outdir>/state.json. Runs in the bench venv (Playwright).
"""
import json
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

import settings

FIX = settings.path("dir") / "fixtures"
PY = sys.executable
SCALE = {4.0, 8.0, 12.0, 16.0, 24.0, 32.0}


def close(a, b, tol=0.5):
    return abs(a - b) <= tol


def turn_text(jsonl):
    """All assistant text of the turn."""
    out = []
    for line in pathlib.Path(jsonl).read_text(errors="replace").splitlines():
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("type") != "message_end":
            continue
        m = d.get("message") or {}
        if m.get("role") != "assistant" or not isinstance(m.get("content"), list):
            continue
        out += [c.get("text", "") for c in m["content"] if c.get("type") == "text"]
    return "\n".join(out)


def run(cmd, cwd, timeout=60):
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return -1, "", "timeout"


class Browser:
    def __enter__(self):
        from playwright.sync_api import sync_playwright  # only the browser tasks need Playwright

        self.pw = sync_playwright().start()
        self.b = self.pw.chromium.launch(executable_path=str(settings.binary("chromium")))
        return self

    def page(self, url, w, h):
        pg = self.b.new_page(viewport={"width": w, "height": h})
        pg.goto(url)
        pg.wait_for_timeout(150)
        return pg

    def __exit__(self, *a):
        self.b.close()
        self.pw.stop()


# ---------------------------------------------------------------- ui_cards
CARDS_JS = r"""
() => {
  const pad = e => { const s = getComputedStyle(e);
    return [s.paddingTop, s.paddingRight, s.paddingBottom, s.paddingLeft].map(parseFloat); };
  const rect = e => { const r = e.getBoundingClientRect();
    return {left: r.left, right: r.right, top: r.top, bottom: r.bottom}; };
  const cards = [...document.querySelectorAll('.card')];
  const foot = document.querySelector('.site-footer');
  const textLeft = e => { const r = document.createRange(); r.selectNodeContents(e); return r.getBoundingClientRect().left; };
  return {
    cards: cards.map(c => ({rect: rect(c), pad: pad(c)})),
    footer: {rect: rect(foot), pad: pad(foot)},
    scrollW: document.scrollingElement.scrollWidth,
    vw: innerWidth,
    titleX: textLeft(document.querySelector('.site-header h1')),
    cardTextX: textLeft(cards[0].querySelector('h3')),
  };
}
"""


def cards_at(br, repo, w):
    pg = br.page((repo / "index.html").as_uri(), w, 800)
    m = pg.evaluate(CARDS_JS)
    pg.close()
    return m


def row_gaps(m):
    c = [x["rect"] for x in m["cards"]]
    return [c[i + 1]["left"] - c[i]["right"] for i in range(len(c) - 1)]


def one_row(m):
    tops = [x["rect"]["top"] for x in m["cards"]]
    return max(tops) - min(tops) < 0.5 and all(g > 0 for g in row_gaps(m))


def grade_ui_cards(repo, turn, state, text):
    c, info = {}, {}
    with Browser() as br:
        wide = cards_at(br, repo, 1200)
        narrow = cards_at(br, repo, 600) if turn == 3 else None
    gaps = row_gaps(wide)
    pad = wide["cards"][0]["pad"]
    same_pad = all(x["pad"] == pad for x in wide["cards"])
    info.update(gaps=gaps, card_pad=pad, footer_pad=wide["footer"]["pad"])
    if turn == 1:
        css = "\n".join(p.read_text() for p in repo.glob("*.css") if p.name != "tokens.css")
        css += "\n".join(re.findall(r"<style[^>]*>(.*?)</style>", (repo / "index.html").read_text(), re.S))
        c["t1_one_row_no_overflow"] = one_row(wide) and wide["scrollW"] <= 1200
        c["t1_gap_from_scale"] = len(set(round(g, 1) for g in gaps)) == 1 and round(gaps[0], 1) in SCALE
        c["t1_padding_from_scale"] = same_pad and all(round(p, 1) in SCALE for p in pad)
        c["t1_uses_space_vars"] = len(re.findall(r"var\(\s*--space-\d", css)) >= 2
        state.update(gap=gaps[0] if gaps else None, pad=pad)
        return c, info
    G, P = state["gap"], state["pad"]
    foot = wide["footer"]
    lowest = max(x["rect"]["bottom"] for x in wide["cards"])
    info["footer_gap"] = foot["rect"]["top"] - lowest
    footer_ok = foot["pad"] == pad and close(foot["rect"]["top"] - lowest, gaps[0] if gaps else -99)
    if turn == 2:
        c["t2_footer_padding_matches_cards"] = foot["pad"] == pad
        c["t2_footer_distance_equals_card_gap"] = close(foot["rect"]["top"] - lowest, gaps[0] if gaps else -99)
        c["t2_cards_unchanged"] = one_row(wide) and all(close(g, G) for g in gaps) and pad == P
        return c, info
    n = narrow
    nc = [x["rect"] for x in n["cards"]]
    vgaps = [nc[i + 1]["top"] - nc[i]["bottom"] for i in range(len(nc) - 1)]
    info.update(narrow_vgaps=vgaps, narrow_scrollW=n["scrollW"], narrow_pad=n["cards"][0]["pad"],
                title_x=[wide["titleX"], n["titleX"]], card_text_x=[wide["cardTextX"], n["cardTextX"]])
    c["t3_no_horizontal_overflow_600"] = n["scrollW"] <= 600
    c["t3_stacked_600"] = len({round(r["left"], 1) for r in nc}) == 1 and all(g > 0 for g in vgaps)
    c["t3_vertical_gap_kept_600"] = all(close(g, G) for g in vgaps)
    c["t3_padding_kept_600"] = all(x["pad"] == P for x in n["cards"])
    c["t3_wide_layout_kept_1200"] = one_row(wide) and all(close(g, G) for g in gaps) and pad == P and footer_ok
    c["t3_title_aligned_1200"] = close(wide["titleX"], wide["cardTextX"])
    c["t3_title_aligned_600"] = close(n["titleX"], n["cardTextX"])
    return c, info


# ---------------------------------------------------------------- measure
HERO_H = 360.34375
PROMO = "QX7-R2M9"
CTA = "rgb(228, 87, 46)"
MEASURE_JS = r"""
() => {
  const r = s => document.querySelector(s).getBoundingClientRect();
  const bg = s => getComputedStyle(document.querySelector(s)).backgroundColor;
  const logo = r('.logo'), nav = r('.nav');
  return {hero: r('.hero').height, cta: bg('.cta'), footer: bg('.site-footer'),
          footerText: document.querySelector('.site-footer').textContent,
          logo: {left: logo.left, right: logo.right, top: logo.top, bottom: logo.bottom},
          nav: {left: nav.left, right: nav.right, top: nav.top, bottom: nav.bottom}};
}
"""


def grade_measure(repo, turn, state, text):
    c = {}
    with Browser() as br:
        pg = br.page((repo / "page.html").as_uri(), 1024, 768)
        m = pg.evaluate(MEASURE_JS)
        pg.close()
    info = {"measured": m}
    if turn == 1:
        nums = [float(x) for x in re.findall(r"(?<![\d#.])(\d{2,4}(?:\.\d+)?)", text)]
        nums = [x for x in nums if x not in (1024.0, 768.0)]
        info["numbers_in_reply"] = nums[:20]
        c["t1_height_reported"] = any(abs(x - HERO_H) <= 1.05 for x in nums)
        c["t1_hex_reported"] = re.search(r"#e4572e\b", text, re.I) is not None
        c["t1_promo_code_reported"] = PROMO in text
        c["t1_no_file_changes"] = run(["git", "diff", "--quiet", "HEAD", "--", "."], repo)[0] == 0
        return c, info
    half_ok = abs(m["hero"] - HERO_H / 2) <= 1.0
    lg, nv = m["logo"], m["nav"]
    if turn == 2:
        c["t2_hero_half_height"] = half_ok
        c["t2_footer_is_button_colour"] = m["footer"] == CTA
        c["t2_button_unchanged"] = m["cta"] == CTA
        c["t2_footer_has_code_after_copyright"] = "©" in m["footerText"] and m["footerText"].find(PROMO) > m["footerText"].find("©")
        return c, info
    c["t3_nav_left_of_logo"] = nv["right"] <= lg["left"] + 0.5
    c["t3_same_row"] = nv["top"] < lg["bottom"] and lg["top"] < nv["bottom"]
    c["t3_hero_kept"] = half_ok
    c["t3_footer_kept"] = m["footer"] == CTA and m["cta"] == CTA and PROMO in m["footerText"]
    return c, info


# ---------------------------------------------------------------- services
def isint(v):
    return isinstance(v, int) and not isinstance(v, bool)


def validate(files):
    """files: {stem: text} -> list of problems."""
    probs, ports = [], {}
    keys = {"name", "port", "replicas", "owner", "healthcheck"}
    for stem, text in sorted(files.items()):
        try:
            o = json.loads(text)
        except ValueError:
            probs.append(f"{stem}: invalid json")
            continue
        if not isinstance(o, dict) or set(o) != keys:
            probs.append(f"{stem}: keys")
            continue
        if o["name"] != stem:
            probs.append(f"{stem}: name")
        if not (isint(o["port"]) and 1024 <= o["port"] <= 65535):
            probs.append(f"{stem}: port")
        else:
            ports.setdefault(o["port"], []).append(stem)
        if not (isint(o["replicas"]) and o["replicas"] >= 1):
            probs.append(f"{stem}: replicas")
        if not (isinstance(o["owner"], str) and re.fullmatch(r"[^@\s]+@example\.org", o["owner"])):
            probs.append(f"{stem}: owner")
        hc = o["healthcheck"]
        if not (isinstance(hc, dict) and set(hc) == {"path", "interval_s"}
                and isinstance(hc["path"], str) and hc["path"].startswith("/")
                and isint(hc["interval_s"]) and 5 <= hc["interval_s"] <= 300):
            probs.append(f"{stem}: healthcheck")
    probs += [f"dup port {p}: {s}" for p, s in ports.items() if len(s) > 1]
    return probs


def load_dir(d):
    return {p.stem: p.read_text() for p in sorted((d / "services").glob("*.json"))}


MUTATIONS = {
    "port_string": ("search", lambda o: o.update(port=str(o["port"]))),
    "port_low": ("search", lambda o: o.update(port=80)),
    "dup_port": ("search", None),  # set to auth's port
    "replicas_zero": ("auth", lambda o: o.update(replicas=0)),
    "path_no_slash": ("auth", lambda o: o["healthcheck"].update(path="healthz")),
    "name_mismatch": ("auth", lambda o: o.update(name="authn")),
    "interval_string": ("gateway", lambda o: o["healthcheck"].update(interval_s="30s")),
    "interval_range": ("gateway", lambda o: o["healthcheck"].update(interval_s=900)),
    "owner_domain": ("gateway", lambda o: o.update(owner="x@example.com")),
    "missing_key": ("profiles", lambda o: o.pop("replicas")),
    "extra_key": ("profiles", lambda o: o.update(region="eu")),
    "invalid_json": ("profiles", None),
}


def checker_on(repo, kind):
    with tempfile.TemporaryDirectory() as t:
        t = pathlib.Path(t) / "r"
        shutil.copytree(repo, t, ignore=shutil.ignore_patterns(".git"))
        if kind:
            stem, fn = MUTATIONS[kind]
            p = t / "services" / f"{stem}.json"
            if kind == "invalid_json":
                p.write_text(p.read_text().rstrip().rstrip("}") + ",}\n")
            else:
                o = json.loads(p.read_text())
                if kind == "dup_port":
                    o["port"] = json.loads((t / "services/auth.json").read_text())["port"]
                else:
                    fn(o)
                p.write_text(json.dumps(o, indent=2) + "\n")
        return run([PY, "scripts/check_configs.py"], t, timeout=60)


def grade_services(repo, turn, state, text):
    c, info = {}, {}
    files = load_dir(repo)
    orig = load_dir(FIX / "services")
    probs = validate(files)
    info["problems"] = probs

    def obj(s):
        return json.loads(files[s]) if s in files else {}

    if turn == 1:
        c["t1_all_valid"] = not probs
        c["t1_no_renames_or_new"] = set(files) == set(orig)
        c["t1_valid_files_untouched"] = all(files.get(s) == orig[s] for s in ("auth", "payments", "gateway", "profiles"))
        o = {s: json.loads(orig[s]) for s in orig if s != "search-indexer"}
        def same_except(s, path, want):
            got = obj(s)
            exp = json.loads(json.dumps(o[s]))
            ref = exp
            for k in path[:-1]:
                ref = ref[k]
            ref[path[-1]] = want
            return got == exp
        c["t1_fix_search_port"] = same_except("search", ["port"], 7003)
        c["t1_fix_reports_interval"] = same_except("reports", ["healthcheck", "interval_s"], 45)
        c["t1_fix_mailer_path"] = same_except("mailer", ["healthcheck", "path"], "/health")
        c["t1_fix_images_name"] = same_except("images", ["name"], "images")
        c["t1_fix_audit_owner"] = same_except("audit", ["owner"], "lena@example.org")
        led = obj("ledger")
        c["t1_fix_ledger_replicas"] = (isinstance(led.get("replicas"), int) and led["replicas"] >= 1
                                       and {k: v for k, v in led.items() if k != "replicas"}
                                       == {k: v for k, v in o["ledger"].items() if k != "replicas"})
        si = files.get("search-indexer", "")
        try:
            c["t1_fix_indexer_json"] = json.loads(si) == {"name": "search-indexer", "port": 7013, "replicas": 1,
                                                           "owner": "omar@example.org",
                                                           "healthcheck": {"path": "/health", "interval_s": 30}}
        except ValueError:
            c["t1_fix_indexer_json"] = False
        cat, ntf = obj("catalog"), obj("notify")
        moved = [s for s, a, b in (("catalog", cat, o["catalog"]), ("notify", ntf, o["notify"])) if a != b]
        one = moved and len(moved) == 1 and {k: v for k, v in obj(moved[0]).items() if k != "port"} == \
            {k: v for k, v in o[moved[0]].items() if k != "port"}
        c["t1_fix_dup_port_one_side"] = bool(one) and not any("dup port" in p for p in probs)
        return c, info
    if turn == 2:
        rc, out, err = checker_on(repo, None)
        info["clean_run"] = {"rc": rc, "out": out[-400:], "err": err[-400:]}
        c["t2_script_exits0_on_valid"] = rc == 0
        c["t2_configs_still_valid"] = not probs
        det = {}
        for kind in MUTATIONS:
            rc2, out2, _ = checker_on(repo, kind)
            det[kind] = rc2 == 1 and bool(out2.strip())
        info["detects"] = det
        for k, v in det.items():
            c[f"t2_detects_{k}"] = v
        return c, info
    others = [json.loads(t)["port"] for s, t in files.items() if s != "billing" and not validate({s: t})]
    b = obj("billing")
    info["billing"] = b
    c["t3_all_valid_incl_billing"] = not probs and "billing" in files
    c["t3_billing_port_max_plus_1"] = bool(others) and b.get("port") == max(others) + 1
    c["t3_billing_replicas_2"] = b.get("replicas") == 2
    c["t3_billing_owner_matches_payments"] = b.get("owner") == obj("payments").get("owner")
    rc, out, err = checker_on(repo, None) if (repo / "scripts/check_configs.py").exists() else (None, "", "")
    c["t3_checker_passes"] = rc == 0
    return c, info


# ---------------------------------------------------------------- ledger
LEDGER_HIDDEN = '''
import unittest
from ledger.convert import to_eur_cents
from ledger.parse import parse_amount, parse_file
from ledger.report import format_total, totals_by_category

class Hidden(unittest.TestCase):
    def test_amounts(self):
        for s, v in (("4.35", 435), ("2.90", 290), ("0.07", 7), ("1158.10", 115810), ("19.99", 1999)):
            self.assertEqual(parse_amount(s), v, s)
    def test_convert(self):
        self.assertEqual(to_eur_cents(1299, "GBP"), 1559)
        self.assertEqual(to_eur_cents(18000, "USD"), 16200)
        self.assertEqual(to_eur_cents(500, "EUR"), 500)
    def test_format(self):
        for c, s in ((5, "€0.05"), (1075, "€10.75"), (3359, "€33.59"), (100, "€1.00")):
            self.assertEqual(format_total(c), s)
    def test_sample_totals(self):
        t = totals_by_category(parse_file("data/sample.csv"))
        self.assertEqual(t, {"coffee": 1075, "books": 3359, "rent": 70000, "travel": 16200})
'''
LEDGER_EXPECTED = ["rent: €700.00", "travel: €162.00", "books: €33.59", "coffee: €10.75"]


def unittest_in(repo, extra=None, original=None):
    """Run the repo's own suite, plus the fixture's original tests and/or hidden tests as extra files."""
    with tempfile.TemporaryDirectory() as t:
        t = pathlib.Path(t) / "r"
        shutil.copytree(repo, t, ignore=shutil.ignore_patterns(".git", "__pycache__"))
        if original:
            shutil.copy(original, t / "tests" / "test_zz_original.py")
        if extra:
            (t / "tests" / "test_zz_hidden.py").write_text(extra)
        rc, out, err = run([PY, "-m", "unittest", "-v"], t, timeout=120)
        ran = re.search(r"Ran (\d+) test", err)
        return rc, int(ran.group(1)) if ran else 0, err[-1500:]


def test_defs(path):
    """{Class.method: ast dump} of the test methods in a file."""
    import ast
    try:
        tree = ast.parse(pathlib.Path(path).read_text())
    except (OSError, SyntaxError):
        return {}
    return {f"{cls.name}.{fn.name}": ast.dump(fn) for cls in tree.body if isinstance(cls, ast.ClassDef)
            for fn in cls.body if isinstance(fn, ast.FunctionDef)}


def grade_ledger(repo, turn, state, text):
    c, info = {}, {}
    orig_test = FIX / "ledger/tests/test_ledger.py"
    orig, now = test_defs(orig_test), test_defs(repo / "tests/test_ledger.py")
    # "Don't edit the existing tests": every original test method is still there, unchanged (new ones may join).
    c[f"t{turn}_original_tests_unchanged"] = all(now.get(k) == v for k, v in orig.items())
    rc, n, err = unittest_in(repo, original=orig_test)
    c[f"t{turn}_suite_passes"] = rc == 0
    rc2, _, err2 = unittest_in(repo, extra=LEDGER_HIDDEN, original=orig_test)
    c[f"t{turn}_hidden_tests_pass"] = rc2 == 0
    if rc2:
        info["hidden_err"] = err2[-800:]
    if turn == 2:
        _, own, _ = unittest_in(repo)
        info["own_suite_ran"] = own
        rcc, out, e = run([PY, "-m", "ledger", "summary", "data/sample.csv"], repo)
        info["cli"] = out.strip().splitlines()
        c["t2_cli_sorted_by_total"] = out.strip().splitlines() == LEDGER_EXPECTED
        c["t2_new_test_added"] = own > len(orig)
    return c, info


# ---------------------------------------------------------------- crm
CRM_HIDDEN = '''
import unittest
from datetime import date, timedelta
from crm.users import User
from crm import stats

T = date(2026, 5, 20)
def u(i, en, days, plan):
    return User(i, f"u{i}", en, T - timedelta(days=days), plan)
USERS = [u(10, True, 1, "free"), u(11, False, 2, "pro"), u(12, True, 28, "team"), u(13, True, 33, "pro"),
         u(14, True, 200, "team"), u(15, False, 90, "free"), u(16, True, 15, "trial"), u(17, True, 3, "pro"),
         u(5, True, 6, "pro")]

class Hidden(unittest.TestCase):
    def test_active(self):
        self.assertEqual(list(stats.active_users(USERS, T)), [5, 10, 12, 16, 17])
    def test_active_empty(self):
        self.assertEqual(list(stats.active_users([], T)), [])
'''
CRM_HIDDEN2 = '''
class Hidden2(unittest.TestCase):
    def test_paying(self):
        self.assertEqual(stats.paying_active_count(USERS, T), 3)
'''


def grade_crm(repo, turn, state, text):
    c, info = {}, {}
    rc, n, err = unittest_in(repo)
    c[f"t{turn}_suite_passes"] = rc == 0
    rc2, _, err2 = unittest_in(repo, extra=CRM_HIDDEN)
    c[f"t{turn}_hidden_active_users"] = rc2 == 0
    if rc2:
        info["hidden_err"] = err2[-800:]
    code = ("from datetime import date;from crm.users import load_users;from crm.stats import active_users;"
            "print(list(active_users(load_users('data/users.json'), date(2026,10,1))))")
    rcd, out, e = run([PY, "-c", code], repo)
    info["data_active"] = out.strip() or e[-300:]
    c[f"t{turn}_active_on_data"] = out.strip() == "[1, 2, 3, 8, 9, 12, 14]"
    if turn == 2:
        rc3, _, err3 = unittest_in(repo, extra=CRM_HIDDEN + CRM_HIDDEN2)
        c["t2_hidden_paying_active"] = rc3 == 0
        rcc, out, e = run([PY, "-m", "crm", "report", "data/users.json", "--today", "2026-10-01"], repo)
        lines = [ln.strip() for ln in out.splitlines()]
        info["cli"] = lines or e[-300:]
        c["t2_cli_active_7"] = "active: 7" in lines
        c["t2_cli_paying_active_4"] = "paying active: 4" in lines
        c["t2_cli_existing_lines_kept"] = "users: 14" in lines and "plan pro: 5" in lines
    return c, info


GRADERS = {"ui_cards": grade_ui_cards, "measure": grade_measure, "services": grade_services,
           "ledger": grade_ledger, "crm": grade_crm}


def main():
    task, repo, turn, outdir, jsonl = sys.argv[1:6]
    repo, turn, outdir = pathlib.Path(repo).resolve(), int(turn), pathlib.Path(outdir)
    sp = outdir / "state.json"
    state = json.loads(sp.read_text()) if sp.exists() else {}
    try:
        checks, info = GRADERS[task](repo, turn, state, turn_text(jsonl))
    except Exception as e:  # a broken page/repo fails the turn's grading, recorded
        checks, info = {f"t{turn}_gradable": False}, {"error": repr(e)}
    sp.write_text(json.dumps(state))
    print(json.dumps({"checks": checks, "info": info}))


if __name__ == "__main__":
    main()
