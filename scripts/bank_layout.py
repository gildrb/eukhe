#!/usr/bin/env python3
"""Lay out the laws and the proofs as the Bend Bank does (Victor Taelin,
bend skill examples/bank), one area per bend/ module:

  LAWS.bend                imports only
  laws/base.bend           spec helpers the laws of two or more areas use
  laws/<area>.bend         the laws of one area and the helpers only they use
  PROOF.bend               imports only
  proof/base.bend          lemmas the proofs of two or more areas use
  proof/<area>/base.bend   lemmas two or more laws of one area use
  proof/<area>/<law>.bend  the fill of one law and the lemmas only it uses

The area of a law is the laws/<area>.bend file that holds it; a law still
in LAWS.bend gets the area of the bend/ module its claim calls
(`Laws.area_of_claims`) and moves to that file.

Laws: each block (a law, a helper, with its comment) keeps its text; a
helper the laws of one area use goes to that area, any other to
laws/base.bend. A section comment (from a `# ---- x ----` line, or any
comment paragraph between two blocks) goes before the first block it
covers in each file that receives one of its laws (copied when they are
in several areas).

Proofs: the script reads every block (a def or a type, with the comment
lines above it) of the proof/ files PROOF.bend imports, follows each
block's references (by name; a name bound inside the block is a local,
not a reference), and places each block:

- a fill (`def <Area>.<law>`) goes to its law's file;
- a lemma that only one law reaches goes to that law's file, one that laws
  of one area reach to the area's base, any other (several areas, or no
  law) to proof/base.bend;
- what a base file uses must be in that base file or a lower one
  (proof/<area>/base.bend, then proof/base.bend): a lemma it uses moves
  down; a fill it uses moves down too when the fill's file imports the
  base file (Bend refuses import cycles). Every such move is reported.

A file past 1,000 lines (SITTING) becomes a folder of the same name:
proof/base.bend -> proof/base/<topic>.bend, a law's lemmas -> proof/<area>/
<law>/<topic>.bend (its fill stays). The topic of a lemma is the code
module or Base type its claim calls (`claim_refs`); a topic still too long
splits by the first def of that topic the claim calls. A lemma joins the
latest topic one of its lemmas is in (Base types, then modules by import
depth; misc, then by name, below a topic), so the topic files never import
in a cycle.

Each file keeps the blocks in their order of the sources (Bend refuses a
call to a def written below it). References are rewritten with the
alias of the file that now holds the name; nothing else in a block
changes. Rerun it after a change to re-place helpers and lemmas (one a
second area or law starts using moves to a base); a run on its own output
changes nothing.

  python3 scripts/bank_layout.py           write the files, print the report
  python3 scripts/bank_layout.py --check   exit 1 if a file would change
  python3 scripts/bank_layout.py --dry-run print the report only
"""
import os
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# the headers of these sources describe an old layout: dropped
OBSOLETE_HEADERS = {"PROOF.bend", "LAWS.bend"}

# the names Base (Bend 2.0.38, `bend base`) declares: no area alias
BASE_NAMES = set("""
ALeaf ANode App Array Audio Bool Chan Char Chr Close Cmp Con Done EQ Either
Emit Empty Equal Event Exists Exit F32 Fail False File GT Halt IO Image Inl
Inr Key LT List Listener Look MLeaf MNode MTip Map Maybe Mouse Move Nat Nil
None Or Pair Pix Poll Process Qua Ready Result SCon SNil Scroll Set Sigma
Socket Some String Succ TCP Text True Tuple U32 UDP Unit WCon WNil Wait
Window Word Zero
""".split())

TOK = re.compile(r"(?<![A-Za-z0-9_.'])([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)")
STR = re.compile(r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])\'')
IMPORT = re.compile(r"^import (\S+)(?: as (\S+))?\s*$")
START = re.compile(r"^(def|type|law) ([A-Za-z_][A-Za-z0-9_.]*)")
CTOR = re.compile(r"^\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{")

PROOF_HEADER = [
    "# eukhe: the proofs. Each law of laws/<area>.bend is proven in",
    "# proof/<area>/<law>.bend from the lemmas of its area (proof/<area>/base.bend)",
    "# and of every area (proof/base.bend). `bend PROOF.bend --verdict` checks them all.",
]
GLOBAL_HEADER = ["# eukhe: lemmas the proofs of two or more areas share"]
LAWS_HEADER = [
    "# eukhe: the laws. laws/<area>.bend holds the laws of one area (the bend/",
    "# module they call) and the spec helpers only they use; laws/base.bend the",
    "# spec helpers of two or more areas. PROOF.bend proves them all.",
]
LAWS_BASE_HEADER = ["# eukhe: the spec helpers the laws of two or more areas use"]


def laws_header(area):
    return [f"# eukhe: the laws of area {area}"]


def area_header(area):
    return [f"# eukhe: lemmas the proofs of area {area} share"]


def law_header(law):
    return [f"# eukhe: the proof of LAW {law}"]


GENERATED_FIRST = re.compile(r"^# eukhe: ")


def mask(line):
    """the code of a line: comments and literals blanked, offsets kept"""
    if line.lstrip().startswith("#"):
        return " " * len(line)
    return STR.sub(lambda m: " " * len(m.group(0)), line)


def camel(name):
    return "".join(p[:1].upper() + p[1:] for p in name.split("_") if p)


# ---------------------------------------------------------------- files


class Src:
    """a parsed .bend file: header comment, imports, blocks"""

    def __init__(self, path):
        self.path = path
        self.rel = path.relative_to(ROOT).as_posix()
        lines = path.read_text().split("\n")
        if lines and lines[-1] == "":
            lines.pop()
        starts = [i for i, l in enumerate(lines) if START.match(l)]
        first = starts[0] if starts else len(lines)
        imps = [i for i, l in enumerate(lines[:first]) if l.startswith("import ")]
        last_imp = imps[-1] if imps else -1
        head = lines[: imps[0]] if imps else []
        while head and head[-1].strip() == "":
            head.pop()
        self.header = head
        self.aliases = {}  # alias -> absolute path
        for i in imps:
            m = IMPORT.match(lines[i])
            if m and m.group(2):
                self.aliases[m.group(2)] = (path.parent / m.group(1)).resolve()
        self.blocks = []
        pending = lines[last_imp + 1 : first]
        while pending and pending[0].strip() == "":
            pending.pop(0)
        for k, s in enumerate(starts):
            e = starts[k + 1] if k + 1 < len(starts) else len(lines)
            body = lines[s:e]
            j = len(body)
            while j > 1 and (body[j - 1].strip() == "" or body[j - 1].startswith("#")):
                j -= 1
            tail = body[j:]
            if k + 1 == len(starts):
                # comments after the last block stay with it
                while tail and tail[-1].strip() == "":
                    tail.pop()
                j += len(tail)
                tail = []
            m = START.match(body[0])
            self.blocks.append(Block(self, m.group(1), m.group(2), pending + body[:j], len(pending)))
            pending = tail


class Block:
    def __init__(self, src, kind, name, lines, start):
        self.src = src
        self.start = start  # the index of the def line
        self.kind = kind
        self.name = name
        self.lines = lines
        self.ctors = []
        if kind == "type":
            self.ctors = [m.group(1) for l in lines[start + 1 :] if (m := CTOR.match(l))]
        self.occ = []  # (line index, start, end, symbol)


# ---------------------------------------------------------------- binders

PARAM = re.compile(r"(?:^|[(,]|\bfor|\bexs|@)\s*[+\-~]?([A-Za-z_]\w*)\s*:(?![:=])")
CASE = re.compile(r"^\s*case (.*):\s*$")
LET = re.compile(r"^\s*[+\-]?([A-Za-z_]\w*)\s*(?::[^=]*)?=(?![=>])")
TUPLE = re.compile(r"^\s*\(([^()]*)\)\s*=(?![=>])")
LAM = re.compile(r"([A-Za-z_]\w*)\s*=>")
LAMS = re.compile(r"\(([^()]*)\)\s*=>")
PCT = re.compile(r"%([A-Za-z_]\w*)@")
WORD = re.compile(r"[A-Za-z_]\w*")


def binders(code_lines):
    out = set()
    for c in code_lines:
        out.update(PARAM.findall(c))
        m = CASE.match(c)
        if m:
            pat = m.group(1)
            for t in TOK.finditer(pat):
                rest = pat[t.end() :].lstrip()
                if "." not in t.group(1) and not rest.startswith("{"):
                    out.add(t.group(1))
        m = LET.match(c)
        if m:
            out.add(m.group(1))
        m = TUPLE.match(c)
        if m:
            out.update(WORD.findall(m.group(1)))
        out.update(LAM.findall(c))
        for g in LAMS.findall(c):
            out.update(WORD.findall(g))
        out.update(PCT.findall(c))
    return out


# ---------------------------------------------------------------- laws


class Laws:
    """the law modules: LAWS.bend and the laws/ files it imports"""

    def __init__(self):
        self.index = (ROOT / "LAWS.bend").resolve()
        self.law_mod = {}  # law -> module path
        self.helper_mod = {}  # helper -> module path
        self.order = {}  # law -> position
        self.area = {}  # law -> area
        self.modules = {}  # path -> Src
        self.multi = {}  # law -> modules its claim calls (several)
        self.witness = {}  # law -> law it takes its area from
        idx = Src(self.index)
        self.modules[self.index] = idx
        self.alias = {self.index: "Laws"}  # module path -> its alias
        for a, p in idx.aliases.items():
            if p.parent == (ROOT / "laws").resolve():
                self.modules[p] = Src(p)
                self.alias[p] = a
        for path, src in self.modules.items():
            for b in src.blocks:
                if b.kind == "law":
                    self.order[b.name] = len(self.order)
                    self.law_mod[b.name] = path
                else:
                    self.helper_mod[b.name] = path
        for law, path in self.law_mod.items():
            if path != self.index:
                self.area[law] = path.stem
        if any(p == self.index for p in self.law_mod.values()):
            self.area_of_claims(idx)

    def area_of_claims(self, src):
        """the area of a law of LAWS.bend: the bend/ module its claim
        calls (spec helpers inlined); bend/ffi_<x>.bend is area <x>,
        bend/wire.bend (and wire_flat) area wire; of several, not wire
        and not spec, then the first called; no call: the modules of its
        types; none at all (a witness or an example): the area of the
        nearest law whose premise it witnesses or that shares a helper"""
        blocks = {b.name: b for b in src.blocks}
        helpers = {b.name for b in src.blocks if b.kind != "law"}

        def module(alias):
            x = src.aliases[alias].stem
            if x.startswith("ffi_"):
                x = x[4:]
            return "wire" if x == "wire_flat" else x

        def walk(name, seen, calls, out):
            b = blocks[name]
            for line in b.lines[1:] if b.kind == "law" else b.lines:
                c = mask(line)
                for m in TOK.finditer(c):
                    t = m.group(1)
                    nxt = c[m.end() : m.end() + 1]
                    head = t.split(".")[0]
                    if "." in t and head in src.aliases:
                        if not calls or (nxt and nxt in "({"):
                            mod = module(head)
                            if mod not in out:
                                out.append(mod)
                    elif t in helpers and t not in seen and t != name:
                        seen.add(t)
                        walk(t, seen, calls, out)

        def helper_set(name):
            seen = set()
            walk(name, seen, False, [])
            return seen

        pending = []
        for law in (b.name for b in src.blocks if b.kind == "law"):
            called = []
            walk(law, set(), True, called)
            core = [m for m in called if m not in ("wire", "spec")]
            if not core:
                typed = []
                walk(law, set(), False, typed)
                core = [m for m in typed if m not in ("wire", "spec")]
                called = called or typed
            if core:
                self.area[law] = core[0]
                if len(core) > 1:
                    self.multi[law] = core
            elif "wire" in called:
                self.area[law] = "wire"
            elif called:
                self.area[law] = called[0]
            else:
                pending.append(law)
        for law in pending:
            claim = blocks[law].lines[-1].strip()
            cands = [
                n
                for n in self.area
                if any(l.strip().startswith("for") and claim in l for l in blocks[n].lines)
            ]
            if not cands:
                hs = helper_set(law)
                cands = [n for n in self.area if hs & helper_set(n)]
            if not cands:
                self.area[law] = "misc"
                self.witness[law] = None
                continue
            best = min(cands, key=lambda n: abs(self.order[n] - self.order[law]))
            self.area[law] = self.area[best]
            self.witness[law] = best


# ---------------------------------------------------------------- laws out


def trim(lines):
    lines = list(lines)
    while lines and lines[0].strip() == "":
        lines.pop(0)
    while lines and lines[-1].strip() == "":
        lines.pop()
    return lines


def split_pre(b):
    """a block's leading lines: (paragraphs that end the block above,
    section comment, its own comment). The section comment starts at a
    `# ---- ` line; without one, every detached paragraph is section."""
    pre = b.lines[: b.start]
    k = len(pre)
    while k > 0 and pre[k - 1].startswith("#"):
        k -= 1
    detached = pre[:k]
    head = next((i for i, l in enumerate(detached) if l.startswith("# ---- ")), None)
    if head is None:
        return [], trim(detached), pre[k:]
    return trim(detached[:head]), trim(detached[head:]), pre[k:]


def proof_aliases():
    """the aliases the proof files give bend/ modules"""
    out = set()
    for f in [ROOT / "PROOF.bend"] + sorted((ROOT / "proof").rglob("*.bend")):
        for a, q in Src(f.resolve()).aliases.items():
            if (ROOT / "proof") not in q.parents and (ROOT / "laws") not in q.parents and q.name != "LAWS.bend":
                out.add(a)
    return out


def layout_laws(laws):
    """the text of LAWS.bend and of every laws/ file, and the report"""
    srcs = list(laws.modules.values())
    lawdir = (ROOT / "laws").resolve()
    owner, by_src = {}, defaultdict(set)
    for s in srcs:
        for b in s.blocks:
            for n in dict.fromkeys([b.name] + b.ctors):
                if n in owner:
                    raise SystemExit(f"{n}: defined in {owner[n].src.rel} and {s.rel}")
                owner[n] = b
                by_src[s.path].add(n)
    mod_alias = {}
    for s in srcs:
        for alias, q in s.aliases.items():
            if q in laws.modules:
                continue
            if mod_alias.get(alias, q) != q:
                raise SystemExit(f"{s.rel}: alias {alias} is {q}, elsewhere {mod_alias[alias]}")
            mod_alias[alias] = q
        for b in s.blocks:
            code = [mask(l) for l in b.lines]
            local = binders(code)
            for i, c in enumerate(code):
                for m in TOK.finditer(c):
                    t = m.group(1)
                    if i == b.start and m.start() == len(b.kind) + 1:
                        continue
                    head, _, rest = t.partition(".")
                    if rest and head in s.aliases:
                        q = s.aliases[head]
                        if q in laws.modules:
                            if rest not in by_src[q]:
                                raise SystemExit(f"{s.rel}:{b.name}: {t} is not in {q.name}")
                            b.occ.append((i, m.start(), m.end(), ("lsym", rest)))
                        else:
                            b.occ.append((i, m.start(), m.end(), ("mod", head)))
                    elif t in by_src[s.path] and t not in local:
                        b.occ.append((i, m.start(), m.end(), ("lsym", t)))
    blocks = [b for s in srcs for b in s.blocks]
    dep = {id(b): [owner[sym[1]] for *_, sym in b.occ if sym[0] == "lsym" and owner[sym[1]] is not b] for b in blocks}
    users = defaultdict(set)  # helper -> areas whose laws reach it
    for b in blocks:
        if b.kind != "law":
            continue
        stack, seen = [b], {id(b)}
        while stack:
            for d in dep[id(stack.pop())]:
                if d.kind == "law":
                    raise SystemExit(f"{b.name}: uses law {d.name}")
                if id(d) not in seen:
                    seen.add(id(d))
                    users[id(d)].add(laws.area[b.name])
                    stack.append(d)
    home, unreached = {}, []
    for b in blocks:
        if b.kind == "law":
            home[id(b)] = laws.area[b.name]
        elif len(users[id(b)]) == 1:
            home[id(b)] = next(iter(users[id(b)]))
        else:
            if not users[id(b)]:
                unreached.append(b)
            # a helper no law uses stays where it is
            keep = b.src.path.parent == lawdir and not users[id(b)]
            home[id(b)] = b.src.path.stem if keep else "base"
    changed = True
    while changed:
        changed = False
        for b in blocks:
            for d in dep[id(b)]:
                if home[id(d)] not in (home[id(b)], "base"):
                    home[id(d)] = "base"
                    changed = True

    # aliases: the area in CamelCase; Laws appended on a clash
    taken = set(mod_alias) | proof_aliases() | BASE_NAMES | {"Laws", "LawsBase", "L", "LA", "Base"}
    taken |= {"P" + camel(law) for law in laws.law_mod}
    areas = list(dict.fromkeys(laws.area[law] for law in sorted(laws.law_mod, key=laws.order.get)))
    alias, suffixed = {"base": "LawsBase"}, []
    for a in areas:
        name = camel(a)
        if name in taken:
            name += "Laws"
            suffixed.append((a, name))
        if name in taken or name in alias.values():
            raise SystemExit(f"alias {name} of area {a} is taken")
        alias[a] = name

    # section comments: each covers the blocks up to the next one
    run_of, runs = {}, []
    for s in srcs:
        cur = None
        for b in s.blocks:
            orphan, section, own = split_pre(b)
            b.orphan, b.own = orphan, own
            if section or cur is None:
                cur = len(runs)
                runs.append((section, []))
            runs[cur][1].append(b)
            run_of[id(b)] = cur
    run_files = []
    for section, covered in runs:
        law_areas = list(dict.fromkeys(home[id(b)] for b in covered if b.kind == "law"))
        run_files.append(law_areas or list(dict.fromkeys(home[id(b)] for b in covered)))
    copied = [(sec[0], files) for (sec, _), files in zip(runs, run_files) if sec and len(files) > 1]

    outputs = {}
    files = ["base"] + areas
    for f in files:
        mine = [b for b in blocks if home[id(b)] == f]
        if not mine:
            continue
        path = lawdir / f"{f}.bend"
        out, used, uses_base, done = [], set(), False, set()
        for k, b in enumerate(mine):
            r = run_of[id(b)]
            if f in run_files[r] and r not in done and runs[r][0]:
                done.add(r)
                out += [""] + runs[r][0]
            lines = list(b.lines)
            for i, st, en, sym in sorted(b.occ, key=lambda o: (o[0], -o[1])):
                if sym[0] == "mod":
                    used.add(sym[1])
                    continue
                h = home[id(owner[sym[1]])]
                if h == f:
                    text = sym[1]
                else:
                    uses_base = True
                    text = f"LawsBase.{sym[1]}"
                lines[i] = lines[i][:st] + text + lines[i][en:]
            out += [""] + b.own + lines[b.start :]
            # paragraphs that ended this block in its source
            nxt = b.src.blocks.index(b) + 1
            if nxt < len(b.src.blocks) and b.src.blocks[nxt].orphan:
                out += [""] + b.src.blocks[nxt].orphan
        head = LAWS_BASE_HEADER if f == "base" else laws_header(f)
        extra = [] if laws.modules.get(path) is None else trim(
            laws.modules[path].header[1:] if laws.modules[path].header and GENERATED_FIRST.match(laws.modules[path].header[0]) else laws.modules[path].header
        )
        imps = ["import Base"]
        for a in sorted(used, key=lambda a: (mod_alias[a].as_posix(), a)):
            imps.append(f"import ../{mod_alias[a].relative_to(ROOT).as_posix()} as {a}")
        if uses_base:
            imps.append("import ./base.bend as LawsBase")
        text = "\n".join(head + (["#"] + extra if extra else []) + [""] + imps + out)
        outputs[path] = re.sub(r"\n{3,}", "\n\n", text) + "\n"
    index = LAWS_HEADER + ["", "import Base"]
    for f in files:
        if (lawdir / f"{f}.bend") in outputs:
            index.append(f"import ./laws/{f}.bend as {alias[f]}")
    outputs[laws.index] = "\n".join(index) + "\n"

    rep = []
    counts = Counter(laws.area.values())
    rep.append("law areas (laws): " + ", ".join(f"{a} {counts[a]}" for a in areas))
    nbase = sum(1 for b in blocks if home[id(b)] == "base")
    rep.append(f"laws/base.bend: {nbase} helpers")
    for a, name in suffixed:
        rep.append(f"area {a}: alias {name} ({camel(a)} is taken)")
    for first, fs in copied:
        rep.append(f"section comment copied into {', '.join(fs)}: {first}")
    for b in unreached:
        rep.append(f"helper no law uses: {b.name} (in laws/{home[id(b)]}.bend)")
    return outputs, rep


# ---------------------------------------------------------------- places

GLOBAL = ("base",)


def area_place(a):
    return ("area", a)


def law_place(law, a):
    return ("law", a, law)


def parent(place):
    if place[0] == "law":
        return area_place(place[1])
    if place[0] == "area":
        return GLOBAL
    return None


def chain(place):
    out = []
    while place is not None:
        out.append(place)
        place = parent(place)
    return out


def meet(a, b):
    ca = chain(a)
    for p in chain(b):
        if p in ca:
            return p
    return GLOBAL


def place_path(place):
    if place == GLOBAL:
        return ROOT / "proof" / "base.bend"
    if place[0] == "area":
        return ROOT / "proof" / place[1] / "base.bend"
    return ROOT / "proof" / place[1] / f"{place[2]}.bend"


# ---------------------------------------------------------------- folders

SITTING = 1000  # lines one reads in a sitting; a longer file becomes a folder

# Base types, the most basic first: a lemma goes to the topic of its claim,
# or to a later topic one of its lemmas is in, so a topic file imports only
# earlier ones (no cycle)
BASE_TOPICS = ["logic", "bool", "nat", "u32", "char", "string", "list", "maybe", "pair", "equal"]
TYPE_TOPIC = {"Bool": "bool", "Nat": "nat", "U32": "u32", "Word": "u32", "Char": "char",
              "String": "string", "List": "list", "Maybe": "maybe", "Pair": "pair", "Equal": "equal"}


def global_topic_header(tp):
    return [f"# eukhe: lemmas the proofs of two or more areas share: {'/'.join(tp)}"]


def area_topic_header(area, tp):
    return [f"# eukhe: lemmas the proofs of area {area} share: {'/'.join(tp)}"]


def law_topic_header(law, tp):
    return [f"# eukhe: lemmas of the proof of LAW {law}: {'/'.join(tp)}"]


def fk_path(fk):
    pl, tp = fk
    path = place_path(pl)
    if not tp:
        return path
    return path.with_suffix("").joinpath(*tp[:-1], tp[-1] + ".bend")


def code_area(path):
    """the area of a bend/ module: bend/<x>.bend, bend/ffi_<x>.bend and
    bend/<x>/<part>.bend are area <x>; bend/wire_flat.bend is wire"""
    bend = (ROOT / "bend").resolve()
    x = path.stem if path.parent == bend else path.parent.name
    if x.startswith("ffi_"):
        x = x[4:]
    return "wire" if x == "wire_flat" else x


_DEPTH = {}


def code_depth(path):
    """1 + the longest chain of bend/ imports below a module"""
    if path not in _DEPTH:
        _DEPTH[path] = 0
        below = [q for q in Src(path).aliases.values() if q.suffix == ".bend" and q.exists()] if path.exists() else []
        _DEPTH[path] = 1 + max((code_depth(q) for q in below), default=0)
    return _DEPTH[path]


def signature(b):
    """the masked text of a def's parameters and of its claim"""
    text = ""
    for line in b.lines[b.start :]:
        text += " " + mask(line)
        if "->" in text and mask(line).rstrip().endswith(":"):
            break
    i = text.find("->")
    return (text[:i], text[i + 2 :]) if i >= 0 else (text, "")


def claim_refs(b):
    """(topic, first name after it) of each code module or Base type the
    claim of b calls (a name before `(` or `{`), in order; else the
    parameters' calls; else the types the claim, then the parameters,
    name"""
    params, claim = signature(b)
    for part, calls in ((claim, True), (params, True), (claim, False), (params, False)):
        out = []
        for m in TOK.finditer(part):
            if calls and part[m.end() : m.end() + 1] not in ("(", "{"):
                continue
            head, _, rest = m.group(1).partition(".")
            q = b.src.aliases.get(head)
            if q is not None and (ROOT / "bend") in q.parents:
                out.append((code_area(q), rest.split(".")[0]))
            elif head in TYPE_TOPIC and (rest or not calls):
                out.append((TYPE_TOPIC[head], rest.split(".")[0]))
        if out:
            return out
    return []


def topic_rank(t):
    if t in BASE_TOPICS:
        return (0, BASE_TOPICS.index(t), t)
    paths = [p for p in (ROOT / "bend").rglob("*.bend") if code_area(p.resolve()) == t]
    return (1, max((code_depth(p.resolve()) for p in paths), default=0), t)


def split_file(fk, mine, level, dep, fkey, sub, laws):
    """give each block of the file fk the topic of the next level; the
    fill of a law's file, and the lemmas that use it, stay"""
    pl, tp = fk
    stay = set()
    if pl[0] == "law" and level == 0:
        for b in mine:
            if b.fill or any(id(d) in stay for d in dep[id(b)]):
                stay.add(id(b))
    raw = {}
    for b in mine:
        if id(b) in stay:
            continue
        if level == 0:
            refs = claim_refs(b)
            raw[id(b)] = laws.area[b.fill] if b.fill else refs[0][0] if refs else "logic"
        else:
            topic = tp[-1]
            names = [n for t, n in claim_refs(b) if t == topic and n]
            raw[id(b)] = names[0] if names else "misc"
    if level == 0:
        rank = topic_rank
    else:
        # a sub-topic of a few lemmas joins misc
        size = Counter()
        for b in mine:
            if id(b) in raw:
                size[raw[id(b)]] += len(b.lines) - b.start  # the def, not its comment
        for k in raw:
            if size[raw[k]] < SMALL:
                raw[k] = "misc"
        def rank(t):
            # misc first, then by name: any fixed order keeps the files acyclic
            return (t != "misc", t)
    for b in mine:
        if id(b) in stay:
            continue
        t = raw[id(b)]
        for d in dep[id(b)]:
            if fkey(d)[0] == pl and id(d) in raw and len(sub[id(d)]) == level + 1 and sub[id(d)][:level] == tp:
                if rank(sub[id(d)][level]) > rank(t):
                    t = sub[id(d)][level]
        sub[id(b)] = tp + (t,)


SMALL = 60  # lines: a smaller sub-topic joins misc


# ---------------------------------------------------------------- main


def sources(laws):
    """PROOF.bend and the proof files it imports, dependencies first"""
    proof = (ROOT / "PROOF.bend").resolve()
    order, seen = [], set()

    def visit(path):
        if path in seen:
            return
        seen.add(path)
        src = Src(path)
        for p in src.aliases.values():
            if p.suffix == ".bend" and (ROOT / "proof") in p.parents:
                visit(p)
        order.append(src)

    visit(proof)
    return order


def resolve(srcs, laws):
    """symbols of every reference; returns name -> block, the module
    alias -> path map, and the errors"""
    owner = {}  # proof symbol -> block
    for s in srcs:
        for b in s.blocks:
            if b.kind == "law":
                raise SystemExit(f"{s.rel}: declares law {b.name}")
            for n in dict.fromkeys([b.name] + b.ctors):
                if n in owner:
                    raise SystemExit(f"{n}: defined in {owner[n].src.rel} and {s.rel}")
                owner[n] = b
    by_src = defaultdict(set)
    for n, b in owner.items():
        by_src[b.src.path].add(n)
    lawmods = set(laws.modules)
    proofs = {s.path for s in srcs}
    mod_alias = {}
    errors = []
    for s in srcs:
        own = by_src[s.path]
        for alias, p in s.aliases.items():
            if p in lawmods or p in proofs:
                continue
            if mod_alias.get(alias, p) != p:
                errors.append(f"{s.rel}: alias {alias} is {p}, elsewhere {mod_alias[alias]}")
            mod_alias[alias] = p
        for b in s.blocks:
            code = [mask(l) for l in b.lines]
            local = binders(code)
            fill = None
            for i, c in enumerate(code):
                for m in TOK.finditer(c):
                    t = m.group(1)
                    head, _, rest = t.partition(".")
                    sym = None
                    if rest and head in s.aliases:
                        p = s.aliases[head]
                        if p in lawmods:
                            # by name: a law or helper may have moved
                            if rest in laws.law_mod:
                                sym = ("law", rest)
                            elif rest in laws.helper_mod:
                                sym = ("helper", rest)
                            else:
                                errors.append(f"{s.rel}:{b.name}: {t} is no law nor helper")
                                continue
                        elif p in proofs:
                            if rest not in by_src[p]:
                                errors.append(f"{s.rel}:{b.name}: {t} is not in {p.name}")
                                continue
                            sym = ("proof", rest)
                        else:
                            sym = ("mod", head)
                    elif t in own and (t not in local or (i == b.start and m.start() == len(b.kind) + 1)):
                        sym = ("proof", t)
                    if sym is None:
                        continue
                    if i == b.start and m.start() == len(b.kind) + 1:
                        if sym[0] == "law":
                            fill = sym[1]
                    b.occ.append((i, m.start(), m.end(), sym))
            b.fill = fill
    return owner, mod_alias, errors


def main():
    check = "--check" in sys.argv
    dry = "--dry-run" in sys.argv
    first = laws = Laws()
    laws_out, laws_rep = layout_laws(laws)
    laws_stale = [m for m in laws.modules if m not in laws_out]
    laws_differs = [q for q, t in laws_out.items() if not q.exists() or q.read_text() != t] + laws_stale
    if not check and not dry:
        for q in laws_stale:
            q.unlink()
        for q, t in laws_out.items():
            q.parent.mkdir(parents=True, exist_ok=True)
            q.write_text(t)
        laws = Laws()
    srcs = sources(laws)
    owner, mod_alias, errors = resolve(srcs, laws)
    if errors:
        print("\n".join(errors))
        sys.exit(1)
    blocks = [b for s in srcs for b in s.blocks]
    fills = {b.fill: b for b in blocks if b.fill}
    missing = sorted(set(laws.law_mod) - set(fills), key=laws.order.get)
    if missing:
        print("laws without a fill: " + ", ".join(missing))
        sys.exit(1)

    def deps(b):
        out = []
        for _, _, _, sym in b.occ:
            if sym[0] == "proof":
                d = owner[sym[1]]
                if d is not b:
                    out.append(d)
            elif sym[0] == "law" and sym[1] != b.fill:
                out.append(fills[sym[1]])
        return out

    dep = {id(b): deps(b) for b in blocks}
    # the laws that reach each lemma, through no other fill
    users = defaultdict(set)
    for law, f in fills.items():
        stack, seen = [f], {id(f)}
        while stack:
            x = stack.pop()
            for d in dep[id(x)]:
                if d.fill or id(d) in seen:
                    continue
                seen.add(id(d))
                users[id(d)].add(law)
                stack.append(d)
    place = {}
    unreached = []
    for b in blocks:
        if b.fill:
            place[id(b)] = law_place(b.fill, laws.area[b.fill])
            continue
        us = users[id(b)]
        if not us:
            unreached.append(b)
            place[id(b)] = GLOBAL
        elif len(us) == 1:
            (law,) = us
            place[id(b)] = law_place(law, laws.area[law])
        else:
            areas = {laws.area[u] for u in us}
            place[id(b)] = area_place(areas.pop()) if len(areas) == 1 else GLOBAL

    def imports_of(pl):
        """the places a place's file imports: its blocks' references"""
        out = set()
        for b in blocks:
            if place[id(b)] != pl:
                continue
            for d in dep[id(b)]:
                q = place[id(d)]
                if q != pl:
                    out.add(q)
        return out

    def reaches(src, dst):
        stack, seen = [src], {src}
        while stack:
            x = stack.pop()
            if x == dst:
                return True
            for y in imports_of(x):
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return False

    moved = []  # (law, from, to, reason)
    changed = True
    while changed:
        changed = False
        for b in blocks:
            pl = place[id(b)]
            if pl[0] == "law":
                continue
            for d in dep[id(b)]:
                q = place[id(d)]
                if q in chain(pl):
                    continue
                if d.fill:
                    # a base file may import a fill's file when that file
                    # does not import it back
                    if q[0] == "law" and not reaches(q, pl):
                        continue
                    new = meet(pl, q)
                    moved.append((d.fill, q, new, b.name))
                else:
                    new = meet(pl, q)
                place[id(d)] = new
                changed = True
    # a law file must not reach itself through law files
    order_places = []
    for b in blocks:
        if place[id(b)] not in order_places:
            order_places.append(place[id(b)])
    for pl in order_places:
        for q in imports_of(pl):
            if reaches(q, pl):
                raise SystemExit(f"import cycle: {place_path(pl)} and {place_path(q)}")

    # ------------------------------------------------------------ write
    module_order = sorted(mod_alias, key=lambda a: (mod_alias[a].as_posix(), a))
    law_alias = {}
    taken = set(mod_alias) | set(laws.alias.values()) | {"L", "LA", "LL", "Base"}
    for law in laws.law_mod:
        a = "P" + camel(law)
        if a in taken:
            raise SystemExit(f"alias {a} of law {law} is taken")
        taken.add(a)
        law_alias[law] = a

    # a file is a place and a topic path (empty: the place's own file)
    sub = {id(b): () for b in blocks}

    def fkey(b):
        return (place[id(b)], sub[id(b)])

    def alias_in(fk):
        """the name a proof file gives the file fk"""
        pl, tp = fk
        if pl == GLOBAL:
            return "L" + "".join(camel(t) for t in tp)
        if pl[0] == "area":
            return "LA" + "".join(camel(t) for t in tp)
        if not tp:
            return law_alias[pl[2]]
        return "LL" + "".join(camel(t) for t in tp)

    def index_name(fk):
        """the name PROOF.bend gives the file fk"""
        pl, tp = fk
        if pl == GLOBAL:
            return "L" + "".join(camel(t) for t in tp)
        if pl[0] == "area":
            return "LA" + camel(pl[1]) + "".join(camel(t) for t in tp)
        if not tp:
            return law_alias[pl[2]]
        return "LL" + camel(pl[2]) + "".join(camel(t) for t in tp)

    extra_header = {}
    for s in srcs:
        if s.rel in OBSOLETE_HEADERS or not s.blocks:
            continue
        head = list(s.header)
        if head and GENERATED_FIRST.match(head[0]):
            head = head[1:]
        while head and head[0].strip() in ("", "#"):
            head.pop(0)
        if not head:
            continue
        fs = [b for b in s.blocks if b.fill]
        if len(fs) == 1:
            target = place[id(fs[0])]
        else:
            target = Counter(place[id(b)] for b in s.blocks).most_common(1)[0][0]
        extra_header.setdefault((target, ()), head)

    def render():
        files = list(dict.fromkeys(fkey(b) for b in blocks))
        outputs = {}
        for fk in files:
            pl, tp = fk
            path = fk_path(fk)
            mine = [b for b in blocks if fkey(b) == fk]
            body, used_mods, used_files, used_laws = [], [], set(), set()
            for b in mine:
                lines = list(b.lines)
                for i, st, en, sym in sorted(b.occ, key=lambda o: (o[0], -o[1])):
                    if sym[0] == "proof":
                        q = fkey(owner[sym[1]])
                        text = sym[1] if q == fk else f"{alias_in(q)}.{sym[1]}"
                        if q != fk:
                            used_files.add(q)
                    elif sym[0] == "law":
                        mod = laws.law_mod[sym[1]]
                        used_laws.add(mod)
                        text = f"{laws.alias[mod]}.{sym[1]}"
                        if not (i == b.start and st == len(b.kind) + 1) and sym[1] != b.fill:
                            q = fkey(fills[sym[1]])
                            if q != fk:
                                used_files.add(q)
                    elif sym[0] == "helper":
                        mod = laws.helper_mod[sym[1]]
                        used_laws.add(mod)
                        text = f"{laws.alias[mod]}.{sym[1]}"
                    else:
                        if sym[1] not in used_mods:
                            used_mods.append(sym[1])
                        continue
                    lines[i] = lines[i][:st] + text + lines[i][en:]
                body.append(lines)
            rel = os.path.relpath(ROOT, path.parent)
            if pl[0] == "law":
                head = law_header(pl[2]) if not tp else law_topic_header(pl[2], tp)
            elif pl[0] == "area":
                head = area_header(pl[1]) if not tp else area_topic_header(pl[1], tp)
            else:
                head = GLOBAL_HEADER if not tp else global_topic_header(tp)
            if fk in extra_header:
                head = head + ["#"] + extra_header[fk]
            imps = ["import Base"]
            for a in module_order:
                if a in used_mods:
                    imps.append(f"import {rel}/{mod_alias[a].relative_to(ROOT).as_posix()} as {a}")
            for mod in sorted(used_laws, key=lambda m: (m != laws.index, laws.alias[m])):
                imps.append(f"import {rel}/{mod.relative_to(ROOT).as_posix()} as {laws.alias[mod]}")
            for q in sorted(used_files, key=lambda q: (len(chain(q[0])), index_key(q[0], laws), q[1])):
                target = os.path.relpath(fk_path(q), path.parent)
                if not target.startswith("."):
                    target = "./" + target
                imps.append(f"import {target} as {alias_in(q)}")
            out = head + [""] + imps
            for lines in body:
                out.append("")
                out.extend(lines)
            # leading blank lines of a block were kept: no double blank
            outputs[path] = re.sub(r"\n{3,}", "\n\n", "\n".join(out)) + "\n"
        index = PROOF_HEADER + ["", "import Base", "import ./LAWS.bend as Laws"]
        for fk in sorted(files, key=lambda q: (index_key(q[0], laws), q[1])):
            index.append(f"import ./{fk_path(fk).relative_to(ROOT).as_posix()} as {index_name(fk)}")
        outputs[(ROOT / "PROOF.bend").resolve()] = "\n".join(index) + "\n"
        return outputs

    # a file past one sitting becomes a folder of the same name, split by
    # the topic of its lemmas, then by the topic's first def they claim
    # about (`topic_of`); a law's fill stays in its file
    outputs = render()
    folders = []
    for level in (0, 1):
        over = [
            fk for fk in dict.fromkeys(fkey(b) for b in blocks)
            if len(fk[1]) == level and outputs[fk_path(fk)].count("\n") > SITTING
        ]
        for fk in over:
            split_file(fk, [b for b in blocks if fkey(b) == fk], level, dep, fkey, sub, laws)
            folders.append(fk_path(fk))
        if not over:
            break
        outputs = render()
    for path, text in outputs.items():
        if path.name != "PROOF.bend" and text.count("\n") > SITTING:
            raise SystemExit(f"{path.relative_to(ROOT)}: {text.count(chr(10))} lines after the split")
    for path, text in outputs.items():
        names = re.findall(r"^import \S+ as (\S+)$", text, re.M)
        if len(names) != len(set(names)):
            raise SystemExit(f"{path.relative_to(ROOT)}: an alias names two imports")

    old = {s.path for s in srcs}
    stale = sorted(p for p in old if p not in outputs)
    differs = laws_differs + [p for p, t in outputs.items() if not p.exists() or p.read_text() != t] + stale
    if dry:
        report(first, laws_rep, blocks, place, unreached, moved, outputs, folders)
        return
    if check:
        for p in differs:
            print(f"would change: {p.relative_to(ROOT)}")
        sys.exit(1 if differs else 0)
    for p in stale:
        p.unlink()
    for p, t in outputs.items():
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(t)
    for d in sorted((ROOT / "proof").rglob("*/"), key=lambda d: -len(d.parts)):
        if d.is_dir() and not any(d.iterdir()):
            d.rmdir()
    report(first, laws_rep, blocks, place, unreached, moved, outputs, folders)


def index_key(q, laws):
    """global base, then per area (in law order): its base, its laws"""
    if q == GLOBAL:
        return (-1, 0, 0)
    area = q[1]
    first = min((laws.order[l] for l, a in laws.area.items() if a == area), default=10**9)
    if q[0] == "area":
        return (first, 0, 0)
    return (first, 1, laws.order[q[2]])


def report(laws, laws_rep, blocks, place, unreached, moved, outputs, folders):
    print("\n".join(laws_rep))
    for path in folders:
        print(f"split into a folder: {path.relative_to(ROOT)}")
    files = [p for p in outputs if p.name != "PROOF.bend"]
    areas = Counter(laws.area[l] for l in laws.law_mod)
    print(f"files: {len(files)} under proof/ (+ PROOF.bend)")
    base = ROOT / "proof" / "base.bend"
    if base in outputs:
        print(f"proof/base.bend: {outputs[base].count(chr(10))} lines, {sum(1 for b in blocks if place[id(b)] == GLOBAL)} blocks")
    print("areas (laws): " + ", ".join(f"{a} {n}" for a, n in sorted(areas.items())))
    for law, mods in laws.multi.items():
        print(f"multi-module law {law}: {' '.join(mods)} -> {laws.area[law]}")
    for law, by in laws.witness.items():
        print(f"no-module law {law}: area {laws.area[law]} (from {by})")
    in_base = [b.fill for b in blocks if b.fill and place[id(b)][0] != "law"]
    for law, q, new, by in moved:
        print(f"fill {law} moved to {place_path(new).relative_to(ROOT)}: {by} there uses it")
    if in_base:
        print("laws filled in a base file: " + ", ".join(in_base))
    for b in unreached:
        print(f"unreached by any law (in proof/base.bend): {b.name} ({b.src.rel})")


if __name__ == "__main__":
    main()
