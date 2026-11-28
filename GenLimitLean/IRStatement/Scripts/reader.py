"""Generate, save and verify the IR statements.

Default: verify Readings/P01.md (the first experiment) with its negative controls.
`--papers 00 00A 02 …` verifies the papers listed; `--all` verifies every paper, P00–P39, and
writes the check log Readings/RUN-LOG.md, the reading index and the rule cards. With --write the
selected pages are regenerated, verified as staged copies, and only then published.

Verification reads each saved body from disk, parses it under the paper's grammar (exactly
one complete parse required), compares the parse with the tree selected from the Lean
export, renders the *parsed* tree as a Lean proposition and asks the kernel to compare it
with the declaration's entire type.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import re
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True  # keep the folders free of caches
BASE = Path(__file__).resolve().parents[1]  # the IRStatement folder
sys.path.insert(0, str(Path(__file__).resolve().parent))
from runner import Grammar, KEYS, LAKE, LEAN, inventory, run
from selector import label_words, paper_names, select
import cards
import throughout
import unfolding

FIRST = "01"
# The papers after P15 that have a Results/Overview.lean (runner.KEYS lists P00–P15).
LATER = tuple(sorted(d.name[5:].split("_")[0] for d in (LEAN / "GenLimit").glob("Paper*_*")
                     if (d / "Results" / "Overview.lean").is_file() and d.name[5:].split("_")[0] not in KEYS))
READINGS = BASE / "Readings"
EXPORTER = "IRStatement.Export"
VOCABULARY = "IRStatement.Vocabulary"
# How Lean proves a hidden proof argument that is not a hypothesis in scope (see selector.hide_proofs).
# The exporter tries the same tactic on each proof argument (Export.lean, `hiddenTactic`).
TACTIC = "first | assumption | linarith | positivity | simp_all +zetaDelta"
assert f'def hiddenTactic : String := "{TACTIC}"' in (BASE / "Export.lean").read_text()
UNFOLD = [line.split("\t")[0] for line in (BASE / "Tables" / "Unfold.tsv").read_text().splitlines()[1:]]
WORD = r"[^\W\d_][^\W_]*(?:-[^\W\d_][^\W_]*)*'*"
TOKEN = re.compile(rf"{WORD}|[0-9]+|\S")
MARKS = {"GLUE", "PARA", "INMARK", "NEXTMARK", "OUTMARK"}


# ---------- Lean ----------

def lean_file(work, name, lines, imports):
    path = work / name
    path.write_text("".join(f"import {m}\n" for m in imports) + "".join(s + "\n" for s in lines))
    return run([*LAKE, "env", "lean", "--json", str(path)], cwd=LEAN, check=False)


def messages(result):
    out = [json.loads(s) for s in result.stdout.splitlines() if s.startswith("{")]
    if result.stderr.strip():
        raise ValueError(result.stderr)
    return out


def export(work, key, entries):
    """The Lean export of each entry, with the definitions of Unfold.tsv and the paper's
    `unfold` decisions in Unfolding.tsv shown by their bodies."""
    modules = sorted({e.module for e in entries})
    unfold = " ".join(UNFOLD + unfolding.unfolded(key))
    result = lean_file(work, f"Export{key}.lean",
                       [f"#ir_export {e.name} unfolding {unfold}" for e in entries],
                       [EXPORTER, *modules])
    trees = dict(json.loads(m["data"]) for m in messages(result) if m["severity"] == "information")
    if result.returncode or list(trees) != [e.name for e in entries]:
        raise ValueError(f"Export failed for P{key}: {result.stdout[:2000]}")
    return trees


def kernel(work, name, checks, modules):
    """Run one #check_statement per (declaration, proposition); return the errors of each line."""
    imports = ["IRStatement.Check", VOCABULARY, *modules]
    lines = [f"#check_statement {d} against ({p})" for d, p in checks]
    result = lean_file(work, name, lines, imports)
    found = [[] for _ in checks]
    first = len(imports) + 1
    for m in messages(result):
        if m["severity"] == "error":
            found[m["pos"]["line"] - first].append(m["data"])
    return found


def stage(name, errors):
    if not errors:
        return "accepted"
    return "kernel mismatch" if errors[0].startswith(f"statement mismatch for '{name}'") else "elaboration error"


# ---------- tokens and display ----------

def gf_string(display):
    """A display string as GF tokens: words separated by ++, GLUE where the text has no space."""
    out, end = [], None
    for m in TOKEN.finditer(display):
        if end is not None and display[end:m.start()] == "":
            out.append('"GLUE"')
        out.append(json.dumps(m.group(), ensure_ascii=False))
        end = m.end()
    return " ++ ".join(out)


def display(linearized):
    """GF output -> Markdown: paragraphs, bullet lists, and no space at GLUE."""
    lines, words, depth = [], [], 0

    def flush(prefix):
        if words:
            lines.append(prefix + " ".join(words).replace(" GLUE ", ""))
            words.clear()
    prefix = ""
    for t in linearized.split():
        if t not in ("PARA", "INMARK", "NEXTMARK", "OUTMARK"):
            words.append(t)
            continue
        flush(prefix)
        if t == "PARA":
            lines.append("")
            prefix = ""
        elif t == "INMARK":
            depth += 1
            prefix = "  " * (depth - 1) + "- "
        elif t == "NEXTMARK":
            prefix = "  " * (depth - 1) + "- "
        else:
            depth -= 1
            prefix = "  " * (depth - 1) + "- " if depth else ""
    flush(prefix)
    if depth:
        raise ValueError("Unbalanced list in the rendering")
    return "\n".join(lines)


def tokens(body):
    """Visible Markdown body -> GF tokens. GLUE marks adjacency, PARA a blank line, and
    INMARK/NEXTMARK/OUTMARK the bullets of a list."""
    out, depth, blank = [], 0, False
    for k, line in enumerate(body.split("\n")):
        if not line:
            if blank or k == 0:
                raise ValueError("Two blank lines or a leading blank line")
            blank = True
            continue
        indent = len(line) - len(line.lstrip(" "))
        item = line.lstrip(" ").startswith("- ")
        level = indent // 2 + 1 if item else 0
        if indent % 2 or (item and level > depth + 1) or (not item and indent):
            raise ValueError(f"Malformed line {line!r}")
        if k:
            if item:
                if blank:
                    raise ValueError("A blank line inside a list")
                out += ["OUTMARK"] * (depth - level) + ["INMARK" if level > depth else "NEXTMARK"]
            else:
                if not blank:
                    raise ValueError(f"A paragraph must follow a blank line: {line!r}")
                out += ["OUTMARK"] * depth + ["PARA"]
        elif item:
            raise ValueError("A reading cannot begin with a list")
        depth, blank = level, False
        text = line.lstrip(" ")[2:] if item else line
        if text != text.strip() or "  " in text:
            raise ValueError(f"Irregular spacing in {line!r}")
        end = None
        for m in TOKEN.finditer(text):
            if end is not None:
                gap = text[end:m.start()]
                if gap not in ("", " "):
                    raise ValueError(f"Irregular spacing {gap!r} in {line!r}")
                if not gap:
                    out.append("GLUE")
            if m.group() in MARKS:
                raise ValueError("A structural token appeared in the prose")
            out.append(m.group())
            end = m.end()
    return " ".join(out + ["OUTMARK"] * depth)


def lean_text(s):
    return s.replace(" GLUE ", "")


# ---------- lexicon and grammar ----------

def labels(keys):
    """Give each constant its label; when two constants of one paper share a label, prefix
    namespace components until the labels differ. A key c#h (c with a hidden proof argument h)
    has the label of c."""
    from selector import label_constant
    base = plain_labels(sorted({label_constant(k)[0] for k in keys}))
    return {k: base[label_constant(k)[0]] for k in keys}


def plain_labels(consts):
    depth = {c: 1 for c in consts}

    def make(c):
        parts = c.split(".")
        return " ".join(label_words(p) for p in parts[-depth[c]:])
    while True:
        seen = {}
        for c in consts:
            seen.setdefault(make(c), []).append(c)
        clashes = [cs for cs in seen.values() if len(cs) > 1]
        if not clashes:
            return {c: make(c) for c in consts}
        for cs in clashes:
            for c in cs:
                depth[c] += 1


# A label beginning with one of these words is a verb phrase: "H has …", not "H is has …".
VERBS = {'identifies', 'decides', 'have', 'learns', 'stabilizes', 'extends', 'presents', 'admits', 'belongs', 'achieves', 'has', 'lies', 'matches', 'can', 'holds', 'is', 'contains', 'solves', 'agrees', 'realizes', 'dominates', 'separates', 'satisfies', 'covers', 'are', 'generates'}


def plural(words):
    """English plural of a label: its last word gets -s, -es or -ies."""
    *head, last = words.split()
    if last.isupper():
        last += "s"
    elif last.endswith("y") and len(last) > 1 and last[-2] not in "aeiou":
        last = last[:-1] + "ies"
    elif last.endswith(("s", "x", "z", "ch", "sh")):
        last += "es"
    else:
        last += "s"
    return " ".join(head + [last])


# Names Lean reads as plain identifiers. Any other display name (t⋆, 𝒞, Σ, 𝒫: some are Mathlib
# notation) is written «…» in Lean, which is the same identifier.
PLAIN = re.compile(r"[A-Za-z_α-κμ-ωΑ-ΟΡΤ-Ω][A-Za-z0-9_'α-κμ-ωΑ-ΟΡΤ-Ω₀-₉]*")


def lean_ident(v):
    return v if PLAIN.fullmatch(v) else f"«{v}»"


def compile_grammar(work, name, sels, names):
    """The shared rules plus a lexicon of names: the variables, families, labels and numerals
    of the given readings. Each reading is parsed with the lexicon of its own Lean statement."""
    for g in ("IR", "IREng", "IRLean"):
        if not (work / f"{g}.gf").exists():
            shutil.copyfile(BASE / "Grammar" / f"{g}.gf", work / f"{g}.gf")
    vars_, fams, consts, nums, frames, negated = {}, {}, set(), set(), set(), set()
    for s in sels:
        frames |= s.frames
        negated |= s.negated
        vars_.update(s.vars)
        for f, letter in s.fams.items():
            if fams.setdefault(f, letter) != letter:
                raise ValueError(f"Family {f} needs two language letters")
        consts |= s.consts
        nums |= s.numerals
    from selector import tag
    abstract, english, formal = [], [], []
    for v, t in sorted(vars_.items()):
        abstract.append(f"fun {t} : Var ;")
        english.append(f"lin {t} = {gf_string(v)} ;")
        formal.append(f"lin {t} = {json.dumps(lean_ident(v), ensure_ascii=False)} ;")
    for f, letter in sorted(fams.items()):
        t = tag("f_", f)
        abstract.append(f"fun {t} : Fam ;")
        english.append(f'lin {t} = {{s = {gf_string(f)} ; lang = "{letter}"}} ;')
        formal.append(f"lin {t} = {json.dumps(lean_ident(f), ensure_ascii=False)} ;")
    from selector import FRAMES, frame_arity, frame_negation, label_constant
    for c in sorted(consts):
        t = tag("l_", c)
        base, hidden = label_constant(c)
        words = names[c] if c in names else names[base]
        # A hidden proof argument is a named argument that Lean fills from the assumptions.
        # It must be in the same application as the label's other arguments: every rule that applies
        # a label writes "(label args)", and a label with a hidden proof is always applied.
        lean = " ".join([base, *(f"({h} := by assumption)" if not h.endswith("!") else f"({h[:-1]} := by {TACTIC})"
                                 for h in hidden)])
        art = "an" if words[:1].lower() in "aeiou" else "a"
        verbal = "Verb" if words.split()[0] in VERBS else "Copular"
        abstract.append(f"fun {t} : Lbl ;")
        english.append(f'lin {t} = {{s = {gf_string("*" + words + "*")} ; pl = {gf_string("*" + plural(words) + "*")} ; '
                       f'art = "{art}" ; v = {verbal}}} ;')
        formal.append(f"lin {t} = {json.dumps(lean, ensure_ascii=False)} ;")
        if c in frames:
            # The label read as a sentence: English puts the arguments in the frame's slots, Lean applies
            # the constant to them in its own order. The kernel check covers the order; the words are the table's.
            frame = FRAMES[base]
            xs = [f"x{k}" for k in range(1, frame_arity(frame) + 1)]
            s_t = tag("s_", c)
            applied = f"par ({json.dumps(lean, ensure_ascii=False)} ++ {' ++ '.join(xs)})"
            # The negated frame ("X is not *label* for Y") is the same entry with "¬" in Lean.
            for t_, f_, how, lean_ in ((s_t, frame, "atom", applied),
                                       ("sn_" + s_t[2:], frame_negation(frame) if c in negated else None, "denied",
                                        f'par ("¬" ++ {applied})')):
                if f_ is None:
                    continue
                eng = [gf_string("*" + words + "*") if w == "{label}" else f"operand x{w[1:-1]}" if w.startswith("{")
                       else gf_string(w) for w in f_.split()]
                abstract.append(f"fun {t_} : {' -> '.join(['Term'] * len(xs))} -> Prop ;")
                english.append(f"lin {t_} {' '.join(xs)} = {how} ({' ++ '.join(eng)}) ;")
                formal.append(f"lin {t_} {' '.join(xs)} = {lean_} ;")
    for k in sorted(nums):
        t = tag("n_", str(k))
        abstract.append(f"fun {t} : Numeral ;")
        english.append(f'lin {t} = "{k}" ;')
        formal.append(f'lin {t} = "{k}" ;')
    (work / f"{name}.gf").write_text(f"abstract {name} = IR ** {{\n" + "\n".join(abstract) + "\n}\n")
    for suffix, rules in (("Eng", english), ("Lean", formal)):
        (work / f"{name}{suffix}.gf").write_text(
            f"concrete {name}{suffix} of {name} = IR{suffix} ** {{\n" + "\n".join(rules) + "\n}\n")
    return Grammar(work, name, (name + "Eng", name + "Lean"), work)


def parse(g, name, body):
    try:
        toks = tokens(body)
    except ValueError as error:
        return [f"The tokenizer rejected the body: {error}"]
    [result] = g.batch([f"p -lang={name}Eng -cat=Doc {json.dumps(toks, ensure_ascii=False)}"], name)
    return result


def complete(parses):
    return [t for t in parses if not t.startswith(("The parser failed", "The tokenizer")) and "?" not in t]


# ---------- pages ----------

def heading(e):
    # Section heading from the declaration name, e.g. theorem_3_15 → Theorem 3.15.
    label = e.name.rsplit(".", 1)[1]
    label = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", label)
    label = re.sub(r"\b(theorem|lemma|corollary|proposition|remark|example|claim)_([A-Z0-9]+(?:_[0-9]+)*)",
                   lambda m: m[1] + " " + m[2].replace("_", "."), label.replace("corrected_", "Corrected "))
    label = label.replace("_", " ")
    return label[0].upper() + label[1:]


def page_path(key):
    return READINGS / f"P{key}.md"


def reference(e, base):
    return f"[Lean declaration]({os.path.relpath(e.path, base)}#L{e.line}) · `{e.name}`"


def page(key, entries, bodies, names, missing, base):
    reg = json.loads((LEAN.parent / "registry" / "papers" / f"P{key}.json").read_text())
    title = reg["paper"]["title"]
    links = "[Rules](../RULES.md) · [Reading index](README.md) · [Check log](RUN-LOG.md)"
    intro = (f"# P{key} · {title}\n\n"
             "IR statements, generated directly from the full Lean types. "
             "The checker parses each body below as displayed, renders the parse as a Lean proposition "
             f"and asks the kernel to compare it with the declaration's entire type. {links}")
    # Leading sentences that several readings share are stated once, under "Throughout".
    settings = throughout.choose({e.name: b for e, b in zip(entries, bodies)})
    shown = {e.name: b for e, b in zip(entries, bodies)}
    for letter, (text, users) in zip(throughout.letters(settings), settings):
        for name in users:
            shown[name] = throughout.shorten(shown[name], text, letter)
    parts = [intro, *([throughout.section(settings)] if settings else []),
             *(f"## {heading(e)}\n\n{shown[e.name]}\n\n{reference(e, base)}" for e in entries)]
    if missing:
        parts.append("## Declarations without a checked reading\n\n" +
                     "\n".join(f"- `{e.name}`: {why}" for e, why in missing))
    from selector import label_constant
    used = sorted({(names[c], label_constant(c)[0]) for c in names if any(f"*{names[c]}*" in b for b in bodies)})
    from selector import FRAMES, frame_arity
    framed = [(label, FRAMES[c]) for label, c in used if c in FRAMES]
    if framed:
        label, frame = min(framed, key=lambda f: frame_arity(f[1]))
        slots = "XYZWV"[:frame_arity(frame)]
        sentence = " ".join(f"*{label}*" if w == "{label}" else slots[int(w[1:-1]) - 1] if w.startswith("{") else w
                            for w in frame.split())
        framed = (f" Some labels read as a short sentence instead: “{sentence}” stands for *{label}*({', '.join(slots)}). "
                  "Frames.tsv lists these sentences, and the glossary states each definition in the same form.")
    if used:
        parts.append("## Labels\n\nEach label in italics stands for one Lean constant. It is made from the "
                     "constant's name by a fixed rule; a label with one argument reads “X is *label*”, "
                     f"otherwise “*label*(X, Y, …)” with the arguments in Lean's order.{framed or ''} A proof argument is "
                     "not shown; Lean proves it from the assumptions.\n\n"
                     "| Label | Lean constant |\n|---|---|\n" +
                     "\n".join(f"| *{label}* | `{c}` |" for label, c in used))
    return "\n\n".join(parts) + "\n"


def saved_sections(path):
    """Return (declaration name, body, link, line, setting) for each reading on the visible page.
    The body is the full text: a leading mark *Setting A.* is replaced by the text of Setting A."""
    text, settings = throughout.split(path.read_text())
    text = text.split("\n## Declarations without a checked reading\n")[0].split("\n## Labels\n")[0]
    parts = re.split(r"^## (.+)$", text, flags=re.MULTILINE)
    out, used = [], set()
    for section in parts[2::2]:
        body, ref = section.strip("\n").rsplit("\n\n", 1)
        m = re.fullmatch(r"\[Lean declaration\]\(([^)#]+)#L(\d+)\) · `([^`]+)`", ref)
        if not m:
            raise ValueError(f"Missing declaration reference: {ref!r}")
        body, letter = throughout.expand(body, settings)
        used.add(letter)
        out.append((m[3], body, m[1], int(m[2]), letter))
    if set(settings) - used:
        raise ValueError(f"Settings used by no reading: {sorted(set(settings) - used)}")
    return out


# ---------- negative control ----------

def sample_before_threshold(body, update_dependencies):
    """Move the sample S before the threshold so that the threshold may depend on S.

    The binder sentence moves to the introductions before the threshold, its hypothesis
    |S| ≥ t_C becomes an assumption after the threshold, and (optionally) the displayed
    dependency list gains S."""
    paras = body.split("\n\n")
    [k] = [i for i, p in enumerate(paras) if p.startswith("There is ")]
    m = re.match(r"Let (\w+) be (a [^.]*?) with (\|\1\| ≥ \w+)\. ", paras[k + 1])
    if not m:
        raise ValueError("Control could not find the sample sentence after the threshold")
    sample, kind, hypothesis = m.groups()
    rest = paras[k + 1][m.end():]
    threshold = paras[k]
    if update_dependencies:
        d = re.search(r"depending only on (.+?), with the following property\.$", threshold)
        names = re.split(r", | and ", d[1]) + [sample]
        listed = ", ".join(names[:-1]) + " and " + names[-1]
        threshold = threshold[:d.start(1)] + listed + threshold[d.end(1):]
    edited = [*paras[:k - 1], paras[k - 1] + f" Let {sample} be {kind}.", threshold,
              f"Suppose that {hypothesis}.", rest, *paras[k + 2:]]
    return "\n\n".join(edited)


def control(work, gname, g, e, body, modules, log):
    log.append("## Negative control · P01 Theorem 2.2 with the sample chosen before the threshold\n")
    outcomes = []
    for update, label in ((True, "A. Dependency list updated to include S"),
                          (False, "B. Dependency list left as “O and C”")):
        edited = sample_before_threshold(body, update)
        parses = parse(g, gname, edited)
        trees = complete(parses)
        entry = f"### {label}\n\nEdited English (temporary copy):\n\n```text\n{edited}\n```\n\n" \
                f"- GF parses: {len(trees)} complete\n"
        if len(trees) == 1:
            term = lean_text(g.render(trees, gname, gname + "Lean")[0])
            [errors] = kernel(work, f"Control{len(outcomes)}.lean", [(e.name, term)], modules)
            outcome = {"accepted": "ACCEPTED (control failed)", "kernel mismatch": "kernel: statement mismatch",
                       "elaboration error": "elaboration: " + (errors or [""])[0].splitlines()[0]}[stage(e.name, errors)]
            entry += f"- Outcome: {outcome}\n\nRecovered proposition P′:\n\n```lean\n{term}\n```\n"
            outcomes.append(outcome)
        else:
            outcomes.append("no unique parse")
        log.append(entry)
        print(f"Control {label[0]}: {outcomes[-1]}", flush=True)
    return outcomes


# ---------- grammar regression ----------

def roundtrip(g, work, name, seed=0, sizes=((("Prop", 4, 400), ("Term", 4, 200), ("Doc", 5, 300), ("Doc", 7, 200)))):
    """Random well-formed trees (not only the readings) must each come back as the only
    parse of their own English."""
    signatures = {}
    source = re.sub(r"--.*", "", (BASE / "Grammar" / "IR.gf").read_text() + (work / f"{name}.gf").read_text())
    for block in re.findall(r"\bfun\b(.*?)(?=\bfun\b|\bcat\b|\}|$)", source, re.S):
        for decl in block.split(";"):
            if ":" in decl:
                names, ty = decl.split(":")
                *args, result = [p.strip() for p in ty.split("->")]
                for n in filter(None, (n.strip() for n in names.split(","))):
                    signatures.setdefault(result, []).append((n, args))
    height = {}
    for _ in range(len(signatures) + 1):
        for cat, options in signatures.items():
            for _, args in options:
                if all(a in height for a in args):
                    height[cat] = min(height.get(cat, 99), 1 + max((height[a] for a in args), default=0))
    rng = random.Random(seed)

    def tree(cat, depth):
        # Only constructors whose argument categories have trees in this paper's lexicon.
        options = [o for o in signatures[cat] if all(a in height for a in o[1])]
        if depth <= 0:
            options = [o for o in options if 1 + max((height[a] for a in o[1]), default=0) == height[cat]]
        f, args = rng.choice(options)
        return f if not args else "(" + " ".join([f, *(tree(a, depth - 1) for a in args)]) + ")"

    def bare(t):  # GF prints the root application without parentheses
        return t[1:-1] if t.startswith("(") else t

    trees = sorted({(cat, bare(tree(cat, depth))) for cat, depth, n in sizes for _ in range(n)})
    texts = g.batch([f"l -lang={name}Eng {t}" for _, t in trees], name)
    parses = g.batch([f"p -lang={name}Eng -cat={c} {json.dumps(x[0], ensure_ascii=False)}"
                      for (c, _), x in zip(trees, texts)], name)
    failures = [(t, p) for (_, t), p in zip(trees, parses) if p != [t]]
    return len(trees), failures


# ---------- one paper ----------

def build(work, key):
    entries = inventory(key)
    exported = export(work, key, entries)
    chosen, missing = [], []
    avoid = paper_names(exported.values(), key)
    for e in entries:
        try:
            tree, sel = select(exported[e.name], avoid, paper=key)
        except Exception as error:  # the selector reports what it cannot read yet
            missing.append((e, f"no reading yet ({type(error).__name__}: {str(error)[:160]})"))
            continue
        chosen.append((e, tree, sel))
    names = labels(sorted(set().union(*(sel.consts for _, _, sel in chosen)) if chosen else set()))
    folder = work / key
    folder.mkdir()
    readings = []
    for k, (e, tree, sel) in enumerate(chosen):
        gname = f"R{key}x{k}"
        readings.append({"entry": e, "tree": tree, "sel": sel, "gname": gname,
                         "g": compile_grammar(folder, gname, [sel], names)})
    return entries, readings, missing, names, folder


def render(r, lang):
    return r["g"].render([r["tree"]], r["gname"], r["gname"] + lang)[0]


def verify(work, key, readings, path, log):
    """Parse each saved body with its own lexicon, compare trees, render P′ and run the kernel."""
    sections = saved_sections(path)
    by_name = {r["entry"].name: r for r in readings}
    if [s[0] for s in sections] != [r["entry"].name for r in readings]:
        raise ValueError(f"{path.name} must contain the selected declarations in source order")
    checks, status = [], {}
    for name, body, link, line, letter in sections:
        r = by_name[name]
        e, g, gname = r["entry"], r["g"], r["gname"]
        if (page_path(key).parent / link).resolve() != e.path.resolve() or line != e.line:
            raise ValueError(f"The link for {name} does not open its declaring line")
        parses = parse(g, gname, body)
        trees = complete(parses)
        unique = len(trees) == 1
        same = unique and trees[0] == r["tree"]
        canonical = unique and display(g.render(trees, gname, gname + "Eng")[0]) == body
        status[name] = {"parses": len(trees), "same": same, "canonical": canonical, "lean": "not run",
                        "why": "" if trees else parses[0][:200], "setting": letter}
        if unique:
            checks.append((name, lean_text(g.render(trees, gname, gname + "Lean")[0])))
    modules = sorted({r["entry"].module for r in readings})
    results = kernel(work, f"Checked{key}.lean", checks, modules) if checks else []
    for (name, term), errors in zip(checks, results):
        status[name]["lean"] = stage(name, errors)
        status[name]["errors"] = errors
        status[name]["term"] = term
    for name, s in status.items():
        e = by_name[name]["entry"]
        log.append(f"### {heading(e)} · `{name}`\n\n"
                   + (f"- The body begins with Setting {s['setting']}; the check reads the setting's text in "
                      "place of the mark\n" if s["setting"] else "")
                   + f"- GF parses of the saved body: {s['parses']} complete"
                   + (f" ({s['why']})" if s["why"] else "") + "\n"
                   f"- Parsed tree equals the tree selected from the Lean export: {s['same']}\n"
                   f"- Saved body is the canonical rendering of the parsed tree: {s['canonical']}\n"
                   f"- Lean: {s['lean']}" + (": " + " | ".join(x[:300] for x in s.get("errors", []))
                                              if s.get("errors") else "") + "\n" +
                   (f"\nRecovered proposition P′:\n\n```lean\n{s['term']}\n```\n" if "term" in s else ""))
    return status


def write_index(keys, summary):
    """Readings/README.md: one row per paper, from this run's results."""
    rows = []
    for key, line in zip(keys, summary):
        reg = json.loads((LEAN.parent / "registry" / "papers" / f"P{key}.json").read_text())
        m = re.match(rf"P{key}: (\d+)/(\d+)", line)
        rows.append(f"| [P{key}](P{key}.md) | {reg['paper']['title']} | {m[1]} / {m[2]} |")
    total = [re.match(r"P\w+: (\d+)/(\d+)", s).groups() for s in summary]
    READINGS.mkdir(exist_ok=True)
    (READINGS / "README.md").write_text(
        "# IR statements of P00–P39\n\n"
        "Controlled-English readings of the theorem, lemma and alias declarations in each paper's "
        "`Results/Overview.lean`, in file order. Every reading listed here was parsed back from the saved page "
        "and accepted by the Lean kernel as definitionally equal to its declaration's entire type. "
        "[Rules](../RULES.md) · [Rule cards](../RULE-CARDS.md) · [Check log](RUN-LOG.md)\n\n"
        "| Paper | Title | Checked readings |\n|---|---|---:|\n" + "\n".join(rows) +
        f"\n| **Total** | | **{sum(int(a) for a, _ in total)} / {sum(int(b) for _, b in total)}** |\n")


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--write", action="store_true", help="regenerate the selected pages, verify them, then publish")
    cli.add_argument("--papers", nargs="+", choices=KEYS + LATER, default=[FIRST], help="papers to process (default: 01)")
    cli.add_argument("--all", action="store_true", help="process every paper, P00–P39, and write the log")
    cli.add_argument("--page", type=Path, help="verify another copy of Readings/P01.md (for trying edits)")
    args = cli.parse_args()
    keys = list(KEYS) + list(LATER) if args.all else args.papers
    if args.page and (args.write or keys != [FIRST]):
        cli.error("--page verifies an edited copy of Readings/P01.md only")
    summary, ok = [], True
    log = ["# Check log\n\nWritten by `reader.py` from the saved pages; do not edit.\n"]
    usage, sources = {}, {}
    with tempfile.TemporaryDirectory(prefix="ir-reader-") as temp:
        work = Path(temp)
        run([*LAKE, "build", EXPORTER, VOCABULARY], cwd=LEAN)
        for key in keys:
            evidence = unfolding.check(key)
            if evidence:
                raise SystemExit(f"P{key}: Unfolding.tsv cites the paper wrongly:\n  " + "\n  ".join(evidence))
            entries, readings, missing, names, folder = build(work, key)
            target = page_path(key)
            path = args.page.resolve() if args.page else target
            if args.write:
                bodies = [display(render(r, "Eng")) for r in readings]
                path = folder / target.name
                path.write_text(page(key, [r["entry"] for r in readings], bodies, names, missing, target.parent))
            if not args.write:
                # The page lists the readings Lean rejected when it was written; verify the rest.
                listed = set(re.findall(r"^- `([^`]+)`: no checked reading yet", path.read_text(), re.M))
                missing += [(r["entry"], "listed on the page without a checked reading")
                            for r in readings if r["entry"].name in listed]
                readings = [r for r in readings if r["entry"].name not in listed]
            if args.write:
                # A reading Lean rejects is listed as not yet readable, with the reason, and the page is
                # published with the rest. The same rule holds for every paper.
                trial = verify(work, key, readings, path, [])
                rejected = {n for n, s in trial.items() if s["lean"] != "accepted"}
                if rejected:
                    missing += [(r["entry"], f"no checked reading yet (Lean: {trial[r['entry'].name]['lean']}: "
                                 f"{(trial[r['entry'].name].get('errors') or [''])[0].splitlines()[0][:120]})")
                                for r in readings if r["entry"].name in rejected]
                    missing.sort(key=lambda m: entries.index(m[0]))
                    readings = [r for r in readings if r["entry"].name not in rejected]
                    bodies = [display(render(r, "Eng")) for r in readings]
                    path.write_text(page(key, [r["entry"] for r in readings], bodies, names, missing, target.parent))
            log.append(f"## P{key}\n\nSHA-256 of the checked page: `{hashlib.sha256(path.read_bytes()).hexdigest()}`\n")
            status = verify(work, key, readings, path, log)
            good = [n for n, s in status.items() if s["parses"] == 1 and s["same"] and s["canonical"]
                    and s["lean"] == "accepted"]
            for n, s in status.items():
                if n not in good:
                    print(f"P{key} {n}: parses {s['parses']}, same {s['same']}, canonical {s['canonical']}, "
                          f"Lean {s['lean']} {(s.get('errors') or [''])[0][:300]}", flush=True)
            for r in readings:
                if r["entry"].name in good:   # the rule cards count only checked readings
                    usage[(key, heading(r["entry"]), r["entry"].name)] = r["tree"]
                    sources[(key, heading(r["entry"]), r["entry"].name)] = (r["g"], r["gname"], folder)
            line = f"P{key}: {len(good)}/{len(entries)} readings checked"
            if missing:
                line += f"; {len(missing)} without a reading"
            recovered = total = 0
            sample = ((("Prop", 4, 400), ("Term", 4, 200), ("Doc", 5, 300), ("Doc", 7, 200)) if key == FIRST else
                      (("Prop", 3, 40), ("Term", 3, 20), ("Doc", 4, 40)))
            for r in readings:
                count, failures = roundtrip(r["g"], folder, r["gname"], sizes=sample)
                total += count
                recovered += count - len(failures)
            ok &= recovered == total
            if key == FIRST and not args.page:
                [r22] = [r for r in readings if r["entry"].name.endswith(".theorem_2_2")]
                body22 = dict((s[0], s[1]) for s in saved_sections(path))[r22["entry"].name]
                outcomes = control(work, r22["gname"], r22["g"], r22["entry"], body22, [r22["entry"].module], log)
                ok &= outcomes[0] == "kernel: statement mismatch"
                line += "; control A rejected by the kernel"
            line += f"; {recovered}/{total} random trees recovered"
            log.append(f"Grammar regression for P{key}: {recovered}/{total} random trees of the readings' "
                       "grammars (fixed seed) came back as the unique parse of their own English.\n")
            print(line, flush=True)
            summary.append(line)
            ok &= len(good) == len(status)
            if args.write and len(good) == len(status):
                target.parent.mkdir(exist_ok=True)
                target.write_text(path.read_text())
            elif args.write:
                print(f"P{key}: not published, because some readings failed", flush=True)
        if args.page:
            raise SystemExit(0 if ok else "Verification of the edited page failed.")
        log.insert(1, "\n".join(f"- {s}" for s in summary) + "\n")
        if args.all:
            # The whole corpus: index, log and rule cards for all readings. A partial run writes no log.
            write_index(keys, summary)
            (READINGS / "RUN-LOG.md").write_text("\n".join(log))
            cards.save_usage("readings", usage, sources, "reading")
            total, used = cards.write_cards(work)
            print(f"Rule cards: {used} of {total} rules used by the checked texts; see RULE-CARDS.md", flush=True)
    if not ok:
        raise SystemExit("Verification failed; see the messages above.")


if __name__ == "__main__":
    main()
