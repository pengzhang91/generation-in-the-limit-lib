"""Write RULE-CARDS.md: one card per GF rule, with patterns generated from the grammar itself.

Each rule is linearized on placeholder arguments (P, X, T, …) in both concrete syntaxes,
so a card shows exactly the English and the Lean that the checker uses. Below the patterns,
up to two examples from the checked readings show the rule at work: the sentence of a real
reading that contains it, with the rest of the text as "…", linearized by that reading's own
grammar. A reviewer signs a card in RuleTiers.tsv; a theorem is reviewed when every rule its
reading uses is signed.

The cards cover every checked text: the readings of P00–P39 and the glossary definitions. Each full
run saves which rules its texts use, with example candidates linearized by their own lexicons:

    reader.py --all  → Readings/RULE-USAGE.json
    glossary.py     → Readings/Glossary/RULE-USAGE.json

and then rewrites RULE-CARDS.md from both files. `python3 cards.py` rewrites it from the files alone.
"""
import csv
import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile

BASE = Path(__file__).resolve().parents[1]  # the IRStatement folder
sys.path.insert(0, str(Path(__file__).resolve().parent))
from runner import Grammar  # noqa: E402

USAGE = {
    "readings": (BASE / "Readings" / "RULE-USAGE.json", "reader.py --all", "the readings of P00–P39"),
    "glossary": (BASE / "Readings" / "Glossary" / "RULE-USAGE.json", "glossary.py", "the glossary definitions"),
}
TIERS = ["plumbing", "type", "notation", "label", "structure", "hidden", "domain"]
TIER_TEXT = {
    "plumbing": "Glue with no mathematical content.",
    "type": "Types of bound variables.",
    "notation": "Symbols and short predicates with a direct Lean counterpart.",
    "label": "How the label of a Lean constant is used. A label is made from the constant's name by one fixed "
             "rule, so these few conventions cover every constant without a card of its own. A proof argument "
             "that is an assumption in scope is not shown: the label's Lean side passes it as "
             "(h := by assumption).",
    "structure": "Sentences that bind, assume, define and conclude. Their scope convention: "
                 "what a sentence introduces holds for the rest of the text.",
    "hidden": "Rules whose Lean side contains something the English does not show: an unnamed proof, "
              "a checked dependency list, a type-directed choice or a generic definition.",
    "domain": "Vocabulary of this paper: families with oracles, the generators, robustness.",
}

# Placeholder arguments: (abstract name, category, English record, Lean string). The second
# slot of a category, when present, is the variant that changes the English layout.
SLOTS = {
    "Var": [("SV1", '"x"', '"x"'), ("SV2", '"y"', '"y"'), ("SV3", '"t"', '"t"'), ("SV4", '"u"', '"u"'),
            ("SV5", '"v"', '"v"')],
    "Fam": [("SF", '{s = "O" ; lang = "L"}', '"O"')],
    "Lbl": [("SL", '{s = "*" ++ "GLUE" ++ "label" ++ "GLUE" ++ "*" ; pl = "*" ++ "GLUE" ++ "labels" ++ "GLUE" ++ "*" ; '
                   'art = "a" ; v = Copular}', '"c"')],
    "Binds": [("SB", '{s = "x ∈ T" ; n = One}', '"∃ x : T ,"')],
    "Numeral": [("SNum", '"k"', '"k"')],
    "Prop": [("SP", '{s = "P" ; c = "P" ; k = Atom}', '"P"'), ("SQ", '{s = "Q" ; c = "Q" ; k = Atom}', '"Q"')],
    "Term": [("SX", '{s = "X" ; p = Simple}', '"X"'), ("SY", '{s = "Y" ; p = Simple}', '"Y"'),
             ("SZ", '{s = "Z" ; p = Simple}', '"Z"')],
    "Args": [("SA", '"X₁" ++ "GLUE" ++ "," ++ "…" ++ "GLUE" ++ "," ++ "Xₖ"', '{s = "X₁ … Xₖ" ; c = "X₁ , … , Xₖ"}')],
    "Ty": [("STy", '{sg = "T" ; pl = "Ts" ; compl = [] ; sym = "T" ; bind = [] ; art = "a" ; ref = "T" ; has = NoSym ; kind = KOther}', '"T"'),
           ("STy2", '{sg = "U" ; pl = "Us" ; compl = [] ; sym = "U" ; bind = [] ; art = "a" ; ref = "U" ; has = NoSym ; kind = KOther}', '"U"')],
    "TyArgs": [("STA", '{s = "A" ; c = "A" ; n = One}', '"A"')],
    "Outline": [("SO", '{s = "…" ; inl = "…" ; afterSup = "…" ; afterSupInl = "…" ; items = [] ; k = KLet}', '"…"')],
    "Items": [("SI", '"I₁" ++ "NEXTMARK" ++ "I₂"', '"(I₁) ∧ (I₂)"')],
    "Concl": [("SC", '"C" ++ "GLUE" ++ "."', '"C"')],
    "Names": [("SN", '{s = "N" ; n = One}', '{c = "N" ; sp = "N"}')],
    "Pred": [("SPred", '"R"', '"R subject"')],
    "FamTy": [("SFT", '"F"', '"F"')],
    "Ref": [("SR", '"r"', '"r"')],
}
VARIANTS = {
    "Outline": ("SOl", '{s = "All" ++ "of" ++ "the" ++ "following" ++ "hold" ++ "GLUE" ++ ":" ++ "INMARK" ++ "I₁" ++ "NEXTMARK" ++ "I₂" ++ "OUTMARK" ; '
                'inl = "…" ; afterSup = "…" ; afterSupInl = "…" ; '
                'items = "GLUE" ++ ":" ++ "INMARK" ++ "I₁" ++ "NEXTMARK" ++ "I₂" ++ "OUTMARK" ; k = KList}', '"(I₁) ∧ (I₂)"',
                "the rest is a list"),
    "Prop": ("SPc", '{s = "for every y, P" ; c = "For every y, P" ; k = Quant}', '"P"', "P is not atomic"),
    "Term": ("SXd", '{s = "the X" ; p = Described}', '"X"', "X is a noun phrase"),
    "Ty": ("STyN", '{sg = "natural number" ; pl = "natural numbers" ; compl = [] ; sym = "ℕ" ; bind = "∈" ++ "ℕ" ; '
           'art = "a" ; ref = "ℕ" ; has = HasSym ; kind = KNat}', '"ℕ"', "T is ℕ"),
}


def signatures():
    source = re.sub(r"--.*", "", (BASE / "Grammar" / "IR.gf").read_text())
    out = []
    for block in re.findall(r"\bfun\b(.*?)(?=\bfun\b|\bcat\b|\}|$)", source, re.S):
        for decl in block.split(";"):
            if ":" in decl:
                names, ty = decl.split(":")
                *args, result = [p.strip() for p in ty.split("->")]
                out += [(n.strip(), args, result) for n in names.split(",") if n.strip()]
    return out


def tiers():
    with (BASE / "Tables" / "RuleTiers.tsv").open() as source:
        rows = {r["rule"]: r for r in csv.DictReader(source, delimiter="\t")}
    for r in rows.values():  # an empty last column may be missing from the line
        r["reviewed by"] = r.get("reviewed by") or ""
    return rows


def compile_cards(work):
    slots = [(n, cat, e, l) for cat, xs in SLOTS.items() for n, e, l in xs] + \
            [(n, cat, e, l) for cat, (n, e, l, _) in VARIANTS.items()]
    (work / "IRCards.gf").write_text(
        "abstract IRCards = IR ** {\n" + "".join(f"fun {n} : {c} ;\n" for n, c, _, _ in slots) + "}\n")
    (work / "IRCardsEng.gf").write_text(
        "concrete IRCardsEng of IRCards = IREng ** {\n" +
        "".join(f"lin {n} = {e} ;\n" for n, _, e, _ in slots) + "}\n")
    (work / "IRCardsLean.gf").write_text(
        "concrete IRCardsLean of IRCards = IRLean ** {\n" +
        "".join(f"lin {n} = {l} ;\n" for n, _, _, l in slots) + "}\n")
    return Grammar(work, "IRCards", ("IRCardsEng", "IRCardsLean"), work)


def patterns(name, args, result=None):
    """The plain card and one layout variant per argument whose category has one."""
    used = {c: 0 for c in SLOTS}
    base = []
    for a in args:
        base.append(SLOTS[a][used[a] % len(SLOTS[a])][0])
        used[a] += 1
    trees = [(None, base)]
    for k, a in enumerate(args):
        # The list variant of an outline changes only the wording of a choice.
        if a in VARIANTS and (a != "Outline" or name.startswith("There")):
            v = list(base)
            v[k] = VARIANTS[a][0]
            trees.append((VARIANTS[a][3], v))
    out = [(note, f"({name} {' '.join(v)})" if v else name) for note, v in trees]
    if result == "Ty":  # a type has no sentence of its own; show it in "Let v be …"
        out = [(note, f"(LetTy SV5 {t} SO)") for note, t in out]
    return out


# ---------- examples from the readings ----------

LEAVES = {"v_": "Var", "f_": "Fam", "l_": "Lbl", "n_": "Numeral"}
EXAMPLES = 2            # per card
CANDIDATES = 6          # smallest example trees per rule that are linearized before choosing
LONGEST = 420           # characters; a second example longer than this is left out


def tree_of(text):
    """A GF tree as printed (root application without brackets) -> (head, [children])."""
    tokens = re.findall(r"\(|\)|[^\s()]+", "(" + text + ")")
    pos = 0

    def node():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token != "(":
            return (token, [])
        head, pos = tokens[pos], pos + 1
        children = []
        while tokens[pos] != ")":
            children.append(node())
        pos += 1
        return (head, children)
    root = node()
    if pos != len(tokens):
        raise ValueError(f"Malformed tree {text[:80]}")
    return root


def text_of(node):
    head, children = node
    return head if not children else "(" + " ".join([head, *map(text_of, children)]) + ")"


def size(node):
    return 1 + sum(map(size, node[1]))


def sentence_trees(root, sigs):
    """For each rule node of a reading: the nearest enclosing outline (the sentence that contains it), with
    the rest of the text replaced by the placeholder SO. Yields (rule, example tree)."""
    kinds = {n: (args, result) for n, args, result in sigs}
    rest = {n for n, args, result in sigs if result == "Outline" and args[-1:] == ["Outline"] and args[0] != "Outline"}

    def cut(node):
        head, children = node
        return (head, children[:-1] + [("SO", [])]) if head in rest else node

    def walk(node, sentence):
        head, children = node
        if head in kinds:
            if kinds[head][1] == "Outline":
                sentence = cut(node)
            if sentence is not None:
                yield head, sentence
        for child in children:
            yield from walk(child, sentence)
    yield from walk(root, None)


def grammar_sha():
    h = hashlib.sha256()
    for g in ("IR", "IREng", "IRLean"):
        h.update((BASE / "Grammar" / f"{g}.gf").read_bytes())
    return h.hexdigest()


def order(paper):
    return (int(paper[:2]), paper)


def rank(o):
    """A fixed order on example candidates: smaller trees first, then by paper, readings before glossaries."""
    return (o["size"], order(o["paper"]), o["part"] != "reading", o["heading"], o["name"], o["tree"])


def shortlist(options):
    """The smallest sentence trees, at most two from one paper."""
    picked, per_paper = [], {}
    for o in sorted(options, key=rank):
        if len(picked) == CANDIDATES:
            break
        if per_paper.get(o["paper"], 0) < 2:
            picked.append(o)
            per_paper[o["paper"]] = per_paper.get(o["paper"], 0) + 1
    return picked


def save_usage(kind, usage, sources, part):
    """Save which rules each checked text of one full run uses, and each rule's example candidates.
    usage maps (paper, heading, declaration) to a GF tree; sources maps the same keys to (grammar,
    grammar name, folder); part is "reading" or "glossary"."""
    sigs = signatures()
    names = [n for n, _, _ in sigs]
    texts = [{"paper": k[0], "heading": k[1], "name": k[2], "part": part,
              "rules": sorted(n for n in names if re.search(rf"\b{n}\b", tree))} for k, tree in usage.items()]
    found = {}
    for k, tree in usage.items():
        for rule, sentence in sentence_trees(tree_of(tree), sigs):
            o = {"size": size(sentence), "paper": k[0], "part": part, "heading": k[1], "name": k[2],
                 "tree": text_of(sentence)}
            old = found.setdefault(rule, {}).get(o["tree"])
            if old is None or rank(o) < rank(old):
                found[rule][o["tree"]] = o
    wanted = {rule: shortlist(options.values()) for rule, options in found.items()}
    # Linearize every candidate with its own text's lexicon, extended by the placeholder SO.
    by_text = {}
    for picked in wanted.values():
        for o in picked:
            by_text.setdefault((o["paper"], o["heading"], o["name"]), set()).add(o["tree"])
    lin = {}
    _, so_eng, so_lean = SLOTS["Outline"][0]
    for k, trees in by_text.items():
        g, gname, folder = sources[k]
        x = "X" + gname
        (folder / f"{x}.gf").write_text(f"abstract {x} = {gname} ** {{ fun SO : Outline ; }}\n")
        (folder / f"{x}Eng.gf").write_text(f"concrete {x}Eng of {x} = {gname}Eng ** {{ lin SO = {so_eng} ; }}\n")
        (folder / f"{x}Lean.gf").write_text(f"concrete {x}Lean of {x} = {gname}Lean ** {{ lin SO = {so_lean} ; }}\n")
        gx = Grammar(folder, x, (x + "Eng", x + "Lean"), folder)
        trees = sorted(trees)
        eng = gx.batch([f"l -lang={x}Eng {t}" for t in trees], x)
        lean = gx.batch([f"l -lang={x}Lean {t}" for t in trees], x)
        for t, e, l in zip(trees, eng, lean):
            lin[(k, t)] = (shown(e[0]), shown(l[0]))
    for picked in wanted.values():
        for o in picked:
            o["eng"], o["lean"] = lin[((o["paper"], o["heading"], o["name"]), o["tree"])]
    path = USAGE[kind][0]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"grammar_sha256": grammar_sha(), "texts": texts, "examples": wanted},
                               ensure_ascii=False, indent=1) + "\n")


def load_usage():
    """All saved runs: (texts, {rule: candidates}, one note per run)."""
    texts, options, notes = [], {}, []
    current = grammar_sha()
    for path, command, what in USAGE.values():
        if not path.exists():
            notes.append(f"{what}: missing, run `{command}`")
            continue
        data = json.loads(path.read_text())
        texts += data["texts"]
        for rule, found in data["examples"].items():
            options.setdefault(rule, []).extend(found)
        notes.append(f"{what} (`{command}`" +
                     (")" if data["grammar_sha256"] == current else "; checked with an older grammar, run it again)"))
    return texts, options, notes


def examples(options):
    """{rule: [(where, English, Lean)]}: the shortest sentences that use each rule, from different papers."""
    result = {}
    for rule, found in options.items():
        unique = {}
        for o in found:
            if o["tree"] not in unique or rank(o) < rank(unique[o["tree"]]):
                unique[o["tree"]] = o
        rows = sorted(shortlist(unique.values()), key=lambda o: (len(o["eng"]),) + rank(o)[1:])
        chosen = []
        for o in rows:
            if len(chosen) == EXAMPLES:
                break
            if chosen and (o["paper"] == chosen[0]["paper"] or o["eng"] == chosen[0]["eng"] or len(o["eng"]) > LONGEST):
                continue
            chosen.append(o)
        result[rule] = [(f"P{o['paper']} {o['heading']}", o["eng"], o["lean"]) for o in chosen]
    return result


def shown(s):
    s = f" {s} ".replace(" PARA ", " ¶ ").replace(" INMARK ", " [– ").replace(" NEXTMARK ", " – ")
    s = s.replace(" OUTMARK ", " ] ").replace(" GLUE ", "").strip()
    return s.replace("|", "\\|")


def write_cards(work):
    """Rewrite RULE-CARDS.md from the saved usage of all runs. work is a scratch folder."""
    for g in ("IR", "IREng", "IRLean"):
        if not (work / f"{g}.gf").exists():
            (work / f"{g}.gf").write_text((BASE / "Grammar" / f"{g}.gf").read_text())
    g = compile_cards(work)
    table = tiers()
    sigs = signatures()
    names = [n for n, _, _ in sigs]
    if sorted(names) != sorted(table) or any(table[n]["tier"] not in TIERS for n in names):
        raise ValueError(f"RuleTiers.tsv must give each rule one known tier: "
                         f"{sorted(set(names) ^ set(table))}")
    texts, options, notes = load_usage()
    uses = [(x, set(x["rules"]) & set(names)) for x in texts]
    readings = {n: [x for x, u in uses if n in u] for n in names}
    cards = {}
    for name, args, result in sigs:
        rows = patterns(name, args, result)
        eng = g.batch([f"l -lang=IRCardsEng {t}" for _, t in rows], "IRCards")
        lean = g.batch([f"l -lang=IRCardsLean {t}" for _, t in rows], "IRCards")
        seen, out = set(), []
        for (note, _), e, l in zip(rows, eng, lean):
            if e[0] not in seen:
                seen.add(e[0])
                out.append((note, shown(e[0]), shown(l[0])))
        cards[name] = out
    found = examples(options)

    def signed(rules):
        return sum(bool(table[n]["reviewed by"].strip()) for n in rules)

    lines = ["# Rule cards", "",
             "Generated by `cards.py` from the grammar and the saved rule usage of the checked texts; do not edit. "
             "Each card shows the English and the Lean "
             "of one rule on placeholder arguments (P, Q: claims; X, Y: terms; T: a type; x, y, t: variables; "
             "…: the rest of the text). To review a rule, check that a mathematician reads the English as the "
             "Lean says, then put your name in the `reviewed by` column of `RuleTiers.tsv`. "
             "A reading is reviewed when every rule it uses is signed. Labels of Lean constants are made by "
             "one fixed rule (`label_words` in `selector.py`) and need no card. Rows marked “e.g.” are real "
             "examples: the shortest sentences of the checked readings and glossary definitions that use the "
             "rule, with the rest of the text as “…”, from two papers where possible. [Rules](RULES.md)", "",
             "Built from: " + "; ".join(notes) + ".", "",
             "## Review status by paper", "",
             "| Paper | Texts | Rules used | New rules | " + " | ".join(TIERS) + " | Signed |",
             "|---|---:|---:|---:|" + "---:|" * len(TIERS) + "---:|"]
    papers = sorted({x["paper"] for x, _ in uses if x["part"] == "reading"}, key=order)
    groups = [(f"P{p}", [u for x, u in uses if x["part"] == "reading" and x["paper"] == p]) for p in papers]
    groups.append(("Glossary", [u for x, u in uses if x["part"] == "glossary"]))
    seen = set()
    for label, group in groups + [("All", [u for _, u in uses])]:
        rules = set().union(*group) if group else set()
        counts = [sum(table[n]["tier"] == tier for n in rules) for tier in TIERS]
        new = "" if label == "All" else str(len(rules - seen))
        seen |= rules
        lines.append(f"| {label} | {len(group)} | {len(rules)} | {new} | " + " | ".join(map(str, counts)) +
                     f" | {signed(rules)} |")
    used = [n for n in names if readings[n]]
    per = sorted(len(u) for _, u in uses)
    lines += ["", "“Texts” counts the checked readings of a paper; the glossary row counts the checked "
              "definitions of all glossary pages. “New rules” counts the rules a row uses that no earlier row used. "
              f"The grammar has {len(names)} rules; {len(names) - len(used)} are used by no checked text"
              + (f" ({', '.join(f'`{n}`' for n in names if not readings[n])})" if len(used) < len(names) else "")
              + ". " + (f"A text uses between {per[0]} and {per[-1]} rules (median {per[len(per) // 2]})." if per else ""),
              ""]
    for tier in TIERS:
        lines += [f"## {tier.capitalize()}", "", TIER_TEXT[tier], "",
                  "| Rule | English | Lean | Texts | Check | Signed |", "|---|---|---|---:|---|---|"]
        for name in names:
            if table[name]["tier"] != tier:
                continue
            count = len(readings[name])
            papers_n = len({x["paper"] for x in readings[name]})
            for k, (note, e, l) in enumerate(cards[name]):
                first = k == 0
                label = f"`{name}`" if first else f"↳ if {note}"
                lines.append(f"| {label} | {e} | `{l}` | " + (f"{count} ({papers_n} papers)" if first else "") +
                             " | " + table[name]["what to check"].replace("|", "\\|") * first + " | " +
                             (table[name]["reviewed by"].strip() or "—") * first + " |")
            if name != "Reading":   # the whole reading is its own example
                for where, e, l in found.get(name, []):
                    lines.append(f"| ↳ e.g. {where} | {e} | `{l}` |  |  |  |")
        lines.append("")
    (BASE / "RULE-CARDS.md").write_text("\n".join(lines))
    return len(names), len(used)


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="ir-cards-") as temp:
        total, used = write_cards(Path(temp))
    print(f"Rule cards: {used} of {total} rules used by the checked texts; see RULE-CARDS.md")
