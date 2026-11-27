"""Select a GF tree from the structural Lean export (Export.lean).

Constructions are chosen by the shape of the expression: binder types, hypotheses,
logical connectives and the head constants of atoms. The theorem name is never consulted.
The P01 vocabulary comes first; every other constant is shown by its label, a phrase made
from its Lean name by `label_words`, with its arguments in Lean's order, or as a short sentence
when Frames.tsv gives one.
"""
import csv
import hashlib
from pathlib import Path
import re

BASE = Path(__file__).resolve().parents[1]  # the IRStatement folder
NAT = ["const", "Nat", []]
FAMILY_TYPES = {"GenLimit.OracleFamily", "GenLimit.KM.Transport.IndexedOracleFamily"}
LANGUAGE = {"GenLimit.OracleFamily.language", "GenLimit.KM.Transport.IndexedOracleFamily.language"}
QUERY = {"GenLimit.OracleFamily.query", "GenLimit.KM.Transport.IndexedOracleFamily.query"}
SAMPLES = {"GenLimit.sample", "GenLimit.Generic.sample"}
with (BASE / "Tables" / "Renaming.tsv").open() as source:
    # Display names for bound variables. Renaming is α-equivalence, so the kernel check covers it.
    # A row with a paper applies to that paper only. A row whose Lean name is a constant gives the
    # name of a named term headed by that constant ("Let t⋆ = …"), in place of its first letter.
    _rows = list(csv.DictReader(source, delimiter="\t"))
RENAMING = {r["Lean name"]: r["display name"] for r in _rows if not r["paper"]}
PAPER_RENAMING, PREFERRED = {}, {}
for _r in _rows:
    if _r["paper"]:
        (PREFERRED if "." in _r["Lean name"] else PAPER_RENAMING).setdefault(_r["paper"], {})[_r["Lean name"]] = \
            _r["display name"]
with (BASE / "Tables" / "Frames.tsv").open() as source:
    # A label with several arguments may read as a short sentence: {label} is the label in italics and
    # {1}, {2}, … are the shown arguments in Lean's order, e.g. "{1} {label} {3} on {2}".
    FRAMES = {r["constant"]: r["frame"] for r in csv.DictReader(source, delimiter="\t")}
FRAME_WORD = re.compile(r"[a-z]+")
# Words a frame may not add: the grammar's own connectives and quantifier words, which would make the
# sentence ambiguous or look like logic the label does not have.
FRAME_STOP = {"and", "or", "not", "if", "then", "iff", "only", "every", "some", "each", "all", "any", "no", "there",
              "exists", "holds", "hold", "does", "such", "that", "let", "be", "suppose", "it", "case", "false", "true",
              "the", "following", "where", "when", "always", "eventually", "never"}


def frame_arity(frame):
    """The number of arguments of a frame; raises unless {label} and each {k} occur exactly once."""
    words = frame.split()
    slots = [int(w[1:-1]) for w in words if re.fullmatch(r"\{[1-9]\}", w)]
    bad = [w for w in words if w != "{label}" and not re.fullmatch(r"\{[1-9]\}", w)
           and (not FRAME_WORD.fullmatch(w) or w in FRAME_STOP)]
    if words.count("{label}") != 1 or sorted(slots) != list(range(1, len(slots) + 1)) or len(slots) < 2 or bad:
        raise ValueError(f"Malformed frame {frame!r}")
    return len(slots)


for _f in FRAMES.values():
    frame_arity(_f)


def frame_negation(frame):
    """The frame of the negation when a copula comes before the label: "is" → "is not", "are" → "are not",
    "has" → "does not have". None otherwise (the negation then reads "it is not the case that …")."""
    words = frame.split()
    for i, w in enumerate(words[:words.index("{label}")]):
        if w in ("is", "are"):
            return " ".join(words[:i + 1] + ["not"] + words[i + 1:])
        if w == "has":
            return " ".join(words[:i] + ["does", "not", "have"] + words[i + 1:])
    return None
with (BASE / "Tables" / "Unfold.tsv").open() as source:
    # An unfolded definition with a local word becomes a defined adjective.
    WORDS = {r["definition"]: r["local word"] for r in csv.DictReader(source, delimiter="\t") if r["local word"]}
# A generator is named once (G); its outputs form a sequence (o, w). `prefix` counts the
# arguments that fix the generator; the rest are inputs, proofs and finally the step.
GENERATORS = {
    "GenLimit.OracleFamily.kmGenerator":
        {"ctor": "KMGenerator", "prefix": 1, "fam": 0, "params": [], "run": "RunAt", "proofs": [], "seq": "o"},
    "GenLimit.KM.Prompted.generatorOfEquiv":
        {"ctor": "PromptedGenerator", "prefix": 2, "fam": 1, "params": [0], "run": "RunPromptedAt",
         "proofs": [4], "seq": "w"},
}
# `e a₁ … aₖ h` lists the elements of `s a₁ … aₖ` in increasing order, where `h` proves
# that set infinite. The kernel confirms this identification through
# IRStatement.increasingEnumeration.
ENUMERATIONS = {"GenLimit.KM.FiniteFamily.enumerateAccepted": "GenLimit.KM.FiniteFamily.acceptedSet"}
COMPREHENSIONS = {"setOf": "ABCDEFH", "Finset.filter": "IJKMN"}
SYMBOLIC = {"LE.le", "Membership.mem", "HasSubset.Subset"}
# Names that would collide with English words of the grammar or with formal binders.
RESERVED = {"a", "an", "it", "i", "n", "c", "subject", "the", "is", "be", "if", "or", "and", "on", "at", "to", "of"}
RELATIONS = {"Eq": "Eq", "Ne": "Ne", "LE.le": "Le", "LT.lt": "Lt", "GE.ge": "Ge", "GT.gt": "Gt"}
OPERATORS = {"HAdd.hAdd": "Add", "HSub.hSub": "Minus", "HMul.hMul": "Mul", "HDiv.hDiv": "Div", "HPow.hPow": "Pow",
             "Union.union": "Union", "Inter.inter": "Inter", "SDiff.sdiff": "Diff"}
NAME = r"[^\W\d_][^\W_]*(?:_[^\W_]+)*'*[⋆∗]?"   # a star as in t⋆ is a superscript


class NotInline(Exception):
    pass


def node(op, *args):
    return op if not args else "(" + " ".join([op, *args]) + ")"


def tag(prefix, key):
    return prefix + hashlib.sha256(key.encode()).hexdigest()[:12]


def label_words(name):
    """The label of a Lean constant: its last name component, split into lower-case words.
    Acronyms keep their capitals: GenLimit.Generic.GeneratableInLimit ↦ generatable in limit."""
    words = []
    for piece in name.split(".")[-1].split("_"):
        for w in re.findall(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+[^\W_A-Za-z0-9]*|[A-Z]+[^\W_A-Za-z0-9]*|[0-9]+|[^\W_]+",
                            piece):
            words.append(w if len(w) > 1 and w.isupper() else w.lower())
    return " ".join(words)


def core(n):
    while n[0] == "unfolded":
        n = n[3]
    return n


def is_const(n, *names):
    n = core(n)
    return n[0] == "const" and (not names or n[1] in names)


def var_name(n):
    n = core(n)
    if n[0] != "var" or n[2]:
        raise NotInline(f"expected a variable, found {n}")
    return n[1]


def is_node(c):
    return isinstance(c, list) and bool(c) and isinstance(c[0], str)


def children_of(n):
    for c in n[1:]:
        if is_node(c):
            yield c
        elif isinstance(c, list):
            yield from (a for a in c if is_node(a))


def free_vars(n, bound=frozenset(), hidden=True):
    """Free variables of a node. With hidden=False, a hypothesis passed as a hidden proof argument
    (see `hide_proofs`) does not count: it is used, but not shown."""
    t = n[0]
    if t == "var":
        out = set() if n[1] in bound else {n[1]}
        for a in n[2]:
            out |= free_vars(a, bound, hidden)
        return out
    if t == "const":
        out = set().union(*(free_vars(a, bound, hidden) for a in n[2])) if n[2] else set()
        if hidden and len(n) > 3 and isinstance(n[3], tuple):
            out |= {v for v in n[3] if v not in bound}
        return out
    if t == "unfolded":
        return free_vars(n[3], bound, hidden)
    if t in ("forall", "exists", "lam", "let"):
        if t == "forall":
            parts, body = [n[5]], n[6]
        elif t == "exists":
            parts, body = [n[3]], n[4]
        elif t == "lam":
            parts, body = [n[2]], n[3]
        else:
            parts, body = [n[2], n[3]], n[4]
        out = set().union(*(free_vars(p, bound, hidden) for p in parts))
        return out | free_vars(body, bound | {n[1]}, hidden)
    if t in ("and", "or", "iff"):
        return free_vars(n[1], bound, hidden) | free_vars(n[2], bound, hidden)
    if t == "not":
        return free_vars(n[1], bound, hidden)
    return set()


def binder_names(n):
    out = {n[1]} if n[0] in ("forall", "exists", "lam", "let") else set()
    for c in children_of(n):
        out |= binder_names(c)
    return out


def visible_names(n):
    """Names that can be displayed. Arrow-type binders (ℕ → ℕ), instance binders and proof
    binders never appear in the English or in P′, so they cannot clash with a display name."""
    hidden = n[0] == "forall" and ((not n[3] and not n[4]) or n[3] or n[2] == "inst")
    out = {n[1]} if n[0] in ("forall", "exists", "lam", "let") and not hidden else set()
    for c in children_of(n):
        out |= visible_names(c)
    return out


def rename(n, old, new):
    if not isinstance(n, list):
        return n
    if n and n[0] == "var" and n[1] == old:
        return ["var", new, [rename(a, old, new) for a in n[2]]]
    if n and n[0] in ("forall", "exists", "lam", "let") and n[1] == old:
        n = [n[0], new, *n[2:]]
    return [rename(c, old, new) if isinstance(c, list) else c for c in n]


def replace(n, target, new):
    if n == target:
        return new
    if not isinstance(n, list):
        return n
    return [replace(c, target, new) if isinstance(c, list) else c for c in n]


def tidy(value, taken):
    """Restore the source names of bound variables that Lean suffixed to avoid a capture."""
    for name in sorted(binder_names(value)):
        m = re.fullmatch(r"(.+)_\d+", name)
        if m and m[1] not in taken and m[1] not in binder_names(value) | free_vars(value):
            value = rename(value, name, m[1])
    return value


def name_list(refs):
    out = node("OneName", refs[-1])
    for r in reversed(refs[:-1]):
        out = node("MoreNames", r, out)
    return out


def chain(ctor_one, ctor_more, items):
    out = node(ctor_one, items[-1])
    for x in reversed(items[:-1]):
        out = node(ctor_more, x, out)
    return out


def conjuncts(n):
    """The right spine of a conjunction."""
    items, n = [], core(n)
    while n[0] == "and":
        items.append(n[1])
        n = core(n[2])
    return items + [n]


def simple_claim(n):
    """A claim that reads as one clause: no quantifier, implication, or nested connective."""
    n = core(n)
    if n[0] == "not":
        return simple_claim(n[1])
    return n[0] in ("const", "var")


def opens_with_universal(n):
    """Whether the property of a choice opens by introducing a variable for all its values: a "Let …"
    sentence or a leading "for every", possibly after local definitions and assumptions. Only then
    does the choice show its dependency list, which tells the reader that the chosen object does not
    depend on that variable. A variable inside a bullet or a later clause is plainly introduced after
    the choice."""
    n = core(n)
    while n[0] == "let" or (n[0] == "forall" and (n[3] or n[2] == "inst")):
        n = core(n[4] if n[0] == "let" else n[6])
    return n[0] == "forall"


def below(h, x):
    """Whether the hypothesis h reads x < n, for the variable x."""
    h = core(h)
    return h[0] == "const" and h[1] == "LT.lt" and len(h[2]) == 2 and h[2][0] == ["var", x, []]


def quantified_claim(n):
    """A universal claim that reads as one clause, "P for every x ∈ T" (or "for every x ∈ X", "for every
    t ≥ T"), with P a simple claim."""
    n = core(n)
    if n[0] != "forall" or n[3] or n[2] == "inst":
        return False
    b = core(n[6])
    if b[0] == "forall" and b[3] and not b[4]:
        h = core(b[5])
        bound = h[0] == "const" and h[1] in ("LE.le", "Membership.mem") and len(h[2]) == 2 \
            and h[2][1] == ["var", n[1], []]
        return (bound or (below(h, n[1]) and n[5] == NAT)) and simple_claim(b[6])
    while b[0] == "forall" and not b[3] and b[2] != "inst" and b[5] == n[5]:
        b = core(b[6])
    return simple_claim(b)


def introduces(n):
    """Whether a claim introduces a variable of its own: a universal or existential binder, or
    "for infinitely many" and "for all sufficiently large". A choice followed by such a
    variable shows its dependency list, so the reader sees that it does not depend on it."""
    n = core(n)
    t = n[0]
    if t == "forall":
        return (n[2] != "inst" and not n[3]) or introduces(n[6])
    if t == "exists":
        return not n[2] or introduces(n[4])
    if t in ("and", "or", "iff"):
        return introduces(n[1]) or introduces(n[2])
    if t == "not":
        return introduces(n[1])
    if t == "let":
        return introduces(n[4])
    return t == "const" and n[1] in ("Filter.Frequently", "Filter.Eventually")


# Constants that the selector shows by a construction of its own; only label applications are named.
SPECIAL = (LANGUAGE | QUERY | SAMPLES | set(GENERATORS) | set(ENUMERATIONS) | set(COMPREHENSIONS) | SYMBOLIC
           | set(RELATIONS) | set(OPERATORS) | {"Nat.cast", "Neg.neg", "Finset.toSet", "Set.range", "Finset.card",
              "List.length", "List.IsPrefix", "Function.Injective", "Set.Infinite", "Prod.mk", "Subtype.mk",
              "Subtype.val", "List.cons", "List.nil", "Unit.unit", "PUnit.unit", "Filter.Frequently",
              "Filter.Eventually", "Filter.atTop", "Bool.true", "Bool.false", "Option.some", "Option.none",
              "List", "Set", "Finset", "Option", "Prod", "Sum", "Fin", "Multiset"})


def only_coerced(x, n):
    """Whether every use of the variable x in n is under a coercion, so that its type cannot be inferred."""
    def uses(m, under):
        if not is_node(m):
            return 0, 0
        if m[0] == "var" and m[1] == x and not m[2]:
            return 1, int(under)
        coercion = m[0] == "const" and m[1] in ("Subtype.val", "Nat.cast")
        total = hidden = 0
        for c in children_of(m):
            a, b = uses(c, under or coercion)
            total, hidden = total + a, hidden + b
        return total, hidden
    total, hidden = uses(n, False)
    return total > 0 and total == hidden


def plain(n):
    """A term made only of applications of constants and variables, and numerals."""
    if not is_node(n):
        return False
    if n[0] == "nat":
        return True
    return n[0] in ("const", "var") and all(plain(a) for a in n[2])


def width(n):
    """About how many characters the term takes in the English: label, name, brackets and commas.
    An unfolded application counts as its label application, which its body is never shorter than."""
    if n[0] == "nat":
        return len(str(n[1]))
    head = len(label_words(n[1])) + 2 if n[0] in ("const", "unfolded") else len(n[1])
    return head + (sum(width(a) for a in n[2]) + 2 * len(n[2]) if n[2] else 0)


def binder_counts(n, out=None):
    out = {} if out is None else out
    if n[0] in ("forall", "exists", "lam", "let"):
        out[n[1]] = out.get(n[1], 0) + 1
    for c in children_of(n):
        binder_counts(c, out)
    return out


def nameable(a):
    """A label application worth naming when repeated: plain arguments, not shown by a construction
    of its own. An unfolded one (a definition the reading shows by its body) counts too."""
    if not is_node(a) or a[0] not in ("const", "unfolded") or a[1] in SPECIAL or a[1] in WORDS or not a[2]:
        return False
    return all(plain(x) for x in a[2])


def occurrences(n, out):
    """Count the label applications that occur as arguments. An unfolded definition counts in its body.
    Types of binders are skipped: a type is never named."""
    if not is_node(n):
        return
    if n[0] == "unfolded":
        return occurrences(n[3], out)
    if n[0] == "forall":
        return occurrences(n[6], out) if not n[3] else (occurrences(n[5], out), occurrences(n[6], out))[1]
    if n[0] == "exists":
        return occurrences(n[4], out) if not n[2] else (occurrences(n[3], out), occurrences(n[4], out))[1]
    if n[0] == "lam":
        return occurrences(n[3], out)
    if n[0] in ("const", "var"):
        for a in n[2]:
            if nameable(a):
                key = repr(a)
                out[key] = (out.get(key, (a, 0))[0], out.get(key, (a, 0))[1] + 1)
    for c in children_of(n):
        occurrences(c, out)


def extends(n, a):
    """Whether n applies the same constant as the label application a to a's arguments and more."""
    return (is_node(n) and n[0] in ("const", "unfolded") and is_node(a) and a[0] in ("const", "unfolded")
            and n[1] == a[1] and len(n[2]) > len(a[2]) and n[2][:len(a[2])] == a[2])


def substitute(n, target, new):
    """Replace target by new. When new is a variable K naming the label application target,
    an application of the same label to target's arguments and more becomes K(more)."""
    if n == target:
        return new
    if not isinstance(n, list):
        return n
    if new[0] == "var" and extends(n, target):
        return ["var", new[1], [substitute(x, target, new) for x in n[2][len(target[2]):]]]
    return [substitute(c, target, new) if isinstance(c, list) else c for c in n]


def extended(n, a, found):
    """Count the shown applications that extend a (see `extends`); like `occurrences`, skip types of binders
    and the arguments recorded on an unfolded node."""
    if not is_node(n):
        return
    if extends(n, a):
        found[0] += 1
    if n[0] == "unfolded":
        return extended(n[3], a, found)
    if n[0] == "forall" and not n[3]:
        return extended(n[6], a, found)
    if n[0] == "exists" and not n[2]:
        return extended(n[4], a, found)
    for c in children_of(n):
        extended(c, a, found)


def recorded(n, out):
    """Label applications recorded as arguments of unfolded nodes: not shown themselves, but a
    name for them can be shown where their extensions are."""
    if not is_node(n):
        return
    if n[0] == "unfolded":
        for a in n[2]:
            if nameable(a):
                out.setdefault(repr(a), (a, 0))
    for c in children_of(n):
        recorded(c, out)


def candidates(root, lifted):
    """Repeated label applications worth a name: used at least twice (counting applications to more
    arguments, which read K(i)), and saving about 20 characters or more. Larger ones first, so a named term absorbs the terms inside it. Each variable of the
    term must be bound once, so every use refers to the same objects."""
    counts = {}
    occurrences(root, counts)
    for d in lifted:
        occurrences(["const", "_", [d["value"]]], counts)
    recorded(root, counts)
    for key, (a, k) in list(counts.items()):  # K(i) for K = c(x) also uses the name K
        found = [0]
        for m in [root, *(d["value"] for d in lifted)]:
            extended(m, a, found)
        counts[key] = (a, k + found[0])
    bound = binder_counts(root)
    names = {d["name"] for d in lifted}
    out = [(a, k) for a, k in counts.values()
           if k >= 2 and (k - 1) * width(a) >= 20 and all(bound.get(v, 0) == 1 or v in names for v in free_vars(a))]
    return [a for a, _ in sorted(out, key=lambda x: -width(x[0]))]


class Selector:
    def __init__(self):
        self.vars, self.fams, self.consts, self.numerals = {}, {}, set(), set()
        self.frames = set()       # constants read as a sentence (FRAMES)
        self.negated = set()      # constants whose negated frame is used
        self.definitions = []     # pending definitions, in the order they were found
        self.meaning = {}         # set name -> the node it abbreviates
        self.adjectives = set()
        self.defines = None       # (constant, kind) when reading a definition statement of the glossary

    # ---------- lexicon ----------
    def var(self, name):
        if not re.fullmatch(NAME, name):
            raise ValueError(f"Display name {name!r} is not an identifier")
        self.vars[name] = tag("v_", name)
        return self.vars[name]

    def fam(self, name):
        if name in RESERVED:
            raise ValueError(f"Family name {name!r} is reserved")
        if name not in self.fams:
            self.fams[name] = "LMKP"[len(self.fams)]
        return tag("f_", name)

    def lbl(self, const):
        self.consts.add(const)
        return tag("l_", const)

    def numeral(self, k):
        self.numerals.add(k)
        return tag("n_", str(k))

    # ---------- naming pass ----------
    def name_subterms(self, root):
        taken = binder_names(root) | free_vars(root) | RESERVED
        types = {}

        def fresh(letters):
            name = next(c for c in letters if c not in taken)
            taken.add(name)
            return name

        def type_of(arg):
            arg = core(arg)
            if arg[0] != "var":
                raise ValueError(f"Cannot type {arg}")
            ty = types[arg[1]]
            for _ in arg[2]:
                if ty[0] != "forall":
                    raise ValueError(f"Too many arguments in {arg}")
                ty = ty[6]
            return ty

        def children(n):
            if n[0] in ("forall", "exists", "lam"):
                types[n[1]] = n[5] if n[0] == "forall" else n[3] if n[0] == "exists" else n[2]
            return [n[0], *[[visit(a) for a in c] if isinstance(c, list) and not is_node(c)
                             else visit(c) for c in n[1:]]]

        def visit(n):
            if not is_node(n):
                return n
            if n[0] == "unfolded" and n[1] in WORDS:
                *others, arg = n[2]
                word = WORDS[n[1]]
                body = visit(replace(n[3], arg, ["var", "subject", []]))
                if word not in self.adjectives:
                    self.adjectives.add(word)
                    taken.add(word)
                    ty = type_of(arg)
                    self.definitions.append({"name": word, "kind": "pred", "type": ty, "body": body,
                                             "free": (free_vars(body) - {"subject"}) | free_vars(ty)})
                return ["var", word, [visit(arg)]]
            c = core(n)
            if c[0] == "const" and c[1] in COMPREHENSIONS and n[0] == "unfolded":
                # Name an unfolded comprehension; inner ones first. Remember what it unfolds.
                value = children(c)
                name = fresh(COMPREHENSIONS[c[1]])
                self.definitions.append({"name": name, "kind": "set", "value": value, "free": free_vars(value)})
                self.meaning[name] = n
                return ["var", name, []]
            n = children(n)
            c = core(n)
            if c[0] == "const" and c[1] in GENERATORS:
                spec = GENERATORS[c[1]]
                head, rest, step = c[2][:spec["prefix"]], c[2][spec["prefix"]:-1], c[2][-1]
                if step[0] != "var" or step[2]:
                    raise ValueError(f"Generator step is not a variable in {c}")
                gen = next((d for d in self.definitions if d["kind"] == "gen" and d["key"] == (c[1], head)), None)
                if gen is None:
                    gen = {"name": fresh("GHK"), "kind": "gen", "key": (c[1], head), "spec": spec,
                           "args": head, "free": free_vars(["const", "_", head])}
                    self.definitions.append(gen)
                seq = next((d for d in self.definitions if d["kind"] == "seq" and d["key"] == (gen["name"], rest)), None)
                if seq is None:
                    seq = {"name": fresh(spec["seq"]), "kind": "seq", "key": (gen["name"], rest), "gen": gen["name"],
                           "spec": spec, "args": rest, "step": step[1],
                           "free": {gen["name"]} | free_vars(["const", "_", rest])}
                    self.definitions.append(seq)
                return ["var", seq["name"], [step]]
            return n

        return visit(root), fresh

    # ---------- outline ----------
    def emit_ready(self, scope, rest):
        """Introduce each pending definition as soon as everything it uses is in scope."""
        names = {s[0] for s in scope}
        ready = [d for d in self.definitions if d["free"] <= names]
        if not ready:
            return rest(scope)
        d = ready[0]
        self.definitions.remove(d)
        inner = scope + [(d["name"], "letfam" if d.get("family") else "let")]
        then = self.emit_ready(inner, rest)
        if d.get("family"):  # a named term that is a family of languages: its languages get a letter
            return node("DefineFam", self.fam(d["name"]), self.term(d["value"], scope), then)
        v = self.var(d["name"])
        if d["kind"] == "set":
            return node("Define", v, self.term(tidy(d["value"], names), scope), then)
        if d["kind"] == "term":
            return node("Define", v, self.term(d["value"], scope), then)
        if d["kind"] == "pred":
            return node("DefinePred", v, self.ty(d["type"]), self.pred(d["body"]), then)
        spec = d["spec"]
        if d["kind"] == "gen":
            params = [self.var(var_name(d["args"][i])) for i in spec["params"]]
            return node("Define", v, node(spec["ctor"], self.fam(var_name(d["args"][spec["fam"]])), *params), then)
        proofs = [i - spec["prefix"] for i in spec["proofs"]]
        for p in proofs:
            if dict(scope).get(var_name(d["args"][p])) != "hyp":
                raise ValueError(f"Proof argument {d['args'][p]} is not a hypothesis in scope")
        shown = [self.var(var_name(a)) for k, a in enumerate(d["args"]) if k not in proofs]
        step = d["step"] if d["step"] not in names else next(c for c in "tsk" if c not in names)
        return node("DefineSeq", v, self.var(step),
                    node(spec["run"], self.var(d["gen"]), *shown, self.var(step)), then)

    def hypotheses_after(self, body, x):
        """Symbolic hypotheses directly after a binder that mention it join its sentence."""
        out = []
        while body[0] == "forall" and body[3] and not body[4] and x in free_vars(body[5]) \
                and is_const(body[5], *SYMBOLIC) and len(out) < 2:
            out.append(body[5])
            body = body[6]
        return out, body

    def outline(self, n, scope, started=False):
        return self.emit_ready(scope, lambda sc: self.step(n, sc, started or len(sc) > len(scope)))

    def deps(self, scope):
        refs = []
        for name, kind in scope:
            if kind in ("var", "type"):
                refs.append(node("RVar", self.var(name)))
            elif kind == "fam":
                refs.append(node("RFam", self.fam(name)))
        return name_list(refs) if refs else None

    def uses_proof(self, h, body):
        """Whether the hypothesis h is shown later, so that it needs a name. A hidden proof argument
        uses h without showing it."""
        def shown(d):
            part = d.get("value", d.get("body"))
            return free_vars(part, hidden=False) if part is not None else d["free"]
        return h in free_vars(body, hidden=False) or any(h in shown(d) and d["kind"] != "seq" for d in self.definitions)

    def step(self, n, scope, started):
        if n[0] == "unfolded":
            return self.step(n[3], scope, started)
        if n[0] == "let":
            _, x, _, value, body = n
            return node("Define", self.var(x), self.term(value, scope), self.outline(body, scope + [(x, "let")], True))
        if n[0] == "forall":
            _, x, info, prop, dependent, dom, body = n
            if info == "inst":
                inner = self.outline(body, scope + [(x, "inst")], True)
                d = core(dom)
                if is_const(d, "DecidableEq"):
                    return node("AssumeDecEq", self.var(var_name(d[2][0])), inner)
                if d[0] == "const" and len(d[2]) == 1:
                    return node("AssumeClass", self.var(var_name(d[2][0])), self.lbl(d[1]), inner)
                if d[0] == "const" and len(d[2]) > 1:
                    return node("AssumeClassOver", self.lbl(d[1]), chain("OneTy", "MoreTy", [self.ty(a) for a in d[2]]),
                                inner)
                raise ValueError(f"Unsupported instance {dom}")
            if prop:
                if dependent and self.uses_proof(x, body):
                    return node("SupposeNamed", self.var(x), self.prop(dom, scope),
                                self.outline(body, scope + [(x, "hyp")], True))
                return node("Suppose", self.prop(dom, scope), self.outline(body, scope + [(x, "hyp")], True))
            if dom[0] == "sort" and dom[1] != "Prop":
                # "Let A and B be types." Lean gives each binder of `(A B : Type _)` its own universe.
                group, last = [x], n
                while core(last[6])[0] == "forall" and not core(last[6])[3] and core(last[6])[2] != "inst" \
                        and core(core(last[6])[5])[0] == "sort" and self.ty(core(last[6])[5]) == self.ty(dom):
                    last = core(last[6])
                    group.append(last[1])
                if len(group) > 1:
                    return node("LetMany", name_list([node("RVar", self.var(g)) for g in group]), self.ty(dom),
                                self.outline(last[6], scope + [(g, "type") for g in group], True))
                return node("LetTy", self.var(x), self.ty(dom), self.outline(body, scope + [(x, "type")], True))
            if is_const(dom, *FAMILY_TYPES):
                fam_ty = "NatLanguages" if not dom[2] else node("LanguagesOver", self.ty(dom[2][0]))
                return node("LetFamily", self.fam(x), fam_ty, self.outline(body, scope + [(x, "fam")], True))
            group, last = [x], n
            while True:
                b = core(last[6])
                if self.hypotheses_after(last[6], last[1])[0] or b[0] != "forall" or b[3] or b[2] == "inst" \
                        or b[5] != dom or is_const(dom, *FAMILY_TYPES) or self.hypotheses_after(b[6], b[1])[0]:
                    break
                group.append(b[1])
                last = b
            if len(group) > 1:
                kind = "type" if dom[0] == "sort" else "var"
                return node("LetMany", name_list([node("RVar", self.var(g)) for g in group]), self.ty(dom),
                            self.outline(last[6], scope + [(g, kind) for g in group], True))
            hyps, rest = self.hypotheses_after(body, x)
            inner = scope + [(x, "var")] + [("_", "hyp")] * len(hyps)
            v = self.var(x)
            first = core(hyps[0]) if hyps else None
            if first and dom == NAT and is_const(first, "LE.le") and first[2][1] == ["var", x, []]:
                if len(hyps) != 1:
                    raise ValueError("A lower bound and a second hypothesis after one binder")
                lo = self.term(first[2][0], scope)
                if core(rest)[0] in ("and", "not", "const", "var") and not self.definitions:
                    # A final claim under "for every t ≥ T" fits in one sentence.
                    try:
                        return node("Claim", node("ForallAtLeast", v, lo, self.prop(rest, inner)))
                    except NotInline:
                        pass
                return node("LetGe", v, lo, self.outline(rest, inner, True))
            if first and is_const(first, "Membership.mem") and first[2][1] == ["var", x, []]:
                where = self.term(first[2][0], scope)
                if len(hyps) == 2:
                    return node("LetInWith", v, where, self.prop(hyps[1], scope + [(x, "var")]),
                                self.outline(rest, inner, True))
                return node("LetIn", v, where, self.outline(rest, inner, True))
            if hyps:
                if len(hyps) != 1:
                    raise ValueError("Two symbolic hypotheses after a typed binder")
                return node("LetTyWith", v, self.ty(dom), self.prop(hyps[0], scope + [(x, "var")]),
                            self.outline(rest, inner, True))
            return node("LetTy", v, self.ty(dom), self.outline(body, scope + [(x, "var")], True))
        if n[0] == "exists" and not n[2]:
            chosen, body = [], n
            while core(body)[0] == "exists" and not core(body)[2]:
                b = core(body)
                chosen.append((b[1], b[3]))
                body = b[4]
            later = introduces(body)
            if len(chosen) == 1 and not later and not self.definitions \
                    and all(simple_claim(c) for c in conjuncts(body)):
                # "Then there is x ∈ A such that P." A choice that ends the text needs no property paragraph.
                try:
                    return self.final(n, scope, started)
                except NotInline:
                    pass
            deps = self.deps(scope) if opens_with_universal(body) else None
            inner = self.outline(body, scope + [(c, "var") for c, _ in chosen])
            if len(chosen) > 1:
                binds = node("OneBind", self.var(chosen[-1][0]), self.ty(chosen[-1][1]))
                for c, t in reversed(chosen[:-1]):
                    binds = node("MoreBinds", self.var(c), self.ty(t), binds)
                if deps is None:
                    return node("ThereAreFree", binds, inner)
                return node("ThereAre", binds, deps, inner)
            (x, dom), = chosen
            if deps is None:
                return node("ThereIsFree", self.var(x), self.ty(dom), inner)
            return node("ThereIs", self.var(x), self.ty(dom), deps, inner)
        if n[0] == "exists":
            _, h, _, dom, body = n
            if is_const(dom, "Set.Infinite") and core(core(dom)[2][0])[0] == "var" and core(dom)[2][0][1] in self.meaning:
                return self.infinite_enumeration(n, scope)
            # Any other existential over a proof: state the fact and name it for later use.
            return node("FactNamed", self.var(h), self.prop(dom, scope), self.outline(body, scope + [(h, "hyp")], True))
        return self.final(n, scope, started)

    def final(self, n, scope, started):
        """The claim that ends an outline: one sentence when simple, a list when compound."""
        c = core(n)
        if self.defines:
            return self.definition(c, scope)
        if c[0] == "and" and not all(simple_claim(x) for x in conjuncts(c)):
            # A bullet that is one universal claim reads "P for every x ∈ T", not "Let x ∈ T. Then P."
            items = [node("Claim", self.prop(x, scope)) if quantified_claim(x) else self.outline(x, scope)
                     for x in conjuncts(c)]
            return node("AllHold", chain("OneItem", "MoreItems", items))
        if c[0] == "iff" and not (simple_claim(c[1]) and simple_claim(c[2])):
            return node("Equivalent", self.outline(c[1], scope), self.outline(c[2], scope))
        if c[0] == "or":
            p, q = core(c[1]), core(c[2])
            if p[0] == q[0] == "and" and core(p[2])[0] == "not" and core(q[1])[0] == "not" \
                    and core(p[2])[1] == q[2] and core(q[1])[1] == p[1]:
                return node("ExactlyOne", self.prop(p[1], scope), self.prop(q[2], scope))
            if not (simple_claim(p) and simple_claim(q)):
                return node("EitherOr", self.outline(p, scope), self.outline(q, scope))
        if started:
            return node("Then", self.conclusions(n, scope))
        return node("Claim", self.prop(n, scope))

    def definition(self, c, scope):
        """The end of a definition statement: "By definition, P if and only if Q." for a
        proposition, "By definition, X = Y." for data, "By definition, a T is a U." for a type."""
        const, kind = self.defines
        self.defines = None  # only the outermost claim is the definition
        if kind == "prop" and c[0] == "iff" and is_const(c[1], const):
            p, rhs = self.prop(c[1], scope), c[2]
            if simple_claim(rhs) and not self.definitions:
                try:
                    return node("ByDefinition", p, self.prop(rhs, scope))
                except NotInline:
                    pass
            return node("ByDefinitionThen", p, self.outline(rhs, scope))
        if kind in ("data", "type") and is_const(c, "Eq") and len(c[2]) == 2 and is_const(c[2][0], const):
            if kind == "type":
                return node("DefinedType", self.ty(c[2][0]), self.ty(c[2][1]))
            return node("DefinedAs", self.term(c[2][0], scope), self.term(c[2][1], scope))
        raise ValueError(f"Not a definition statement of {const}")

    def infinite_enumeration(self, n, scope):
        """`∃ h : A.Infinite, P (e … h)`: A is infinite; list it in increasing order; then P."""
        _, h, _, dom, body = n
        if not is_const(dom, "Set.Infinite"):
            raise ValueError("Only an infinitude proof can stay implicit")
        a = var_name(core(dom)[2][0])
        source = self.meaning.get(a)
        if source is None or source[0] != "unfolded":
            raise ValueError(f"{a} does not abbreviate a named set")
        uses = []

        def collect(m):
            if is_node(m):
                if m[0] == "const" and m[1] in ENUMERATIONS:
                    uses.append(m)
                for c in children_of(m):
                    collect(c)
        collect(body)
        if not uses or any(u != uses[0] for u in uses):
            raise ValueError("Expected one enumeration term")
        e = uses[0]
        if ENUMERATIONS[e[1]] != source[1] or e[2][:-1] != source[2] or e[2][-1] != ["var", h, []]:
            raise ValueError(f"{e} is not the increasing enumeration of {a}")
        u = self.fresh("uvs")
        rest = replace(body, e, ["var", u, []])
        inner = scope + [(h, "hyp"), (u, "let")]
        return node("ThenInfinite", self.var(a),
                    node("ListIncreasing", self.var(u), self.var(a), node("Then", self.conclusions(rest, inner))))

    def conclusions(self, n, scope):
        """A right-nested conjunction becomes separate sentences: Then P. Also, Q."""
        items = conjuncts(n)
        props, k = [], 0
        while k < len(items):
            pair = items[k:k + 2]
            if len(pair) == 2 and self.member_pair(*pair):
                props.append(self.prop(["and", *pair], scope))
                k += 2
            else:
                props.append(self.prop(items[k], scope))
                k += 1
        if len(props) == 2 and all(core(i)[0] in ("const", "not", "var") for i in items):
            return node("Finally", node("And", *props))
        return chain("Finally", "Also", props)

    @staticmethod
    def member_pair(p, q):
        p, q = core(p), core(q)
        sets = {"Set", "Finset"}
        return (is_const(p, "Membership.mem") and q[0] == "not" and is_const(q[1], "Membership.mem")
                and core(q[1])[2][1] == p[2][1] and p[3:4] and p[3] in sets
                and core(q[1])[3:4] and core(q[1])[3] in sets)

    # ---------- types and predicates ----------
    def ty(self, n):
        n = core(n)
        if n == NAT:
            return "TNat"
        if n[0] == "sort":
            return {"Prop": "TProp", "Type _": "TType", "Type": "TType0"}.get(n[1], "TSort")
        if n[0] == "var" and not n[2]:
            if n[1] in self.fams:
                return node("TFamily", self.fam(n[1]))
            return node("TVar", self.var(n[1]))
        if n[0] == "var":
            return node("TVarApp", self.var(n[1]), self.args(n[2], []))
        if n[0] == "const" and n[1] == "Subtype" and len(n[2]) == 1 and core(n[2][0])[0] == "lam":
            lam = core(n[2][0])
            body = core(lam[3])
            if is_const(body, "Membership.mem") and body[2][1] == ["var", lam[1], []] \
                    and lam[1] not in free_vars(body[2][0]):
                return node("TMember", self.term(body[2][0], []))
        if n[0] == "const" and n[1] == "Fin" and len(n[2]) == 1:
            k = core(n[2][0])
            if k[0] == "nat" and k[1] >= 1:
                return node("TFinUpTo", self.numeral(k[1] - 1))
            return node("TFin", self.term(k, []))
        if n[0] == "const" and n[1] in LANGUAGE and len(n[2]) == 1 and var_name(n[2][0]) in self.fams:
            return node("TLangFamily", self.fam(var_name(n[2][0])))
        if n[0] == "forall" and not n[3] and not n[4]:
            if n[5] == NAT:
                return node("TSeq", self.ty(n[6]))
            return node("TFun", self.ty(n[5]), self.ty(n[6]))
        if n[0] == "const":
            simple = {"Real": "TReal", "Int": "TInt", "Bool": "TBool"}
            if n[1] in simple and not n[2]:
                return simple[n[1]]
            one = {"Finset": "TFinset", "Set": "TSet", "Option": "TOption", "List": "TList"}
            if n[1] in one and len(n[2]) == 1:
                return node(one[n[1]], self.ty(n[2][0]))
            two = {"Equiv": "TEquiv", "Prod": "TProd", "Sum": "TSum", "Function.Embedding": "TEmbed"}
            if n[1] in two and len(n[2]) == 2:
                return node(two[n[1]], self.ty(n[2][0]), self.ty(n[2][1]))
            if not n[2]:
                return node("TLbl", self.lbl(n[1]))
            if len(n[2]) == 1 and core(n[2][0])[0] == "nat":
                return node("TLblApp", self.lbl(n[1]), self.numeral(core(n[2][0])[1]))
            if len(n[2]) == 1 and is_const(n[2][0], "HAdd.hAdd") and self.is_var(core(n[2][0])[2][0]) \
                    and core(core(n[2][0])[2][1])[0] == "nat":
                d, k = core(n[2][0])[2]
                return node("TLblAppPlus", self.lbl(n[1]), self.var(var_name(d)), self.numeral(core(k)[1]))
            return node("TLblOver", self.lbl(n[1]), chain("OneTy", "MoreTy", [self.ty(a) for a in n[2]]))
        raise ValueError(f"Unsupported binder type {n}")

    def pred(self, body):
        """∀ i n, ∃ c, n ≤ |c| ∧ subject ++ c ∈ L_i: arbitrarily long extensions in every L_i."""
        b = core(body)
        try:
            _, i, _, _, _, d1, b1 = b
            _, n, _, _, _, d2, b2 = core(b1)
            _, c, _, _, conj = core(b2)
            le, mem = core(conj)[1:]
            ok = (b[0] == "forall" and d1 == NAT and d2 == NAT and core(b2)[0] == "exists"
                  and core(conj)[0] == "and" and is_const(le, "LE.le") and core(le)[2] == [["var", n, []],
                  ["const", "List.length", [["var", c, []]]]] and is_const(mem, "Membership.mem")
                  and is_const(core(mem)[2][0], *LANGUAGE) and core(core(mem)[2][0])[2][1] == ["var", i, []]
                  and core(mem)[2][1] == ["const", "HAppend.hAppend", [["var", "subject", []], ["var", c, []]]])
        except (ValueError, IndexError, TypeError):
            ok = False
        if not ok:
            raise ValueError(f"No predicate construction for {body}")
        return node("LongExtensions", self.fam(var_name(core(core(mem)[2][0])[2][0])))

    # ---------- propositions ----------
    def prop(self, n, scope):
        n = core(n)
        t = n[0]
        if t == "forall" and n[3] and not n[4]:
            return node("Imp", self.prop(n[5], scope), self.prop(n[6], scope))
        if t == "forall" and not n[3]:
            _, x, _, _, _, dom, body = n
            inner = scope + [(x, "var")]
            b = core(body)
            if b[0] == "forall" and b[3] and not b[4]:
                h = core(b[5])
                if is_const(h, "LE.le") and h[2][1] == ["var", x, []] and dom == NAT:
                    return node("ForallAtLeast", self.var(x), self.term(h[2][0], scope), self.prop(b[6], inner))
                if is_const(h, "Membership.mem") and h[2][1] == ["var", x, []]:
                    return node("ForallIn", self.var(x), self.term(h[2][0], scope), self.prop(b[6], inner))
                if below(h, x) and dom == NAT:
                    return node("ForallBelow", self.var(x), self.term(core(h)[2][1], scope), self.prop(b[6], inner))
            group, inner_body = [x], body
            while core(inner_body)[0] == "forall" and not core(inner_body)[3] and core(inner_body)[5] == dom:
                group.append(core(inner_body)[1])
                inner_body = core(inner_body)[6]
            if len(group) > 1:
                return node("ForallMany", name_list([node("RVar", self.var(g)) for g in group]), self.ty(dom),
                            self.prop(inner_body, scope + [(g, "var") for g in group]))
            return node("ForallOne", self.var(x), self.ty(dom), self.prop(body, inner))
        if t == "exists" and not n[2]:
            _, x, _, dom, body = n
            inner = scope + [(x, "var")]
            b = core(body)
            if b[0] == "and" and is_const(b[1], "Membership.mem") and core(b[1])[2][1] == ["var", x, []]:
                return node("ExistsIn", self.var(x), self.term(core(b[1])[2][0], scope), self.prop(b[2], inner))
            if b[0] == "and" and is_const(b[1], "GE.ge") and core(b[1])[2][0] == ["var", x, []] and dom == NAT:
                return node("ExistsGe", self.var(x), self.term(core(b[1])[2][1], scope), self.prop(b[2], inner))
            if b[0] == "and" and below(b[1], x) and dom == NAT:
                return node("ExistsBelow", self.var(x), self.term(core(b[1])[2][1], scope), self.prop(b[2], inner))
            return node("ExistsSuch", self.var(x), self.ty(dom), self.prop(body, inner))
        if t == "and":
            if self.member_pair(n[1], n[2]):
                p, q = core(n[1]), core(core(n[2])[1])
                return node("Mem", self.term(p[2][1], scope),
                            node("Diff", self.term(p[2][0], scope), self.term(q[2][0], scope)))
            return node("And", self.prop(n[1], scope), self.prop(n[2], scope))
        if t == "or":
            return node("Or", self.prop(n[1], scope), self.prop(n[2], scope))
        if t == "iff":
            return node("Iff", self.prop(n[1], scope), self.prop(n[2], scope))
        if t == "not":
            m = core(n[1])
            if is_const(m, "Membership.mem"):
                return node("NotMem", self.term(m[2][1], scope), self.term(m[2][0], scope))
            if m[0] == "exists" and not m[2]:
                return node("NoneSuch", self.var(m[1]), self.ty(m[3]), self.prop(m[4], scope + [(m[1], "var")]))
            if m[0] == "const" and len(m[2]) == 1 and m[1] not in RELATIONS and not self.special(m):
                return node("IsNotLbl", self.term(m[2][0], scope), self.lbl(m[1]))
            inner = self.prop(m, scope)
            # "X is not *label* for Y" when the label has a frame with a copula.
            framed = {tag("s_", c): c for c in self.frames}
            head = inner[1:].split(" ", 1)[0]
            if head in framed and frame_negation(FRAMES[label_constant(framed[head])[0]]):
                self.negated.add(framed[head])
                return "(sn_" + inner[len("(s_"):]
            # "*label*(X, Y) does not hold", "P(X) does not hold" and "A ⊈ B" for the commonest negations.
            for holds, fails in (("LblHolds", "LblFails"), ("VarHolds", "VarFails"), ("Sub", "NotSub")):
                if inner.startswith(f"({holds} "):
                    return f"({fails} " + inner[len(holds) + 2:]
            return node("Not", inner)
        if t == "var":
            if n[1] in self.adjectives and len(n[2]) == 1:
                return node("Holds", self.term(n[2][0], scope), self.var(n[1]))
            if not n[2]:
                return node("VarProp", self.var(n[1]))
            return node("VarHolds", self.var(n[1]), self.args(n[2], scope))
        if t == "const":
            c, args = n[1], n[2]
            if c == "Membership.mem":
                return node("Mem", self.term(args[1], scope), self.term(args[0], scope))
            if c == "HasSubset.Subset" and is_const(args[0], "Set.range") and self.is_var(core(args[0])[2][0]):
                return node("ValuesIn", self.var(var_name(core(args[0])[2][0])), self.term(args[1], scope))
            if c == "HasSubset.Subset":
                return node("Sub", self.term(args[0], scope), self.term(args[1], scope))
            if c == "Function.Injective" and self.is_var(args[0]):
                return node("Injective", self.var(var_name(args[0])))
            if c == "LE.le" and is_const(args[1], "Finset.card"):
                return node("CardAtLeast", self.term(core(args[1])[2][0], scope), self.term(args[0], scope))
            if c == "LE.le" and is_const(args[1], "List.length"):
                return node("LengthAtLeast", self.term(core(args[1])[2][0], scope), self.term(args[0], scope))
            if c == "List.IsPrefix":
                return node("IsPrefix", self.term(args[0], scope), self.term(args[1], scope))
            if c == "Eq" and is_const(args[0], "Set.range") and self.is_var(core(args[0])[2][0]):
                return node("ValuesExactly", self.var(var_name(core(args[0])[2][0])), self.term(args[1], scope))
            if c == "Eq" and is_const(args[0], *QUERY) and is_const(args[1], "Bool.true"):
                o, i, x = core(args[0])[2]
                return node("Confirms", self.fam(var_name(o)), self.term(x, scope), self.var(var_name(i)))
            if c in RELATIONS and len(args) == 2:
                return node(RELATIONS[c], self.term(args[0], scope), self.term(args[1], scope))
            if c in ("Filter.Frequently", "Filter.Eventually") and len(args) == 2 \
                    and is_const(args[1], "Filter.atTop") and core(args[0])[0] == "lam" and core(args[0])[2] == NAT:
                lam = core(args[0])
                return node("Frequently" if c == "Filter.Frequently" else "Eventually", self.var(lam[1]),
                            self.prop(lam[3], scope + [(lam[1], "var")]))
            if not args:
                return node("LblProp", self.lbl(c))
            if len(args) == 1:
                return node("IsLbl", self.term(args[0], scope), self.lbl(c))
            frame = FRAMES.get(label_constant(c)[0])
            if frame and frame_arity(frame) == len(args):
                self.lbl(c)
                self.frames.add(c)
                return node(tag("s_", c), *self.arg_terms(args, scope))
            return node("LblHolds", self.lbl(c), self.args(args, scope))
        raise NotInline(f"No inline construction for {n}")

    @staticmethod
    def is_var(n):
        n = core(n)
        return n[0] == "var" and not n[2]

    @staticmethod
    def special(m):
        return m[1] in ("Function.Injective", "Set.range")

    def args(self, xs, scope):
        return chain("OneArg", "MoreArgs", self.arg_terms(xs, scope))

    def arg_terms(self, xs, scope):
        # A finite set passed where a set is expected keeps its coercion: Lean may not infer it there.
        return [node("FinsetSet", self.term(core(a)[2][0], scope)) if is_const(a, "Finset.toSet") and len(core(a)[2]) == 1
                else self.term(a, scope) for a in xs]

    # ---------- terms ----------
    def term(self, n, scope):
        n = core(n)
        names = {s[0] for s in scope}
        kinds = dict(scope)
        if n[0] == "nat":
            return node("NumT", self.numeral(n[1]))
        if n[0] == "var":
            if not n[2]:
                if kinds.get(n[1]) in ("fam", "letfam"):
                    return node("FamT", self.fam(n[1]))
                return node("V", self.var(n[1]))
            return node("Call", self.var(n[1]), self.args(n[2], scope))
        if n[0] == "lam":
            _, x, _, body, is_prop = n
            inner = scope + [(x, "var")]
            if is_prop:
                return node("LamP", self.var(x), self.prop(body, inner))
            if x not in free_vars(body) or only_coerced(x, body):
                return node("LamTy", self.var(x), self.ty(n[2]), self.term(body, inner))
            return node("Lam", self.var(x), self.term(body, inner))
        if n[0] == "const":
            c, args = n[1], n[2]
            if c in LANGUAGE and len(args) == 2:
                return node("Lang", self.fam(var_name(args[0])), self.var(var_name(args[1])))
            if c in LANGUAGE and len(args) == 1 and dict(scope).get(var_name(args[0])) in ("fam", "letfam"):
                return node("LangFamily", self.fam(var_name(args[0])))
            if c in OPERATORS and len(args) == 2:
                # A finite set on the left of ∪, ∩ or ∖ keeps its coercion: Lean elaborates that side first.
                left = (node("FinsetSet", self.term(core(args[0])[2][0], scope))
                        if is_const(args[0], "Finset.toSet") and len(core(args[0])[2]) == 1 else self.term(args[0], scope))
                return node(OPERATORS[c], left, self.term(args[1], scope))
            if c == "Neg.neg" and len(args) == 1:
                return node("Neg", self.term(args[0], scope))
            if c == "Nat.cast" and len(args) == 1:
                return node("Cast", self.term(args[0], scope))
            if c == "Finset.toSet":
                return self.term(args[0], scope)
            if c == "Prod.mk" and len(args) == 2:
                return node("Pair", self.term(args[0], scope), self.term(args[1], scope))
            if c in ("Unit.unit", "PUnit.unit") and not args:
                return "UnitT"
            if c == "List.nil" and not args:
                return "ListNil"
            if c == "List.cons" and len(args) == 2:
                items, rest = [], n
                while is_const(rest, "List.cons") and len(core(rest)[2]) == 2:
                    items.append(core(rest)[2][0])
                    rest = core(rest)[2][1]
                if is_const(rest, "List.nil") and not core(rest)[2]:
                    return node("ListOf", self.args(items, scope))
            if c == "Subtype.mk" and len(args) == 2:
                return node("Elem", self.term(args[0], scope))
            if c == "Subtype.val" and len(args) == 1:
                return node("Cast", self.term(args[0], scope))
            if c in SAMPLES:
                dummy = next(d for d in "nmk" if d not in names)
                return node("FirstTerms", self.var(dummy), self.var(var_name(args[0])), self.var(var_name(args[1])))
            if c == "setOf" and args[0][0] == "lam":
                _, x, dom, body = args[0][:4]
                inner = scope + [(x, "var")]
                b = core(body)
                if b[0] == "and" and core(b[1])[0] == "not" and is_const(core(b[1])[1], "Membership.mem") \
                        and core(core(b[1])[1])[2][1] == ["var", x, []]:
                    outside = core(core(b[1])[1])[2][0]
                    return node("SetOfOutside", self.var(x), self.ty(dom), self.term(outside, scope),
                                self.prop(b[2], inner))
                return node("SetOfTy", self.var(x), self.ty(dom), self.prop(body, inner))
            if c == "Finset.filter" and args[0][0] == "lam":
                _, i, _, body = args[0][:4]
                return node("FilterSet", self.var(i), self.term(args[1], scope), self.prop(body, scope + [(i, "var")]))
            if not args:
                return node("LblT", self.lbl(c))
            return node("LblApp", self.lbl(c), self.args(args, scope))
        raise NotInline(f"No term construction for {n}")


PARAMETER = re.compile(r"[A-Za-z][A-Za-z0-9_']*")


def hide_proofs(n):
    """Proof arguments, marked ["proof", parameter, tree] by the exporter. A label application leaves
    its proof arguments to Lean: they are not shown. A proof that is a hypothesis in scope stands for
    `c (h := by assumption)`, written "c#h"; another proof, when the exporter found that the tactic
    proves it, for `c (h := by TACTIC)`, written "c#h!" (see `label_constant`); the rest are shown. Proofs do not change a statement's meaning (proof irrelevance), and the
    kernel checks the result. A label with no other explicit argument shows its proofs as before."""
    if not isinstance(n, list):
        return n
    if is_node(n) and n[0] == "const" and any(is_node(a) and a[0] == "proof" for a in n[2]):
        hidden, args = [], []
        for a in n[2]:
            if is_node(a) and a[0] == "proof":
                param, proof, provable = a[1], a[2], len(a) > 3 and a[3]
                simple = proof[0] == "var" and not proof[2]
                if n[1] not in SPECIAL and n[1] not in WORDS and PARAMETER.fullmatch(param) and (simple or provable):
                    hidden.append((param if simple else param + "!",
                                   (proof[1],) if simple else tuple(sorted(free_vars(strip_proofs(proof))))))
                    continue
                a = proof
            args.append(hide_proofs(a))
        if not args:   # keep the label applied, so that its Lean form stays in one application
            return ["const", n[1], [hide_proofs(a[2] if is_node(a) and a[0] == "proof" else a) for a in n[2]], *n[3:]]
        # The fourth element (a tuple, which no traversal enters) lists the variables the proofs use,
        # so that the term is placed after them.
        return ["const", "#".join([n[1], *(p for p, _ in hidden)]), args, tuple(h for _, hs in hidden for h in hs)]
    if is_node(n) and n[0] == "proof":
        return hide_proofs(n[2])
    return [hide_proofs(c) if isinstance(c, list) else c for c in n]


def strip_proofs(n):
    """A tree without the ["proof", parameter, tree] marks of the exporter."""
    if is_node(n) and n[0] == "proof":
        return strip_proofs(n[2])
    return [strip_proofs(c) if isinstance(c, list) else c for c in n] if isinstance(n, list) else n


def label_constant(key):
    """(constant, hidden proof parameters) of a label key "c" or "c#h1#h2"; a parameter "h!" is proved by a tactic."""
    c, *hidden = key.split("#")
    return c, hidden


def paper_names(exports, paper=None):
    """Names bound anywhere in a paper's readings, after renaming. A new name avoids them, so one
    letter does not mean two things on one page."""
    out = set()
    for e in exports:
        out |= visible_names(e) | free_vars(e)
    renaming = {**RENAMING, **PAPER_RENAMING.get(paper, {})}
    return out | {new for old, new in renaming.items() if old in out} | set(PREFERRED.get(paper, {}).values())


def select(exported, avoid=frozenset(), defines=None, paper=None):
    exported = hide_proofs(exported)
    prefer = PREFERRED.get(paper, {})
    names = visible_names(exported) | free_vars(exported)
    # Renaming x → y also renames the fresh copies x_1, x_2, … that Lean made of x, to y_1, y_2, ….
    pairs = [(o, n) for old, new in {**RENAMING, **PAPER_RENAMING.get(paper, {})}.items() for o, n in [(old, new)] +
             [(m, new + m[len(old):]) for m in sorted(names) if re.fullmatch(re.escape(old) + r"_[0-9]+", m)]]
    for old, new in pairs:
        if old in names:
            if new in names or new in RESERVED:
                continue   # the display name is taken in this statement: keep the Lean name
            exported = rename(exported, old, new)
            names = (names - {old}) | {new}
    # Name repeated terms one at a time, keeping a name only if the reading can still be selected.
    named = []
    while True:
        root, lifted = name_terms(exported, named, avoid, prefer)
        for a in candidates(root, lifted):
            try:
                attempt(exported, named + [a], avoid, defines, prefer)
            except Exception:
                continue
            named.append(a)
            break
        else:
            return attempt(exported, named, avoid, defines, prefer)


def attempt(exported, named, avoid, defines=None, prefer={}):
    """Select a tree with the named terms. A named term used as a family of languages is
    introduced as a family, so that no name is both a variable and a family."""
    tree, s = attempt_once(exported, named, avoid, defines, frozenset(), prefer)
    both = set(s.vars) & set(s.fams)
    if both:
        tree, s = attempt_once(exported, named, avoid, defines, frozenset(both), prefer)
        if set(s.vars) & set(s.fams):
            raise ValueError(f"Names used both as variables and as families: {sorted(set(s.vars) & set(s.fams))}")
    return tree, s


def short_name(term, taken, avoid, prefer={}):
    preferred = prefer.get(label_constant(term[1])[0])
    if preferred and preferred not in taken:
        return preferred
    first = label_words(term[1]).split()[0][:1].upper()
    options = [c for c in [first, *"KMNQRUVWYZ"] if c and c not in taken and c not in RESERVED]
    return next((c for c in options if c not in avoid), options[0])


def name_terms(exported, named, avoid, prefer={}):
    """Replace each term in `named` (in order) by a new variable. Each term is written with the
    variables of the terms named before it; a later, smaller term is also replaced inside them."""
    taken = binder_names(exported) | free_vars(exported)
    root, lifted = exported, []
    for a in named:
        name = short_name(a, taken, avoid, prefer)
        taken.add(name)
        var = ["var", name, []]
        root = substitute(root, a, var)
        for d in lifted:
            d["value"] = substitute(d["value"], a, var)
            d["free"] = free_vars(d["value"])
        lifted.append({"name": name, "kind": "term", "value": a, "free": free_vars(a)})
    return root, lifted


def attempt_once(exported, named, avoid, defines, families, prefer={}):
    """Select a tree, introducing each named term by "Let K = …" as soon as its variables are in scope."""
    s = Selector()
    s.defines = defines
    root, s.definitions = name_terms(exported, named, avoid, prefer)
    for d in s.definitions:
        d["family"] = d["name"] in families
    root, s.fresh = s.name_subterms(root)
    tree = node("Reading", s.outline(root, []))
    if s.definitions:
        raise ValueError(f"Definitions never introduced: {[d['name'] for d in s.definitions]}")
    return tree[1:-1], s
