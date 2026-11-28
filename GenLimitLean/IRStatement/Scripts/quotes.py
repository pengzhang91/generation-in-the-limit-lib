"""Paper quotations for the web pages: fetch the sources, check every quotation, render it.

Each paper has PaperStatements/Pxx.json:

    {
      "edition": "<registry edition id>",
      "pdf": "<URL of the registered PDF>",            "pdf_sha256": "<hex>",
      "source": "<URL of the LaTeX source, optional>", "source_sha256": "<hex>",
      "preamble": ["\\newcommand{\\cL}{\\mathcal{L}}", …],   macro definitions copied from the source
      "preamble_extra": [{"tex": "…", "why": "…"}, …],      only for rendering, e.g. dropping \\xspace
      "refs": {"<label or cite key>": "<printed text>", …},  how \\ref and \\cite appear in print
      "setting": [quote, …],                                optional
      "declarations": {
        "<full Lean name>": {"item": "Theorem 3.3" | null, "quotes": [quote, …],
                             "terms": [quote, …], "notes": ["…"]}       terms and notes optional
      },
      "unavailable": "<why the paper is not quoted>"         instead of everything above
    }

A scanned paper with no LaTeX source (P00, P00A) also has:

      "supplied": "<why>"          the PDF was placed in the cache by hand; it is never downloaded
      "transcribed": "<why>"       tex quotes are transcribed from the scan, not copied from a source
      "ocr_fixes": [{"page": n, "pdf": "<text layer>", "reads": "<as printed>", "why": "…"}, …]

A quote is {"page": n, "tex": "<LaTeX copied from the source>"} or {"page": n, "text": "<Unicode
text copied from the PDF; L_1 marks a subscript>"}. Pages are PDF pages, starting at 1.

Checks (`check`), all against the downloaded files:
- the PDF and source have the recorded SHA-256;
- a "text" quote occurs in the text of page n or n+1, ignoring spacing, and begins on page n; a word
  hyphenated at a line break may be quoted whole;
- a "tex" quote occurs in the source, ignoring spacing and comments, and its prose (everything
  outside formulas and commands) occurs, letter by letter, on page n or n+1 of the PDF, beginning on page n;
  a statement that is only a formula has no prose, and is placed by its item number alone;
- a numbered item ("Theorem 3.3") is printed on page n−1, n or n+1;
- every preamble line occurs in the source, every \\ref has an entry in refs, and pandoc
  renders the quote without skipping anything.
For a transcribed paper, a tex quote's prose is checked against the PDF's text layer as above, after
the listed OCR fixes; each fix must match the text layer of its page and give a reason. The formulas
of a transcribed quote are checked against nothing; the page says so.
"""
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import unicodedata
import urllib.request

BASE = Path(__file__).resolve().parents[1]  # the IRStatement folder
STATEMENTS = BASE / "PaperStatements"
CACHE = BASE / "local" / "papers"
ITEM = re.compile(r"(Theorem|Lemma|Corollary|Proposition|Claim|Definition|Remark|Example|Fact|Observation)"
                  r"\s+([A-Z]?[0-9]+(?:\.[0-9]+)*|[A-Z](?:\.[0-9]+)+|[IVX]+\.[0-9]+)")
MATH = [r"\$\$.*?\$\$", r"\\\[.*?\\\]", r"\\\(.*?\\\)",
        r"\\begin\{(equation|align|gather|multline|eqnarray|displaymath|math|split|alignat)(\*?)\}.*?\\end\{\1\2\}",
        r"(?<!\\)\$.*?(?<!\\)\$"]
DROP = r"\\(?:cite[a-z]*|[cC]?ref|eqref|autoref|nameref|label|footnote|url|href)\*?(?:\[[^\]]*\])*\{[^{}]*\}"
SKIP_OK = re.compile(r"Skipped '\[")           # optional arguments, such as enumerate labels
RAW_OK = re.compile(r"Not rendering RawInline \(Format \"latex\"\) \"\\\\cite")
SUBSCRIPT = re.compile(r"(?<!\w)([^\W\d_])_([^\W_]+)")   # L_1, t_C, 𝒞_1: one letter, then the subscript


def load(key):
    path = STATEMENTS / f"P{key}.json"
    return json.loads(path.read_text()) if path.exists() else None


# ---------- files ----------

def sha(data):
    return hashlib.sha256(data).hexdigest()


def download(url, path):
    request = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (paper-statement checker)"})
    with urllib.request.urlopen(request, timeout=120) as response:
        data = response.read()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return data


def unpack(data, folder):
    """Unpack an arXiv e-print (gzipped tar or a gzipped single file) into folder."""
    if folder.exists():
        shutil.rmtree(folder)
    folder.mkdir(parents=True)
    raw = gzip.decompress(data) if data[:2] == b"\x1f\x8b" else data
    try:
        with tarfile.open(fileobj=io.BytesIO(raw)) as tar:
            tar.extractall(folder, filter="data")
    except tarfile.ReadError:
        (folder / "main.tex").write_bytes(raw)


def fetch(key, paper, cache=CACHE):
    """Download the PDF and the source of one paper into cache/Pxx, unless present."""
    folder = cache / f"P{key}"
    pdf = folder / "paper.pdf"
    if paper.get("supplied"):
        return folder
    if not pdf.exists():
        download(paper["pdf"], pdf)
    if paper.get("source"):
        archive = folder / "source.bin"
        data = archive.read_bytes() if archive.exists() else download(paper["source"], archive)
        if not (folder / "source").exists():
            unpack(data, folder / "source")
    return folder


# ---------- normal forms ----------

def plain(text):
    text = unicodedata.normalize("NFKD", unicodedata.normalize("NFKC", text))
    return "".join(c for c in text if not unicodedata.combining(c))


def letters(text):
    return re.sub(r"[^a-z]", "", plain(text).lower())


def spaceless(text):
    return re.sub(r"\s+", "", unicodedata.normalize("NFKC", text)).replace("_", "")


def uncomment(tex):
    return re.sub(r"(?<!\\)%[^\n]*", "", tex)


def prose(tex):
    """The prose pieces of a LaTeX quote: formulas, commands and references removed."""
    tex = uncomment(tex)
    for pattern in MATH:
        tex = re.sub(pattern, "\0", tex, flags=re.S)
    tex = re.sub(DROP, "\0", tex)
    tex = re.sub(r"\\(?:begin|end)\{[^{}]*\}(?:\[[^\]]*\])?|\\item(?:\[[^\]]*\])?", "\0", tex)
    tex = re.sub(r"\\[A-Za-z@]+\*?|\\.", "\0", tex)
    return [p for p in (letters(piece) for piece in tex.split("\0")) if len(p) >= 12]


class Paper:
    """The downloaded files of one paper, with their normal forms."""

    def __init__(self, key, paper, cache=CACHE):
        import pypdf
        self.key, self.paper, self.folder = key, paper, cache / f"P{key}"
        self.pdf_bytes = (self.folder / "paper.pdf").read_bytes()
        pages = [p.extract_text() or "" for p in pypdf.PdfReader(io.BytesIO(self.pdf_bytes)).pages]
        self.fix_problems = []
        for fix in paper.get("ocr_fixes", []):
            n, wrong = fix["page"], fix["pdf"]
            if not fix.get("why"):
                self.fix_problems.append(f"OCR fix needs a reason: {wrong[:40]}")
            if not 1 <= n <= len(pages) or wrong not in pages[n - 1]:
                self.fix_problems.append(f"OCR fix not in the text layer of page {n}: {wrong[:40]}")
            else:
                pages[n - 1] = pages[n - 1].replace(wrong, fix["reads"])
        self.pages = pages
        self.page_letters = [letters(p) for p in pages]
        self.page_spaceless = [spaceless(p) for p in pages]
        # The same text with words joined across a hyphenated line break ("con-\nstant" → "constant").
        self.page_joined = [spaceless(re.sub(r"-[ \t]*\n", "", p)) for p in pages]
        self.page_items = [spaceless(plain(p)).lower() for p in pages]
        self.source = ""
        if paper.get("source"):
            files = sorted(f for f in (self.folder / "source").rglob("*")
                           if f.suffix in {".tex", ".sty", ".def", ".macros", ".bbl"})
            self.source = spaceless(uncomment("\n".join(f.read_text(errors="replace") for f in files)))

    def near(self, table, page, before=0):
        return "".join(table[max(page - 1 - before, 0):page + 1])


# ---------- rendering ----------

def typeset(text):
    """Unicode text with L_1 subscripts, t∗ superscripts and *italic* labels, escaped for HTML."""
    from html import escape
    html = SUBSCRIPT.sub(r"\1<sub>\2</sub>", escape(text, quote=False))
    html = re.sub(r"(?<=[^\W\d_])([∗⋆])", r'<sup class="star">\1</sup>', html)
    return re.sub(r"\*([^*\n]+)\*", r"<em>\1</em>", html)


LIST = re.compile(r"\\(begin|end)\{(enumerate|itemize|description)\}(\[(?:[^\[\]]|\[[^\]]*\])*\])?"
                  r"|\\item\b\s*(\[(?:[^\[\]]|\[[^\]]*\])*\])?")


def roman(n):
    out = ""
    for value, digits in ((10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")):
        while n >= value:
            out, n = out + digits, n - value
    return out


def counter(template, k):
    """The printed label of item k (from 1) for an enumerate label template such as (\\roman*) or (a)."""
    forms = {r"\roman*": roman(k), r"\Roman*": roman(k).upper(), r"\alph*": chr(96 + k),
             r"\Alph*": chr(64 + k), r"\arabic*": str(k)}
    for key, value in forms.items():
        if key in template:
            return template.replace(key, value)
    m = re.search(r"[aAiI1]", template)   # enumerate-package short form, e.g. [(a)] or [i.]
    if not m:
        return template
    c = m[0]
    value = {"a": chr(96 + k), "A": chr(64 + k), "i": roman(k), "I": roman(k).upper(), "1": str(k)}[c]
    return template[:m.start()] + value + template[m.end():]


def labelled_lists(tex):
    """Make printed item labels explicit for pandoc, which drops \\item[...] and enumerate label options.
    Rendering only: the quotation and its checks are unchanged."""
    out, stack, last = [], [], 0
    for m in LIST.finditer(tex):
        out.append(tex[last:m.start()])
        last = m.end()
        if m[1] == "begin":
            option = (m[3] or "")[1:-1]
            template = None
            if m[2] == "enumerate" and option:
                lab = re.search(r"label\s*=\s*(\{[^{}]*\}|[^,]+)", option)
                template = (lab[1].strip().strip("{}") if lab else option if "=" not in option else None)
            stack.append([m[2], template, 0])
            out.append(f"\\begin{{{m[2]}}}")
        elif m[1] == "end":
            if stack:
                stack.pop()
            out.append(m[0])
        else:
            explicit = m[4][1:-1] if m[4] else None
            if stack:
                stack[-1][2] += 1
            label = explicit
            if label is None and stack and stack[-1][1]:
                label = counter(stack[-1][1], stack[-1][2])
            out.append(f"\\item {{}}ITEMLABEL{label}ENDLABEL " if label is not None else m[0] + " ")
    out.append(tex[last:])
    return "".join(out)


def pandoc(paper, tex):
    """LaTeX → HTML with MathML. Returns (html, problems)."""
    preamble = paper.get("preamble", []) + [e["tex"] for e in paper.get("preamble_extra", [])]
    source = "\n".join(preamble) + "\n\n" + labelled_lists(tex)
    result = subprocess.run(["pandoc", "--verbose", "-f", "latex", "-t", "html", "--mathml", "--wrap=none"],
                            input=source, capture_output=True, text=True)
    problems = [line for line in result.stderr.splitlines()
                if ("Skipped" in line and not SKIP_OK.search(line))
                or "Could not" in line or ("Not rendering" in line and not RAW_OK.search(line))
                or "[WARNING]" in line or "[ERROR]" in line]
    if result.returncode:
        problems.append(result.stderr.strip()[:300])
    html = result.stdout
    refs = paper.get("refs", {})

    def cite(m):
        keys = m[1].split()
        return "[" + "; ".join(refs.get(k, k) for k in keys) + "]"

    def ref(m):
        label, kind = m[2], m[1]
        if label not in refs:
            problems.append(f"no entry in refs for \\ref{{{label}}}")
            return "??"
        return f"({refs[label]})" if kind == "eqref" else refs[label]

    html = re.sub(r'<span class="citation" data-cites="([^"]*)">.*?</span>', cite, html, flags=re.S)
    html = re.sub(r'<a href="#[^"]*" data-reference-type="([^"]+)"\s+data-reference="([^"]*)">.*?</a>',
                  ref, html, flags=re.S)
    html = re.sub(r'<a href="#fn[0-9]+" class="footnote-ref"[^>]*>(.*?)</a>', r"\1", html, flags=re.S)
    html = re.sub(r'<a href="#fnref[0-9]+" class="footnote-back"[^>]*>.*?</a>', "", html, flags=re.S)
    html = re.sub(r'\s(?:id|label)="[^"]*"', "", html)
    html = re.sub(r"ITEMLABEL(.*?)ENDLABEL", r'<span class="item-label">\1</span>', html, flags=re.S)
    if "ITEMLABEL" in html or "ENDLABEL" in html:
        problems.append("an item label did not survive pandoc")
    html = re.sub(r"<annotation encoding=\"application/x-tex\">.*?</annotation>", "", html, flags=re.S)
    return html.strip(), problems


def render(paper, quote):
    if "tex" in quote:
        html, problems = pandoc(paper, quote["tex"])
        if problems:
            raise ValueError("pandoc: " + "; ".join(problems))
        return html
    return "<p>" + typeset(quote["text"]) + "</p>"


# ---------- checks ----------

def check_quote(files, quote, item=None):
    """Problems with one quotation; an empty list means it passed."""
    out, page = [], quote["page"]
    if not 1 <= page <= len(files.pages):
        return [f"page {page} is outside the PDF"]
    if "text" in quote:
        text = spaceless(quote["text"])
        tables = (files.page_spaceless, files.page_joined)
        if not any(text in files.near(table, page) for table in tables):
            out.append(f"text not found on page {page} or {page + 1}")
        elif not any(text[:40] in table[page - 1] for table in tables):
            out.append(f"the text does not begin on page {page}")
    else:
        tex = quote["tex"]
        if not files.source:
            if not files.paper.get("transcribed"):
                out.append("a tex quote needs the paper's source")
        elif spaceless(uncomment(tex)) not in files.source:
            out.append("tex not found in the source")
        text = files.near(files.page_letters, page)
        missing = [p for p in prose(tex) if p not in text]
        if missing:
            out.append(f"prose not found on page {page} or {page + 1}: {missing[0][:60]}")
        if not prose(tex):
            # A statement that is only a formula: the numbered item, printed nearby, places it.
            if not (item and ITEM.fullmatch(item) and files.source):
                out.append("the quote has no prose to compare with the PDF")
        elif not missing and prose(tex)[0] not in files.page_letters[page - 1]:
            out.append(f"the quote does not begin on page {page}")
        _, problems = pandoc(files.paper, tex)
        out += problems
    if item and ITEM.fullmatch(item):
        label = spaceless(plain(item)).lower()
        if not re.search(re.escape(label) + r"(?![0-9])", files.near(files.page_items, page, before=1)):
            out.append(f"{item} is not printed on pages {page - 1}–{page + 1}")
    return out


def check(key, paper, names, cache=CACHE):
    """Check one paper's quotations against its files. Returns a list of problems."""
    if paper.get("unavailable"):
        return []
    files = Paper(key, paper, cache)
    out = list(files.fix_problems)
    if sha(files.pdf_bytes) != paper.get("pdf_sha256"):
        out.append(f"PDF SHA-256 is {sha(files.pdf_bytes)}, not the recorded one")
    if paper.get("source"):
        data = (files.folder / "source.bin").read_bytes()
        if sha(data) != paper.get("source_sha256"):
            out.append(f"source SHA-256 is {sha(data)}, not the recorded one")
    for line in paper.get("preamble", []):
        if spaceless(uncomment(line)) not in files.source:
            out.append(f"preamble line not in the source: {line[:60]}")
    out += [f"preamble_extra needs a reason: {e.get('tex', '')[:60]}"
            for e in paper.get("preamble_extra", []) if not e.get("why")]
    for q in paper.get("setting", []):
        out += [f"setting: {p}" for p in check_quote(files, q)]
    decls = paper.get("declarations", {})
    for name in names:
        if name not in decls:
            out.append(f"{name}: no entry")
            continue
        d = decls[name]
        if d.get("item") and not d.get("quotes"):
            out.append(f"{name}: {d['item']} has no quote")
        for q in d.get("quotes", []):
            out += [f"{name}: {p}" for p in check_quote(files, q, d.get("item"))]
        for q in d.get("terms", []):
            out += [f"{name} (term): {p}" for p in check_quote(files, q)]
    out += [f"{n}: not a declaration of this paper's readings" for n in decls if n not in names]
    return out
