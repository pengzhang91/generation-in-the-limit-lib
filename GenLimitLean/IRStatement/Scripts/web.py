"""Build the web pages: each Overview declaration in the paper, as an IR statement, and in Lean.

Every page is built from files on disk:
- the saved readings (Readings/Pxx.md). The check log Readings/RUN-LOG.md
  must record a pass for exactly that file (its SHA-256), so no unchecked reading is shown;
- PaperStatements/Pxx.json, verbatim quotations from the paper. They are checked against the
  downloaded PDF and LaTeX source on every build (see quotes.py), so no unchecked quotation is shown;
- Results/Overview.lean for the Lean statements and docstrings, and the registry for titles.

Usage, from the repository root:
    python3 GenLimitLean/IRStatement/Scripts/web.py --fetch       # all papers
    python3 GenLimitLean/IRStatement/Scripts/web.py --papers 05   # one page
--fetch downloads missing papers into local/papers (arXiv and PMLR). A paper marked "supplied" (P00, P00A,
P26, P27) is never fetched: its PDF is copied by hand to local/papers/Pxx/paper.pdf.
"""
import argparse
import hashlib
from html import escape
import json
import os
from pathlib import Path
import re
from string import Template
import subprocess
import sys

sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parents[1]  # the IRStatement folder
sys.path.insert(0, str(Path(__file__).resolve().parent))
import quotes
import throughout
import unfolding

ROOT = BASE.parents[1]
WEB = BASE / "Web"
LOGS = [BASE / "Readings" / "RUN-LOG.md"]
REPOSITORY_URL = "https://github.com/pengzhang91/generation-in-the-limit-lib"
REFERENCE = re.compile(r"\[Lean declaration\]\(([^)#]+)#L(\d+)\) · `([^`]+)`")
NUMBER = re.compile(r"(?:Corrected )?(?:theorem|Theorem|Lemma|Corollary|Proposition|Claim)\s+([A-Z]?[0-9]+(?:\.[0-9]+)*|[A-Z]\.[0-9]+)\b\s*(.*)")


def keys():
    found = [p.stem[1:] for p in (BASE / "Readings").glob("P*.md")]
    return sorted(set(found), key=lambda k: (int(k[:2]), k))


def page_path(key):
    return BASE / "Readings" / f"P{key}.md"


# ---------- inputs ----------

def sections(text):
    """(heading, declaration, body, link, line, shown, setting) for each reading, the label table,
    [(declaration, why)] for the declarations without a checked reading, and {letter: setting text}.
    The body is the full text that was checked; shown is the text on the page, which may begin
    with the mark of a setting."""
    text, settings = throughout.split(text)
    text, _, label_part = text.partition("\n## Labels\n")
    text, _, missing_part = text.partition("\n## Declarations without a checked reading\n")
    missing = re.findall(r"^- `([^`]+)`: (.+)$", missing_part, re.M)
    labels = dict(re.findall(r"^\| \*(.+?)\* \| `([^`]+)` \|$", label_part, re.M))
    out = []
    for part in re.split(r"^## ", text, flags=re.M)[1:]:
        heading, rest = part.split("\n\n", 1)
        body, reference = rest.rstrip().rsplit("\n\n", 1)
        m = REFERENCE.fullmatch(reference)
        if not m:
            raise ValueError(f"Missing Lean declaration for {heading}")
        full, letter = throughout.expand(body, settings)
        out.append((heading, m[3], full, m[1], int(m[2]), body, letter))
    return out, labels, missing, settings


def selector_words(const):
    """The label of a constant by the rule of the readings (selector.label_words)."""
    from selector import label_words
    return [label_words(const)]


def setting_anchor(letter):
    return f"throughout-{letter.lower()}"


def shown_reading(r):
    """The reading as shown: a leading setting mark links to the setting, and the full text is one click away."""
    if not r["setting"]:
        return reading(r["body"])
    letter = r["setting"]
    mark = f"<em>Setting {letter}.</em>"
    html = reading(r["shown"])
    if not html.startswith("<p>" + mark):
        raise ValueError(f"Unexpected rendering of the mark of Setting {letter}")
    html = html.replace(mark, f'<a class="mark" href="#{setting_anchor(letter)}">Setting {letter}.</a>', 1)
    return (f'{html}<details class="full"><summary>Full statement, with Setting {letter} in place</summary>'
            f'<div class="reading">{reading(r["body"])}</div></details>')


GLOSSARY_LOGS = [BASE / "Readings" / "Glossary" / "RUN-LOG.md"]


def def_anchor(const):
    return "def-" + re.sub(r"[^A-Za-z0-9]+", "-", const).strip("-")


def label_table(text):
    """{label: constant} from the '## Labels' table of a reading page or a glossary page."""
    part = text.partition("\n## Labels\n")[2].split("\n## ", 1)[0]
    return dict(re.findall(r"^\| \*(.+?)\* \| `([^`]+)` \|$", part, re.M))


def with_plurals(labels):
    """The labels and their plurals, as in “a set of *languages*”, each mapped to its constant."""
    from reader import plural
    out = dict(labels)
    for l, c in labels.items():
        out.setdefault(plural(l), c)
    return out


def link_labels(html, labels, defined, skip=None):
    """Each italic label links to its definition when the page has one, and its title names the Lean constant.
    `labels` maps a label to its constant; `skip` is a constant not to link (a definition's own label)."""
    by_text = {escape(l, quote=False): c for l, c in labels.items()}

    def one(m):
        c = by_text.get(m[1])
        if c is None:
            return m[0]
        if c in defined and c != skip:
            return f'<a class="label" href="#{def_anchor(c)}" title="{escape(c)}"><em>{m[1]}</em></a>'
        return f'<em title="{escape(c)}">{m[1]}</em>'
    return re.sub(r"<em>([^<]+)</em>", one, html)


def status(summary):
    """The log's summary line, split into the sidebar's count and the footer's tests."""
    m = re.fullmatch(r"P\w+: (\d+)/(\d+) readings checked(; control A rejected by the kernel)?"
                     r"(?:; \d+ without a reading)?; (\d+)/(\d+) random trees recovered", summary)
    if not m:
        raise ValueError(f"Unexpected summary line in the check log: {summary}")
    side = f"{m[1]} of {m[2]} statements checked by Lean"
    foot = (f"Ambiguity test: {m[4]} of {m[5]} random sentences made from the same rules parse back to their own "
            f"tree and to no other.")
    if m[3]:
        foot += (" Negative control: a copy of the reading of Theorem 2.2, edited so that the threshold may depend "
                 "on the sample, is rejected by the kernel.")
    return side, foot


def glossary(key):
    """[(label, constant, body, link, line)] from the paper's glossary page, if its log records a pass
    for the page's exact bytes; otherwise []."""
    path = BASE / "Readings" / "Glossary" / f"P{key}.md"
    logs = [log.read_text() for log in GLOSSARY_LOGS if log.exists()]
    logs = [text for text in logs if f"\n## P{key}\n" in text]
    if not path.exists() or not logs:
        return []
    data = path.read_bytes()
    text = logs[0]
    part = text.split(f"\n## P{key}\n", 1)[1].split("\n## ", 1)[0]
    if f"`{hashlib.sha256(data).hexdigest()}`" not in part:
        raise ValueError(f"The glossary log does not record the current Glossary/P{key}.md; run glossary.py")
    for block in re.split(r"^### ", part, flags=re.M)[1:]:
        if "- Lean: accepted\n" not in block or ": 1 complete\n" not in block or block.count(": True") != 2:
            raise ValueError(f"The glossary log does not record a pass for {block.splitlines()[0]}")
    body = data.decode().split("\n## Labels without a checked definition\n")[0].split("\n## Labels\n")[0]
    out = []
    for part in re.split(r"^## ", body, flags=re.M)[1:]:
        heading, rest = part.split("\n\n", 1)
        text_, ref = rest.rstrip().rsplit("\n\n", 1)
        m = re.fullmatch(r"\[Lean definition\]\(([^)#]+)#L(\d+)\) · `([^`]+)`", ref)
        out.append((heading.strip("*"), m[3], text_, m[1], int(m[2])))
    return out


def checked(key, page_bytes):
    """Find a check log that records a pass for this exact page. Returns (summary, {name: P′})."""
    digest = hashlib.sha256(page_bytes).hexdigest()
    for log in LOGS:
        if not log.exists():
            continue
        text = log.read_text()
        if f"\n## P{key}\n" not in text:
            continue
        part = text.split(f"\n## P{key}\n", 1)[1].split("\n## ", 1)[0]
        m = re.search(r"SHA-256 of the checked page: `([0-9a-f]{64})`", part)
        if not m or m[1] != digest:
            continue
        terms = {}
        for block in re.split(r"^### ", part, flags=re.M)[1:]:
            name = re.match(r".+ · `([^`]+)`", block)[1]
            if not ("- GF parses of the saved body: 1 complete\n" in block
                    and "Parsed tree equals the tree selected from the Lean export: True" in block
                    and "Saved body is the canonical rendering of the parsed tree: True" in block
                    and "- Lean: accepted\n" in block):
                raise ValueError(f"{log.name} does not record a pass for {name}")
            terms[name] = re.search(r"```lean\n(.+?)\n```", block, re.S)[1]
        summary = re.search(rf"^- (P{key}: .+)$", text, re.M)
        return (summary[1] if summary else ""), terms
    raise ValueError(f"No check log records a pass for the current P{key} page; run reader.py first")


def source_url(path, source):
    relative = path.relative_to(ROOT).as_posix()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    committed = subprocess.run(["git", "show", f"{revision}:{relative}"], cwd=ROOT, capture_output=True).stdout
    if committed != source:
        return os.path.relpath(path, WEB)
    return f"{REPOSITORY_URL}/blob/{revision}/{relative}"


def signature(lines, index, short):
    if not re.match(rf"(?:private )?(?:theorem|lemma) {re.escape(short)}\b", lines[index]):
        raise ValueError(f"Line {index + 1} does not declare {short}")
    text = "\n".join(lines[index:index + 80])
    m = re.search(r"\s:=(?=\s|$)", text)
    if not m:
        raise ValueError(f"No end of signature for {short}")
    return text[:m.start()].rstrip()


def docstring(lines, index):
    i = index - 1
    while i >= 0 and lines[i].startswith("@["):
        i -= 1
    if i < 0 or not lines[i].rstrip().endswith("-/"):
        return ""
    end = i
    while i >= 0 and not lines[i].lstrip().startswith("/--"):
        i -= 1
    if i < 0:
        return ""
    text = " ".join(l.strip() for l in lines[i:end + 1])
    return text.removeprefix("/--").removesuffix("-/").strip()


def claim_titles(registry, edition_id):
    by_name, by_locator = {}, []
    for c in registry["claims"]:
        for link in c.get("lean_links", []):
            by_name.setdefault(link["declaration"], c["title"])
        for r in c["source_refs"]:
            if edition_id in (None, r["edition"]):
                by_locator.append((r["locator"], c["title"]))
    return by_name, by_locator


def title_for(name, heading, by_name, by_locator):
    if name in by_name:
        return shown_title(by_name[name])
    for locator, title in by_locator:
        if re.match(re.escape(heading) + r"(?:[,;( ]|$)", locator):
            return shown_title(title)
    return None


def shown_title(title):
    """A registry title without the edition prefix (“ArXiv v2”, “Public-v1”): the page already names its edition."""
    title = re.sub(r"^(?:ArXiv v\d+|Public-v\d+):?\s+", "", title)
    return title[:1].upper() + title[1:]


# ---------- rendering ----------

def authors(names):
    return names[0] if len(names) == 1 else ", ".join(names[:-1]) + " and " + names[-1]


def code(text):
    return re.sub(r"`([^`]+)`", r"<code>\1</code>", escape(text, quote=False))


def reading(body):
    """The saved Markdown body: paragraphs, each a line of text and possibly nested bullets."""
    blocks = []
    for paragraph in body.split("\n\n"):
        html, depth = [], 0
        for line in paragraph.split("\n"):
            stripped = line.lstrip(" ")
            if not stripped.startswith("- "):
                html.append(f"<p>{quotes.typeset(line)}</p>")
                continue
            level = (len(line) - len(stripped)) // 2 + 1
            if level > depth:
                html.append("<ul><li>")
            else:
                html.append("</li></ul>" * (depth - level) + "</li><li>")
            depth = level
            html.append(quotes.typeset(stripped[2:]))
        html.append("</li></ul>" * depth)
        blocks.append("".join(html))
    return "\n".join(blocks)


def page_link(pdf, page):
    return f'<a href="{escape(pdf)}#page={page}">p. {page}</a>'


def paper_panel(paper, entry, why_missing):
    if entry is None:
        return f'<section class="form paper" aria-label="Statement in the paper"><h3 class="form-label">In the paper</h3><p class="missing">{escape(why_missing)}</p></section>'
    pdf = paper["pdf"]
    pages = sorted({q["page"] for q in entry.get("quotes", [])})
    where = escape(entry["item"] or "Unnumbered")
    if pages:
        where += ", " + ", ".join(page_link(pdf, p) for p in pages)
    body = "".join(f"<blockquote>{quotes.render(paper, q)}</blockquote>" for q in entry.get("quotes", []))
    if not entry.get("quotes"):
        body = '<p class="missing">The paper has no single statement for this declaration; see the docstring under the Lean statement.</p>'
    terms = "".join(f'<li>{quotes.render(paper, t)} {page_link(pdf, t["page"])}</li>' for t in entry.get("terms", []))
    if terms:
        n = len(entry["terms"])
        body += f'<details class="terms"><summary>Terms from the paper ({n})</summary><ul>{terms}</ul></details>'
    return f'''<section class="form paper" aria-label="Statement in the paper">
    <h3 class="form-label">In the paper <span class="where">{where}</span></h3>
    {body}
  </section>'''


def article(r, paper, entry, why_missing):
    anchor = r["short"].replace("_", "-")
    number = NUMBER.match(r["heading"])
    title = r["title"] or r["heading"]
    notes = "".join(f"<li>{quotes.typeset(n)}</li>" for n in (entry or {}).get("notes", []))
    notes = (f'<details class="notes"><summary>Paper vs. IR statement: notes (not checked by Lean)</summary>'
             f'<ul>{notes}</ul></details>') if notes else ""
    doc = f'<p class="doc"><span>Docstring.</span> {code(r["doc"])}</p>' if r["doc"] else ""
    toc = f'<a href="#{anchor}"><span>{escape(number[1]) if number else "·"}</span>{escape(title)}</a>'
    # The same text has the same unique parse, hence the same P′; both types are definitionally equal to it.
    same = "".join(f'<a href="#{o["short"].replace("_", "-")}">{escape(o["title"] or o["heading"])}</a>'
                   for o in r["same_as"])
    same = (f'<p class="same">Word for word the same as {same}.</p>') if same else ""
    html = f'''<article id="{anchor}" aria-labelledby="{anchor}-title">
  <h2 id="{anchor}-title"><span class="locator">{escape(r["heading"])}</span>{f' <span class="title">{escape(r["title"])}</span>' if r["title"] and r["title"] != r["heading"] else ""}</h2>
  {paper_panel(paper, entry, why_missing)}
  <section class="form ir" aria-label="IR statement">
    <h3 class="form-label">IR statement <span class="chips" title="The saved text has exactly one parse, it is the tree selected from the Lean export, and the kernel accepts it as the declaration's type.">checked by Lean</span></h3>
    <div class="reading" data-declaration="{escape(r["name"])}">{link_labels(shown_reading(r), r["label_map"], r["defined"])}</div>
    {same}
  </section>
  <details class="form lean" aria-label="Lean statement">
    <summary><span class="form-label">Lean statement</span> <code class="name">{escape(r["short"])}</code></summary>
    <div class="source"><code class="name">{escape(r["name"])}</code>{doc}<pre><code>{escape(r["signature"])}</code></pre>
      <a href="{escape(r["url"])}#L{r["line"]}">Overview.lean, line {r["line"]}</a>
      <p class="hint">The IR statement in Lean. The kernel checked that it equals the declaration above, up to unfolding definitions.</p>
      <pre><code>{escape(r["term"])}</code></pre></div>
  </details>
  {notes}
</article>'''
    return toc, html


def build_paper(key, cache, fetch):
    page = page_path(key)
    page_bytes = page.read_bytes()
    summary, terms = checked(key, page_bytes)
    side, tests = status(summary)
    items, labels, unread, settings = sections(page_bytes.decode())
    labels = with_plurals(labels)
    registry = json.loads((ROOT / "registry" / "papers" / f"P{key}.json").read_text())
    paper = quotes.load(key)
    names = [i[1] for i in items]
    edition_id = paper.get("edition") if paper else None
    editions = {e["id"]: e for e in registry["source_editions"]}
    edition = editions.get(edition_id) or registry["source_editions"][0]
    why = ("This page does not quote the paper yet." if paper is None else paper.get("unavailable", ""))
    quoted = paper if paper and not paper.get("unavailable") else None
    footer_pdf = ""
    if quoted:
        if fetch:
            quotes.fetch(key, quoted, cache)
        if not (cache / f"P{key}" / "paper.pdf").exists():
            why = ("The quotations are written but not yet checked, because the PDF has not been downloaded. "
                   "Run web.py with --fetch.")
            quoted = None
    if quoted:
        problems = quotes.check(key, quoted, names, cache)
        if problems:
            raise ValueError(f"P{key} quotations failed:\n  " + "\n  ".join(problems))
        registered = edition.get("pdf_sha256")
        match = ("matches the registry" if registered == quoted["pdf_sha256"] else
                 "the registry records a different copy" if registered else "the registry records no hash")
        source = (f' LaTeX from <a href="{escape(quoted["source"])}">the source</a> '
                  f'(SHA-256 <code>{quoted["source_sha256"][:12]}…</code>).') if quoted.get("source") else ""
        footer_pdf = (f'The quotations are verbatim from <a href="{escape(quoted["pdf"])}">the PDF</a> '
                      f'(SHA-256 <code>{quoted["pdf_sha256"][:12]}…</code>; {match}).{source} ')
        if quoted.get("transcribed"):
            fixes = len(quoted.get("ocr_fixes", []))
            footer_pdf = (f'The quotations are transcribed from a scan of <a href="{escape(quoted["pdf"])}">the paper</a> '
                          f'(SHA-256 <code>{quoted["pdf_sha256"][:12]}…</code>; {match}). Their words are checked '
                          f'against the scan’s text layer'
                          + (f' ({fixes} correction{"s" if fixes != 1 else ""} to the text layer, such as OCR misreadings, each with a reason)' if fixes else '')
                          + '; their formulas are transcribed by hand and not checked. ')
    by_name, by_locator = claim_titles(registry, edition["id"])
    sources, rows = {}, []
    for heading, name, body, link, line, shown, letter in items:
        path = (page.parent / link).resolve()
        if path not in sources:
            text = path.read_bytes()
            sources[path] = (text.decode().splitlines(), source_url(path, text))
        lines, url = sources[path]
        short = name.rsplit(".", 1)[1]
        rows.append({"heading": heading, "name": name, "short": short, "body": body, "line": line, "url": url,
                     "shown": shown, "setting": letter,
                     "signature": signature(lines, line - 1, short), "doc": docstring(lines, line - 1),
                     "term": terms.pop(name), "label_map": labels,
                     "title": title_for(name, heading, by_name, by_locator)})
    if terms:
        raise ValueError(f"P{key}: the log checks declarations missing from the page: {sorted(terms)}")
    definitions = glossary(key)
    defined = {c for _, c, _, _, _ in definitions}
    for r in rows:
        r["same_as"] = [o for o in rows if o is not r and o["body"] == r["body"]]
        r["defined"] = defined
    order = keys()
    k = order.index(key)
    pager = "".join([f'<a href="P{order[k - 1]}.html">← P{order[k - 1]}</a>' if k else "<span></span>",
                     '<a href="index.html">All papers</a>',
                     f'<a href="P{order[k + 1]}.html">P{order[k + 1]} →</a>' if k + 1 < len(order) else "<span></span>"])
    nav, articles = [], []
    if quoted and quoted.get("setting"):
        nav.append('<a href="#setting"><span>§</span>The paper’s setting</a>')
    if settings:
        nav.append('<a href="#throughout"><span>∀</span>Throughout</a>')
    decisions = [d for d in unfolding.rows() if d["paper"] == key]
    for r in rows:
        entry = quoted["declarations"].get(r["name"]) if quoted else None
        toc, html = article(r, quoted, entry, why)
        nav.append(toc)
        articles.append(html)
    if unread:
        nav.append('<a href="#unread"><span>–</span>Declarations without an IR statement</a>')
        items_html = "".join(f"<li><code>{escape(n)}</code>: {escape(why)}</li>" for n, why in unread)
        articles.append(f'''<section class="setting" id="unread" aria-labelledby="unread-title">
          <p class="locator">Not yet readable</p>
          <h2 id="unread-title">Declarations without an IR statement</h2>
          <p class="hint">The reader has no rule for these Lean statements yet, so they have no checked IR statement.</p>
          <ul>{items_html}</ul>
        </section>''')
    if decisions:
        nav.append('<a href="#unfolded"><span>↧</span>Definitions shown by their bodies</a>')

        def entry(d):
            label = " ".join(selector_words(d["constant"]))
            cite = ""
            if d[unfolding.EVIDENCE] and quoted:
                q = {"page": int(d["page"]), "tex": d[unfolding.EVIDENCE]}
                cite = (f'<blockquote>{quotes.render(quoted, q)}</blockquote>'
                        f'<p class="hint">The paper, {page_link(quoted["pdf"], q["page"])}; checked against the PDF and source.</p>')
            return (f'<li><p><em>{escape(label)}</em> <code>{escape(d["constant"])}</code>: '
                    f'{quotes.typeset(d["reason"])}</p>{cite}</li>')
        shown_ = [d for d in decisions if d["decision"] == "unfold"]
        kept = [d for d in decisions if d["decision"] == "keep"]
        articles.append(f'''<details class="setting unfolded folded" id="unfolded">
          <summary><h2 id="unfolded-title">Definitions shown by their bodies ({len(shown_)})</h2></summary>
          <p class="hint">Names that only Lean uses are written out; the paper's own terms stay labels. Lean checks the
          statements either way; the quotations below are checked against the paper.</p>
          <h3>Shown by their bodies</h3><ul class="decisions">{"".join(entry(d) for d in shown_)}</ul>
          <details><summary>Kept as labels ({len(kept)})</summary><ul class="decisions">{"".join(entry(d) for d in kept)}</ul></details>
        </details>''')
    if definitions:
        nav.append('<a href="#definitions"><span>≔</span>Definitions of the labels</a>')
        # Definitions also name constants that occur only inside other definitions; the glossary page lists them.
        glabels = {**with_plurals(label_table((BASE / "Readings" / "Glossary" / f"P{key}.md").read_text())), **labels}
        entries = []
        for label, const, body, link, line in definitions:
            path = (BASE / "Readings" / "Glossary" / link).resolve()
            url = source_url(path, path.read_bytes())
            entries.append(f'''<div class="definition" id="{def_anchor(const)}">
            <h3><em>{escape(label)}</em> <code>{escape(const)}</code></h3>
            <div class="reading">{link_labels(reading(body), glabels, defined, skip=const)}</div>
            <p class="hint"><a href="{escape(url)}#L{line}">Lean definition, line {line}</a></p>
          </div>''')
        articles.append(f'''<details class="definitions folded" id="definitions">
          <summary><h2 id="definitions-title">Definitions of the labels ({len(entries)})</h2></summary>
          <p class="hint">Each definition is checked by Lean like the statements above (proved by Iff.rfl or rfl).</p>
          {"".join(entries)}
        </details>''')
    setting = ""
    if quoted and quoted.get("setting"):
        items_html = "".join(f'<li>{quotes.render(quoted, s)} {page_link(quoted["pdf"], s["page"])}</li>'
                             for s in quoted["setting"])
        setting = f'''<details class="setting folded" id="setting">
          <summary><h2 id="setting-title">The paper’s setting ({len(quoted["setting"])})</h2></summary>
          <ul class="quotes">{items_html}</ul>
        </details>'''
    if settings:
        blocks = []
        for letter, text in settings.items():
            users = "".join(f'<li><a href="#{r["short"].replace("_", "-")}">{escape(r["title"] or r["heading"])}</a></li>'
                            for r in rows if r["setting"] == letter)
            blocks.append(f'''<div class="ir-setting" id="{setting_anchor(letter)}">
            <h3>Setting {letter}</h3>
            <div class="reading">{link_labels(reading(text), labels, defined)}</div>
          </div>''')
        setting += f'''<section class="setting throughout" id="throughout" aria-labelledby="throughout-title">
          <p class="locator">IR statements</p>
          <h2 id="throughout-title">Throughout</h2>
          <p class="hint">A statement that begins with “Setting A.” begins with these sentences.</p>
          {"".join(blocks)}
        </section>'''
    paper_meta = registry["paper"]
    html = Template((WEB / "template.html").read_text()).substitute(
        key=key, title=escape(paper_meta["title"]), authors=escape(authors(paper_meta["authors"])),
        venue=escape(edition["label"]), paper_url=escape((quoted or {}).get("pdf") or edition.get("url", "")),
        overview_url=escape(rows[0]["url"]), nav="\n".join(nav), setting=setting,
        articles="\n".join(articles), summary=escape(side), tests=escape(tests), count=len(rows),
        page_link=escape(os.path.relpath(page, WEB)), page_sha=hashlib.sha256(page_bytes).hexdigest()[:12],
        footer_pdf=footer_pdf, pager=pager)
    (WEB / f"P{key}.html").write_text(html)
    quoted_count = sum(1 for r in rows if quoted and quoted["declarations"].get(r["name"], {}).get("quotes"))
    return {"key": key, "title": paper_meta["title"], "authors": paper_meta["authors"],
            "year": paper_meta.get("year"), "venue": edition["label"], "count": len(rows), "unread": len(unread),
            "quoted": quoted_count, "why": why if not quoted else ""}


def build_index(results):
    rows = []
    for r in results:
        short = ("out of date: the Lean source changed after the check" if r.get("stale") else
                 "not quoted: the publisher restricts downloads" if "Elsevier" in r["why"] else
                 "not quoted: the download was refused" if "refused" in r["why"] else
                 "written, not yet checked" if "not yet checked" in r["why"] else "not quoted yet")
        status = (f"{r['quoted']} / {r['count']}" if not r["why"] else f'<span title="{escape(r["why"])}">{short}</span>')
        rows.append(f'''<tr><th scope="row"><a href="P{r["key"]}.html">P{r["key"]}</a></th>
  <td><a href="P{r["key"]}.html">{escape(r["title"])}</a><span class="by">{escape(", ".join(r["authors"]))} · {escape(r["venue"])}</span></td>
  <td class="num">{r["count"]}{f' <span class="by">+{r["unread"]} unread</span>' if r["unread"] else ""}</td><td class="num">{status}</td></tr>''')
    total = sum(r["count"] for r in results if not r.get("stale"))
    unread = sum(r["unread"] for r in results)
    quoted = sum(r["quoted"] for r in results)
    html = Template((WEB / "index-template.html").read_text()).substitute(
        rows="\n".join(rows), total=total, quoted=quoted, papers=len(results),
        unread=("No declaration lacks an IR statement." if not unread else
                "1 declaration has no IR statement yet; its page lists it." if unread == 1 else
                f"{unread} declarations have no IR statement yet; their pages list them."),
        first=results[0]["key"], last=results[-1]["key"])
    (WEB / "index.html").write_text(html)


def main():
    cli = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    cli.add_argument("--papers", nargs="+", help="papers to build (default: all)")
    cli.add_argument("--fetch", action="store_true", help="download missing papers into the cache")
    cli.add_argument("--cache", type=Path, default=quotes.CACHE, help="where downloaded papers live")
    args = cli.parse_args()
    selected = args.papers or keys()
    results = []
    for key in selected:
        try:
            results.append(build_paper(key, args.cache.resolve(), args.fetch))
        except ValueError as error:
            # Typically Overview.lean changed after the readings were checked. The page is not rebuilt;
            # the index says so, and the previous page (checked against the previous source) stays.
            registry = json.loads((ROOT / "registry" / "papers" / f"P{key}.json").read_text())
            meta = registry["paper"]
            results.append({"key": key, "title": meta["title"], "authors": meta["authors"], "year": meta.get("year"),
                            "venue": registry["source_editions"][0]["label"], "count": "—", "unread": 0, "quoted": 0,
                            "why": f"Not rebuilt: {error}. Run reader.py again.", "stale": True})
            print(f"P{key}: NOT REBUILT ({error})", flush=True)
            continue
        r = results[-1]
        print(f"P{key}: {r['count']} statements, {r['quoted']} quoted from the paper"
              + (f" ({r['why']})" if r["why"] else ""), flush=True)
    if not args.papers:
        build_index(results)
        print(f"Built {len(results)} pages and the index in {WEB}")


if __name__ == "__main__":
    main()
