"""Shared settings of a reading page (the "Throughout" section).

A setting is a run of leading sentences that several readings on one page share word for word:
introductions (Let …), assumptions (Assume …) and hypotheses (Suppose …). The page states it
once, under "## Throughout", as "### Setting A". A reading that shares it begins with the mark
*Setting A.* in place of those sentences.

The mark is plain text substitution. Before checking, the checker replaces the mark by the
text of the setting, then parses, compares and kernel-checks the full text exactly as if the
page spelled it out. So a setting adds one reading convention and no grammar rule.
"""
import re

MARK = re.compile(r"\*Setting ([A-Z])\.\*")
OPENERS = ("Let ", "Assume ", "Suppose ")
SECTION = "\n## Throughout\n"
MIN_SENTENCES = 3       # a shorter setting costs the reader a lookup and saves little
MIN_GAIN = 200          # characters a setting must save on its page
MAX_SETTINGS = 4
INTRO = ("Each setting below begins several readings on this page. A reading that begins with "
         "“*Setting A.*” begins with the text of Setting A: the checker puts the text in place of the "
         "mark and checks the full reading.")


def cuts(body):
    """The prefixes of `body` that a setting may cover: whole leading sentences that introduce,
    assume or suppose, in plain paragraphs, leaving the rest of the reading non-empty."""
    out, paras = [], body.split("\n\n")
    for i, para in enumerate(paras):
        if "\n" in para:        # a bullet list ends the run
            return out
        sentences = re.split(r"(?<=\.) (?=[A-Z])", para)
        for j, sentence in enumerate(sentences):
            if not sentence.startswith(OPENERS):
                return out
            if i + 1 < len(paras) or j + 1 < len(sentences):
                out.append(("\n\n".join(paras[:i] + [" ".join(sentences[:j + 1])]),
                            sum(len(re.split(r"(?<=\.) (?=[A-Z])", p)) for p in paras[:i]) + j + 1))
    return out


def choose(bodies):
    """Settings for a page: [(text, [names])], lettered in the order of their first reading.
    Greedy: each step takes the shared prefix that saves the most text; a reading uses at most one.
    A setting must save MIN_GAIN characters of reading text on its page."""
    options = {name: dict(cuts(body)) for name, body in bodies.items()}
    free, chosen = list(bodies), []
    while len(chosen) < MAX_SETTINGS:
        best = None
        for text in sorted({t for n in free for t, k in options[n].items() if k >= MIN_SENTENCES}):
            users = [n for n in free if text in options[n]]
            gain = (len(users) - 1) * len(text) - len(users) * len("*Setting A.*") - len("### Setting A")
            if len(users) >= 2 and (best is None or gain > best[0]):
                best = (gain, text, users)
        if best is None or best[0] < MIN_GAIN:
            break
        chosen.append(best)
        free = [n for n in free if n not in best[2]]
    order = list(bodies)
    return sorted(((text, users) for _, text, users in chosen), key=lambda s: order.index(s[1][0]))


def letters(settings):
    return {chr(ord("A") + k): text for k, (text, _) in enumerate(settings)}


def shorten(body, text, letter):
    """The body as shown: the setting's text replaced by its mark."""
    rest = body[len(text):]
    if not body.startswith(text) or not rest.startswith((" ", "\n\n")):
        raise ValueError(f"Setting {letter} is not a prefix of the reading")
    return f"*Setting {letter}.*" + rest


def section(settings):
    if not settings:
        return ""
    parts = [f"### Setting {letter}\n\n{text}" for letter, text in letters(settings).items()]
    return "## Throughout\n\n" + INTRO + "\n\n" + "\n\n".join(parts)


def split(page_text):
    """(page without its Throughout section, {letter: text})."""
    if SECTION not in page_text:
        return page_text, {}
    head, rest = page_text.split(SECTION, 1)
    block, sep, tail = rest.partition("\n## ")
    found = re.split(r"^### Setting ([A-Z])\n\n", block.strip("\n"), flags=re.M)
    if found[0].strip() != INTRO:
        raise ValueError("The Throughout section must begin with its fixed introduction")
    settings = {}
    for letter, text in zip(found[1::2], found[2::2]):
        text = text.strip("\n")
        if letter in settings or not text or MARK.search(text):
            raise ValueError(f"Malformed Setting {letter}")
        settings[letter] = text
    return head + sep + tail, settings


def expand(body, settings):
    """(full text of a shown body, letter of its setting or None). The mark may only open the body,
    followed by a space (same paragraph) or a blank line (new paragraph)."""
    m = MARK.match(body)
    if MARK.search(body, m.end() if m else 0):
        raise ValueError("A setting mark may only open a reading")
    if not m:
        return body, None
    rest = body[m.end():]
    if m[1] not in settings or not rest.startswith((" ", "\n\n")) or rest.startswith(("  ", "\n\n\n")):
        raise ValueError(f"Malformed use of Setting {m[1]}")
    return settings[m[1]] + rest, m[1]
