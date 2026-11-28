"""Minimal pairs: small grammatical edits of the saved P01 readings, judged by Lean.

Each pair changes one structural feature of a reading (an order of sentences, a dependency
list, the place of a definition). The edited text is parsed on its own, its proposition is
sent to Lean against one or more declarations, and the verdicts are written to
MINIMAL-PAIRS.md together with a question a mathematician can answer from the English.
Comparing the reader's answer with Lean's verdict tests the scope conventions themselves.
"""
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parents[1]  # the IRStatement folder
sys.path.insert(0, str(Path(__file__).resolve().parent))
import reader

UNIFORM = "GenLimit.KM.Prompted.theorem_7_1_uniform"


def move(text, sentence, before=None, after=None):
    """Move one sentence (with its trailing space or paragraph break) next to an anchor."""
    if text.count(sentence) != 1:
        raise ValueError(f"Sentence not unique: {sentence!r}")
    text = text.replace(sentence, "", 1).replace("  ", " ").replace(" \n", "\n").replace("\n ", "\n")
    anchor = before or after
    if text.count(anchor) != 1:
        raise ValueError(f"Anchor not unique: {anchor!r}")
    return text.replace(anchor, f"{sentence}{anchor}" if before else f"{anchor}{sentence}", 1)


def replaced(text, old, new):
    if old not in text:
        raise ValueError(f"Edit anchor not found: {old[:60]!r}")
    return text.replace(old, new)


def pairs(bodies):
    b21, b22, b71 = (bodies[f"GenLimit.KM.Results.theorem_{n}"] for n in ("2_1", "2_2", "7_1"))
    out = []
    out.append(("Threshold after the sample (P01 Theorem 2.2)",
                "May t_C depend on the sample S?",
                reader.sample_before_threshold(b22, True), ["GenLimit.KM.Results.theorem_2_2"],
                "No: in the theorem t_C is chosen before S, so it cannot depend on S. The edit makes it depend "
                "on S, which Lean rejects as a different statement."))
    out.append(("Dependency list left stale (P01 Theorem 2.2)",
                "Is the edited text consistent?",
                reader.sample_before_threshold(b22, False), ["GenLimit.KM.Results.theorem_2_2"],
                "No: the text says t_C depends only on O and C although S was chosen first. Lean stops at the "
                "dependency check."))
    uniform = replaced(b71, "Let p be a sequence of words over A.\n\nSuppose that p(t) is robust for every t ∈ ℕ.\n\n"
                          "Let w(t) be the output of G on x and p at step t.\n\n"
                          "There is t⋆ ∈ ℕ, depending only on A, e, C, x, z and p, with the following property.",
                          "Then there is t⋆ ∈ ℕ, depending only on A, e, C, x and z, with the following property.\n\n"
                          "Let p be a sequence of words over A.\n\nSuppose that p(t) is robust for every t ∈ ℕ.\n\n"
                          "Let w(t) be the output of G on x and p at step t.\n\n")
    uniform = uniform.replace(" Let w(t) be the output of G on x and p at step t.\n\n For every", "\n\nFor every")
    uniform = uniform.replace("at step t.\n\n For every", "at step t.\n\nFor every")
    out.append(("One threshold for all prompt sequences (P01 Theorem 7.1)",
                "Does one t⋆ work for every robust prompt sequence p?",
                uniform, ["GenLimit.KM.Results.theorem_7_1", UNIFORM],
                "In Theorem 7.1, no: t⋆ is chosen after p. The edit chooses t⋆ first, which is the library's "
                "stronger lemma theorem_7_1_uniform; Lean accepts the edited text against that lemma only."))
    out.append(("Index introduced after the sets I and A (P01 Theorem 2.2)",
                "Do I and A depend on z?",
                move(b22, " Let z ∈ C with S ⊆ L_z.", before=" Let I = "), ["GenLimit.KM.Results.theorem_2_2"],
                "No: their definitions do not mention z, so moving z earlier does not change the statement. "
                "Lean accepts the edited text."))
    out.append(("Generator output defined after z (P01 Theorem 2.1)",
                "Does the order of these two introductions matter?",
                move(b21, " Let o(t) be the output of G on x at step t.", after=" Let z ∈ ℕ."),
                ["GenLimit.KM.Results.theorem_2_1"],
                "No: o does not use z. Lean accepts the edited text."))
    late_z = b21.replace(" Let z ∈ ℕ.", "", 1).replace(
        "Suppose that the set of values of x is exactly L_z.\n\nThen there is",
        "Suppose that the set of values of x is exactly L_z.\n\nLet z ∈ ℕ.\n\nThere is")
    out.append(("Index used before it is introduced (P01 Theorem 2.1)",
                "Is the edited text well formed?",
                late_z, ["GenLimit.KM.Results.theorem_2_1"],
                "No: L_z mentions z before z is introduced. Lean cannot elaborate it."))
    early_w = replaced(b71, "Suppose that p(t) is robust for every t ∈ ℕ.\n\nLet w(t) be the output of G on x and p at step t.",
                          "Let w(t) be the output of G on x and p at step t.\n\nSuppose that p(t) is robust for every t ∈ ℕ.")
    early_w = replaced(early_w, "Let p be a sequence of words over A.\n\nLet w(t)", "Let p be a sequence of words over A. Let w(t)")
    early_w = replaced(early_w, "\n\nThere is t⋆ ∈ ℕ, depending", "\n\nThen there is t⋆ ∈ ℕ, depending")
    out.append(("Generator run before robustness is assumed (P01 Theorem 7.1)",
                "Is the edited text well formed?",
                early_w, ["GenLimit.KM.Results.theorem_7_1"],
                "No: the prompted generator needs the robustness hypothesis as an argument, so it cannot be "
                "run before that hypothesis. Lean cannot elaborate it."))
    return out


def main():
    lines = ["# Minimal pairs", "",
             "Generated by `pairs.py`; do not edit. Each pair is a grammatical edit of one saved P01 reading. "
             "The question tests how a mathematician reads the scope conventions; the verdict is Lean's. "
             "A reader whose answers match the verdicts reads the conventions as the grammar defines them. "
             "[Readings](Readings/P01.md) · [Rules](RULES.md)", ""]
    with tempfile.TemporaryDirectory(prefix="ir-pairs-") as temp:
        work = Path(temp)
        reader.run([*reader.LAKE, "build", reader.EXPORTER, reader.VOCABULARY], cwd=reader.LEAN)
        entries, readings, missing, names, folder = reader.build(work, reader.FIRST)
        by_name = {r["entry"].name: r for r in readings}
        bodies = {s[0]: s[1] for s in reader.saved_sections(reader.page_path(reader.FIRST))}
        modules = sorted({r["entry"].module for r in readings})
        for k, (title, question, text, decls, explanation) in enumerate(pairs(bodies)):
            r = by_name[decls[0]]
            trees = reader.complete(reader.parse(r["g"], r["gname"], text))
            verdicts = []
            if len(trees) == 1:
                term = reader.lean_text(r["g"].render(trees, r["gname"], r["gname"] + "Lean")[0])
                results = reader.kernel(work, f"Pair{k}.lean", [(d, term) for d in decls], modules)
                verdicts = [(d, reader.stage(d, errors), errors) for d, errors in zip(decls, results)]
            lines += [f"## {k + 1}. {title}", "", f"**Question.** {question}", "", "```text", text, "```", "",
                      f"- GF parses of the edited text: {len(trees)}"]
            for d, stage, errors in verdicts:
                detail = "" if not errors else f" ({errors[0].splitlines()[0][:160]})"
                lines.append(f"- Lean against `{d}`: {stage}{detail}")
            lines += ["", f"**Answer.** {explanation}", ""]
            print(f"{k + 1}. {title}: {len(trees)} parse(s); " +
                  "; ".join(f"{d.rsplit('.', 1)[1]} {s}" for d, s, _ in verdicts), flush=True)
    (BASE / "MINIMAL-PAIRS.md").write_text("\n".join(lines))


if __name__ == "__main__":
    main()
