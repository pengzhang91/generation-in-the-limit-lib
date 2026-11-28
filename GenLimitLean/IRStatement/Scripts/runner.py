"""Shared helpers: run Lake and GF, and list the results of each paper.

`inventory(key)` lists the theorem, lemma and alias declarations of the paper's
`Results/Overview.lean`, in file order, with their full names and lines.
"""
from dataclasses import dataclass
import os
from pathlib import Path
import re
import shutil
import subprocess

BASE = Path(__file__).resolve().parents[1]  # the IRStatement folder
LEAN = BASE.parent  # the Lake project: GenLimitLean/
LAKE = ["lake"]
# P00–P15; reader.LATER adds every later paper that has a Results/Overview.lean.
KEYS = ("00", "00A", "01", "02", "03", "04") + tuple(f"{n:02}" for n in range(5, 16))


def run(args, *, cwd, stdin=None, env=None, check=True):
    result = subprocess.run(args, cwd=cwd, input=stdin, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if check and result.returncode:
        raise ValueError(result.stdout + result.stderr)
    return result


class Grammar:
    """A GF grammar compiled in `work` from `name`.gf and its concrete `languages`, run in batch mode.
    GF is `GF_BIN`, `gf` on the path, or a copy in `local/tools/` next to this file."""

    def __init__(self, work, name, languages, source_dir):
        self.work = work
        self.env = os.environ.copy()
        self.gf = os.environ.get("GF_BIN") or shutil.which("gf")
        if not self.gf:
            local = BASE / "local" / "tools"
            if not (local / "gf").is_file():
                raise ValueError("Set GF_BIN to the path of your GF executable.")
            self.gf = str(local / "gf")
            self.env["DYLD_LIBRARY_PATH"] = str(local)
        for module in (name, *languages):
            if source_dir != work:
                shutil.copyfile(source_dir / (module + ".gf"), work / (module + ".gf"))
        run([self.gf, "-make", *(lang + ".gf" for lang in languages)], cwd=work, env=self.env)

    def batch(self, commands, grammar):
        marker = "END_OF_SCOPE_RESULT"
        script = "".join(f'{cmd}\nps "{marker}"\n' for cmd in commands)
        result = run([self.gf, "--run", grammar + ".pgf"], cwd=self.work, env=self.env, stdin=script)
        groups = re.split(rf"(?m)^{marker}$", result.stdout)
        if len(groups) != len(commands) + 1 or groups[-1].strip() or result.stderr.strip():
            raise ValueError(f"Unexpected GF output: {result.stderr or result.stdout[:400]}")
        return [[line.strip() for line in group.splitlines() if line.strip()] for group in groups[:-1]]

    def render(self, trees, grammar, language):
        results = self.batch([f"l -all -lang={language} {tree}" for tree in trees], grammar)
        out = []
        for tree, result in zip(trees, results):
            if len(result) != 1:
                raise ValueError(f"Expected one rendering for {tree!r}, obtained {result!r}")
            out.append(result[0])
        return out


@dataclass(frozen=True)
class Entry:
    name: str
    path: Path
    line: int

    @property
    def module(self):
        return ".".join(self.path.relative_to(LEAN).with_suffix("").parts)


def inventory(key):
    """The declarations of GenLimit/PaperXX_*/Results/Overview.lean, in file order."""
    directory, = (p for p in (LEAN / "GenLimit").glob(f"Paper{key}_*") if p.is_dir())
    path = directory / "Results" / "Overview.lean"
    entries, scope = [], []
    for line, s in enumerate(path.read_text().splitlines(), 1):
        if match := re.fullmatch(r"namespace ([\w.]+)", s):
            scope.append(match[1])
        elif scope and s == "end " + scope[-1]:
            scope.pop()
        elif match := re.match(r"^(?:theorem|lemma|alias) ([\w.]+)", s):
            entries.append(Entry(".".join([*scope, match[1]]), path, line))
    if not entries or len({e.name for e in entries}) != len(entries):
        raise ValueError(f"Empty or duplicate result inventory for P{key}")
    return entries
