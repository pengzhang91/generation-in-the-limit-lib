"""Check the P23 bridge against Kleinberg and Wei's pinned Lean sources.

Usage: python3 scripts/check_p23_power_filter.py /path/to/authors-checkout
Release: fan-wei-math/characterizing-local-breadth-lean-public-candidate
Commit: 8e16d388e9078aa16890881c2b4d013eb48bfcf1
"""

import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile


PROJECT = Path(__file__).resolve().parents[1] / "GenLimitLean"
MODULES = (
    "Basic", "Common", "Histories", "Game", "Trees", "Separation", "Forest",
    "Sewing", "CharacterizationProofs", "CharacterizationSuff",
    "CharacterizationSuff2", "Characterization", "AppendixA",
    "AppendixAConstruction", "FiniteRank",
)
DIGEST = "d839aea51deebb6d70b31029cbea975411310144b64b2cedfb2e42726a161e4a"
# The release targets Lean 4.35. These are the 4.24 spellings in this project.
RENAMES = {
    "dite_eq_left ": "dif_pos ",
    "dite_eq_right ": "dif_neg ",
    "ite_eq_left ": "if_pos ",
    "ite_eq_right ": "if_neg ",
    "Set.countable_ofPred_finite_subset": "Set.countable_setOf_finite_subset",
    "Set.ncard_sdiff_singleton_of_mem": "Set.ncard_diff_singleton_of_mem",
    "ENat.natCast_lt_top": "ENat.coe_lt_top",
    "Finset.single_le_prod ": "Finset.single_le_prod' ",
    "Fin.val_cast": "Fin.coe_cast",
    "Int.ediv_ediv_of_nonneg": "Int.ediv_ediv",
    "Finset.card_filter_add_card_filter_not": "Finset.filter_card_add_filter_neg_card_eq_card",
}


def port_source(name, data):
    source = data.decode()
    for new, old in RENAMES.items():
        source = source.replace(new, old)
    if name == "AppendixA":
        # Lean 4.24 needs subset reflexivity spelled out in two proofs.
        # Its simplifier also closes the last filter-membership goal directly.
        lines = source.splitlines(keepends=True)
        for line in (300, 610):
            lines[line - 1] = lines[line - 1].replace("le_rfl", "(fun _ hx => hx)")
        lines[1739] = lines[1739].replace("]; exact", "] <;> exact")
        source = "".join(lines)
    return source


def upstream_sources(checkout):
    directory = checkout / "reproducibility" / "lean" / "BanachDensityHD"
    sources = {name: (directory / (name + ".lean")).read_bytes() for name in MODULES}
    digest = hashlib.sha256()
    for name, data in sorted(sources.items()):
        digest.update(("BanachDensityHD." + name).encode() + bytes([0]))
        digest.update(hashlib.sha256(data).digest())
    if digest.hexdigest() != DIGEST:
        raise SystemExit("The source files differ from the pinned release at 8e16d388.")
    return sources


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    sources = upstream_sources(parser.parse_args().checkout)
    prefix = "GenLimit.Paper23_BanachDensityTopologyAndGeometry."
    subprocess.run(
        ["lake", "build", prefix + "FixedShapeDensity", prefix + "MovingCubes"],
        cwd=PROJECT, check=True,
    )
    lake_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=PROJECT, text=True,
    ).strip()
    with tempfile.TemporaryDirectory(prefix="p23-power-") as temp:
        root = Path(temp)
        modules = root / "BanachDensityHD"
        modules.mkdir()
        env = {**os.environ, "LEAN_PATH": str(root) + os.pathsep + lake_path}
        for name, data in sources.items():
            print("Checking BanachDensityHD." + name, flush=True)
            source = port_source(name, data)
            path = modules / (name + ".lean")
            path.write_text(source)
            subprocess.run(
                ["lean", "-R", root, "-o", path.with_suffix(".olean"), path],
                cwd=PROJECT, env=env, check=True,
            )
        subprocess.run(
            ["lean", "-R", PROJECT, PROJECT / "External" / "Paper23PowerFilter.lean"],
            cwd=PROJECT, env=env, check=True,
        )


if __name__ == "__main__":
    main()
