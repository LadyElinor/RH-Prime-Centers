"""Recompile the pinned Core 3 source and its application inside a Lean 4.34.1 Lake environment."""
import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import urllib.request

HERE = Path(__file__).resolve().parent
UPSTREAM = (
    "https://raw.githubusercontent.com/Osgood001/riemann-hypothesis/"
    "25bc57f3919f3578d396b71f8bc2cf9b3675ac63/community/core3-attempt-97759/Solution.lean"
)
SHA256 = "28fab02c68c3a5a4d596e72f68caa532d14ddf8c70a5a2abfe5c4e821bf76e68"
THEOREMS = (
    "AlpogeRHCore3.explicitFormula",
    "PrimeWindowCore3.chebyshev_tent_bound",
    "PrimeWindowCore3.chebyshev_tent_vanishing",
)
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def verify(source):
    if hashlib.sha256(source).hexdigest() != SHA256:
        raise SystemExit("The Core 3 source does not match the pinned SHA-256.")
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    if "version 4.34.1," not in version:
        raise SystemExit("Run this check with the Lean toolchain selected in formal/core3.")
    print(version, flush=True)
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        (work / "PiCore3.lean").write_bytes(source)
        for file in (HERE.parent / "TentTransfer.lean", HERE.parent / "Core3Adapter.lean",
                     HERE / "PinnedFormula.lean"):
            shutil.copyfile(file, work / file.name)
        paths = [os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(work), *paths]))
        modules = ["PiCore3", "TentTransfer", "Core3Adapter", "PinnedFormula"]
        for module in modules:
            print(f"Compiling {module}", flush=True)
            result = subprocess.run(["lean", "-j2", "-o", module + ".olean", module + ".lean"],
                                    cwd=work, env=env, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            print(result.stdout, end="", flush=True)
            result.check_returncode()
            if module == "PinnedFormula":
                for target in THEOREMS:
                    match = re.search(r"'" + re.escape(target) + r"' depends on axioms:\s*\[([^\]]*)\]",
                                      result.stdout)
                    if not match or {s.strip() for s in match[1].split(",")} != AXIOMS:
                        raise SystemExit(f"Unexpected axiom report for {target}")
        for module in modules:
            subprocess.run(["leanchecker", "--verbose", module], cwd=work, env=env, check=True)
        print("Checked the pinned source, the three axiom reports and all four module replays.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="already downloaded pinned Solution.lean")
    args = parser.parse_args()
    if args.source:
        verify(args.source.read_bytes())
    else:
        with urllib.request.urlopen(UPSTREAM, timeout=60) as response:
            source = response.read()
        verify(source)
