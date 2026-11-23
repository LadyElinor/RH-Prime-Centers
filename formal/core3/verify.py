"""Recompile the pinned Core 3 source and its application inside a Lean 4.34.1 Lake environment."""
import argparse
import hashlib
import json
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
MODULES = ("PiCore3", "TentTransfer", "Core3Adapter", "PinnedFormula",
           "DiscreteTent", "HigherPowers", "OrdinaryFormula")
REPORTS = {
    "PinnedFormula": (
        "AlpogeRHCore3.explicitFormula",
        "PrimeWindowCore3.chebyshev_tent_bound",
        "PrimeWindowCore3.chebyshev_tent_vanishing",
    ),
    "OrdinaryFormula": (
        "PrimeWindowDiscrete.primePower_identity",
        "PrimeWindowDiscrete.ordinary_prime_identity",
        "PrimeWindowDiscrete.omitted_nonneg",
        "PrimeWindowDiscrete.split_squares_higher",
        "PrimeWindowDiscrete.squareCoeff_at_square",
        "PrimeWindowDiscrete.higherCoeff_pos_iff",
        "PrimeWindowDiscrete.higher_window_bound",
        "PrimeWindowDiscrete.higher_window_vanishing",
        "PrimeWindowCore3.ordinary_tent_bound",
        "PrimeWindowCore3.ordinary_tent_vanishing",
        "PrimeWindowCore3.square_tent_vanishing",
    ),
}
SQUARE_REPORTS = {
    "SquareKernel": (
        "PrimeWindowDiscrete.neg_tent_sqrt",
        "PrimeWindowDiscrete.square_limit_of_theta",
    ),
    "SquareBias": (
        "WeakPNT",
        "PrimeWindowDiscrete.theta_ratio",
        "PrimeWindowDiscrete.square_window_limit",
        "PrimeWindowDiscrete.square_window_uniform",
    ),
    "BiasFormula": (
        "PrimeWindowCore3.bias_tent_vanishing",
        "PrimeWindowCore3.signed_bias_vanishing",
        "PrimeWindowCore3.doubling_of_spectral_margin",
        "PrimeWindowCore3.power_windows_of_spectral_margin",
    ),
}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def prepare_square_sources(work, source_dir):
    modules = []
    for package in json.loads((HERE / "square-sources.json").read_text()):
        for filename, expected in package["files"].items():
            if source_dir:
                data = (source_dir / filename).read_bytes()
            else:
                url = (f"https://raw.githubusercontent.com/{package['repository']}/"
                       f"{package['commit']}/{filename}")
                with urllib.request.urlopen(url, timeout=60) as response:
                    data = response.read()
            if hashlib.sha256(data).hexdigest() != expected:
                raise SystemExit(f"Source hash mismatch for {filename}")
            path = work / filename
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            modules.append(filename.removesuffix(".lean").replace("/", "."))
    for module in SQUARE_REPORTS:
        shutil.copyfile(HERE / (module + ".lean"), work / (module + ".lean"))
    return [*modules, *SQUARE_REPORTS]


def verify(source, square_bias=False, square_sources=None):
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
                     HERE / "PinnedFormula.lean", HERE / "DiscreteTent.lean",
                     HERE / "HigherPowers.lean", HERE / "OrdinaryFormula.lean"):
            shutil.copyfile(file, work / file.name)
        paths = [os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(work), *paths]))
        modules = list(MODULES)
        reports = dict(REPORTS)
        if square_bias:
            modules.extend(prepare_square_sources(work, square_sources))
            reports.update(SQUARE_REPORTS)
        for module in modules:
            print(f"Compiling {module}", flush=True)
            path = module.replace(".", "/")
            result = subprocess.run(["lean", "-j2", "-o", path + ".olean", path + ".lean"],
                                    cwd=work, env=env, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            print(result.stdout, end="", flush=True)
            result.check_returncode()
            for target in reports.get(module, ()):
                match = re.search(r"'" + re.escape(target) + r"' depends on axioms:\s*\[([^\]]*)\]",
                                  result.stdout)
                if not match or {s.strip() for s in match[1].split(",")} != AXIOMS:
                    raise SystemExit(f"Unexpected axiom report for {target}")
        for module in modules:
            subprocess.run(["leanchecker", "--verbose", module], cwd=work, env=env, check=True)
        print(f"Checked the pinned source, {sum(map(len, reports.values()))} axiom reports "
              f"and all {len(modules)} module replays.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="already downloaded pinned Solution.lean")
    parser.add_argument("--square-bias", action="store_true",
                        help="also verify the prime-square limit and signed spectral margin")
    parser.add_argument("--square-sources", type=Path,
                        help="local directory of pinned PNT and Architect modules (implies --square-bias)")
    args = parser.parse_args()
    if args.source:
        source = args.source.read_bytes()
    else:
        with urllib.request.urlopen(UPSTREAM, timeout=60) as response:
            source = response.read()
    verify(source, args.square_bias or args.square_sources is not None, args.square_sources)
