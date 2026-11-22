"""Recompute the certificate with Python 3.10+, g++ and GMP development headers."""
import argparse
import csv
from decimal import Decimal, localcontext
from fractions import Fraction
from io import StringIO
from pathlib import Path
import subprocess
import tempfile


def anchor_floor(x):
    with localcontext() as ctx:
        ctx.prec = 60
        if x == 1:
            return 0
        rounded = x.ln()
        lo = Fraction(rounded.next_minus()) * 2**57
        hi = Fraction(rounded.next_plus()) * 2**57
        if lo // 1 != hi // 1:
            raise ArithmeticError("anchor straddles a fixed-point boundary")
        return lo // 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path, help="match the recomputed certificate exactly")
    args = parser.parse_args()
    src = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory() as temporary:
        temp = Path(temporary)
        anchors = [anchor_floor(Decimal(2))]
        anchors.extend(anchor_floor(Decimal(h)/4096) for h in range(4096,8192))
        (temp/"anchors").write_text("\n".join(map(str,anchors))+"\n")
        for name in ("check_interior", "verify"):
            subprocess.run(["g++", "-std=c++17", "-O3", str(src/(name + ".cpp")),
                            "-lgmpxx", "-lgmp", "-o", str(temp/name)], check=True)
        subprocess.run([temp/"check_interior"], check=True)
        report = subprocess.check_output([temp/"verify",temp/"anchors"],text=True)
    rows = list(csv.DictReader(StringIO(report)))
    if len(rows) != 6:
        raise ArithmeticError("incomplete certificate")
    if args.check and report != args.check.read_text():
        raise SystemExit("certificate mismatch")
    print(report,end="")


if __name__ == "__main__":
    main()
