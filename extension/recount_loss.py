"""Independently verify the three smallest rows of the published loss certificate.

Run with Python 3 and the path to the integer CSV. Uses stdlib Decimal and a
prime-prefix evaluation of each checkpoint. All comparisons after computing
logarithm enclosures are integer operations.
"""
import argparse
import csv
from bisect import bisect_right
from decimal import Decimal, localcontext
from math import isqrt
from pathlib import Path


WINDOWS = [(400, 800), (256, 1024), (20736, 248832)]
SCALE = 10**30


def prime_prefixes(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = b'\0\0'
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes(len(range(p*p, limit+1, p)))
    primes = [p for p in range(2, limit + 1) if sieve[p]]
    logs = [0]
    recip_lo = [0]
    recip_hi = [0]
    with localcontext() as ctx:
        ctx.prec = 48
        for p in primes:
            # Decimal ln is correctly rounded. For p <= 248832, ln(p)<13.
            # After exact scaling by 10^30 its error is <1 absolute unit.
            q = int(Decimal(p).ln().scaleb(30))
            lo, hi = q - 1, q + 2
            logs.append(logs[-1] + lo)
            recip_lo.append(recip_lo[-1] + lo // p)
            recip_hi.append(recip_hi[-1] + (hi + p - 1) // p)
    return primes, logs, recip_lo, recip_hi


def double_deficit(x, data):
    primes, logs, recip_lo, recip_hi = data
    i, j, k = (bisect_right(primes, bound) for bound in (x // 4, x // 2, x))
    a, b = logs[j] - logs[i], logs[k] - logs[j]
    a_hi, b_hi = a + 3*(j-i), b + 3*(k-j)
    lo = x*logs[1] - 4*a_hi + 2*b
    hi = x*(logs[1]+3) - 4*a + 2*b_hi
    lo += x*((recip_lo[j] - recip_lo[i]) - 2*(recip_hi[k] - recip_hi[j]))
    hi += x*((recip_hi[j] - recip_hi[i]) - 2*(recip_lo[k] - recip_lo[j]))
    return lo, hi


def check_row(row, data):
    a, b = int(row["left"]), int(row["right"])
    primes = data[0]
    checkpoints = [a] + [2*p for p in primes if a < 2*p < b] + [b]
    values = [double_deficit(x, data) for x in checkpoints]
    start = values[0]
    winner = min(range(len(values)), key=lambda i: values[i][0])
    if any(v[0] <= values[winner][1] for i, v in enumerate(values) if i != winner):
        raise ValueError("raw minimum unresolved")
    loss = (start[0] - values[winner][1], start[1] - values[winner][0])
    gross_lo = gross_hi = 0
    first_excess = 0
    cuts = []
    block_start = start
    block_lo = block_hi = 0
    for i in range(1, len(values)):
        prev, curr = values[i-1:i+1]
        drop_lo = max(0, prev[0] - curr[1])
        drop_hi = max(0, prev[1] - curr[0])
        gross_lo += drop_lo
        gross_hi += drop_hi
        if not first_excess and gross_hi >= start[0]:
            if gross_lo <= start[1]:
                raise ValueError("unresolved first crossing")
            first_excess = checkpoints[i]
        block_lo += drop_lo
        block_hi += drop_hi
        if block_hi >= block_start[0]:
            if block_lo <= block_start[1] or drop_hi >= prev[0]:
                raise ValueError("unresolved block split")
            cuts.append(checkpoints[i-1])
            block_start, block_lo, block_hi = prev, drop_lo, drop_hi

    # Published bounds are for 2F in units of 2^-80. Our intervals use 10^-30.
    for key, (lo, hi) in {"start": start, "loss": loss,
                          "downward": (gross_lo, gross_hi)}.items():
        if not (int(row[key+"_lo"])*SCALE <= lo*(1 << 80)
                <= hi*(1 << 80) <= int(row[key+"_hi"])*SCALE):
            raise ValueError(f"{a}..{b}: {key} enclosure escapes published bounds")
    fields = {"checkpoints": len(checkpoints), "minimum_x": checkpoints[winner],
              "first_excess_x": first_excess, "blocks": len(cuts)+1,
              "interior_splits": "|".join(str(x) for x in cuts)}
    for key, calculated in fields.items():
        if str(calculated) != row[key]:
            raise ValueError(f"{a}..{b}: {key} disagrees")
    print(f"{a}..{b}: all fields verified ({len(checkpoints)} checkpoints)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    data = prime_prefixes(max(b for _, b in WINDOWS))
    with args.certificate.open(newline="") as f:
        rows = {(int(r["left"]), int(r["right"])): r for r in csv.DictReader(f)}
    for key in WINDOWS:
        check_row(rows[key], data)


if __name__ == "__main__":
    main()
