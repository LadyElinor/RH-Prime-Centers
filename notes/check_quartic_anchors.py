"""Outward integer bounds at the fourth powers. Run with Python 3.11 or later."""
from decimal import Decimal, localcontext
from fractions import Fraction
from math import isqrt

SCALE = 10**25


def covered_sums(anchors, power):
    """Enclose the tent on n=p**power by streaming two cumulative integer sums."""
    positions = sorted({k**4 // d for k in anchors for d in (4, 2, 1)})
    maximum = positions[-1] if power == 1 else isqrt(positions[-1])
    sieve = bytearray(b"\x01") * (maximum + 1)
    for p in range(2, isqrt(maximum) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((maximum - p*p)//p + 1)

    sums = {}
    i = 0
    total = reciprocal = 0
    with localcontext() as ctx:
        ctx.prec = 50
        for p in range(2, maximum + 1):
            if not sieve[p]:
                continue
            n = p**power
            while i < len(positions) and positions[i] < n:
                sums[positions[i]] = total, reciprocal
                i += 1
            # Decimal.ln is correctly rounded. Directed neighbours enclose the log.
            v = Decimal(p).ln()
            lo = Fraction(v.next_minus()) * SCALE // (2*n)
            hi = Fraction(v.next_plus()) * SCALE // (2*n)
            if lo != hi:
                raise ArithmeticError(f"Tick unresolved for {p}")
            total += n*lo
            reciprocal += lo
    for t in positions[i:]:
        sums[t] = total, reciprocal

    for k in anchors:
        x = k**4
        a, b, c = [sums[x//d] for d in (4, 2, 1)]
        q = 4*(b[0]-a[0]) - x*(b[1]-a[1]) + 2*x*(c[1]-b[1]) - 2*(c[0]-b[0])
        # Each tick is rounded down with error <1. A weight uses at most 2n
        # ticks and at most x primes can occur, giving an upper error of 2x².
        yield k, Fraction(q, SCALE), Fraction(q+2*x*x, SCALE)


def main():
    minima = min((lo/(k*k), k) for k, lo, _ in covered_sums(range(23, 3000), 2))
    if minima[0] <= Fraction(2338, 10000):
        raise ArithmeticError("Insufficient prime-square margin")
    with localcontext() as ctx:
        ctx.prec = 50
        log2_lower = Fraction(Decimal(2).ln().next_minus())
    direct = min(((k**4 * log2_lower / 2 - hi)/(k*k), k)
                 for k, _, hi in covered_sums(range(1, 23), 1))
    if direct[0] <= Fraction(2174, 10000):
        raise ArithmeticError("Insufficient ordinary-prime margin")
    for title, (ratio, k) in (("Square sum / k²", minima), ("Ordinary deficit / k²", direct)):
        print(f"{title} >= {ratio*10**6//1}/1000000; minimum lower enclosure at k={k}")


if __name__ == "__main__":
    main()
