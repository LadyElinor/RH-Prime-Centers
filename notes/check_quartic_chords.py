"""Certify the ordinary-prime tent on [6^4, 6^8] using integer arithmetic."""
from decimal import Decimal, localcontext
from fractions import Fraction
from math import ceil, floor, isqrt

K = 6
B = K**8
SCALE = 10**24


def primes_through(n):
    sieve = bytearray(b"\x01") * (n + 1)
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((n - p*p)//p + 1)
    return (p for p in range(2, n + 1) if sieve[p])


def log_ticks(p):
    # ln is correctly rounded (half even). Adjacent decimals enclose log p.
    with localcontext() as ctx:
        ctx.prec = 60
        logp = Decimal(p).ln()
        lo = Fraction(logp.next_minus()) * SCALE // (2*p)
        hi = Fraction(logp.next_plus()) * SCALE // (2*p)
        if lo != hi:
            raise ArithmeticError(f"Ambiguous tick at prime {p}")
        return lo


def check():
    anchors = [k**4 for k in range(K, K*K + 1)]
    jumps = dict.fromkeys(anchors, 0)
    for p in primes_through(B):
        q = log_ticks(p)
        for x, jump in ((p, -2*q), (2*p, 3*q), (4*p, -q)):
            if x <= B:
                jumps[x] = jumps.get(x, 0) + jump

    slope = 2 * log_ticks(2)
    previous = value = 0
    values = {}
    for x in sorted(jumps):
        value += slope * (x - previous)
        if x >= anchors[0]:
            values[x] = value
        slope += jumps[x]
        previous = x

    # At an integer x the factor multiplying q_p is in [0, 2p].
    # All primes and the linear term together cost fewer than error ticks.
    error = 2*B*B + 2*B
    margin, margin_k = min((Fraction(values[k**4] - error, SCALE*k*k), k)
                           for k in range(K, K*K + 1))
    max_departure = Fraction(0)
    worst_vertex = anchors[0]
    cell = 0
    for x, value in values.items():
        if x > anchors[cell + 1]:
            cell += 1
        a, b = anchors[cell:cell+2]
        chord = Fraction((b-x)*values[a] + (x-a)*values[b], b-a)
        normalized = (abs(value-chord) + 2*error) / (SCALE*(K+cell)**2)
        if normalized > max_departure:
            max_departure = normalized
            worst_vertex = x
    # F and its chord are affine between successive event positions.
    print("Range", anchors[0], B, "cells", len(anchors)-1, "vertices", len(values))
    print("Lower bound on anchor margin / k² (rounded down)",
          floor(margin*10000), "/ 10000 at k =", margin_k)
    print("Upper bound on absolute departure / k² (rounded up)",
          ceil(max_departure*10000), "/ 10000 at x =", worst_vertex)
    if margin <= max_departure:
        raise ArithmeticError("Uniform bounds do not certify this block")


if __name__ == "__main__":
    check()
