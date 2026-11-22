"""Certify dyadic prime deficits by two independent evaluations. Python 3.10+."""
import argparse
import json
from bisect import bisect_right
from decimal import Decimal, localcontext
from heapq import merge
from math import isqrt
from pathlib import Path

DIGITS = 24
SCALE = 10 ** DIGITS
WINDOWS = [(400, 800)] + [(n**4, n**5) for n in (4, 12, 24)]


def primes_to(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            size = (limit - p*p) // p + 1
            flags[p*p::p] = bytes(size)
    return [i for i, flag in enumerate(flags) if flag]


def odd_sieve(limit):
    # Entry i represents 2*i+1. Mark odd composites from each square.
    flags = bytearray([1]) * ((limit + 1) // 2)
    flags[0] = 0
    for i in range(1, (isqrt(limit) + 1) // 2):
        if flags[i]:
            p = 2*i + 1
            start = (p*p - 1) // 2
            flags[start::p] = bytes(len(range(start, len(flags), p)))
    return [2] + [2*i+1 for i, flag in enumerate(flags) if flag]


class Minimum:
    """Track the two lowest lower endpoints to certify the winning location."""
    def __init__(self):
        self.count = 0
        self.best = None
        self.runner_lower = None

    def add(self, x, lower, upper):
        if lower > upper:
            raise ValueError("reversed interval")
        self.count += 1
        if self.best is None or lower < self.best[1]:
            if self.best is not None:
                self.runner_lower = self.best[1]
            self.best = (x, lower, upper)
        elif self.runner_lower is None or lower < self.runner_lower:
            self.runner_lower = lower

    def result(self):
        x, lower, upper = self.best
        if lower <= 0 or self.runner_lower is None or upper >= self.runner_lower:
            raise ArithmeticError("positivity or the unique minimizer is unresolved")
        return {"points": self.count, "x_at_min": x, "lower": lower, "upper": upper}


def candidates(primes, left, right):
    return sorted({left, right} | {2*p for p in primes if left < 2*p < right})


def prefix_check(windows):
    primes = primes_to(max(right for _, right in windows))
    log_prefix = [0]
    ratio_prefix = [0]
    with localcontext() as ctx:
        ctx.prec = DIGITS + 20
        for p in primes:
            value = Decimal(p).ln()
            lower = int(value.next_minus().scaleb(DIGITS))
            upper = int(value.next_plus().scaleb(DIGITS))
            if lower != upper:
                raise ArithmeticError("raise decimal precision")
            log_prefix.append(log_prefix[-1] + lower)
            ratio_prefix.append(ratio_prefix[-1] + lower // p)
    log_two = log_prefix[1]
    summaries = []
    for left, right in windows:
        minimum = Minimum()
        for x in candidates(primes, left, right):
            if x % 2:
                raise ValueError("the prefix method expects even x endpoints")
            k = x // 2
            i = bisect_right(primes, k // 2)
            j = bisect_right(primes, k)
            h = bisect_right(primes, 2*k)
            n_a, n_b = j-i, h-j
            log_a, log_b = log_prefix[j]-log_prefix[i], log_prefix[h]-log_prefix[j]
            ratio_a = ratio_prefix[j]-ratio_prefix[i]
            ratio_b = ratio_prefix[h]-ratio_prefix[j]
            base = k*log_two - 2*log_a + k*ratio_a + log_b - 2*k*ratio_b
            lower = base - 2*n_a - 2*k*n_b
            upper = base + k + k*n_a + n_b
            minimum.add(x, lower, upper)
        summaries.append(minimum.result())
    return summaries


def ceil_div(a, b):
    return -(-a // b)


def log_ratio(a, b, terms):
    """Bound SCALE*log(a/b), 1 <= a/b <= 2, by the odd atanh series."""
    n, d = a-b, a+b
    if not 0 <= n <= d//3:
        raise ValueError("ratio outside the series bound")
    if n == 0:
        return (0, 0)
    # log(a/b) = 2*sum z^(2j+1)/(2j+1), z=n/d.
    # After 'terms' terms the scaled remainder is <=
    # 2*SCALE*z^(2*terms+1)/(1-z^2). Check it is at most one unit.
    if 2*SCALE*pow(n, 2*terms+1)*d*d > pow(d, 2*terms+1)*(d*d-n*n):
        raise ArithmeticError("increase term count")
    power_lo, power_hi = SCALE*n//d, ceil_div(SCALE*n, d)
    n2, d2 = n*n, d*d
    lo = hi = 0
    for j in range(terms):
        odd = 2*j+1
        lo += 2*power_lo//odd
        hi += ceil_div(2*power_hi, odd)
        power_lo = power_lo*n2//d2
        power_hi = ceil_div(power_hi*n2, d2)
    return lo, hi+1


def event_stream(primes, ratios, factor, coefficient, xmax):
    for p, (lo, hi) in zip(primes, ratios):
        x = factor*p
        if x > xmax:
            break
        a, b = coefficient*lo, coefficient*hi
        yield (x, min(a,b), max(a,b))


def sweep_check(windows):
    xmax = max(right for _, right in windows)
    primes = odd_sieve(xmax)
    two_lo, two_hi = log_ratio(2, 1, 28)
    anchors = [log_ratio(h, 32, 28) for h in range(32, 64)]
    ratios = []
    for p in primes:
        e = p.bit_length()-1
        base = 1 << e
        h = 32*p//base
        anchor_lo, anchor_hi = anchors[h-32]
        # Residual ratio < 33/32, so eight terms suffice at this scale.
        rem_lo, rem_hi = log_ratio(32*p, h*base, 8)
        log_lo = e*two_lo + anchor_lo + rem_lo
        log_hi = e*two_hi + anchor_hi + rem_hi
        ratios.append((log_lo//p, ceil_div(log_hi, p)))

    # Sweep the slope of 2*D(x/4). Only centers (x=2p) and endpoints
    # need a value check. Events at a coincident location have zero spacing.
    ends = {t for pair in windows for t in pair}
    jumps = merge(event_stream(primes, ratios, 1, -2, xmax),
                  event_stream(primes, ratios, 2, 3, xmax),
                  event_stream(primes, ratios, 4, -1, xmax),
                  ((x,0,0) for x in sorted(ends)))
    centers = iter(2*p for p in primes if 2*p <= xmax)
    center = next(centers, None)
    minima = [Minimum() for _ in windows]
    slope_lo, slope_hi = two_lo, two_hi
    value_lo = value_hi = previous = 0
    for x, jump_lo, jump_hi in jumps:
        if x != previous:
            value_lo += (x-previous)*slope_lo
            value_hi += (x-previous)*slope_hi
            if x == center or x in ends:
                for (left,right), minimum in zip(windows, minima):
                    if left <= x <= right and (x == center or x in (left,right)):
                        minimum.add(x, value_lo//2, ceil_div(value_hi, 2))
                if x == center:
                    center = next(centers, None)
            previous = x
        slope_lo += jump_lo
        slope_hi += jump_hi
    return [minimum.result() for minimum in minima]


def certificate(windows):
    direct = prefix_check(windows)
    sweep = sweep_check(windows)
    results = []
    for (left, right), a, b in zip(windows, direct, sweep):
        if (a["points"], a["x_at_min"]) != (b["points"], b["x_at_min"]):
            raise ValueError("methods disagree on count or minimizer")
        if max(a["lower"], b["lower"]) > min(a["upper"], b["upper"]):
            raise ValueError("disjoint minimum enclosures")
        results.append({"x_interval": [left, right], "points": a["points"],
                        "x_at_min": a["x_at_min"],
                        "prefix_bounds": [a["lower"], a["upper"]],
                        "sweep_bounds": [b["lower"], b["upper"]]})
    return {"denominator_for_bounds": SCALE, "windows": results}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path, help="compare the recomputed record to this JSON file")
    args = parser.parse_args()
    report = certificate(WINDOWS)
    if args.check and report != json.loads(args.check.read_text()):
        raise SystemExit("record mismatch")
    print(json.dumps(report, indent=2))
