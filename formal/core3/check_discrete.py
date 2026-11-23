"""Compare the two tent formulas exactly, coefficient by coefficient in log(p)."""
from collections import defaultdict
from fractions import Fraction
from math import isqrt


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def prime_powers(limit):
    events = []
    for p in range(2, limit + 1):
        if is_prime(p):
            n, k = p, 1
            while n <= limit:
                events.append((n, p, k))
                n *= p
                k += 1
    return sorted(events)


def integrate_half(y, multiplier, events, coefficients):
    # ψ is constant between consecutive events. Integrate u⁻² on each piece.
    cuts = sorted({y, 2*y, *(Fraction(n) for n, _, _ in events if y < n < 2*y)})
    for left, right in zip(cuts, cuts[1:]):
        mass = multiplier * y * (1/left - 1/right)
        for n, p, _ in events:
            if n > left:
                break
            coefficients[p] += mass


def check_scale(y):
    events = prime_powers(int(4*y))
    integral = defaultdict(Fraction)
    integrate_half(y, -2, events, integral)
    integrate_half(2*y, 2, events, integral)

    ordinary, squares, higher = (defaultdict(Fraction) for _ in range(3))
    for n, p, k in events:
        weight = max(0, min(2*(1-y/n), 4*y/n-1))
        group = ordinary if k == 1 else squares if k == 2 else higher
        group[p] += weight
    for p in {p for _, p, _ in events}:
        assert integral[p] == ordinary[p] + squares[p] + higher[p], (y, p)
    return squares, higher


if __name__ == "__main__":
    for i in range(1, 258):
        check_scale(Fraction(i, 4))
    squares, higher = check_scale(Fraction(2))
    assert {p: w for p, w in squares.items() if w} == {2: 1}
    assert not any(higher.values())
    assert check_scale(Fraction(9, 2))[0][3] == 1
    assert check_scale(Fraction(4))[1][2] == 1
    print("257 rational scales matched exactly, including the square and cube endpoint checks.")
