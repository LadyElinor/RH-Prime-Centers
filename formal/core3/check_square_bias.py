"""Print finite ordinary-prime square sums alongside their asymptotic coefficient."""
from math import fsum, isqrt, log, sqrt


def primes_up_to(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            size = (limit - p*p) // p + 1
            sieve[p*p::p] = bytes(size)
    return [p for p in range(2, limit + 1) if sieve[p]]


def normalized_square_sum(y, primes):
    terms = []
    for p in primes:
        n = p*p
        if n > 4*y:
            break
        if n > y:
            numerator = 2*(n-y) if n <= 2*y else 4*y-n
            terms.append(log(p) * (numerator / n))
    return fsum(terms) / sqrt(y)


if __name__ == "__main__":
    scales = (10**4, 10**8, 10**12)
    primes = primes_up_to(isqrt(4*max(scales)))
    assert normalized_square_sum(2, primes) == log(2)/sqrt(2)
    print("y,Q2(y)/sqrt(y),difference_from_limit")
    for y in scales:
        value = normalized_square_sum(y, primes)
        print(f"{y},{value:.9f},{value - (6*sqrt(2)-8):+.9f}")
