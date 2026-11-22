"""Numerical diagnostic for core3-window-roadmap.md. Requires mpmath 1.3."""
from decimal import Decimal, localcontext
from fractions import Fraction
from math import isqrt
from mpmath import mp

mp.dps = 40
starts = (32, 64, 128)
limit = 8 * max(starts)
sieve = bytearray([1]) * (limit + 1)
sieve[:2] = b'\0\0'
for p in range(2, isqrt(limit) + 1):
    if sieve[p]:
        for n in range(p * p, limit + 1, p):
            sieve[n] = 0
primes = [p for p in range(2, limit + 1) if sieve[p]]


def weight(t):
    if 1 < t <= 2:
        return 2 * (1 - 1/t)
    if 2 < t < 4:
        return 4/t - 1
    return 0


def transform(s):
    return (2**s - 1) * (2**s - 2) / (s * (s-1))


zeros = []
for k in range(1, 1000):
    rho = mp.zetazero(k)
    if rho.imag >= max(starts):
        break
    zeros.append(rho)
else:
    raise RuntimeError("Increase zero budget")
for rho in zeros[:3]:
    direct = mp.quad(lambda t: weight(t)*t**(rho-1), [1, 2, 4])
    assert abs(direct-transform(rho)) < mp.mpf('1e-32')

print("Y  positive zeros  min D/sqrt(y)  min spectral sum/sqrt(y)  max abs residual/sqrt(y)  spectral grid floor")
for Y in starts:
    terms = [(r, transform(r)) for r in zeros if r.imag < Y]
    rows = []
    for j in range(65):
        y = Y * mp.power(2, mp.mpf(j)/64)
        prime_sum = mp.mpf(0)
        higher = mp.mpf(0)
        for p in primes:
            if p >= 4*y:
                break
            logp = mp.log(p)
            prime_sum += logp*weight(p/y)
            n = p*p
            while n < 4*y:
                higher += logp*weight(n/y)
                n *= p
        deficit = 2*y*mp.log(2) - prime_sum
        spectrum = 2*mp.fsum((h*y**r).real for r,h in terms)
        rows.append((deficit/mp.sqrt(y), spectrum/mp.sqrt(y),
                     abs(deficit-higher-spectrum)/mp.sqrt(y)))
    # In u = log(y/Y), bound the derivative of the normalized finite sum.
    lip = 2*mp.fsum(abs(h*(r-mp.mpf('0.5'))) *
                    max(Y**(r.real-mp.mpf('0.5')), (2*Y)**(r.real-mp.mpf('0.5')))
                    for r,h in terms)
    grid_floor = min(r[1] for r in rows) - lip*mp.log(2)/128
    print(Y, len(terms), *(mp.nstr(x, 9) for x in
          (min(r[0] for r in rows), min(r[1] for r in rows), max(r[2] for r in rows), grid_floor)))

# Independent continuous-interval check using standard-library rational bounds.
# For x = 4y all corners occur at x = p, 2p or 4p. The raw deficit is
# affine between corners, so its minimum occurs at one of these or an endpoint.

with localcontext() as ctx:
    ctx.prec = 36
    bounds = {}
    for p in primes:
        rounded = Decimal(p).ln()
        bounds[p] = Fraction(rounded.next_minus()), Fraction(rounded.next_plus())

print("Y  knots including endpoints  certified lower bound for raw D(y)")
for Y in starts:
    knots = {4*Y, 8*Y}
    knots.update(k*p for p in primes for k in (1, 2, 4) if 4*Y <= k*p <= 8*Y)
    lower = min(Fraction(x,2)*bounds[2][0] -
                sum(weight(Fraction(4*p,x))*bounds[p][1] for p in primes if x < 4*p < 4*x)
                for x in knots)
    milli = (lower*1000).__floor__()
    assert milli > 0
    print(Y, len(knots), f"{milli//1000}.{milli%1000:03}")

root_two = mp.sqrt(2)
bias = 6*root_two - 8
line_bound = (1+root_two)*(2+root_two)*(2+mp.euler-mp.log(4*mp.pi))
print("Square bias, critical-line bound, remaining margin:",
      *(mp.nstr(v, 12) for v in (bias, line_bound, bias-line_bound)))
