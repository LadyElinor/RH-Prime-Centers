"""Enclose finite tent spectra and the all-height line budget. python-flint==0.9.0."""
import argparse

from flint import acb, arb, ctx

ctx.prec = 144
half = arb(1) / 2
log2 = arb(2).log()


def window_coefficient(z):
    w = (log2 * z).exp()
    return (w-1)*(w-2)/(z*(z-1))


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def outer_integer(x, direction):
    endpoint = x.lower().floor() if direction == "down" else x.upper().ceil()
    return int(endpoint.unique_fmpz())


def decimal_bound(x, direction):
    scaled = outer_integer(x * 10**6, direction)
    return f"{'-' if scaled < 0 else ''}{abs(scaled)//10**6}.{abs(scaled)%10**6:06d}"


def main(*, lean_inputs=False):
    zeros = acb.zeta_zeros(1, 512)
    require(len(zeros) == 512, "Incomplete zero block")
    last = arb(0)
    for z in zeros:
        require(z.real == half and z.imag > last, "Unresolved zero position")
        last = z.imag
    require(zeros[0].imag > 14, "First ordinate bound did not resolve")
    terms = [(z.imag, window_coefficient(z)) for z in zeros]
    sqrt2 = arb(2).sqrt()
    numerator_max = (1+sqrt2)*(2+sqrt2)
    hadamard = 2 + arb.const_euler() - (4*arb.pi()).log()
    bias = 6*sqrt2 - 8
    # Deduct the Hadamard mass of the known prefix, then pay its actual norm.
    used = arb(0)
    cost = arb(0)
    print("positive zeros | line budget upper | available margin lower")
    for n, (g, h) in enumerate(terms, 1):
        # On the critical line the modulus of the numerator is 3 sqrt(2) - 4 cos(g log 2).
        direct_norm = (3*sqrt2 - 4*(g*log2).cos())/(half**2 + g**2)
        require(abs(h).overlaps(direct_norm), "Independent coefficient norm disagrees")
        used += 2/(half**2 + g**2)
        cost += 2*abs(h)
        if n in (42, 512):
            budget = cost + numerator_max*(hadamard-used)
            require(hadamard-used > 0, "Inconsistent remaining zero mass")
            print(n, decimal_bound(budget, "up"), decimal_bound(bias-budget, "down"))

    print("Y | positive zeros | lower and upper bounds for the spectral minimum")
    for Y in (32, 64, 128):
        count = arb(Y).zeta_nzeros().unique_fmpz()
        require(count is not None, "Unresolved zero count")
        n = int(count)
        require(0 < n < len(terms) and terms[n-1][0] < Y < terms[n][0],
                "Zero intersects the cutoff or enumeration is incomplete")
        subset = terms[:n]
        # q(v) = 2 Re sum h exp(i*g*(log Y + v)), 0 <= v <= log 2.
        bins = 256
        step = log2/bins
        curvature = 2*sum(abs(h)*g**2 for g, h in subset)
        nodes = []
        for j in range(bins + 1):
            u = arb(Y).log() + j*step
            nodes.append(2*sum((h*acb(0,g*u).exp()).real for g,h in subset))
        least = nodes[0]
        for sample in nodes[1:]:
            least = least.min(sample)
        lower = least - curvature*step**2/8
        print(Y, n, decimal_bound(lower, "down"), decimal_bound(least, "up"))
        if lean_inputs:
            # Lower nodal bound A and upper curvature bound M, in billionths.
            a = outer_integer(least * 10**9, "down")
            m = outer_integer(curvature * 10**9, "up")
            print(f"Lean inputs: Y={Y} A={a}/1000000000 M={m}/1000000000")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-inputs", action="store_true", help="print rational grid inputs")
    main(lean_inputs=parser.parse_args().lean_inputs)
