"""Exploratory residual optimization, followed by rational trial coefficients.

This selects a candidate only. All physical claims must be checked afterwards
by check_trial.py.  In particular the fixed target shift is not trusted as an
energy bound and does not appear in that checker's certificate inequalities.
"""
import argparse
import json
import tempfile
import time
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from pathlib import Path

from hylleraas import assemble, h_action, inner
from select_trial import dec, matvec
from check_trial import log2_bounds
from certified_interval import pi


ROOT = Path(__file__).resolve().parent
TARGET = F(-2903724377, 10**9)


def factor_ldl(a):
    n = len(a)
    lower = [[D(0)] * n for _ in range(n)]
    pivots = [D(0)] * n
    for i in range(n):
        lower[i][i] = D(1)
        for j in range(i):
            lower[i][j] = (a[i][j] - sum(
                (lower[i][k] * pivots[k] * lower[j][k] for k in range(j)),
                D(0))) / pivots[j]
        pivots[i] = a[i][i] - sum(
            (lower[i][k]**2 * pivots[k] for k in range(i)), D(0))
        if pivots[i] <= 0:
            raise ArithmeticError(('nonpositive exploratory residual pivot', i, pivots[i]))
    return lower, pivots


def solve_ldl(lower, pivots, rhs):
    n = len(rhs)
    y = []
    for i in range(n):
        y.append(rhs[i] - sum((lower[i][j] * y[j] for j in range(i)), D(0)))
    y = [y[i] / pivots[i] for i in range(n)]
    for i in reversed(range(n)):
        y[i] -= sum((lower[j][i] * y[j] for j in range(i+1, n)), D(0))
    return y


def quadratic(a, v):
    return sum((x*y for x, y in zip(v, matvec(a, v))), D(0))


def check_without_overwrite(path, bits):
    """Reuse the independent checker without overwriting an energy trial's log."""
    from check_trial import check
    with tempfile.TemporaryDirectory(prefix='helium-residual-check-') as directory:
        temporary_trial = Path(directory) / path.name
        temporary_trial.write_text(path.read_text())
        certificate = check(temporary_trial, bits)
    target = ROOT / f'certificate_residual_{certificate["order"]}_{bits}.json'
    target.write_text(json.dumps(certificate, indent=2) + '\n')
    print('residual certificate output', target, flush=True)
    return certificate


def select(order, precision=90, iterations=8, check_bits=None):
    started = time.monotonic()
    entries, sr, hr = assemble(order)
    n = len(entries)
    hs = [h_action(poly) for _, poly in entries]
    print('assembled rational norm/energy', order, n,
          'seconds', time.monotonic()-started, flush=True)
    with localcontext() as ctx:
        ctx.prec = precision
        constant_bits = max(128, precision * 4)
        loglo, loghi = log2_bounds(constant_bits)
        logtwo = dec((loglo + loghi) / 2)
        pic = pi(bits=constant_bits)
        pisquared = dec(pic.midpoint)**2
        diagonal_scale = [dec(sr[i][i]).sqrt() for i in range(n)]
        sm = [[dec(sr[i][j]) / (diagonal_scale[i]*diagonal_scale[j])
               for j in range(n)] for i in range(n)]
        hm = [[dec(hr[i][j]) / (diagonal_scale[i]*diagonal_scale[j])
               for j in range(n)] for i in range(n)]
        h2m = [[D(0)] * n for _ in range(n)]
        for i in range(n):
            for j in range(i+1):
                expr = inner(hs[i], hs[j], F(4))
                value = dec(expr[0]) + dec(expr[1])*logtwo + dec(expr[2])*pisquared
                value /= diagonal_scale[i] * diagonal_scale[j]
                h2m[i][j] = h2m[j][i] = value
            if i % 10 == 0 or i == n-1:
                print('assembled squared-action row', i+1, '/', n,
                      'seconds', time.monotonic()-started, flush=True)
        c = dec(TARGET)
        residual = [[h2m[i][j] - 2*c*hm[i][j] + c*c*sm[i][j]
                     for j in range(n)] for i in range(n)]
        lower, pivots = factor_ldl(residual)
        print('factored residual; smallest pivot', min(pivots),
              'seconds', time.monotonic()-started, flush=True)
        v = [D(1)] + [D(0)] * (n-1)
        previous = ROOT / f'trial_{order}.json'
        if previous.exists():
            old = json.loads(previous.read_text())
            if (old['indices'] == [list(e) for e, _ in entries]
                    and F(old['alpha']) == 2 and F(old['Z']) == 2):
                v = [dec(F(x))*diagonal_scale[i]
                     for i, x in enumerate(old['coefficients'])]
                print('initialized from', previous.name, flush=True)
        for iteration in range(iterations):
            y = solve_ldl(lower, pivots, matvec(sm, v))
            size = max(abs(x) for x in y)
            if not size:
                raise ArithmeticError('zero exploratory inverse-iteration vector')
            v = [x/size for x in y]
            mean = quadratic(hm, v) / quadratic(sm, v)
            variance = quadratic(h2m, v) / quadratic(sm, v) - mean**2
            print('iteration', iteration+1, 'mean', mean, 'variance', variance,
                  'Temple width', variance/(D('-2.5')-mean), flush=True)
        coefficients = [v[i]/diagonal_scale[i] for i in range(n)]
        coefficient_scale = coefficients[0] or max(abs(x) for x in coefficients)
        rational_coefficients = [F(str(x/coefficient_scale)) for x in coefficients]
        data = {
            'order': order, 'dimension': n, 'alpha': '2', 'Z': '2',
            'basis': 'symmetric r^i s^j u^k / (i+j+k)!; i>=j',
            'indices': [list(e) for e, _ in entries],
            'coefficients': [str(x) for x in rational_coefficients],
            'candidate_method': 'minimum squared continuum residual by Decimal inverse iteration',
            'candidate_target_shift': str(TARGET),
            'candidate_target_shift_not_used_for_certification': True,
            'candidate_decimal_precision': precision,
            'candidate_iterations': iterations,
            'candidate_mean_display': str(mean),
            'candidate_variance_display': str(variance),
            'candidate_temple_width_display': str(variance/(D('-2.5')-mean)),
            'candidate_seconds': str(time.monotonic()-started),
        }
    destination = ROOT / f'trial_residual_{order}.json'
    destination.write_text(json.dumps(data, indent=2) + '\n')
    print('rational candidate output', destination,
          'seconds', time.monotonic()-started, flush=True)
    if check_bits is not None:
        check_without_overwrite(destination, check_bits)
    return destination


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('order', type=int)
    parser.add_argument('--precision', type=int, default=90)
    parser.add_argument('--iterations', type=int, default=8)
    parser.add_argument('--check-bits', type=int)
    args = parser.parse_args()
    select(args.order, args.precision, args.iterations, args.check_bits)
