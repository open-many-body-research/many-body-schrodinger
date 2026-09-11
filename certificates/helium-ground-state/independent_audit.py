"""Independent checks of the helium certificate's finite algebra.

This is an implementation audit, not a Lean proof of integration or spectrum.
All comparisons that affect PASS use integers/Fraction or outward intervals.
The reference moment algorithms do not use hylleraas.angular_B or its
polynomial-in-(r-s)/(r+s) recurrence.  They use perimetric variables and an
auxiliary Laplace transform.  Remaining double-singular cases use positive
series with a separately bounded remainder (and are labelled accordingly).
Cartesian jet tests independently differentiate distances in six coordinates.

Run from any directory: python3 helium/independent_audit.py
No large stored trial is integrated and no other certificate is overwritten.
"""

from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial, isqrt
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "gaussian"))
import hylleraas as subject
import check_trial as checker
from certified_interval import Interval, set_precision


def assert_equal(actual, expected, context):
    if actual != expected:
        raise AssertionError((context, actual, expected))


def pure_rational(expression):
    assert expression[1:] == (F(0), F(0)), expression
    return expression[0]


@lru_cache(None)
def perimetric_nonnegative(a, b, c, kappa):
    """I(a,b,c;kappa), a,b,c>=0, by positive octant factorial integrals.

    r=y+z, s=x+z, u=x+y, x,y,z>0, Jacobian=2.
    r+s=x+y+2z.  Expand each nonnegative integer power using the
    binomial theorem and integrate x,y,z separately.
    """
    assert min(a, b, c) >= 0 and kappa > 0
    result = F(0)
    for i in range(a + 1):       # power of y from (y+z)^a
        for j in range(b + 1):   # power of x from (x+z)^b
            for k in range(c + 1):
                nx, ny, nz = j + k, i + c - k, a + b - i - j
                result += (2 * comb(a, i) * comb(b, j) * comb(c, k)
                           * F(factorial(nx), kappa ** (nx + 1))
                           * F(factorial(ny), kappa ** (ny + 1))
                           * F(factorial(nz), (2 * kappa) ** (nz + 1)))
    return result


@lru_cache(None)
def laplace_pair(m, n):
    """Exact coefficients (rational, log2) of J_mn.

    J_mn = integral_0^infinity (t+1)^(-m)(t+2)^(-n) dt.
    J_11=log2; J_m0=1/(m-1); J_0n=2^(1-n)/(n-1).
    For m,n>0, m+n>2, partial fractions give
    J_mn=J_m,n-1 - J_m-1,n.  Each boundary used is convergent.
    """
    assert m >= 0 and n >= 0 and m + n > 1
    if m == n == 1:
        return F(0), F(1)
    if n == 0:
        return F(1, m - 1), F(0)
    if m == 0:
        return F(2) ** (1 - n) / (n - 1), F(0)
    left, right = laplace_pair(m, n - 1), laplace_pair(m - 1, n)
    return left[0] - right[0], left[1] - right[1]


@lru_cache(None)
def perimetric_radial_inverse(b, c, kappa):
    """I(-1,b,c;kappa), b,c>=0, by 1/(y+z) Laplace transform.

    Integrate the positive expanded terms in x,y,z first.  The remaining
    integral is laplace_pair(c-k+1,b-j+1) after t=kappa*v.
    Tonelli applies before the finite partial-fraction evaluation.
    """
    assert min(b, c) >= 0 and kappa > 0
    q, log = F(0), F(0)
    for j in range(b + 1):
        for k in range(c + 1):
            coefficient = (2 * comb(b, j) * comb(c, k)
                           * factorial(j + k) * factorial(c - k)
                           * factorial(b - j) / kappa ** (b + c + 2))
            constant, logarithm = laplace_pair(c - k + 1, b - j + 1)
            q += coefficient * constant
            log += coefficient * logarithm
    return q, log, F(0)


@lru_cache(None)
def perimetric_pair_inverse(a, b, kappa):
    """I(a,b,-1;kappa), a,b>=0, by x+y=w, x=w*t.

    The Jacobian w cancels 1/u=1/w.  Integrals in w,z are factorial
    moments; the t integral is the integer beta integral.
    """
    assert min(a, b) >= 0 and kappa > 0
    result = F(0)
    for i in range(a + 1):
        for j in range(b + 1):
            nz = a + b - i - j
            result += (2 * comb(a, i) * comb(b, j)
                       * F(factorial(i) * factorial(j), i + j + 1)
                       / kappa ** (i + j + 1)
                       * factorial(nz) / (2 * kappa) ** (nz + 1))
    return result


@lru_cache(None)
def positive_angular_enclosure(n, c, terms=1024):
    """Bounds the positive series for the remaining angular integral.

    Expanding 1/(1-x^2), then integrating x^n J_c(x) termwise,
    gives sum_{l>=0} 1/[(n+2l+1)(n+2l+c+2)], including c=-1.
    For l>=K the summand <=1/(n+2l+1)^2.  Its decreasing tail is
    at most the first term plus its integral on [K,infinity):
    1/(n+2K+1)^2 + 1/[2(n+2K+1)].
    """
    assert n >= 0 and n % 2 == 0 and c >= -1 and terms > 0
    lower = sum((F(1, (n + 2*l + 1) * (n + 2*l + c + 2))
                 for l in range(terms)), F(0))
    d = n + 2 * terms + 1
    return lower, lower + F(1, d*d) + F(1, 2*d)


def positive_singular_enclosure(a, b, c, kappa):
    """Separate positive-series check, not an independent coordinate map."""
    assert min(a, b) == -1
    m = max(a, b)
    lower = upper = F(0)
    for j in range((m + 1)//2 + 1):
        lo, hi = positive_angular_enclosure(2*j, c)
        multiplier = 2 * comb(m + 1, 2*j)
        lower += multiplier * lo
        upper += multiplier * hi
    radial = (F(2) ** (-a-b-1) * factorial(a+b+c+2)
              / kappa ** (a+b+c+3))
    return lower * radial, upper * radial


class Jet:
    """Value, six Cartesian first derivatives and Cartesian Laplacian."""
    def __init__(self, value, gradient=None, laplacian=F(0)):
        self.value = F(value)
        self.gradient = tuple(F(v) for v in (gradient or (0,)*6))
        self.laplacian = F(laplacian)

    def __add__(self, other):
        other = other if isinstance(other, Jet) else Jet(other)
        return Jet(self.value+other.value,
                   tuple(a+b for a,b in zip(self.gradient, other.gradient)),
                   self.laplacian+other.laplacian)

    __radd__ = __add__

    def __mul__(self, other):
        other = other if isinstance(other, Jet) else Jet(other)
        return Jet(self.value*other.value,
                   tuple(self.value*b+other.value*a
                         for a,b in zip(self.gradient, other.gradient)),
                   self.value*other.laplacian+other.value*self.laplacian
                   + 2*sum(a*b for a,b in zip(self.gradient, other.gradient)))

    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        result = Jet(1)
        for _ in range(exponent):
            result = result*self
        return result


def integer_norm(vector):
    squared = sum(v*v for v in vector)
    root = isqrt(squared)
    assert root*root == squared and root > 0
    return F(root)


def distance_jets(x, y):
    r, s = integer_norm(x), integer_norm(y)
    difference = tuple(a-b for a,b in zip(x,y))
    u = integer_norm(difference)
    return (Jet(r, tuple(F(a)/r for a in x)+(F(0),)*3, 2/r),
            Jet(s, (F(0),)*3+tuple(F(b)/s for b in y), 2/s),
            Jet(u, tuple(F(a)/u for a in difference)
                +tuple(-F(a)/u for a in difference), 4/u))


def polynomial_value(poly, values):
    return sum((coefficient * values[0]**i * values[1]**j * values[2]**k
                for (i,j,k), coefficient in poly.items()), F(0))


def cartesian_action(poly, x, y, alpha, charge):
    distances = distance_jets(x,y)
    p = sum((coefficient * distances[0]**i * distances[1]**j * distances[2]**k
             for (i,j,k), coefficient in poly.items()), Jet(0))
    t = distances[0]+distances[1]
    gradient_dot = sum(a*b for a,b in zip(t.gradient,p.gradient))
    gradient_square = sum(a*a for a in t.gradient)
    scaled_laplacian = (p.laplacian - 2*alpha*gradient_dot
                        + (alpha**2*gradient_square-alpha*t.laplacian)*p.value)
    r,s,u = (d.value for d in distances)
    return -scaled_laplacian/2+(-charge/r-charge/s+1/u)*p.value


def poly_add(*polys):
    out = {}
    for poly in polys:
        for key, value in poly.items():
            out[key] = out.get(key,F(0))+value
    return {key:value for key,value in out.items() if value}


def poly_scale(poly, coefficient):
    return {key:value*coefficient for key,value in poly.items() if value*coefficient}


def poly_derivative(poly, coordinate):
    out = {}
    for exponents, coefficient in poly.items():
        degree = exponents[coordinate]
        if degree:
            key = list(exponents)
            key[coordinate] -= 1
            out[tuple(key)] = coefficient*degree
    return out


def poly_product(left, right):
    out = {}
    for a, coefficient in left.items():
        for b, factor in right.items():
            key = tuple(x+y for x,y in zip(a,b))
            out[key] = out.get(key,F(0))+coefficient*factor
    return {key:value for key,value in out.items() if value}


def independent_integral(poly,kappa):
    return sum((coefficient * perimetric_nonnegative(i+1,j+1,k+1,kappa)
                for (i,j,k),coefficient in poly.items()),F(0))


def gradient_energy(left, right, alpha, charge):
    """Bilinear kinetic form + Coulomb potential, with independent moments.

    The off-diagonal distance metric entries are Cr/2 and Cs/2.
    The kinetic form has another prefactor 1/2.  This reference does not
    apply the Laplacian/H_action to either polynomial.
    """
    dl = [poly_derivative(left,i) for i in range(3)]
    dr = [poly_derivative(right,i) for i in range(3)]
    for i in (0,1):
        dl[i] = poly_add(dl[i], poly_scale(left,-alpha))
        dr[i] = poly_add(dr[i], poly_scale(right,-alpha))
    kinetic = poly_add(*(poly_scale(poly_product(dl[i],dr[i]),factor)
                        for i,factor in enumerate((F(1,2),F(1,2),F(1)))))
    cr = {(1,0,-1):F(1),(-1,0,1):F(1),(-1,2,-1):F(-1)}
    cs = {(0,1,-1):F(1),(0,-1,1):F(1),(2,-1,-1):F(-1)}
    for index,cross in ((0,cr),(1,cs)):
        pair = poly_add(poly_product(dl[index],dr[2]),
                        poly_product(dl[2],dr[index]))
        kinetic = poly_add(kinetic,poly_scale(poly_product(cross,pair),F(1,4)))
    potential = {(-1,0,0):-charge,(0,-1,0):-charge,(0,0,-1):F(1)}
    combined = poly_add(kinetic,poly_product(potential,poly_product(left,right)))
    return independent_integral(combined,2*alpha)


def alternating_log2_enclosure(terms):
    assert terms > 0 and terms % 2 == 0
    lower = sum((F(1 if k%2 else -1,k) for k in range(1,terms+1)),F(0))
    return lower,lower+F(1,terms+1)


def require_raises(exception, function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except exception:
        return
    raise AssertionError(('expected rejection',function.__name__,args,kwargs))


def check_exact_trial_schema(path, raw=None):
    """Read mathematical input fields with the hardened parsing contract.

    This does not form/integrate the trial or run the expensive checker.
    Indices are independently checked as integer triples in canonical order.
    """
    raw = path.read_bytes() if raw is None else raw
    data = json.loads(raw,parse_float=checker.reject_float)
    assert type(data['order']) is int and data['order'] >= 0
    alpha = checker.exact_fraction(data['alpha'])
    charge = checker.exact_fraction(data['Z'])
    assert alpha > 0 and charge == 2
    indices = data['indices']
    assert all(isinstance(e,list) and len(e)==3
               and all(type(v) is int for v in e) for e in indices)
    # Compute the index list only; no polynomial, moment or matrix is formed.
    expected = []
    for degree in range(data['order']+1):
        for k in range(degree+1):
            for j in range((degree-k)//2+1):
                expected.append([degree-k-j,j,k])
    assert indices == expected
    coefficients = [checker.exact_fraction(c) for c in data['coefficients']]
    assert len(coefficients) == len(indices) and any(coefficients)
    return data


def run_audit():
    set_precision(512)
    print("Independent helium algebra audit: exact rational comparisons")
    print("No stored large trial integration; no certificate mutation")
    print("Python:",sys.version.replace('\n',' '))
    for source in (HERE/'hylleraas.py',HERE/'check_trial.py',HERE/'THEORY.md',
                   HERE/'independent_audit.py',
                   HERE/'certified_interval.py'):
        print("Source SHA256:",source.name,hashlib.sha256(source.read_bytes()).hexdigest())
    # (1) All nonnegative moments: independent positive perimetric sums.
    count = 0
    kappas = (F(1),F(2),F(7,3))
    for a in range(7):
        for b in range(7):
            for c in range(7):
                for kappa in kappas:
                    actual = pure_rational(subject.moment(a,b,c,kappa))
                    expected = perimetric_nonnegative(a,b,c,kappa)
                    assert_equal(actual,expected,("nonnegative",a,b,c,kappa))
                    count += 1
    print(f"PASS {count} nonnegative moment equalities from perimetric coordinates")
    # (2) Single negative powers, both kinds, with independent exact recurrences.
    count = 0
    for a in range(9):
        for b in range(9):
            for kappa in kappas:
                assert_equal(subject.moment(-1,a,b,kappa),
                             perimetric_radial_inverse(a,b,kappa),
                             ("radial inverse",a,b,kappa))
                assert_equal(subject.moment(a,-1,b,kappa),
                             perimetric_radial_inverse(a,b,kappa),
                             ("symmetric radial inverse",a,b,kappa))
                assert_equal(pure_rational(subject.moment(a,b,-1,kappa)),
                             perimetric_pair_inverse(a,b,kappa),
                             ("pair inverse",a,b,kappa))
                count += 3
    print(f"PASS {count} exact single-negative moment equalities (Laplace/beta integrals)")
    # (3) Double negative powers: no logs/pi in the independent bounds.
    cases = [(-1,b,-1) for b in range(9)] + [(-1,-1,c) for c in range(9)]
    for a,b,c in cases:
        for kappa in kappas:
            lower,upper = positive_singular_enclosure(a,b,c,kappa)
            actual = checker.evaluate(subject.moment(a,b,c,kappa),512)
            assert lower <= actual.lo <= actual.hi <= upper, (a,b,c,kappa)
    print(f"PASS {len(cases)*len(kappas)} double-negative moments inside positive-series enclosures")
    # (4) Exponent admissibility and direct Cartesian differentiation.
    points = (((3,0,0),(0,4,0)),((3,4,0),(-3,4,0)),
              ((1,2,2),(1,-2,2)),((1,0,0),(3,0,0)))
    count = 0
    parameters = ((F(2),F(2)),(F(7,4),F(2)),(F(1,3),F(5,2)))
    for i in range(5):
        for j in range(5):
            for k in range(5):
                poly = {(i,j,k):F((i+1)*(j+2),k+1)}
                for alpha,charge in parameters:
                    action = subject.h_action(poly,alpha,charge)
                    for exponents in action:
                        assert min(exponents) >= -1
                    for x,y in points:
                        values = tuple(d.value for d in distance_jets(x,y))
                        assert_equal(polynomial_value(action,values),
                                     cartesian_action(poly,x,y,alpha,charge),
                                     ("Cartesian",i,j,k,x,y,alpha,charge))
                        count += 1
    print(f"PASS {count} Hamiltonian-action identities by six-variable Cartesian jets")
    # (5) Distinct kinetic-form route with positive perimetric integration.
    polys = [{(i,j,k):F(1)} for i in range(3) for j in range(3) for k in range(3)]
    count = 0
    for idx,left in enumerate(polys):
        for right in (polys[(idx*7+3)%len(polys)],polys[(idx*13+5)%len(polys)]):
            for alpha,charge in parameters[:2]:
                expected = gradient_energy(left,right,alpha,charge)
                actual = pure_rational(subject.inner(left,subject.h_action(right,alpha,charge),2*alpha))
                assert_equal(actual,expected,("energy form",left,right,alpha,charge))
                count += 1
    print(f"PASS {count} energy bilinear forms by independent gradient/perimetric route")
    # (6) Normalization factor: one-particle product integrals on R^3.
    # Full norm of exp[-alpha(r+s)] is (pi/alpha^3)^2.
    for alpha in kappas:
        assert_equal(perimetric_nonnegative(1,1,1,2*alpha),F(1,8)/alpha**6,
                     ("8pi2 Jacobian factor",alpha))
    print("PASS 3 full-space normalization identities checking the common 8*pi^2 factor")
    # (7) Independently bracket the log constant and check directed formatting.
    lo,hi = alternating_log2_enclosure(2048)
    for terms in (16,64,512):
        lower,upper = checker.log2_bounds(terms)
        assert lo < lower < upper < hi
    print("PASS log2 constants lie in an independent alternating-harmonic enclosure")
    count = 0
    for q in (F(-7,3),F(-1,10**20),F(0),F(7,3),F(10**20+1,3)):
        for digits in (0,1,6,12):
            lower = checker.outward_decimal(q,digits)
            upper = checker.outward_decimal(q,digits,True)
            step = F(1,10**digits)
            assert lower <= q <= upper and q-lower < step and upper-q < step
            count += 1
    print(f"PASS {count} directed decimal endpoint checks, including negative values")
    # (8) Hardened mathematical inputs reject floats/bools without integration.
    for value in (True,False,1.25,0.0,None,[],{}):
        require_raises(TypeError,checker.exact_fraction,value)
    for value in (0,-3,7,'0','-7/13','0.125','2'):
        assert_equal(checker.exact_fraction(value),F(value),('exact input',value))
    for source in ('{"alpha":1.25}','{"coefficients":[1e-20]}','{"Z":2.0}'):
        require_raises(TypeError,json.loads,source,parse_float=checker.reject_float)
    # JSON's optional non-finite constants bypass parse_float, but are rejected
    # by exact_fraction when present in a mathematical scalar field.
    for token in ('NaN','Infinity','-Infinity'):
        value = json.loads('{"alpha":'+token+'}',parse_float=checker.reject_float)['alpha']
        require_raises(TypeError,checker.exact_fraction,value)
    print("PASS hardened rational-field parsing: float/bool/nonfinite rejection and exact inputs")
    # (9) Replay only final arithmetic of every saved certificate, not integrals.
    certificates = sorted(HERE.glob("certificate_*.json"))
    modern = legacy = 0
    for path in certificates:
        raw = path.read_bytes()
        data = json.loads(raw,parse_float=checker.reject_float)
        bits = data['interval_bits']
        assert type(bits) is int and bits > 0
        set_precision(bits)
        norm = F(data['norm_without_common_8pi2'])
        numerator = F(data['energy_numerator_without_common_8pi2'])
        mean = F(data['mean'])
        assert norm > 0 and mean == numerator/norm
        h2 = tuple(F(c) for c in data['h2_without_common_8pi2_Q_log2_pi2'])
        derived_variance = (h2[0]/norm-mean**2,h2[1]/norm,h2[2]/norm)
        assert_equal(derived_variance,tuple(F(c) for c in data['variance_Q_log2_pi2']),
                     ('variance arithmetic',path.name))
        variance = checker.evaluate(tuple(F(c) for c in data['variance_Q_log2_pi2']),bits)
        stored_lower,stored_upper = (F(v) for v in data['variance_interval'])
        assert stored_lower == max(F(0),variance.lo)
        assert stored_upper == variance.hi
        assert 0 <= stored_lower <= stored_upper
        beta = F(data['spectral_separator'])
        assert beta == -F(5,2) and mean < beta
        assert_equal(beta-mean,F(data['separator_minus_mean']),('separator difference',path.name))
        lower = mean-stored_upper/(beta-mean)
        assert_equal(lower,F(data['temple_lower_raw']),('Temple arithmetic',path.name))
        assert F(data['ell']) <= lower <= mean <= F(data['u'])
        assert_equal(F(data['u'])-F(data['ell']),F(data['width']),('width',path.name))
        assert type(data['width_at_most_1e_minus_6']) is bool
        assert_equal(F(data['width']) <= F(1,10**6),data['width_at_most_1e_minus_6'],
                     ('width predicate',path.name))
        assert_equal(F(data['ell_decimal']),F(data['ell']),('lower display',path.name))
        assert_equal(F(data['u_decimal']),F(data['u']),('upper display',path.name))
        assert_equal(F(data['width_decimal']),F(data['width']),('width display',path.name))
        trial_path = HERE/data['trial_file']
        assert trial_path.parent == HERE and trial_path.is_file()
        trial_raw = trial_path.read_bytes()
        trial = check_exact_trial_schema(trial_path,trial_raw)
        assert trial['order'] == data['order']
        assert len(trial['indices']) == data['dimension']
        assert F(trial['alpha']) == F(data['alpha']) and F(trial['Z']) == F(data['Z'])
        if 'trial_sha256' in data:
            assert_equal(data['trial_sha256'],hashlib.sha256(trial_raw).hexdigest(),
                         ('trial provenance',path.name))
            assert 'certificate_wall_seconds_display_only' not in data
            modern += 1
            provenance = 'verified trial SHA256, no certificate timing metadata'
        else:
            assert data['order'] < 20, ('final certificate missing trial SHA256',path.name)
            legacy += 1
            provenance = 'LEGACY: no saved trial SHA256'
        print("PASS saved final-arithmetic replay:",path.name,"bits",bits,
              "width",data['width_decimal'],provenance)
        print("Certificate SHA256:",path.name,hashlib.sha256(raw).hexdigest())
    for path in sorted(HERE.glob('trial_*.json')):
        check_exact_trial_schema(path)
    print("PASS all stored trial rational fields, canonical indices and coefficient counts")
    print("Saved certificate coverage:",len(certificates),"total,",modern,
          "hardened-schema certificates,",legacy,"legacy certificates explicitly labelled")
    print("AUDIT PASS: no certificate-breaking discrepancy found in checked algebra")
    print("Paper dependencies remain: continuum weak derivatives/domain, integration identities,")
    print("hydrogenic spectral/min-max comparison, and Temple inequality. This is not a Lean proof.")


if __name__ == '__main__':
    run_audit()
