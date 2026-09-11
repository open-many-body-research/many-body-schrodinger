"""Outward dyadic intervals for certifying Gaussian-integral calculations.

All load-bearing arithmetic is Python integer arithmetic.  An interval stores two
integers divided by 2**bits; every operation rounds its lower endpoint down and
its upper endpoint up.  Float input is deliberately rejected.  This is an
executable rational-arithmetic certificate implementation, not a Lean proof.

Proof notes
-----------
* +, -, *, / use exact endpoint formulas followed by floor/ceiling.  Division
  rejects an interval containing zero.  sqrt uses isqrt(endpoint * 2**bits),
  with an extra unit for a non-square upper endpoint.
* pi uses Machin's identity pi=16 atan(1/5)-4 atan(1/239).  The alternating
  arctangent series has decreasing positive term magnitudes.  The first omitted
  term bounds the remainder.  All computed terms and sums are intervals.
* exp_neg(x) encloses exp(-x) for x>=0.  Range reduction puts y=x/2**k in [0,1].
  Taylor's theorem bounds the signed remainder after degree n by
  y**(n+1)/(n+1)!.  Repeated interval squaring restores exp(-x).  For x>=bits,
  0<=exp(-x)<=2**(-bits), using e>=2 and monotonicity.
* Boys F0(T)=integral_0^1 exp(-T*u*u) du is decreasing for T>=0.  Through
  T<=256, integrate the Taylor polynomial; the degree-n remainder is bounded
  by T**(n+1)/((n+1)!*(2*n+3)), with alternating sign.  For T>256,
      sqrt(pi)/(2 sqrt(T))-exp(-T)/(2T) <= F0(T)
          <= sqrt(pi)/(2 sqrt(T)).
  This follows from integral_z^infinity exp(-u*u)du <= exp(-z*z)/(2z), z>0,
  obtained by replacing 1 by u/z under the positive integral.
* At non-point arguments, monotonicity selects endpoint evaluations.  Clipping
  exp_neg and F0 to [0,1] uses their integral/exponential definitions.

Extra working precision reduces cancellation, but validity does not depend on
an informal rounding-error estimate: every intermediate value is enclosed.
For Boys F0 above 256 the analytic tail bound can dominate the interval width.
Use .width to inspect that width; no function silently claims a requested error.

Public API: Interval, interval, sqrt, exp_neg, boys_f0, pi, set_precision.
Default precision is 512 fractional bits.  Interval endpoints .lo/.hi and
.midpoint/.width are exact Fraction values.  .decimal() is display only.
"""

from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
from math import isqrt
from typing import Union


PRECISION = 512
Scalar = Union[int, str, Fraction]


def set_precision(bits: int) -> None:
    """Set precision for newly created intervals; existing ones keep theirs."""
    if not isinstance(bits, int) or isinstance(bits, bool) or bits < 32:
        raise ValueError("precision must be an integer >= 32")
    global PRECISION
    PRECISION = bits


def _fraction(value: Scalar) -> Fraction:
    if isinstance(value, float):
        raise TypeError("float inputs are forbidden; use int, Fraction, or string")
    if isinstance(value, (int, str, Fraction)):
        return Fraction(value)
    raise TypeError(f"unsupported exact scalar type: {type(value).__name__}")


def _floor_scaled(value: Fraction, bits: int) -> int:
    return (value.numerator << bits) // value.denominator


def _ceil_scaled(value: Fraction, bits: int) -> int:
    return -((-value.numerator << bits) // value.denominator)


def _ceildiv(numerator: int, denominator: int) -> int:
    return -((-numerator) // denominator)


class Interval:
    """Closed real interval with outward-rounded dyadic endpoints."""

    __slots__ = ("_lo", "_hi", "bits")

    def __init__(self, lo: Union[Scalar, "Interval"], hi: Scalar | None = None,
                 *, bits: int | None = None):
        if isinstance(lo, Interval):
            if hi is not None:
                raise TypeError("an Interval argument cannot have a second endpoint")
            p = lo.bits if bits is None else bits
            a, b = lo.lo, lo.hi
        else:
            p = PRECISION if bits is None else bits
            a = _fraction(lo)
            b = a if hi is None else _fraction(hi)
        if not isinstance(p, int) or isinstance(p, bool) or p < 32:
            raise ValueError("precision must be an integer >= 32")
        if a > b:
            raise ValueError("lower endpoint exceeds upper endpoint")
        self._lo = _floor_scaled(a, p)
        self._hi = _ceil_scaled(b, p)
        self.bits = p

    @classmethod
    def _from_scaled(cls, lo: int, hi: int, bits: int) -> "Interval":
        if lo > hi:
            raise ArithmeticError("invalid interval bounds")
        result = object.__new__(cls)
        result._lo, result._hi, result.bits = lo, hi, bits
        return result

    @classmethod
    def point(cls, value: Scalar, *, bits: int | None = None) -> "Interval":
        """Enclose an exact scalar (not necessarily exactly dyadic)."""
        return cls(value, bits=bits)

    @property
    def lo(self) -> Fraction:
        return Fraction(self._lo, 1 << self.bits)

    @property
    def hi(self) -> Fraction:
        return Fraction(self._hi, 1 << self.bits)

    @property
    def midpoint(self) -> Fraction:
        return Fraction(self._lo + self._hi, 1 << (self.bits + 1))

    @property
    def mid(self) -> Fraction:
        return self.midpoint

    @property
    def width(self) -> Fraction:
        return Fraction(self._hi - self._lo, 1 << self.bits)

    @property
    def radius(self) -> Fraction:
        return Fraction(self._hi - self._lo, 1 << (self.bits + 1))

    @property
    def is_point(self) -> bool:
        return self._lo == self._hi

    def contains(self, value: Scalar) -> bool:
        q = _fraction(value)
        return self.lo <= q <= self.hi

    def __contains__(self, value: Scalar) -> bool:
        return self.contains(value)

    def with_precision(self, bits: int) -> "Interval":
        return Interval(self, bits=bits)

    def _align(self, other: Union[Scalar, "Interval"]):
        b = other if isinstance(other, Interval) else Interval(other, bits=self.bits)
        p = max(self.bits, b.bits)
        return (self._lo << (p - self.bits), self._hi << (p - self.bits),
                b._lo << (p - b.bits), b._hi << (p - b.bits), p)

    def __add__(self, other: Union[Scalar, "Interval"]) -> "Interval":
        a, b, c, d, p = self._align(other)
        return self._from_scaled(a + c, b + d, p)

    __radd__ = __add__

    def __neg__(self) -> "Interval":
        return self._from_scaled(-self._hi, -self._lo, self.bits)

    def __sub__(self, other: Union[Scalar, "Interval"]) -> "Interval":
        a, b, c, d, p = self._align(other)
        return self._from_scaled(a - d, b - c, p)

    def __rsub__(self, other: Scalar) -> "Interval":
        return -self + other

    def __mul__(self, other: Union[Scalar, "Interval"]) -> "Interval":
        a, b, c, d, p = self._align(other)
        products = (a * c, a * d, b * c, b * d)
        scale = 1 << p
        return self._from_scaled(min(products) // scale,
                                 _ceildiv(max(products), scale), p)

    __rmul__ = __mul__

    def __truediv__(self, other: Union[Scalar, "Interval"]) -> "Interval":
        a, b, c, d, p = self._align(other)
        if c <= 0 <= d:
            raise ZeroDivisionError("divisor interval contains zero")
        numerators = (a << p, b << p)
        lowers = [n // den for n in numerators for den in (c, d)]
        uppers = [_ceildiv(n, den) for n in numerators for den in (c, d)]
        return self._from_scaled(min(lowers), max(uppers), p)

    def __rtruediv__(self, other: Scalar) -> "Interval":
        return Interval(other, bits=self.bits) / self

    def square(self) -> "Interval":
        a, b, p = self._lo, self._hi, self.bits
        low = 0 if a <= 0 <= b else min(a * a, b * b)
        high = max(a * a, b * b)
        return self._from_scaled(low // (1 << p),
                                 _ceildiv(high, 1 << p), p)

    def __pow__(self, exponent: int) -> "Interval":
        if not isinstance(exponent, int):
            raise TypeError("only integer powers are supported")
        if exponent < 0:
            return 1 / (self ** (-exponent))
        result = Interval(1, bits=self.bits)
        base = self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent >>= 1
            if exponent:
                base = base.square()
        return result

    def __abs__(self) -> "Interval":
        if self._lo >= 0:
            return self
        if self._hi <= 0:
            return -self
        return self._from_scaled(0, max(-self._lo, self._hi), self.bits)

    def sqrt(self) -> "Interval":
        if self._lo < 0:
            raise ValueError("sqrt requires a nonnegative interval")
        lower = isqrt(self._lo << self.bits)
        upper_squared = self._hi << self.bits
        upper = isqrt(upper_squared)
        if upper * upper != upper_squared:
            upper += 1
        return self._from_scaled(lower, upper, self.bits)

    def exp_neg(self) -> "Interval":
        if self._lo < 0:
            raise ValueError("exp_neg requires a nonnegative interval")
        lower = _exp_neg_scalar(self.hi, self.bits)._lo
        upper = _exp_neg_scalar(self.lo, self.bits)._hi
        return self._from_scaled(lower, upper, self.bits)

    def boys_f0(self) -> "Interval":
        if self._lo < 0:
            raise ValueError("Boys F0 requires a nonnegative interval")
        lower = _boys_scalar(self.hi, self.bits)._lo
        upper = _boys_scalar(self.lo, self.bits)._hi
        return self._from_scaled(lower, upper, self.bits)

    def decimal(self, digits: int = 20) -> str:
        """Display-only decimal approximation; .lo/.hi remain authoritative."""
        with localcontext() as ctx:
            ctx.prec = digits
            scale = Decimal(1 << self.bits)
            return f"[{Decimal(self._lo) / scale}, {Decimal(self._hi) / scale}]"

    def __repr__(self) -> str:
        return f"Interval({self.lo!r}, {self.hi!r}, bits={self.bits})"


def interval(value: Union[Scalar, Interval], hi: Scalar | None = None,
             *, bits: int | None = None) -> Interval:
    return Interval(value, hi, bits=bits)


def sqrt(value: Union[Scalar, Interval], *, bits: int | None = None) -> Interval:
    return Interval(value, bits=bits).sqrt()


def exp_neg(value: Union[Scalar, Interval], *, bits: int | None = None) -> Interval:
    return Interval(value, bits=bits).exp_neg()


def boys_f0(value: Union[Scalar, Interval], *, bits: int | None = None) -> Interval:
    return Interval(value, bits=bits).boys_f0()


def _unit_clip(value: Interval) -> Interval:
    """Intersect with [0,1], for functions mathematically known to lie there."""
    return Interval._from_scaled(max(0, value._lo),
                                 min(1 << value.bits, value._hi), value.bits)


def _alternating_remainder(partial: Interval, next_term: Interval,
                           degree: int) -> Interval:
    # Sign of remainder after degree n is (-1)**(n+1).
    if degree & 1:
        return Interval._from_scaled(partial._lo,
                                     partial._hi + next_term._hi, partial.bits)
    return Interval._from_scaled(partial._lo - next_term._hi,
                                 partial._hi, partial.bits)


@lru_cache(maxsize=8192)
def _exp_neg_scalar(x: Fraction, bits: int) -> Interval:
    if x < 0:
        raise ValueError("negative exponential argument")
    if x == 0:
        return Interval(1, bits=bits)
    if x >= bits:
        return Interval._from_scaled(0, 1, bits)
    k = 0
    y = x
    while y > 1:
        y /= 2
        k += 1
    working = bits + 2 * k + 48
    y_i = Interval(y, bits=working)
    term = total = Interval(1, bits=working)
    tail_threshold = 1 << (working - (bits + k + 16))
    n = 0
    while True:
        next_term = term * y_i / (n + 1)
        if next_term._hi <= tail_threshold:
            result = _unit_clip(_alternating_remainder(total, next_term, n))
            break
        n += 1
        total = total - next_term if n & 1 else total + next_term
        term = next_term
        if n > 10000:
            raise ArithmeticError("exponential series enclosure failed to contract")
    for _ in range(k):
        result = _unit_clip(result.square())
    return result.with_precision(bits)


@lru_cache(maxsize=64)
def _pi_cached(bits: int) -> Interval:
    working = bits + 32

    def arctan_inverse(q: int) -> Interval:
        total = Interval(0, bits=working)
        power = q
        n = 0
        threshold = Fraction(1, 1 << (bits + 16))
        while True:
            term = Interval(Fraction(1, (2 * n + 1) * power), bits=working)
            total = total - term if n & 1 else total + term
            next_n = n + 1
            power *= q * q
            tail = Fraction(1, (2 * next_n + 1) * power)
            if tail <= threshold:
                return _alternating_remainder(total, Interval(tail, bits=working), n)
            n = next_n

    return (16 * arctan_inverse(5) - 4 * arctan_inverse(239)).with_precision(bits)


def pi(*, bits: int | None = None) -> Interval:
    """Enclose pi using rational alternating series and Machin's identity."""
    return _pi_cached(PRECISION if bits is None else bits)


@lru_cache(maxsize=8192)
def _boys_scalar(t: Fraction, bits: int) -> Interval:
    if t < 0:
        raise ValueError("negative Boys argument")
    if t == 0:
        return Interval(1, bits=bits)
    if t > 256:
        # Extra bits tighten operations, but the analytic erfc-tail bound is
        # deliberately retained in the returned interval, never discarded.
        working = bits + 32
        t_i = Interval(t, bits=working)
        central = pi(bits=working).sqrt() / (2 * t_i.sqrt())
        tail = _exp_neg_scalar(t, working) / (2 * t_i)
        result = Interval._from_scaled(central._lo - tail._hi,
                                       central._hi, working)
        return _unit_clip(result).with_precision(bits)
    cancellation_bits = _ceildiv(2 * t.numerator, t.denominator)
    working = bits + cancellation_bits + 64
    t_i = Interval(t, bits=working)
    term = total = Interval(1, bits=working)
    threshold = 1 << (working - (bits + 16))
    monotone_start = _ceildiv(t.numerator, t.denominator)
    n = 0
    while True:
        next_term = term * t_i * (2 * n + 1) / ((n + 1) * (2 * n + 3))
        if n >= monotone_start and next_term._hi <= threshold:
            return _unit_clip(_alternating_remainder(total, next_term, n)).with_precision(bits)
        n += 1
        total = total - next_term if n & 1 else total + next_term
        term = next_term
        if n > 10000:
            raise ArithmeticError("Boys series enclosure failed to contract")


def run_self_tests() -> None:
    """Compare interval code with independent exact-rational computations.

    No decimal or floating-point reference values are used in assertions.
    Taylor references retain every term as a Fraction and use extra accuracy;
    they have neither dyadic roundoff nor the exponential range reduction used
    by the production implementation.  The pi reference uses a different
    identity, pi=4*(atan(1/2)+atan(1/3)).  These tests validate the executable
    arithmetic but do not machine-formalize the analytic identities.
    """
    assert (Interval(Fraction(1, 3)) + Interval(Fraction(2, 3))).contains(1)
    assert (Interval(-2, 3).square()).lo == 0
    assert sqrt(4).contains(2) and sqrt(4).width == 0
    assert sqrt(2).lo ** 2 <= 2 <= sqrt(2).hi ** 2
    assert exp_neg(0).contains(1) and boys_f0(0).contains(1)
    assert exp_neg(1024).lo == 0 and exp_neg(1024).hi == Fraction(1, 1 << PRECISION)
    assert Fraction(314159, 100000) < pi().lo < pi().hi < Fraction(314160, 100000)
    print("PASS exact identities, square-root enclosure, exponential tail cutoff")

    pairs = [(Fraction(-7, 3), Fraction(-4, 7)),
             (Fraction(-3, 2), Fraction(5, 9)),
             (Fraction(0), Fraction(11, 13)),
             (Fraction(2, 7), Fraction(19, 5))]
    count = 0
    for a, b in pairs:
        x_i = Interval(a, b)
        for c, d in pairs:
            y_i = Interval(c, d, bits=PRECISION + 11)
            for x in (a, (a + b) / 2, b):
                for y in (c, (c + d) / 2, d):
                    assert (x_i + y_i).contains(x + y)
                    assert (x_i - y_i).contains(x - y)
                    assert (x_i * y_i).contains(x * y)
                    if not c <= 0 <= d:
                        assert (x_i / y_i).contains(x / y)
                    count += 1
    print("PASS rational endpoint/interior arithmetic checks:", count)

    try:
        Interval(0.1)
        raise AssertionError("float input was accepted")
    except TypeError:
        pass
    try:
        Interval(1) / Interval(-1, 1)
        raise AssertionError("division by a zero-containing interval was accepted")
    except ZeroDivisionError:
        pass
    try:
        sqrt(Interval(-1, 1))
        raise AssertionError("negative sqrt interval was accepted")
    except ValueError:
        pass
    print("PASS rejection of inexact input and invalid domains")

    def alternating_atan(q: int):
        total = Fraction(0)
        power = q
        k = 0
        bound = Fraction(1, 1 << (PRECISION + 100))
        while True:
            total += (-1) ** k * Fraction(1, (2 * k + 1) * power)
            power *= q * q
            tail = Fraction(1, (2 * k + 3) * power)
            if tail < bound:
                return (total, total + tail) if k & 1 else (total - tail, total)
            k += 1

    a_low, a_high = alternating_atan(2)
    b_low, b_high = alternating_atan(3)
    pi_ref_lo, pi_ref_hi = 4 * (a_low + b_low), 4 * (a_high + b_high)
    pi_i = pi()
    assert pi_i.lo <= pi_ref_lo <= pi_ref_hi <= pi_i.hi
    assert pi_i.width <= Fraction(2, 1 << PRECISION)
    print("PASS pi: independent rational atan(1/2)+atan(1/3) enclosure")

    def rational_taylor(t: Fraction, boys: bool):
        # Exact direct power series; no interval rounding or range reduction.
        factorial_term = Fraction(1)
        total = Fraction(1)
        n = 0
        target = Fraction(1, 1 << (PRECISION + 100))
        while True:
            factorial_term *= t / (n + 1)
            remainder = factorial_term / (2 * n + 3) if boys else factorial_term
            if n > t and remainder < target:
                return (total, total + remainder) if n & 1 else (total - remainder, total)
            n += 1
            term = factorial_term / (2 * n + 1) if boys else factorial_term
            total += -term if n & 1 else term

    for argument in (Fraction(1, 2), Fraction(17, 23), Fraction(1), Fraction(3),
                     Fraction(32), Fraction(256), Fraction(257)):
        for fn, use_boys, name in ((exp_neg, False, "exp_neg"),
                                   (boys_f0, True, "boys_f0")):
            answer = fn(argument)
            ref_lo, ref_hi = rational_taylor(argument, use_boys)
            assert answer.lo <= ref_lo <= ref_hi <= answer.hi, (name, argument)
            print("PASS independent exact-rational Taylor reference:", name, argument)

    for fn in (exp_neg, boys_f0):
        wide = fn(Interval(Fraction(1, 2), Fraction(3, 2)))
        left, right = fn(Fraction(1, 2)), fn(Fraction(3, 2))
        assert wide.lo == right.lo and wide.hi == left.hi
    print("PASS monotone endpoint evaluation for non-point arguments")
    print("Display-only decimal approximations follow; assertions above are rational.")
    print("pi:", pi_i.decimal(30))
    for point in (0, 1, 32, 256, 257, 1024, 10 ** 51):
        b = boys_f0(point)
        print("Boys F0 at", point, b.decimal(30), "width < 2^-100:", b.width < Fraction(1, 1 << 100))
    print("ALL CERTIFIED-INTERVAL SELF-TESTS PASSED")


if __name__ == "__main__":
    run_self_tests()
