> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# An elementary odd-parity lower bound for the one-electron H₂⁺ operator

**Status: PROVEN (paper proof and exact rational arithmetic only).** This is a fallback separator ingredient at separation `R=7/5`, not a machine-verified theorem and not a two-electron energy computation. It uses the exact hydrogenic spectral theorem, the spectral theorem for the free kinetic operator, and elementary integral identities. The stronger one-electron Temple construction developed independently by the other agent should be preferred if its integrals are certified; the present argument avoids any nuclear-potential-squared integrals.

The result is

    h restricted to odd inversion parity >= −941/1000,
    h = −Delta/2 − 1/|x−A| − 1/|x−B|,
    A=(0,0,−7/10), B=(0,0,7/10).                      (Theorem)

It supplies the lower bound `−941/500=−1.882` on the two-electron odd–odd noninteracting block. It does not alone bound the other block or prove a two-electron separator.

## 1. Atomic spectral comparison with a retained positive kinetic term

Let `T=−Delta/2`, `q>2`, and let `h_A(q)=T−q/|x−A|`, with the analogous definition at B. Write `f_A=(q³/pi)^(1/2) exp(−q|x−A|)` and similarly for B; these are normalized hydrogenic ground states. Put `P_A=|f_A><f_A|` and `P_B=|f_B><f_B|`.

The hydrogenic ground energy is `−q²/2` and all the other spectral values are at least `−q²/8`. Hence, in quadratic-form order,

    h_A(q) >= −q²/8 I − 3q²/8 P_A.

The exact decomposition

    h = [h_A(q)+h_B(q)]/q + (1−2/q)T

therefore gives

    h >= −q/4 I + cT − (3q/8)(P_A+P_B),
    c=1−2/q>0.                                       (1)

Let inversion mean `x↦−x`; it exchanges the two centers. Put

    S=<f_A,f_B>,
    phi=(f_A−f_B)/sqrt(2(1−S)),
    kappa=(3q/8)(1−S).

For `R>0`, `0<S<1`. On the odd inversion subspace, `P_A+P_B=(1−S)|phi><phi|`. Thus

    h_odd >= −q/4 I + cT − kappa |phi><phi|.           (2)

Dropping `cT` gives an insufficient lower bound. Keeping only its expectation and an unrestricted complement gives a bound near `−0.94527`, also insufficient for the desired fallback. The following positive-operator estimate keeps additional information without computing a resolvent explicitly.

## 2. A two-moment resolvent bound

Let T be any nonnegative self-adjoint operator, and let `phi∈D(T)` be normalized. Define

    t1=<phi,T phi>>0,
    t2=||T phi||²,

and choose `x>0`, `c>=0`. In the spectral probability measure of T associated with phi, Cauchy–Schwarz gives

    t1²
      = [integral sqrt(t/(x+ct)) sqrt(t(x+ct)) dmu(t)]²
      <= [integral t/(x+ct) dmu(t)] * (x t1+c t2).

Since `1/(x+ct)=1/x−(c/x)t/(x+ct)`, it follows that

    <phi,(x+cT)^(-1)phi>
      <= 1/x − c t1²/[x(x t1+c t2)].                 (3)

No third moment is used or assumed. In particular a Coulomb cusp does not create a hidden higher-domain requirement.

Weighted Cauchy–Schwarz also gives, for every vector in the form domain of T,

    |<phi,v>|²
      <= <phi,(x+cT)^(-1)phi> * <v,(x+cT)v>.

Consequently

    kappa * [1/x − c t1²/[x(x t1+c t2)]] <= 1

implies `cT−kappa|phi><phi|>=−x I`. All denominators are positive. The sufficient scalar condition is equivalently

    F=x² t1+x(c t2−kappa t1)−kappa c(t2−t1²) >= 0.   (4)

This is the most convenient finite arithmetic certificate. A Lean proof of (4) implying the displayed rational inequality would verify only this scalar rearrangement until the spectral and integral dependencies are also formalized.

## 3. Exact moments for the odd pair of Slater functions

Put `w=qR` and `e=exp(−w)`. Direct integration in prolate coordinates gives

    S=e(1+w+w²/3),
    <f_A,f_B/|x−A|> = q e(1+w),
    <f_A,f_B/(|x−A||x−B|)> = 2q² e.                 (5)

For completeness, in coordinates `mu=(r_A+r_B)/R`, `nu=(r_A−r_B)/R`, the domain is `mu>=1`, `−1<=nu<=1`, and the volume element is

    R³(mu²−nu²)/8 dmu dnu dtheta.

Substitution proves each formula in (5) by polynomial-exponential integration. In the last formula, division by `r_A r_B=R²(mu²−nu²)/4` cancels the polynomial in the Jacobian. The result is `2 pi (q³/pi) R exp(−qR)/(qR)=2q²e`.

The hydrogenic eigenvalue equation gives

    T f_A=(q/r_A−q²/2)f_A.

Using (5) and the diagonal moments `<1/r_A>=q`, `<1/r_A²>=2q²` yields

    <f_A,T f_A>=q²/2,
    <f_A,T f_B>=q²[e(1+w)−S/2],
    ||T f_A||²=5q⁴/4,
    <T f_A,T f_B>=q⁴[e(1−w)+S/4].

Therefore the normalized odd state has exact moments

    t1=q²[(1+S)/2−e(1+w)]/(1−S),
    t2=q⁴[(5−S)/4−e(1−w)]/(1−S).                   (6)

The functions belong to H²; their Laplacians have only locally square-integrable `1/r` singularities. Thus t2 is the legitimate operator second moment `||T phi||²`.

## 4. Rational certificate

Choose

    q=41/20,   R=7/5,   w=287/100,
    c=1/41,    x=857/2000.

To bound e, define the rational finite sums

    P_n=sum_(j=0)^n (−287/100)^j/j!.

Taylor's theorem with its signed remainder gives `P_41<exp(−287/100)<P_40`. Exact rational comparison then gives

    56698926579846 / 10^15 < e < 56698926579847 / 10^15.

Substituting these endpoints into (5)–(6), with outward rational interval operations, gives the following convenient wider rational bounds:

| Quantity | Lower numerator / 10^10 | Upper numerator / 10^10 |
|---|---:|---:|
| S | 3750993086 | 3750993087 |
| t1 | 31481714371 | 31481714372 |
| t2 | 356738977779 | 356738977780 |
| kappa | 4803924064 | 4803924065 |

All entries are positive and the S interval lies strictly below one. If the lower and upper endpoints in the last three rows are denoted `tL,tU,vL,vU,kL,kU`, a conservative lower endpoint for (4) is

    F >= x² tL+x c vL−x kU tU−kU c vU+kL c tL²
       = 1245556719817049970196953907
           /1281250000000000000000000000000
       > 9/10000 > 0.

The numerator of the difference from `9/10000`, over the same positive denominator, is

    92431719817049970196953907.

These checks were executed with Python integer/Fraction arithmetic. They are reproducible exact arithmetic, not a claim that Python or these integral identities have been checked by Lean. Equations (2)–(4) now prove

    h_odd >= −q/4−x
           = −41/80−857/2000
           = −941/1000.

## 5. How this can enter a full two-electron separator

The scalar two-electron Coulomb ground state, when it exists, can be chosen strictly positive and unique by the positivity-improving semigroup theorem. Exchange and simultaneous inversion commute with the scalar operator, so uniqueness and positivity make this spatial state exchange-symmetric and inversion-even. Tensoring with the spin singlet realizes it in the full fermionic space. These are substantive paper-theorem dependencies, not numerical assumptions.

In that spatial symmetry sector, the noninteracting sum `h_1+h_2` splits into gerade–gerade and ungerade–ungerade blocks. The latter is bounded below by `−941/500`. At q=2 the atomic comparison (1), separately in each one-electron parity sector, has only one rank-one exceptional direction below `−1/2`. Therefore the second min-max level in the one-electron gerade sector is at least `−1/2`. If a separate certificate proves that its ground value is at least `ell_g`, the second min-max level of the two-electron noninteracting sum in the exchange-symmetric inversion-even sector is at least

    beta=min(ell_g−1/2, −941/500).

Adding nonnegative electron repulsion preserves this lower bound. Thus, for example, `ell_g>=−1382/1000` would give `beta=−941/500`. A trial mean below beta could then use Temple in this restricted sector, whose ground energy is the full physical ground energy by the positivity argument above. The statement is conditional on the separate gerade lower certificate and the indicated domain/spectral facts.

The independent one-electron Temple route exploits the same rank-one comparison in **both** parity sectors. A trial below `−1/2` in each sector can produce much stronger ground-value lower bounds than the odd fallback proved here. That route is preferable for numerical two-electron certification because a larger valid beta gives a wider Temple denominator. No unverified numerical variational value is used as a lower bound in this file.
