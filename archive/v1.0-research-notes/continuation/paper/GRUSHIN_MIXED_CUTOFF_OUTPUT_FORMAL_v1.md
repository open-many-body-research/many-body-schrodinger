> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual mixed weak cutoff output estimate, version 1

This checkpoint establishes the operator-output side of the factorial recurrence for
`P_c = -Delta_Y - c |Y|^2 Delta_T` on the actual seven-dimensional product Lebesgue
space. The potential B is real and the solution and forcing are complex. This is a
Lean-verified conditional analytic estimate; no numerical algorithm is asserted.

Let Omega_t be the coordinate box with Y/T half-widths aY-t and aT-t, centered at a
with a.Y=0. Let e>0, t+e<=rho<min(aY,aT). The actual smooth cutoff is
`factorialRectCutoff a aY aT t e`, equal to one on Omega_(t+e), supported compactly
inside Omega_t, and valued in [0,1]. Its derivative constants C1,C2 are bounds for
the actual Mathlib smooth transition and its second derivative. The paper quintic
constants are not substituted.

Assume an actual natural weak derivative family F through order r+2 on Omega_t,
r>=2, with one finite region L2 budget and genuine Y/T weak shift identities.
Assume only the original equation `(P_c+B) F(0,0)=src`, with B and src smooth on
Omega_t. For each coordinate word w of length at most r, assume
`|D_w B| <= M A^|w| |w|!`, M,A>=0. Let N(k)>=0 bound the actual shifted 498-component
outer L2 norm at every base index of cost at most k, for k<=r-1; the exact cost is
`|alpha|+|beta|+min(|alpha|,4)`. Let the actual source derivative at (alpha,beta) have
restricted L2 norm at most S0 and its cost be at most r.

The theorem `factorial_mixed_cutoff_output_bound` constructs an actual global
compact weak H2 vector U=chi F(alpha,beta), all first and ordered second weak jets,
and its actual global L2 principal output H=P_c U. It proves

    ||H|| <= S0
      + M sum_(j=1)^r choose(r,j) A^j j! N(r-j)
      + 6 |c| r N(r-1) + 3 |c| r(r-1) N(r-2)
      + M N(r-1) + (K1/e) N(r-1) + (K2/e^2) N(r-2),

where

    K1 = (8/3) C1 [8/(aY-rho)^2 + 6 |c|],
    K2 = (32/9) (C2+C1^2) [4/(aY-rho)^2 + 3 |c|].

No H2 premise or positive-order PDE premise occurs in this final theorem. Local H2
is reconstructed from genuine diagonal weak jets. An auxiliary outer plateau
constructs global representatives; local weak uniqueness identifies their actual
first derivatives. Consequently the proved global source formula is

    H = chi [mixedMultiIndexGrushinSource - B F(alpha,beta)]
        - rawGrushinCutoffError.

The raw cutoff error is the negative of [P_c,chi]F. The differentiated source has
already been identified as the ordinary source derivative minus the actual
potential proper Leibniz sum plus the exact quadratic principal commutator.
All integrability and zero-extension norm transfers are proved. Indicators are
used solely to compare L2 classes and are never differentiated.

The finite derivative budget V0 does not enter the displayed bound. It licenses
actual derivatives and test manipulations; lower outer norms remain the explicit
quantitative inputs. These premises can be supplied by the separately proved raw
PDE all-order family and actual finite profile constructions. This checkpoint
itself does not prove the full profile recurrence, factorial bounds, analyticity,
the open approximation lemma, or Theorem T. The remaining composition is the
compact maximal graph estimate and the inner plateau comparison, followed by the
scalar recurrence argument.

Five modules and eleven declarations passed strict v7 expanded-statement and axiom
audits. All final expanded outputs were read. Only propext, Classical.choice and
Quot.sound occur. Pinned dependency objects were reused; this is outside the prior
isolated v20 source rebuild. All PASS bytes and failed logs are preserved.
