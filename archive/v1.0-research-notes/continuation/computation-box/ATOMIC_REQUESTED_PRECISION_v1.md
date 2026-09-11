> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Executable gap-free atomic precision wrapper

`atomic_enclose_v1.py` implements the previously proposed full-space localization
recursion using the now implemented general box procedure. The target is the
spectral infimum of the actual fixed-point-nucleus continuum Coulomb Hamiltonian
in the full N-electron fermionic spin-space, including unbound inputs where the
infimum is not attained. Inputs are finite integers N>=0,Z>=1,p>=1; output is a
rational interval of width at most 2^-p. This is a paper-supported computability
construction with executable code, **not Lean implementation verification,
practical performance, novelty or polynomial precision cost**.

The frozen baseline is `TWO_ELECTRON_THEOREM.md`, SHA-256
`7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. This sine/occupation algorithm is a distinct
result, not a completion of its frozen trial dictionary or claimed exponents.

## The continuum localization dependency

The paper proof is §1–2 of the unchanged predecessor
`THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/arbitrary_n/GAP_FREE_COMPUTABILITY_v1.md`,
SHA-256 `18093804ba5070c6ad66767432de1ee04eb76bec52bdbe13ee3e0dfc65f4b1bb`.
It defines E_k as the full-space fermionic form infimum and lambda_k(R) as the
uncut Dirichlet-box infimum, and proves

`min(lambda_k(R),E_(k-1)-kZ/R)-k pi²/(8R²) <= E_k`

`E_k <= min(lambda_k(R),E_(k-1))`.

The proof uses compact-support fermionic form density and a distant extra
electron to establish monotonicity `E_k<=E_(k-1)`, then a Lipschitz IMS partition
and subgroup fermionic slicing for exterior clusters. It does not assume
ground-state existence, binding, a discrete spectral separator or a spectral
gap. The operator/form-spectrum connection remains a classical paper
foundation and a separate Lean obligation.

Consequently, given intervals [a,b] for lambda_k(R) and [c,d] for E_(k-1), the
explicit rational interval

`[min(a,c-kZ/R)-5k/(4R²), min(b,d)]`

contains E_k, using pi²<10. If both source widths are <=epsilon, its width is
at most `epsilon+kZ/R+5k/(4R²)` by the 1-Lipschitz property of minimum.

## Actual iteration and precision shifts

The mathematical recursive call would request particle count k-1 with three
extra precision bits. The code implements this **bottom-up**, avoiding a Python
recursion-depth limit for arbitrarily large finite N.

At level k=1,...,N, define

`p_k=p+3(N-k)`, `epsilon_k=2^(-p_k-3)`,

`R_k=2^(p_k+3) k (Z+1)`.

Begin with the exact E_0 interval [0,0]. Call the implemented general
`BoxEnclose(k,Z,R_k,epsilon_k)`. Its box interval width is <=epsilon_k.
The previous level's precision is p_(k-1)=p_k+3, so its returned width is
<=`2^(-p_k-3)=epsilon_k`. These are checked by exact rational comparisons before
combination.

The explicit radius gives `kZ/R_k<=epsilon_k` and
`5k/(4R_k²)<=epsilon_k`. Therefore each new interval has width <=3epsilon_k,
which is strictly less than 2^-p_k. The code checks that bound after every
combination. At k=N the requested precision is exactly p.

There are exactly N box calls and each box call has the paper finite-termination
proof in `GENERAL_BOX_REQUESTED_WIDTH_v1.md`: fixed clipping/cube/grid parameters
and eventual acceptance of rational row-error bounds as arithmetic precision
increases. Thus the composition is a finite procedure in the stated unbounded
integer/finite-array model. No noncomputable choice or successful-box oracle
remains in the source. The actual libraries and all analytical dependencies
remain unverified in Lean, and finite physical resource limits remain separate.

## Certificates and tests

Every level records its effective precision, radius, epsilon, predecessor
interval, complete box certificate, resulting interval and rational width bound.
Every box certificate includes the full computed finite matrix and all source
hashes. The checker recomputes the entire procedure, compares every matrix and
all energy/parameter fields, and checks the chain of source hashes. It shares
the published implementation and is not a separately verified arithmetic kernel.

The arbitrary-length decimal runtime policy is imported before argument parsing
or certificate serialization. See `ERRATUM_INTEGER_CONVERSION_LIMIT_v1.md` for
the reproduced defect in the earlier default-runtime claim and its new-version
repair. For N=0, no huge precision-dependent power is materialized: the answer
[0,0] has width zero for every finite p. A regression actually executes N=0 with
p=10^5000 and checks exact JSON roundtrip.

The tests additionally check 702 level budgets across N<=12, Z in {1,3,12},
p in {1,4,16}, and k=1,...,N, and 729 combinations of interval centers/widths for
the exact minimum width inequality. These counts describe finite arithmetic
tests; the inequalities above are the paper proof for arbitrary inputs.

No positive-N conservative scheduled full-space call has been executed. The
stored N=3,Z=3,p=1 localization plan is a schedule only. Actual positive-N
evidence is supplied by the separately executed N1/N2/N3 finite stages and full
occupation matrices, which use feasible explicit parameters and report their
achieved widths honestly. Their certificates are not substituted for the
unexecuted scheduled calls.

## Remaining distinction

The prior paper computability reduction was conditional on an unimplemented
BoxEnclose. This continuation supplies inspectable source for the integration,
occupation assembly, requested-width box procedure and localization wrapper,
with paper proofs and finite replay checks. It still does not supply a Lean
theorem linking that source to the physical operator, a formally verified
runtime, a useful large-precision performance guarantee, the original Theorem T,
or an efficient universal many-electron solver.

Commands:

```sh
python3 -B test_atomic_enclose_v1.py
python3 -B atomic_enclose_v1.py plan --N 3 --Z 3 --p 1
python3 -B atomic_enclose_v1.py enclose --N 0 --Z 1 --p 1 --output new_vacuum_certificate.json
python3 -B atomic_enclose_v1.py check --certificate new_vacuum_certificate.json
```
