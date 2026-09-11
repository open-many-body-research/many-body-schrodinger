> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exact hydrogen radial form bounds on an actual closure domain

This continuation record states the half-line result established by the new
Lean source chain. It is a mathematical form theorem, not a claim that the
three-dimensional or many-electron spectral problem has been completed.

## Model and exact statement

Let \(E=L^2((0,\infty),dr;\mathbb C)\). Let \(D\) be the closure in
\(E\times E\) of the pairs \((\phi,\phi')\) where \(\phi:\mathbb R\to
\mathbb C\) is globally smooth, compactly supported, and has topological
support contained in \((0,\infty)\). The core is already a complex linear
subspace, so this is also the closure of its complex linear span. Write
\(Ju\) and \(dJu\) for the two projections. The value map \(J\) is
injective with dense range. No equivalence with a separately defined Sobolev
trace space is assumed in this statement.

The actual reciprocal multiplier \(Wu=(Ju)/r\) belongs to \(E\) and obeys
\(\|Wu\|\leq2\|dJu\|\). For real \(Z\), define the finite form

\[
q_Z(u)=\frac12\|dJu\|^2-Z\int_0^\infty\frac{|Ju(r)|^2}{r}\,dr.
\]

For every real \(Z>0\), the functions

\[
g_Z(r)=r e^{-Zr},\qquad
s_Z(r)=r(1-Zr/2)e^{-Zr/2}
\]

are the values of nonzero vectors in \(D\). Their normalized values
\(\widehat g_Z,\widehat s_Z\) are orthogonal. Their actual form values
are \(-Z^2/2\) and \(-Z^2/8\), respectively. The normalized form minimum
is \(-Z^2/2\); equality in its homogeneous lower bound holds exactly for
complex multiples of \(g_Z\). The normalized form minimum on the
\(g_Z\)-orthogonal subspace is \(-Z^2/8\), and this complement coefficient
is optimal.

For every \(u\in D\), with no orthogonality assumption,

\[
q_Z(u)\geq-\frac{Z^2}{8}\|Ju\|^2
-\frac{3Z^2}{8}|\langle\widehat g_Z,Ju\rangle|^2.
\]

Consequently a normalized \(Ju\) satisfies the proved ground-line error bound

\[
\|Ju-\langle\widehat g_Z,Ju\rangle\widehat g_Z\|^2
\leq\frac{8}{3Z^2}\left(q_Z(u)+\frac{Z^2}{2}\right).
\]

This error guarantee uses the proved radial complement bound. It does not
infer general wavefunction accuracy from many-electron energy accuracy.

## Proof structure

Actual compact integration by parts gives the weak derivative graph. Local
test separation makes the derivative unique and makes \(J\) injective and
dense. The compact Hardy identity extends by completion; a separate closed
multiplier argument identifies the extension with the literal reciprocal
quotient almost everywhere.

On all of \(D\), set
\(A_Z=dJ-W+ZJ\), \(B_Z=-dJ-W+ZJ\), and
\(C_Z=dJ-2W+(Z/2)J\). The proved identities are

\[
\|A_Zu\|^2=2q_Z(u)+Z^2\|Ju\|^2,
\qquad
\|B_Zu\|^2=\|C_Zu\|^2+\frac{3Z^2}{4}\|Ju\|^2,
\]

together with the complex factor pairing
\(\langle A_Zu,Jv\rangle=\langle Ju,B_Zv\rangle\).
The partner controls the complete domain norm, so its range is closed.
An actual weak ODE classification and a reverse compact-test identity give
\(\operatorname{ran}(B_Z)^\perp=\mathbb Cg_Z\). The proved Hilbert-space
partner transfer therefore yields the radial complement inequality.

Explicit smooth cutoffs place \(g_Z\) in \(D\). Their derivative near the
origin is controlled by the support of a fixed transition derivative, giving
\(|\eta_m'(r)|r\leq C(2+r)\). Both value and derivative converge in
\(L^2\) by proved integrable majorants. The same argument places
\(k_a(r)=r^2e^{-ar}\) in \(D\). For \(a=Z/2\),
\(s_Z=g_a-ak_a\), and actual factor identities give
\(A_{2a}s_Z=-a^2k_a\), \(B_{2a}k_a=-3s_Z\).
Their pairing proves \(a^2\|k_a\|^2=3\|s_Z\|^2\), giving attainment
without an unproved moment calculation. Subtracting the ground component
inside \(D\) gives the general rank-one comparison.

## Exact sources and evidence

The joint endpoint is `lean/HalfLineRadialHydrogenPackage_v1.lean`, with
`hydrogen_radial_form_package` and `hydrogen_radial_closed_factor_package`.
The endpoint imports the independent source branches in one successful Lean
environment. The form minima, equality cases, sharpness, stability and actual
operator graphs also have individual theorem statements in
`HalfLineGroundMinimum_v1`, `HalfLineComplementSharp_v1`,
`HalfLineComplementMinimum_v1`, `HalfLineGroundStability_v1`, and
`HalfLineFactorOperators_v1`.

All claimed final source statements compile with Lean 4.34.0-rc2. The strict
audits print complete expanded statements and complete axiom dependencies;
only `propext`, `Classical.choice`, and `Quot.sound` occur. Successful source
and object hashes are recorded in `logs/halfline/` and the corresponding
`audits/formal_semantics/` receipts. Development checks reused the pinned
dependency object cache; the program's isolated source rebuild is a separate
workstream and is not implied by those cache-based checks.

The first-order factors are represented as actual densely defined closed
`LinearPMap`s in \(E\), with exact domain \(J(D)\) and proved formal
adjoint pairing. Equality with the maximal Hilbert adjoints, a self-adjoint
second-order operator, and identification of these form minima with its
spectrum are separate obligations. Angular decomposition and transfer to
the actual three-dimensional model are also separate. This file makes no
novelty, executable algorithm, certified many-electron numerical output, or
complexity claim.

## Preservation

This is a new continuation artifact. The frozen baseline is
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. No frozen or previously successful source
bytes were changed.
