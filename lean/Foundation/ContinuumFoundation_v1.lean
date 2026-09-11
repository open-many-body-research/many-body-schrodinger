import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

/-!
Faithful continuum definitions and structural lemmas, version 1.

This file does not assert Coulomb self-adjointness, H2-domain equality for an
operator constructed by another method, a spectral separator, approximation,
or Theorem T. The operator is specified by its weak-derivative graph, and the
ground energy below is a variational infimum in EReal, not an asserted spectral
minimum. No mathematical premise is hidden in an assumed structure.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace ContDiff

namespace TheoremT.Continuum

abbrev Coordinate (N : ℕ) := Fin N × Fin 3
abbrev Configuration (N : ℕ) := EuclideanSpace ℝ (Coordinate N)
abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev SpinConfiguration (N : ℕ) := Fin N → Fin 2
abbrev SpatialL2 (N : ℕ) := Lp ℂ 2 (volume : Measure (Configuration N))
/-- Counting measure in spin, Lebesgue measure in physical configuration space. -/
abbrev SpinSpace (N : ℕ) := PiLp 2 (fun _ : SpinConfiguration N => SpatialL2 N)

def position {N : ℕ} (x : Configuration N) (i : Fin N) : Position :=
  WithLp.toLp 2 (fun k => x (i, k))

def coordinatePermutation {N : ℕ} (π : Equiv.Perm (Fin N)) :
    Equiv.Perm (Coordinate N) := Equiv.prodCongr π (Equiv.refl (Fin 3))

/-- The convention is (P_pi x)_i = x_(pi i). -/
def permuteSpace {N : ℕ} (π : Equiv.Perm (Fin N)) :
    Configuration N ≃ₗᵢ[ℝ] Configuration N :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (coordinatePermutation π).symm

theorem permuteSpace_apply {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (i : Fin N) (k : Fin 3) :
    permuteSpace π x (i, k) = x (π i, k) := rfl

def permuteSpin {N : ℕ} (π : Equiv.Perm (Fin N)) (σ : SpinConfiguration N) :
    SpinConfiguration N := σ ∘ π

def permutationSign {N : ℕ} (π : Equiv.Perm (Fin N)) : ℂ :=
  ((Equiv.Perm.sign π : ℤˣ) : ℤ)

def pullback {N : ℕ} (π : Equiv.Perm (Fin N)) : SpatialL2 N →ₗ[ℂ] SpatialL2 N :=
  Lp.compMeasurePreservingₗ ℂ (permuteSpace π) (permuteSpace π).measurePreserving

/-- Actual antisymmetry in the continuum L2 quotient. -/
def fermionicSubspace (N : ℕ) : Submodule ℂ (SpinSpace N) where
  carrier := {ψ | ∀ π σ,
    pullback π (ψ (permuteSpin π σ)) = permutationSign π • ψ σ}
  zero_mem' := by intro π σ; simp
  add_mem' := by
    intro ψ φ hψ hφ π σ
    change pullback π (ψ (permuteSpin π σ) + φ (permuteSpin π σ)) =
      permutationSign π • (ψ σ + φ σ)
    rw [map_add, hψ π σ, hφ π σ, smul_add]
  smul_mem' := by
    intro c ψ hψ π σ
    change pullback π (c • ψ (permuteSpin π σ)) =
      permutationSign π • (c • ψ σ)
    rw [map_smul, hψ π σ, smul_comm]

abbrev FermionicSpace (N : ℕ) := fermionicSubspace N

theorem fermionic_exchange {N : ℕ} (ψ : FermionicSpace N)
    (π : Equiv.Perm (Fin N)) (σ : SpinConfiguration N) :
    pullback π (ψ.val (permuteSpin π σ)) = permutationSign π • ψ.val σ :=
  ψ.property π σ

/-- No softening or finite-dimensional replacement: poles occur at the exact
physical distances. Lean's inverse at zero is a representative convention;
identification modulo the collision null set is a separate obligation. -/
def coulombPotential (N : ℕ) (Z : ℝ) (x : Configuration N) : ℝ :=
  -Z * (∑ i : Fin N, ‖position x i‖⁻¹) +
    ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
      ‖position x i - position x j‖⁻¹

def collisionFree {N : ℕ} (x : Configuration N) : Prop :=
  (∀ i, position x i ≠ 0) ∧ ∀ i j, i ≠ j → position x i ≠ position x j

def coordinateVector {N : ℕ} (k : Coordinate N) : Configuration N := PiLp.single 2 k 1

/-- Distributional first derivative tested against every real C_c^infinity
test function. Complex-valued wavefunctions are integrated as complex vectors. -/
def WeakPartial {N : ℕ} (f g : SpatialL2 N) (k : Coordinate N) : Prop :=
  ∀ φ : Configuration N → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, φ x • g x) = -(∫ x, (fderiv ℝ φ x (coordinateVector k)) • f x)

theorem weakPartial_unique {N : ℕ} {f g h : SpatialL2 N} {k : Coordinate N}
    (hg : WeakPartial f g k) (hh : WeakPartial f h k) : g = h := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp g).locallyIntegrable (by norm_num))
    ((Lp.memLp h).locallyIntegrable (by norm_num))
  intro φ hφ hc
  rw [hg φ hφ hc, hh φ hφ hc]

/-- H1 and H2 are genuine weak Sobolev conditions with L2 derivatives. -/
def HasH1 {N : ℕ} (f : SpatialL2 N) : Prop :=
  ∃ d : Coordinate N → SpatialL2 N, ∀ k, WeakPartial f (d k) k

def HasH2 {N : ℕ} (f : SpatialL2 N) : Prop :=
  ∃ d : Coordinate N → SpatialL2 N,
    (∀ k, WeakPartial f (d k) k) ∧
    ∀ k l, ∃ e : SpatialL2 N, WeakPartial (d k) e l

theorem h2_implies_h1 {N : ℕ} {f : SpatialL2 N} (h : HasH2 f) : HasH1 f := by
  obtain ⟨d, hd, _⟩ := h
  exact ⟨d, hd⟩

/-- The requested H2 fermionic domain, defined independently of image existence. -/
def targetDomain (N : ℕ) : Set (SpinSpace N) :=
  {ψ | ψ ∈ fermionicSubspace N ∧ ∀ σ, HasH2 (ψ σ)}

/-- Scalar Coulomb graph on the H2 domain. All mixed second derivatives are
required; the kinetic term is minus one half the sum of diagonal derivatives. -/
def scalarHamiltonianGraph (N : ℕ) (Z : ℝ) (f h : SpatialL2 N) : Prop :=
  ∃ d : Coordinate N → SpatialL2 N, ∃ e : Coordinate N → Coordinate N → SpatialL2 N,
    (∀ k, WeakPartial f (d k) k) ∧
    (∀ k l, WeakPartial (d k) (e k l) l) ∧
    ∀ᵐ x : Configuration N,
      h x = (-((1 : ℂ) / 2)) * (∑ k, e k k x) +
        (coulombPotential N Z x : ℂ) * f x

theorem scalar_graph_hasH2 {N : ℕ} {Z : ℝ} {f h : SpatialL2 N}
    (hgraph : scalarHamiltonianGraph N Z f h) : HasH2 f := by
  obtain ⟨d, e, hd, he, _⟩ := hgraph
  exact ⟨d, hd, fun k l => ⟨e k l, he k l⟩⟩

theorem scalar_graph_unique {N : ℕ} {Z : ℝ} {f h h' : SpatialL2 N}
    (hgraph : scalarHamiltonianGraph N Z f h)
    (hgraph' : scalarHamiltonianGraph N Z f h') : h = h' := by
  obtain ⟨d, e, hd, he, hv⟩ := hgraph
  obtain ⟨d', e', hd', he', hv'⟩ := hgraph'
  have hfirst : d = d' := funext (fun k => weakPartial_unique (hd k) (hd' k))
  subst d'
  have hsecond : e = e' := funext (fun k => funext (fun l =>
    weakPartial_unique (he k l) (he' k l)))
  subst e'
  apply Lp.ext
  filter_upwards [hv, hv'] with x hx hx'
  exact hx.trans hx'.symm

/-- The full continuum Coulomb Hamiltonian is specified by this graph.
Existence of an output for every input in targetDomain is NOT assumed. -/
def hamiltonianGraph (N : ℕ) (Z : ℝ) (ψ h : SpinSpace N) : Prop :=
  ψ ∈ fermionicSubspace N ∧ h ∈ fermionicSubspace N ∧
    ∀ σ, scalarHamiltonianGraph N Z (ψ σ) (h σ)

theorem graph_input_in_targetDomain {N : ℕ} {Z : ℝ} {ψ h : SpinSpace N}
    (hg : hamiltonianGraph N Z ψ h) : ψ ∈ targetDomain N :=
  ⟨hg.1, fun σ => scalar_graph_hasH2 (hg.2.2 σ)⟩

theorem hamiltonian_graph_unique {N : ℕ} {Z : ℝ} {ψ h h' : SpinSpace N}
    (hg : hamiltonianGraph N Z ψ h) (hg' : hamiltonianGraph N Z ψ h') : h = h' := by
  apply (WithLp.ext_iff 2).mpr
  funext σ
  exact scalar_graph_unique (hg.2.2 σ) (hg'.2.2 σ)

/-- The finite-spin sum of continuum L2 inner products. -/
def rayleighNumerator {N : ℕ} (ψ h : SpinSpace N) : ℝ :=
  ∑ σ, (inner ℂ (ψ σ) (h σ)).re

/-- EReal avoids assigning an arbitrary finite value to an empty or unbounded
numerical range. Its equality to infimum of the spectrum remains unproved. -/
def variationalGroundEnergy (N : ℕ) (Z : ℝ) : EReal :=
  sInf {e | ∃ ψ h : SpinSpace N, ‖ψ‖ = 1 ∧ hamiltonianGraph N Z ψ h ∧
    e = (rayleighNumerator ψ h : EReal)}

theorem variational_ground_le_trial {N : ℕ} {Z : ℝ} {ψ h : SpinSpace N}
    (hn : ‖ψ‖ = 1) (hg : hamiltonianGraph N Z ψ h) :
    variationalGroundEnergy N Z ≤ (rayleighNumerator ψ h : EReal) :=
  sInf_le ⟨ψ, h, hn, hg, rfl⟩

#print axioms permuteSpace_apply
#print axioms fermionic_exchange
#print axioms weakPartial_unique
#print axioms h2_implies_h1
#print axioms scalar_graph_hasH2
#print axioms scalar_graph_unique
#print axioms graph_input_in_targetDomain
#print axioms hamiltonian_graph_unique
#print axioms variational_ground_le_trial

end TheoremT.Continuum
