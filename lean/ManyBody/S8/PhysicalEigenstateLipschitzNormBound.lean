import CoulombLipschitzPointBound_v1
import CoulombSpinLocallyLipschitz_v1
import ScalarCoulombFoundation_v1
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! A norm-uniform local Lipschitz estimate on each fixed physical Coulomb
    eigenspace. The constant is existential and may depend on N, Z, E and
    the chosen compact ball, but never on the eigenfunction. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace ManyBody.S8
open TheoremT.Continuum

private def scalarEigenGraphMap (N : ℕ) (E : ℝ) :
    SpatialL2 N →L[ℂ] SpatialL2 N × SpatialL2 N :=
  (ContinuousLinearMap.id ℂ (SpatialL2 N)).prod
    ((E : ℂ) • ContinuousLinearMap.id ℂ (SpatialL2 N))

private def scalarPhysicalEigenspace (N : ℕ) (Z E : ℝ) :
    Submodule ℂ (SpatialL2 N) :=
  (scalarCoulombGraphSubmodule N Z).comap (scalarEigenGraphMap N E).toLinearMap

private theorem scalarPhysicalEigenspace_graph {N : ℕ} {Z E : ℝ}
    (f : scalarPhysicalEigenspace N Z E) :
    scalarHamiltonianGraph N Z (f : SpatialL2 N) ((E : ℂ) • (f : SpatialL2 N)) :=
  f.property

private theorem scalarPhysicalEigenspace_closed (N : ℕ) (Z E : ℝ) :
    IsClosed (scalarPhysicalEigenspace N Z E : Set (SpatialL2 N)) := by
  have hg := scalarCoulombOperator_closed N Z
  change IsClosed ((scalarCoulombOperator N Z).graph : Set (SpatialL2 N × SpatialL2 N)) at hg
  rw [scalarCoulombOperator_graph] at hg
  exact hg.preimage (scalarEigenGraphMap N E).continuous

private instance scalarPhysicalEigenspace_complete (N : ℕ) (Z E : ℝ) :
    CompleteSpace (scalarPhysicalEigenspace N Z E) :=
  (scalarPhysicalEigenspace_closed N Z E).completeSpace_coe

private def eigenRepresentative {N : ℕ} (hN : 0 < N) (Z E : ℝ)
    (f : scalarPhysicalEigenspace N Z E) : Configuration N → ℂ :=
  Classical.choose (scalar_coulomb_bounded_locally_lipschitz_representative hN
    (scalarPhysicalEigenspace_graph f))

private theorem eigenRepresentative_spec {N : ℕ} (hN : 0 < N) (Z E : ℝ)
    (f : scalarPhysicalEigenspace N Z E) :
    LocallyLipschitz (eigenRepresentative hN Z E f) ∧
    ((f : SpatialL2 N) : Configuration N → ℂ) =ᵐ[volume] eigenRepresentative hN Z E f ∧
    ∀ x, ‖eigenRepresentative hN Z E f x‖ ≤ coulombMoserBoundCoefficient N Z E * ‖f‖ :=
  Classical.choose_spec (scalar_coulomb_bounded_locally_lipschitz_representative hN
    (scalarPhysicalEigenspace_graph f))

private theorem eigenRepresentative_add {N : ℕ} (hN : 0 < N) (Z E : ℝ)
    (f g : scalarPhysicalEigenspace N Z E) :
    eigenRepresentative hN Z E (f + g) =
      fun x => eigenRepresentative hN Z E f x + eigenRepresentative hN Z E g x := by
  have hf := eigenRepresentative_spec hN Z E f
  have hg := eigenRepresentative_spec hN Z E g
  have hfg := eigenRepresentative_spec hN Z E (f + g)
  apply volume.eq_of_ae_eq _ hfg.1.continuous (hf.1.continuous.add hg.1.continuous)
  filter_upwards [hfg.2.1, hf.2.1, hg.2.1, Lp.coeFn_add (f : SpatialL2 N) (g : SpatialL2 N)]
    with x h1 h2 h3 h4
  change ((f : SpatialL2 N) + (g : SpatialL2 N)) x = _ at h1
  rw [← h1, h4]
  simpa only [Pi.add_apply] using congrArg₂ (fun a b : ℂ => a + b) h2 h3

private theorem eigenRepresentative_smul {N : ℕ} (hN : 0 < N) (Z E : ℝ)
    (c : ℂ) (f : scalarPhysicalEigenspace N Z E) :
    eigenRepresentative hN Z E (c • f) =
      fun x => c • eigenRepresentative hN Z E f x := by
  have hf := eigenRepresentative_spec hN Z E f
  have hcf := eigenRepresentative_spec hN Z E (c • f)
  apply volume.eq_of_ae_eq _ hcf.1.continuous (hf.1.continuous.const_smul c)
  filter_upwards [hcf.2.1, hf.2.1, Lp.coeFn_smul c (f : SpatialL2 N)] with x h1 h2 h3
  change (c • (f : SpatialL2 N)) x = _ at h1
  rw [← h1, h3]
  simpa only [Pi.smul_apply] using congrArg (fun a : ℂ => c • a) h2

private def eigenEvaluation {N : ℕ} (hN : 0 < N) (Z E : ℝ) (x : Configuration N) :
    scalarPhysicalEigenspace N Z E →L[ℂ] ℂ :=
  ({ toFun := fun f => eigenRepresentative hN Z E f x
     map_add' := fun f g => congrFun (eigenRepresentative_add hN Z E f g) x
     map_smul' := fun c f => congrFun (eigenRepresentative_smul hN Z E c f) x } :
      scalarPhysicalEigenspace N Z E →ₗ[ℂ] ℂ).mkContinuous
    (coulombMoserBoundCoefficient N Z E)
    (fun f => (eigenRepresentative_spec hN Z E f).2.2 x)

private def ballDifferenceIndex (N : ℕ) (A : ℝ) :=
  {p : Configuration N × Configuration N //
    p.1 ∈ Metric.closedBall 0 A ∧ p.2 ∈ Metric.closedBall 0 A ∧ p.1 ≠ p.2}

private def eigenDifferenceQuotient {N : ℕ} (hN : 0 < N) (Z E A : ℝ)
    (p : ballDifferenceIndex N A) : scalarPhysicalEigenspace N Z E →L[ℂ] ℂ :=
  ((dist p.val.1 p.val.2 : ℝ)⁻¹ : ℂ) •
    (eigenEvaluation hN Z E p.val.1 - eigenEvaluation hN Z E p.val.2)

private theorem eigenDifferenceQuotient_apply_norm {N : ℕ} (hN : 0 < N) (Z E A : ℝ)
    (p : ballDifferenceIndex N A) (f : scalarPhysicalEigenspace N Z E) :
    ‖eigenDifferenceQuotient hN Z E A p f‖ =
      dist (eigenRepresentative hN Z E f p.val.1) (eigenRepresentative hN Z E f p.val.2) /
        dist p.val.1 p.val.2 := by
  simp [eigenDifferenceQuotient, eigenEvaluation, dist_eq_norm, div_eq_mul_inv, mul_comm]

/-- Every fixed physical Coulomb eigenspace has a local Lipschitz estimate
    controlled by the original L2 norm on any fixed compact configuration ball.
    The common constant is chosen before the state. -/
theorem scalar_coulomb_local_lipschitz_original_norm_bound {N : ℕ} (hN : 0 < N)
    (Z E A : ℝ) :
    ∃ C : ℝ≥0, ∀ f : SpatialL2 N,
      scalarHamiltonianGraph N Z f ((E : ℂ) • f) →
      ∃ u : Configuration N → ℂ,
        LocallyLipschitz u ∧ (f : Configuration N → ℂ) =ᵐ[volume] u ∧
        (∀ x, ‖u x‖ ≤ coulombMoserBoundCoefficient N Z E * ‖f‖) ∧
        LipschitzOnWith (C * ‖f‖₊) u (Metric.closedBall 0 A) := by
  have hpointwise : ∀ f : scalarPhysicalEigenspace N Z E,
      ∃ B : ℝ, ∀ p : ballDifferenceIndex N A,
        ‖eigenDifferenceQuotient hN Z E A p f‖ ≤ B := by
    intro f
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : Configuration N) A)
      (eigenRepresentative_spec hN Z E f).1.locallyLipschitzOn
    refine ⟨K, fun p => ?_⟩
    rw [eigenDifferenceQuotient_apply_norm]
    exact (div_le_iff₀ (dist_pos.mpr p.property.2.2)).mpr
      (hK.dist_le_mul p.val.1 p.property.1 p.val.2 p.property.2.1)
  obtain ⟨B, hB⟩ := banach_steinhaus hpointwise
  let C : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  refine ⟨C, fun f hf => ?_⟩
  let v : scalarPhysicalEigenspace N Z E := ⟨f, hf⟩
  have hv := eigenRepresentative_spec hN Z E v
  refine ⟨eigenRepresentative hN Z E v, hv.1, hv.2.1, hv.2.2, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simp
  · let p : ballDifferenceIndex N A := ⟨(x,y), hx, hy, hxy⟩
    have hb := (eigenDifferenceQuotient hN Z E A p).le_opNorm v
    have hn := hB p
    have hc : ‖eigenDifferenceQuotient hN Z E A p‖ ≤ (C : ℝ) :=
      hn.trans (le_max_left _ _)
    have he : ‖eigenDifferenceQuotient hN Z E A p v‖ ≤ (C : ℝ) * ‖v‖ :=
      hb.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg v))
    rw [eigenDifferenceQuotient_apply_norm] at he
    have hh := (div_le_iff₀ (dist_pos.mpr hxy)).mp he
    change dist (eigenRepresentative hN Z E v x) (eigenRepresentative hN Z E v y) ≤
      (C : ℝ) * ‖f‖ * dist x y at hh
    simpa only [NNReal.coe_mul, coe_nnnorm] using hh

#print axioms scalar_coulomb_local_lipschitz_original_norm_bound

/-- The same state-independent bound holds for every continuous representative
    of the original physical state, so it can be used by existing KS theorems. -/
theorem scalar_coulomb_continuous_lipschitz_original_norm_bound {N : ℕ} (hN : 0 < N)
    (Z E A : ℝ) :
    ∃ C : ℝ≥0, ∀ f : SpatialL2 N,
      scalarHamiltonianGraph N Z f ((E : ℂ) • f) →
      ∀ u : Configuration N → ℂ, Continuous u →
        (f : Configuration N → ℂ) =ᵐ[volume] u →
        LipschitzOnWith (C * ‖f‖₊) u (Metric.closedBall 0 A) := by
  obtain ⟨C, hC⟩ := scalar_coulomb_local_lipschitz_original_norm_bound hN Z E A
  refine ⟨C, fun f hf u hu he => ?_⟩
  obtain ⟨v, hv, hev, _, hlv⟩ := hC f hf
  have heq : v = u := volume.eq_of_ae_eq (hev.symm.trans he) hv.continuous hu
  rwa [← heq]

/-- All spin components share one local Lipschitz constant controlled by the
    original full spin-space L2 norm. N, Z, E and the compact radius are fixed
    before choosing the state or its components. -/
theorem coulomb_spin_local_lipschitz_original_norm_bound {N : ℕ} (hN : 0 < N)
    (Z E A : ℝ) :
    ∃ C : ℝ≥0, ∀ ψ : SpinSpace N,
      hamiltonianGraph N Z ψ ((E : ℂ) • ψ) →
      ∃ u : SpinConfiguration N → Configuration N → ℂ,
        (∀ σ, LocallyLipschitz (u σ)) ∧
        (∀ᵐ x ∂volume, ∀ σ, ψ σ x = u σ x) ∧
        (∀ π : Equiv.Perm (Fin N), ∀ σ, ∀ x,
          u (permuteSpin π σ) (permuteSpace π x) = permutationSign π • u σ x) ∧
        (∀ x, Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ x‖^2) ≤
          coulombMoserBoundCoefficient N Z E * ‖ψ‖) ∧
        ∀ σ, LipschitzOnWith (C * ‖ψ‖₊) (u σ) (Metric.closedBall 0 A) := by
  obtain ⟨C, hC⟩ := scalar_coulomb_continuous_lipschitz_original_norm_bound hN Z E A
  refine ⟨C, fun ψ hψ => ?_⟩
  obtain ⟨u, hu, he, hp, hm⟩ := coulomb_spin_locally_lipschitz_representative hN hψ
  refine ⟨u, hu, he, hp, hm, fun σ => ?_⟩
  have hl := hC (ψ σ) (hψ.2.2 σ) (u σ) (hu σ).continuous
    (he.mono fun x hx => hx σ)
  apply hl.weaken
  gcongr
  exact PiLp.nnnorm_apply_le ψ σ

#print axioms scalar_coulomb_continuous_lipschitz_original_norm_bound
#print axioms coulomb_spin_local_lipschitz_original_norm_bound
end ManyBody.S8
