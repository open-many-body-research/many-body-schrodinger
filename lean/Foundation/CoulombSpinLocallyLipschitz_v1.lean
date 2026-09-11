import CoulombLipschitzPointBound_v1
import FermionicContinuousRepresentative_v1

/-! Full physical fermionic spin-space representatives. The square-sum
amplitude bound retains no factor for the number of spin configurations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem coulomb_spin_locally_lipschitz_representative {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {ψ : SpinSpace N} (hg : hamiltonianGraph N Z ψ ((E : ℂ) • ψ)) :
    ∃ u : SpinConfiguration N → Configuration N → ℂ,
      (∀ σ, LocallyLipschitz (u σ)) ∧
      (∀ᵐ x ∂volume, ∀ σ, ψ σ x=u σ x) ∧
      (∀ π : Equiv.Perm (Fin N), ∀ σ, ∀ x,
        u (permuteSpin π σ) (permuteSpace π x)=permutationSign π • u σ x) ∧
      ∀ x, Real.sqrt (∑ σ : SpinConfiguration N, ‖u σ x‖^2) ≤
        coulombMoserBoundCoefficient N Z E*‖ψ‖ := by
  have hex (σ : SpinConfiguration N) :=
    scalar_coulomb_bounded_locally_lipschitz_representative hN (hg.2.2 σ)
  choose u hu he hb using hex
  refine ⟨u,hu,ae_all_iff.mpr he,
    fermionic_continuous_representative_antisymmetric hg.1 (fun σ => (hu σ).continuous) he,?_⟩
  intro x
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun σ _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hb σ x) 2)
  simp only [mul_pow,← Finset.mul_sum,← PiLp.norm_sq_eq_of_L2] at hs
  apply (Real.sqrt_le_sqrt hs).trans_eq
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (coulombMoserBoundCoefficient_pos N Z E).le,
    Real.sqrt_sq (norm_nonneg ψ)]

#print axioms coulomb_spin_locally_lipschitz_representative
end TheoremT.Continuum
