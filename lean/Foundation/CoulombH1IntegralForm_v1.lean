import CoulombH1PhysicalEnergy_v1

/-! The form graph is exactly the usual continuum gradient-plus-potential
integral formula, without requiring a supplied multiplication witness. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TheoremT.Continuum

theorem coulombH1FormValue_iff_integral {N : ℕ} {Z : ℝ} {ψ : SpinSpace N} {q : ℝ} :
    coulombH1FormValue N Z ψ q ↔
      ψ ∈ fermionicSubspace N ∧
      ∃ d : Coordinate N → SpinSpace N,
        (∀ σ k, WeakPartial (ψ σ) (d k σ) k) ∧
        q = (1 / 2 : ℝ) * (∑ k, ‖d k‖^2) +
          ∑ σ : SpinConfiguration N, ∫ x, coulombPotential N Z x * ‖ψ σ x‖^2 := by
  constructor
  · rintro ⟨hf, d, v, hd, hv, rfl⟩
    refine ⟨hf, d, hd, ?_⟩
    simp only [coulombH1Energy, PiLp.inner_apply]
    congr 1
    exact Finset.sum_congr rfl (fun σ _ => coulomb_potential_energy_eq_integral (hv σ))
  · rintro ⟨hf, d, hd, rfl⟩
    obtain ⟨v, hv⟩ := spin_coulomb_product_exists_of_hasH1 Z ψ
      (fun σ => ⟨fun k => d k σ, hd σ⟩)
    refine ⟨hf, d, v, hd, hv, ?_⟩
    simp only [coulombH1Energy, PiLp.inner_apply]
    congr 1
    exact Finset.sum_congr rfl (fun σ _ => (coulomb_potential_energy_eq_integral (hv σ)).symm)

#print axioms coulombH1FormValue_iff_integral

end TheoremT.Continuum
