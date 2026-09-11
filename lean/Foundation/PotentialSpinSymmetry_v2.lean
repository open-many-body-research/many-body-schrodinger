import PotentialSymmetry_v2

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TheoremT.Continuum

/-- Full physical spin-space symmetry follows by its exact finite inner-product
sum. No spin or spatial-symmetry restriction is needed for the real multiplier. -/
theorem coulomb_product_spin_inner_symmetry {N : ℕ} (Z : ℝ)
    (f g vf vg : SpinSpace N)
    (hvf : ∀ σ, vf σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f σ x)
    (hvg : ∀ σ, vg σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * g σ x) :
    inner ℂ vf g = inner ℂ f vg := by
  simp only [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun σ _ =>
    coulomb_product_inner_symmetry Z (f σ) (g σ) (vf σ) (vg σ) (hvf σ) (hvg σ))

#print axioms coulomb_product_spin_inner_symmetry

end TheoremT.Continuum
