import WeakCoulombL2_v2

/-! Symmetry of multiplication by the actual real Coulomb potential.
This is the potential term alone; kinetic symmetry and self-adjointness are
separate claims. The representatives may be arbitrary actual L² products. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators

namespace TheoremT.Continuum

theorem coulomb_product_inner_symmetry {N : ℕ} (Z : ℝ)
    (f g vf vg : SpatialL2 N)
    (hvf : vf =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x)
    (hvg : vg =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * g x) :
    inner ℂ vf g = inner ℂ f vg := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hvf, hvg] with x hfx hgx
  rw [hfx, hgx]
  change inner ℂ ((coulombPotential N Z x : ℂ) • f x) (g x) =
    inner ℂ (f x) ((coulombPotential N Z x : ℂ) • g x)
  rw [inner_smul_left, inner_smul_right]
  simp

theorem coulomb_toLp_inner_symmetry {N : ℕ} (Z : ℝ)
    (f g : SpatialL2 N) (hf : HasH1 f) (hg : HasH1 g) :
    inner ℂ ((coulombProductL2_of_hasH1 Z hf).toLp
      (fun x => (coulombPotential N Z x : ℂ) * f x)) g =
    inner ℂ f ((coulombProductL2_of_hasH1 Z hg).toLp
      (fun x => (coulombPotential N Z x : ℂ) * g x)) :=
  coulomb_product_inner_symmetry Z f g _ _
    (coulombProductL2_of_hasH1 Z hf).coeFn_toLp
    (coulombProductL2_of_hasH1 Z hg).coeFn_toLp

#print axioms coulomb_product_inner_symmetry
#print axioms coulomb_toLp_inner_symmetry

end TheoremT.Continuum
