import DirectionalSpinCoulombNorm_v1
import CoulombRelativeBound_v2

/-! The refined coefficient also gives an explicit infinitesimal relative bound.
This sharpens a numerical constant; earlier verified operator constructions remain unchanged. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem coulomb_product_directional_infinitesimal_bound {N : ℕ} (Z : ℝ)
    (f : SpatialL2 N) (d e : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k, WeakPartial (d k) (e k) k)
    (v : SpatialL2 N)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x)
    {ε : ℝ} (hε : 0 < ε) :
    ‖v‖ ≤ ε * ‖∑ k : Coordinate N, e k‖ +
      ((N : ℝ) * (2*|Z| + (N : ℝ) - 1)^2) / (4*ε) * ‖f‖ := by
  have h := (coulomb_product_directional_norm_le Z f d hd v hv).trans
    (coulomb_young_numeric (coulomb_directional_coefficient_nonneg N Z) (norm_nonneg f)
      (norm_nonneg (∑ k : Coordinate N, e k)) hε (weak_laplacian_interpolation d e hd he))
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] using h

theorem coulomb_product_spin_directional_infinitesimal_bound {N : ℕ} (Z : ℝ)
    (ψ : SpinSpace N) (d e : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (he : ∀ σ k, WeakPartial (d k σ) (e k σ) k)
    (v : SpinSpace N)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x)
    {ε : ℝ} (hε : 0 < ε) :
    ‖v‖ ≤ ε * ‖∑ k : Coordinate N, e k‖ +
      ((N : ℝ) * (2*|Z| + (N : ℝ) - 1)^2) / (4*ε) * ‖ψ‖ := by
  have h := (coulomb_product_spin_directional_norm_le Z ψ d hd v hv).trans
    (coulomb_young_numeric (coulomb_directional_coefficient_nonneg N Z) (norm_nonneg ψ)
      (norm_nonneg (∑ k : Coordinate N, e k)) hε (weak_laplacian_spin_interpolation ψ d e hd he))
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] using h

#print axioms coulomb_product_directional_infinitesimal_bound
#print axioms coulomb_product_spin_directional_infinitesimal_bound
end TheoremT.Continuum
