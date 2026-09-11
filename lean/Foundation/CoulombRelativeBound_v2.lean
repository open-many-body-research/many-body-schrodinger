import CoulombYoung_v2
import HardyWeakLaplacian_v1

/-! Infinitesimal relative bounds against the actual weak Laplacian.
The physical Coulomb products and all derivative witnesses refer to the original
continuum spaces. Self-adjointness is not asserted in this module. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TheoremT.Continuum

theorem coulomb_product_infinitesimal_bound {N : ℕ} (Z : ℝ)
    (f : SpatialL2 N) (d e : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k, WeakPartial (d k) (e k) k)
    (v : SpatialL2 N)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x)
    {ε : ℝ} (hε : 0 < ε) :
    ‖v‖ ≤ ε * ‖∑ k : Coordinate N, e k‖ +
      (2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)))^2 / (4 * ε) * ‖f‖ := by
  exact (coulomb_product_norm_le Z f d hd v hv).trans
    (coulomb_young_numeric (by positivity) (norm_nonneg f)
      (norm_nonneg (∑ k : Coordinate N, e k)) hε (weak_laplacian_interpolation d e hd he))

theorem weak_laplacian_spin_energy_identity {N : ℕ} (ψ : SpinSpace N)
    (d e : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (he : ∀ σ k, WeakPartial (d k σ) (e k σ) k) :
    (∑ k : Coordinate N, ‖d k‖^2) = -inner ℝ ψ (∑ k : Coordinate N, e k) := by
  calc
    (∑ k : Coordinate N, ‖d k‖^2) =
        ∑ k : Coordinate N, ∑ σ : SpinConfiguration N, ‖d k σ‖^2 := by
      simp only [PiLp.norm_sq_eq_of_L2]
    _ = ∑ σ : SpinConfiguration N, ∑ k : Coordinate N, ‖d k σ‖^2 := Finset.sum_comm
    _ = ∑ σ : SpinConfiguration N, -inner ℝ (ψ σ) ((∑ k : Coordinate N, e k) σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      simpa only [WithLp.ofLp_sum, Finset.sum_apply] using
        weak_laplacian_energy_identity (fun k => d k σ) (fun k => e k σ) (hd σ) (he σ)
    _ = -inner ℝ ψ (∑ k : Coordinate N, e k) := by
      simp only [PiLp.inner_apply, Finset.sum_neg_distrib]

theorem weak_laplacian_spin_interpolation {N : ℕ} (ψ : SpinSpace N)
    (d e : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (he : ∀ σ k, WeakPartial (d k σ) (e k σ) k) :
    (∑ k : Coordinate N, ‖d k‖^2) ≤ ‖ψ‖ * ‖∑ k : Coordinate N, e k‖ := by
  rw [weak_laplacian_spin_energy_identity ψ d e hd he]
  exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)

/-- Full-spin infinitesimal relative boundedness, with no spin dimension factor.
Every ε>0 is allowed, and the lower-order coefficient is explicit. -/
theorem coulomb_product_spin_infinitesimal_bound {N : ℕ} (Z : ℝ)
    (ψ : SpinSpace N) (d e : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (he : ∀ σ k, WeakPartial (d k σ) (e k σ) k)
    (v : SpinSpace N)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x)
    {ε : ℝ} (hε : 0 < ε) :
    ‖v‖ ≤ ε * ‖∑ k : Coordinate N, e k‖ +
      (2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)))^2 / (4 * ε) * ‖ψ‖ := by
  exact (coulomb_product_spin_norm_le Z ψ d hd v hv).trans
    (coulomb_young_numeric (by positivity) (norm_nonneg ψ)
      (norm_nonneg (∑ k : Coordinate N, e k)) hε (weak_laplacian_spin_interpolation ψ d e hd he))

#print axioms coulomb_product_infinitesimal_bound
#print axioms weak_laplacian_spin_energy_identity
#print axioms weak_laplacian_spin_interpolation
#print axioms coulomb_product_spin_infinitesimal_bound

end TheoremT.Continuum
