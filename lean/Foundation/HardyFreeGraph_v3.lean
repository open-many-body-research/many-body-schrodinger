import HardyFreeGraph_v2

/-! Sharp energy control for the actual positive free resolvent graph. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem positiveFreeGraph_energy {N : ℕ} {μ : ℝ} {u f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial u (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (hout : f = (-1/2 : ℝ) • (∑ k : Coordinate N, e k k) + μ • u) :
    inner ℝ u f = (1/2 : ℝ)*(∑ k : Coordinate N, ‖d k‖^2)+μ*‖u‖^2 := by
  have henergy := weak_laplacian_energy_identity d (fun k => e k k) hd (fun k => he k k)
  rw [hout,inner_add_right,real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  linarith

/-- The factor 1/(2μ) follows by completing the scalar square in the exact
energy identity; it is independent of dimension and spin multiplicity. -/
theorem positiveFreeGraph_gradient_sq_le {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    {u f : SpatialL2 N} (d : Coordinate N → SpatialL2 N)
    (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial u (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (hout : f = (-1/2 : ℝ) • (∑ k : Coordinate N, e k k) + μ • u) :
    (∑ k : Coordinate N, ‖d k‖^2) ≤ ‖f‖^2 / (2*μ) := by
  have hcs := real_inner_le_norm u f
  rw [positiveFreeGraph_energy d e hd he hout] at hcs
  have hm := mul_le_mul_of_nonneg_left hcs hμ.le
  apply (le_div_iff₀ (by positivity : 0 < 2*μ)).mpr
  nlinarith [sq_nonneg (2*μ*‖u‖-‖f‖)]

theorem positiveFreeGraph_spin_gradient_sq_le {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    {u f : SpinSpace N} (d : Coordinate N → SpinSpace N)
    (e : Coordinate N → Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (u σ) (d k σ) k)
    (he : ∀ σ k l, WeakPartial (d k σ) (e k l σ) l)
    (hout : ∀ σ, f σ = (-1/2 : ℝ) • (∑ k : Coordinate N, e k k σ) + μ • u σ) :
    (∑ k : Coordinate N, ‖d k‖^2) ≤ ‖f‖^2/(2*μ) := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (SpinConfiguration N)))
    (fun σ _ => positiveFreeGraph_gradient_sq_le hμ (fun k => d k σ) (fun k l => e k l σ)
      (hd σ) (he σ) (hout σ))
  rw [←Finset.sum_div,←PiLp.norm_sq_eq_of_L2,Finset.sum_comm] at hs
  simpa only [←PiLp.norm_sq_eq_of_L2] using hs

#print axioms positiveFreeGraph_gradient_sq_le
#print axioms positiveFreeGraph_spin_gradient_sq_le
end TheoremT.Continuum
