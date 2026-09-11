import PuncturedH1Density_v2
import CoulombH1Continuity_v1

/-! Actual inverse-radius L² convergence from weak-H¹ graph convergence.
This supplies the singular weight control needed when passing punctured-core
identities to H¹. It asserts neither an H² core nor an executable selection. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum

theorem weakH1_inverse_radius_norm_le (f : SpatialL2 1)
    (d : Coordinate 1 → SpatialL2 1) (hd : ∀ k, WeakPartial f (d k) k)
    (v : SpatialL2 1) (hv : v =ᵐ[volume] fun x => f x / (‖x‖ : ℂ)) :
    ‖v‖ ≤ 2 * Real.sqrt (∑ k : Coordinate 1, ‖d k‖ ^ 2) := by
  have h := weak_nuclear_memLp_two_and_bound (0 : Fin 1) f d hd
  have he : h.1.toLp (fun x => f x / (‖position x 0‖ : ℂ)) = v := by
    apply Lp.ext
    exact h.1.coeFn_toLp.trans (by simpa only [position_one_norm] using hv.symm)
  rw [← he]
  exact nuclear_product_norm_le 0 f d hd

theorem weakH1_inverse_radius_tendsto
    (fn : ℕ → SpatialL2 1) (f : SpatialL2 1)
    (dn : ℕ → Coordinate 1 → SpatialL2 1) (d : Coordinate 1 → SpatialL2 1)
    (vn : ℕ → SpatialL2 1) (v : SpatialL2 1)
    (hdn : ∀ n k, WeakPartial (fn n) (dn n k) k)
    (hd : ∀ k, WeakPartial f (d k) k)
    (hvn : ∀ n, vn n =ᵐ[volume] fun x => fn n x / (‖x‖ : ℂ))
    (hv : v =ᵐ[volume] fun x => f x / (‖x‖ : ℂ))
    (hdt : ∀ k, Tendsto (fun n => dn n k) atTop (𝓝 (d k))) :
    Tendsto vn atTop (𝓝 v) := by
  have hD : Tendsto (fun n => ∑ k : Coordinate 1, ‖dn n k - d k‖ ^ 2)
      atTop (𝓝 0) := by
    have hh := tendsto_finset_sum Finset.univ (fun k _ =>
      (((hdt k).sub_const (d k)).norm.pow 2))
    simpa using hh
  have hs : Tendsto (fun n => 2 * Real.sqrt
      (∑ k : Coordinate 1, ‖dn n k - d k‖ ^ 2)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hD).const_mul 2
  have hsub : Tendsto (fun n => vn n - v) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hs
    apply weakH1_inverse_radius_norm_le (fn n - f) (fun k => dn n k - d k)
      (fun k => weakPartial_sub_h1 (hdn n k) (hd k)) (vn n - v)
    filter_upwards [hvn n, hv, Lp.coeFn_sub (vn n) v, Lp.coeFn_sub (fn n) f]
      with x hnx hvx hx hfx
    simp only [Pi.sub_apply] at hx hfx
    rw [hx, hfx, hnx, hvx, sub_div]
  simpa only [sub_add_cancel, zero_add] using hsub.add_const v

#print axioms weakH1_inverse_radius_norm_le
#print axioms weakH1_inverse_radius_tendsto
end TheoremT.Continuum
