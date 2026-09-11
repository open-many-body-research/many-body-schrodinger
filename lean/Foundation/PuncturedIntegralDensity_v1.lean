import PuncturedHardyTransfer_v1

/-! Punctured smooth-core density in literal configuration-space integrals.
This includes the Hardy-weighted L² error needed for polar-coordinate limits.
The input derivative graph is the original weak H¹ definition. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum

theorem spatialL2_norm_sq_integral_of_ae {N : ℕ} (g : SpatialL2 N)
    (u : Configuration N → ℂ) (hu : g =ᵐ[volume] u) :
    ‖g‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  rw [spatialL2_norm_sq_integral]
  exact integral_congr_ae (hu.fun_comp (fun z : ℂ => ‖z‖ ^ 2))

theorem weakH1_punctured_smooth_compact_integral_sequence {f : SpatialL2 1}
    (d : Coordinate 1 → SpatialL2 1) (hd : ∀ k, WeakPartial f (d k) k) :
    ∃ u : ℕ → Configuration 1 → ℂ,
      (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, (0 : Configuration 1) ∉ tsupport (u n)) ∧
      Tendsto (fun n => ∫ x, ‖u n x - f x‖ ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, ∑ k : Coordinate 1,
        ‖smoothPartial (u n) k x - d k x‖ ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, ‖u n x - f x‖ ^ 2 / ‖x‖ ^ 2) atTop (𝓝 0) := by
  classical
  obtain ⟨u,g,dg,hu,hc,hzero,hgu,hdgu,hdg,hH2,hgt,hdt⟩ :=
    weakH1_punctured_smooth_compact_graph_sequence d hd
  have hgsub (n : ℕ) : (g n - f : SpatialL2 1) =ᵐ[volume] fun x => u n x - f x := by
    filter_upwards [Lp.coeFn_sub (g n) f, hgu n] with x hx hgx
    simp only [Pi.sub_apply] at hx
    rw [hx, hgx]
  have hdsub (n : ℕ) (k : Coordinate 1) :
      (dg n k - d k : SpatialL2 1) =ᵐ[volume] fun x => smoothPartial (u n) k x - d k x := by
    filter_upwards [Lp.coeFn_sub (dg n k) (d k), hdgu n k] with x hx hdx
    simp only [Pi.sub_apply] at hx
    rw [hx, hdx]
  have hderint (n : ℕ) (k : Coordinate 1) :
      Integrable (fun x => ‖smoothPartial (u n) k x - d k x‖ ^ 2) volume :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp (dg n k - d k)).aestronglyMeasurable).mp
      (Lp.memLp (dg n k - d k))).congr
        ((hdsub n k).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  have hderEq (n : ℕ) : (∑ k : Coordinate 1, ‖dg n k - d k‖ ^ 2) =
      ∫ x, ∑ k : Coordinate 1, ‖smoothPartial (u n) k x - d k x‖ ^ 2 := by
    rw [integral_finsetSum Finset.univ (fun k _ => hderint n k)]
    exact Finset.sum_congr rfl (fun k _ => spatialL2_norm_sq_integral_of_ae
      (dg n k - d k) _ (hdsub n k))
  let vm := weakH1_div_configuration_norm_memLp f d hd
  let v : SpatialL2 1 := vm.toLp (fun x => f x / (‖x‖ : ℂ))
  let vnm (n : ℕ) := weakH1_div_configuration_norm_memLp (g n) (dg n) (hdg n)
  let vn (n : ℕ) : SpatialL2 1 := (vnm n).toLp (fun x => g n x / (‖x‖ : ℂ))
  have hv : v =ᵐ[volume] fun x => f x / (‖x‖ : ℂ) := vm.coeFn_toLp
  have hvn (n : ℕ) : vn n =ᵐ[volume] fun x => g n x / (‖x‖ : ℂ) :=
    (vnm n).coeFn_toLp
  have hvt := weakH1_inverse_radius_tendsto g f dg d vn v hdg hd hvn hv hdt
  have hvsub (n : ℕ) : (vn n - v : SpatialL2 1) =ᵐ[volume]
      fun x => (u n x - f x) / (‖x‖ : ℂ) := by
    filter_upwards [Lp.coeFn_sub (vn n) v, hvn n, hv, hgu n] with x hx hnx hvx hux
    simp only [Pi.sub_apply] at hx
    rw [hx, hnx, hvx, hux, sub_div]
  refine ⟨u,hu,hc,hzero,?_,?_,?_⟩
  · have ht := ((hgt.sub_const f).norm.pow 2)
    simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, spatialL2_norm_sq_integral_of_ae _ _ (hgsub _)] using ht
  · have ht := tendsto_finset_sum Finset.univ (fun k _ =>
      ((hdt k).sub_const (d k)).norm.pow 2)
    simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, hderEq] using ht
  · have ht := ((hvt.sub_const v).norm.pow 2)
    simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, spatialL2_norm_sq_integral_of_ae _ _ (hvsub _), norm_div,
      Complex.norm_real, norm_norm, div_pow] using ht

#print axioms spatialL2_norm_sq_integral_of_ae
#print axioms weakH1_punctured_smooth_compact_integral_sequence
end TheoremT.Continuum
