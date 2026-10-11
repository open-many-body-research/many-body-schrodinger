import CompactGrushinRadialComponentBounds_v1
import CompactWeakGrushinOutputEstimates_v1

/-! Radial component estimates for genuine compact weak H2 jets. A single
existing mollifier sequence and compact-weight L2 convergence discharge all
approximation obligations. No solution smoothness or weighted jet bound is
assumed by the weak result. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem smooth_radial_jet_bounds {c : ℝ} (hc : 0 ≤ c)
    {G : Space κ → ℂ} (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, (d v : Space κ → ℂ) =ᵐ[volume] (fun p => fderiv ℝ G p v))
    (he : ∀ v w, (e v w : Space κ → ℂ) =ᵐ[volume]
      (fun p => fderiv ℝ (fun z => fderiv ℝ G z v) p w)) :
    (∀ j : κ, 16*c*(∫ p, ‖d (tDir j) p‖^2) ≤ ∫ p, ‖principal c e p‖^2) ∧
    (∀ i j : Fin 4, (∫ p, ‖e (yDir i) (yDir j) p‖^2) ≤
      (3/2 : ℝ)*(∫ p, ‖principal c e p‖^2)) ∧
    (∀ (i : Fin 4) (j : κ), 2*c*(∫ p, ‖‖p.1‖ • e (yDir i) (tDir j) p‖^2) ≤
      (3/2 : ℝ)*(∫ p, ‖principal c e p‖^2)) ∧
    (∀ i j : κ, c^2*(∫ p, ‖(‖p.1‖^2) • e (tDir i) (tDir j) p‖^2) ≤
      (3/2 : ℝ)*(∫ p, ‖principal c e p‖^2)) := by
  have hp : (∫ p, ‖principal c e p‖^2) = ∫ p, ‖euclideanGrushin c G p‖^2 := by
    apply integral_congr_ae
    filter_upwards [principal_ae_smooth c he] with p hp
    rw [hp]
  have ht (j : κ) : (∫ p, ‖d (tDir j) p‖^2) =
      ∫ p, ‖partialTDirectional G (oscillatorBasis j) p‖^2 := by
    apply integral_congr_ae
    filter_upwards [hd (tDir j)] with p hp
    rw [hp]
    rfl
  have hyy (i j : Fin 4) : (∫ p, ‖e (yDir i) (yDir j) p‖^2) =
      ∫ p, ‖partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2 := by
    apply integral_congr_ae
    filter_upwards [he (yDir i) (yDir j)] with p hp
    rw [hp]
    rfl
  have hyt (i : Fin 4) (j : κ) : (∫ p, ‖‖p.1‖ • e (yDir i) (tDir j) p‖^2) =
      ∫ p, ‖‖p.1‖ • partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2 := by
    apply integral_congr_ae
    filter_upwards [he (yDir i) (tDir j)] with p hp
    rw [hp]
    rfl
  have htt (i j : κ) : (∫ p, ‖(‖p.1‖^2) • e (tDir i) (tDir j) p‖^2) =
      ∫ p, ‖(‖p.1‖^2) • partialTDirectional (partialTDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2 := by
    apply integral_congr_ae
    filter_upwards [he (tDir i) (tDir j)] with p hp
    rw [hp]
    rfl
  simp_rw [ht,hyy,hyt,htt,hp]
  exact compact_grushin_radial_component_bounds hc hG hcG

theorem compact_weakH2_radial_estimates {c : ℝ} (hc : 0 ≤ c)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    (∀ j : κ, 16*c*(∫ p, ‖d (tDir j) p‖^2) ≤ ∫ p, ‖principal c e p‖^2) ∧
    (∀ i j : Fin 4, (∫ p, ‖e (yDir i) (yDir j) p‖^2) ≤
      (3/2 : ℝ)*(∫ p, ‖principal c e p‖^2)) ∧
    (∀ (i : Fin 4) (j : κ), 2*c*(∫ p, ‖‖p.1‖ • e (yDir i) (tDir j) p‖^2) ≤
      (3/2 : ℝ)*(∫ p, ‖principal c e p‖^2)) ∧
    (∀ i j : κ, c^2*(∫ p, ‖(‖p.1‖^2) • e (tDir i) (tDir j) p‖^2) ≤
      (3/2 : ℝ)*(∫ p, ‖principal c e p‖^2)) := by
  obtain ⟨L,hL,hKL,u,g,dg,eg,hu,huc,hus,hgu,hdu,heu,hgconv,hdconv,heconv⟩ :=
    product_compact_weakH2_uniform_support_approximation d e hd he hK hs
  have hes (n : ℕ) (v w : Space κ) : ∀ᵐ p ∂volume, p ∉ L → eg n v w p = 0 :=
    lp_ae_zero_off_of_second_directional_support (hus n) (heu n v w)
  have hPn := principal_norm_sq_tendsto c hL heconv hes
  have hb (n : ℕ) := smooth_radial_jet_bounds hc (hu n) (huc n) (dg n) (eg n) (hdu n) (heu n)
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    exact le_of_tendsto_of_tendsto'
      ((l2_integral_norm_sq_tendsto (hdconv (tDir j))).const_mul (16*c)) hPn
      (fun n => (hb n).1 j)
  · intro i j
    exact le_of_tendsto_of_tendsto'
      (l2_integral_norm_sq_tendsto (heconv (yDir i) (yDir j))) (hPn.const_mul (3/2))
      (fun n => (hb n).2.1 i j)
  · intro i j
    have ht := compact_support_weight_norm_sq_tendsto hL (fun p : Space κ => ‖p.1‖)
      (by fun_prop) (heconv (yDir i) (tDir j)) (fun n => hes n (yDir i) (tDir j))
    exact le_of_tendsto_of_tendsto' (ht.const_mul (2*c)) (hPn.const_mul (3/2))
      (fun n => (hb n).2.2.1 i j)
  · intro i j
    have ht := compact_support_weight_norm_sq_tendsto hL (fun p : Space κ => ‖p.1‖^2)
      (by fun_prop) (heconv (tDir i) (tDir j)) (fun n => hes n (tDir i) (tDir j))
    exact le_of_tendsto_of_tendsto' (ht.const_mul (c^2)) (hPn.const_mul (3/2))
      (fun n => (hb n).2.2.2 i j)

end TheoremT.Continuum.WeakGrushin
