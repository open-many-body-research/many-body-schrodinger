import WeakGrushinJetLimits_v1
import ProductCompactH2Approximation_v1
import CompactDerivativeL2Support_v1
import GrushinYHessianIdentity_v1
import CompactGrushinTangentialBound_v1

/-! The actual compact Grushin estimates extend to genuine weak H2 inputs.
The derivative witnesses are defined by all compact smooth weak tests. The
proof constructs the smooth approximants, their uniform support, and every
weighted L2 limit; none of these facts is an added approximation hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem smooth_jet_estimates {c : ℝ} (hc0 : 0 ≤ c)
    {G : Space κ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, (d v : Space κ → ℂ) =ᵐ[volume] (fun p => fderiv ℝ G p v))
    (he : ∀ v w, (e v w : Space κ → ℂ) =ᵐ[volume]
      (fun p => fderiv ℝ (fun z => fderiv ℝ G z v) p w)) :
    ((16*c)*(∑ j : κ, ∫ p, ‖d (tDir j) p‖^2) ≤ ∫ p, ‖principal c e p‖^2) ∧
    ((∑ i : Fin 4, ∑ j : Fin 4, ∫ p, ‖e (yDir i) (yDir j) p‖^2) +
      (∫ p, ‖tWeighted c e p‖^2) +
      2*c*(∑ i : Fin 4, ∑ j : κ, ∫ p, ‖p.1‖^2 * ‖e (yDir i) (tDir j) p‖^2) ≤
        (3/2 : ℝ)*(∫ p, ‖principal c e p‖^2)) := by
  have hp : (∫ p, ‖principal c e p‖^2) = ∫ p, ‖euclideanGrushin c G p‖^2 := by
    apply integral_congr_ae
    filter_upwards [principal_ae_smooth c he] with p hp
    rw [hp]
  have ht : (∫ p, ‖tWeighted c e p‖^2) = ∫ p, ‖grushinWeightedT c G p‖^2 := by
    apply integral_congr_ae
    filter_upwards [tWeighted_ae_smooth c he] with p hp
    rw [hp]
  have hdt (j : κ) : (∫ p, ‖d (tDir j) p‖^2) =
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
  have hyt (i : Fin 4) (j : κ) : (∫ p, ‖p.1‖^2 * ‖e (yDir i) (tDir j) p‖^2) =
      ∫ p, ‖p.1‖^2 *
        ‖partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2 := by
    apply integral_congr_ae
    filter_upwards [he (yDir i) (tDir j)] with p hp
    rw [hp]
    rfl
  constructor
  · simp_rw [hdt,hp]
    exact compact_grushin_tangential_bound hc0 hG hc
  · simp_rw [hyy,ht,hyt,hp]
    exact compact_grushin_full_y_hessian_bound hc0 hG hc

theorem compact_weakH2_estimates {c : ℝ} (hc0 : 0 ≤ c)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    MemLp (principal c e) 2 volume ∧
    ((16*c)*(∑ j : κ, ∫ p, ‖d (tDir j) p‖^2) ≤ ∫ p, ‖principal c e p‖^2) ∧
    ((∑ i : Fin 4, ∑ j : Fin 4, ∫ p, ‖e (yDir i) (yDir j) p‖^2) +
      (∫ p, ‖tWeighted c e p‖^2) +
      2*c*(∑ i : Fin 4, ∑ j : κ, ∫ p, ‖p.1‖^2 * ‖e (yDir i) (tDir j) p‖^2) ≤
        (3/2 : ℝ)*(∫ p, ‖principal c e p‖^2)) := by
  obtain ⟨L,hL,hKL,u,g,dg,eg,hu,huc,hus,hgu,hdu,heu,hgconv,hdconv,heconv⟩ :=
    product_compact_weakH2_uniform_support_approximation d e hd he hK hs
  have hes (n : ℕ) (v w : Space κ) : ∀ᵐ p ∂volume, p ∉ L → eg n v w p = 0 :=
    lp_ae_zero_off_of_second_directional_support (hus n) (heu n v w)
  have hel (v w : Space κ) : ∀ᵐ p ∂volume, p ∉ L → e v w p = 0 :=
    lp_second_directional_support_of_tendsto hL.measurableSet hus
      (fun n => heu n v w) (heconv v w)
  have hPn := principal_norm_sq_tendsto c hL heconv hes
  have htn := tWeighted_norm_sq_tendsto c hL heconv hes
  have hym := yHessian_norm_sq_tendsto heconv
  have htm := tGradient_norm_sq_tendsto hdconv
  have hmix := mixed_norm_sq_tendsto hL heconv hes
  have hb (n : ℕ) := smooth_jet_estimates hc0 (hu n) (huc n) (dg n) (eg n) (hdu n) (heu n)
  refine ⟨principal_memLp c hL e hel, ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto' (htm.const_mul (16*c)) hPn (fun n => (hb n).1)
  · exact le_of_tendsto_of_tendsto'
      ((hym.add htn).add (hmix.const_mul (2*c))) (hPn.const_mul (3/2)) (fun n => (hb n).2)

end TheoremT.Continuum.WeakGrushin
