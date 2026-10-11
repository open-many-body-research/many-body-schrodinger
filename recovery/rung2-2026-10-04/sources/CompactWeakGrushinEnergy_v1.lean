import CompactGrushinEnergy_v1
import CompactWeakGrushinCutoffEnergy_v1
import WeakGrushinPrincipalTests_v1
import ActualL2IntegralCauchy_v1

/-! The actual compact weak H2 energy identity and Cauchy bounds. Smooth
approximation uses its proved common compact support; no support radius or
energy identity is assumed. The output version uses the original global
compact-test equation. The coefficient c is arbitrary for the identity and
Cauchy estimate; only domination by the energy requires nonnegative c. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def weakGrushinGradientEnergy (c : ℝ)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) : ℝ :=
  (∑ i : Fin 4, ∫ p, ‖d (yDir i) p‖^2) +
    c*(∑ j : κ, ∫ p, ‖p.1‖^2*‖d (tDir j) p‖^2)

theorem weakGrushinGradientEnergy_eq_cutoff_one (c : ℝ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    weakGrushinGradientEnergy c d = cutoffGradient c (fun _ => 1) f d := by
  simp [weakGrushinGradientEnergy,cutoffGradient,cutoffDirectional]

theorem compact_smooth_jet_energy (c : ℝ)
    {G : Space κ → ℂ} (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hf : (f : Space κ → ℂ) =ᵐ[volume] G)
    (hd : ∀ v, (d v : Space κ → ℂ) =ᵐ[volume] (fun p => fderiv ℝ G p v))
    (he : ∀ v w, (e v w : Space κ → ℂ) =ᵐ[volume]
      (fun p => fderiv ℝ (fun z => fderiv ℝ G z v) p w)) :
    weakGrushinGradientEnergy c d = ∫ p, inner ℝ (f p) (principal c e p) := by
  have hY (i : Fin 4) : (∫ p, ‖d (yDir i) p‖^2) =
      ∫ p, ‖partialYDirectional G (oscillatorBasis i) p‖^2 := by
    apply integral_congr_ae
    filter_upwards [hd (yDir i)] with p hp
    rw [hp]
    rfl
  have hT (j : κ) : (∫ p, ‖p.1‖^2*‖d (tDir j) p‖^2) =
      ∫ p, ‖p.1‖^2*‖partialTDirectional G (oscillatorBasis j) p‖^2 := by
    apply integral_congr_ae
    filter_upwards [hd (tDir j)] with p hp
    rw [hp]
    rfl
  have hgrad : weakGrushinGradientEnergy c d = grushinGradientEnergy c G := by
    simp only [weakGrushinGradientEnergy,grushinGradientEnergy,hY,hT]
    rfl
  have hpair : (∫ p, inner ℝ (f p) (principal c e p)) =
      ∫ p, inner ℝ (G p) (euclideanGrushin c G p) := by
    apply integral_congr_ae
    filter_upwards [hf,principal_ae_smooth c he] with p hp hq
    rw [hp,hq]
  rw [hgrad,hpair]
  exact compact_grushin_energy c hG hcG

theorem compact_weakH2_energy (c : ℝ)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    MemLp (principal c e) 2 volume ∧
      weakGrushinGradientEnergy c d = ∫ p, inner ℝ (f p) (principal c e p) := by
  obtain ⟨L,hL,_hKL,u,g,dg,eg,hu,huc,hus,hgu,hdu,heu,hgconv,hdconv,heconv⟩ :=
    product_compact_weakH2_uniform_support_approximation d e hd he hK hs
  have hgs (n : ℕ) : ∀ᵐ p ∂volume, p ∉ L → g n p = 0 := by
    filter_upwards [hgu n] with p hp ho
    rw [hp]
    exact image_eq_zero_of_notMem_tsupport (fun hx => ho (hus n hx))
  have hds (n : ℕ) (v : Space κ) : ∀ᵐ p ∂volume, p ∉ L → dg n v p = 0 :=
    lp_ae_zero_off_of_directional_support (hus n) (hdu n v)
  have hes (n : ℕ) (v w : Space κ) : ∀ᵐ p ∂volume, p ∉ L → eg n v w p = 0 :=
    lp_ae_zero_off_of_second_directional_support (hus n) (heu n v w)
  have hel (v w : Space κ) : ∀ᵐ p ∂volume, p ∉ L → e v w p = 0 :=
    lp_second_directional_support_of_tendsto hL.measurableSet hus
      (fun n => heu n v w) (heconv v w)
  have hleft : Tendsto (fun n => weakGrushinGradientEnergy c (dg n)) atTop
      (𝓝 (weakGrushinGradientEnergy c d)) := by
    simpa only [← weakGrushinGradientEnergy_eq_cutoff_one] using
      cutoffGradient_tendsto c hL (contDiff_const : ContDiff ℝ ∞ (fun _ : Space κ => (1 : ℝ)))
        hgconv hdconv hgs hds
  have hright : Tendsto (fun n => ∫ p, inner ℝ (g n p) (principal c (eg n) p)) atTop
      (𝓝 (∫ p, inner ℝ (f p) (principal c e p))) := by
    simpa only [one_pow,one_smul] using
      cutoffPrincipalPairing_tendsto c hL (continuous_const : Continuous (fun _ : Space κ => (1 : ℝ)))
        hgconv heconv hgs hes
  have hE (n : ℕ) := compact_smooth_jet_energy c (hu n) (huc n)
    (g n) (dg n) (eg n) (hgu n) (hdu n) (heu n)
  have ht : Tendsto (fun n => weakGrushinGradientEnergy c (dg n)) atTop
      (𝓝 (∫ p, inner ℝ (f p) (principal c e p))) := by
    simpa only [hE] using hright
  exact ⟨principal_memLp c hL e hel,tendsto_nhds_unique hleft ht⟩

theorem weakGrushinGradientEnergy_nonneg {c : ℝ} (hc : 0 ≤ c)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    0 ≤ weakGrushinGradientEnergy c d := by
  unfold weakGrushinGradientEnergy
  exact add_nonneg
    (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
    (mul_nonneg hc (Finset.sum_nonneg (fun _ _ =>
      integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))))

theorem weakGrushin_y_gradient_le_energy {c : ℝ} (hc : 0 ≤ c)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    (∑ i : Fin 4, ∫ p, ‖d (yDir i) p‖^2) ≤ weakGrushinGradientEnergy c d := by
  unfold weakGrushinGradientEnergy
  exact le_add_of_nonneg_right
    (mul_nonneg hc (Finset.sum_nonneg (fun _ _ =>
      integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))))

theorem compact_weakH2_energy_cauchy (c : ℝ)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    (weakGrushinGradientEnergy c d)^2 ≤
      (∫ p, ‖f p‖^2)*(∫ p, ‖principal c e p‖^2) := by
  obtain ⟨hm,henergy⟩ := compact_weakH2_energy c d e hd he hK hs
  rw [henergy]
  exact actual_l2_integral_inner_sq_le (Lp.memLp f) hm

theorem compact_weakH2_energy_output (c : ℝ)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    (weakGrushinGradientEnergy c d = ∫ p, inner ℝ (f p) (h p)) ∧
      (weakGrushinGradientEnergy c d)^2 ≤ ‖f‖^2*‖h‖^2 := by
  have ha := principal_ae_eq_of_weak_output c d e hd he hP
  have hp : (∫ p, inner ℝ (f p) (principal c e p)) =
      ∫ p, inner ℝ (f p) (h p) := by
    apply integral_congr_ae
    filter_upwards [ha] with p hp
    rw [hp]
  have henergy := (compact_weakH2_energy c d e hd he hK hs).2.trans hp
  refine ⟨henergy,?_⟩
  rw [henergy,l2_norm_sq_integral f,l2_norm_sq_integral h]
  exact actual_l2_integral_inner_sq_le (Lp.memLp f) (Lp.memLp h)

theorem compact_weakH2_y_gradient_square_output {c : ℝ} (hc : 0 ≤ c)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    (∑ i : Fin 4, ∫ p, ‖d (yDir i) p‖^2)^2 ≤ ‖f‖^2*‖h‖^2 := by
  have hy : 0 ≤ ∑ i : Fin 4, ∫ p, ‖d (yDir i) p‖^2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  exact (pow_le_pow_left₀ hy (weakGrushin_y_gradient_le_energy hc d) 2).trans
    (compact_weakH2_energy_output c d e hd he hK hs hP).2

end TheoremT.Continuum.WeakGrushin
