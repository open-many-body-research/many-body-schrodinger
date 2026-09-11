import WeakGrushinCutoffLimits_v1
import CompactWeakGrushinEstimates_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem smooth_cutoff_jet_energy (c : ℝ)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {G : Space κ → ℂ} (hG : ContDiff ℝ ∞ G)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hf : (f : Space κ → ℂ) =ᵐ[volume] G)
    (hd : ∀ v, (d v : Space κ → ℂ) =ᵐ[volume] (fun p => fderiv ℝ G p v))
    (he : ∀ v w, (e v w : Space κ → ℂ) =ᵐ[volume]
      (fun p => fderiv ℝ (fun z => fderiv ℝ G z v) p w)) :
    cutoffGradient c η f d =
      (∫ p, inner ℝ ((η p)^2 • f p) (principal c e p)) + grushinCutoffEnergy c η f := by
  have hD (v : Space κ) : cutoffDirectional η f d v =ᵐ[volume]
      (fun p => fderiv ℝ (fun q => η q • G q) p v) := by
    filter_upwards [hf,hd v] with p hp hq
    simp only [cutoffDirectional,hp,hq,cutoff_directional_product hη hG,add_comm]
  have hY (i : Fin 4) : (∫ p, ‖cutoffDirectional η f d (yDir i) p‖^2) =
      ∫ p, ‖partialYDirectional (fun q => η q • G q) (oscillatorBasis i) p‖^2 := by
    apply integral_congr_ae
    filter_upwards [hD (yDir i)] with p hp
    rw [hp]
    rfl
  have hT (j : κ) : (∫ p, ‖p.1‖^2*‖cutoffDirectional η f d (tDir j) p‖^2) =
      ∫ p, ‖p.1‖^2*‖partialTDirectional (fun q => η q • G q) (oscillatorBasis j) p‖^2 := by
    apply integral_congr_ae
    filter_upwards [hD (tDir j)] with p hp
    rw [hp]
    rfl
  have hgrad : cutoffGradient c η f d = grushinGradientEnergy c (fun q => η q • G q) := by
    simp only [cutoffGradient,grushinGradientEnergy,hY,hT]
    rfl
  have herr : grushinCutoffEnergy c η f = grushinCutoffEnergy c η G := by
    unfold grushinCutoffEnergy
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [hf] with p hp
      rw [hp]
    · congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [hf] with p hp
      rw [hp]
  have hpair : (∫ p, inner ℝ ((η p)^2 • f p) (principal c e p)) =
      ∫ p, inner ℝ ((η p)^2 • G p) (euclideanGrushin c G p) := by
    apply integral_congr_ae
    filter_upwards [hf,principal_ae_smooth c he] with p hp hq
    rw [hp,hq]
  rw [hgrad,herr,hpair]
  exact compact_cutoff_grushin_energy c hη hcη hG

theorem compact_weakH2_cutoff_energy (c : ℝ)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    cutoffGradient c η f d =
      (∫ p, inner ℝ ((η p)^2 • f p) (principal c e p)) + grushinCutoffEnergy c η f := by
  obtain ⟨L,hL,hKL,u,g,dg,eg,hu,huc,hus,hgu,hdu,heu,hgconv,hdconv,heconv⟩ :=
    product_compact_weakH2_uniform_support_approximation d e hd he hK hs
  have hgs (n : ℕ) : ∀ᵐ p ∂volume, p ∉ L → g n p = 0 := by
    filter_upwards [hgu n] with p hp ho
    rw [hp]
    exact image_eq_zero_of_notMem_tsupport (fun hx => ho (hus n hx))
  have hds (n : ℕ) (v : Space κ) : ∀ᵐ p ∂volume, p ∉ L → dg n v p = 0 :=
    lp_ae_zero_off_of_directional_support (hus n) (hdu n v)
  have hes (n : ℕ) (v w : Space κ) : ∀ᵐ p ∂volume, p ∉ L → eg n v w p = 0 :=
    lp_ae_zero_off_of_second_directional_support (hus n) (heu n v w)
  have hleft := cutoffGradient_tendsto c hL hη hgconv hdconv hgs hds
  have hright := (cutoffPrincipalPairing_tendsto c hL hη.continuous hgconv heconv hgs hes).add
    (cutoffError_tendsto c hL hη hgconv hgs)
  have hE (n : ℕ) := smooth_cutoff_jet_energy c hη hcη (hu n)
    (g n) (dg n) (eg n) (hgu n) (hdu n) (heu n)
  have ht : Tendsto (fun n => cutoffGradient c η (g n) (dg n)) atTop
      (𝓝 ((∫ p, inner ℝ ((η p)^2 • f p) (principal c e p)) + grushinCutoffEnergy c η f)) := by
    simpa only [hE] using hright
  exact tendsto_nhds_unique hleft ht

end TheoremT.Continuum.WeakGrushin
