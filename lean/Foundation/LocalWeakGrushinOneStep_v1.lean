import WeakGrushinCutoffUniformOutput_v1
import WeakGrushinAnisotropicLimitExistsOutput_v1
import GrushinPartialRegularizationSequence_v1
import GrushinPartialCutoffConvergence_v1
import GrushinLocalL2Neighborhood_v1

/-! The actual local anisotropic gain from an L² weak Grushin equation.
No derivative of the original input is assumed. Cutoffs, their constants,
and the interior regularization domain are fixed before the input functions.
The result supplies Y/T first and ordered YY second weak derivatives of χf;
it does not assert full joint H² regularity. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weak_grushin_cutoff_one_step {c : ℝ} (hc : 0 < c)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f h : Lp ℂ 2 (volume : Measure (Space κ))),
      (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) →
      ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        U =ᵐ[volume] (fun p => χ p • f p) ∧
        (∑ i, ‖gy i‖^2) ≤ 2*(C*‖f‖^2)+(3/4 : ℝ)*(C*(‖f‖^2+‖h‖^2)) ∧
        (∑ j, ‖gt j‖^2) ≤ (C*(‖f‖^2+‖h‖^2))/(16*c) ∧
        (∑ i, ∑ j, ‖hyy i j‖^2) ≤ (3/2 : ℝ)*(C*(‖f‖^2+‖h‖^2)) ∧
        (∀ i, WeakProductL2Directional U (gy i) (yDir i)) ∧
        (∀ j, WeakProductL2Directional U (gt j) (tDir j)) ∧
        ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  obtain ⟨K,hK,hKΩ,V,hV,hχV,hVK⟩ := product_compact_intermediate_neighborhood hcχ hΩ hχΩ
  obtain ⟨C,hC,hout⟩ := local_weakH2_cutoff_uniform_output hc.le hV hχ hcχ hχV
  refine ⟨C,hC,?_⟩
  intro f h hP
  have hχtop : MemLp χ ⊤ volume := hχ.continuous.memLp_top_of_hasCompactSupport hcχ volume
  let U := measureBoundedRealMul χ hχtop f
  let u : ℕ → Lp ℂ 2 (volume : Measure (Space κ)) :=
    fun n => measureBoundedRealMul χ hχtop (partialMollifyLp n f)
  have hU : U =ᵐ[volume] (fun p => χ p • f p) := measureBoundedRealMul_ae χ hχtop f
  have hu : Tendsto u atTop (𝓝 U) :=
    partialMollify_cutoff_tendsto_of_eventual_ae hχ.continuous hcχ f
      (Filter.Eventually.of_forall (fun n => measureBoundedRealMul_ae χ hχtop (partialMollifyLp n f))) hU
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  have hsequence := grushin_partial_regularization_sequence c (EuclideanSpace.basisFun κ ℝ)
    hΩ hK hKΩ hV hVK f h (by simpa only [hBasis] using hP)
  rw [hBasis] at hsequence
  obtain ⟨hcontract,_,_,hstage⟩ := hsequence
  have ha : ∀ᶠ n : ℕ in atTop,
      ∃ H : Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ e : Jet κ, ∃ L : Set (Space κ),
        (∀ v, WeakProductL2Directional (u n) (d v) v) ∧
        (∀ v w, WeakProductL2Directional (d v) (e v w) w) ∧
        IsCompact L ∧ (∀ᵐ p ∂volume, p ∉ L → u n p = 0) ∧
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • u n p) = ∫ p, φ p • H p) ∧
        ‖u n‖^2 ≤ C*‖f‖^2 ∧ ‖H‖^2 ≤ C*(‖f‖^2+‖h‖^2) := by
    filter_upwards [hstage] with n hn
    obtain ⟨W,H,a,b,hW,ha,hb,hWs,_,hWH,hWn,hHn⟩ :=
      hout (partialMollifyLp n f) (partialMollifyLp n h) hn.1 hn.2
    have heW : W = u n := Lp.ext
      (hW.trans (measureBoundedRealMul_ae χ hχtop (partialMollifyLp n f)).symm)
    rw [heW] at ha hWs hWH hWn
    have hf2 := pow_le_pow_left₀ (norm_nonneg _) (hcontract n).1 2
    have hh2 := pow_le_pow_left₀ (norm_nonneg _) (hcontract n).2 2
    exact ⟨H,a,b,tsupport χ,ha,hb,hcχ,hWs,hWH,
      hWn.trans (mul_le_mul_of_nonneg_left hf2 hC),
      hHn.trans (mul_le_mul_of_nonneg_left (add_le_add hf2 hh2) hC)⟩
  obtain ⟨gy,gt,hyy,hY,hT,hYY,hgy,hgt,hhyy⟩ :=
    anisotropic_limit_of_eventually_exists_compact_outputs hc u U hu ha
  exact ⟨U,gy,gt,hyy,hU,hY,hT,hYY,hgy,hgt,hhyy⟩

#print axioms local_weak_grushin_cutoff_one_step
end TheoremT.Continuum.WeakGrushin
