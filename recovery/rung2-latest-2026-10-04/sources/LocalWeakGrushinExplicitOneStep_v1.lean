import LocalWeakGrushinExplicitCutoffOutput_v1
import LocalWeakGrushinOneStep_v1

/-! Actual derivative-free local Grushin gain with exposed cutoff constants.
All five constants bound explicit cutoff functions/derivatives. No smoothness
or derivative of the input is assumed; the actual partial regularization and
weak-limit argument preserve the separate input/source coefficients. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weak_grushin_explicit_one_step {c : ℝ} (hc : 0 < c)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ η : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {W : Set (Space κ)} (hW : IsOpen W) (hχW : tsupport χ ⊆ W)
    (hη1 : ∀ p ∈ W, η p = 1)
    (M A B D Q : ℝ) (hB0 : 0 ≤ B) (hD0 : 0 ≤ D) (hQ0 : 0 ≤ Q)
    (hM : ∀ p, |χ p| ≤ M)
    (hA : ∀ p ∈ tsupport χ, |combinedCutoffScalar c χ p| ≤ A)
    (hB : ∀ p ∈ tsupport χ, cutoffGradientWeight c χ p ≤ B)
    (hD : ∀ p, (η p)^2 ≤ D) (hQ : ∀ p, grushinCutoffWeight c η p ≤ Q)
    (f h : Lp ℂ 2 (volume : Measure (Space κ)))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    let J : ℝ := (4*A^2+16*B*(D/2+Q))*‖f‖^2+(2*M^2+8*B*D)*‖h‖^2
    ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
      U =ᵐ[volume] (fun p => χ p • f p) ∧ ‖U‖^2 ≤ M^2*‖f‖^2 ∧
      (∑ i, ‖gy i‖^2) ≤ 2*(M^2*‖f‖^2)+(3/4 : ℝ)*J ∧
      (∑ j, ‖gt j‖^2) ≤ J/(16*c) ∧
      (∑ i, ∑ j, ‖hyy i j‖^2) ≤ (3/2 : ℝ)*J ∧
      (∀ i, WeakProductL2Directional U (gy i) (yDir i)) ∧
      (∀ j, WeakProductL2Directional U (gt j) (tDir j)) ∧
      ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  dsimp only
  let C0 : ℝ := 4*A^2+16*B*(D/2+Q)
  let C1 : ℝ := 2*M^2+8*B*D
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  obtain ⟨K,hK,hKΩ,V,hV,hηV,hVK⟩ := product_compact_intermediate_neighborhood hcη hΩ hηΩ
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
        ‖u n‖^2 ≤ M^2*‖f‖^2 ∧ ‖H‖^2 ≤ C0*‖f‖^2+C1*‖h‖^2 := by
    filter_upwards [hstage] with n hn
    obtain ⟨S,H,a,b,hS,ha,hb,hSs,_,hSH,hSn,hHn⟩ :=
      local_weakH2_explicit_cutoff_output hc.le hV hχ hcχ hη hcη hηV hW hχW hη1
        M A B D Q hB0 hM hA hB hD hQ (partialMollifyLp n f) (partialMollifyLp n h) hn.1 hn.2
    have heS : S = u n := Lp.ext
      (hS.trans (measureBoundedRealMul_ae χ hχtop (partialMollifyLp n f)).symm)
    rw [heS] at ha hSs hSH hSn
    have hf2 := pow_le_pow_left₀ (norm_nonneg _) (hcontract n).1 2
    have hh2 := pow_le_pow_left₀ (norm_nonneg _) (hcontract n).2 2
    exact ⟨H,a,b,tsupport χ,ha,hb,hcχ,hSs,hSH,
      hSn.trans (mul_le_mul_of_nonneg_left hf2 (sq_nonneg M)),
      hHn.trans (add_le_add (mul_le_mul_of_nonneg_left hf2 hC0)
        (mul_le_mul_of_nonneg_left hh2 hC1))⟩
  have hUn : ‖U‖^2 ≤ M^2*‖f‖^2 := le_of_tendsto (hu.norm.pow 2) (by
    filter_upwards [ha] with n hn
    obtain ⟨H,d,e,L,_,_,_,_,_,hb,_⟩ := hn
    exact hb)
  obtain ⟨gy,gt,hyy,hY,hT,hYY,hgy,hgt,hhyy⟩ :=
    anisotropic_limit_of_eventually_exists_compact_outputs hc u U hu ha
  exact ⟨U,gy,gt,hyy,hU,hUn,hY,hT,hYY,hgy,hgt,hhyy⟩

#print axioms local_weak_grushin_explicit_one_step
end TheoremT.Continuum.WeakGrushin
