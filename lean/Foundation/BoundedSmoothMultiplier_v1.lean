import HardyWeakCutoff_v2

/-! Bounded smooth real multipliers on the actual weak Sobolev domain. Compact
support of the multiplier is unnecessary; compactness remains on test functions.
These are mathematical L² maps, not executable integration algorithms. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

def boundedRealMul {N : ℕ} (χ : Configuration N → ℝ) (hχ : MemLp χ (⊤ : ENNReal) volume)
    (f : SpatialL2 N) : SpatialL2 N :=
  ((Lp.memLp f).smul hχ).toLp (fun x => χ x • f x)

theorem boundedRealMul_ae {N : ℕ} (χ : Configuration N → ℝ)
    (hχ : MemLp χ (⊤ : ENNReal) volume) (f : SpatialL2 N) :
    boundedRealMul χ hχ f =ᵐ[volume] (fun x => χ x • f x) :=
  MemLp.coeFn_toLp _

theorem integral_test_boundedRealMul {N : ℕ} (χ : Configuration N → ℝ)
    (hχ : MemLp χ (⊤ : ENNReal) volume) (f : SpatialL2 N) (φ : Configuration N → ℝ) :
    (∫ x, φ x • boundedRealMul χ hχ f x) = (∫ x, (φ x * χ x) • f x) := by
  apply integral_congr_ae
  filter_upwards [boundedRealMul_ae χ hχ f] with x hx
  rw [hx,mul_smul]

theorem weakPartial_boundedRealMul {N : ℕ} {f g : SpatialL2 N} {k : Coordinate N}
    (hg : WeakPartial f g k) (χ : Configuration N → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hm : MemLp χ (⊤ : ENNReal) volume)
    (hdm : MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) (⊤ : ENNReal) volume) :
    WeakPartial (boundedRealMul χ hm f)
      (boundedRealMul χ hm g +
        boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) hdm f) k := by
  intro φ hφ hcφ
  have hdχ : Continuous (fun x => fderiv ℝ χ x (coordinateVector k)) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x (coordinateVector k)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hprod (x : Configuration N) :
      fderiv ℝ (fun y => φ y * χ y) x (coordinateVector k) =
        φ x * fderiv ℝ χ x (coordinateVector k) +
        fderiv ℝ φ x (coordinateVector k) * χ x := by
    have hh := (hφ.differentiable (by simp) x).hasFDerivAt.mul
      ((hχ.differentiable (by simp) x).hasFDerivAt)
    change HasFDerivAt (𝕜 := ℝ) (fun y => φ y * χ y) _ x at hh
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have hb : Integrable (fun x => (φ x * fderiv ℝ χ x (coordinateVector k)) • f x) :=
    test_integrable f (hφ.continuous.mul hdχ) hcφ.mul_right
  have hc : Integrable (fun x => (fderiv ℝ φ x (coordinateVector k) * χ x) • f x) :=
    test_integrable f (hdφ.mul hχ.continuous) (hcφ.fderiv_apply ℝ (coordinateVector k)).mul_right
  have htest := hg (fun x => φ x * χ x) (hφ.mul hχ) hcφ.mul_right
  have he : (∫ x, fderiv ℝ (fun y => φ y * χ y) x (coordinateVector k) • f x) =
      (∫ x, (φ x * fderiv ℝ χ x (coordinateVector k)) • f x) +
      (∫ x, (fderiv ℝ φ x (coordinateVector k) * χ x) • f x) := by
    simp_rw [hprod,add_smul]
    exact integral_add hb hc
  rw [he] at htest
  rw [integral_test_add _ _ hφ.continuous hcφ,
    integral_test_boundedRealMul,integral_test_boundedRealMul,
    integral_test_boundedRealMul,htest]
  abel

theorem HasH1.mul_bounded_smooth {N : ℕ} {f : SpatialL2 N} (hf : HasH1 f)
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hm : MemLp χ (⊤ : ENNReal) volume)
    (hdm : ∀ k : Coordinate N,
      MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) (⊤ : ENNReal) volume) :
    HasH1 (boundedRealMul χ hm f) := by
  obtain ⟨d,hd⟩ := hf
  exact ⟨fun k => boundedRealMul χ hm (d k) +
    boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) (hdm k) f,
    fun k => weakPartial_boundedRealMul (hd k) χ hχ hm (hdm k)⟩

theorem HasH2.mul_bounded_smooth {N : ℕ} {f : SpatialL2 N} (hf : HasH2 f)
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hm : MemLp χ (⊤ : ENNReal) volume)
    (hdm : ∀ k : Coordinate N,
      MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) (⊤ : ENNReal) volume)
    (hddm : ∀ k l : Coordinate N, MemLp
      (fun x => fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector k)) x
        (coordinateVector l)) (⊤ : ENNReal) volume) : HasH2 (boundedRealMul χ hm f) := by
  obtain ⟨d,hd,hdd⟩ := hf
  have hχd (k : Coordinate N) :
      ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (coordinateVector k)) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  refine ⟨fun k => boundedRealMul χ hm (d k) +
    boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) (hdm k) f,
    fun k => weakPartial_boundedRealMul (hd k) χ hχ hm (hdm k),?_⟩
  intro k l
  obtain ⟨e,he⟩ := hdd k l
  exact ⟨_,weakPartial_add
    (weakPartial_boundedRealMul he χ hχ hm (hdm l))
    (weakPartial_boundedRealMul (hd l) _ (hχd k) (hdm k) (hddm k l))⟩

#print axioms weakPartial_boundedRealMul
#print axioms HasH1.mul_bounded_smooth
#print axioms HasH2.mul_bounded_smooth
end TheoremT.Continuum
