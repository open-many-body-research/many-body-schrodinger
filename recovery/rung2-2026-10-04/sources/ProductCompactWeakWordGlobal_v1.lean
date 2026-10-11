import ProductCompactWeakDirectionalGlobal_v1

/-! A single actual global L2 family for the finite weak derivatives of a
compact cutoff times a raw local weak family. The ordered Leibniz formula is
explicit and every component is supported in the cutoff support. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
variable {ι : Type}

theorem directionalWordDeriv_tsupport_subset (dirs : ι → Y × T) (χ : Y × T → ℝ)
    (w : List ι) : tsupport (directionalWordDeriv dirs χ w) ⊆ tsupport χ := by
  induction w with
  | nil => exact subset_rfl
  | cons i w ih => exact (tsupport_fderiv_apply_subset ℝ (dirs i)).trans ih

theorem directionalWordProduct_support_subset (dirs : ι → Y × T) (χ : Y × T → ℝ)
    (D : List ι → Y × T → ℂ) (w : List ι) :
    Function.support (directionalWordProduct dirs χ D w) ⊆ tsupport χ := by
  intro p hp
  by_contra hn
  apply hp
  unfold directionalWordProduct
  have hz : ∀ ab : List ι × List ι,
      directionalWordDeriv dirs χ ab.1 p • D ab.2 p = 0 := by
    intro ab
    rw [image_eq_zero_of_notMem_tsupport (fun h => hn (directionalWordDeriv_tsupport_subset dirs χ ab.1 h)),zero_smul]
  simp only [hz]
  induction WeakGrushin.spectatorWordSplits w with
  | nil => simp
  | cons a l ih => simpa using ih

theorem product_compact_local_weak_word_family_global
    {Ω K : Set (Y × T)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKO : K ⊆ Ω)
    (dirs : ι → Y × T) (D : List ι → Y × T → ℂ) {m : ℕ}
    (hL2 : ∀ w, w.length ≤ m → ProductLocallyL2On (D w) Ω)
    (hD : ∀ w i, w.length < m → ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (dirs i))
    (hs : ∀ w, w.length ≤ m → Function.support (D w) ⊆ K) :
    ∃ F : List ι → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ w, w.length ≤ m → F w =ᵐ[volume] D w) ∧
      (∀ w i, w.length < m → WeakProductL2Directional (F w) (F (i :: w)) (dirs i)) := by
  classical
  have hm (w : List ι) (hw : w.length ≤ m) : MemLp (D w) 2 volume :=
    product_locallyL2_memLp_of_compact_support hK hKO (hL2 w hw) (hs w hw)
  let F : List ι → Lp ℂ 2 (volume : Measure (Y × T)) :=
    fun w => if hw : w.length ≤ m then (hm w hw).toLp (D w) else 0
  have hF (w : List ι) (hw : w.length ≤ m) : F w =ᵐ[volume] D w := by
    dsimp only [F]
    rw [dite_eq_left hw]
    exact (hm w hw).coeFn_toLp
  refine ⟨F,hF,?_⟩
  intro w i hw φ hφ hcφ
  have hwi : (i :: w).length ≤ m := by simp only [List.length_cons]; omega
  have hL : (∫ p, φ p • F (i :: w) p) = ∫ p, φ p • D (i :: w) p := by
    apply integral_congr_ae
    filter_upwards [hF (i :: w) hwi] with p hp
    rw [hp]
  have hR : (∫ p, fderiv ℝ φ p (dirs i) • F w p) =
      ∫ p, fderiv ℝ φ p (dirs i) • D w p := by
    apply integral_congr_ae
    filter_upwards [hF w hw.le] with p hp
    rw [hp]
  rw [hL,hR]
  exact (hD w i hw).global_tests_of_compact_support hΩ hK hKO
    (hs w hw.le) (hs (i :: w) hwi) φ hφ hcφ

theorem product_compact_cutoff_finite_weak_word_family
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω)
    (dirs : ι → Y × T) {χ : Y × T → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω)
    (D : List ι → Y × T → ℂ) {m : ℕ}
    (hL2 : ∀ w, w.length ≤ m → ProductLocallyL2On (D w) Ω)
    (hD : ∀ w i, w.length < m → ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (dirs i)) :
    ∃ F : List ι → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ w, w.length ≤ m → F w =ᵐ[volume] directionalWordProduct dirs χ D w) ∧
      (∀ w i, w.length < m → WeakProductL2Directional (F w) (F (i :: w)) (dirs i)) :=
  product_compact_local_weak_word_family_global hΩ hcχ hsχ dirs
    (directionalWordProduct dirs χ D)
    (directionalWordProduct_locallyL2 dirs hΩ hχ.contDiffOn D hL2)
    (directionalWordProduct_localD dirs hΩ hχ.contDiffOn D hD)
    (fun w _ => directionalWordProduct_support_subset dirs χ D w)

end TheoremT.Continuum
