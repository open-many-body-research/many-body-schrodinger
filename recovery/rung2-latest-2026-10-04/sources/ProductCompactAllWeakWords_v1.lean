import ProductCompactWeakWordGlobal_v1

/-! One actual global L2 word family for every derivative order of a fixed
compact cutoff. The cutoff and global family are chosen before the order. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
variable {ι : Type}

theorem product_compact_local_all_weak_words_global
    {Ω K : Set (Y × T)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKO : K ⊆ Ω)
    (dirs : ι → Y × T) (D : List ι → Y × T → ℂ)
    (hL2 : ∀ w, ProductLocallyL2On (D w) Ω)
    (hD : ∀ w i, ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (dirs i))
    (hs : ∀ w, Function.support (D w) ⊆ K) :
    ∃ F : List ι → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ w, F w =ᵐ[volume] D w) ∧
      (∀ w i, WeakProductL2Directional (F w) (F (i :: w)) (dirs i)) := by
  have hm (w : List ι) : MemLp (D w) 2 volume :=
    product_locallyL2_memLp_of_compact_support hK hKO (hL2 w) (hs w)
  let F : List ι → Lp ℂ 2 (volume : Measure (Y × T)) := fun w => (hm w).toLp (D w)
  have hF (w : List ι) : F w =ᵐ[volume] D w := (hm w).coeFn_toLp
  refine ⟨F,hF,?_⟩
  intro w i φ hφ hcφ
  have hL : (∫ p, φ p • F (i :: w) p) = ∫ p, φ p • D (i :: w) p := by
    apply integral_congr_ae
    filter_upwards [hF (i :: w)] with p hp
    rw [hp]
  have hR : (∫ p, fderiv ℝ φ p (dirs i) • F w p) =
      ∫ p, fderiv ℝ φ p (dirs i) • D w p := by
    apply integral_congr_ae
    filter_upwards [hF w] with p hp
    rw [hp]
  rw [hL,hR]
  exact (hD w i).global_tests_of_compact_support hΩ hK hKO (hs w) (hs (i :: w)) φ hφ hcφ

theorem product_compact_cutoff_all_weak_word_family
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω)
    (dirs : ι → Y × T) {χ : Y × T → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω)
    (D : List ι → Y × T → ℂ)
    (hL2 : ∀ w, ProductLocallyL2On (D w) Ω)
    (hD : ∀ w i, ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (dirs i)) :
    ∃ F : List ι → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ w, F w =ᵐ[volume] directionalWordProduct dirs χ D w) ∧
      (∀ w i, WeakProductL2Directional (F w) (F (i :: w)) (dirs i)) := by
  apply product_compact_local_all_weak_words_global hΩ hcχ hsχ dirs
    (directionalWordProduct dirs χ D)
  · intro w
    exact directionalWordProduct_locallyL2 dirs hΩ hχ.contDiffOn D
      (m := w.length) (fun v _ => hL2 v) w le_rfl
  · intro w i
    exact directionalWordProduct_localD dirs hΩ hχ.contDiffOn D
      (m := w.length+1) (fun v j _ => hD v j) w i (Nat.lt_succ_self _)
  · exact directionalWordProduct_support_subset dirs χ D

end TheoremT.Continuum
