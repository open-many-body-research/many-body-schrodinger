import ProductSevenCoordinateTransport_v1
import SmoothWordBoxContinuousRepresentative_v1

/-! Concrete physical product word mollifiers supply all ordinary seven-coordinate
smooth approximants and their actual restricted L2 limits. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
open WeakGrushin

def sevenProductL2Pullback :
    Lp ℂ 2 (volume : Measure (Space (Fin 3))) →ₗᵢ[ℝ] Lp ℂ 2 (volume : Measure (Fin 7 → ℝ)) :=
  Lp.compMeasurePreservingₗᵢ ℝ sevenToProduct sevenToProduct_measurePreserving

def sevenRestrictL2 (K : Set (Fin 7 → ℝ)) :
    Lp ℂ 2 (volume : Measure (Fin 7 → ℝ)) →L[ℝ] Lp ℂ 2 (volume.restrict K) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by norm_num) (by simpa using Measure.restrict_le_self (μ := volume) (s := K))

def productSevenMollifier
    (D : List (Fin 4 ⊕ Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (n : ℕ) : (Fin 7 → ℝ) → ℂ :=
  productMollifiedWord productCoordinateDirection D n [] ∘ sevenToProduct

def productSevenWordLimit (K : Set (Fin 7 → ℝ))
    (D : List (Fin 4 ⊕ Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (w : List (Fin 7)) : Lp ℂ 2 (volume.restrict K) :=
  sevenRestrictL2 K (sevenProductL2Pullback (D (w.map sevenCoordinateEquiv)))

def productSevenMollifiedWordLp (K : Set (Fin 7 → ℝ))
    (D : List (Fin 4 ⊕ Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (n : ℕ) (w : List (Fin 7)) : Lp ℂ 2 (volume.restrict K) :=
  sevenRestrictL2 K (sevenProductL2Pullback
    (productMollifiedWordLp D n (w.map sevenCoordinateEquiv)))

theorem productSevenMollifier_contDiff
    (D : List (Fin 4 ⊕ Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (n : ℕ) :
    ContDiff ℝ ∞ (productSevenMollifier D n) :=
  (productMollifiedWord_contDiff productCoordinateDirection D n []).comp sevenToProduct.contDiff

theorem productSevenWordLimit_ae (K : Set (Fin 7 → ℝ))
    (D : List (Fin 4 ⊕ Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (w : List (Fin 7)) :
    (productSevenWordLimit K D w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict K]
      (D (w.map sevenCoordinateEquiv) : Space (Fin 3) → ℂ) ∘ sevenToProduct := by
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _).trans
    (ae_restrict_of_ae (Lp.coeFn_compMeasurePreserving _ sevenToProduct_measurePreserving))

theorem productSevenMollifiedWordLp_ae (K : Set (Fin 7 → ℝ))
    (D : List (Fin 4 ⊕ Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) {m : ℕ}
    (hD : ∀ w i, w.length < m →
      WeakProductL2Directional (D w) (D (i :: w)) (productCoordinateDirection i))
    (n : ℕ) (w : List (Fin 7)) (hw : w.length ≤ m) :
    (productSevenMollifiedWordLp K D n w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict K]
      coordinateWordDeriv7 (productSevenMollifier D n) w := by
  have hmap := productMollifiedWordLp_ae productCoordinateDirection D hD n
    (w.map sevenCoordinateEquiv) (by simpa using hw)
  have h := sevenToProduct_measurePreserving.quasiMeasurePreserving.ae hmap
  have hc : (productSevenMollifiedWordLp K D n w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict K]
      (productMollifiedWordLp D n (w.map sevenCoordinateEquiv) : Space (Fin 3) → ℂ) ∘ sevenToProduct :=
    (Lp.coeFn_LpToLpOfMeasureLeSMul _ _
      (sevenProductL2Pullback (productMollifiedWordLp D n (w.map sevenCoordinateEquiv)))).trans
    (ae_restrict_of_ae (Lp.coeFn_compMeasurePreserving _ sevenToProduct_measurePreserving))
  rw [show coordinateWordDeriv7 (productSevenMollifier D n) w =
      productMollifiedWord productCoordinateDirection D n (w.map sevenCoordinateEquiv) ∘ sevenToProduct
      from sevenToProduct_word_chain D n w]
  exact hc.trans (ae_restrict_of_ae h)

theorem productSevenMollifiedWordLp_tendsto (K : Set (Fin 7 → ℝ))
    (D : List (Fin 4 ⊕ Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (w : List (Fin 7)) :
    Tendsto (fun n => productSevenMollifiedWordLp K D n w) atTop (𝓝 (productSevenWordLimit K D w)) :=
  ((sevenRestrictL2 K).continuous.tendsto _).comp
    ((sevenProductL2Pullback.continuous.tendsto _).comp
      (productMollifiedWordLp_tendsto D (w.map sevenCoordinateEquiv)))

theorem product_weak_words7_continuous_representatives
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (D : List (Fin 4 ⊕ Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) {m : ℕ}
    (hD : ∀ w i, w.length < m+7 →
      WeakProductL2Directional (D w) (D (i :: w)) (productCoordinateDirection i)) :
    ∃ G : List (Fin 7) → (Fin 7 → ℝ) → ℂ, ∀ w, w.length ≤ m →
      ContinuousOn (G w) (tensorClosedBox7 a b) ∧
      TendstoUniformlyOn (fun n => coordinateWordDeriv7 (productSevenMollifier D n) w)
        (G w) atTop (tensorClosedBox7 a b) ∧
      ((D (w.map sevenCoordinateEquiv) : Space (Fin 3) → ℂ) ∘ sevenToProduct)
        =ᵐ[volume.restrict (tensorClosedBox7 a b)] G w := by
  obtain ⟨G,hG⟩ := smooth_words7_continuous_representatives_of_L2_limits hab
    (productSevenMollifier D) (productSevenMollifier_contDiff D)
    (productSevenMollifiedWordLp (tensorClosedBox7 a b) D)
    (productSevenMollifiedWordLp_ae _ D hD)
    (productSevenWordLimit (tensorClosedBox7 a b) D)
    (fun w _ => productSevenMollifiedWordLp_tendsto _ D w)
  refine ⟨G,fun w hw => ⟨(hG w hw).1,(hG w hw).2.1,?_⟩⟩
  exact (productSevenWordLimit_ae _ D w).symm.trans (hG w hw).2.2

end TheoremT.Continuum
