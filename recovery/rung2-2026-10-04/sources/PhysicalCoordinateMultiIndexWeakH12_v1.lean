import CoordinateMultiIndexWord_v1
import ProductCoordinateWeakWordTests_v1
import PhysicalSpectatorReindexAll_v1

/-! Exact multiindex extraction directly in either physical spectator space.
Only coordinate labels are mapped; domains and test integrals remain physical.
The hypothesis supplies the actual coordinate weak family. No PDE is assumed
to follow merely from indexing, and W is the squared L2 budget.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

def h12PhysicalCoordinateWord (i : Fin 2) (alpha : boundedMultiIndex 7 12) :
    List (Fin 4 ⊕ SpectatorCoordinate i) :=
  (h12CoordinateWord alpha).map
    (Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm)

theorem h12PhysicalCoordinateWord_length (i : Fin 2) (alpha : boundedMultiIndex 7 12) :
    (h12PhysicalCoordinateWord i alpha).length = ∑ k, alpha.val k := by
  rw [h12PhysicalCoordinateWord, List.length_map, h12CoordinateWord_length]

theorem h12PhysicalCoordinateWord_length_le (i : Fin 2) (alpha : boundedMultiIndex 7 12) :
    (h12PhysicalCoordinateWord i alpha).length ≤ 12 := by
  rw [h12PhysicalCoordinateWord_length]
  exact alpha.property

theorem h12PhysicalCoordinateWord_zero (i : Fin 2) :
    h12PhysicalCoordinateWord i h12ZeroMultiIndex = [] := by
  rw [h12PhysicalCoordinateWord, h12CoordinateWord_zero, List.map_nil]

theorem h12PhysicalCoordinateWord_reindex (i : Fin 2) (alpha : boundedMultiIndex 7 12) :
    (h12PhysicalCoordinateWord i alpha).map
      (Sum.map id (twoElectronSpectatorCoordinateEquiv i)) = h12CoordinateWord alpha := by
  rw [h12PhysicalCoordinateWord, List.map_map]
  have hmap : (Sum.map (id : Fin 4 → Fin 4) (twoElectronSpectatorCoordinateEquiv i)) ∘
      (Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm) = id := by
    funext k
    cases k <;> simp
  rw [hmap, List.map_id]

theorem h12PhysicalCoordinateWord_injective (i : Fin 2) :
    Function.Injective (h12PhysicalCoordinateWord i) := by
  intro alpha beta h
  apply h12CoordinateWord_injective
  have hm := congrArg
    (List.map (Sum.map id (twoElectronSpectatorCoordinateEquiv i))) h
  simpa only [h12PhysicalCoordinateWord_reindex] using hm

def physicalH12RegionL2Sum (i : Fin 2)
    (V : boundedMultiIndex 7 12 → Space (SpectatorCoordinate i) → ℂ)
    (Ω : Set (Space (SpectatorCoordinate i))) : ℝ :=
  ∑ alpha ∈ h12MultiIndices, ∫ p in Ω, ‖V alpha p‖^2

theorem physicalH12RegionL2Sum_le (i : Fin 2)
    {Ω : Set (Space (SpectatorCoordinate i))} {W : ℝ}
    (V : boundedMultiIndex 7 12 → Space (SpectatorCoordinate i) → ℂ)
    (hV : ∀ alpha, RegionL2Budget (V alpha) Ω W) :
    physicalH12RegionL2Sum i V Ω ≤ 50388 * W := by
  calc
    physicalH12RegionL2Sum i V Ω ≤ ∑ alpha ∈ h12MultiIndices, W :=
      Finset.sum_le_sum (fun alpha _ => (hV alpha).2)
    _ = 50388 * W := by
      rw [Finset.sum_const, nsmul_eq_mul, h12MultiIndices_card]
      norm_num

theorem physical_coordinateWeakHk_multiIndex_extraction (i : Fin 2)
    {Ω : Set (Space (SpectatorCoordinate i))} {f : Space (SpectatorCoordinate i) → ℂ} {W : ℝ}
    (hf : ProductCoordinateWeakHk Ω f 12 W) :
    ∃ V : boundedMultiIndex 7 12 → Space (SpectatorCoordinate i) → ℂ,
      V h12ZeroMultiIndex = f ∧
      (∀ alpha, RegionL2Budget (V alpha) Ω W) ∧
      physicalH12RegionL2Sum i V Ω ≤ 50388 * W ∧
      ∀ alpha (φ : Space (SpectatorCoordinate i) → ℝ), ContDiff ℝ ∞ φ →
        HasCompactSupport φ → tsupport φ ⊆ Ω →
        Integrable (fun p => φ p • V alpha p) ∧
        Integrable (fun p => productCoordinateTestWord (h12PhysicalCoordinateWord i alpha) φ p • f p) ∧
        (∫ p, φ p • V alpha p) =
          ((-1 : ℝ)^(∑ k, alpha.val k)) •
            (∫ p, productCoordinateTestWord (h12PhysicalCoordinateWord i alpha) φ p • f p) := by
  obtain ⟨D, h0, hBudget, hD⟩ := hf
  let V := fun alpha : boundedMultiIndex 7 12 => D (h12PhysicalCoordinateWord i alpha)
  have hV : ∀ alpha, RegionL2Budget (V alpha) Ω W :=
    fun alpha => hBudget _ (h12PhysicalCoordinateWord_length_le i alpha)
  refine ⟨V, ?_, hV, physicalH12RegionL2Sum_le i V hV, ?_⟩
  · change D (h12PhysicalCoordinateWord i h12ZeroMultiIndex) = f
    rw [h12PhysicalCoordinateWord_zero, h0]
  · intro alpha φ hφ hc hs
    have hi := product_coordinate_family_tests_integrable D hBudget
      (h12PhysicalCoordinateWord i alpha) (h12PhysicalCoordinateWord_length_le i alpha) hφ hc hs
    refine ⟨hi.1, ?_, ?_⟩
    · simpa only [h0] using hi.2
    · simpa only [h12PhysicalCoordinateWord_length] using
        product_coordinate_family_test_identity D h0 hD (h12PhysicalCoordinateWord i alpha)
          (h12PhysicalCoordinateWord_length_le i alpha) hφ hc hs

theorem physical_mixedTriangularState_multiIndex_extraction (i : Fin 2)
    {Ω : Set (Space (SpectatorCoordinate i))} {f : Space (SpectatorCoordinate i) → ℂ} {W : ℝ}
    (hf : MixedTriangularState Ω f 12 12 W) :
    ∃ V : boundedMultiIndex 7 12 → Space (SpectatorCoordinate i) → ℂ,
      V h12ZeroMultiIndex = f ∧
      (∀ alpha, RegionL2Budget (V alpha) Ω W) ∧
      physicalH12RegionL2Sum i V Ω ≤ 50388 * W ∧
      ∀ alpha (φ : Space (SpectatorCoordinate i) → ℝ), ContDiff ℝ ∞ φ →
        HasCompactSupport φ → tsupport φ ⊆ Ω →
        Integrable (fun p => φ p • V alpha p) ∧
        Integrable (fun p => productCoordinateTestWord (h12PhysicalCoordinateWord i alpha) φ p • f p) ∧
        (∫ p, φ p • V alpha p) =
          ((-1 : ℝ)^(∑ k, alpha.val k)) •
            (∫ p, productCoordinateTestWord (h12PhysicalCoordinateWord i alpha) φ p • f p) :=
  physical_coordinateWeakHk_multiIndex_extraction i (mixedTriangularState_coordinateWeakHk hf)

end TheoremT.Continuum.WeakGrushin
