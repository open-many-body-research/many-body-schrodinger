import GrushinRectangularBoxGeometry_v1
import SmoothTransitionWindow_v1

/-! Tensor cutoffs with independent Y and T half-widths and one common
positive transition gap. These represent the exact rectangular chart geometry. -/
noncomputable section
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum.WeakGrushin

def grushinRectCutoff (a : Space (Fin 3)) (ry rt g : ℝ) : Space (Fin 3) → ℝ :=
  cutoffRescale (coordinateProduct boxCoordinate (fun i =>
    transitionWindow (boxHalfWidth ry rt i) (boxHalfWidth ry rt i+g))) a 1

theorem grushinRectCutoff_apply (a : Space (Fin 3)) (ry rt g : ℝ) (p : Space (Fin 3)) :
    grushinRectCutoff a ry rt g p = ∏ i, transitionWindow (boxHalfWidth ry rt i)
      (boxHalfWidth ry rt i+g) (boxCoordinate i (p-a)) := by
  simp [grushinRectCutoff,cutoffRescale,cutoffRescaleMap,coordinateProduct]

theorem grushinRectCutoff_contDiff (a : Space (Fin 3)) (ry rt g : ℝ) :
    ContDiff ℝ ∞ (grushinRectCutoff a ry rt g) :=
  cutoffRescale_contDiff (coordinateProduct_contDiff boxCoordinate
    (fun _ => transitionWindow_contDiff _ _)) a 1

theorem grushinRectCutoff_nonneg (a : Space (Fin 3)) (ry rt g : ℝ) (p : Space (Fin 3)) :
    0 ≤ grushinRectCutoff a ry rt g p := by
  rw [grushinRectCutoff_apply]
  exact Finset.prod_nonneg (fun i _ => transitionWindow_nonneg _ _ _)

theorem grushinRectCutoff_le_one (a : Space (Fin 3)) (ry rt g : ℝ) (p : Space (Fin 3)) :
    grushinRectCutoff a ry rt g p ≤ 1 := by
  rw [grushinRectCutoff_apply]
  exact Finset.prod_le_one₀ (fun i _ => transitionWindow_nonneg _ _ _)
    (fun i _ => transitionWindow_le_one _ _ _)

theorem grushinRectCutoff_plateau (a : Space (Fin 3)) (ry rt : ℝ) {g : ℝ} (hg : 0 < g)
    {p : Space (Fin 3)} (hp : p ∈ rectangularClosedBox a ry rt) :
    grushinRectCutoff a ry rt g p = 1 := by
  rw [grushinRectCutoff_apply]
  apply Finset.prod_eq_one
  intro i _
  exact transitionWindow_plateau (by linarith) (abs_le.mp (hp i))

theorem grushinRectCutoff_tsupport (a : Space (Fin 3)) (ry rt : ℝ) {g : ℝ} (hg : 0 < g) :
    tsupport (grushinRectCutoff a ry rt g) ⊆ rectangularClosedBox a (ry+g) (rt+g) := by
  apply closure_minimal _ (rectangularClosedBox_isClosed a (ry+g) (rt+g))
  intro p hp i
  have hne : grushinRectCutoff a ry rt g p ≠ 0 := hp
  rw [grushinRectCutoff_apply] at hne
  have hi : transitionWindow (boxHalfWidth ry rt i) (boxHalfWidth ry rt i+g)
      (boxCoordinate i (p-a)) ≠ 0 := by
    intro hz
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  have hb := abs_le.mpr (transitionWindow_tsupport (show boxHalfWidth ry rt i <
    boxHalfWidth ry rt i+g by linarith) (subset_tsupport _ hi))
  cases i <;> simpa only [boxHalfWidth] using hb

theorem grushinRectCutoff_compact (a : Space (Fin 3)) {ry rt g : ℝ}
    (hy : 0 ≤ ry) (ht : 0 ≤ rt) (hg : 0 < g) :
    HasCompactSupport (grushinRectCutoff a ry rt g) :=
  (rectangularClosedBox_isCompact a (by linarith : 0 ≤ ry+g) (by linarith : 0 ≤ rt+g)).of_isClosed_subset
    (isClosed_tsupport _) (grushinRectCutoff_tsupport a ry rt hg)

theorem grushinRectCutoff_first_bound (a : Space (Fin 3)) (ry rt : ℝ) {C1 g : ℝ}
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1) (hg : 0 < g)
    (j : Fin 4 ⊕ Fin 3) (p : Space (Fin 3)) :
    |fderiv ℝ (grushinRectCutoff a ry rt g) p (boxDirection j)| ≤ 2*C1/g := by
  have hφ := fun i : Fin 4 ⊕ Fin 3 =>
    transitionWindow_contDiff (boxHalfWidth ry rt i) (boxHalfWidth ry rt i+g)
  have hM (i : Fin 4 ⊕ Fin 3) (x : ℝ) :
      |transitionWindow (boxHalfWidth ry rt i) (boxHalfWidth ry rt i+g) x| ≤ 1 := by
    rw [abs_of_nonneg (transitionWindow_nonneg _ _ _)]
    exact transitionWindow_le_one _ _ _
  have hD (i : Fin 4 ⊕ Fin 3) (x : ℝ) :
      |deriv (transitionWindow (boxHalfWidth ry rt i) (boxHalfWidth ry rt i+g)) x| ≤ 2*C1/g := by
    simpa only [add_sub_cancel_left] using transitionWindow_first_bound hC1
      (show boxHalfWidth ry rt i < boxHalfWidth ry rt i+g by linarith) x
  have hb := coordinateProduct_first_bound boxCoordinate hφ j (boxDirection j)
    (fun i => boxCoordinate_direction i j) hM hD (p-a)
  unfold grushinRectCutoff
  rw [cutoffRescale_first (coordinateProduct_contDiff boxCoordinate hφ)]
  simpa [cutoffRescaleMap] using hb

theorem grushinRectCutoff_second_bound (a : Space (Fin 3)) (ry rt : ℝ) {C1 C2 g : ℝ}
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) (hg : 0 < g)
    (j : Fin 4 ⊕ Fin 3) (p : Space (Fin 3)) :
    |fderiv ℝ (fun q => fderiv ℝ (grushinRectCutoff a ry rt g) q (boxDirection j)) p
      (boxDirection j)| ≤ 2*(C2+C1^2)/g^2 := by
  have hφ := fun i : Fin 4 ⊕ Fin 3 =>
    transitionWindow_contDiff (boxHalfWidth ry rt i) (boxHalfWidth ry rt i+g)
  have hM (i : Fin 4 ⊕ Fin 3) (x : ℝ) :
      |transitionWindow (boxHalfWidth ry rt i) (boxHalfWidth ry rt i+g) x| ≤ 1 := by
    rw [abs_of_nonneg (transitionWindow_nonneg _ _ _)]
    exact transitionWindow_le_one _ _ _
  have hD (i : Fin 4 ⊕ Fin 3) (x : ℝ) :
      |deriv (deriv (transitionWindow (boxHalfWidth ry rt i) (boxHalfWidth ry rt i+g))) x| ≤
        2*(C2+C1^2)/g^2 := by
    simpa only [add_sub_cancel_left] using transitionWindow_second_bound hC1 hC2
      (show boxHalfWidth ry rt i < boxHalfWidth ry rt i+g by linarith) x
  have hb := coordinateProduct_second_bound boxCoordinate hφ j (boxDirection j)
    (fun i => boxCoordinate_direction i j) hM hD (p-a)
  unfold grushinRectCutoff
  rw [cutoffRescale_second (coordinateProduct_contDiff boxCoordinate hφ)]
  simpa [cutoffRescaleMap] using hb

theorem grushinRectCutoff_coefficients (a : Space (Fin 3)) {c C1 C2 ry rt g S : ℝ}
    (hc : 0 ≤ c) (hy : 0 ≤ ry) (ht : 0 ≤ rt) (hg : 0 < g)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    (hS : ‖a.1‖+2*(ry+g) ≤ S) :
    (∀ p, cutoffGradientWeight c (grushinRectCutoff a ry rt g) p ≤
      (4+3*c*S^2)*(2*C1/g)^2) ∧
    (∀ p, |combinedCutoffScalar c (grushinRectCutoff a ry rt g) p| ≤
      (4+3*c*S^2)*(2*(C2+C1^2)/g^2)) := by
  have hY : ∀ p ∈ tsupport (grushinRectCutoff a ry rt g), ‖p.1‖ ≤ S := by
    intro p hp
    exact (rectangularClosedBox_y_radius a (by linarith : 0 ≤ ry+g)
      (grushinRectCutoff_tsupport a ry rt hg hp)).trans hS
  have hC20 : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0)
  constructor
  · intro p
    have hb := cutoffGradientWeight_coordinate_bound hc (2*C1/g) S
      (grushinRectCutoff a ry rt g)
      (fun p i => grushinRectCutoff_first_bound a ry rt hC1 hg (.inl i) p)
      (fun p j => grushinRectCutoff_first_bound a ry rt hC1 hg (.inr j) p) hY p
    simpa only [Fintype.card_fin,Nat.cast_ofNat,mul_comm,mul_left_comm,mul_assoc] using hb
  · intro p
    have hb := combinedCutoffScalar_coordinate_bound hc (2*(C2+C1^2)/g^2) S
      (by positivity) (grushinRectCutoff a ry rt g)
      (fun p i => grushinRectCutoff_second_bound a ry rt hC1 hC2 hg (.inl i) p)
      (fun p j => grushinRectCutoff_second_bound a ry rt hC1 hC2 hg (.inr j) p) hY p
    simpa only [Fintype.card_fin,Nat.cast_ofNat,mul_comm,mul_left_comm,mul_assoc] using hb

end TheoremT.Continuum.WeakGrushin
