import FiniteCoordinateProductDerivatives_v1

/-! Seven-coordinate boxes in the actual Euclidean four-by-three product.
They are not identified with maximum-norm balls; the explicit factor two
below comes from the four Y coordinates and three spectator coordinates. -/
noncomputable section
open scoped Topology BigOperators
namespace TheoremT.Continuum.WeakGrushin

def boxCoordinate : Fin 4 ⊕ Fin 3 → Space (Fin 3) →L[ℝ] ℝ
  | .inl i => (EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
  | .inr j => (EuclideanSpace.proj j).comp (ContinuousLinearMap.snd ℝ _ _)

def boxDirection : Fin 4 ⊕ Fin 3 → Space (Fin 3)
  | .inl i => yDir i
  | .inr j => tDir j

theorem boxCoordinate_direction (i j : Fin 4 ⊕ Fin 3) :
    boxCoordinate i (boxDirection j) = if i = j then 1 else 0 := by
  cases i <;> cases j <;>
    simp [boxCoordinate,boxDirection,yDir,tDir,oscillatorBasis]

def coordinateClosedBox (a : Space (Fin 3)) (R : ℝ) : Set (Space (Fin 3)) :=
  {p | ∀ i, |boxCoordinate i (p-a)| ≤ R}

theorem coordinateClosedBox_isClosed (a : Space (Fin 3)) (R : ℝ) :
    IsClosed (coordinateClosedBox a R) := by
  have he : coordinateClosedBox a R = ⋂ i, {p | |boxCoordinate i (p-a)| ≤ R} := by
    ext p
    simp [coordinateClosedBox]
  rw [he]
  apply isClosed_iInter
  intro i
  exact isClosed_le (((boxCoordinate i).continuous.comp (continuous_id.sub continuous_const)).abs)
    continuous_const

theorem coordinateClosedBox_y_norm (a : Space (Fin 3)) {R : ℝ} (hR : 0 ≤ R)
    {p : Space (Fin 3)} (hp : p ∈ coordinateClosedBox a R) :
    ‖p.1-a.1‖ ≤ 2*R := by
  have hsq : ‖p.1-a.1‖^2 ≤ 4*R^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin 4, R^2 := Finset.sum_le_sum (fun i _ => by
        have hi : |p.1 i-a.1 i| ≤ R := hp (.inl i)
        simpa only [sq_abs, PiLp.sub_apply] using pow_le_pow_left₀ (abs_nonneg _) hi 2)
      _ = _ := by simp
  nlinarith [norm_nonneg (p.1-a.1)]

theorem coordinateClosedBox_t_norm (a : Space (Fin 3)) {R : ℝ} (hR : 0 ≤ R)
    {p : Space (Fin 3)} (hp : p ∈ coordinateClosedBox a R) :
    ‖p.2-a.2‖ ≤ 2*R := by
  have hsq : ‖p.2-a.2‖^2 ≤ 3*R^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin 3, R^2 := Finset.sum_le_sum (fun i _ => by
        have hi : |p.2 i-a.2 i| ≤ R := hp (.inr i)
        simpa only [sq_abs, PiLp.sub_apply] using pow_le_pow_left₀ (abs_nonneg _) hi 2)
      _ = _ := by simp
  nlinarith [norm_nonneg (p.2-a.2),sq_nonneg R]

theorem coordinateClosedBox_subset_closedBall (a : Space (Fin 3)) {R : ℝ} (hR : 0 ≤ R) :
    coordinateClosedBox a R ⊆ Metric.closedBall a (2*R) := by
  intro p hp
  rw [Metric.mem_closedBall,dist_eq_norm]
  exact max_le (coordinateClosedBox_y_norm a hR hp) (coordinateClosedBox_t_norm a hR hp)

theorem coordinateClosedBox_isCompact (a : Space (Fin 3)) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (coordinateClosedBox a R) :=
  (isCompact_closedBall a (2*R)).of_isClosed_subset
    (coordinateClosedBox_isClosed a R) (coordinateClosedBox_subset_closedBall a hR)

theorem coordinateClosedBox_y_radius (a : Space (Fin 3)) {R : ℝ} (hR : 0 ≤ R)
    {p : Space (Fin 3)} (hp : p ∈ coordinateClosedBox a R) :
    ‖p.1‖ ≤ ‖a.1‖+2*R := by
  calc
    ‖p.1‖ = ‖(p.1-a.1)+a.1‖ := by rw [sub_add_cancel]
    _ ≤ ‖p.1-a.1‖+‖a.1‖ := norm_add_le _ _
    _ ≤ 2*R+‖a.1‖ := add_le_add (coordinateClosedBox_y_norm a hR hp) (le_refl _)
    _ = _ := by ring

end TheoremT.Continuum.WeakGrushin
