import GrushinRectangularCutoff_v1

/-! Spatial cutoff derivatives vanish throughout the inner spatial slab.
Their closed supports therefore stay outside the inner coordinate radius.
The physical |y| lower bound explicitly requires the Y center to be zero. -/
noncomputable section
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem transitionWindow_deriv_zero_inner {r R x : ℝ} (hgap : r < R) (hx : |x| < r) :
    deriv (transitionWindow r R) x = 0 := by
  have he : Set.EqOn (transitionWindow r R) (fun _ => (1 : ℝ)) (Set.Ioo (-r) r) := by
    intro z hz
    exact transitionWindow_plateau hgap ⟨hz.1.le,hz.2.le⟩
  simpa only [deriv_const] using he.deriv isOpen_Ioo (abs_lt.mp hx)

theorem transitionWindow_second_zero_inner {r R x : ℝ} (hgap : r < R) (hx : |x| < r) :
    deriv (deriv (transitionWindow r R)) x = 0 := by
  have he : Set.EqOn (deriv (transitionWindow r R)) (fun _ => (0 : ℝ)) (Set.Ioo (-r) r) := by
    intro z hz
    exact transitionWindow_deriv_zero_inner hgap (abs_lt.mpr hz)
  simpa only [deriv_const] using he.deriv isOpen_Ioo (abs_lt.mp hx)

theorem grushinRectCutoff_first_formula (a : Space (Fin 3)) (ry rt g : ℝ)
    (j : Fin 4 ⊕ Fin 3) (p : Space (Fin 3)) :
    fderiv ℝ (grushinRectCutoff a ry rt g) p (boxDirection j) =
      (∏ i ∈ Finset.univ.erase j, transitionWindow (boxHalfWidth ry rt i)
        (boxHalfWidth ry rt i+g) (boxCoordinate i (p-a))) *
      deriv (transitionWindow (boxHalfWidth ry rt j) (boxHalfWidth ry rt j+g))
        (boxCoordinate j (p-a)) := by
  have hφ := fun i : Fin 4 ⊕ Fin 3 =>
    transitionWindow_contDiff (boxHalfWidth ry rt i) (boxHalfWidth ry rt i+g)
  unfold grushinRectCutoff
  rw [cutoffRescale_first (coordinateProduct_contDiff boxCoordinate hφ)]
  simpa [cutoffRescaleMap] using coordinateProduct_first boxCoordinate hφ j
    (boxDirection j) (fun i => boxCoordinate_direction i j) (p-a)

theorem grushinRectCutoff_second_formula (a : Space (Fin 3)) (ry rt g : ℝ)
    (j : Fin 4 ⊕ Fin 3) (p : Space (Fin 3)) :
    fderiv ℝ (fun q => fderiv ℝ (grushinRectCutoff a ry rt g) q (boxDirection j)) p
      (boxDirection j) =
      (∏ i ∈ Finset.univ.erase j, transitionWindow (boxHalfWidth ry rt i)
        (boxHalfWidth ry rt i+g) (boxCoordinate i (p-a))) *
      deriv (deriv (transitionWindow (boxHalfWidth ry rt j) (boxHalfWidth ry rt j+g)))
        (boxCoordinate j (p-a)) := by
  have hφ := fun i : Fin 4 ⊕ Fin 3 =>
    transitionWindow_contDiff (boxHalfWidth ry rt i) (boxHalfWidth ry rt i+g)
  unfold grushinRectCutoff
  rw [cutoffRescale_second (coordinateProduct_contDiff boxCoordinate hφ)]
  simpa [cutoffRescaleMap] using coordinateProduct_second boxCoordinate hφ j
    (boxDirection j) (fun i => boxCoordinate_direction i j) (p-a)

theorem grushinRectCutoff_first_tsupport_lower (a : Space (Fin 3)) (ry rt : ℝ)
    {g : ℝ} (hg : 0 < g) (j : Fin 4 ⊕ Fin 3) :
    tsupport (fun p => fderiv ℝ (grushinRectCutoff a ry rt g) p (boxDirection j)) ⊆
      {p | boxHalfWidth ry rt j ≤ |boxCoordinate j (p-a)|} := by
  apply closure_minimal _ (isClosed_le continuous_const
    (((boxCoordinate j).continuous.comp (continuous_id.sub continuous_const)).abs))
  intro p hp
  by_contra hn
  have hz := transitionWindow_deriv_zero_inner
    (show boxHalfWidth ry rt j < boxHalfWidth ry rt j+g by linarith) (lt_of_not_ge hn)
  exact hp ((grushinRectCutoff_first_formula a ry rt g j p).trans (mul_eq_zero_of_right _ hz))

theorem grushinRectCutoff_second_tsupport_lower (a : Space (Fin 3)) (ry rt : ℝ)
    {g : ℝ} (hg : 0 < g) (j : Fin 4 ⊕ Fin 3) :
    tsupport (fun p => fderiv ℝ
      (fun q => fderiv ℝ (grushinRectCutoff a ry rt g) q (boxDirection j)) p (boxDirection j)) ⊆
      {p | boxHalfWidth ry rt j ≤ |boxCoordinate j (p-a)|} := by
  apply closure_minimal _ (isClosed_le continuous_const
    (((boxCoordinate j).continuous.comp (continuous_id.sub continuous_const)).abs))
  intro p hp
  by_contra hn
  have hz := transitionWindow_second_zero_inner
    (show boxHalfWidth ry rt j < boxHalfWidth ry rt j+g by linarith) (lt_of_not_ge hn)
  exact hp ((grushinRectCutoff_second_formula a ry rt g j p).trans (mul_eq_zero_of_right _ hz))

theorem centered_grushinRectCutoff_y_derivative_lower_radius
    (a : Space (Fin 3)) (ha : a.1 = 0) (ry rt : ℝ) {g : ℝ} (hg : 0 < g)
    (i : Fin 4) {p : Space (Fin 3)}
    (hp : p ∈ tsupport (fun q => fderiv ℝ (grushinRectCutoff a ry rt g) q (yDir i)) ∨
      p ∈ tsupport (fun q => fderiv ℝ
        (fun z => fderiv ℝ (grushinRectCutoff a ry rt g) z (yDir i)) q (yDir i))) :
    ry ≤ ‖p.1‖ := by
  have hb : ry ≤ |boxCoordinate (.inl i) (p-a)| := by
    rcases hp with hp | hp
    · exact grushinRectCutoff_first_tsupport_lower a ry rt hg (.inl i) hp
    · exact grushinRectCutoff_second_tsupport_lower a ry rt hg (.inl i) hp
  have he : boxCoordinate (.inl i) (p-a) = p.1 i := by
    simp [boxCoordinate,ha]
  rw [he] at hb
  exact hb.trans (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p.1 i)

theorem factorial_rectangular_cutoff_y_lower_radius
    (a : Space (Fin 3)) (ha : a.1 = 0) (aY aT s : ℝ) {e κ : ℝ}
    (he : 0 < e) (hκ : κ ≤ aY-s-e) (i : Fin 4) {p : Space (Fin 3)}
    (hp : p ∈ tsupport (fun q => fderiv ℝ
        (grushinRectCutoff a (aY-s-e) (aT-s-e) (3*e/4)) q (yDir i)) ∨
      p ∈ tsupport (fun q => fderiv ℝ (fun z => fderiv ℝ
        (grushinRectCutoff a (aY-s-e) (aT-s-e) (3*e/4)) z (yDir i)) q (yDir i))) :
    κ ≤ ‖p.1‖ :=
  hκ.trans (centered_grushinRectCutoff_y_derivative_lower_radius a ha _ _ (by positivity) i hp)

end TheoremT.Continuum.WeakGrushin
