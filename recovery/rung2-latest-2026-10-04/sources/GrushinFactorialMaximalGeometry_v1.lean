import GrushinFactorialCutoffData_v1

/-! Support constants for applying the compact Grushin graph estimate to
the actual factorial cutoff. The center has zero Y coordinate and the
shrink parameter is nonnegative, so both radii depend only on aY. -/
noncomputable section
open scoped Topology
namespace TheoremT.Continuum.WeakGrushin

theorem factorialRectCutoff_maximal_geometry
    (a : Space (Fin 3)) (ha : a.1 = 0) {aY aT ρ t e : ℝ}
    (ht : 0 ≤ t) (he : 0 < e) (hte : t+e ≤ ρ)
    (hρy : ρ < aY) (hρt : ρ < aT) :
    0 < aY ∧ 1 ≤ max 1 (2*aY) ∧
    IsCompact (tsupport (factorialRectCutoff a aY aT t e)) ∧
    tsupport (factorialRectCutoff a aY aT t e) ⊆
      rectangularOpenBox a (aY-t) (aT-t) ∧
    (∀ i : Fin 4, ∀ p ∈ tsupport (factorialRectCutoff a aY aT t e),
      |p.1 i| ≤ aY) ∧
    (∀ p ∈ tsupport (factorialRectCutoff a aY aT t e),
      ‖p.1‖ ≤ max 1 (2*aY)) ∧
    (∀ p ∈ rectangularOpenBox a (aY-(t+e)) (aT-(t+e)),
      factorialRectCutoff a aY aT t e p = 1) := by
  obtain ⟨_, hc, _, hplateau, hs, hso⟩ :=
    factorialRectCutoff_geometry a he hte hρy hρt
  refine ⟨by linarith, le_max_left _ _, hc.isCompact, hso, ?_, ?_, hplateau⟩
  · intro i p hp
    have hi : |p.1 i - a.1 i| ≤ aY-t-e/4 := hs hp (.inl i)
    simp only [ha, PiLp.zero_apply, sub_zero] at hi
    linarith
  · intro p hp
    have hn := rectangularClosedBox_y_norm a (by linarith : 0 ≤ aY-t-e/4) (hs hp)
    rw [ha, sub_zero] at hn
    exact hn.trans ((by linarith : 2*(aY-t-e/4) ≤ 2*aY).trans (le_max_right _ _))

end TheoremT.Continuum.WeakGrushin
