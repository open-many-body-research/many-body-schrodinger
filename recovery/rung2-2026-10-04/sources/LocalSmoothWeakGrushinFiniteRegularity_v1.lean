import FiniteWeakGrushinCoordinateRegularity_v1
import GrushinFiniteNestedGeometry_v1
import SmoothComplexMixedSourceBounds_v1
import GrushinQuadraticYWordBound_v1

/-! Arbitrary finite local coordinate weak regularity for the actual
seven-coordinate Grushin potential equation, from a raw locally L2 solution
and locally smooth coefficient/source. All finite derivative data, constants,
and actual cutoff stages are constructed in the proof. No solution derivative
is assumed; this theorem does not estimate growth in the requested order.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin

set_option maxHeartbeats 1600000 in
theorem local_smooth_weak_grushin_finite_regularity
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    (a : Space (Fin 3)) {aY aT bY bT c : ℝ}
    (hby : 0 < bY) (hbt : 0 < bT) (hy : bY < aY) (ht : bT < aT)
    (hKΩ : rectangularClosedBox a aY aT ⊆ Ω) (hc : 0 < c)
    {B : Space (Fin 3) → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {s : Space (Fin 3) → ℂ} (hs : ContDiffOn ℝ ∞ s Ω)
    {f : Space (Fin 3) → ℂ} (hf : ProductLocallyL2On f Ω)
    (hEq : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p, φ p • s p)
    (m : ℕ) : ∃ W : ℝ, 0 ≤ W ∧
      ProductCoordinateWeakHk (rectangularOpenBox a bY bT) f m W := by
  have haY : 0 ≤ aY := (hby.trans hy).le
  have haT : 0 ≤ aT := (hbt.trans ht).le
  let K := rectangularClosedBox a aY aT
  have hK : IsCompact K := rectangularClosedBox_isCompact a haY haT
  have hfK : MemLp f 2 (volume.restrict K) := hf K hK hKΩ
  let W0 : ℝ := ∫ p in K, ‖f p‖^2
  have hW0 : 0 ≤ W0 := integral_nonneg (fun p => sq_nonneg _)
  have hfBudget : RegionL2Budget f K W0 := ⟨hfK,le_rfl⟩
  obtain ⟨K0,hK0,hCoeff⟩ := mixedWordDeriv_compact_finite_bound hΩ hB hK hKΩ m
  obtain ⟨H0,hH0,hSource⟩ := complexMixedSourceWord_compact_region_budgets hΩ hs hK hKΩ m
  obtain ⟨C1,C2,hC10,hC20,hC1,hC2⟩ := smoothTransition_derivative_bounds
  let δ := finiteGrushinGap aY aT bY bT (2*m)
  let Θ := finiteGrushinRegion a aY aT δ
  let V := finiteGrushinMiddle a aY aT δ
  let χ := finiteGrushinInnerCutoff a aY aT δ
  let η := finiteGrushinEnergyCutoff a aY aT δ
  let R : ℝ := ‖a.1‖+2*aY
  let AT := h12CutoffScalarBound c R C1 C2 δ
  let LT := h12CutoffWeightBound c R C1 δ
  let AY := h12CutoffScalarBound 0 R C1 C2 δ
  let LY := h12CutoffWeightBound 0 R C1 δ
  have hR : 0 ≤ R := add_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) haY)
  have hStage := finite_grushin_nested_geometry a (2*m) hby hbt hy ht
    (fun k => if k < m then c else 0)
    (fun k hk => by split_ifs <;> positivity) hC1 hC2
  have hTGeom : ∀ k, k < m → SpectatorStepGeometry c (Θ k) (Θ (k+1)) (V k)
      (χ k) (η k) 1 AT LT 1 LT := by
    intro k hk
    simpa only [if_pos hk] using hStage k (by omega)
  have hYGeom : ∀ k, k < m → SpectatorStepGeometry 0 (Θ (m+k)) (Θ (m+(k+1))) (V (m+k))
      (χ (m+k)) (η (m+k)) 1 AY LY 1 LY := by
    intro k hk
    have hmk : ¬m+k < m := by omega
    simpa only [if_neg hmk,Nat.add_assoc] using hStage (m+k) (by omega)
  have hOpen : ∀ k, IsOpen (Θ k) := fun k => finiteGrushinRegion_isOpen a _ _ _ k
  have hInitial : Θ 0 ⊆ K := by
    simpa only [Θ,finiteGrushinRegion_zero] using rectangularOpenBox_subset_closedBox a aY aT
  have hInitialΩ := hInitial.trans hKΩ
  have hQuad : ∀ ya : List (Fin 4), ∀ p ∈ Θ 0,
      |directionalWordDeriv yDir (fun q : Space (Fin 3) => ‖q.1‖^2) ya p| ≤
        grushinQuadraticYWordBound R := by
    have hh := grushin_quadratic_y_word_bound_on hR
      (fun p hp => rectangularClosedBox_y_radius a haY (hInitial hp))
    simpa only [Real.norm_eq_abs] using hh
  obtain ⟨W,hW,hResult⟩ := finite_weak_grushin_coordinate_regularity hc m
    Θ V (fun k => Θ (m+k)) (fun k => V (m+k)) χ η
    (fun k => χ (m+k)) (fun k => η (m+k))
    (fun _ => 1) (fun _ => AT) (fun _ => LT) (fun _ => 1) (fun _ => LT)
    (fun _ => 1) (fun _ => AY) (fun _ => LY) (fun _ => 1) (fun _ => LY)
    hTGeom hYGeom (fun k hk => hOpen _) (by simp)
    (hB.mono hInitialΩ) f (complexMixedSourceWord s)
    K0 (grushinQuadraticYWordBound R) H0 W0 hK0 hH0 hW0
    (hfBudget.restrict hInitial le_rfl)
    (fun ya tb hn => (hSource ya tb hn).restrict hInitial le_rfl)
    (fun ya tb i hn => (complexMixedSourceWord_localY hΩ hs ya tb i).mono hInitialΩ)
    (fun tb j hn => (complexMixedSourceWord_localT_zero hΩ hs tb j).mono hInitialΩ)
    (fun ya tb hn p hp => hCoeff ya tb hn p (hInitial hp))
    (fun ya hn => hQuad ya)
    (fun φ hφ hcφ hφΘ => hEq φ hφ hcφ (hφΘ.trans hInitialΩ))
  have hFinal : rectangularOpenBox a bY bT ⊆ Θ (m+m) := by
    have hh := (rectangularOpenBox_subset_closedBox a bY bT).trans
      (finite_grushin_nested_final_contains a (2*m) hy ht)
    simpa only [Θ,δ,two_mul] using hh
  exact ⟨W,hW,hResult.restrict hFinal le_rfl⟩

#print axioms local_smooth_weak_grushin_finite_regularity
end TheoremT.Continuum.WeakGrushin
