import GrushinFiniteStepGeometry_v1
import GrushinFiniteBoxGap_v1

/-! A finite solution-independent cutoff schedule between arbitrary positive
nested rectangular widths. The terminal open box contains the requested closed
inner box, with one unused two-gap collar. This licenses any finite number of
geometric stages without assuming a PDE estimate or high regularity. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem finite_grushin_nested_geometry (a : Space (Fin 3)) (n : ℕ)
    {aY aT bY bT C1 C2 : ℝ}
    (hby : 0 < bY) (hbt : 0 < bT) (hy : bY < aY) (ht : bT < aT)
    (c : ℕ → ℝ) (hc : ∀ k, k < n → 0 ≤ c k)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) :
    let δ := finiteGrushinGap aY aT bY bT n
    ∀ k, k < n → SpectatorStepGeometry (c k)
      (finiteGrushinRegion a aY aT δ k) (finiteGrushinRegion a aY aT δ (k+1))
      (finiteGrushinMiddle a aY aT δ k)
      (finiteGrushinInnerCutoff a aY aT δ k) (finiteGrushinEnergyCutoff a aY aT δ k)
      1 (h12CutoffScalarBound (c k) (‖a.1‖+2*aY) C1 C2 δ)
      (h12CutoffWeightBound (c k) (‖a.1‖+2*aY) C1 δ)
      1 (h12CutoffWeightBound (c k) (‖a.1‖+2*aY) C1 δ) := by
  exact finite_grushin_step_geometry a n (finiteGrushinGap_pos n hy ht)
    (finiteGrushinGap_y_consumed_le n hby hy ht)
    (finiteGrushinGap_t_consumed_le n hbt hy ht) c hc hC1 hC2

theorem finite_grushin_nested_final_contains (a : Space (Fin 3)) (n : ℕ)
    {aY aT bY bT : ℝ} (hy : bY < aY) (ht : bT < aT) :
    rectangularClosedBox a bY bT ⊆
      finiteGrushinRegion a aY aT (finiteGrushinGap aY aT bY bT n) n :=
  finiteGrushinRegion_contains_closed a n
    (finiteGrushinGap_y_strict n hy ht) (finiteGrushinGap_t_strict n hy ht)

theorem finite_grushin_nested_domains (a : Space (Fin 3)) (n : ℕ)
    {aY aT bY bT : ℝ} (hy : bY < aY) (ht : bT < aT) :
    let δ := finiteGrushinGap aY aT bY bT n
    (∀ k, IsOpen (finiteGrushinRegion a aY aT δ k) ∧
      MeasurableSet (finiteGrushinRegion a aY aT δ k)) ∧
    Antitone (finiteGrushinRegion a aY aT δ) ∧
    (∀ k, finiteGrushinRegion a aY aT δ k ⊆ rectangularOpenBox a aY aT) ∧
    rectangularClosedBox a bY bT ⊆ finiteGrushinRegion a aY aT δ n := by
  dsimp only
  exact ⟨fun k => ⟨finiteGrushinRegion_isOpen a _ _ _ k,
    finiteGrushinRegion_measurableSet a _ _ _ k⟩,
    finiteGrushinRegion_antitone a _ _ (finiteGrushinGap_pos n hy ht).le,
    finiteGrushinRegion_subset_initial a _ _ (finiteGrushinGap_pos n hy ht).le,
    finite_grushin_nested_final_contains a n hy ht⟩

#print axioms finite_grushin_nested_geometry
#print axioms finite_grushin_nested_domains
end TheoremT.Continuum.WeakGrushin
