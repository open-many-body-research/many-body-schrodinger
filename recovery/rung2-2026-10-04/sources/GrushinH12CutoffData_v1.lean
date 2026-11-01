import GrushinRectangularCutoff_v1

/-! Exact half-gap cutoffs for one outer-to-inner two-gap gain in the
34-gap initialization. The spatial and spectator widths are independent.
The finite constants belong to the actual smooth transition, not a quintic. -/
noncomputable section
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum.WeakGrushin

def h12InnerCutoff (a : Space (Fin 3)) (ry rt δ : ℝ) : Space (Fin 3) → ℝ :=
  grushinRectCutoff a (ry-2*δ) (rt-2*δ) (δ/2)

def h12EnergyCutoff (a : Space (Fin 3)) (ry rt δ : ℝ) : Space (Fin 3) → ℝ :=
  grushinRectCutoff a (ry-δ) (rt-δ) (δ/2)

def h12CutoffWeightBound (c S C1 δ : ℝ) : ℝ :=
  (4+3*c*S^2)*(4*C1/δ)^2

def h12CutoffScalarBound (c S C1 C2 δ : ℝ) : ℝ :=
  (4+3*c*S^2)*(8*(C2+C1^2)/δ^2)

theorem h12CutoffWeightBound_nonneg {c : ℝ} (hc : 0 ≤ c) (S C1 δ : ℝ) :
    0 ≤ h12CutoffWeightBound c S C1 δ := by
  unfold h12CutoffWeightBound
  positivity

theorem h12_cutoff_geometry (a : Space (Fin 3)) {ry rt δ : ℝ}
    (hδ : 0 < δ) (hy : 2*δ ≤ ry) (ht : 2*δ ≤ rt) :
    ContDiff ℝ ∞ (h12InnerCutoff a ry rt δ) ∧
    HasCompactSupport (h12InnerCutoff a ry rt δ) ∧
    ContDiff ℝ ∞ (h12EnergyCutoff a ry rt δ) ∧
    HasCompactSupport (h12EnergyCutoff a ry rt δ) ∧
    tsupport (h12EnergyCutoff a ry rt δ) ⊆ rectangularOpenBox a ry rt ∧
    tsupport (h12InnerCutoff a ry rt δ) ⊆ rectangularOpenBox a (ry-δ) (rt-δ) ∧
    (∀ p ∈ rectangularOpenBox a (ry-δ) (rt-δ), h12EnergyCutoff a ry rt δ p = 1) ∧
    (∀ p ∈ rectangularClosedBox a (ry-2*δ) (rt-2*δ), h12InnerCutoff a ry rt δ p = 1) := by
  have hg : 0 < δ/2 := by positivity
  refine ⟨grushinRectCutoff_contDiff a _ _ _,
    grushinRectCutoff_compact a (by linarith) (by linarith) hg,
    grushinRectCutoff_contDiff a _ _ _,
    grushinRectCutoff_compact a (by linarith) (by linarith) hg,?_,?_,?_,?_⟩
  · exact (grushinRectCutoff_tsupport a (ry-δ) (rt-δ) hg).trans
      (rectangularClosedBox_subset_openBox a (by linarith) (by linarith))
  · exact (grushinRectCutoff_tsupport a (ry-2*δ) (rt-2*δ) hg).trans
      (rectangularClosedBox_subset_openBox a (by linarith) (by linarith))
  · intro p hp
    exact grushinRectCutoff_plateau a _ _ hg
      (rectangularOpenBox_subset_closedBox a _ _ hp)
  · intro p hp
    exact grushinRectCutoff_plateau a _ _ hg hp

theorem h12_cutoff_value_bounds (a : Space (Fin 3)) (ry rt δ : ℝ) :
    (∀ p, |h12InnerCutoff a ry rt δ p| ≤ 1) ∧
    (∀ p, (h12EnergyCutoff a ry rt δ p)^2 ≤ 1) := by
  constructor
  · intro p
    unfold h12InnerCutoff
    rw [abs_of_nonneg (grushinRectCutoff_nonneg a _ _ _ p)]
    exact grushinRectCutoff_le_one a _ _ _ p
  · intro p
    have hl := grushinRectCutoff_nonneg a (ry-δ) (rt-δ) (δ/2) p
    have hu := grushinRectCutoff_le_one a (ry-δ) (rt-δ) (δ/2) p
    change (grushinRectCutoff a (ry-δ) (rt-δ) (δ/2) p)^2 ≤ 1
    nlinarith

theorem h12_cutoff_coefficient_bounds (a : Space (Fin 3)) {c C1 C2 ry rt δ S : ℝ}
    (hc : 0 ≤ c) (hδ : 0 < δ) (hy : 2*δ ≤ ry) (ht : 2*δ ≤ rt)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    (hS : ‖a.1‖+2*ry ≤ S) :
    (∀ p, |combinedCutoffScalar c (h12InnerCutoff a ry rt δ) p| ≤
      h12CutoffScalarBound c S C1 C2 δ) ∧
    (∀ p, cutoffGradientWeight c (h12InnerCutoff a ry rt δ) p ≤
      h12CutoffWeightBound c S C1 δ) ∧
    (∀ p, grushinCutoffWeight c (h12EnergyCutoff a ry rt δ) p ≤
      h12CutoffWeightBound c S C1 δ) := by
  have hg : 0 < δ/2 := by positivity
  have he1 : 2*C1/(δ/2) = 4*C1/δ := by field_simp; ring
  have he2 : 2*(C2+C1^2)/(δ/2)^2 = 8*(C2+C1^2)/δ^2 := by field_simp; ring
  obtain ⟨hbχ,haχ⟩ := grushinRectCutoff_coefficients a hc
    (by linarith : 0 ≤ ry-2*δ) (by linarith : 0 ≤ rt-2*δ) hg hC1 hC2
    (show ‖a.1‖+2*(ry-2*δ+δ/2) ≤ S by linarith)
  obtain ⟨hbη,_⟩ := grushinRectCutoff_coefficients a hc
    (by linarith : 0 ≤ ry-δ) (by linarith : 0 ≤ rt-δ) hg hC1 hC2
    (show ‖a.1‖+2*(ry-δ+δ/2) ≤ S by linarith)
  refine ⟨?_,?_,?_⟩
  · intro p
    simpa only [h12InnerCutoff,h12CutoffScalarBound,he2] using haχ p
  · intro p
    simpa only [h12InnerCutoff,h12CutoffWeightBound,he1] using hbχ p
  · intro p
    simpa only [h12EnergyCutoff,h12CutoffWeightBound,he1,
      cutoffGradientWeight_eq_grushinCutoffWeight] using hbη p

end TheoremT.Continuum.WeakGrushin
