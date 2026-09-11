import HalfLineDomain_v1

/-! Cutting an actual smooth function to the positive half-line is smooth when
its closed support avoids zero. The resulting compact function is an actual
HalfLine.Test; its derivative on the positive ray is unchanged. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.OneDimensional

def positiveRestriction (k : ℝ → ℂ) (r : ℝ) : ℂ := if 0 < r then k r else 0

theorem positiveRestriction_eq_of_pos (k : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    positiveRestriction k r = k r := by simp [positiveRestriction, hr]

theorem positiveRestriction_eq_zero_of_nonpos (k : ℝ → ℂ) {r : ℝ} (hr : r ≤ 0) :
    positiveRestriction k r = 0 := by simp [positiveRestriction, not_lt.mpr hr]

theorem positiveRestriction_eventuallyEq_of_pos (k : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    positiveRestriction k =ᶠ[𝓝 r] k := by
  filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
  exact positiveRestriction_eq_of_pos k hs

theorem positiveRestriction_contDiff {k : ℝ → ℂ} (hk : ContDiff ℝ ∞ k)
    (hk0 : (0 : ℝ) ∉ tsupport k) : ContDiff ℝ ∞ (positiveRestriction k) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : 0 < r
  · exact hk.contDiffAt.congr_of_eventuallyEq (positiveRestriction_eventuallyEq_of_pos k hr)
  · by_cases hneg : r < 0
    · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) r).congr_of_eventuallyEq
      filter_upwards [isOpen_Iio.mem_nhds hneg] with s hs
      exact positiveRestriction_eq_zero_of_nonpos k hs.le
    · have heq : r = 0 := le_antisymm (not_lt.mp hr) (not_lt.mp hneg)
      subst r
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) 0).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport k).isOpen_compl.mem_nhds hk0] with s hs
      simp [positiveRestriction, image_eq_zero_of_notMem_tsupport hs]

theorem positiveRestriction_tsupport_subset (k : ℝ → ℂ) :
    tsupport (positiveRestriction k) ⊆ tsupport k := by
  apply closure_mono
  intro r hr
  by_contra hk
  have hk' : k r = 0 := not_not.mp hk
  exact hr (by simp [positiveRestriction, hk'])

theorem positiveRestriction_compact {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    HasCompactSupport (positiveRestriction k) :=
  hk.of_isClosed_subset (isClosed_tsupport _) (positiveRestriction_tsupport_subset k)

theorem positiveRestriction_tsupport_pos {k : ℝ → ℂ}
    (hk0 : (0 : ℝ) ∉ tsupport k) : tsupport (positiveRestriction k) ⊆ Ioi 0 := by
  have hnn : tsupport (positiveRestriction k) ⊆ Ici (0 : ℝ) := by
    apply closure_minimal _ isClosed_Ici
    intro r hr
    change 0 ≤ r
    by_contra hn
    exact hr (positiveRestriction_eq_zero_of_nonpos k (not_le.mp hn).le)
  intro r hr
  have hne : r ≠ 0 := by
    intro heq
    subst r
    exact hk0 (positiveRestriction_tsupport_subset k hr)
  exact lt_of_le_of_ne (hnn hr) hne.symm

theorem positiveRestriction_deriv_of_pos (k : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    deriv (positiveRestriction k) r = deriv k r :=
  (positiveRestriction_eventuallyEq_of_pos k hr).deriv_eq

def positiveRestrictionTest (k : ℝ → ℂ) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (hk0 : (0 : ℝ) ∉ tsupport k) : TheoremT.HalfLine.Test :=
  ⟨positiveRestriction k, positiveRestriction_contDiff hk hk0,
    positiveRestriction_compact hkc, positiveRestriction_tsupport_pos hk0⟩

theorem positiveRestrictionTest_value_of_pos (k : ℝ → ℂ) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (hk0 : (0 : ℝ) ∉ tsupport k)
    {r : ℝ} (hr : 0 < r) :
    (positiveRestrictionTest k hk hkc hk0 : ℝ → ℂ) r = k r :=
  positiveRestriction_eq_of_pos k hr

theorem positiveRestrictionTest_deriv_of_pos (k : ℝ → ℂ) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (hk0 : (0 : ℝ) ∉ tsupport k)
    {r : ℝ} (hr : 0 < r) :
    deriv (positiveRestrictionTest k hk hkc hk0 : ℝ → ℂ) r = deriv k r :=
  positiveRestriction_deriv_of_pos k hr

#print axioms positiveRestriction_contDiff
#print axioms positiveRestriction_tsupport_pos
#print axioms positiveRestrictionTest
#print axioms positiveRestrictionTest_deriv_of_pos
end TheoremT.OneDimensional
