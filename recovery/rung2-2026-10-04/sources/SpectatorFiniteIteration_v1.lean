import SpectatorIterationStep_v1
import SpectatorIterationGeometry_v1
import SpectatorIterationBudgetSequence_v1

/-! Actual finite tangential iteration from a raw L2 solution, with no input
solution derivatives. For n steps, only source/coefficient words of length
less than n are used. All earlier Y/YY witnesses survive on the final region. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 1200000 in
theorem spectatorFiniteState_iterate
    {c : ℝ} (hc : 0 < c) (n : ℕ)
    (Ω W : ℕ → Set (Space κ)) (χ η : ℕ → Space κ → ℝ)
    (M A B D Q : ℕ → ℝ)
    (hGeom : ∀ i, i < n → SpectatorStepGeometry c (Ω i) (Ω (i+1)) (W i)
      (χ i) (η i) (M i) (A i) (B i) (D i) (Q i))
    {P : Space κ → ℝ} (hP : ContDiffOn ℝ ∞ P (Ω 0))
    (f : Space κ → ℂ) (F : List κ → Space κ → ℂ) (K0 Winit H0 : ℝ)
    (hK0 : 0 ≤ K0) (hWinit : 0 ≤ Winit) (hH0 : 0 ≤ H0)
    (hf : RegionL2Budget f (Ω 0) Winit)
    (hF : ∀ w, w.length < n → RegionL2Budget (F w) (Ω 0) H0)
    (hFD : ∀ w j, w.length+1 < n → LocalSpectatorD (Ω 0) (F w) (F (j :: w)) j)
    (hCoeff : ∀ w, w.length < n → ∀ p ∈ Ω 0, |spectatorWordDeriv P w p| ≤ K0)
    (hEq : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω 0 →
      (∫ p, splitGrushin c oscillatorBasis P φ p • f p) = ∫ p, φ p • F [] p) :
    0 ≤ spectatorIterationBudgetSeq c M A B D Q K0 H0 Winit n ∧
    SpectatorFiniteState (Ω n) f n
      (spectatorIterationBudgetSeq c M A B D Q K0 H0 Winit n) := by
  let R := spectatorIterationBudgetSeq c M A B D Q K0 H0 Winit
  have hDom : ∀ i, i ≤ n → Ω i ⊆ Ω 0 := by
    intro i
    induction i with
    | zero => intro _; exact Set.Subset.rfl
    | succ i ih =>
      intro hi
      exact (hGeom i (by omega)).domain_subset.trans (ih (by omega))
  have hAll : ∀ i, i ≤ n → 0 ≤ R i ∧ SpectatorFiniteState (Ω i) f i (R i) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨hWinit,spectatorFiniteState_zero hf⟩
    | succ i ih =>
      intro hi
      have hin : i < n := by omega
      obtain ⟨hRi,hSi⟩ := ih (by omega)
      have hDi := hDom i (by omega)
      obtain ⟨hΩ,hχ,hcχ,hη,hcη,hηΩ,hW,hχW,hη1,hB0,hD0,hQ0,hM,hA,hB,hD,hQ,hχ1⟩ :=
        hGeom i hin
      have hn := spectatorFiniteState_step hc hΩ hχ hcχ hη hcη hηΩ
        hW hχW hη1 (M i) (A i) (B i) (D i) (Q i) hB0 hD0 hQ0 hM hA hB hD hQ hχ1
        (hP.mono hDi) i f F K0 (R i) H0 hK0 hRi hH0 hSi
        (fun w hw => (hF w (by omega)).restrict hDi le_rfl)
        (fun w j hw => (hFD w j (by omega)).mono hDi)
        (fun w hw p hp => hCoeff w (by omega) p (hDi hp))
        (fun φ hφ hc hs => hEq φ hφ hc (hs.trans hDi))
      have hpos := (spectatorIterationBudget_bounds c (M i) (A i) (B i) (D i) (Q i)
        K0 H0 i (R i) hc hB0 hD0 hQ0 hK0 hH0 hRi).2.1
      exact ⟨hpos,hn⟩
  exact hAll n le_rfl

#print axioms spectatorFiniteState_iterate
end TheoremT.Continuum.WeakGrushin
