import LocalWeakYLaplacianDifferentiate_v1

/-! Iteration of the constant-coefficient weak Y equation along a finite
ordered family. All derivative premises are actual local weak identities;
only the original zero-word PDE is assumed. No positive-order PDE is a premise.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ ι : Type} [Fintype κ] [DecidableEq κ]

theorem local_weak_y_laplacian_word_equations
    {Ω : Set (Space κ)} (dirs : ι → Space κ) (m : ℕ)
    (F H : List ι → Space κ → ℂ)
    (hF : ∀ w, w.length ≤ m → ProductLocallyL2On (F w) Ω)
    (hH : ∀ w, w.length ≤ m → ProductLocallyL2On (H w) Ω)
    (hD : ∀ w i, w.length < m →
      ProductLocalWeakDirectional Ω (F w) (F (i :: w)) (dirs i))
    (hHD : ∀ w i, w.length < m →
      ProductLocalWeakDirectional Ω (H w) (H (i :: w)) (dirs i))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • F [] p) = ∫ p, φ p • H [] p) :
    ∀ w, w.length ≤ m →
      ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        Integrable (fun p => splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • F w p) ∧
        Integrable (fun p => φ p • H w p) ∧
        (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • F w p) = ∫ p, φ p • H w p := by
  intro w
  induction w with
  | nil =>
    intro hw φ hφ hc hs
    refine ⟨?_,?_,hP φ hφ hc hs⟩
    · exact product_raw_locallyL2_compact_smul_integrable (hF [] hw)
        (splitGrushin_zero_contDiff 0 oscillatorBasis hφ).continuous
        (splitGrushin_compact 0 oscillatorBasis (fun _ => 0) hc)
        ((splitGrushin_test_tsupport_subset 0 φ).trans hs)
    · exact product_raw_locallyL2_compact_smul_integrable (hH [] hw) hφ.continuous hc hs
  | cons i w ih =>
    intro hw
    have hwm : w.length < m := by simp only [List.length_cons] at hw; omega
    exact local_weak_y_laplacian_differentiate (hD w i hwm) (hHD w i hwm)
      (fun φ hφ hc hs => (ih (by omega) φ hφ hc hs).2.2)

#print axioms local_weak_y_laplacian_word_equations
end TheoremT.Continuum.WeakGrushin
