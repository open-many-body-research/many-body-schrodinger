import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-! Finite genuine coordinate jet families give finite classical regularity.
The derivative is a real continuous linear map on the ordinary finite Pi
space, assembled by the exact inverse of `ContinuousLinearEquiv.piRing`.
The reserve is explicit and no all-order regularity is asserted. -/
noncomputable section
open Set
open scoped ContDiff
namespace TheoremT.Continuum

theorem finite_coordinate_jet_contDiffOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) {m : ℕ}
    (G : List ι → (ι → ℝ) → ℂ)
    (hG : ∀ w, w.length ≤ m → ContinuousOn (G w) U)
    (hdG : ∀ w, w.length < m → ∀ x ∈ U,
      HasFDerivAt (G w)
        ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℂ) ι).symm
          (fun i => G (i :: w) x)) x)
    (k : ℕ) (w : List ι) (hw : w.length + k ≤ m) :
    ContDiffOn ℝ k (G w) U := by
  induction k generalizing w with
  | zero =>
      simpa only [Nat.cast_zero] using contDiffOn_zero.mpr (hG w (by omega))
  | succ k ih =>
      have hd : w.length < m := by omega
      have hpi : ContDiffOn ℝ k (fun x i => G (i :: w) x) U := by
        apply contDiffOn_pi.mpr
        intro i
        exact ih (i :: w) (by simp only [List.length_cons]; omega)
      have hder : ContDiffOn ℝ k
          (fun x => (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℂ) ι).symm
            (fun i => G (i :: w) x)) U :=
        (ContinuousLinearEquiv.comp_contDiffOn_iff
          (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℂ) ι).symm).mpr hpi
      rw [Nat.cast_succ]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
      refine ⟨?_, _, hder, ?_⟩
      · simp
      · intro x hx
        exact (hdG w hd x hx).hasFDerivWithinAt

theorem finite_coordinate_jet_base_contDiffOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) (m : ℕ)
    (G : List ι → (ι → ℝ) → ℂ)
    (hG : ∀ w, w.length ≤ m → ContinuousOn (G w) U)
    (hdG : ∀ w, w.length < m → ∀ x ∈ U,
      HasFDerivAt (G w)
        ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℂ) ι).symm
          (fun i => G (i :: w) x)) x) :
    ContDiffOn ℝ m (G []) U :=
  finite_coordinate_jet_contDiffOn hU G hG hdG m [] (by simp)

end TheoremT.Continuum
