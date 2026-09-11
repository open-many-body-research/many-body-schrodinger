import LaplacianSobolevBridge_v1
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
Global elliptic gain on an arbitrary finite-dimensional Euclidean space.
The conclusion is expressed by actual L2 witnesses and all real compact smooth
integration-by-parts tests, for every ordered list of directions. No weak
regularity conclusion, basis restriction, or derivative existence is assumed.
This module does not identify a product endowed with its maximum norm with a
Euclidean space; transporting such a model requires a separate coordinate map.
-/

noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff

namespace TheoremT.Continuum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Genuine directional weak derivative, tested against every real smooth
compactly supported function and using the actual Lebesgue measure. -/
def WeakL2Directional (f g : Lp ℂ 2 (volume : Measure E)) (v : E) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, φ x • g x) = -(∫ x, fderiv ℝ φ x v • f x)

/-- Finite-order weak regularity in all ordered directions, with actual L2
witnesses. Order two includes all mixed second weak derivatives. -/
def HasWeakL2Order (f : Lp ℂ 2 (volume : Measure E)) : ℕ → Prop
  | 0 => True
  | n + 1 => ∃ d : E → Lp ℂ 2 (volume : Measure E),
      (∀ v, WeakL2Directional f (d v) v) ∧ ∀ v, HasWeakL2Order (d v) n

theorem weakL2Directional_of_distribution
    {f g : Lp ℂ 2 (volume : Measure E)} {v : E}
    (h : ∂_{v} (f : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ))) :
    WeakL2Directional f g v := by
  intro φ hφ hcφ
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hcφ.comp_left rfl
  have hd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  let φS : 𝓢(E, ℂ) := hc.toSchwartzMap hd
  have hderiv (x : E) :
      (∂_{v} φS) x = (fderiv ℝ φ x v : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change fderiv ℝ (Complex.ofRealCLM ∘ φ) x v = _
    rw [fderiv_comp x Complex.ofRealCLM.differentiableAt
      (hφ.differentiable (by norm_num) x)]
    simp
  calc
    (∫ x, φ x • g x) = (g : 𝓢'(E, ℂ)) φS := by
      simp [φS, Lp.toTemperedDistribution_apply]
    _ = (∂_{v} (f : 𝓢'(E, ℂ))) φS := by rw [h]
    _ = -(∫ x, fderiv ℝ φ x v • f x) := by
      simp [TemperedDistribution.lineDerivOp_apply_apply,
        Lp.toTemperedDistribution_apply, hderiv, integral_neg]

theorem hasWeakL2Order_of_memSobolev_nat
    {n : ℕ} (f : Lp ℂ 2 (volume : Measure E))
    (hf : MemSobolev (n : ℝ) 2 (f : 𝓢'(E, ℂ))) :
    HasWeakL2Order f n := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    have hfirst (v : E) : ∃ g : Lp ℂ 2 (volume : Measure E),
        ∂_{v} (f : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ)) := by
      apply memSobolev_zero_iff.mp
      apply MemSobolev.mono (show (0 : ℝ) ≤ (n + 1 : ℕ) - 1 by simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]; positivity)
      exact hf.lineDerivOp (m := v)
    choose d hd using hfirst
    refine ⟨d, fun v => weakL2Directional_of_distribution (hd v), fun v => ?_⟩
    apply ih
    have hh := hf.lineDerivOp (m := v)
    rw [hd v] at hh
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hh

theorem hasWeakL2Order_two_of_distribution_laplacian
    (f w : Lp ℂ 2 (volume : Measure E))
    (hw : Δ (f : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    HasWeakL2Order f 2 := by
  apply hasWeakL2Order_of_memSobolev_nat
  exact memSobolev_two_of_laplacian_l2 f w hw

theorem exists_weakL2_first_and_second_jets_of_distribution_laplacian
    (f w : Lp ℂ 2 (volume : Measure E))
    (hw : Δ (f : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    ∃ d : E → Lp ℂ 2 (volume : Measure E),
      (∀ v, WeakL2Directional f (d v) v) ∧
      ∀ v q : E, ∃ e : Lp ℂ 2 (volume : Measure E),
        WeakL2Directional (d v) e q := by
  obtain ⟨d, hd, hdd⟩ := hasWeakL2Order_two_of_distribution_laplacian f w hw
  refine ⟨d, hd, fun v q => ?_⟩
  obtain ⟨e, he, _⟩ := hdd v
  exact ⟨e q, he q⟩

#print axioms weakL2Directional_of_distribution
#print axioms hasWeakL2Order_of_memSobolev_nat
#print axioms hasWeakL2Order_two_of_distribution_laplacian
#print axioms exists_weakL2_first_and_second_jets_of_distribution_laplacian

end TheoremT.Continuum
