import TensorBoxContinuousRepresentative_v1
import SmoothCoordinateSubsetFields7_v1

/-! A finite reserve of seven extra coordinate derivatives gives continuous
representatives for every requested coordinate word through the target order.
All approximants are actual smooth functions and every L2 class is identified
with its actual coordinate derivative. No representative is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem smooth_word7_continuous_representative_of_L2_limits
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (u : ℕ → (Fin 7 → ℝ) → ℂ) (hu : ∀ n, ContDiff ℝ ∞ (u n)) {m : ℕ}
    (V : ℕ → List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n w, w.length ≤ m+7 →
      (V n w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] coordinateWordDeriv7 (u n) w)
    (W : List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hW : ∀ w, w.length ≤ m+7 → Tendsto (fun n => V n w) atTop (𝓝 (W w)))
    (w : List (Fin 7)) (hw : w.length ≤ m) :
    ∃ g : (Fin 7 → ℝ) → ℂ, ContinuousOn g (tensorClosedBox7 a b) ∧
      TendstoUniformlyOn (fun n => coordinateWordDeriv7 (u n) w) g atTop (tensorClosedBox7 a b) ∧
      (W w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] g := by
  have hs (s : Finset (Fin 7)) : (canonicalSubsetWord7 s ++ w).length ≤ m+7 :=
    (canonicalSubsetWord7_append_length s w).trans (Nat.add_le_add_right hw 7)
  have hsm (n : ℕ) : ContDiff ℝ ∞ (coordinateWordDeriv7 (u n) w) :=
    normedComplexDirectionalWordDeriv_contDiff _ (hu n) w
  have h := tensor_box7_continuous_representative_of_L2_limits hab
    (fun n s => smoothSubsetField7 (coordinateWordDeriv7 (u n) w) s)
    (fun n s => (smoothSubsetField7_contDiff (hsm n) s).continuous.continuousOn)
    (fun n s i hi x _ => smoothSubsetField7_coordinate_hasDerivAt (hsm n) s i hi x)
    (fun n s => V n (canonicalSubsetWord7 s ++ w))
    (fun n s => by
      rw [smoothSubsetField7_word_base]
      exact hV n _ (hs s))
    (fun s => W (canonicalSubsetWord7 s ++ w))
    (fun s => hW _ (hs s))
  simpa only [smoothSubsetField7_empty,canonicalSubsetWord7,Finset.sort_empty,List.nil_append] using h

theorem smooth_words7_continuous_representatives_of_L2_limits
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (u : ℕ → (Fin 7 → ℝ) → ℂ) (hu : ∀ n, ContDiff ℝ ∞ (u n)) {m : ℕ}
    (V : ℕ → List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n w, w.length ≤ m+7 →
      (V n w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] coordinateWordDeriv7 (u n) w)
    (W : List (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hW : ∀ w, w.length ≤ m+7 → Tendsto (fun n => V n w) atTop (𝓝 (W w))) :
    ∃ G : List (Fin 7) → (Fin 7 → ℝ) → ℂ, ∀ w, w.length ≤ m →
      ContinuousOn (G w) (tensorClosedBox7 a b) ∧
      TendstoUniformlyOn (fun n => coordinateWordDeriv7 (u n) w) (G w) atTop (tensorClosedBox7 a b) ∧
      (W w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] G w := by
  classical
  have h (w : List (Fin 7)) (hw : w.length ≤ m) :=
    smooth_word7_continuous_representative_of_L2_limits hab u hu V hV W hW w hw
  let G : List (Fin 7) → (Fin 7 → ℝ) → ℂ := fun w =>
    if hw : w.length ≤ m then Classical.choose (h w hw) else 0
  refine ⟨G,?_⟩
  intro w hw
  dsimp only [G]
  rw [dite_eq_left hw]
  exact Classical.choose_spec (h w hw)

end TheoremT.Continuum
