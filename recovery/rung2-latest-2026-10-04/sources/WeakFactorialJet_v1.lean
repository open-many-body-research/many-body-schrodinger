import SmoothFactorialJet_v1
import ProductCompactH2Approximation_v1

/-! Actual L2 representatives indexed by the fixed coordinate word, through
order two. The total function uses its first two letters on longer words;
no higher derivative interpretation is assigned to that default branch.
Coordinate permutation identifications are proved in a separate module. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum.WeakGrushin

def weakCoordinateJet
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (e : Jet (Fin 3)) : List (Fin 4 ⊕ Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))
  | [] => f
  | [i] => d (productCoordinateDirection i)
  | i :: j :: _ => e (productCoordinateDirection j) (productCoordinateDirection i)

def weakFactorialJet
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (e : Jet (Fin 3)) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    Lp ℂ 2 (volume : Measure (Space (Fin 3))) :=
  weakCoordinateJet f d e (mixedMultiIndexWord α β)

theorem weakCoordinateJet_tendsto
    {g : ℕ → Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    {dg : ℕ → Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    {eg : ℕ → Jet (Fin 3)}
    {f : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    {d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    {e : Jet (Fin 3)}
    (hg : Tendsto g atTop (𝓝 f))
    (hd : ∀ v, Tendsto (fun n => dg n v) atTop (𝓝 (d v)))
    (he : ∀ v w, Tendsto (fun n => eg n v w) atTop (𝓝 (e v w)))
    (w : List (Fin 4 ⊕ Fin 3)) :
    Tendsto (fun n => weakCoordinateJet (g n) (dg n) (eg n) w) atTop
      (𝓝 (weakCoordinateJet f d e w)) := by
  cases w with
  | nil => exact hg
  | cons i w =>
    cases w with
    | nil => exact hd _
    | cons j w => exact he _ _

theorem weakCoordinateJet_ae_smooth
    {G : Space (Fin 3) → ℂ}
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (e : Jet (Fin 3))
    (hf : (f : Space (Fin 3) → ℂ) =ᵐ[volume] G)
    (hd : ∀ v, (d v : Space (Fin 3) → ℂ) =ᵐ[volume] (fun p => fderiv ℝ G p v))
    (he : ∀ v w, (e v w : Space (Fin 3) → ℂ) =ᵐ[volume]
      (fun p => fderiv ℝ (fun z => fderiv ℝ G z v) p w))
    (w : List (Fin 4 ⊕ Fin 3)) (hw : w.length ≤ 2) :
    (weakCoordinateJet f d e w : Space (Fin 3) → ℂ) =ᵐ[volume]
      complexDirectionalWordDeriv productCoordinateDirection G w := by
  cases w with
  | nil => exact hf
  | cons i w =>
    cases w with
    | nil => exact hd _
    | cons j w =>
      cases w with
      | nil => exact he _ _
      | cons k w => simp only [List.length_cons] at hw; omega

theorem weakFactorialJet_zero
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3)) :
    weakFactorialJet f d e 0 0 = f := by
  change weakCoordinateJet f d e (mixedMultiIndexWord (fun _ => 0) (fun _ => 0)) = f
  rw [mixedMultiIndexWord_zero]
  rfl

end TheoremT.Continuum.WeakGrushin
