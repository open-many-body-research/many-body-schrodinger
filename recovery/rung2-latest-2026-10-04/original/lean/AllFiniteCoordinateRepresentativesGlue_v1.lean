import SmoothWordBoxFiniteQuantitative_v1
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Finite local representatives of one almost-everywhere field have the
same classical values on an open set. This joins independently constructed
finite-order mollifications into one smooth quantitative representative. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem coordinate_words7_congr_on_open
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U)
    {f g : (Fin 7 → ℝ) → ℂ} (hfg : EqOn f g U)
    (w : List (Fin 7)) : EqOn (coordinateWordDeriv7 f w) (coordinateWordDeriv7 g w) U := by
  induction w with
  | nil => exact hfg
  | cons i w ih =>
    intro x hx
    have he : coordinateWordDeriv7 f w =ᶠ[𝓝 x] coordinateWordDeriv7 g w :=
      Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => ih hy)
    change fderiv ℝ (coordinateWordDeriv7 f w) x (Pi.single i 1) =
      fderiv ℝ (coordinateWordDeriv7 g w) x (Pi.single i 1)
    rw [he.fderiv_eq]

theorem all_finite_coordinate_representatives_glue
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U)
    (f : (Fin 7 → ℝ) → ℂ)
    (D : List (Fin 7) → (Fin 7 → ℝ) → ℂ) (B : List (Fin 7) → ℝ)
    (hfinite : ∀ m : ℕ, ∃ g : (Fin 7 → ℝ) → ℂ,
      ContDiffOn ℝ m g U ∧ f =ᵐ[volume.restrict U] g ∧
      (∀ w, w.length ≤ m → D w =ᵐ[volume.restrict U] coordinateWordDeriv7 g w) ∧
      (∀ w, w.length ≤ m → ∀ x ∈ U, ‖coordinateWordDeriv7 g w x‖ ≤ B w)) :
    ∃ g : (Fin 7 → ℝ) → ℂ,
      ContDiffOn ℝ ∞ g U ∧ f =ᵐ[volume.restrict U] g ∧
      (∀ w, D w =ᵐ[volume.restrict U] coordinateWordDeriv7 g w) ∧
      (∀ w x, x ∈ U → ‖coordinateWordDeriv7 g w x‖ ≤ B w) := by
  classical
  choose G hG using hfinite
  have heq (m : ℕ) : EqOn (G 0) (G m) U :=
    volume.eqOn_open_of_ae_eq ((hG 0).2.1.symm.trans (hG m).2.1) hU
      (hG 0).1.continuousOn (hG m).1.continuousOn
  have hwEq (m : ℕ) (w : List (Fin 7)) := coordinate_words7_congr_on_open hU (heq m) w
  refine ⟨G 0, ?_, (hG 0).2.1, ?_, ?_⟩
  · apply contDiffOn_infty.mpr
    intro m
    exact (hG m).1.congr (heq m)
  · intro w
    filter_upwards [(hG w.length).2.2.1 w le_rfl,ae_restrict_mem hU.measurableSet] with x hx hxU
    exact hx.trans (hwEq w.length w hxU).symm
  · intro w x hx
    rw [hwEq w.length w hx]
    exact (hG w.length).2.2.2 w le_rfl x hx

end TheoremT.Continuum
