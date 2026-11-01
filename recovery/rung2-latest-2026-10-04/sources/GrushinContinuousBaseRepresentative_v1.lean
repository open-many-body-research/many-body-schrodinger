import GrushinActualProfileSmoothRepresentative_v1
import Mathlib.MeasureTheory.Measure.OpenPos

/-! When the original base field is already continuous, the constructed smooth
representative agrees with it at every interior point. Hence regularity and
quantitative word estimates hold for that actual base, not a new AE version. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem complex_word_congr_on_open
    {κ : Type} [Fintype κ] [DecidableEq κ] {ι : Type}
    (dirs : ι → Space κ) {U : Set (Space κ)} (hU : IsOpen U)
    {f g : Space κ → ℂ} (hfg : EqOn f g U) (w : List ι) :
    EqOn (complexDirectionalWordDeriv dirs f w) (complexDirectionalWordDeriv dirs g w) U := by
  induction w with
  | nil => exact hfg
  | cons i w ih =>
    intro p hp
    have he : complexDirectionalWordDeriv dirs f w =ᶠ[𝓝 p] complexDirectionalWordDeriv dirs g w :=
      Filter.mem_of_superset (hU.mem_nhds hp) (fun q hq => ih hq)
    change fderiv ℝ (complexDirectionalWordDeriv dirs f w) p (dirs i) =
      fderiv ℝ (complexDirectionalWordDeriv dirs g w) p (dirs i)
    rw [he.fderiv_eq]

theorem grushin_actual_profile_continuous_base
    {Ω O ΩN : Set (Space (Fin 3))} (hΩ : IsOpen Ω) (hO : IsOpen O)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω)
    (hpχ : ∀ p ∈ O, χ p = 1)
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (hKO : MapsTo sevenToProduct (tensorClosedBox7 a b) O)
    (hKN : MapsTo sevenToProduct (tensorClosedBox7 a b) ΩN)
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U) (hUK : U ⊆ tensorClosedBox7 a b)
    (F : FactorialRawJetFamily)
    (hL2 : ∀ α β, ProductLocallyL2On (F α β) Ω)
    (hY : ∀ α β i, ProductLocalWeakDirectional Ω (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hT : ∀ α β j, ProductLocalWeakDirectional Ω (F α β) (F α (β+Pi.single j 1)) (tDir j))
    (hN : ∀ r, FactorialLocalMemLp F ΩN r)
    (hbase : ContinuousOn (F 0 0) (Set.image sevenToProduct U)) :
    ContDiffOn ℝ ∞ (F 0 0) (Set.image sevenToProduct U) ∧
      (∀ w, mixedMultiIndexWordFamily F w =ᵐ[volume.restrict (Set.image sevenToProduct U)]
        complexDirectionalWordDeriv productCoordinateDirection (F 0 0) w) ∧
      (∀ w p, p ∈ Set.image sevenToProduct U →
        ‖complexDirectionalWordDeriv productCoordinateDirection (F 0 0) w p‖ ≤
          boxEvaluationConstant a b * factorialLocalProfile F ΩN (w.length+11)) := by
  obtain ⟨f,hfs,hf0,hfw,hfb⟩ := grushin_actual_profile_smooth_representative
    hΩ hO hχ hcχ hsχ hpχ hab hKO hKN hU hUK F hL2 hY hT hN
  have hopen : IsOpen (Set.image sevenToProduct U) := sevenToProduct.toHomeomorph.isOpenMap U hU
  have he : EqOn (F 0 0) f (Set.image sevenToProduct U) :=
    volume.eqOn_open_of_ae_eq hf0 hopen hbase hfs.continuousOn
  have hwEq (w : List (Fin 4 ⊕ Fin 3)) := complex_word_congr_on_open productCoordinateDirection hopen he w
  refine ⟨hfs.congr he,?_,?_⟩
  · intro w
    filter_upwards [hfw w,ae_restrict_mem hopen.measurableSet] with p hp hpU
    exact hp.trans (hwEq w hpU).symm
  · intro w p hp
    rw [hwEq w hp]
    exact hfb w p hp

end TheoremT.Continuum.WeakGrushin
