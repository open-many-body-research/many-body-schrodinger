import GrushinContinuousBaseRepresentative_v1
import GrushinRectangularCutoff_v1

/-! Concrete nested boxes for the weak-profile embedding, with an actual
smooth tensor cutoff and the original physical four-plus-three coordinates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem seven_symm_coordinate (p : Space (Fin 3)) (i : Fin 7) :
    sevenToProduct.symm p i = boxCoordinate (sevenCoordinateEquiv i) p := by
  cases h : sevenCoordinateEquiv i with
  | inl j =>
    change (Sum.elim (fun j => p.1 j) (fun j => p.2 j)) (sevenCoordinateEquiv i) = _
    rw [h]
    rfl
  | inr j =>
    change (Sum.elim (fun j => p.1 j) (fun j => p.2 j)) (sevenCoordinateEquiv i) = _
    rw [h]
    rfl

def fixedSevenLower (z : Space (Fin 3)) : Fin 7 → ℝ :=
  fun i => sevenToProduct.symm z i - 1/512

def fixedSevenUpper (z : Space (Fin 3)) : Fin 7 → ℝ :=
  fun i => sevenToProduct.symm z i + 1/512

def fixedSevenOpen (z : Space (Fin 3)) : Set (Fin 7 → ℝ) :=
  sevenToProduct ⁻¹' rectangularOpenBox z (1/512) (1/512)

theorem fixedSeven_lower_lt_upper (z : Space (Fin 3)) (i : Fin 7) :
    fixedSevenLower z i < fixedSevenUpper z i := by
  dsimp [fixedSevenLower,fixedSevenUpper]
  linarith

theorem fixedSeven_closed_iff (z : Space (Fin 3)) (x : Fin 7 → ℝ) :
    x ∈ tensorClosedBox7 (fixedSevenLower z) (fixedSevenUpper z) ↔
      sevenToProduct x ∈ rectangularClosedBox z (1/512) (1/512) := by
  have hcoord (i : Fin 7) :
      boxCoordinate (sevenCoordinateEquiv i) (sevenToProduct x-z) =
        x i-sevenToProduct.symm z i := by
    rw [← seven_symm_coordinate, map_sub]
    simp only [ContinuousLinearEquiv.symm_apply_apply, Pi.sub_apply]
  constructor
  · intro hx j
    obtain ⟨i,rfl⟩ := sevenCoordinateEquiv.surjective j
    rw [hcoord]
    have hi := hx i (Set.mem_univ i)
    have hi' : fixedSevenLower z i ≤ x i ∧ x i ≤ fixedSevenUpper z i := hi
    have hb : |x i-sevenToProduct.symm z i| ≤ (1/512 : ℝ) := by
      rw [abs_le]
      dsimp [fixedSevenLower,fixedSevenUpper] at hi'
      constructor <;> linarith [hi'.1,hi'.2]
    cases sevenCoordinateEquiv i <;> exact hb
  · intro hx i hi
    have hb := hx (sevenCoordinateEquiv i)
    rw [hcoord] at hb
    have hb' : |x i-sevenToProduct.symm z i| ≤ (1/512 : ℝ) := by
      cases he : sevenCoordinateEquiv i <;> simpa only [he,boxHalfWidth] using hb
    have hh := abs_le.mp hb'
    change fixedSevenLower z i ≤ x i ∧ x i ≤ fixedSevenUpper z i
    dsimp [fixedSevenLower,fixedSevenUpper]
    constructor <;> linarith [hh.1,hh.2]

theorem fixedSeven_open_isOpen (z : Space (Fin 3)) :
    IsOpen (fixedSevenOpen z) :=
  (rectangularOpenBox_isOpen z _ _).preimage sevenToProduct.continuous

theorem fixedSeven_open_subset_closed (z : Space (Fin 3)) :
    fixedSevenOpen z ⊆ tensorClosedBox7 (fixedSevenLower z) (fixedSevenUpper z) := by
  intro x hx
  exact (fixedSeven_closed_iff z x).mpr
    (rectangularOpenBox_subset_closedBox z _ _ hx)

theorem fixedSeven_open_image (z : Space (Fin 3)) :
    Set.image sevenToProduct (fixedSevenOpen z) = rectangularOpenBox z (1/512) (1/512) := by
  exact Set.image_preimage_eq _ sevenToProduct.surjective

theorem fixedSeven_maps_plateau (z : Space (Fin 3)) :
    MapsTo sevenToProduct (tensorClosedBox7 (fixedSevenLower z) (fixedSevenUpper z))
      (rectangularOpenBox z (3/1024) (3/1024)) := by
  intro x hx
  exact rectangularClosedBox_subset_openBox z (by norm_num) (by norm_num)
    ((fixedSeven_closed_iff z x).mp hx)

theorem fixedSeven_maps_norm_region (z : Space (Fin 3)) :
    MapsTo sevenToProduct (tensorClosedBox7 (fixedSevenLower z) (fixedSevenUpper z))
      (rectangularOpenBox z (1/256) (1/256)) := by
  intro x hx
  exact rectangularClosedBox_subset_openBox z (by norm_num) (by norm_num)
    ((fixedSeven_closed_iff z x).mp hx)

def fixedSevenCutoff (z : Space (Fin 3)) : Space (Fin 3) → ℝ :=
  grushinRectCutoff z (3/1024) (3/1024) (1/1024)

theorem fixedSevenCutoff_data (z : Space (Fin 3)) :
    ContDiff ℝ ∞ (fixedSevenCutoff z) ∧ HasCompactSupport (fixedSevenCutoff z) ∧
      tsupport (fixedSevenCutoff z) ⊆ rectangularOpenBox z (1/128) (1/128) ∧
      ∀ p ∈ rectangularOpenBox z (3/1024) (3/1024), fixedSevenCutoff z p = 1 := by
  refine ⟨grushinRectCutoff_contDiff _ _ _ _,
    grushinRectCutoff_compact _ (by norm_num) (by norm_num) (by norm_num),?_,?_⟩
  · exact (grushinRectCutoff_tsupport z (3/1024) (3/1024) (by norm_num)).trans
      (rectangularClosedBox_subset_openBox z (by norm_num) (by norm_num))
  · intro p hp
    exact grushinRectCutoff_plateau z _ _ (by norm_num)
      (rectangularOpenBox_subset_closedBox z _ _ hp)

def fixedSevenEvaluationConstant : ℝ := (257/16 : ℝ)^7

theorem fixedSevenEvaluationConstant_pos : 0 < fixedSevenEvaluationConstant := by
  norm_num [fixedSevenEvaluationConstant]

theorem fixedSeven_evaluation_constant (z : Space (Fin 3)) :
    boxEvaluationConstant (fixedSevenLower z) (fixedSevenUpper z) = fixedSevenEvaluationConstant := by
  dsimp only [fixedSevenEvaluationConstant]
  rw [boxEvaluationConstant_eq_product (fixedSeven_lower_lt_upper z)]
  have hlen (i : Fin 7) : fixedSevenUpper z i-fixedSevenLower z i = (1/256 : ℝ) := by
    dsimp [fixedSevenUpper,fixedSevenLower]
    ring
  simp_rw [hlen]
  have hs : Real.sqrt (1/256 : ℝ) = 1/16 := by
    rw [show (1/256 : ℝ) = (1/16 : ℝ)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs]
  norm_num

end TheoremT.Continuum.WeakGrushin
