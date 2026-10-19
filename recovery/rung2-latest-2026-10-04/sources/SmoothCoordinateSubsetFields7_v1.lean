import CompactHessianCross_v1
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Finset.Sort

/-! Canonical mixed subset fields of actual smooth complex coordinate words
on the ordinary seven-coordinate space. The normed-domain word definition
requires no inner-product structure. Sorted finite subsets contain each
coordinate once; smooth permutation identifies insertion with differentiation. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

def normedComplexDirectionalWordDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} (dirs : ι → E) (f : E → ℂ) : List ι → E → ℂ
  | [] => f
  | i :: w => fun x => fderiv ℝ (normedComplexDirectionalWordDeriv dirs f w) x (dirs i)

theorem normedComplexDirectionalWordDeriv_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} (dirs : ι → E) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (w : List ι) :
    ContDiff ℝ ∞ (normedComplexDirectionalWordDeriv dirs f w) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem normedComplexDirectionalWordDeriv_append {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} (dirs : ι → E) (f : E → ℂ) (u v : List ι) :
    normedComplexDirectionalWordDeriv dirs f (u ++ v) =
      normedComplexDirectionalWordDeriv dirs (normedComplexDirectionalWordDeriv dirs f v) u := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append,normedComplexDirectionalWordDeriv,ih]

theorem normedComplexDirectionalWordDeriv_perm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} (dirs : ι → E) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) {u v : List ι} (huv : u.Perm v) :
    normedComplexDirectionalWordDeriv dirs f u = normedComplexDirectionalWordDeriv dirs f v := by
  induction huv with
  | nil => rfl
  | cons i h ih => simp only [normedComplexDirectionalWordDeriv,ih]
  | swap i j w =>
    funext x
    exact smooth_second_directional_commute
      (normedComplexDirectionalWordDeriv_contDiff dirs hf w) x _ _
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

def coordinateWordDeriv7 (f : (Fin 7 → ℝ) → ℂ) : List (Fin 7) → (Fin 7 → ℝ) → ℂ :=
  normedComplexDirectionalWordDeriv (fun i => Pi.single i (1 : ℝ)) f

def canonicalSubsetWord7 (s : Finset (Fin 7)) : List (Fin 7) := s.sort (· ≤ ·)

theorem canonicalSubsetWord7_nodup (s : Finset (Fin 7)) : (canonicalSubsetWord7 s).Nodup :=
  Finset.sort_nodup _ _

theorem canonicalSubsetWord7_insert_perm (s : Finset (Fin 7)) (i : Fin 7) (hi : i ∉ s) :
    (canonicalSubsetWord7 (insert i s)).Perm (i :: canonicalSubsetWord7 s) := by
  apply Multiset.coe_eq_coe.mp
  simp only [canonicalSubsetWord7,Finset.sort_eq,← Multiset.cons_coe]
  rw [← Finset.cons_val hi,Finset.cons_eq_insert]

theorem canonicalSubsetWord7_append_length (s : Finset (Fin 7)) (w : List (Fin 7)) :
    (canonicalSubsetWord7 s ++ w).length ≤ w.length + 7 := by
  have hs : s.card ≤ 7 := by simpa using Finset.card_le_card (Finset.subset_univ s)
  simp only [List.length_append,canonicalSubsetWord7,Finset.length_sort]
  omega

def smoothSubsetField7 (f : (Fin 7 → ℝ) → ℂ) (s : Finset (Fin 7)) : (Fin 7 → ℝ) → ℂ :=
  coordinateWordDeriv7 f (canonicalSubsetWord7 s)

theorem smoothSubsetField7_empty (f : (Fin 7 → ℝ) → ℂ) : smoothSubsetField7 f ∅ = f := by
  simp only [smoothSubsetField7,canonicalSubsetWord7,Finset.sort_empty,
    coordinateWordDeriv7,normedComplexDirectionalWordDeriv]

theorem smoothSubsetField7_contDiff {f : (Fin 7 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (s : Finset (Fin 7)) : ContDiff ℝ ∞ (smoothSubsetField7 f s) :=
  normedComplexDirectionalWordDeriv_contDiff _ hf _

theorem smoothSubsetField7_word_base (f : (Fin 7 → ℝ) → ℂ)
    (w : List (Fin 7)) (s : Finset (Fin 7)) :
    smoothSubsetField7 (coordinateWordDeriv7 f w) s =
      coordinateWordDeriv7 f (canonicalSubsetWord7 s ++ w) :=
  (normedComplexDirectionalWordDeriv_append _ f _ w).symm

theorem smoothSubsetField7_directional {f : (Fin 7 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (s : Finset (Fin 7)) (i : Fin 7) (hi : i ∉ s) (x : Fin 7 → ℝ) :
    fderiv ℝ (smoothSubsetField7 f s) x (Pi.single i (1 : ℝ)) =
      smoothSubsetField7 f (insert i s) x := by
  exact congrFun (normedComplexDirectionalWordDeriv_perm
    (fun j => Pi.single j (1 : ℝ)) hf (canonicalSubsetWord7_insert_perm s i hi)).symm x

theorem smoothSubsetField7_coordinate_hasDerivAt
    {f : (Fin 7 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (s : Finset (Fin 7)) (i : Fin 7) (hi : i ∉ s) (x : Fin 7 → ℝ) :
    HasDerivAt (fun r => smoothSubsetField7 f s (Function.update x i r))
      (smoothSubsetField7 f (insert i s) x) (x i) := by
  have hh := (((smoothSubsetField7_contDiff hf s).differentiable (by simp))
    (Function.update x i (x i))).hasFDerivAt.comp_hasDerivAt (x i)
      (hasDerivAt_update x i (x i))
  simpa only [Function.update_eq_self,Function.comp_def,
    smoothSubsetField7_directional hf s i hi x] using hh

end TheoremT.Continuum
