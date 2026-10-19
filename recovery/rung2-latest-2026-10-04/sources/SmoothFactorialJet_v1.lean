import SmoothComplexMixedSourceWords_v1
import ProductCoordinateWeakHk_v1
import MixedMultiIndexWord_v1
import CompactHessianCross_v1

/-! The actual smooth factorial jet, using the previously fixed canonical word.
Permutation invariance follows from ordinary second derivative symmetry. This
gives exact coordinate-shift identities and the compact support needed for the
weighted component estimates; no weak derivative family is assumed. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem complexDirectionalWordDeriv_contDiff {κ ι : Type}
    [Fintype κ] [DecidableEq κ] (dirs : ι → Space κ)
    {G : Space κ → ℂ} (hG : ContDiff ℝ ∞ G) (w : List ι) :
    ContDiff ℝ ∞ (complexDirectionalWordDeriv dirs G w) := by
  induction w with
  | nil => exact hG
  | cons i w ih =>
    exact (ih.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const

theorem complexDirectionalWordDeriv_tsupport_subset {κ ι : Type}
    [Fintype κ] [DecidableEq κ] (dirs : ι → Space κ)
    (G : Space κ → ℂ) (w : List ι) :
    tsupport (complexDirectionalWordDeriv dirs G w) ⊆ tsupport G := by
  induction w with
  | nil => exact Set.Subset.rfl
  | cons i w ih => exact (tsupport_fderiv_apply_subset ℝ (dirs i)).trans ih

theorem complexDirectionalWordDeriv_hasCompactSupport {κ ι : Type}
    [Fintype κ] [DecidableEq κ] (dirs : ι → Space κ)
    {G : Space κ → ℂ} (hc : HasCompactSupport G) (w : List ι) :
    HasCompactSupport (complexDirectionalWordDeriv dirs G w) := by
  induction w with
  | nil => exact hc
  | cons i w ih => exact ih.fderiv_apply ℝ (dirs i)

theorem complexDirectionalWordDeriv_perm {κ ι : Type}
    [Fintype κ] [DecidableEq κ] (dirs : ι → Space κ)
    {G : Space κ → ℂ} (hG : ContDiff ℝ ∞ G)
    {u v : List ι} (huv : u.Perm v) :
    complexDirectionalWordDeriv dirs G u = complexDirectionalWordDeriv dirs G v := by
  induction huv with
  | nil => rfl
  | cons i h ih => simp only [complexDirectionalWordDeriv, ih]
  | swap i j w =>
    funext p
    exact smooth_second_directional_commute
      (complexDirectionalWordDeriv_contDiff dirs hG w) p _ _
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

def smoothFactorialJet (G : Space (Fin 3) → ℂ)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) : Space (Fin 3) → ℂ :=
  complexDirectionalWordDeriv productCoordinateDirection G (mixedMultiIndexWord α β)

theorem smoothFactorialJet_contDiff {G : Space (Fin 3) → ℂ}
    (hG : ContDiff ℝ ∞ G) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    ContDiff ℝ ∞ (smoothFactorialJet G α β) :=
  complexDirectionalWordDeriv_contDiff productCoordinateDirection hG _

theorem smoothFactorialJet_tsupport_subset (G : Space (Fin 3) → ℂ)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    tsupport (smoothFactorialJet G α β) ⊆ tsupport G :=
  complexDirectionalWordDeriv_tsupport_subset productCoordinateDirection G _

theorem smoothFactorialJet_hasCompactSupport {G : Space (Fin 3) → ℂ}
    (hc : HasCompactSupport G) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
    HasCompactSupport (smoothFactorialJet G α β) :=
  complexDirectionalWordDeriv_hasCompactSupport productCoordinateDirection hc _

theorem smoothFactorialJet_zero (G : Space (Fin 3) → ℂ) :
    smoothFactorialJet G 0 0 = G := by
  change complexDirectionalWordDeriv productCoordinateDirection G
    (mixedMultiIndexWord (fun _ => 0) (fun _ => 0)) = G
  rw [mixedMultiIndexWord_zero]
  rfl

theorem smoothFactorialJet_add_single_y {G : Space (Fin 3) → ℂ}
    (hG : ContDiff ℝ ∞ G) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (i : Fin 4) :
    smoothFactorialJet G (α + Pi.single i 1) β =
      partialYDirectional (smoothFactorialJet G α β) (oscillatorBasis i) := by
  exact complexDirectionalWordDeriv_perm productCoordinateDirection hG
    (mixedMultiIndexWord_add_single_y_perm α β i)

theorem smoothFactorialJet_add_single_t {G : Space (Fin 3) → ℂ}
    (hG : ContDiff ℝ ∞ G) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (j : Fin 3) :
    smoothFactorialJet G α (β + Pi.single j 1) =
      partialTDirectional (smoothFactorialJet G α β) (oscillatorBasis j) := by
  exact complexDirectionalWordDeriv_perm productCoordinateDirection hG
    (mixedMultiIndexWord_add_single_t_perm α β j)

theorem smoothFactorialJet_single_y {G : Space (Fin 3) → ℂ}
    (hG : ContDiff ℝ ∞ G) (i : Fin 4) :
    smoothFactorialJet G (Pi.single i 1) 0 = partialYDirectional G (oscillatorBasis i) := by
  simpa only [zero_add, smoothFactorialJet_zero] using smoothFactorialJet_add_single_y hG 0 0 i

theorem smoothFactorialJet_single_t {G : Space (Fin 3) → ℂ}
    (hG : ContDiff ℝ ∞ G) (j : Fin 3) :
    smoothFactorialJet G 0 (Pi.single j 1) = partialTDirectional G (oscillatorBasis j) := by
  simpa only [zero_add, smoothFactorialJet_zero] using smoothFactorialJet_add_single_t hG 0 0 j

theorem smoothFactorialJet_double_y {G : Space (Fin 3) → ℂ}
    (hG : ContDiff ℝ ∞ G) (i j : Fin 4) :
    smoothFactorialJet G (Pi.single i 1 + Pi.single j 1) 0 =
      partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) := by
  rw [smoothFactorialJet_add_single_y hG, smoothFactorialJet_single_y hG]

theorem smoothFactorialJet_mixed {G : Space (Fin 3) → ℂ}
    (hG : ContDiff ℝ ∞ G) (i : Fin 4) (j : Fin 3) :
    smoothFactorialJet G (Pi.single i 1) (Pi.single j 1) =
      partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) := by
  simpa only [zero_add, smoothFactorialJet_single_y hG] using
    smoothFactorialJet_add_single_t hG (Pi.single i 1) 0 j

theorem smoothFactorialJet_double_t {G : Space (Fin 3) → ℂ}
    (hG : ContDiff ℝ ∞ G) (i j : Fin 3) :
    smoothFactorialJet G 0 (Pi.single i 1 + Pi.single j 1) =
      partialTDirectional (partialTDirectional G (oscillatorBasis i)) (oscillatorBasis j) := by
  rw [smoothFactorialJet_add_single_t hG, smoothFactorialJet_single_t hG]

end TheoremT.Continuum.WeakGrushin
