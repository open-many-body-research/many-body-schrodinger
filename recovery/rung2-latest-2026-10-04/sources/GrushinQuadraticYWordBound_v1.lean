import ProductDirectionalWordLeibniz_v1
import FstDirectionalJet_v1
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Exact Y-word derivatives of the actual quadratic Grushin weight.
The scalar weight is norm(y)^2 in the existing product coordinates. Its first
two word derivatives are explicit, all words of length at least three vanish,
and one elementary bound covers every word on a bounded Y-region.
No solution derivative or regularity assertion is made.
-/
noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace TheoremT.Continuum.WeakGrushin
variable {kappa : Type} [Fintype kappa] [DecidableEq kappa]

def grushinQuadraticYWordBound (R : ℝ) : ℝ := R^2 + 2*R + 2

theorem grushinQuadraticYWordBound_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ grushinQuadraticYWordBound R := by
  dsimp [grushinQuadraticYWordBound]
  positivity

theorem grushin_quadratic_y_word_nil (p : Space kappa) :
    directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [] p = ‖p.1‖^2 := rfl

theorem grushin_quadratic_y_word_singleton (i : Fin 4) (p : Space kappa) :
    directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [i] p =
      2 * inner ℝ (oscillatorBasis i) p.1 := by
  have hn : ContDiff ℝ ∞ (fun y : KSSpace => ‖y‖^2) := contDiff_norm_sq ℝ
  change fderiv ℝ (fun q : Space kappa => ‖q.1‖^2) p (yDir i) = _
  rw [first_directional_fst (hn.differentiable (by simp)),
    fderiv_norm_sq_apply]
  simp [yDir, real_inner_comm]

theorem grushin_quadratic_y_word_pair (i j : Fin 4) (p : Space kappa) :
    directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [i,j] p =
      2 * inner ℝ (oscillatorBasis j : KSSpace) (oscillatorBasis i) := by
  have hfirst : directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [j] =
      (fun q : Space kappa => ((2 : ℝ) • innerSL ℝ (oscillatorBasis j)) q.1) := by
    funext q
    rw [grushin_quadratic_y_word_singleton]
    simp
  change fderiv ℝ (directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [j])
    p (yDir i) = _
  rw [hfirst,first_directional_fst (((2 : ℝ) • innerSL ℝ (oscillatorBasis j)).differentiable),
    ContinuousLinearMap.fderiv]
  simp [yDir]

theorem grushin_quadratic_y_word_triple (i j k : Fin 4) (p : Space kappa) :
    directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [i,j,k] p = 0 := by
  have hsecond : directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [j,k] =
      (fun _ : Space kappa => 2 * inner ℝ (oscillatorBasis k : KSSpace) (oscillatorBasis j)) :=
    funext (grushin_quadratic_y_word_pair j k)
  change fderiv ℝ (directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [j,k])
    p (yDir i) = 0
  rw [hsecond]
  simp

theorem grushin_quadratic_y_word_vanishes (w : List (Fin 4)) (hw : 3 ≤ w.length)
    (p : Space kappa) :
    directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) w p = 0 := by
  induction w generalizing p with
  | nil => simp at hw
  | cons i w ih =>
    by_cases htail : 3 ≤ w.length
    · have hzero : directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) w =
          (fun _ => 0) := funext (ih htail)
      change fderiv ℝ (directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) w)
        p (yDir i) = 0
      rw [hzero]
      simp
    · have hlen : w.length = 2 := by simp only [List.length_cons] at hw; omega
      obtain ⟨j,k,rfl⟩ := List.length_eq_two.mp hlen
      exact grushin_quadratic_y_word_triple i j k p

theorem grushin_quadratic_y_word_nil_bound {R : ℝ} {p : Space kappa}
    (hp : ‖p.1‖ ≤ R) :
    ‖directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [] p‖ ≤ R^2 := by
  rw [grushin_quadratic_y_word_nil,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hp 2

theorem grushin_quadratic_y_word_singleton_bound {R : ℝ} {p : Space kappa}
    (hp : ‖p.1‖ ≤ R) (i : Fin 4) :
    ‖directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [i] p‖ ≤ 2*R := by
  have hi : ‖(oscillatorBasis i : KSSpace)‖ = 1 := by
    simp [oscillatorBasis,EuclideanSpace.single]
  have hinner := norm_inner_le_norm (𝕜 := ℝ) (oscillatorBasis i) p.1
  rw [hi,one_mul,Real.norm_eq_abs] at hinner
  rw [grushin_quadratic_y_word_singleton,norm_mul]
  norm_num
  linarith

theorem grushin_quadratic_y_word_pair_bound (i j : Fin 4) (p : Space kappa) :
    ‖directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) [i,j] p‖ ≤ 2 := by
  have hi : ‖(oscillatorBasis i : KSSpace)‖ = 1 := by
    simp [oscillatorBasis,EuclideanSpace.single]
  have hj : ‖(oscillatorBasis j : KSSpace)‖ = 1 := by
    simp [oscillatorBasis,EuclideanSpace.single]
  have hinner := norm_inner_le_norm (𝕜 := ℝ) (oscillatorBasis j : KSSpace) (oscillatorBasis i)
  rw [hi,hj,one_mul,Real.norm_eq_abs] at hinner
  rw [grushin_quadratic_y_word_pair,norm_mul]
  norm_num
  linarith

theorem grushin_quadratic_y_word_bound {R : ℝ} (hR : 0 ≤ R)
    (w : List (Fin 4)) {p : Space kappa} (hp : ‖p.1‖ ≤ R) :
    ‖directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) w p‖ ≤
      grushinQuadraticYWordBound R := by
  rcases w with _ | ⟨i,w⟩
  · exact (grushin_quadratic_y_word_nil_bound hp).trans (by
      dsimp [grushinQuadraticYWordBound]; nlinarith [sq_nonneg R])
  rcases w with _ | ⟨j,w⟩
  · exact (grushin_quadratic_y_word_singleton_bound hp i).trans (by
      dsimp [grushinQuadraticYWordBound]; nlinarith [sq_nonneg R])
  rcases w with _ | ⟨k,w⟩
  · exact (grushin_quadratic_y_word_pair_bound i j p).trans (by
      dsimp [grushinQuadraticYWordBound]; nlinarith [sq_nonneg R])
  · rw [grushin_quadratic_y_word_vanishes (i :: j :: k :: w) (by simp),norm_zero]
    exact grushinQuadraticYWordBound_nonneg hR

theorem grushin_quadratic_y_word_bound_on
    {Omega : Set (Space kappa)} {R : ℝ} (hR : 0 ≤ R)
    (hOmega : ∀ p ∈ Omega, ‖p.1‖ ≤ R) :
    ∀ w : List (Fin 4), ∀ p ∈ Omega,
      ‖directionalWordDeriv yDir (fun q : Space kappa => ‖q.1‖^2) w p‖ ≤
        grushinQuadraticYWordBound R :=
  fun w p hp => grushin_quadratic_y_word_bound hR w (hOmega p hp)

end TheoremT.Continuum.WeakGrushin
