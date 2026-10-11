import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Tactic

/-! A finite-coordinate estimate for an actual continuous multilinear
operator norm. Reconstruction and unit coordinate bounds are explicit;
no orthonormal structure, change of ambient norm, or desired operator bound
is assumed. The cardinality factor counts all coordinate tuples. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_coordinate_multilinear_opNorm_le
    (dirs : ι → E) (coord : E → ι → ℝ)
    (hreconstruct : ∀ x, ∑ j, coord x j • dirs j = x)
    (hcoord : ∀ x j, |coord x j| ≤ ‖x‖)
    {k : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ a : Fin k → ι, ‖T (fun i => dirs (a i))‖ ≤ M) :
    ‖T‖ ≤ (Fintype.card ι : ℝ)^k*M := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hM)
  intro v
  have hexpand : T v = ∑ a : Fin k → ι,
      T (fun i => coord (v i) (a i) • dirs (a i)) := by
    simpa only [hreconstruct] using
      T.map_sum (fun i j => coord (v i) j • dirs j)
  have hterm (a : Fin k → ι) :
      ‖T (fun i => coord (v i) (a i) • dirs (a i))‖ ≤ M*∏ i, ‖v i‖ := by
    rw [T.map_smul_univ, norm_smul, Real.norm_eq_abs, Finset.abs_prod]
    have hp : (∏ i, |coord (v i) (a i)|) ≤ ∏ i, ‖v i‖ := by
      gcongr with i
      exact hcoord (v i) (a i)
    calc
      _ ≤ (∏ i, ‖v i‖)*M := mul_le_mul hp (hT a) (norm_nonneg _) (by positivity)
      _ = _ := mul_comm _ _
  calc
    ‖T v‖ = ‖∑ a : Fin k → ι,
      T (fun i => coord (v i) (a i) • dirs (a i))‖ := congrArg norm hexpand
    _ ≤ ∑ a : Fin k → ι, ‖T (fun i => coord (v i) (a i) • dirs (a i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _a : Fin k → ι, M*∏ i, ‖v i‖ := Finset.sum_le_sum (fun a _ => hterm a)
    _ = ((Fintype.card ι : ℝ)^k*M)*∏ i, ‖v i‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      ring

end TheoremT.Continuum
