import ProductBoxAverageMeasure_v1
import Mathlib.Algebra.BigOperators.Fin

/-! Algebra of the actual finite rectangular evaluation constant. The generic
constant equals the product of the one-coordinate inverse-square-root plus
square-root factors. The seven-coordinate specialization has four Y factors
and three T factors, without dependence on any function or derivative order. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι]

def boxEvaluationConstant (a b : ι → ℝ) : ℝ :=
  (Real.sqrt (productBoxVolume a b))⁻¹ * ∏ i, (1+(b i-a i))

theorem boxEvaluationConstant_pos {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    0 < boxEvaluationConstant a b := by
  unfold boxEvaluationConstant
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (productBoxVolume_pos hab)))
    (Finset.prod_pos (fun i _ => by linarith [hab i]))

theorem boxEvaluationConstant_eq_product {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    boxEvaluationConstant a b =
      ∏ i, ((Real.sqrt (b i-a i))⁻¹ + Real.sqrt (b i-a i)) := by
  unfold boxEvaluationConstant productBoxVolume
  rw [Real.sqrt_prod _ (fun i _ => (sub_pos.mpr (hab i)).le),
    ← Finset.prod_inv_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hL : 0 < b i-a i := sub_pos.mpr (hab i)
  have hs : 0 < Real.sqrt (b i-a i) := Real.sqrt_pos.mpr hL
  field_simp
  nlinarith [Real.sq_sqrt hL.le]

theorem boxEvaluationConstant_four_three
    {a b : Fin 7 → ℝ} {Ly Lt : ℝ} (hLy : 0 < Ly) (hLt : 0 < Lt)
    (hlen : ∀ i, b i-a i = if i.val < 4 then Ly else Lt) :
    boxEvaluationConstant a b =
      ((Real.sqrt Ly)⁻¹ + Real.sqrt Ly)^4 *
        ((Real.sqrt Lt)⁻¹ + Real.sqrt Lt)^3 := by
  have hab : ∀ i, a i < b i := by
    intro i
    apply sub_pos.mp
    rw [hlen i]
    split_ifs <;> assumption
  rw [boxEvaluationConstant_eq_product hab]
  simp_rw [hlen]
  norm_num [Fin.prod_univ_succ]
  ring

end TheoremT.Continuum
