import PhysicalKSBoxFactorialBudgetMono_v1
import CoulombSpinPhysicalH12_v1

/-! Finite-spin domination for the displayed physical KS source and H12
budgets. No spin wavefunction or derivative family is chosen here: the final
implication enlarges the bound of an existing component family to the shared
finite-spin budgets while keeping every weak identity intact. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
namespace TheoremT.Continuum
open WeakGrushin

theorem complex_component_norm_le_sqrt_sum_sq {ι : Type} [Fintype ι]
    (z : ι → ℂ) (i : ι) : ‖z i‖ ≤ Real.sqrt (∑ j, ‖z j‖^2) := by
  classical
  exact Real.le_sqrt_of_sq_le
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ i))

def spinOriginFactorialSourceBudget (M : ℝ)
    (u : SpinConfiguration 2 → Configuration 2 → ℂ) : ℝ :=
  M*Real.sqrt (∑ σ, ‖u σ 0‖^2)*Real.sqrt physicalKSUniformSourceVolume

theorem spinOriginFactorialSourceBudget_nonneg {M : ℝ} (hM : 0 ≤ M)
    (u : SpinConfiguration 2 → Configuration 2 → ℂ) :
    0 ≤ spinOriginFactorialSourceBudget M u := by
  unfold spinOriginFactorialSourceBudget
  positivity

theorem spinOriginFactorialSourceBudget_component_le {M : ℝ} (hM : 0 ≤ M)
    (u : SpinConfiguration 2 → Configuration 2 → ℂ) (σ : SpinConfiguration 2) :
    M*‖u σ 0‖*Real.sqrt physicalKSUniformSourceVolume ≤
      spinOriginFactorialSourceBudget M u := by
  unfold spinOriginFactorialSourceBudget
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (complex_component_norm_le_sqrt_sum_sq (fun τ => u τ 0) σ) hM)
    (Real.sqrt_nonneg _)

theorem spinOriginH12Budget_component_le {C_H : ℝ} (hC : 0 ≤ C_H)
    (L : ℝ≥0) (u : SpinConfiguration 2 → Configuration 2 → ℂ) (σ : SpinConfiguration 2) :
    (((L : ℝ)^2+‖u σ 0‖^2)*C_H) ≤ spinOriginH12Budget C_H L u := by
  classical
  have hi : ‖u σ 0‖^2 ≤ ∑ τ, ‖u τ 0‖^2 :=
    Finset.single_le_sum (fun τ _ => sq_nonneg ‖u τ 0‖) (Finset.mem_univ σ)
  exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hi) hC

theorem PhysicalKSBoxFactorialData.mono_spin_budget
    {f : Space (Fin 3) → ℂ} {t0 : Position} {C_H M A : ℝ}
    {L : ℝ≥0} {u : SpinConfiguration 2 → Configuration 2 → ℂ} {σ : SpinConfiguration 2}
    (h : PhysicalKSBoxFactorialData f t0 M A
      (M*‖u σ 0‖*Real.sqrt physicalKSUniformSourceVolume)
      (((L : ℝ)^2+‖u σ 0‖^2)*C_H))
    (hC : 1 ≤ C_H) (hM : 1 ≤ M) (hA : 1 ≤ A) :
    PhysicalKSBoxFactorialData f t0 M A
      (spinOriginFactorialSourceBudget M u) (spinOriginH12Budget C_H L u) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hC0 : 0 ≤ C_H := zero_le_one.trans hC
  exact h.mono_source_budget hM hA (by positivity) (by positivity)
    (spinOriginFactorialSourceBudget_component_le hM0 u σ)
    (spinOriginH12Budget_component_le hC0 L u σ)

end TheoremT.Continuum
