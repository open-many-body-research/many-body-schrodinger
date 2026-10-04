import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
/-! Finite real distance monomials with one rational coefficient approximation.

The exact iterated derivatives of a finite dictionary depend linearly on its
coefficients. Compactness of a literal bounded coordinate box and rational
density provide one rational coefficient family that approximates the same
polynomial in value and in real first and second operator norms throughout
the box. No derivative bound, approximation premise, or effective choice is
assumed. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff BigOperators
namespace ManyBody.S8
abbrev DistanceMultiIndex := Fin 3 → ℕ

def realDistanceMonomial (α : DistanceMultiIndex) (p : Fin 3 → ℝ) : ℝ :=
  ∏ j, (p j)^(α j)

def realDistancePolynomial (s : Finset DistanceMultiIndex)
    (c : DistanceMultiIndex → ℝ) (p : Fin 3 → ℝ) : ℝ :=
  ∑ α∈s, c α • realDistanceMonomial α p

theorem realDistanceMonomial_contDiff (α : DistanceMultiIndex) :
    ContDiff ℝ ∞ (realDistanceMonomial α) := by
  unfold realDistanceMonomial
  fun_prop

theorem realDistancePolynomial_contDiff (s : Finset DistanceMultiIndex)
    (c : DistanceMultiIndex → ℝ) : ContDiff ℝ ∞ (realDistancePolynomial s c) := by
  unfold realDistancePolynomial
  exact ContDiff.sum fun α _ => (realDistanceMonomial_contDiff α).const_smul (c α)

theorem iteratedFDeriv_realDistancePolynomial (s : Finset DistanceMultiIndex)
    (c : DistanceMultiIndex → ℝ) (n : ℕ) (p : Fin 3 → ℝ) :
    iteratedFDeriv ℝ n (realDistancePolynomial s c) p=
      ∑ α∈s, c α • iteratedFDeriv ℝ n (realDistanceMonomial α) p := by
  unfold realDistancePolynomial
  rw [iteratedFDeriv_fun_sum_apply (fun α _ =>
    ((realDistanceMonomial_contDiff α).of_le (by simp : (n:ℕ∞ω)≤∞)).contDiffAt.const_smul (c α))]
  apply Finset.sum_congr rfl
  intro α hα
  exact iteratedFDeriv_const_smul_apply' (a := c α)
    (((realDistanceMonomial_contDiff α).of_le (by simp : (n:ℕ∞ω)≤∞)).contDiffAt)

theorem rational_realDistancePolynomial_uniform_C2
    (s : Finset DistanceMultiIndex) (c : DistanceMultiIndex → ℝ) (b : ℝ)
    {ε : ℝ} (hε : 0<ε) :
    ∃ r : DistanceMultiIndex → ℚ,
      ∀ p : Fin 3 → ℝ, ‖p‖≤b → ∀ k : Fin 3,
        ‖iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s c) p-
          iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s (fun α => (r α:ℝ))) p‖<ε := by
  classical
  have hBounds : ∀ α : DistanceMultiIndex, ∀ k : Fin 3, ∃ B : ℝ, 0≤B ∧
      ∀ p∈closedBall (0 : Fin 3 → ℝ) b,
        ‖iteratedFDeriv ℝ (k:ℕ) (realDistanceMonomial α) p‖≤B := by
    intro α k
    have hcont : Continuous (iteratedFDeriv ℝ (k:ℕ) (realDistanceMonomial α)) :=
      continuous_iff_continuousAt.mpr fun p =>
        (realDistanceMonomial_contDiff α).contDiffAt.continuousAt_iteratedFDeriv (by simp)
    obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Fin 3 → ℝ) b).exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨max 0 B,le_max_left _ _,fun p hp => (hB p hp).trans (le_max_right _ _)⟩
  choose B hB0 hB using hBounds
  let K : ℝ := 1+∑ α∈s, ∑ k : Fin 3, B α k
  have hK : 0<K := by
    have hs : 0≤∑ α∈s, ∑ k : Fin 3, B α k :=
      Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun k _ => hB0 α k
    dsimp [K]
    linarith
  let η : ℝ := ε/(2*K)
  have hη : 0<η := div_pos hε (mul_pos (by norm_num) hK)
  have hrat : ∀ α : DistanceMultiIndex, ∃ q : ℚ, |c α-(q:ℝ)|<η :=
    fun α => exists_rat_near (c α) hη
  choose r hr using hrat
  refine ⟨r,?_⟩
  intro p hp k
  have hpball : p∈closedBall (0 : Fin 3 → ℝ) b := by simpa only [mem_closedBall,dist_zero_right] using hp
  rw [iteratedFDeriv_realDistancePolynomial,iteratedFDeriv_realDistancePolynomial,←Finset.sum_sub_distrib]
  simp_rw [←sub_smul]
  have hk : (∑ α∈s, B α k)≤K := by
    have hh := Finset.sum_le_sum (s:=s) (fun α _ =>
      Finset.single_le_sum (fun j _ => hB0 α j) (Finset.mem_univ k))
    dsimp [K]
    linarith
  calc
    _≤∑ α∈s, ‖(c α-(r α:ℝ)) • iteratedFDeriv ℝ (k:ℕ) (realDistanceMonomial α) p‖ :=
      norm_sum_le _ _
    _≤∑ α∈s, η*B α k := by
      apply Finset.sum_le_sum
      intro α hα
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hr α).le (hB α k p hpball) (norm_nonneg _) hη.le
    _=η*(∑ α∈s, B α k) := by rw [Finset.mul_sum]
    _≤η*K := mul_le_mul_of_nonneg_left hk hη.le
    _=ε/2 := by dsimp [η]; field_simp
    _<ε := by linarith

#print axioms iteratedFDeriv_realDistancePolynomial
#print axioms rational_realDistancePolynomial_uniform_C2
end ManyBody.S8
