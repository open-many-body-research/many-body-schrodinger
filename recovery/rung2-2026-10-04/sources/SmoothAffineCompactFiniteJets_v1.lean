import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Finite-order compact jet bounds for smooth real affine coefficient families.
The constant is chosen before the parameter in [0,1] and before the complex
constant vector. Only a fixed finite derivative reserve is bounded. These
existence statements give no algorithm for evaluating the constant and assert
no bound with a prescribed dependence on derivative order.
-/
noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem smooth_compact_finite_iteratedFDeriv_bound
    {f : X → ℝ} {Omega K : Set X} (hOmega : IsOpen Omega)
    (hK : IsCompact K) (hKOmega : K ⊆ Omega)
    (hf : ContDiffOn ℝ ∞ f Omega) (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ k : ℕ, k ≤ m → ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ M := by
  classical
  have hb (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
    have hc : ContinuousOn (iteratedFDeriv ℝ k f) K :=
      (ContinuousOn.continuousOn_iteratedFDeriv hf hOmega (by simp)).mono hKOmega
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
    exact ⟨max 0 C, le_max_left _ _, fun x hx => (hC x hx).trans (le_max_right _ _)⟩
  choose C hC0 hC using hb
  refine ⟨1 + ∑ k ∈ Finset.range (m + 1), C k, ?_, ?_⟩
  · have hs : 0 ≤ ∑ k ∈ Finset.range (m + 1), C k :=
      Finset.sum_nonneg (fun k _ => hC0 k)
    linarith
  · intro k hk x hx
    have hs : C k ≤ ∑ j ∈ Finset.range (m + 1), C j :=
      Finset.single_le_sum (fun j _ => hC0 j)
        (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))
    exact (hC k x hx).trans (by linarith)

theorem smooth_affine_compact_finite_iteratedFDeriv_bound
    {f0 f1 : X → ℝ} {Omega K : Set X} (hOmega : IsOpen Omega)
    (hK : IsCompact K) (hKOmega : K ⊆ Omega)
    (hf0 : ContDiffOn ℝ ∞ f0 Omega) (hf1 : ContDiffOn ℝ ∞ f1 Omega)
    (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ k : ℕ, k ≤ m → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x‖ ≤ M ∧
        ‖iteratedFDeriv ℝ k (fun q => eps * (f0 q + eps * f1 q)) x‖ ≤ M := by
  obtain ⟨M0, hM0, hb0⟩ :=
    smooth_compact_finite_iteratedFDeriv_bound hOmega hK hKOmega hf0 m
  obtain ⟨M1, hM1, hb1⟩ :=
    smooth_compact_finite_iteratedFDeriv_bound hOmega hK hKOmega hf1 m
  refine ⟨M0 + M1, by linarith, ?_⟩
  intro eps heps0 heps1 k hk x hx
  have h0 : ContDiffAt ℝ k f0 x :=
    (hf0.contDiffAt (hOmega.mem_nhds (hKOmega hx))).of_le (by simp)
  have h1 : ContDiffAt ℝ k f1 x :=
    (hf1.contDiffAt (hOmega.mem_nhds (hKOmega hx))).of_le (by simp)
  have heps : ‖eps‖ ≤ 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg heps0]
  have ha : ContDiffAt ℝ k (fun q => f0 q + eps * f1 q) x := by
    simpa only [smul_eq_mul] using h0.add (h1.const_smul eps)
  have h1eps : ContDiffAt ℝ k (eps • f1) x := h1.const_smul eps
  have hba : ‖iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x‖ ≤ M0 + M1 := by
    change ‖iteratedFDeriv ℝ k (f0 + eps • f1) x‖ ≤ M0 + M1
    rw [iteratedFDeriv_add_apply h0 h1eps,
      iteratedFDeriv_const_smul_apply h1]
    calc
      ‖iteratedFDeriv ℝ k f0 x + eps • iteratedFDeriv ℝ k f1 x‖
          ≤ ‖iteratedFDeriv ℝ k f0 x‖ + ‖eps • iteratedFDeriv ℝ k f1 x‖ := norm_add_le _ _
      _ = ‖iteratedFDeriv ℝ k f0 x‖ + ‖eps‖ * ‖iteratedFDeriv ℝ k f1 x‖ := by rw [norm_smul]
      _ ≤ M0 + 1 * M1 := add_le_add (hb0 k hk x hx)
        (mul_le_mul heps (hb1 k hk x hx) (norm_nonneg _) (by norm_num))
      _ = M0 + M1 := by ring
  refine ⟨hba, ?_⟩
  change ‖iteratedFDeriv ℝ k (eps • (fun q => f0 q + eps * f1 q)) x‖ ≤ M0 + M1
  rw [iteratedFDeriv_const_smul_apply ha, norm_smul]
  calc
    ‖eps‖ * ‖iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x‖
        ≤ 1 * (M0 + M1) := mul_le_mul heps hba (norm_nonneg _) (by norm_num)
    _ = M0 + M1 := one_mul _

theorem smooth_affine_compact_finite_source_bound
    {f0 f1 : X → ℝ} {Omega K : Set X} (hOmega : IsOpen Omega)
    (hK : IsCompact K) (hKOmega : K ⊆ Omega)
    (hf0 : ContDiffOn ℝ ∞ f0 Omega) (hf1 : ContDiffOn ℝ ∞ f1 Omega)
    (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ k : ℕ, k ≤ m → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x‖ ≤ M ∧
        ‖iteratedFDeriv ℝ k (fun q => eps * (f0 q + eps * f1 q)) x‖ ≤ M ∧
        ∀ a0 : ℂ,
          ‖iteratedFDeriv ℝ k (fun q => (f0 q + eps * f1 q) • a0) x‖ ≤ M * ‖a0‖ := by
  obtain ⟨M, hM, hb⟩ :=
    smooth_affine_compact_finite_iteratedFDeriv_bound hOmega hK hKOmega hf0 hf1 m
  refine ⟨M, hM, ?_⟩
  intro eps heps0 heps1 k hk x hx
  obtain ⟨ha, hs⟩ := hb eps heps0 heps1 k hk x hx
  refine ⟨ha, hs, ?_⟩
  intro a0
  have h0 : ContDiffAt ℝ k f0 x :=
    (hf0.contDiffAt (hOmega.mem_nhds (hKOmega hx))).of_le (by simp)
  have h1 : ContDiffAt ℝ k f1 x :=
    (hf1.contDiffAt (hOmega.mem_nhds (hKOmega hx))).of_le (by simp)
  have hc : ContDiffAt ℝ k (fun q => f0 q + eps * f1 q) x := by
    simpa only [smul_eq_mul] using h0.add (h1.const_smul eps)
  rw [iteratedFDeriv_smul_const_apply hc]
  calc
    ‖((ContinuousLinearMap.id ℝ ℝ).smulRight a0).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x)‖
        ≤ ‖(ContinuousLinearMap.id ℝ ℝ).smulRight a0‖ *
          ‖iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ = ‖a0‖ * ‖iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_id, one_mul]
    _ ≤ ‖a0‖ * M := mul_le_mul_of_nonneg_left ha (norm_nonneg _)
    _ = M * ‖a0‖ := mul_comm _ _

end TheoremT.Continuum
