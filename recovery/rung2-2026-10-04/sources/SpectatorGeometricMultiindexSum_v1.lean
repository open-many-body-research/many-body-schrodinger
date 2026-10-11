import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-! Exact geometric summation over actual spectator multiindices Fin d → Nat.
The proof includes dimension zero and uses no assumed multivariate series. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

def spectatorGeometricWeight {d : ℕ} (q : Fin d → ℝ) (γ : Fin d → ℕ) : ℝ :=
  ∏ i : Fin d, q i ^ γ i

theorem spectatorGeometricWeight_nonneg {d : ℕ} (q : Fin d → ℝ)
    (h0 : ∀ i, 0 ≤ q i) (γ : Fin d → ℕ) : 0 ≤ spectatorGeometricWeight q γ :=
  Finset.prod_nonneg (fun i _ => pow_nonneg (h0 i) _)

theorem spectator_geometric_hasSum (d : ℕ) (q : Fin d → ℝ)
    (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i < 1) :
    HasSum (spectatorGeometricWeight q) (∏ i : Fin d, (1-q i)⁻¹) := by
  induction d with
  | zero =>
    rw [show spectatorGeometricWeight q = (fun _γ : Fin 0 → ℕ => (1 : ℝ)) by
      funext γ
      simp [spectatorGeometricWeight]]
    simpa using
      hasSum_fintype (fun _γ : Fin 0 → ℕ => (1 : ℝ))
  | succ d ih =>
    have hh := hasSum_geometric_of_lt_one (h0 0) (h1 0)
    have ht := ih (fun i => q i.succ) (fun i => h0 i.succ) (fun i => h1 i.succ)
    have hp := hh.mul ht (hh.summable.mul_of_nonneg ht.summable
      (fun n => pow_nonneg (h0 0) n)
      (fun γ => spectatorGeometricWeight_nonneg _ (fun i => h0 i.succ) γ))
    rw [← (Fin.consEquiv (fun _ : Fin (d+1) => ℕ)).hasSum_iff]
    simpa [Function.comp_def, spectatorGeometricWeight, Fin.prod_univ_succ,
      Fin.consEquiv, mul_comm] using hp

theorem spectator_geometric_summable {d : ℕ} (q : Fin d → ℝ)
    (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i < 1) :
    Summable (spectatorGeometricWeight q) :=
  (spectator_geometric_hasSum d q h0 h1).summable

theorem spectator_geometric_tsum {d : ℕ} (q : Fin d → ℝ)
    (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i < 1) :
    (∑' γ : Fin d → ℕ, spectatorGeometricWeight q γ) = ∏ i : Fin d, (1-q i)⁻¹ :=
  (spectator_geometric_hasSum d q h0 h1).tsum_eq

theorem spectator_geometric_tsum_uniform_bound {d : ℕ} (q : Fin d → ℝ)
    (h0 : ∀ i, 0 ≤ q i) {s : ℝ} (hs : s < 1) (hqs : ∀ i, q i ≤ s) :
    (∑' γ : Fin d → ℕ, spectatorGeometricWeight q γ) ≤ ((1-s)^d)⁻¹ := by
  rw [spectator_geometric_tsum q h0 (fun i => (hqs i).trans_lt hs), ← inv_pow]
  calc
    _ ≤ ∏ _i : Fin d, (1-s)⁻¹ := by
      apply Finset.prod_le_prod₀ (fun i _ => inv_nonneg.mpr (sub_nonneg.mpr ((hqs i).trans hs.le)))
      intro i hi
      simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hs) (sub_le_sub_left (hqs i) 1)
    _ = ((1-s)⁻¹)^d := by simp

theorem spectator_geometric_tsum_dimension_zero (q : Fin 0 → ℝ) :
    (∑' γ : Fin 0 → ℕ, spectatorGeometricWeight q γ) = 1 := by
  simpa using spectator_geometric_tsum q (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

end TheoremT.Continuum
