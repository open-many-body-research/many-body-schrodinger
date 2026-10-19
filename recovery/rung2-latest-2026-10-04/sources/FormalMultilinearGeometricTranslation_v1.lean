import FormalMultilinearGeometricAnalytic_v1
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Powerset

/-! Explicit norms of actual translated multilinear coefficients. The
binomial multiplicity is counted exactly and summed by a proved geometric
identity, so the constant is uniform in derivative order. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators NNReal ENNReal
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem formalMultilinearSeries_changeOrigin_term_norm
    (p : FormalMultilinearSeries ℂ E ℂ) (x : E) (k l : ℕ) :
    ‖p.changeOriginSeries k l (fun _ => x)‖ ≤
      ((l+k).choose k : ℝ)*‖p (k+l)‖*‖x‖^l := by
  have h := p.nnnorm_changeOriginSeries_apply_le_tsum k l x
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,Fintype.card_finset_len,Fintype.card_fin] at h
  have hc : (k+l).choose l = (l+k).choose k := by
    rw [Nat.add_comm k l, Nat.choose_symm_add]
  rw [hc] at h
  rw [mul_assoc]
  exact_mod_cast h

theorem formalMultilinearSeries_changeOrigin_geometric_bound
    (p : FormalMultilinearSeries ℂ E ℂ) {M D : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hp : ∀ n, ‖p n‖ ≤ M*D^n)
    (x : E) (hx : D*‖x‖ < 1) (k : ℕ) :
    ‖p.changeOrigin x k‖ ≤ M*D^k/(1-D*‖x‖)^(k+1) := by
  have hq : ‖D*‖x‖‖ < 1 := by rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hD (norm_nonneg x))]; exact hx
  have hgeom := (summable_choose_mul_geometric_of_norm_lt_one k hq).mul_left (M*D^k)
  have hterm (l : ℕ) : ‖p.changeOriginSeries k l (fun _ => x)‖ ≤
      (M*D^k)*(((l+k).choose k : ℝ)*(D*‖x‖)^l) := by
    calc
      _ ≤ ((l+k).choose k : ℝ)*‖p (k+l)‖*‖x‖^l := formalMultilinearSeries_changeOrigin_term_norm p x k l
      _ ≤ ((l+k).choose k : ℝ)*(M*D^(k+l))*‖x‖^l := by gcongr; exact hp (k+l)
      _ = _ := by rw [pow_add,mul_pow]; ring
  have habs : Summable (fun l => ‖p.changeOriginSeries k l (fun _ => x)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgeom
  change ‖∑' l, p.changeOriginSeries k l (fun _ => x)‖ ≤ _
  calc
    _ ≤ ∑' l, ‖p.changeOriginSeries k l (fun _ => x)‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' l, (M*D^k)*(((l+k).choose k : ℝ)*(D*‖x‖)^l) := habs.tsum_le_tsum hterm hgeom
    _ = _ := by rw [tsum_mul_left,tsum_choose_mul_geometric_of_norm_lt_one k hq]; ring

end TheoremT.Continuum
