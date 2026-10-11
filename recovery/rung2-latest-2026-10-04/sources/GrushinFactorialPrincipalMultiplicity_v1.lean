import GrushinFactorialPrincipalComponentL2_v1

/-! Exact multiplicity counting and norm summation for R15. Three
spectator directions give factors 6 and 3; the falling factorial is the
natural-number multiplicity r(r-1), including the cases r=0 and r=1. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem factorial_diagonal_pair_count_le (α : Fin 4 → ℕ) (r : ℕ)
    (hA : (∑ i, α i) ≤ r) :
    (∑ i, α i*(α i-1)) ≤ r*(r-1) := by
  let A := ∑ i, α i
  have hi (i : Fin 4) : α i ≤ A :=
    Finset.single_le_sum (fun l _ => Nat.zero_le _) (Finset.mem_univ i)
  calc
    (∑ i, α i*(α i-1)) ≤ ∑ i, α i*(A-1) :=
      Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (hi i) 1))
    _ = A*(A-1) := by rw [← Finset.sum_mul]
    _ ≤ r*(r-1) := Nat.mul_le_mul hA (Nat.sub_le_sub_right hA 1)

theorem factorial_fin4_fin3_norm_sum_le {E : Type*} [SeminormedAddCommGroup E]
    (U : Fin 4 → Fin 3 → E) (a : Fin 4 → ℕ) (N : ℝ)
    (hU : ∀ i j, ‖U i j‖ ≤ (a i : ℝ)*N) :
    ‖∑ i, ∑ j, U i j‖ ≤ 3*((∑ i, a i : ℕ) : ℝ)*N := by
  calc
    ‖∑ i, ∑ j, U i j‖ ≤ ∑ i, ∑ j, ‖U i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 3, (a i : ℝ)*N :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hU i j))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_sum]
      rw [← Finset.mul_sum,← Finset.sum_mul]
      ring

theorem factorial_principal_multiplicity_norm_bound {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (α : Fin 4 → ℕ) (r : ℕ) (hA : (∑ i, α i) ≤ r)
    (U V : Fin 4 → Fin 3 → E) (N1 N2 : ℝ) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2)
    (hU : ∀ i j, ‖U i j‖ ≤ (α i : ℝ)*N1)
    (hV : ∀ i j, ‖V i j‖ ≤ ((α i*(α i-1) : ℕ) : ℝ)*N2) :
    ‖(2*c) • (∑ i, ∑ j, U i j)+c • (∑ i, ∑ j, V i j)‖ ≤
      6*|c| * (r : ℝ)*N1+3*|c| * ((r*(r-1) : ℕ) : ℝ)*N2 := by
  have hUn : ‖∑ i, ∑ j, U i j‖ ≤ 3*(r : ℝ)*N1 := by
    apply (factorial_fin4_fin3_norm_sum_le U α N1 hU).trans
    gcongr
  have hVn : ‖∑ i, ∑ j, V i j‖ ≤ 3*((r*(r-1) : ℕ) : ℝ)*N2 := by
    apply (factorial_fin4_fin3_norm_sum_le V (fun i => α i*(α i-1)) N2 hV).trans
    gcongr
    exact_mod_cast factorial_diagonal_pair_count_le α r hA
  calc
    _ ≤ ‖(2*c) • (∑ i, ∑ j, U i j)‖+‖c • (∑ i, ∑ j, V i j)‖ := norm_add_le _ _
    _ = 2*|c| * ‖∑ i, ∑ j, U i j‖+|c| * ‖∑ i, ∑ j, V i j‖ := by
      norm_num [norm_smul,Real.norm_eq_abs,abs_mul] <;> ring
    _ ≤ 2*|c| * (3*(r : ℝ)*N1)+|c| * (3*((r*(r-1) : ℕ) : ℝ)*N2) := by gcongr
    _ = _ := by ring

end TheoremT.Continuum.WeakGrushin
