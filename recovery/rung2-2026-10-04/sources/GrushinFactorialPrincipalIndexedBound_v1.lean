import GrushinFactorialPrincipalWeightedTerm_v1
import GrushinFactorialPrincipalMultiplicity_v1

/-! The exact indexed functional R15 estimate with actual L2 output.
The raw expression is displayed in full. Its identification as an operator
commutator requires the separately proved genuine derivative identities. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

def factorialPrincipalRawError (c : ℝ) (d : FactorialRawJetFamily)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (p : Space (Fin 3)) : ℂ :=
  (2*c) • (∑ i : Fin 4, ∑ j : Fin 3, (α i : ℝ) • (p.1 i •
    d (fun l => α l-(Pi.single i 1 : Fin 4 → ℕ) l) (β+Pi.single j 2) p))+
  c • (∑ i : Fin 4, ∑ j : Fin 3, ((α i*(α i-1) : ℕ) : ℝ) •
    d (fun l => α l-(Pi.single i 2 : Fin 4 → ℕ) l) (β+Pi.single j 2) p)

theorem factorialOuterNorm_nonneg {E : Type*} [SeminormedAddCommGroup E]
    (F : FactorialOuterIndex → E) : 0 ≤ factorialOuterNorm F :=
  Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem lp_double_sum_ae {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    {μ : Measure X} (U : ι → κ → Lp ℂ 2 μ) (f : ι → κ → X → ℂ)
    (h : ∀ i j, U i j =ᵐ[μ] f i j) :
    (∑ i, ∑ j, U i j) =ᵐ[μ] (fun p => ∑ i, ∑ j, f i j p) := by
  have hin (i : ι) : (∑ j, U i j) =ᵐ[μ] (fun p => ∑ j, f i j p) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (U i),ae_all_iff.mpr (h i)] with p hp hq
    simp only [Finset.sum_apply] at hp
    rw [hp]
    exact Finset.sum_congr rfl (fun j _ => hq j)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => ∑ j, U i j),ae_all_iff.mpr hin] with p hp hq
  simp only [Finset.sum_apply] at hp
  rw [hp]
  exact Finset.sum_congr rfl (fun i _ => hq i)

theorem factorial_principal_indexed_error_L2
    {μ : Measure (Space (Fin 3))} (c : ℝ) (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N1 N2 : ℝ)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep d W a b)
    (hN1 : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → factorialOuterNorm (W a b) ≤ N1)
    (hN2 : ∀ a b, factorialMultiDerivativeCost a b ≤ r-2 → factorialOuterNorm (W a b) ≤ N2)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r) :
    ∃ H : Lp ℂ 2 μ, H =ᵐ[μ] factorialPrincipalRawError c d α β ∧
      ‖H‖ ≤ 6*|c| * (r : ℝ)*N1+3*|c| * ((r*(r-1) : ℕ) : ℝ)*N2 := by
  have hW2 : ∀ a b, factorialMultiDerivativeCost a b ≤ r-2 →
      FactorialShiftedOuterL2Rep d W a b := by
    intro a b h
    exact hW a b (by omega)
  have hzero (k : ℕ) : factorialMultiDerivativeCost 0 0 ≤ k := by
    simp [factorialMultiDerivativeCost,factorialDerivativeCost]
  have hN10 : 0 ≤ N1 := (factorialOuterNorm_nonneg _).trans (hN1 0 0 (hzero _))
  have hN20 : 0 ≤ N2 := (factorialOuterNorm_nonneg _).trans (hN2 0 0 (hzero _))
  choose U hU hUn using fun i : Fin 4 => fun j : Fin 3 =>
    factorial_principal_one_hit_weighted_L2 d W r N1 hW hN1 α β hc i j
  choose V hV hVn using fun i : Fin 4 => fun j : Fin 3 =>
    factorial_principal_two_hit_weighted_L2 d W r N2 hW2 hN2 α β hc i j
  let US : Lp ℂ 2 μ := ∑ i, ∑ j, U i j
  let VS : Lp ℂ 2 μ := ∑ i, ∑ j, V i j
  have hUS := lp_double_sum_ae U _ hU
  have hVS := lp_double_sum_ae V _ hV
  have hA : (∑ i, α i) ≤ r := by
    have ht := factorialDerivativeCost_total_le (∑ i, α i) (∑ j, β j)
    unfold factorialMultiDerivativeCost at hc
    omega
  refine ⟨(2*c) • US+c • VS,?_,
    factorial_principal_multiplicity_norm_bound c α r hA U V N1 N2 hN10 hN20 hUn hVn⟩
  filter_upwards [Lp.coeFn_add ((2*c) • US) (c • VS),Lp.coeFn_smul (2*c) US,
    Lp.coeFn_smul c VS,hUS,hVS] with p hadd hu hv hsumU hsumV
  rw [hadd]
  change ((2*c) • US) p+(c • VS) p = _
  rw [hu,hv]
  change (2*c) • US p+c • VS p = _
  rw [hsumU,hsumV]
  rfl

end TheoremT.Continuum.WeakGrushin
