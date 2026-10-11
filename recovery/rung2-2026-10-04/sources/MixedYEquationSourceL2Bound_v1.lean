import MixedYEquationSource_v1
import MixedPotentialWordL2Bound_v1

/-! Integral budgets for the actual negative Y-Laplacian source. The two
spectator orders in its last term are charged to the triangular reserve.
Coefficient budgets are pointwise; solution and source budgets are L2
integral bounds. All integrability is established before integral comparison.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem complex_finite_family_L2_bound {X I : Type*} [MeasurableSpace X]
    [Fintype I] {μ : Measure X} (f : I → X → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (W : I → ℝ)
    (hBudget : ∀ i, (∫ p, ‖f i p‖^2 ∂μ) ≤ W i) :
    MemLp (fun p => ∑ i, f i p) 2 μ ∧
    Integrable (fun p => ‖∑ i, f i p‖^2) μ ∧
    (∫ p, ‖∑ i, f i p‖^2 ∂μ) ≤ (Fintype.card I : ℝ)*(∑ i, W i) := by
  have hm : MemLp (fun p => ∑ i, f i p) 2 μ :=
    memLp_finsetSum _ (fun i _ => hf i)
  have hsq := hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hisq (i : I) : Integrable (fun p => ‖f i p‖^2) μ :=
    (hf i).integrable_norm_pow (by norm_num)
  have hsint : Integrable (fun p => ∑ i, ‖f i p‖^2) μ :=
    integrable_finsetSum _ (fun i _ => hisq i)
  refine ⟨hm,hsq,?_⟩
  calc
    _ ≤ ∫ p, (Fintype.card I : ℝ)*(∑ i, ‖f i p‖^2) ∂μ :=
      integral_mono_ae hsq (hsint.const_mul (Fintype.card I : ℝ))
        (Filter.Eventually.of_forall (fun p => finite_sum_norm_sq_le_card_sum_norm_sq (fun i => f i p)))
    _ = (Fintype.card I : ℝ)*(∑ i, ∫ p, ‖f i p‖^2 ∂μ) := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hisq i)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hBudget i))
      (Nat.cast_nonneg _)

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem mixedYEquationSource_region_L2_bound
    (c : ℝ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {r m : ℕ}
    (F S : List (Fin 4) → List κ → Space κ → ℂ)
    (hF : ∀ a b, a.length ≤ r → a.length+b.length ≤ m →
      MemLp (F a b) 2 (volume.restrict Ω))
    (a : List (Fin 4)) (b : List κ) (ha : a.length ≤ r)
    (hab : a.length+b.length+2 ≤ m)
    (hS : MemLp (S a b) 2 (volume.restrict Ω)) {K Q W H : ℝ}
    (hCoeff : ∀ ya tb, ya.length ≤ a.length → tb.length ≤ b.length → ∀ p ∈ Ω,
      |directionalWordDeriv yDir (spectatorWordDeriv B tb) ya p| ≤ K)
    (hQuad : ∀ ya, ya.length ≤ a.length → ∀ p ∈ Ω,
      |directionalWordDeriv yDir (fun p : Space κ => ‖p.1‖^2) ya p| ≤ Q)
    (hBudget : ∀ ya tb, ya.length ≤ r → ya.length+tb.length ≤ m →
      (∫ p in Ω, ‖F ya tb p‖^2) ≤ W)
    (hSource : (∫ p in Ω, ‖S a b p‖^2) ≤ H) :
    MemLp (mixedYEquationSource c B F S a b) 2 (volume.restrict Ω) ∧
    Integrable (fun p => ‖mixedYEquationSource c B F S a b p‖^2)
      (volume.restrict Ω) ∧
    (∫ p in Ω, ‖mixedYEquationSource c B F S a b p‖^2) ≤
      3*H + 3*((2 : ℝ)^(a.length+b.length))^2*K^2*W +
        3*c^2*((2 : ℝ)^a.length)^2*(Fintype.card κ : ℝ)^2*Q^2*W := by
  let T := fun q p => ∑ j : κ, F q (j :: j :: b) p
  have hT (q : List (Fin 4)) (hq : q.length ≤ a.length) :
      MemLp (T q) 2 (volume.restrict Ω) ∧
      Integrable (fun p => ‖T q p‖^2) (volume.restrict Ω) ∧
      (∫ p in Ω, ‖T q p‖^2) ≤ (Fintype.card κ : ℝ)^2*W := by
    have hh := complex_finite_family_L2_bound (fun j : κ => F q (j :: j :: b))
      (fun j => hF q (j :: j :: b) (by omega) (by simp only [List.length_cons]; omega))
      (fun _ => W)
      (fun j => hBudget q (j :: j :: b) (by omega) (by simp only [List.length_cons]; omega))
    refine ⟨hh.1,hh.2.1,hh.2.2.trans_eq ?_⟩
    simp
    ring
  let P := mixedPotentialWordProduct B F a b
  let U := directionalWordProduct yDir (fun p : Space κ => ‖p.1‖^2) T a
  have hP := mixedPotentialWordProduct_region_L2_bound hΩ hB F hF a b ha (by omega)
    hCoeff hBudget
  have hU := directionalWordProduct_region_L2_bound yDir hΩ
    (((contDiff_norm_sq ℝ).comp contDiff_fst).contDiffOn) T
    (m := a.length) (fun q hq => (hT q hq).1) a le_rfl hQuad
    (fun q hq => (hT q hq).2.2)
  have hcU : MemLp (fun p => c • U p) 2 (volume.restrict Ω) := hU.1.const_smul c
  have hcUb : (∫ p in Ω, ‖c • U p‖^2) ≤
      c^2*(((2 : ℝ)^a.length)^2*Q^2*((Fintype.card κ : ℝ)^2*W)) := by
    calc
      _ = c^2*(∫ p in Ω, ‖U p‖^2) := by
        simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
        exact integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hU.2.2 (sq_nonneg c)
  let terms : Fin 3 → Space κ → ℂ := ![S a b,fun p => -P p,fun p => c • U p]
  let bounds : Fin 3 → ℝ := ![H,((2 : ℝ)^(a.length+b.length))^2*K^2*W,
    c^2*(((2 : ℝ)^a.length)^2*Q^2*((Fintype.card κ : ℝ)^2*W))]
  have hterms (i : Fin 3) : MemLp (terms i) 2 (volume.restrict Ω) := by
    fin_cases i
    · exact hS
    · exact hP.1.neg
    · exact hcU
  have hbounds (i : Fin 3) : (∫ p in Ω, ‖terms i p‖^2) ≤ bounds i := by
    fin_cases i
    · exact hSource
    · change (∫ p in Ω, ‖-P p‖^2) ≤ ((2 : ℝ)^(a.length+b.length))^2*K^2*W
      simpa only [norm_neg] using hP.2.2
    · exact hcUb
  have hsum := complex_finite_family_L2_bound terms hterms bounds hbounds
  have hsumId (p : Space κ) : (∑ i, terms i p) = mixedYEquationSource c B F S a b p := by
    simp [terms,Fin.sum_univ_succ,mixedYEquationSource,P,U,T,sub_eq_add_neg,add_assoc]
  have hm : MemLp (mixedYEquationSource c B F S a b) 2 (volume.restrict Ω) := by
    simpa only [hsumId] using hsum.1
  have hsq : Integrable (fun p => ‖mixedYEquationSource c B F S a b p‖^2)
      (volume.restrict Ω) := by simpa only [hsumId] using hsum.2.1
  refine ⟨hm,hsq,?_⟩
  have hbnd := hsum.2.2
  simp only [hsumId] at hbnd
  refine hbnd.trans_eq ?_
  simp [bounds,Fin.sum_univ_succ]
  ring

theorem mixedYEquationSource_budget_le_uniform
    (a : List (Fin 4)) (b : List κ) {m : ℕ}
    (hab : a.length+b.length+2 ≤ m) (c K Q W H : ℝ) (hW : 0 ≤ W) :
    3*H + 3*((2 : ℝ)^(a.length+b.length))^2*K^2*W +
        3*c^2*((2 : ℝ)^a.length)^2*(Fintype.card κ : ℝ)^2*Q^2*W ≤
      3*H + 3*((2 : ℝ)^m)^2*(K^2+c^2*(Fintype.card κ : ℝ)^2*Q^2)*W := by
  have hpab : ((2 : ℝ)^(a.length+b.length))^2 ≤ ((2 : ℝ)^m)^2 :=
    pow_le_pow_left₀ (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) 2
  have hpa : ((2 : ℝ)^a.length)^2 ≤ ((2 : ℝ)^m)^2 :=
    pow_le_pow_left₀ (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) 2
  have h1 := mul_le_mul_of_nonneg_right hpab (show 0 ≤ 3*K^2*W by positivity)
  have h2 := mul_le_mul_of_nonneg_right hpa
    (show 0 ≤ 3*c^2*(Fintype.card κ : ℝ)^2*Q^2*W by positivity)
  nlinarith

end TheoremT.Continuum.WeakGrushin
