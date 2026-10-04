import MixedPotentialWordProduct_v1
import ProductDirectionalWordL2Bound_v1

/-! Region budgets for the mixed coefficient product. Each Y/T split
occurrence remains present, and every solution word stays in the supplied
triangular order range. No equation or derivative relation is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem complex_list_L2_bound {X I : Type*} [MeasurableSpace X] {μ : Measure X}
    (l : List I) (f : I → X → ℂ)
    (hf : ∀ i ∈ l, MemLp (f i) 2 μ) {W : ℝ}
    (hBudget : ∀ i ∈ l, (∫ p, ‖f i p‖^2 ∂μ) ≤ W) :
    MemLp (fun p => (l.map (fun i => f i p)).sum) 2 μ ∧
    Integrable (fun p => ‖(l.map (fun i => f i p)).sum‖^2) μ ∧
    (∫ p, ‖(l.map (fun i => f i p)).sum‖^2 ∂μ) ≤ (l.length : ℝ)^2*W := by
  have hsumId (p : X) : (∑ i : Fin l.length, f l[i.val] p) =
      (l.map (fun i => f i p)).sum := Fin.sum_univ_fun_getElem l (fun i => f i p)
  have hm : MemLp (fun p => (l.map (fun i => f i p)).sum) 2 μ := by
    have hs := memLp_finsetSum Finset.univ
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin l.length))) =>
        hf l[i.val] (List.getElem_mem i.isLt))
    simpa only [hsumId] using hs
  have hsq := hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hisq (i : Fin l.length) : Integrable (fun p => ‖f l[i.val] p‖^2) μ :=
    (hf l[i.val] (List.getElem_mem i.isLt)).integrable_norm_pow (by norm_num)
  have hsint : Integrable (fun p => ∑ i : Fin l.length, ‖f l[i.val] p‖^2) μ :=
    integrable_finsetSum _ (fun i _ => hisq i)
  refine ⟨hm,hsq,?_⟩
  calc
    _ ≤ ∫ p, (l.length : ℝ)*(∑ i : Fin l.length, ‖f l[i.val] p‖^2) ∂μ := by
      apply integral_mono_ae hsq (hsint.const_mul (l.length : ℝ))
      exact Filter.Eventually.of_forall (fun p => by
        simpa only [hsumId,Fintype.card_fin] using
          finite_sum_norm_sq_le_card_sum_norm_sq (fun i : Fin l.length => f l[i.val] p))
    _ = (l.length : ℝ)*(∑ i : Fin l.length, ∫ p, ‖f l[i.val] p‖^2 ∂μ) := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hisq i)]
    _ ≤ (l.length : ℝ)*(∑ _i : Fin l.length, W) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => hBudget l[i.val] (List.getElem_mem i.isLt)))
        (Nat.cast_nonneg _)
    _ = _ := by simp; ring

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem mixedPotentialWordProduct_region_L2_bound
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {r m : ℕ}
    (F : List (Fin 4) → List κ → Space κ → ℂ)
    (hF : ∀ a b, a.length ≤ r → a.length+b.length ≤ m →
      MemLp (F a b) 2 (volume.restrict Ω))
    (a : List (Fin 4)) (b : List κ) (ha : a.length ≤ r)
    (hab : a.length+b.length ≤ m) {K W : ℝ}
    (hCoeff : ∀ ya tb, ya.length ≤ a.length → tb.length ≤ b.length → ∀ p ∈ Ω,
      |directionalWordDeriv yDir (spectatorWordDeriv B tb) ya p| ≤ K)
    (hBudget : ∀ ya tb, ya.length ≤ r → ya.length+tb.length ≤ m →
      (∫ p in Ω, ‖F ya tb p‖^2) ≤ W) :
    MemLp (mixedPotentialWordProduct B F a b) 2 (volume.restrict Ω) ∧
    Integrable (fun p => ‖mixedPotentialWordProduct B F a b p‖^2)
      (volume.restrict Ω) ∧
    (∫ p in Ω, ‖mixedPotentialWordProduct B F a b p‖^2) ≤
      ((2 : ℝ)^(a.length+b.length))^2*K^2*W := by
  let l := spectatorWordSplits b
  let term := fun bc : List κ × List κ =>
    directionalWordProduct yDir (spectatorWordDeriv B bc.1) (fun q => F q bc.2) a
  have hterm (bc : List κ × List κ) (hbc : bc ∈ l) :
      MemLp (term bc) 2 (volume.restrict Ω) ∧
      Integrable (fun p => ‖term bc p‖^2) (volume.restrict Ω) ∧
      (∫ p in Ω, ‖term bc p‖^2) ≤ ((2 : ℝ)^a.length)^2*K^2*W := by
    have hn := spectatorWordSplits_length_sum hbc
    apply directionalWordProduct_region_L2_bound yDir hΩ
      (spectatorWordDeriv_contDiffOn hΩ hB bc.1) (fun q => F q bc.2)
      (m := a.length) (fun q hq => hF q bc.2 (by omega) (by omega)) a le_rfl
    · intro q hq p hp
      exact hCoeff q bc.1 hq (by omega) p hp
    · intro q hq
      exact hBudget q bc.2 (by omega) (by omega)
  have hs := complex_list_L2_bound l term (fun bc hbc => (hterm bc hbc).1)
    (fun bc hbc => (hterm bc hbc).2.2)
  refine ⟨hs.1,hs.2.1,hs.2.2.trans_eq ?_⟩
  change (l.length : ℝ)^2*(((2 : ℝ)^a.length)^2*K^2*W) = _
  have hlen : l.length = 2^b.length := spectatorWordSplits_length b
  rw [hlen]
  push_cast
  rw [pow_add]
  ring

end TheoremT.Continuum.WeakGrushin
