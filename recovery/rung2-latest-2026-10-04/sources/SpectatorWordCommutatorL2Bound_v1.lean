import SpectatorWordWeakLeibniz_v1
import FiniteLpTraceBounds_v1
import WeakGrushinPotentialForcingPointwise_v1
import Mathlib.Algebra.BigOperators.Fin

/-! Compact L2 bounds for the exact finite spectator commutator. Every
proper split occurrence is retained, including duplicates. Coefficients
have a common pointwise budget; solution words have only an integral budget.
No pointwise bound on any solution derivative is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spectatorWordCommutator_integrable_norm_sq
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ} (G : List κ → Space κ → ℂ)
    (hG : ∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω)
    {S : Set (Space κ)} (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (w : List κ) (hw : w.length ≤ m) :
    Integrable (fun p => ‖spectatorWordCommutator B G w p‖^2) (volume.restrict S) :=
  (spectatorWordCommutator_locallyL2 hΩ hB G hG w hw S hS hSΩ).integrable_norm_pow
    (by norm_num)

theorem spectatorWordCommutator_integral_norm_sq_le
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ} (G : List κ → Space κ → ℂ)
    (hG : ∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω)
    {S : Set (Space κ)} (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (w : List κ) (hw : w.length ≤ m)
    {K W : ℝ} (_hK : 0 ≤ K) (_hW : 0 ≤ W)
    (hCoeff : ∀ ab ∈ spectatorWordProperSplits w, ∀ p ∈ S,
      |spectatorWordDeriv B ab.1 p| ≤ K)
    (hBudget : ∀ ab ∈ spectatorWordProperSplits w,
      (∫ p in S, ‖G ab.2 p‖^2) ≤ W) :
    (∫ p in S, ‖spectatorWordCommutator B G w p‖^2) ≤
      (((2^w.length-1 : ℕ) : ℝ)^2)*K^2*W := by
  let l := spectatorWordProperSplits w
  let term := fun ab : List κ × List κ => fun p : Space κ =>
    spectatorWordDeriv B ab.1 p • G ab.2 p
  have hterm (ab : List κ × List κ) (hab : ab ∈ l) :
      MemLp (term ab) 2 (volume.restrict S) := by
    have hn := spectatorWordProperSplits_strict hab
    exact product_smooth_coefficient_locallyL2_raw hΩ
      (spectatorWordDeriv_contDiffOn hΩ hB ab.1)
      (hG ab.2 (by omega)) S hS hSΩ
  have hisq (i : Fin l.length) :
      Integrable (fun p => ‖term l[i.val] p‖^2) (volume.restrict S) :=
    (hterm l[i.val] (List.getElem_mem i.isLt)).integrable_norm_pow (by norm_num)
  have htermBound (ab : List κ × List κ) (hab : ab ∈ l) :
      (∫ p in S, ‖term ab p‖^2) ≤ K^2*W := by
    have hn := spectatorWordProperSplits_strict hab
    have hg : MemLp (G ab.2) 2 (volume.restrict S) :=
      hG ab.2 (by omega) S hS hSΩ
    have hgsq : Integrable (fun p => ‖G ab.2 p‖^2) (volume.restrict S) :=
      hg.integrable_norm_pow (by norm_num)
    calc
      _ ≤ ∫ p in S, K^2*‖G ab.2 p‖^2 := by
        apply integral_mono_ae ((hterm ab hab).integrable_norm_pow (by norm_num))
          (hgsq.const_mul (K^2))
        filter_upwards [ae_restrict_mem hS.measurableSet] with p hp
        exact potential_smul_norm_sq_le (G ab.2 p) (hCoeff ab hab p hp)
      _ = K^2*(∫ p in S, ‖G ab.2 p‖^2) := integral_const_mul _ _
      _ ≤ K^2*W := mul_le_mul_of_nonneg_left (hBudget ab hab) (sq_nonneg K)
  have hsumId (p : Space κ) :
      (∑ i : Fin l.length, term l[i.val] p) = spectatorWordCommutator B G w p := by
    exact Fin.sum_univ_fun_getElem l (fun ab => term ab p)
  have hpoint (p : Space κ) :
      ‖spectatorWordCommutator B G w p‖^2 ≤
        (l.length : ℝ)*(∑ i : Fin l.length, ‖term l[i.val] p‖^2) := by
    have hh := finite_sum_norm_sq_le_card_sum_norm_sq
      (fun i : Fin l.length => term l[i.val] p)
    simpa only [hsumId, Fintype.card_fin] using hh
  have hcomm := spectatorWordCommutator_integrable_norm_sq hΩ hB G hG hS hSΩ w hw
  have hsumInt : Integrable (fun p => ∑ i : Fin l.length, ‖term l[i.val] p‖^2)
      (volume.restrict S) := integrable_finsetSum _ (fun i _ => hisq i)
  have hsumBound : (∑ i : Fin l.length, ∫ p in S, ‖term l[i.val] p‖^2) ≤
      (l.length : ℝ)*(K^2*W) := by
    calc
      _ ≤ ∑ _i : Fin l.length, K^2*W :=
        Finset.sum_le_sum (fun i _ => htermBound l[i.val] (List.getElem_mem i.isLt))
      _ = _ := by simp
  have hlen : l.length = 2^w.length-1 := by
    have hh := spectatorWordProperSplits_length w
    change l.length + 1 = 2^w.length at hh
    omega
  calc
    _ ≤ ∫ p in S, (l.length : ℝ)*(∑ i : Fin l.length, ‖term l[i.val] p‖^2) :=
      integral_mono_ae hcomm (hsumInt.const_mul (l.length : ℝ))
        (Filter.Eventually.of_forall hpoint)
    _ = (l.length : ℝ)*(∑ i : Fin l.length, ∫ p in S, ‖term l[i.val] p‖^2) := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hisq i)]
    _ ≤ (l.length : ℝ)*((l.length : ℝ)*(K^2*W)) :=
      mul_le_mul_of_nonneg_left hsumBound (Nat.cast_nonneg _)
    _ = _ := by rw [hlen]; ring

#print axioms spectatorWordCommutator_integrable_norm_sq
#print axioms spectatorWordCommutator_integral_norm_sq_le
end TheoremT.Continuum.WeakGrushin
