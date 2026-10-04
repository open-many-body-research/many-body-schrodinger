import ProductDirectionalWordLeibniz_v1
import FiniteLpTraceBounds_v1
import WeakGrushinPotentialForcingPointwise_v1
import Mathlib.Algebra.BigOperators.Fin

/-! A region L2 budget for the full finite directional-word product.
All split occurrences are retained, including equal words. The region need
not be bounded. Its solution words have actual L2 membership and integral
budgets; no weak derivative or pointwise solution bound is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
open WeakGrushin
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem directionalWordProduct_region_L2_bound {ι : Type} (dirs : ι → Y × T)
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ} (G : List ι → Y × T → ℂ)
    (hG : ∀ q, q.length ≤ m → MemLp (G q) 2 (volume.restrict Ω))
    (w : List ι) (hw : w.length ≤ m) {K W : ℝ}
    (hCoeff : ∀ q, q.length ≤ m → ∀ p ∈ Ω,
      |directionalWordDeriv dirs B q p| ≤ K)
    (hBudget : ∀ q, q.length ≤ m → (∫ p in Ω, ‖G q p‖^2) ≤ W) :
    MemLp (directionalWordProduct dirs B G w) 2 (volume.restrict Ω) ∧
    Integrable (fun p => ‖directionalWordProduct dirs B G w p‖^2)
      (volume.restrict Ω) ∧
    (∫ p in Ω, ‖directionalWordProduct dirs B G w p‖^2) ≤
      ((2 : ℝ)^w.length)^2*K^2*W := by
  let l := spectatorWordSplits w
  let term := fun ab : List ι × List ι => fun p : Y × T =>
    directionalWordDeriv dirs B ab.1 p • G ab.2 p
  have hterm (ab : List ι × List ι) (hab : ab ∈ l) :
      MemLp (term ab) 2 (volume.restrict Ω) := by
    have hn := spectatorWordSplits_length_sum hab
    have hc : MemLp (directionalWordDeriv dirs B ab.1) ⊤ (volume.restrict Ω) := by
      apply memLp_top_of_bound
        ((directionalWordDeriv_contDiffOn dirs hΩ hB ab.1).continuousOn.aestronglyMeasurable
          hΩ.measurableSet) K
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with p hp
      simpa only [Real.norm_eq_abs] using hCoeff ab.1 (by omega) p hp
    exact (hG ab.2 (by omega)).smul hc
  have hisq (i : Fin l.length) :
      Integrable (fun p => ‖term l[i.val] p‖^2) (volume.restrict Ω) :=
    (hterm l[i.val] (List.getElem_mem i.isLt)).integrable_norm_pow (by norm_num)
  have hsumId (p : Y × T) :
      (∑ i : Fin l.length, term l[i.val] p) = directionalWordProduct dirs B G w p := by
    exact Fin.sum_univ_fun_getElem l (fun ab => term ab p)
  have hprod : MemLp (directionalWordProduct dirs B G w) 2 (volume.restrict Ω) := by
    have hs := memLp_finsetSum Finset.univ
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin l.length))) =>
        hterm l[i.val] (List.getElem_mem i.isLt))
    simpa only [hsumId] using hs
  have hprodsq := hprod.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  refine ⟨hprod,hprodsq,?_⟩
  have htermBound (ab : List ι × List ι) (hab : ab ∈ l) :
      (∫ p in Ω, ‖term ab p‖^2) ≤ K^2*W := by
    have hn := spectatorWordSplits_length_sum hab
    have hg := hG ab.2 (by omega)
    have hgsq : Integrable (fun p => ‖G ab.2 p‖^2) (volume.restrict Ω) :=
      hg.integrable_norm_pow (by norm_num)
    calc
      _ ≤ ∫ p in Ω, K^2*‖G ab.2 p‖^2 := by
        apply integral_mono_ae ((hterm ab hab).integrable_norm_pow (by norm_num))
          (hgsq.const_mul (K^2))
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with p hp
        exact potential_smul_norm_sq_le (G ab.2 p) (hCoeff ab.1 (by omega) p hp)
      _ = K^2*(∫ p in Ω, ‖G ab.2 p‖^2) := integral_const_mul _ _
      _ ≤ K^2*W := mul_le_mul_of_nonneg_left (hBudget ab.2 (by omega)) (sq_nonneg K)
  have hpoint (p : Y × T) :
      ‖directionalWordProduct dirs B G w p‖^2 ≤
        (l.length : ℝ)*(∑ i : Fin l.length, ‖term l[i.val] p‖^2) := by
    have hh := finite_sum_norm_sq_le_card_sum_norm_sq
      (fun i : Fin l.length => term l[i.val] p)
    simpa only [hsumId,Fintype.card_fin] using hh
  have hsumInt : Integrable (fun p => ∑ i : Fin l.length, ‖term l[i.val] p‖^2)
      (volume.restrict Ω) := integrable_finsetSum _ (fun i _ => hisq i)
  have hsumBound : (∑ i : Fin l.length, ∫ p in Ω, ‖term l[i.val] p‖^2) ≤
      (l.length : ℝ)*(K^2*W) := by
    calc
      _ ≤ ∑ _i : Fin l.length, K^2*W :=
        Finset.sum_le_sum (fun i _ => htermBound l[i.val] (List.getElem_mem i.isLt))
      _ = _ := by simp
  have hlen : l.length = 2^w.length := spectatorWordSplits_length w
  calc
    _ ≤ ∫ p in Ω, (l.length : ℝ)*(∑ i : Fin l.length, ‖term l[i.val] p‖^2) :=
      integral_mono_ae hprodsq (hsumInt.const_mul (l.length : ℝ))
        (Filter.Eventually.of_forall hpoint)
    _ = (l.length : ℝ)*(∑ i : Fin l.length, ∫ p in Ω, ‖term l[i.val] p‖^2) := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hisq i)]
    _ ≤ (l.length : ℝ)*((l.length : ℝ)*(K^2*W)) :=
      mul_le_mul_of_nonneg_left hsumBound (Nat.cast_nonneg _)
    _ = _ := by rw [hlen]; push_cast; ring

end TheoremT.Continuum
