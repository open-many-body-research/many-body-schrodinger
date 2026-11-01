import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Tactic

/-! A single summable binomial majorant bounds every translated series
coefficient, uniformly over a closed ball of translation vectors and over
all derivative orders. It is a convergent-series bound, not fixed-order
smooth compactness. No function or derivative identification is assumed. -/
noncomputable section
open scoped NNReal ENNReal
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def powerSeriesTranslationMajorant (p : FormalMultilinearSeries ℝ E F)
    (r s : ℝ≥0) : ℝ≥0 :=
  ∑' t : Σ k l : ℕ, {a : Finset (Fin (k+l)) // a.card=l},
    ‖p (t.1+t.2.1)‖₊ * r^t.2.1 * s^t.1

set_option maxHeartbeats 1200000 in
theorem powerSeries_changeOrigin_uniform_nnnorm
    (p : FormalMultilinearSeries ℝ E F) {r s : ℝ≥0}
    (hrs : (r+s : ℝ≥0∞) < p.radius) {x : E} (hx : ‖x‖₊ ≤ r) (k : ℕ) :
    ‖p.changeOrigin x k‖₊ * s^k ≤ powerSeriesTranslationMajorant p r s := by
  have hr : (r : ℝ≥0∞) < p.radius := (le_add_of_nonneg_right (by positivity)).trans_lt hrs
  have hxr : (‖x‖₊ : ℝ≥0∞) < p.radius := (ENNReal.coe_le_coe.mpr hx).trans_lt hr
  have hsum : Summable (fun t : Σ k l : ℕ, {a : Finset (Fin (k+l)) // a.card=l} =>
      ‖p (t.1+t.2.1)‖₊ * r^t.2.1 * s^t.1) :=
    p.changeOriginSeries_summable_aux₁ (r := r) (r' := s) hrs
  have hleft : Summable (fun t : Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l} =>
      ‖p (k+t.1)‖₊ * ‖x‖₊^t.1 * s^k) :=
    (p.changeOriginSeries_summable_aux₂ hxr k).mul_right (s^k)
  have hright : Summable (fun t : Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l} =>
      ‖p (k+t.1)‖₊ * r^t.1 * s^k) := (NNReal.summable_sigma.mp hsum).1 k
  let insertIndex : (Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l}) →
      (Σ k l : ℕ, {a : Finset (Fin (k+l)) // a.card=l}) := fun t => ⟨k,t⟩
  have hi : Function.Injective insertIndex := by
    intro a b hab
    exact eq_of_heq (Sigma.mk.inj_iff.mp hab).2
  calc
    ‖p.changeOrigin x k‖₊ * s^k ≤
        (∑' t : Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l},
          ‖p (k+t.1)‖₊ * ‖x‖₊^t.1) * s^k :=
      mul_le_mul_of_nonneg_right (p.nnnorm_changeOrigin_le k hxr) (by positivity)
    _ = ∑' t : Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l},
        ‖p (k+t.1)‖₊ * ‖x‖₊^t.1 * s^k := (NNReal.tsum_mul_right _ _).symm
    _ ≤ ∑' t : Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l},
        ‖p (k+t.1)‖₊ * r^t.1 * s^k := by
      apply hleft.tsum_le_tsum _ hright
      intro t
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left' hx t.1) (by positivity)) (by positivity)
    _ ≤ powerSeriesTranslationMajorant p r s := by
      simpa only [insertIndex,powerSeriesTranslationMajorant] using
        NNReal.tsum_comp_le_tsum_of_inj (i := insertIndex) hsum hi

theorem powerSeries_changeOrigin_uniform_norm
    (p : FormalMultilinearSeries ℝ E F) {r s : ℝ≥0}
    (hrs : (r+s : ℝ≥0∞) < p.radius) {x : E} (hx : ‖x‖₊ ≤ r) (k : ℕ) :
    ‖p.changeOrigin x k‖ * (s : ℝ)^k ≤ (powerSeriesTranslationMajorant p r s : ℝ) := by
  exact_mod_cast powerSeries_changeOrigin_uniform_nnnorm p hrs hx k

theorem powerSeries_changeOrigin_uniform_geometric_bound
    (p : FormalMultilinearSeries ℝ E F) {r s : ℝ≥0}
    (hs : 0 < s) (hrs : (r+s : ℝ≥0∞) < p.radius) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖₊ ≤ r → ∀ k : ℕ,
      ‖p.changeOrigin x k‖ ≤ C/(s : ℝ)^k := by
  refine ⟨(powerSeriesTranslationMajorant p r s : ℝ)+1,by positivity,?_⟩
  intro x hx k
  apply (le_div_iff₀ (pow_pos (show (0 : ℝ) < s from hs) k)).mpr
  exact (powerSeries_changeOrigin_uniform_norm p hrs hx k).trans (by linarith)

#print axioms powerSeries_changeOrigin_uniform_nnnorm
#print axioms powerSeries_changeOrigin_uniform_geometric_bound
end TheoremT.Continuum
