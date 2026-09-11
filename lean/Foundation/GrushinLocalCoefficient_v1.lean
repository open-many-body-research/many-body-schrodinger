import GrushinTestSupport_v1
import SmoothLocalTestProduct_v1

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  {ι : Type*} [Fintype ι]

theorem splitGrushin_coefficient_congr (c : ℝ) (v : ι → S)
    {B C φ : KSSpace × S → ℝ} (h : ∀ q ∈ tsupport φ, B q=C q) :
    splitGrushin c v B φ=splitGrushin c v C φ := by
  funext q
  by_cases hq : q ∈ tsupport φ
  · simp only [splitGrushin,h q hq]
  · have hz := image_eq_zero_of_notMem_tsupport hq
    simp only [splitGrushin,hz,mul_zero]

theorem splitGrushin_continuous_local_coefficient (c : ℝ) (v : ι → S)
    {B φ : KSSpace × S → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hB : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ B q) :
    Continuous (splitGrushin c v B φ) := by
  have h0 := splitGrushin_continuous c v (B := fun _ => 0) continuous_const hφ
  have hP := (smooth_mul_of_smooth_on_tsupport hφ hB).continuous
  have he : splitGrushin c v B φ = fun q => splitGrushin c v (fun _ => 0) φ q + φ q*B q := by
    funext q
    simp only [splitGrushin,zero_mul,add_zero]
    ring
  rw [he]
  exact h0.add hP

#print axioms splitGrushin_coefficient_congr
#print axioms splitGrushin_continuous_local_coefficient
end TheoremT.Continuum
