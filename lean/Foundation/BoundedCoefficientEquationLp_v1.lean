import CompactLocalMultiplierLp_v1
import CoulombCuspGradientBound_v1

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace TheoremT.Continuum

theorem bounded_coefficient_equation_rhs_memLp {N : ℕ} {q : ℝ≥0∞}
    {μ : Measure (Configuration N)} {β : Coordinate N → Configuration N → ℝ}
    {c : Configuration N → ℝ} (hβ : ∀ k, MemLp (β k) ⊤ μ) (hc : MemLp c ⊤ μ)
    {f : Configuration N → ℂ} {d : Coordinate N → Configuration N → ℂ}
    (hf : MemLp f q μ) (hd : ∀ k, MemLp (d k) q μ) :
    MemLp (fun x => -2*(∑ k, (β k x : ℂ)*d k x)-(c x : ℂ)*f x) q μ := by
  have hD (k : Coordinate N) : MemLp (fun x => (β k x : ℂ)*d k x) q μ := by
    have hm : MemLp (fun x => β k x • d k x) q μ := (hd k).smul (hβ k)
    simpa only [Complex.real_smul] using hm
  have hF : MemLp (fun x => (c x : ℂ)*f x) q μ := by
    have hm : MemLp (fun x => c x • f x) q μ := hf.smul hc
    simpa only [Complex.real_smul] using hm
  exact ((memLp_finsetSum Finset.univ (fun k hk => hD k)).const_mul (-2)).sub hF

theorem coulombCuspGradient_measurable (N : ℕ) (Z : ℝ) (v : Configuration N) :
    Measurable (coulombCuspGradient N Z v) := by
  unfold coulombCuspGradient linearRadiusGradient
  fun_prop

theorem coulombCuspGradient_memLp_top (N : ℕ) (Z : ℝ) (v : Configuration N) :
    MemLp (coulombCuspGradient N Z v) ⊤ volume := by
  apply memLp_top_of_bound (coulombCuspGradient_measurable N Z v).aestronglyMeasurable
    (cuspDirectionalBound N Z v)
  filter_upwards with x
  exact coulombCuspGradient_abs_bound N Z v x

theorem coulombCusp_zero_order_memLp_top (N : ℕ) (Z E : ℝ) :
    MemLp (fun x => (∑ k : Coordinate N, (coulombCuspGradient N Z (coordinateVector k) x)^2)+2*E)
      ⊤ volume := by
  have hm : Measurable (fun x => (∑ k : Coordinate N, (coulombCuspGradient N Z (coordinateVector k) x)^2)+2*E) := by
    have hβ := fun k => coulombCuspGradient_measurable N Z (coordinateVector k)
    fun_prop
  apply memLp_top_of_bound hm.aestronglyMeasurable (cuspCoordinateGradientSquareBound N Z+2*|E|)
  filter_upwards with x
  exact coulombCusp_zero_order_coefficient_bound N Z E x

#print axioms bounded_coefficient_equation_rhs_memLp
#print axioms coulombCusp_zero_order_memLp_top
end TheoremT.Continuum
