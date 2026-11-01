import ExponentialDerivativeNorm_v1
import L2FatouBound_v1

/-! Exponential L² decay passes to every actual weak first derivative of a
scalar Coulomb eigenfunction, at the same exponent, for arbitrary finite N.
No coordinatewise classical differentiability premise is introduced. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem scalar_eigen_first_derivative_exponential_decay
    {N : ℕ} {Z E a : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k)
    (ha : 0 ≤ a) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume)
    (k : Coordinate N) :
    MemLp (fun x => Real.exp (a*‖x‖) • d k x) 2 volume := by
  have hsw := smooth_exponential_memLp_of_physical ha f hw
  obtain ⟨C,hC,hbound⟩ := scalar_eigen_exponential_derivative_uniform_bound hg d hd ha hsw
  have hpos (n : ℕ) : 0 < (n : ℝ)+1 := by positivity
  let U (n : ℕ) : SpatialL2 N := boundedRealMul (boundedExpWeight N a ((n : ℝ)+1))
    (boundedExpWeight_memLp_top N a (hpos n)) (d k)
  have hrep : ∀ᵐ x, ∀ n : ℕ, U n x = boundedExpWeight N a ((n : ℝ)+1) x • d k x := by
    rw [ae_all_iff]
    intro n
    exact boundedRealMul_ae _ _ _
  have ht : ∀ᵐ x, Tendsto (fun n : ℕ => U n x) atTop
      (𝓝 (Real.exp (a*smoothConfigurationRadius N x) • d k x)) := by
    filter_upwards [hrep] with x hx
    exact ((boundedExpWeight_tendsto N a x).smul_const (d k x)).congr'
      (Eventually.of_forall (fun n => (hx n).symm))
  obtain ⟨hm,_⟩ := memLp_of_ae_tendsto_L2_bounded U _ hC
    (fun n => hbound _ (hpos n) k) ht
  exact physical_exponential_memLp_of_smooth ha (d k) hm

#print axioms scalar_eigen_first_derivative_exponential_decay
end TheoremT.Continuum
