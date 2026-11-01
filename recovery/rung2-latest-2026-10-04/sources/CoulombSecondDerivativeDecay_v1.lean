import ExponentialSecondDerivativeNorm_v1
import L2FatouBound_v1

/-! Actual mixed weak second derivative exponential decay at the same exponent
as the supplied physical eigenfunction L² decay, for every finite N. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem scalar_eigen_second_derivative_exponential_decay
    {N : ℕ} {Z E a : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (ha : 0 ≤ a) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume)
    (k l : Coordinate N) :
    MemLp (fun x => Real.exp (a*‖x‖) • e k l x) 2 volume := by
  have hsw := smooth_exponential_memLp_of_physical ha f hw
  obtain ⟨C,hC,hbound⟩ := scalar_eigen_exponential_second_derivative_uniform_bound hg d e hd he ha hsw
  have hpos (n : ℕ) : 0 < (n : ℝ)+1 := by positivity
  let U (n : ℕ) : SpatialL2 N := boundedRealMul (boundedExpWeight N a ((n : ℝ)+1))
    (boundedExpWeight_memLp_top N a (hpos n)) (e k l)
  have hrep : ∀ᵐ x, ∀ n : ℕ, U n x = boundedExpWeight N a ((n : ℝ)+1) x • e k l x := by
    rw [ae_all_iff]
    intro n
    exact boundedRealMul_ae _ _ _
  have ht : ∀ᵐ x, Tendsto (fun n : ℕ => U n x) atTop
      (𝓝 (Real.exp (a*smoothConfigurationRadius N x) • e k l x)) := by
    filter_upwards [hrep] with x hx
    exact ((boundedExpWeight_tendsto N a x).smul_const (e k l x)).congr'
      (Eventually.of_forall (fun n => (hx n).symm))
  obtain ⟨hm,_⟩ := memLp_of_ae_tendsto_L2_bounded U _ hC
    (fun n => hbound _ (hpos n) k l) ht
  exact physical_exponential_memLp_of_smooth ha (e k l) hm

#print axioms scalar_eigen_second_derivative_exponential_decay
end TheoremT.Continuum
