import ExteriorExponentialNorm_v1
import L2FatouBound_v1

/-! Remove saturation by the L² Fatou theorem, with countably intersected
almost-everywhere identities for the actual L² representatives. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem scalar_eigen_exterior_exponential_memLp
    {N : ℕ} {Z E R δ a : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (hR : 0 < R) (ha : 0 ≤ a) (hgap : a^2 < δ)
    (hcoerc : ∀ (v : SpatialL2 N) (q : ℝ), scalarCoulombH1FormValue N Z v q →
      (∀ᵐ x, ‖x‖ ≤ R → v x = 0) → δ*‖v‖^2 ≤ q-E*‖v‖^2) :
    MemLp (fun x => (exteriorTaper N R x *
      Real.exp (a*smoothConfigurationRadius N x)) • f x) 2 volume := by
  obtain ⟨C,hC,hbound⟩ := scalar_eigen_exterior_exponential_uniform_bound hg hR ha hgap hcoerc
  have hpos (n : ℕ) : 0 < (n : ℝ)+1 := by positivity
  let U (n : ℕ) : SpatialL2 N := boundedRealMul
    (exteriorExpWeight N R a ((n : ℝ)+1))
    (exteriorExpWeight_memLp_top N R a (hpos n)) f
  have hrep : ∀ᵐ x, ∀ n : ℕ, U n x = exteriorExpWeight N R a ((n : ℝ)+1) x • f x := by
    rw [ae_all_iff]
    intro n
    exact boundedRealMul_ae _ _ _
  have ht : ∀ᵐ x, Tendsto (fun n : ℕ => U n x) atTop
      (𝓝 ((exteriorTaper N R x * Real.exp (a*smoothConfigurationRadius N x)) • f x)) := by
    filter_upwards [hrep] with x hx
    exact ((exteriorExpWeight_tendsto N R a x).smul_const (f x)).congr'
      (Eventually.of_forall (fun n => (hx n).symm))
  obtain ⟨hm,_⟩ := memLp_of_ae_tendsto_L2_bounded U _ hC
    (fun n => hbound _ (hpos n)) ht
  exact hm

#print axioms scalar_eigen_exterior_exponential_memLp
end TheoremT.Continuum
