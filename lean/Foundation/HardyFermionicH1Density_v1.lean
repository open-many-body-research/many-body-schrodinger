import HardyFermionicH1Projection_v1
import HardyH1SpinDensity_v1

/-! The actual fermionic H² domain is a core for the actual weak H¹ graph norm.
Neither Sobolev density nor invariance of the derivative family is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

/-- Every fermionic weak-H¹ vector is the L² limit of fermionic weak-H² vectors,
with every genuine first weak derivative converging in L² as well. No
normalization, binding, gap, or eigenfunction assumption is imposed. -/
theorem fermionic_h1_approx_by_h2_sequence {N : ℕ} {ψ : SpinSpace N}
    (hψ : ψ ∈ fermionicSubspace N) (d : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k) :
    ∃ ψn : ℕ → SpinSpace N, ∃ dn : ℕ → Coordinate N → SpinSpace N,
      (∀ n, ψn n ∈ targetDomain N) ∧
      (∀ n σ k, WeakPartial (ψn n σ) (dn n k σ) k) ∧
      Tendsto ψn atTop (𝓝 ψ) ∧
      ∀ k, Tendsto (fun n => dn n k) atTop (𝓝 (d k)) := by
  obtain ⟨ψn,dn,hH2,hdn,hψn,hdnlim⟩ := spin_h1_approx_by_h2_sequence d hd
  refine ⟨fun n => fermionicProjection N (ψn n),
    fun n => fermionicDerivativeProjection N (dn n), ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨fermionicProjection_mem N (ψn n),fermionicProjection_preserves_H2 (hH2 n)⟩
  · intro n σ k
    exact fermionicProjection_weakPartial (dn n) (hdn n) σ k
  · have ht := ((fermionicProjection_continuous N).tendsto ψ).comp hψn
    rwa [fermionicProjection_id hψ] at ht
  · have ht : Tendsto dn atTop (𝓝 d) := tendsto_pi_nhds.2 hdnlim
    have hproj := ((fermionicDerivativeProjection_continuous N).tendsto d).comp ht
    rw [fermionicDerivativeProjection_id hψ d hd] at hproj
    exact tendsto_pi_nhds.1 hproj

set_option pp.proofs false in
#print fermionic_h1_approx_by_h2_sequence
#print axioms fermionic_h1_approx_by_h2_sequence
end TheoremT.Continuum
