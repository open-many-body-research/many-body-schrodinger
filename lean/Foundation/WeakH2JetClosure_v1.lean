import HardyH1ClosedGraph_v1
import ConfigurationLpDominated_v1

/-! Closure of the actual weak H2 jet under strong L2 convergence in every
value/derivative coordinate. No differentiability of representatives is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem weakH2_jet_of_tendsto {N : ℕ} {ι : Type*} {l : Filter ι} [NeBot l]
    {f : ι → SpatialL2 N} {d : ι → Coordinate N → SpatialL2 N}
    {e : ι → Coordinate N → Coordinate N → SpatialL2 N}
    {f₀ : SpatialL2 N} {d₀ : Coordinate N → SpatialL2 N}
    {e₀ : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ n k, WeakPartial (f n) (d n k) k)
    (he : ∀ n k j, WeakPartial (d n k) (e n k j) j)
    (hf : Tendsto f l (𝓝 f₀))
    (hdf : ∀ k, Tendsto (fun n => d n k) l (𝓝 (d₀ k)))
    (hef : ∀ k j, Tendsto (fun n => e n k j) l (𝓝 (e₀ k j))) :
    (∀ k, WeakPartial f₀ (d₀ k) k) ∧
      (∀ k j, WeakPartial (d₀ k) (e₀ k j) j) ∧ HasH2 f₀ := by
  have h1 (k : Coordinate N) := WeakPartial.of_tendsto (fun n => hd n k) hf (hdf k)
  have h2 (k j : Coordinate N) := WeakPartial.of_tendsto (fun n => he n k j) (hdf k) (hef k j)
  exact ⟨h1,h2,d₀,h1,fun k j => ⟨e₀ k j,h2 k j⟩⟩

#print axioms weakH2_jet_of_tendsto
end TheoremT.Continuum
