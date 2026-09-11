import TwoElectronFirstSliceSmoothWeak_v1
import ProductL2FiniteSliceConvergence_v1
import HardyH1ScalarDensity_v2
import HardyH1ClosedGraph_v1

/-! Actual weak H1 slicing, proved by smooth graph approximation and a common slice subsequence. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem twoElectronFirstSlice_weakPartial_ae (F : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (hd : ∀ k, WeakPartial F (d k) k) :
    ∀ᵐ y ∂volume, ∀ k : Fin 3,
      WeakPartial (twoElectronFirstSlice F y) (twoElectronFirstSlice (d (0,k)) y) (0,k) := by
  obtain ⟨u,g,dg,hu,hc,hgu,hdgu,hdg,hH2,hg,hdd⟩ :=
    weakH1_smooth_compact_graph_sequence d hd
  let A : ℕ → Option (Fin 3) → TwoElectronProductL2 :=
    fun n i => twoElectronL2ProductEquiv (i.elim (g n) (fun k => dg n (0,k)))
  let B : Option (Fin 3) → TwoElectronProductL2 :=
    fun i => twoElectronL2ProductEquiv (i.elim F (fun k => d (0,k)))
  have hA : ∀ i, Tendsto (fun n => A n i) atTop (𝓝 (B i)) := by
    intro i
    cases i with
    | none => exact twoElectronL2ProductEquiv.continuous.continuousAt.tendsto.comp hg
    | some k => exact twoElectronL2ProductEquiv.continuous.continuousAt.tendsto.comp (hdd (0,k))
  obtain ⟨ns,hns,hconv⟩ := ProductL2.exists_subseq_sliceLeft_tendsto_finite A B hA
  have hweak : ∀ᵐ y ∂volume, ∀ n : ℕ, ∀ k : Fin 3,
      WeakPartial (twoElectronFirstSlice (g (ns n)) y)
        (twoElectronFirstSlice (dg (ns n) (0,k)) y) (0,k) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact twoElectronFirstSlice_smooth_weakPartial (u (ns n)) (hu (ns n)) (hc (ns n))
      (g (ns n)) (dg (ns n) (0,k)) k (hgu (ns n)) (hdgu (ns n) (0,k))
  filter_upwards [hconv,hweak] with y hy hw
  intro k
  exact WeakPartial.of_tendsto (fun n => hw n k) (hy none) (hy (some k))

theorem twoElectronFirstSlice_hasH1_ae (F : SpatialL2 2) (hF : HasH1 F) :
    ∀ᵐ y ∂volume, HasH1 (twoElectronFirstSlice F y) := by
  obtain ⟨d,hd⟩ := hF
  filter_upwards [twoElectronFirstSlice_weakPartial_ae F d hd] with y hy
  refine ⟨fun k => twoElectronFirstSlice (d (0,k.2)) y,?_⟩
  rintro ⟨i,k⟩
  fin_cases i
  exact hy k

#print axioms twoElectronFirstSlice_weakPartial_ae
#print axioms twoElectronFirstSlice_hasH1_ae
end TheoremT.Continuum
