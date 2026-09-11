import NonlinearWeakChainCore_v1
import HardyH1ScalarDensity_v2
import HardyH1ClosedGraph_v1
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! A real C1 chain rule on the actual weak H1 domain. Bounded derivative and
F(0)=0 are explicit, verifiable hypotheses on the nonlinear map. No regularity
or pointwise representative of the input beyond actual weak H1 is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace TheoremT.Continuum

theorem weakH1_C1_chain {N : ℕ} (F : ℂ → ℂ) (hF : ContDiff ℝ 1 F)
    (h0 : F 0 = 0) (K : ℝ≥0) (hb : ∀ z, ‖fderiv ℝ F z‖ ≤ K)
    {f : SpatialL2 N} (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (k : Coordinate N) :
    WeakPartial ((boundedC1_lipschitz F hF K hb).compLp h0 f)
      (nonlinearFieldL2 (fderiv ℝ F) (hF.continuous_fderiv (by norm_num)) K hb f (d k)) k := by
  obtain ⟨u,g,dg,hu,hc,hgu,hdgu,_hw,_hH2,hg,hdg⟩ :=
    weakH1_smooth_compact_graph_sequence d hd
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  apply WeakPartial.of_tendsto (l := atTop)
    (fun n => weakPartial_compact_C1_chain F hF h0 K hb (hu (ns n)) (hc (ns n))
      (g (ns n)) (dg (ns n) k) k (hgu (ns n)) (hdgu (ns n) k))
  · exact ((boundedC1_lipschitz F hF K hb).continuous_compLp h0).tendsto f |>.comp
      (hg.comp hns.tendsto_atTop)
  · exact nonlinearFieldL2_tendsto (fderiv ℝ F) (hF.continuous_fderiv (by norm_num)) K hb
      (fun n => g (ns n)) (fun n => dg (ns n) k) f (d k) hae
      ((hdg k).comp hns.tendsto_atTop)

theorem HasH1.comp_bounded_C1 {N : ℕ} {f : SpatialL2 N} (hf : HasH1 f)
    (F : ℂ → ℂ) (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (K : ℝ≥0) (hb : ∀ z, ‖fderiv ℝ F z‖ ≤ K) :
    HasH1 ((boundedC1_lipschitz F hF K hb).compLp h0 f) := by
  obtain ⟨d,hd⟩ := hf
  exact ⟨fun k => nonlinearFieldL2 (fderiv ℝ F) (hF.continuous_fderiv (by norm_num))
    K hb f (d k),fun k => weakH1_C1_chain F hF h0 K hb d hd k⟩

#print axioms weakH1_C1_chain
#print axioms HasH1.comp_bounded_C1
end TheoremT.Continuum
