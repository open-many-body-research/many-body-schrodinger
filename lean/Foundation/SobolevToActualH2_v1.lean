import LaplacianSobolevBridge_v1
import DistributionWeakPartial_v1

/-!
Connection from mathlib's Bessel-potential Sobolev space to the unchanged
physical weak-H2 definition. The final lemma takes an actual distributional
L2 Laplacian and concludes the project's full ordered-mixed-derivative domain.
The compact-test-to-Schwartz converse is not assumed here.
-/

noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv

namespace TheoremT.Continuum

theorem hasH2_of_memSobolev_two {N : ℕ} (f : SpatialL2 N)
    (hf : MemSobolev 2 2 (f : 𝓢'(Configuration N, ℂ))) :
    HasH2 f := by
  classical
  have hfirst (k : Coordinate N) :
      ∃ g : SpatialL2 N,
        ∂_{coordinateVector k} (f : 𝓢'(Configuration N, ℂ)) =
          (g : 𝓢'(Configuration N, ℂ)) := by
    apply memSobolev_zero_iff.mp
    exact MemSobolev.mono (by norm_num)
      (hf.lineDerivOp (m := coordinateVector k))
  choose d hd using hfirst
  refine ⟨d, fun k => weakPartial_of_temperedDistribution_derivative (hd k), ?_⟩
  intro k l
  have hdk : MemSobolev 1 2 (d k : 𝓢'(Configuration N, ℂ)) := by
    have hh := hf.lineDerivOp (m := coordinateVector k)
    norm_num at hh
    rw [hd k] at hh
    exact hh
  have he : ∃ e : SpatialL2 N,
      ∂_{coordinateVector l} (d k : 𝓢'(Configuration N, ℂ)) =
        (e : 𝓢'(Configuration N, ℂ)) := by
    apply memSobolev_zero_iff.mp
    simpa using hdk.lineDerivOp (m := coordinateVector l)
  obtain ⟨e, he⟩ := he
  exact ⟨e, weakPartial_of_temperedDistribution_derivative he⟩

theorem hasH2_of_temperedDistribution_laplacian {N : ℕ}
    (f w : SpatialL2 N)
    (hw : Δ (f : 𝓢'(Configuration N, ℂ)) = (w : 𝓢'(Configuration N, ℂ))) :
    HasH2 f :=
  hasH2_of_memSobolev_two f (memSobolev_two_of_laplacian_l2 f w hw)

#print axioms hasH2_of_memSobolev_two
#print axioms hasH2_of_temperedDistribution_laplacian

end TheoremT.Continuum
