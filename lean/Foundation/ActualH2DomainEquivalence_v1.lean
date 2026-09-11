import FourierSobolevDomain_v1
import WeakPartialDistribution_v1

/-!
Exact domain equivalences for the pre-existing physical weak HasH2 predicate.
All ordered mixed weak derivatives are present in that unchanged definition.
The existence of an L2 distributional Laplacian is concluded from HasH2.
-/

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv BigOperators

namespace TheoremT.Continuum

theorem HasH2.exists_temperedDistribution_laplacian {N : ℕ}
    {f : SpatialL2 N} (hf : HasH2 f) :
    ∃ w : SpatialL2 N,
      Δ (f : 𝓢'(Configuration N, ℂ)) = (w : 𝓢'(Configuration N, ℂ)) := by
  classical
  obtain ⟨d, hd, hsecond⟩ := hf
  choose e he using hsecond
  have hD (k : Coordinate N) :
      ∂_{coordinateVector k} (f : 𝓢'(Configuration N, ℂ)) =
        (d k : 𝓢'(Configuration N, ℂ)) :=
    (hd k).temperedDistribution_derivative
  have hE (k : Coordinate N) :
      ∂_{coordinateVector k} (d k : 𝓢'(Configuration N, ℂ)) =
        (e k k : 𝓢'(Configuration N, ℂ)) :=
    (he k k).temperedDistribution_derivative
  refine ⟨∑ k, e k k, ?_⟩
  rw [laplacian_eq_sum (EuclideanSpace.basisFun (Coordinate N) ℝ)]
  simp only [EuclideanSpace.basisFun_apply]
  change (∑ k : Coordinate N,
    ∂_{coordinateVector k} (∂_{coordinateVector k} (f : 𝓢'(Configuration N, ℂ)))) = _
  simp_rw [hD, hE]
  simp only [← Lp.toTemperedDistributionCLM_apply, map_sum]

theorem hasH2_iff_exists_temperedDistribution_laplacian {N : ℕ}
    (f : SpatialL2 N) :
    HasH2 f ↔ ∃ w : SpatialL2 N,
      Δ (f : 𝓢'(Configuration N, ℂ)) = (w : 𝓢'(Configuration N, ℂ)) :=
  ⟨HasH2.exists_temperedDistribution_laplacian,
    fun ⟨w, hw⟩ => hasH2_of_temperedDistribution_laplacian f w hw⟩

theorem hasH2_iff_memSobolev_two {N : ℕ} (f : SpatialL2 N) :
    HasH2 f ↔ MemSobolev 2 2 (f : 𝓢'(Configuration N, ℂ)) := by
  constructor
  · intro hf
    obtain ⟨w, hw⟩ := hf.exists_temperedDistribution_laplacian
    exact memSobolev_two_of_laplacian_l2 f w hw
  · exact hasH2_of_memSobolev_two f

theorem hasH2_iff_fourier_normSq_memLp {N : ℕ} (f : SpatialL2 N) :
    HasH2 f ↔ MemLp (fun x : Configuration N =>
      Complex.ofReal (‖x‖ ^ 2) * (𝓕 f) x) 2 volume := by
  constructor
  · intro hf
    obtain ⟨w, hw⟩ := hf.exists_temperedDistribution_laplacian
    exact fourier_normSq_memLp_of_laplacian f w hw
  · exact hasH2_of_fourier_normSq_memLp f

#print axioms HasH2.exists_temperedDistribution_laplacian
#print axioms hasH2_iff_exists_temperedDistribution_laplacian
#print axioms hasH2_iff_memSobolev_two
#print axioms hasH2_iff_fourier_normSq_memLp

end TheoremT.Continuum
