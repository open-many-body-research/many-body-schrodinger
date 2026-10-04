import ManyBody.S8.AmbientProfileRealness
import ManyBody.S8.Internal.RealRationalAmbientProfile
/-! Finite rational distance polynomials for the same actual Coulomb ground profiles.

For every positive tolerance, one rational monomial polynomial per profile
approximates its real value and actual real gradient/Hessian operator norms
uniformly on a fixed closed inner distance box. All nuclear indices and
admissible positive scales share the original physical ground representative.
The genuine analytic, realness, derivative and Taylor data are discharged
from the same original graph-derived witness, not introduced as physical
premises. No computable coefficient selection, physical H2 composition error,
global dictionary or full Rung 2 completion is asserted. -/
set_option autoImplicit false
noncomputable section
open TheoremT.Continuum
open scoped Topology NNReal
open MeasureTheory Metric
namespace ManyBody.S8

def RealRationalDistanceC2ApproximationData (f : (Fin 3 → ℂ) → ℂ)
    (a : Fin 3 → ℝ) (R : ℝ) : Prop :=
  ∀ ζ : ℝ, 0<ζ → ∃ s : Finset DistanceMultiIndex, ∃ r : DistanceMultiIndex → ℚ,
    ∀ p : Fin 3 → ℝ, ‖p-a‖≤R/8 → ∀ k : Fin 3,
      ‖iteratedFDeriv ℝ (k:ℕ) (ambientRealScalarProfile f) p-
        iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s (fun α => (r α:ℝ))) p‖<ζ

def NuclearRationalDistanceC2ApproximationData (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε δ : ℝ) : Prop :=
  RealRationalDistanceC2ApproximationData (nuclearOriginalAmbientA u i ε)
    (nuclearOriginalRealDistanceCenter ε) (ε*δ) ∧
  RealRationalDistanceC2ApproximationData (nuclearOriginalAmbientB u i ε)
    (nuclearOriginalRealDistanceCenter ε) (ε*δ) ∧
  RealRationalDistanceC2ApproximationData (nuclearOriginalAmbientFunction u i ε)
    (nuclearOriginalRealDistanceCenter ε) (ε*δ)

def PairRationalDistanceC2ApproximationData (u : Configuration 2 → ℂ)
    (ε δ : ℝ) : Prop :=
  RealRationalDistanceC2ApproximationData (pairOriginalAmbientA u ε)
    (pairOriginalRealDistanceCenter ε) (ε*δ) ∧
  RealRationalDistanceC2ApproximationData (pairOriginalAmbientB u ε)
    (pairOriginalRealDistanceCenter ε) (ε*δ) ∧
  RealRationalDistanceC2ApproximationData (pairOriginalAmbientFunction u ε)
    (pairOriginalRealDistanceCenter ε) (ε*δ)

theorem nuclear_real_rational_distance_C2_data
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A)
    (haxis : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (hrec : PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
      (nuclearAmbientNormalizedBound M A F0 W))
    (hdata : NuclearAmbientDistanceTaylorData u i ε M A F0 W) :
    NuclearRationalDistanceC2ApproximationData u i ε (nuclearAmbientRetainedRadius M A) := by
  have hδ := nuclearAmbientRetainedRadius_pos (M:=M) hA
  have hprofiles := nuclearOriginalAmbient_profiles_analytic u i hε hA haxis
  have hA' : AnalyticOnNhd ℂ (nuclearOriginalAmbientA u i ε)
      (ball (nuclearOriginalDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A)) :=
    fun q hq => hprofiles.1 q ((nuclear_original_distance_ball_iff hε hδ q).mp hq)
  have hB' : AnalyticOnNhd ℂ (nuclearOriginalAmbientB u i ε)
      (ball (nuclearOriginalDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A)) :=
    fun q hq => hprofiles.2 q ((nuclear_original_distance_ball_iff hε hδ q).mp hq)
  have hH' : AnalyticOnNhd ℂ (nuclearOriginalAmbientFunction u i ε)
      (ball (nuclearOriginalDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A)) :=
    fun q hq => hrec.1 q ((nuclear_original_distance_ball_iff hε hδ q).mp hq)
  refine ⟨?_,?_,?_⟩
  · intro ζ hζ
    exact rational_ambient_profile_uniform_C2 (mul_pos hε hδ)
      (by simpa only [nuclear_real_distance_center_cast] using hdata.1)
      (by simpa only [nuclear_real_distance_center_cast] using hA') hζ
  · intro ζ hζ
    exact rational_ambient_profile_uniform_C2 (mul_pos hε hδ)
      (by simpa only [nuclear_real_distance_center_cast] using hdata.2.1)
      (by simpa only [nuclear_real_distance_center_cast] using hB') hζ
  · intro ζ hζ
    exact rational_ambient_profile_uniform_C2 (mul_pos hε hδ)
      (by simpa only [nuclear_real_distance_center_cast] using hdata.2.2)
      (by simpa only [nuclear_real_distance_center_cast] using hH') hζ

theorem pair_real_rational_distance_C2_data
    (u : Configuration 2 → ℂ) {ε M A F0 W δ : ℝ}
    (hε : 0<ε) (hδ : 0<δ)
    (hrec : PhysicalPairAmbientReconstruction u ε M A F0 W δ)
    (hdata : PairAmbientDistanceTaylorData u ε M A F0 W δ) :
    PairRationalDistanceC2ApproximationData u ε δ := by
  have hA' : AnalyticOnNhd ℂ (pairOriginalAmbientA u ε)
      (ball (pairOriginalDistanceCenter ε) (ε*δ)) :=
    fun q hq => hrec.1 q ((pair_original_distance_ball_iff hε hδ q).mp hq)
  have hB' : AnalyticOnNhd ℂ (pairOriginalAmbientB u ε)
      (ball (pairOriginalDistanceCenter ε) (ε*δ)) :=
    fun q hq => hrec.2.1 q ((pair_original_distance_ball_iff hε hδ q).mp hq)
  have hH' : AnalyticOnNhd ℂ (pairOriginalAmbientFunction u ε)
      (ball (pairOriginalDistanceCenter ε) (ε*δ)) :=
    fun q hq => hrec.2.2.1 q ((pair_original_distance_ball_iff hε hδ q).mp hq)
  refine ⟨?_,?_,?_⟩
  · intro ζ hζ
    exact rational_ambient_profile_uniform_C2 (mul_pos hε hδ)
      (by simpa only [pair_real_distance_center_cast] using hdata.1)
      (by simpa only [pair_real_distance_center_cast] using hA') hζ
  · intro ζ hζ
    exact rational_ambient_profile_uniform_C2 (mul_pos hε hδ)
      (by simpa only [pair_real_distance_center_cast] using hdata.2.1)
      (by simpa only [pair_real_distance_center_cast] using hB') hζ
  · intro ζ hζ
    exact rational_ambient_profile_uniform_C2 (mul_pos hε hδ)
      (by simpa only [pair_real_distance_center_cast] using hdata.2.2)
      (by simpa only [pair_real_distance_center_cast] using hH') hζ

#print axioms nuclear_real_rational_distance_C2_data
#print axioms pair_real_rational_distance_C2_data
theorem twoElectron_scalar_ground_real_rational_distance_C2_approximation
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ C_H M A : ℝ, 1 ≤ C_H ∧ 1 ≤ M ∧ 1 ≤ A ∧
      ∃ f : SpatialL2 2, ∃ u : Configuration 2 → ℂ,
      ∃ L : ℝ≥0, ∃ R : ℝ,
        ‖f‖ = 1 ∧ HasH2 f ∧
        scalarHamiltonianGraph 2 Z f
          (((variationalGroundEnergy 2 Z).toReal : ℂ) • f) ∧
        spectralGroundEnergy 2 Z = ((variationalGroundEnergy 2 Z).toReal : EReal) ∧
        (((variationalGroundEnergy 2 Z).toReal : ℂ) ∈
          TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z)) ∧
        (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
          (variationalGroundEnergy 2 Z).toReal ≤ z.re) ∧
        LocallyLipschitz u ∧ (f : Configuration 2 → ℂ) =ᵐ[volume] u ∧
        (∀ x, ‖u x‖ ≤
          coulombMoserBoundCoefficient 2 Z (variationalGroundEnergy 2 Z).toReal) ∧
        (∀ x, (u x).im = 0) ∧
        (∀ x, u (permuteSpace twoElectronSwap x) = u x) ∧
        (∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
          u (configurationRotation 2 Q x) = u x) ∧
        0 < L ∧ 0 < R ∧ LipschitzOnWith L u (ball 0 R) ∧
        0 ≤ M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume ∧
        0 ≤ (((L : ℝ)^2+‖u 0‖^2)*C_H) ∧
        (∃ d : Coordinate 2 → SpatialL2 2,
          ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
          (∀ k, WeakPartial f (d k) k) ∧
          (∀ k l, WeakPartial (d k) (e k l) l) ∧
          ∀ a : ℝ, 0 ≤ a → a^2 < Z^2/112 →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
              weakH2ExteriorNorm f d e r ≤ Real.exp (-a*r)*C) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxInvariantAnalyticDescentDerivativeData
              ((originScaledDifference u ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference u ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L : ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ t0 : Position, ‖t0‖ = 1 →
            PhysicalKSBoxEvenInvariantAnalyticDescentDerivativeData
              ((originScaledDifference u ε ∘ pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference u ε (pairKSPhysicalCoordinates X T))
              t0 M A (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L : ℝ)^2+‖u 0‖^2)*C_H)) ∧
        0 < physicalKSAnalyticAxisRadius M A ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) → ∀ i : Fin 2,
          PhysicalKSAxisAnalyticDescentData
            ((originScaledDifference u ε ∘ nuclearKSLift i) ∘
              (physicalSpectatorReindexAt i).symm)
            (WithLp.toLp 2 ![0,0,1]) M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L : ℝ)^2+‖u 0‖^2)*C_H) (physicalKSAnalyticAxisRadius M A)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          PhysicalKSAxisAnalyticDescentData
            ((originScaledDifference u ε ∘ pairKSLift) ∘
              (physicalSpectatorReindexAt (0 : Fin 2)).symm)
            (WithLp.toLp 2 ![0,0,1]) M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L : ℝ)^2+‖u 0‖^2)*C_H) (physicalKSAnalyticAxisRadius M A)) ∧
        0<pairAmbientDistanceRadius 1 M A ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientPhysicalAnalyticData (originScaledDifference u ε) 1 M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PhysicalPairAmbientReconstruction u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
        0<nuclearAmbientRetainedRadius M A ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
            (nuclearAmbientNormalizedBound M A
              (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
          NuclearAmbientDistanceDerivativeData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientDistanceDerivativeData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A) ∧
          PairRealAmbientDistanceDerivativeData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearRealAmbientDistanceDerivativeData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearAmbientDistanceTaylorData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) ∧
          NuclearAmbientProfileRealityData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientDistanceTaylorData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A) ∧
          PairAmbientProfileRealityData u ε (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearRationalDistanceC2ApproximationData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairRationalDistanceC2ApproximationData u ε (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT⟩ :=
      twoElectron_scalar_ground_ambient_real_profiles_and_taylor_data Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,?_,?_⟩
  · intro ε hε hlim i
    exact nuclear_real_rational_distance_C2_data u i hε hA (hNA ε hε hlim i)
      (hNrecData ε hε hlim i).1 (hNT ε hε hlim i).1
  · intro ε hε hlim
    exact pair_real_rational_distance_C2_data u hε hδP (hrec ε hε hlim) (hPT ε hε hlim).1

#print axioms twoElectron_scalar_ground_real_rational_distance_C2_approximation
end ManyBody.S8
