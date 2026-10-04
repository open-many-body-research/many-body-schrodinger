import ManyBody.S8.Internal.DyadicTaylorNumeratorBound
import ManyBody.S8.AmbientDyadicRationalDistanceDictionary
/-! Actual original ground profiles with linear raw dyadic numerator magnitude.

The same complete original ground/graph/analytic/Taylor/rational witness is
retained. Genuine original Taylor data discharges the coefficient jet bound;
fixed common offsets at each positive original chart control all raw floor
numerators before every Taylor order and dyadic denominator exponent. This
adds a finite encoding magnitude bound without an evaluation oracle, an
algorithm for the original real coefficients, or a full solver-cost claim. -/
set_option autoImplicit false
noncomputable section
open TheoremT.Continuum
open MeasureTheory Metric
open scoped Topology NNReal BigOperators ContDiff
namespace ManyBody.S8

def NuclearDyadicDistanceNumeratorData (u : Configuration 2 → ℂ) (i : Fin 2) (ε : ℝ) : Prop :=
  RealThreeProfilesDyadicNumeratorData (nuclearOriginalAmbientA u i ε)
    (nuclearOriginalAmbientB u i ε) (nuclearOriginalAmbientFunction u i ε)
    (nuclearOriginalRealDistanceCenter ε)

def PairDyadicDistanceNumeratorData (u : Configuration 2 → ℂ) (ε : ℝ) : Prop :=
  RealThreeProfilesDyadicNumeratorData (pairOriginalAmbientA u ε)
    (pairOriginalAmbientB u ε) (pairOriginalAmbientFunction u ε)
    (pairOriginalRealDistanceCenter ε)

theorem nuclear_dyadic_distance_raw_numerator
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A)
    (hdata : NuclearAmbientDistanceTaylorData u i ε M A F0 W) :
    NuclearDyadicDistanceNumeratorData u i ε := by
  have hδ := nuclearAmbientRetainedRadius_pos (M:=M) hA
  apply real_three_profiles_dyadic_raw_numerator (C:=![
    ‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W),
    (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W),
    ‖u 0‖+ε*nuclearAmbientNormalizedBound M A F0 W]) (mul_pos hε hδ)
  intro j
  fin_cases j
  · simpa [nuclear_real_distance_center_cast] using hdata.1
  · simpa [nuclear_real_distance_center_cast] using hdata.2.1
  · simpa [nuclear_real_distance_center_cast] using hdata.2.2

theorem pair_dyadic_distance_raw_numerator
    (u : Configuration 2 → ℂ) {ε M A F0 W δ : ℝ}
    (hε : 0<ε) (hδ : 0<δ)
    (hdata : PairAmbientDistanceTaylorData u ε M A F0 W δ) :
    PairDyadicDistanceNumeratorData u ε := by
  apply real_three_profiles_dyadic_raw_numerator (C:=![
    ‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W),
    (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W),
    ‖u 0‖+ε*pairAmbientNormalizedBound M A F0 W δ]) (mul_pos hε hδ)
  intro j
  fin_cases j
  · simpa [pair_real_distance_center_cast] using hdata.1
  · simpa [pair_real_distance_center_cast] using hdata.2.1
  · simpa [pair_real_distance_center_cast] using hdata.2.2

theorem real_three_profiles_raw_numerator_linear_precision
    {a b h : (Fin 3 → ℂ) → ℂ} {center : Fin 3 → ℝ}
    (hdata : RealThreeProfilesDyadicNumeratorData a b h center) :
    ∃ k k0 : ℕ, ∀ m p : ℕ, ∀ j : Fin 3, ∀ α : DistanceMultiIndex,
      (realTaylorDyadicRawNumerator (ambientRealScalarProfile (![a,b,h] j)) center
        (2*p+m+4) (15*p+7*m+33) α).natAbs ≤
        2^((2*k+17)*p+(k+8)*m+4*k+k0+38) := by
  obtain ⟨k,k0,hk⟩ := hdata
  refine ⟨k,k0,?_⟩
  intro m p j α
  simpa only [dyadic_raw_numerator_schedule_exponent] using
    hk (2*p+m+4) (15*p+7*m+33) j α

theorem twoElectron_scalar_ground_dyadic_distance_numerator_bound
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
          PairRationalDistanceC2ApproximationData u ε (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearDyadicDistanceTaylorData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairDyadicDistanceTaylorData u ε (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearBoundedDyadicDistanceDictionaryData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairBoundedDyadicDistanceDictionaryData u ε (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearDyadicRationalDistanceDictionaryData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairDyadicRationalDistanceDictionaryData u ε (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearDyadicDistanceNumeratorData u i ε) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairDyadicDistanceNumeratorData u ε) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,
    hNT,hPT,hNR,hPR,hND,hPD,hNBD,hPBD,hNQD,hPQD⟩ :=
      twoElectron_scalar_ground_dyadic_rational_distance_dictionary Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,
    hNT,hPT,hNR,hPR,hND,hPD,hNBD,hPBD,hNQD,hPQD,?_,?_⟩
  · intro ε hε hlim i
    exact nuclear_dyadic_distance_raw_numerator u i hε hA (hNT ε hε hlim i).1
  · intro ε hε hlim
    exact pair_dyadic_distance_raw_numerator u hε hδP (hPT ε hε hlim).1

#print axioms nuclear_dyadic_distance_raw_numerator
#print axioms pair_dyadic_distance_raw_numerator
#print axioms real_three_profiles_raw_numerator_linear_precision
#print axioms twoElectron_scalar_ground_dyadic_distance_numerator_bound
end ManyBody.S8
