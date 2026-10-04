import ManyBody.S8.AmbientRationalDistanceApproximation
import ManyBody.S8.Internal.DyadicTaylorOrder

/-! A common linear dyadic Taylor order for the same original nuclear and pair
profiles. The fixed offset precedes every requested precision. -/
set_option autoImplicit false
noncomputable section
open TheoremT.Continuum
open MeasureTheory Metric
open scoped Topology NNReal
namespace ManyBody.S8

def RealThreeProfilesDyadicTaylorData (a b h : (Fin 3 → ℂ) → ℂ)
    (center : Fin 3 → ℝ) (R : ℝ) : Prop :=
  let f : Fin 3 → (Fin 3 → ℂ) → ℂ := ![a,b,h]
  ∃ m : ℕ, ∀ p : ℕ, ∀ q : Fin 3 → ℝ, ‖q-center‖<R/4 → ∀ j k : Fin 3,
    ‖iteratedFDeriv ℝ (k:ℕ) (ambientRealScalarProfile (f j)) q-
      iteratedFDeriv ℝ (k:ℕ) (realTaylorPolynomial (ambientRealScalarProfile (f j)) center (2*p+m+2)) q‖≤(1/2:ℝ)^p

def NuclearDyadicDistanceTaylorData (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε δ : ℝ) : Prop :=
  RealThreeProfilesDyadicTaylorData (nuclearOriginalAmbientA u i ε)
    (nuclearOriginalAmbientB u i ε) (nuclearOriginalAmbientFunction u i ε)
    (nuclearOriginalRealDistanceCenter ε) (ε*δ)

def PairDyadicDistanceTaylorData (u : Configuration 2 → ℂ) (ε δ : ℝ) : Prop :=
  RealThreeProfilesDyadicTaylorData (pairOriginalAmbientA u ε)
    (pairOriginalAmbientB u ε) (pairOriginalAmbientFunction u ε)
    (pairOriginalRealDistanceCenter ε) (ε*δ)

theorem nuclear_common_dyadic_distance_taylor_order
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A)
    (haxis : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (hrec : PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
      (nuclearAmbientNormalizedBound M A F0 W))
    (hdata : NuclearAmbientDistanceTaylorData u i ε M A F0 W) :
    NuclearDyadicDistanceTaylorData u i ε (nuclearAmbientRetainedRadius M A) := by
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
  apply real_three_profiles_common_dyadic_order (C:=![
    ‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W),
    (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W),
    ‖u 0‖+ε*nuclearAmbientNormalizedBound M A F0 W]) (mul_pos hε hδ)
  · intro j
    fin_cases j
    · simpa [nuclear_real_distance_center_cast] using hdata.1
    · simpa [nuclear_real_distance_center_cast] using hdata.2.1
    · simpa [nuclear_real_distance_center_cast] using hdata.2.2
  · intro j
    fin_cases j
    · simpa [nuclear_real_distance_center_cast] using hA'
    · simpa [nuclear_real_distance_center_cast] using hB'
    · simpa [nuclear_real_distance_center_cast] using hH'

theorem pair_common_dyadic_distance_taylor_order
    (u : Configuration 2 → ℂ) {ε M A F0 W δ : ℝ}
    (hε : 0<ε) (hδ : 0<δ)
    (hrec : PhysicalPairAmbientReconstruction u ε M A F0 W δ)
    (hdata : PairAmbientDistanceTaylorData u ε M A F0 W δ) :
    PairDyadicDistanceTaylorData u ε δ := by
  have hA' : AnalyticOnNhd ℂ (pairOriginalAmbientA u ε)
      (ball (pairOriginalDistanceCenter ε) (ε*δ)) :=
    fun q hq => hrec.1 q ((pair_original_distance_ball_iff hε hδ q).mp hq)
  have hB' : AnalyticOnNhd ℂ (pairOriginalAmbientB u ε)
      (ball (pairOriginalDistanceCenter ε) (ε*δ)) :=
    fun q hq => hrec.2.1 q ((pair_original_distance_ball_iff hε hδ q).mp hq)
  have hH' : AnalyticOnNhd ℂ (pairOriginalAmbientFunction u ε)
      (ball (pairOriginalDistanceCenter ε) (ε*δ)) :=
    fun q hq => hrec.2.2.1 q ((pair_original_distance_ball_iff hε hδ q).mp hq)
  apply real_three_profiles_common_dyadic_order (C:=![
    ‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W),
    (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W),
    ‖u 0‖+ε*pairAmbientNormalizedBound M A F0 W δ]) (mul_pos hε hδ)
  · intro j
    fin_cases j
    · simpa [pair_real_distance_center_cast] using hdata.1
    · simpa [pair_real_distance_center_cast] using hdata.2.1
    · simpa [pair_real_distance_center_cast] using hdata.2.2
  · intro j
    fin_cases j
    · simpa [pair_real_distance_center_cast] using hA'
    · simpa [pair_real_distance_center_cast] using hB'
    · simpa [pair_real_distance_center_cast] using hH'

#print axioms nuclear_common_dyadic_distance_taylor_order
#print axioms pair_common_dyadic_distance_taylor_order
theorem twoElectron_scalar_ground_common_dyadic_distance_taylor_order
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
          PairDyadicDistanceTaylorData u ε (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,hNR,hPR⟩ :=
      twoElectron_scalar_ground_real_rational_distance_C2_approximation Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,hNR,hPR,?_,?_⟩
  · intro ε hε hlim i
    exact nuclear_common_dyadic_distance_taylor_order u i hε hA (hNA ε hε hlim i)
      (hNrecData ε hε hlim i).1 (hNT ε hε hlim i).1
  · intro ε hε hlim
    exact pair_common_dyadic_distance_taylor_order u hε hδP (hrec ε hε hlim) (hPT ε hε hlim).1

#print axioms twoElectron_scalar_ground_common_dyadic_distance_taylor_order
end ManyBody.S8
