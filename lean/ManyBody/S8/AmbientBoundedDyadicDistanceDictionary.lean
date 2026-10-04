import ManyBody.S8.AmbientDyadicDistanceTaylorOrder
import ManyBody.S8.Internal.RealTaylorDictionarySize
/-! Cubic size of actual physical distance Taylor dictionaries at dyadic precision.

The same original Coulomb ground witness at Z >= 2 retains all prior physical
and analytic facts. A fixed chart offset precedes every precision p; the
literal canonical real Taylor dictionary at N=2p+m+2 has total degree<N,
at most N^3 monomials and exact value-polynomial equality. Its genuine real
value/gradient/Hessian errors remain at most 2^-p on the quarter distance box.
Coefficients are the actual real Taylor coefficients; no rational rounding,
effective extraction, global dictionary or physical H2 composition is claimed. -/
set_option autoImplicit false
noncomputable section
open TheoremT.Continuum
open scoped Topology NNReal BigOperators
open MeasureTheory Metric
namespace ManyBody.S8

def RealThreeProfilesBoundedDyadicDictionaryData (a b h : (Fin 3 → ℂ) → ℂ)
    (center : Fin 3 → ℝ) (R : ℝ) : Prop :=
  let f : Fin 3 → (Fin 3 → ℂ) → ℂ := ![a,b,h]
  ∃ m : ℕ, ∀ p : ℕ, ∀ j : Fin 3,
    let g := ambientRealScalarProfile (f j)
    let N := 2*p+m+2
    let s := realTaylorDistanceDictionarySupport g center N
    let c := realTaylorDistanceDictionaryCoefficient g center N
    s.card≤N^3 ∧
    (∀ α∈s, (∑ l : Fin 3, α l)<N) ∧
    (∀ α∈s, ∀ l : Fin 3, α l<N) ∧
    realTaylorPolynomial g center N=realDistancePolynomial s c ∧
    ∀ q : Fin 3 → ℝ, ‖q-center‖<R/4 → ∀ k : Fin 3,
      ‖iteratedFDeriv ℝ (k:ℕ) g q-
        iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s c) q‖≤(1/2:ℝ)^p

def NuclearBoundedDyadicDistanceDictionaryData (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε δ : ℝ) : Prop :=
  RealThreeProfilesBoundedDyadicDictionaryData (nuclearOriginalAmbientA u i ε)
    (nuclearOriginalAmbientB u i ε) (nuclearOriginalAmbientFunction u i ε)
    (nuclearOriginalRealDistanceCenter ε) (ε*δ)

def PairBoundedDyadicDistanceDictionaryData (u : Configuration 2 → ℂ) (ε δ : ℝ) : Prop :=
  RealThreeProfilesBoundedDyadicDictionaryData (pairOriginalAmbientA u ε)
    (pairOriginalAmbientB u ε) (pairOriginalAmbientFunction u ε)
    (pairOriginalRealDistanceCenter ε) (ε*δ)

theorem real_three_profiles_bounded_dyadic_dictionary
    {a b h : (Fin 3 → ℂ) → ℂ} {center : Fin 3 → ℝ} {R : ℝ}
    (hdata : RealThreeProfilesDyadicTaylorData a b h center R) :
    RealThreeProfilesBoundedDyadicDictionaryData a b h center R := by
  obtain ⟨m,hm⟩ := hdata
  refine ⟨m,?_⟩
  intro p j
  let fs : Fin 3 → (Fin 3 → ℂ) → ℂ := ![a,b,h]
  let g := ambientRealScalarProfile (fs j)
  let N := 2*p+m+2
  refine ⟨realTaylorDistanceDictionarySupport_card_le g center N,?_,?_,
    realTaylorPolynomial_exact_distance_dictionary g center N,?_⟩
  · intro α hα
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hα
    exact realTaylorMvPolynomial_support_total_degree_lt g center N hd
  · intro α hα l
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hα
    exact realTaylorMvPolynomial_support_coordinate_lt g center N hd l
  · intro q hq k
    rw [←realTaylorPolynomial_exact_distance_dictionary g center N]
    exact hm p q hq j k

#print axioms real_three_profiles_bounded_dyadic_dictionary
theorem twoElectron_scalar_ground_bounded_dyadic_distance_dictionary
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
          PairBoundedDyadicDistanceDictionaryData u ε (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,hNR,hPR,hND,hPD⟩ :=
      twoElectron_scalar_ground_common_dyadic_distance_taylor_order Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,hNR,hPR,hND,hPD,?_,?_⟩
  · intro ε hε hlim i
    exact real_three_profiles_bounded_dyadic_dictionary (hND ε hε hlim i)
  · intro ε hε hlim
    exact real_three_profiles_bounded_dyadic_dictionary (hPD ε hε hlim)

#print axioms twoElectron_scalar_ground_bounded_dyadic_distance_dictionary
end ManyBody.S8
