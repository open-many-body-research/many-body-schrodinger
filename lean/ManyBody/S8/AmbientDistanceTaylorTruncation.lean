import ManyBody.S8.NuclearAmbientDistanceDerivativeBudgets
import ManyBody.S8.Internal.ComplexTaylorTruncation
/-! Quantitative actual distance-profile Taylor approximation for a physical ground state.

The unchanged original nuclear and pair A/B/H functions are holomorphic and
bounded on their full distance polydiscs. Actual Cauchy coefficients and
complex iterated Frechet derivatives supply fixed-center Taylor polynomials;
on each quarter polydisc their value errors decrease as 3^(-N), with explicit
amplitudes from the same actual physical reconstruction. Every genuine
complex derivative field also has its actual Taylor polynomial, with an
explicit (2/3)^N operator-norm error, including first and second orders.

The principal endpoint retains one actual normalized scalar Coulomb ground
state at Z>=2, all original graph/spectral/H2/physical/decay and descent
facts, both nuclear indices, and the original c=1 pair reconstruction. No
Taylor remainder, derivative budget, replacement state or coefficient family
is assumed. Coefficients are the actual derivatives, with no rational or
computable coefficient assertion. Derivative-field approximants are stated
separately; no coupling to derivatives of a single value truncation is claimed.
-/
noncomputable section
set_option autoImplicit false
open TheoremT.Continuum
open scoped Topology NNReal
open MeasureTheory Metric
namespace ManyBody.S8

def AmbientProfileTaylorData
    (a b h : (Fin 3 → ℂ) → ℂ) (center : Fin 3 → ℂ) (R C_A C_B C_H : ℝ) : Prop :=
  ComplexDistanceTaylorData a center R C_A ∧
  ComplexDistanceTaylorData b center R C_B ∧
  ComplexDistanceTaylorData h center R C_H

def NuclearAmbientDistanceTaylorData (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε M A F0 W : ℝ) : Prop :=
  AmbientProfileTaylorData (nuclearOriginalAmbientA u i ε) (nuclearOriginalAmbientB u i ε)
    (nuclearOriginalAmbientFunction u i ε) (nuclearOriginalDistanceCenter ε)
    (ε*nuclearAmbientRetainedRadius M A)
    (‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W))
    ((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W))
    (‖u 0‖+ε*nuclearAmbientNormalizedBound M A F0 W)

def PairAmbientDistanceTaylorData (u : Configuration 2 → ℂ) (ε M A F0 W δ : ℝ) : Prop :=
  AmbientProfileTaylorData (pairOriginalAmbientA u ε) (pairOriginalAmbientB u ε)
    (pairOriginalAmbientFunction u ε) (pairOriginalDistanceCenter ε) (ε*δ)
    (‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W))
    ((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W))
    (‖u 0‖+ε*pairAmbientNormalizedBound M A F0 W δ)

theorem nuclear_ambient_distance_taylor_data
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A)
    (haxis : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (hrec : PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
      (nuclearAmbientNormalizedBound M A F0 W)) :
    NuclearAmbientDistanceTaylorData u i ε M A F0 W := by
  have hδ := nuclearAmbientRetainedRadius_pos (M:=M) hA
  have hR := mul_pos hε hδ
  obtain ⟨ha,hb⟩ := nuclearOriginalAmbient_profiles_analytic u i hε hA haxis
  have hBound := nuclearOriginalAmbient_profiles_bounds u i hε hA haxis
  have hdom (q : Fin 3 → ℂ) (hq : q∈ball (nuclearOriginalDistanceCenter ε)
      (ε*nuclearAmbientRetainedRadius M A)) :
      q∈nuclearOriginalDistancePolydisc ε (nuclearAmbientRetainedRadius M A) :=
    (nuclear_original_distance_ball_iff hε hδ q).mp hq
  exact ⟨bounded_holomorphic_complex_taylor_data hR (fun q hq => ha q (hdom q hq))
      (fun q hq => (hBound q (hdom q hq)).2.2),
    bounded_holomorphic_complex_taylor_data hR (fun q hq => hb q (hdom q hq))
      (fun q hq => (hBound q (hdom q hq)).2.1),
    bounded_holomorphic_complex_taylor_data hR (fun q hq => hrec.1 q (hdom q hq))
      (fun q hq => hrec.2.1 q (hdom q hq).1 (hdom q hq).2.1 (hdom q hq).2.2)⟩

theorem pair_ambient_distance_taylor_data
    (u : Configuration 2 → ℂ) {ε M A F0 W δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hrec : PhysicalPairAmbientReconstruction u ε M A F0 W δ) :
    PairAmbientDistanceTaylorData u ε M A F0 W δ := by
  have hR := mul_pos hε hδ
  have hdom (q : Fin 3 → ℂ) (hq : q∈ball (pairOriginalDistanceCenter ε) (ε*δ)) :
      ‖q 0-(ε:ℂ)‖<ε*δ ∧ ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2‖<ε*δ :=
    (pair_original_distance_ball_iff hε hδ q).mp hq
  exact ⟨bounded_holomorphic_complex_taylor_data hR (fun q hq => hrec.1 q (hdom q hq))
      (fun q hq => (hrec.2.2.2.1 q (hdom q hq).1 (hdom q hq).2.1 (hdom q hq).2.2).1),
    bounded_holomorphic_complex_taylor_data hR (fun q hq => hrec.2.1 q (hdom q hq))
      (fun q hq => (hrec.2.2.2.1 q (hdom q hq).1 (hdom q hq).2.1 (hdom q hq).2.2).2.1),
    bounded_holomorphic_complex_taylor_data hR (fun q hq => hrec.2.2.1 q (hdom q hq))
      (fun q hq => (hrec.2.2.2.1 q (hdom q hq).1 (hdom q hq).2.1 (hdom q hq).2.2).2.2)⟩

#print axioms nuclear_ambient_distance_taylor_data
#print axioms pair_ambient_distance_taylor_data
theorem twoElectron_scalar_ground_ambient_distance_taylor_truncation
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
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearAmbientDistanceTaylorData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientDistanceTaylorData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hPairRec,hδN,hNuclear⟩ :=
      twoElectron_scalar_ground_nuclear_ambient_distance_derivative_budgets Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hPairRec,hδN,hNuclear,?_,?_⟩
  · intro ε hε hlim i
    exact nuclear_ambient_distance_taylor_data u i hε hA (hNA ε hε hlim i)
      (hNuclear ε hε hlim i).1
  · intro ε hε hlim
    exact pair_ambient_distance_taylor_data u hε hδP (hPairRec ε hε hlim)

#print axioms twoElectron_scalar_ground_ambient_distance_taylor_truncation
end ManyBody.S8