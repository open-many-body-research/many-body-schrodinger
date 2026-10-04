import ManyBody.S8.AmbientDistanceTaylorTruncation
import ManyBody.S8.Internal.ComplexTaylorPolynomialDerivatives
/-! Coupled local distance Taylor approximation for the same physical ground state.

Each actual profile A/B/H has one literal finite canonical Taylor polynomial.
Its genuine complex derivatives are exactly the finite Taylor polynomials of
that profile's derivative fields, with degree cutoff N-k. The resulting
quarter-polydisc estimates simultaneously control its value, gradient and
Hessian, with geometric errors in N. The principal endpoint preserves all
actual scalar-ground, graph, spectral, H2, decay, physical and original
nuclear/pair reconstruction facts of the original Taylor endpoint.

This is a local polynomial approximation of the actual holomorphic distance
profiles. No rational/computable coefficient claim, composed physical H2
error, global dictionary approximation or Rung 2 completion is asserted.
-/
noncomputable section
set_option autoImplicit false
open TheoremT.Continuum
open scoped Topology NNReal
open MeasureTheory Metric
namespace ManyBody.S8

def AmbientProfileCoupledTaylorData
    (a b h : (Fin 3 → ℂ) → ℂ) (center : Fin 3 → ℂ) (R C_A C_B C_H : ℝ) : Prop :=
  CoupledComplexDistanceTaylorData a center R C_A ∧
  CoupledComplexDistanceTaylorData b center R C_B ∧
  CoupledComplexDistanceTaylorData h center R C_H

def NuclearAmbientDistanceCoupledTaylorData (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε M A F0 W : ℝ) : Prop :=
  NuclearAmbientDistanceTaylorData u i ε M A F0 W ∧
  AmbientProfileCoupledTaylorData
    (nuclearOriginalAmbientA u i ε) (nuclearOriginalAmbientB u i ε)
    (nuclearOriginalAmbientFunction u i ε) (nuclearOriginalDistanceCenter ε)
    (ε*nuclearAmbientRetainedRadius M A)
    (‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W))
    ((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W))
    (‖u 0‖+ε*nuclearAmbientNormalizedBound M A F0 W)

def PairAmbientDistanceCoupledTaylorData (u : Configuration 2 → ℂ)
    (ε M A F0 W δ : ℝ) : Prop :=
  PairAmbientDistanceTaylorData u ε M A F0 W δ ∧
  AmbientProfileCoupledTaylorData
    (pairOriginalAmbientA u ε) (pairOriginalAmbientB u ε)
    (pairOriginalAmbientFunction u ε) (pairOriginalDistanceCenter ε) (ε*δ)
    (‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W))
    ((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W))
    (‖u 0‖+ε*pairAmbientNormalizedBound M A F0 W δ)

theorem nuclear_ambient_distance_coupled_taylor_data
    {u : Configuration 2 → ℂ} {i : Fin 2} {ε M A F0 W : ℝ}
    (hdata : NuclearAmbientDistanceTaylorData u i ε M A F0 W) :
    NuclearAmbientDistanceCoupledTaylorData u i ε M A F0 W :=
  ⟨hdata,actual_taylor_data_coupled hdata.1,
    actual_taylor_data_coupled hdata.2.1,actual_taylor_data_coupled hdata.2.2⟩

theorem pair_ambient_distance_coupled_taylor_data
    {u : Configuration 2 → ℂ} {ε M A F0 W δ : ℝ}
    (hdata : PairAmbientDistanceTaylorData u ε M A F0 W δ) :
    PairAmbientDistanceCoupledTaylorData u ε M A F0 W δ :=
  ⟨hdata,actual_taylor_data_coupled hdata.1,
    actual_taylor_data_coupled hdata.2.1,actual_taylor_data_coupled hdata.2.2⟩

#print axioms nuclear_ambient_distance_coupled_taylor_data
#print axioms pair_ambient_distance_coupled_taylor_data
theorem twoElectron_scalar_ground_ambient_distance_coupled_taylor_truncation
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
          NuclearAmbientDistanceCoupledTaylorData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientDistanceCoupledTaylorData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hPairRec,hδN,hNuclear,hTaylorN,hTaylorP⟩ :=
      twoElectron_scalar_ground_ambient_distance_taylor_truncation Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hPairRec,hδN,hNuclear,?_,?_⟩
  · intro ε hε hlim i
    exact nuclear_ambient_distance_coupled_taylor_data (hTaylorN ε hε hlim i)
  · intro ε hε hlim
    exact pair_ambient_distance_coupled_taylor_data (hTaylorP ε hε hlim)

#print axioms twoElectron_scalar_ground_ambient_distance_coupled_taylor_truncation
end ManyBody.S8