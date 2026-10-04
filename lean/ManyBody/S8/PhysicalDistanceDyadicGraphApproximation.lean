import ManyBody.S8.PhysicalDistanceDyadicH2Approximation
import ManyBody.S8.Internal.PhysicalDistanceGraphErrorBudget
import Mathlib.Tactic
/-! The same literal local rational distance dictionaries have true physical
Coulomb graph outputs and energy-shifted graph errors with dyadic rates. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators NNReal
namespace ManyBody.S8
open TheoremT.Continuum

def PhysicalDistanceDyadicGraphApproximation (u : Configuration 2 → ℂ)
    (χ : Configuration 2 → ℝ) (hc : HasCompactSupport χ)
    (h : (Fin 3 → ℂ) → ℂ) (a : Fin 3 → ℝ) (R Z E : ℝ) : Prop :=
  ∃C : ℝ,1≤C ∧ ∃m : ℕ,∀p : ℕ,
    (physicalDyadicDistanceSupport h a m p).card≤(physicalDyadicDistanceOrder m p)^3 ∧
    (∀α∈physicalDyadicDistanceSupport h a m p,(∑j : Fin 3,α j)<physicalDyadicDistanceOrder m p) ∧
    (∀α∈physicalDyadicDistanceSupport h a m p,∀j : Fin 3,α j<physicalDyadicDistanceOrder m p) ∧
    ContDiffOn ℝ ∞ (physicalDyadicDistanceError h a m p) (ball a R) ∧
    PhysicalDistanceCutoffH2ErrorData χ hc (physicalDyadicDistanceError h a m p) ((1/2:ℝ)^p) C ∧
    PhysicalDistanceCutoffGraphErrorData χ hc (physicalDyadicDistanceError h a m p) ((1/2:ℝ)^p) C Z E ∧
    ∀x : Configuration 2,
      physicalCutoffDistanceValue χ (physicalDyadicDistanceError h a m p) x=
      χ x • (u x-(physicalDyadicDistancePolynomial h a m p (physicalDistanceTriple x) : ℂ))


theorem physical_distance_dyadic_graph_approximation_of_H2_data
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {hc : HasCompactSupport χ}
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R : ℝ} (Z E : ℝ)
    (hdata : PhysicalDistanceDyadicH2Approximation u χ hc h a R) :
    PhysicalDistanceDyadicGraphApproximation u χ hc h a R Z E := by
  obtain ⟨C,hC,m,hm⟩ := hdata
  refine ⟨C,hC,m,?_⟩
  intro p
  obtain ⟨hcard,hdegree,hcoord,hsmooth,hH2,hvalue⟩ := hm p
  exact ⟨hcard,hdegree,hcoord,hsmooth,hH2,
    physical_distance_cutoff_graph_error_of_H2_data Z E hH2,hvalue⟩

theorem physical_distance_dyadic_actual_graph_error_small
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {hc : HasCompactSupport χ}
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R Z E : ℝ}
    (hdata : PhysicalDistanceDyadicGraphApproximation u χ hc h a R Z E)
    {η : ℝ} (hη : 0<η) (p0 : ℕ) :
    ∃m p : ℕ,∃F : SpatialL2 2,∃d : Coordinate 2 → SpatialL2 2,
    ∃e : Coordinate 2 → Coordinate 2 → SpatialL2 2,∃H : SpatialL2 2,
      p0≤p ∧
      F=ᵐ[volume] (fun x => χ x • (u x-
        (physicalDyadicDistancePolynomial h a m p (physicalDistanceTriple x):ℂ))) ∧
      (∀k,WeakPartial F (d k) k) ∧ (∀k j,WeakPartial (d k) (e k j) j) ∧
      HasH2 F ∧ scalarHamiltonianGraph 2 Z F H ∧
      physicalH2ComponentNorm F d e+‖H‖+‖H-(E:ℂ) • F‖<η := by
  obtain ⟨C,hC,m,hm⟩ := hdata
  let B := ‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖
  let K := physicalDistanceGraphCoefficient Z E
  have hlim : Tendsto (fun p : ℕ => (1+2*K)*(7*(1/2:ℝ)^p*C*B)) atTop (𝓝 0) := by
    convert (((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ))
      (by norm_num : (1/2:ℝ)<1)).const_mul 7).mul_const C |>.mul_const B).const_mul (1+2*K) using 1
    simp
  obtain ⟨p,hp0,hpη⟩ := ((eventually_ge_atTop p0).and (hlim.eventually (gt_mem_nhds hη))).exists
  obtain ⟨_,_,_,_,_,herr,hid⟩ := hm p
  obtain ⟨F,d,e,H,hF,_,_,hw1,hw2,hH2,hN,hGraph,hHamiltonian,hShift⟩ := herr
  let T := 7*(1/2:ℝ)^p*C*B
  have hT : 0≤T := by dsimp [T,B]; have : 0≤C := le_trans (by norm_num) hC; positivity
  have hH : ‖H‖≤K*T := by
    exact hHamiltonian.trans (mul_le_mul_of_nonneg_right
      (by dsimp [K,physicalDistanceGraphCoefficient]; exact le_add_of_nonneg_right (abs_nonneg E)) hT)
  have hsum : physicalH2ComponentNorm F d e+‖H‖+‖H-(E:ℂ) • F‖≤(1+2*K)*T := by
    change physicalH2ComponentNorm F d e≤T at hN
    change ‖H-(E:ℂ) • F‖≤K*T at hShift
    nlinarith
  exact ⟨m,p,F,d,e,H,hp0,hF.trans (Eventually.of_forall hid),hw1,hw2,hH2,hGraph,
    hsum.trans_lt hpη⟩

def PhysicalGroundDistanceDyadicGraphData (u : Configuration 2 → ℂ) (ε M A Z E : ℝ) : Prop :=
  (∀(χ : Configuration 2 → ℝ) (_hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ),
    (∀x∈tsupport χ,physicalDistanceTriple x∈closedBall (physicalNuclearDistanceCenter ε)
      (ε*nuclearAmbientRetainedRadius M A/8)) →
    PhysicalDistanceDyadicGraphApproximation u χ hc (nuclearOriginalAmbientFunction u 0 ε)
      (physicalNuclearDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A) Z E) ∧
  (∀(χ : Configuration 2 → ℝ) (_hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ),
    (∀x∈tsupport χ,physicalDistanceTriple x∈closedBall (physicalPairDistanceCenter ε)
      (ε*pairAmbientDistanceRadius 1 M A/8)) →
    PhysicalDistanceDyadicGraphApproximation u χ hc (pairOriginalAmbientFunction u ε)
      (physicalPairDistanceCenter ε) (ε*pairAmbientDistanceRadius 1 M A) Z E)


theorem physical_ground_dyadic_graph_data_of_H2_data
    {u : Configuration 2 → ℂ} {ε M A : ℝ} (Z E : ℝ)
    (hdata : PhysicalGroundDistanceDyadicH2Data u ε M A) :
    PhysicalGroundDistanceDyadicGraphData u ε M A Z E := by
  refine ⟨?_,?_⟩
  · intro χ hχ hc hs
    exact physical_distance_dyadic_graph_approximation_of_H2_data Z E (hdata.1 χ hχ hc hs)
  · intro χ hχ hc hs
    exact physical_distance_dyadic_graph_approximation_of_H2_data Z E (hdata.2 χ hχ hc hs)

theorem twoElectron_scalar_ground_physical_distance_dyadic_graph_approximation
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
        (∀ ε : ℝ,0<ε → ε≤min 1 (R/4) →
          PhysicalGroundDistanceDyadicH2Data u ε M A) ∧
        (∀ ε : ℝ,0<ε → ε≤min 1 (R/4) →
          PhysicalGroundDistanceDyadicGraphData u ε M A Z
            (variationalGroundEnergy 2 Z).toReal) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,
    hNR,hPR,hND,hPD,hNBD,hPBD,hNQR,hPQR,hPhys⟩ :=
      twoElectron_scalar_ground_physical_distance_dyadic_H2_approximation Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,
    hNR,hPR,hND,hPD,hNBD,hPBD,hNQR,hPQR,hPhys,?_⟩
  intro ε hε hlim
  exact physical_ground_dyadic_graph_data_of_H2_data Z
    (variationalGroundEnergy 2 Z).toReal (hPhys ε hε hlim)

#print axioms physical_distance_dyadic_graph_approximation_of_H2_data
#print axioms physical_distance_dyadic_actual_graph_error_small
#print axioms physical_ground_dyadic_graph_data_of_H2_data
#print axioms twoElectron_scalar_ground_physical_distance_dyadic_graph_approximation
end ManyBody.S8
