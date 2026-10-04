import ManyBody.S8.Internal.PhysicalDistanceCompositionErrors
import ManyBody.S8.Internal.PhysicalDistanceChartReconstruction
import ManyBody.S8.Internal.RealAmbientCoupledTaylorError
import ManyBody.S8.AmbientDistanceCoupledTaylorTruncation
import OpenSmoothCutoff_v1
import Mathlib.Tactic
/-! Actual local physical H2 approximation by one distance Taylor polynomial.

The original scalar ground witness and physical representative are retained.
For every admissible scale, a genuine smooth compact cutoff whose actual
three-radii image lies in the closed inner distance box has an actual error
class equal to chi*(u-P_N(actual radii)). The finite canonical polynomial is
the SAME literal original-profile Taylor polynomial whose derivatives were
proved coupled. Smooth regularizations, derived physical inverse-distance
L2 domination, and the original weak-jet closure prove the true weak H2
domain across the selected collision. All43 component norms have explicit
bounds and the actual H2 component norm is smaller than any requested
positive tolerance at some cutoff N above any prescribed minimum.

The principal has only Z>=2 as premise and preserves the entire previous
actual scalar graph/spectral/H2/decay/KS/descent witness. The scope is the
selected nuclear index zero and original coefficient-one pair chart, with
state-selected admissible scales and radius. Actual nonzero chart cutoffs
exist at every point of the open inner physical distance patch. Triple
collision coverage, a global dictionary density, rational or computable
coefficients, graph-norm error and complete Rung2 acceptance remain outside
this declaration.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators NNReal
namespace ManyBody.S8
open TheoremT.Continuum

theorem actual_distance_chart_cutoff_exists
    {x : Configuration 2} {a : Fin 3 → ℝ} {R : ℝ}
    (hx : physicalDistanceTriple x∈ball a (R/8)) :
    ∃r : ℝ,0<r ∧ ∃χ : Configuration 2 → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀y∈tsupport χ,physicalDistanceTriple y∈closedBall a (R/8)) ∧
      ∀y∈ball x r,χ y=1 := by
  have hd : Continuous physicalDistanceTriple := continuous_pi fun j =>
    (physicalDistanceLinearMaps j).continuous.norm
  have hΩ : IsOpen (physicalDistanceTriple⁻¹' ball a (R/8)) := isOpen_ball.preimage hd
  obtain ⟨r,hr,χ,hχ,hc,hs,h1⟩ := open_exists_smooth_cutoff_at hΩ hx
  exact ⟨r,hr,χ,hχ,hc,fun y hy => ball_subset_closedBall (hs hy),h1⟩
def PhysicalDistanceTaylorH2Approximation (u : Configuration 2 → ℂ)
    (χ : Configuration 2 → ℝ) (hc : HasCompactSupport χ)
    (h : (Fin 3 → ℂ) → ℂ) (a : Fin 3 → ℝ) (R : ℝ) : Prop :=
  ∃C : ℝ, 1≤C ∧ ∀ζ : ℝ, 0<ζ → ∀N0 : ℕ, ∃N : ℕ,
    N0≤N ∧ 2≤N ∧
    ContDiffOn ℝ ∞ (ambientComplexTaylorError h a N) (ball a R) ∧
    PhysicalDistanceCutoffH2ErrorData χ hc (ambientComplexTaylorError h a N) ζ C ∧
    ∀x : Configuration 2,
      physicalCutoffDistanceValue χ (ambientComplexTaylorError h a N) x=
      χ x • (u x-complexTaylorPolynomial h (ambientRealCast a) N
        (ambientRealCast (physicalDistanceTriple x)))

theorem physical_distance_taylor_actual_H2_error_small
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {hc : HasCompactSupport χ}
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R : ℝ}
    (hdata : PhysicalDistanceTaylorH2Approximation u χ hc h a R)
    {η : ℝ} (hη : 0<η) (N0 : ℕ) :
    ∃N : ℕ,∃F : SpatialL2 2,∃d : Coordinate 2 → SpatialL2 2,
    ∃e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
      N0≤N ∧ 2≤N ∧
      F=ᵐ[volume] (fun x => χ x • (u x-complexTaylorPolynomial h (ambientRealCast a) N
        (ambientRealCast (physicalDistanceTriple x)))) ∧
      (∀k,WeakPartial F (d k) k) ∧ (∀k j,WeakPartial (d k) (e k j) j) ∧
      HasH2 F ∧ physicalH2ComponentNorm F d e<η := by
  obtain ⟨C,hC,happrox⟩ := hdata
  let B := ‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖
  have hB : 0≤B := norm_nonneg _
  have hC0 : 0≤C := (by norm_num : (0:ℝ)≤1).trans hC
  have hden : 0<1+7*C*B := by positivity
  let ζ := η/(1+7*C*B)
  have hζ : 0<ζ := div_pos hη hden
  obtain ⟨N,hN0,hN2,hg,herr,hid⟩ := happrox ζ hζ N0
  obtain ⟨F,d,e,hF,hd,he,hw1,hw2,hH2,h0,h1,h2,hNorm,hSum⟩ := herr
  have hsmall : 7*ζ*C*B<η := by
    calc _=(7*η*C*B)/(1+7*C*B) := by dsimp [ζ]; ring
         _<η := (div_lt_iff₀ hden).mpr (by nlinarith)
  refine ⟨N,F,d,e,hN0,hN2,hF.trans (Eventually.of_forall hid),hw1,hw2,hH2,?_⟩
  exact hNorm.trans_lt hsmall

#print axioms physical_distance_taylor_actual_H2_error_small
theorem actual_physical_distance_taylor_H2_approximation
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ}
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R C : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hR : 0<R)
    (hhol : AnalyticOnNhd ℂ h (ball (ambientRealCast a) R))
    (hdata : CoupledComplexDistanceTaylorData h (ambientRealCast a) R C)
    (hs : ∀x∈tsupport χ,physicalDistanceTriple x∈closedBall a (R/8))
    (hu : ∀x∈tsupport χ,u x=h (ambientRealCast (physicalDistanceTriple x))) :
    PhysicalDistanceTaylorH2Approximation u χ hc h a R := by
  obtain ⟨Cχ,hCχ,herr⟩ := actual_local_physical_distance_cutoff_H2_error hχ hc
  refine ⟨Cχ,hCχ,?_⟩
  intro ζ hζ N0
  obtain ⟨N,hN0,hN2,hg,hb⟩ := ambientComplexTaylorError_C2_arbitrarily_small hR hhol hdata N0 hζ
  refine ⟨N,hN0,hN2,hg,herr _ a R ζ hR hζ.le hg hs (fun x hx => hb _ (hs x hx)),?_⟩
  intro x
  by_cases hx : x∈tsupport χ
  · simp only [physicalCutoffDistanceValue,ambientComplexTaylorError,hu x hx]
  · simp only [physicalCutoffDistanceValue,image_eq_zero_of_notMem_tsupport hx,zero_smul]

theorem actual_nuclear_distance_taylor_H2_approximation
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {ε M A F0 W : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hε : 0<ε)
    (hδ : 0<nuclearAmbientRetainedRadius M A)
    (hrec : PhysicalNuclearAmbientReconstruction u 0 ε (nuclearAmbientRetainedRadius M A)
      (nuclearAmbientNormalizedBound M A F0 W))
    (hdata : NuclearAmbientDistanceCoupledTaylorData u 0 ε M A F0 W)
    (hs : ∀x∈tsupport χ,physicalDistanceTriple x∈closedBall (physicalNuclearDistanceCenter ε)
      (ε*nuclearAmbientRetainedRadius M A/8)) :
    PhysicalDistanceTaylorH2Approximation u χ hc (nuclearOriginalAmbientFunction u 0 ε)
      (physicalNuclearDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A) := by
  have hhol : AnalyticOnNhd ℂ (nuclearOriginalAmbientFunction u 0 ε)
      (ball (ambientRealCast (physicalNuclearDistanceCenter ε)) (ε*nuclearAmbientRetainedRadius M A)) := by
    rw [nuclear_distance_center_real_cast]
    intro q hq
    exact hrec.1 q ((nuclear_original_distance_ball_iff hε hδ q).mp hq)
  have ht := hdata.2.2.2
  rw [←nuclear_distance_center_real_cast] at ht
  exact actual_physical_distance_taylor_H2_approximation hχ hc (mul_pos hε hδ) hhol ht hs
    (fun x hx => actual_nuclear_inner_distance_reconstruction hε hδ (min_le_left _ _) hrec (hs x hx))

theorem actual_pair_distance_taylor_H2_approximation
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {ε M A F0 W δ : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hε : 0<ε) (hδ : 0<δ)
    (hrec : PhysicalPairAmbientReconstruction u ε M A F0 W δ)
    (hdata : PairAmbientDistanceCoupledTaylorData u ε M A F0 W δ)
    (hs : ∀x∈tsupport χ,physicalDistanceTriple x∈closedBall (physicalPairDistanceCenter ε) (ε*δ/8)) :
    PhysicalDistanceTaylorH2Approximation u χ hc (pairOriginalAmbientFunction u ε)
      (physicalPairDistanceCenter ε) (ε*δ) := by
  have hhol : AnalyticOnNhd ℂ (pairOriginalAmbientFunction u ε)
      (ball (ambientRealCast (physicalPairDistanceCenter ε)) (ε*δ)) := by
    rw [pair_distance_center_real_cast]
    intro q hq
    exact hrec.2.2.1 q ((pair_original_distance_ball_iff hε hδ q).mp hq)
  have ht := hdata.2.2.2
  rw [←pair_distance_center_real_cast] at ht
  exact actual_physical_distance_taylor_H2_approximation hχ hc (mul_pos hε hδ) hhol ht hs
    (fun x hx => actual_pair_inner_distance_reconstruction hε hδ hrec (hs x hx))

def PhysicalGroundDistanceTaylorH2Data (u : Configuration 2 → ℂ) (ε M A : ℝ) : Prop :=
  (∀(χ : Configuration 2 → ℝ) (_hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ),
    (∀x∈tsupport χ,physicalDistanceTriple x∈closedBall (physicalNuclearDistanceCenter ε)
      (ε*nuclearAmbientRetainedRadius M A/8)) →
    PhysicalDistanceTaylorH2Approximation u χ hc (nuclearOriginalAmbientFunction u 0 ε)
      (physicalNuclearDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A)) ∧
  (∀(χ : Configuration 2 → ℝ) (_hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ),
    (∀x∈tsupport χ,physicalDistanceTriple x∈closedBall (physicalPairDistanceCenter ε)
      (ε*pairAmbientDistanceRadius 1 M A/8)) →
    PhysicalDistanceTaylorH2Approximation u χ hc (pairOriginalAmbientFunction u ε)
      (physicalPairDistanceCenter ε) (ε*pairAmbientDistanceRadius 1 M A))

#print axioms actual_distance_chart_cutoff_exists
#print axioms actual_nuclear_distance_taylor_H2_approximation
#print axioms actual_pair_distance_taylor_H2_approximation
theorem twoElectron_scalar_ground_physical_distance_taylor_H2_approximation
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
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ε : ℝ, 0<ε → ε≤min 1 (R/4) → PhysicalGroundDistanceTaylorH2Data u ε M A) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hPairRec,hδN,hNuclear,hTaylorN,hTaylorP⟩ :=
      twoElectron_scalar_ground_ambient_distance_coupled_taylor_truncation Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hPairRec,hδN,hNuclear,hTaylorN,hTaylorP,?_⟩
  intro ε hε hlim
  constructor
  · intro χ hχ hc hs
    exact actual_nuclear_distance_taylor_H2_approximation hχ hc hε hδN
      (hNuclear ε hε hlim 0).1 (hTaylorN ε hε hlim 0) hs
  · intro χ hχ hc hs
    exact actual_pair_distance_taylor_H2_approximation hχ hc hε hδP
      (hPairRec ε hε hlim) (hTaylorP ε hε hlim) hs

#print axioms twoElectron_scalar_ground_physical_distance_taylor_H2_approximation
end ManyBody.S8