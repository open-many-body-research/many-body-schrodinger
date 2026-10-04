import ManyBody.S8.PairAmbientDistanceDerivativeBudgets
import ManyBody.S8.Internal.NuclearOriginalAmbientProfiles
import Mathlib.Tactic
/-!
# Literal nuclear distance derivative budgets

The actual original-state nuclear distance profiles have factorial bounds for their
genuine complex iterated Frechet derivatives on the half polydisc.  The proof uses
the actual holomorphic profiles and full-polydisc bounds, with the Pi max norm on
the three complex distance variables.  The original A and full H retain the value
at the triple origin only at derivative order zero; B carries no extra scale
factor.

The ground-state consumer discharges the analytic and boundedness hypotheses for
the same physical representative at every admissible positive scale and both
selected nuclear indices.  Its radius and amplitude budgets may depend on the
selected normalized ground state.  These are distance-coordinate derivatives;
no electron Cartesian norm identification or global atlas conclusion is made.
-/

set_option autoImplicit false
noncomputable section
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin
open scoped ContDiff NNReal BigOperators Topology
open MeasureTheory Metric
namespace ManyBody.S8

def nuclearOriginalDistanceCenter (ε : ℝ) : Fin 3 → ℂ := ![0,(ε:ℂ),(ε:ℂ)]

theorem nuclear_original_distance_ball_iff {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (q : Fin 3 → ℂ) :
    q∈ball (nuclearOriginalDistanceCenter ε) (ε*δ) ↔
      q∈nuclearOriginalDistancePolydisc ε δ := by
  rw [mem_ball,dist_eq_norm,pi_norm_lt_iff (mul_pos hε hδ)]
  constructor
  · intro h
    exact ⟨by simpa [nuclearOriginalDistanceCenter] using h 0,
      by simpa [nuclearOriginalDistanceCenter] using h 1,
      by simpa [nuclearOriginalDistanceCenter] using h 2⟩
  · rintro ⟨h0,h1,h2⟩ j
    fin_cases j
    · simpa [nuclearOriginalDistanceCenter] using h0
    · simpa [nuclearOriginalDistanceCenter] using h1
    · simpa [nuclearOriginalDistanceCenter] using h2

def nuclearOriginalCenteredA (u : Configuration 2 → ℂ) (i : Fin 2) (ε : ℝ)
    (q : Fin 3 → ℂ) : ℂ := nuclearOriginalAmbientA u i ε q-u 0

def nuclearOriginalCenteredFunction (u : Configuration 2 → ℂ) (i : Fin 2) (ε : ℝ)
    (q : Fin 3 → ℂ) : ℂ :=
  nuclearOriginalCenteredA u i ε q+q 0*nuclearOriginalAmbientB u i ε q

def NuclearAmbientDistanceDerivativeData (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε M A F0 W : ℝ) : Prop :=
  let δ := nuclearAmbientRetainedRadius M A
  ∀ q : Fin 3 → ℂ, ‖q-nuclearOriginalDistanceCenter ε‖<ε*δ/2 → ∀ n : ℕ,
    ‖iteratedFDeriv ℂ n (nuclearOriginalAmbientA u i ε) q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        (16*physicalKSPointwiseAmplitude M A F0 W)*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖iteratedFDeriv ℂ n (nuclearOriginalAmbientB u i ε) q‖≤
      (ε⁻¹)^n*((32*(7*physicalKSPointwiseRate M A)^2)*
        (16*physicalKSPointwiseAmplitude M A F0 W))*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖iteratedFDeriv ℂ n (nuclearOriginalAmbientFunction u i ε) q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        nuclearAmbientNormalizedBound M A F0 W*(2*Real.exp 1/δ)^n*(n.factorial:ℝ)

theorem nuclear_ambient_distance_derivative_data
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A)
    (haxis : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A)) :
    NuclearAmbientDistanceDerivativeData u i ε M A F0 W := by
  let δ := nuclearAmbientRetainedRadius M A
  have hδ : 0<δ := nuclearAmbientRetainedRadius_pos hA
  obtain ⟨hAnA,hAnB⟩ := nuclearOriginalAmbient_profiles_analytic u i hε hA haxis
  have hBound := nuclearOriginalAmbient_profiles_bounds u i hε hA haxis
  have hanA : AnalyticOnNhd ℂ (nuclearOriginalCenteredA u i ε)
      (ball (nuclearOriginalDistanceCenter ε) (ε*δ)) := by
    intro q hq
    exact (hAnA q ((nuclear_original_distance_ball_iff hε hδ q).mp hq)).sub analyticAt_const
  have hanB : AnalyticOnNhd ℂ (nuclearOriginalAmbientB u i ε)
      (ball (nuclearOriginalDistanceCenter ε) (ε*δ)) :=
    fun q hq => hAnB q ((nuclear_original_distance_ball_iff hε hδ q).mp hq)
  have hanH : AnalyticOnNhd ℂ (nuclearOriginalCenteredFunction u i ε)
      (ball (nuclearOriginalDistanceCenter ε) (ε*δ)) := by
    intro q hq
    have hcoord : AnalyticAt ℂ (fun p : Fin 3 → ℂ => p 0) q :=
      (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q
    exact (hanA q hq).add (hcoord.mul (hanB q hq))
  have hb (q : Fin 3 → ℂ) (hq : q∈ball (nuclearOriginalDistanceCenter ε) (ε*δ)) :
      ‖nuclearOriginalCenteredA u i ε q‖≤ε*(16*physicalKSPointwiseAmplitude M A F0 W) ∧
      ‖nuclearOriginalAmbientB u i ε q‖≤
        (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W) ∧
      ‖nuclearOriginalCenteredFunction u i ε q‖≤ε*nuclearAmbientNormalizedBound M A F0 W := by
    have hdom := (nuclear_original_distance_ball_iff hε hδ q).mp hq
    obtain ⟨hbA,hbB,_⟩ := hBound q hdom
    refine ⟨hbA,hbB,?_⟩
    calc
      _≤‖nuclearOriginalCenteredA u i ε q‖+‖q 0*nuclearOriginalAmbientB u i ε q‖ := norm_add_le _ _
      _=‖nuclearOriginalCenteredA u i ε q‖+‖q 0‖*‖nuclearOriginalAmbientB u i ε q‖ := by rw [norm_mul]
      _≤ε*(16*physicalKSPointwiseAmplitude M A F0 W)+ε*δ*
          ((32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W)) :=
        add_le_add hbA (mul_le_mul hdom.1.le hbB (norm_nonneg _) (mul_pos hε hδ).le)
      _=_ := by dsimp [nuclearAmbientNormalizedBound,δ]; ring
  have hcenter : nuclearOriginalDistanceCenter ε∈ball (nuclearOriginalDistanceCenter ε) (ε*δ) :=
    mem_ball_self (mul_pos hε hδ)
  have hCA : 0≤ε*(16*physicalKSPointwiseAmplitude M A F0 W) :=
    (norm_nonneg _).trans (hb _ hcenter).1
  have hCB : 0≤(32*(7*physicalKSPointwiseRate M A)^2)*
      (16*physicalKSPointwiseAmplitude M A F0 W) := (norm_nonneg _).trans (hb _ hcenter).2.1
  have hCH : 0≤ε*nuclearAmbientNormalizedBound M A F0 W :=
    (norm_nonneg _).trans (hb _ hcenter).2.2
  intro q hq n
  have hAn := holomorphic_constant_add_half_ball_bound (u 0) (mul_pos hε hδ) hCA hq hanA
    (fun p hp => (hb p hp).1) n
  have hBn := holomorphic_iteratedFDeriv_half_ball_bound (mul_pos hε hδ) hCB hq hanB
    (fun p hp => (hb p hp).2.1) n
  have hHn := holomorphic_constant_add_half_ball_bound (u 0) (mul_pos hε hδ) hCH hq hanH
    (fun p hp => (hb p hp).2.2) n
  have hfunA : (fun p => u 0+nuclearOriginalCenteredA u i ε p)=nuclearOriginalAmbientA u i ε := by
    funext p; dsimp [nuclearOriginalCenteredA]; ring
  have hfunH : (fun p => u 0+nuclearOriginalCenteredFunction u i ε p)=
      nuclearOriginalAmbientFunction u i ε := by
    funext p
    rw [nuclearOriginalAmbient_profiles_recombine u i hε p]
    dsimp [nuclearOriginalCenteredFunction,nuclearOriginalCenteredA]
    ring
  rw [hfunA] at hAn
  rw [hfunH] at hHn
  have hrate : 2*Real.exp 1/(ε*δ)=ε⁻¹*(2*Real.exp 1/δ) := by field_simp
  rw [hrate,mul_pow] at hAn hBn hHn
  refine ⟨?_,?_,?_⟩
  · convert hAn using 1; ring
  · convert hBn using 1; ring
  · convert hHn using 1; ring

theorem nuclear_ambient_distance_coordinate_word_budgets
    {u : Configuration 2 → ℂ} {i : Fin 2} {ε M A F0 W : ℝ}
    (hdata : NuclearAmbientDistanceDerivativeData u i ε M A F0 W)
    (q : Fin 3 → ℂ)
    (hq : ‖q-nuclearOriginalDistanceCenter ε‖<ε*nuclearAmbientRetainedRadius M A/2)
    {n : ℕ} (w : Fin n → Fin 3) :
    ‖ambientDistanceWordDerivative (nuclearOriginalAmbientA u i ε) w q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        (16*physicalKSPointwiseAmplitude M A F0 W)*
        (2*Real.exp 1/nuclearAmbientRetainedRadius M A)^n*(n.factorial:ℝ) ∧
    ‖ambientDistanceWordDerivative (nuclearOriginalAmbientB u i ε) w q‖≤
      (ε⁻¹)^n*((32*(7*physicalKSPointwiseRate M A)^2)*
        (16*physicalKSPointwiseAmplitude M A F0 W))*
        (2*Real.exp 1/nuclearAmbientRetainedRadius M A)^n*(n.factorial:ℝ) ∧
    ‖ambientDistanceWordDerivative (nuclearOriginalAmbientFunction u i ε) w q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        nuclearAmbientNormalizedBound M A F0 W*
        (2*Real.exp 1/nuclearAmbientRetainedRadius M A)^n*(n.factorial:ℝ) :=
  ⟨(ambientDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).1,
    (ambientDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).2.1,
    (ambientDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).2.2⟩

#print axioms nuclear_ambient_distance_derivative_data
#print axioms nuclear_ambient_distance_coordinate_word_budgets
theorem twoElectron_scalar_ground_nuclear_ambient_distance_derivative_budgets
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
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδ,hambient,hrec⟩ :=
      twoElectron_scalar_ground_pair_ambient_distance_reconstruction Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδ,hambient,hrec,nuclearAmbientRetainedRadius_pos hA,?_⟩
  intro ε hε hlim i
  have ht : ‖nuclearDistanceRealSpectator (1:ℝ)‖=1 :=
    nuclearDistanceRealSpectator_norm (by norm_num)
  exact ⟨nuclear_original_ambient_positive_rescaling u i hε hA hF0
    (hN ε hε hlim i _ ht).1.1.1 hrotation,
    nuclear_ambient_distance_derivative_data u i hε hA (hNA ε hε hlim i)⟩

#print axioms twoElectron_scalar_ground_nuclear_ambient_distance_derivative_budgets

end ManyBody.S8
