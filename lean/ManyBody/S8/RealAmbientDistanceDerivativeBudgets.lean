import ManyBody.S8.NuclearAmbientDistanceDerivativeBudgets
import ManyBody.S8.Internal.AmbientRealDerivativeTransport
import Mathlib.Tactic
/-! Genuine real derivative budgets for literal original nuclear and pair profiles.

The real distance functions are the unchanged complex profiles composed with
the actual coordinatewise cast CLM.  Scalar restriction of their genuine analytic
series transports every ordered derivative exactly and bounds the real
multilinear operator norm by its complex counterpart.  Both spaces use their
actual three-coordinate Pi maximum norm.

The physical endpoint chooses the same normalized scalar Coulomb ground
representative as S8-029 and retains all of its graph, spectrum, weak H2 decay,
KS descent and original pair/nuclear reconstruction facts.  It derives all real
operator and coordinate-word estimates from those actual profiles, without
assuming any derivative budget.  The scale and zero-order constant factors
remain literal.  This is a local distance-coordinate extension, including
negative real coordinates in the analytic continuation; physical reconstruction
continues to apply precisely on the earlier actual distance domain.
-/
set_option autoImplicit false
noncomputable section
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin
open scoped ContDiff NNReal BigOperators Topology
open MeasureTheory Metric
namespace ManyBody.S8
def nuclearOriginalRealDistanceCenter (ε : ℝ) : Fin 3 → ℝ := ![0,ε,ε]
def pairOriginalRealDistanceCenter (ε : ℝ) : Fin 3 → ℝ := ![ε,ε,0]

theorem nuclear_real_distance_center_cast (ε : ℝ) :
    ambientRealCast (nuclearOriginalRealDistanceCenter ε)=nuclearOriginalDistanceCenter ε := by
  ext j
  fin_cases j <;> simp [nuclearOriginalRealDistanceCenter,nuclearOriginalDistanceCenter]

theorem pair_real_distance_center_cast (ε : ℝ) :
    ambientRealCast (pairOriginalRealDistanceCenter ε)=pairOriginalDistanceCenter ε := by
  ext j
  fin_cases j <;> simp [pairOriginalRealDistanceCenter,pairOriginalDistanceCenter]

theorem nuclear_real_distance_center_norm (p : Fin 3 → ℝ) (ε : ℝ) :
    ‖ambientRealCast p-nuclearOriginalDistanceCenter ε‖=‖p-nuclearOriginalRealDistanceCenter ε‖ := by
  rw [←nuclear_real_distance_center_cast,←map_sub,ambientRealCast_norm]

theorem pair_real_distance_center_norm (p : Fin 3 → ℝ) (ε : ℝ) :
    ‖ambientRealCast p-pairOriginalDistanceCenter ε‖=‖p-pairOriginalRealDistanceCenter ε‖ := by
  rw [←pair_real_distance_center_cast,←map_sub,ambientRealCast_norm]

def PairRealAmbientDistanceDerivativeData (u : Configuration 2 → ℂ)
    (ε M A F0 W δ : ℝ) : Prop :=
  ∀ q : Fin 3 → ℝ, ‖q-pairOriginalRealDistanceCenter ε‖<ε*δ/2 → ∀ n : ℕ,
    ‖iteratedFDeriv ℝ n (pairOriginalAmbientA u ε ∘ ambientRealCast) q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        (16*physicalKSPointwiseAmplitude M A F0 W)*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖iteratedFDeriv ℝ n (pairOriginalAmbientB u ε ∘ ambientRealCast) q‖≤
      (ε⁻¹)^n*((32*(7*physicalKSPointwiseRate M A)^2)*
        (16*physicalKSPointwiseAmplitude M A F0 W))*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖iteratedFDeriv ℝ n (pairOriginalAmbientFunction u ε ∘ ambientRealCast) q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        pairAmbientNormalizedBound M A F0 W δ*(2*Real.exp 1/δ)^n*(n.factorial:ℝ)

def NuclearRealAmbientDistanceDerivativeData (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε M A F0 W : ℝ) : Prop :=
  let δ := nuclearAmbientRetainedRadius M A
  ∀ q : Fin 3 → ℝ, ‖q-nuclearOriginalRealDistanceCenter ε‖<ε*δ/2 → ∀ n : ℕ,
    ‖iteratedFDeriv ℝ n (nuclearOriginalAmbientA u i ε ∘ ambientRealCast) q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        (16*physicalKSPointwiseAmplitude M A F0 W)*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖iteratedFDeriv ℝ n (nuclearOriginalAmbientB u i ε ∘ ambientRealCast) q‖≤
      (ε⁻¹)^n*((32*(7*physicalKSPointwiseRate M A)^2)*
        (16*physicalKSPointwiseAmplitude M A F0 W))*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖iteratedFDeriv ℝ n (nuclearOriginalAmbientFunction u i ε ∘ ambientRealCast) q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        nuclearAmbientNormalizedBound M A F0 W*(2*Real.exp 1/δ)^n*(n.factorial:ℝ)


theorem pair_real_ambient_distance_derivative_data
    (u : Configuration 2 → ℂ) {ε M A F0 W δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hdata : PairAmbientPhysicalAnalyticData (originScaledDifference u ε) 1 M A F0 W δ) :
    PairRealAmbientDistanceDerivativeData u ε M A F0 W δ := by
  have hcomplex := pair_ambient_distance_derivative_data u hε hδ hdata
  have hrec := pair_original_ambient_positive_rescaling u hε hδ hdata
  intro p hp n
  have hpc : ‖ambientRealCast p-pairOriginalDistanceCenter ε‖<ε*δ/2 := by
    rw [pair_real_distance_center_norm]
    exact hp
  have hpfull : ambientRealCast p∈{q : Fin 3 → ℂ | ‖q 0-(ε:ℂ)‖<ε*δ ∧
      ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2‖<ε*δ} := by
    apply (pair_original_distance_ball_iff hε hδ _).mp
    rw [mem_ball,dist_eq_norm]
    have hrad : 0<ε*δ := mul_pos hε hδ
    linarith
  exact ⟨(ambient_real_iteratedFDeriv_norm_le_complex (hrec.1 _ hpfull) n).trans
      (hcomplex _ hpc n).1,
    (ambient_real_iteratedFDeriv_norm_le_complex (hrec.2.1 _ hpfull) n).trans
      (hcomplex _ hpc n).2.1,
    (ambient_real_iteratedFDeriv_norm_le_complex (hrec.2.2.1 _ hpfull) n).trans
      (hcomplex _ hpc n).2.2⟩

theorem nuclear_real_ambient_distance_derivative_data
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A)
    (haxis : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A)) :
    NuclearRealAmbientDistanceDerivativeData u i ε M A F0 W := by
  have hcomplex := nuclear_ambient_distance_derivative_data u i hε hA haxis
  obtain ⟨hAnA,hAnB⟩ := nuclearOriginalAmbient_profiles_analytic u i hε hA haxis
  intro p hp n
  have hδ := nuclearAmbientRetainedRadius_pos (M:=M) hA
  have hpc : ‖ambientRealCast p-nuclearOriginalDistanceCenter ε‖<
      ε*nuclearAmbientRetainedRadius M A/2 := by
    rw [nuclear_real_distance_center_norm]
    exact hp
  have hpfull : ambientRealCast p∈nuclearOriginalDistancePolydisc ε
      (nuclearAmbientRetainedRadius M A) := by
    apply (nuclear_original_distance_ball_iff hε hδ _).mp
    rw [mem_ball,dist_eq_norm]
    have hrad : 0<ε*nuclearAmbientRetainedRadius M A := mul_pos hε hδ
    linarith
  have hAnH : AnalyticAt ℂ (nuclearOriginalAmbientFunction u i ε) (ambientRealCast p) := by
    have heq : nuclearOriginalAmbientFunction u i ε=
        fun q => nuclearOriginalAmbientA u i ε q+q 0*nuclearOriginalAmbientB u i ε q := by
      funext q
      exact nuclearOriginalAmbient_profiles_recombine u i hε q
    rw [heq]
    have hcoord : AnalyticAt ℂ (fun q : Fin 3 → ℂ => q 0) (ambientRealCast p) :=
      (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt _
    exact (hAnA _ hpfull).add (hcoord.mul (hAnB _ hpfull))
  exact ⟨(ambient_real_iteratedFDeriv_norm_le_complex (hAnA _ hpfull) n).trans
      (hcomplex _ hpc n).1,
    (ambient_real_iteratedFDeriv_norm_le_complex (hAnB _ hpfull) n).trans
      (hcomplex _ hpc n).2.1,
    (ambient_real_iteratedFDeriv_norm_le_complex hAnH n).trans
      (hcomplex _ hpc n).2.2⟩

theorem pair_real_ambient_distance_coordinate_word_budgets
    {u : Configuration 2 → ℂ} {ε M A F0 W δ : ℝ}
    (hdata : PairRealAmbientDistanceDerivativeData u ε M A F0 W δ)
    (q : Fin 3 → ℝ) (hq : ‖q-pairOriginalRealDistanceCenter ε‖<ε*δ/2)
    {n : ℕ} (w : Fin n → Fin 3) :
    ‖ambientRealDistanceWordDerivative (pairOriginalAmbientA u ε) w q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        (16*physicalKSPointwiseAmplitude M A F0 W)*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖ambientRealDistanceWordDerivative (pairOriginalAmbientB u ε) w q‖≤
      (ε⁻¹)^n*((32*(7*physicalKSPointwiseRate M A)^2)*
        (16*physicalKSPointwiseAmplitude M A F0 W))*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) ∧
    ‖ambientRealDistanceWordDerivative (pairOriginalAmbientFunction u ε) w q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        pairAmbientNormalizedBound M A F0 W δ*(2*Real.exp 1/δ)^n*(n.factorial:ℝ) :=
  ⟨(ambientRealDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).1,
    (ambientRealDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).2.1,
    (ambientRealDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).2.2⟩
theorem nuclear_real_ambient_distance_coordinate_word_budgets
    {u : Configuration 2 → ℂ} {i : Fin 2} {ε M A F0 W : ℝ}
    (hdata : NuclearRealAmbientDistanceDerivativeData u i ε M A F0 W)
    (q : Fin 3 → ℝ)
    (hq : ‖q-nuclearOriginalRealDistanceCenter ε‖<ε*nuclearAmbientRetainedRadius M A/2)
    {n : ℕ} (w : Fin n → Fin 3) :
    ‖ambientRealDistanceWordDerivative (nuclearOriginalAmbientA u i ε) w q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        (16*physicalKSPointwiseAmplitude M A F0 W)*
        (2*Real.exp 1/nuclearAmbientRetainedRadius M A)^n*(n.factorial:ℝ) ∧
    ‖ambientRealDistanceWordDerivative (nuclearOriginalAmbientB u i ε) w q‖≤
      (ε⁻¹)^n*((32*(7*physicalKSPointwiseRate M A)^2)*
        (16*physicalKSPointwiseAmplitude M A F0 W))*
        (2*Real.exp 1/nuclearAmbientRetainedRadius M A)^n*(n.factorial:ℝ) ∧
    ‖ambientRealDistanceWordDerivative (nuclearOriginalAmbientFunction u i ε) w q‖≤
      (if n=0 then ‖u 0‖ else 0)+ε*(ε⁻¹)^n*
        nuclearAmbientNormalizedBound M A F0 W*
        (2*Real.exp 1/nuclearAmbientRetainedRadius M A)^n*(n.factorial:ℝ) :=
  ⟨(ambientRealDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).1,
    (ambientRealDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).2.1,
    (ambientRealDistanceWordDerivative_norm_le _ w q).trans (hdata q hq n).2.2⟩
#print axioms pair_real_ambient_distance_derivative_data
#print axioms nuclear_real_ambient_distance_derivative_data
#print axioms pair_real_ambient_distance_coordinate_word_budgets
#print axioms nuclear_real_ambient_distance_coordinate_word_budgets
theorem twoElectron_scalar_ground_real_ambient_distance_derivative_budgets
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
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData⟩ :=
      twoElectron_scalar_ground_nuclear_ambient_distance_derivative_budgets Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,?_,?_⟩
  · intro ε hε hlim
    exact ⟨pair_ambient_distance_derivative_data u hε hδP (hambient ε hε hlim),
      pair_real_ambient_distance_derivative_data u hε hδP (hambient ε hε hlim)⟩
  · intro ε hε hlim i
    exact nuclear_real_ambient_distance_derivative_data u i hε hA (hNA ε hε hlim i)

#print axioms twoElectron_scalar_ground_real_ambient_distance_derivative_budgets

end ManyBody.S8
