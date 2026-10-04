import ManyBody.S8.AmbientRationalDistanceApproximation
import ManyBody.S8.Internal.RationalCollisionStructure
/-! Rational distance polynomials preserving genuine nuclear/pair collision structure.

For the same actual normalized physical Coulomb ground state at Z >= 2,
every admissible chart scale has two globally selected-distance-even rational
polynomials PA and PB. Their ONE reconstruction PA+q_j PB approximates the
actual original H, while PA/PB approximate the actual original A/B, in value
and real first/second multilinear operator norms on a closed inner box.
The reconstruction itself has a proved finite rational monomial dictionary.
All profile analyticity, parity and approximation data are derived from the
unchanged original graph witness. No physical H2 composition error, global
dictionary, computable selection or full Rung 2 completion is asserted. -/
set_option autoImplicit false
noncomputable section
open TheoremT.Continuum
open scoped Topology NNReal
open MeasureTheory Metric
namespace ManyBody.S8

def NuclearStructuredRationalDistanceC2Data (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε δ : ℝ) : Prop :=
  RationalCollisionStructureC2Data
    (ambientRealScalarProfile (nuclearOriginalAmbientA u i ε))
    (ambientRealScalarProfile (nuclearOriginalAmbientB u i ε))
    (ambientRealScalarProfile (nuclearOriginalAmbientFunction u i ε))
    0 (nuclearOriginalRealDistanceCenter ε) (ε*δ/8)

def PairStructuredRationalDistanceC2Data (u : Configuration 2 → ℂ)
    (ε δ : ℝ) : Prop :=
  RationalCollisionStructureC2Data
    (ambientRealScalarProfile (pairOriginalAmbientA u ε))
    (ambientRealScalarProfile (pairOriginalAmbientB u ε))
    (ambientRealScalarProfile (pairOriginalAmbientFunction u ε))
    2 (pairOriginalRealDistanceCenter ε) (ε*δ/8)

theorem ambientRealCast_realDistanceReflect (j : Fin 3) (p : Fin 3 → ℝ) :
    ambientRealCast (realDistanceReflectCLM j p)=ambientCoordinateReflect j (ambientRealCast p) := by
  ext k
  by_cases hk : k=j <;> simp [realDistanceReflectCLM_apply,ambientCoordinateReflect,hk]

theorem ambientRealScalarProfile_analytic {f : (Fin 3 → ℂ) → ℂ} {p : Fin 3 → ℝ}
    (hf : AnalyticAt ℂ f (ambientRealCast p)) :
    AnalyticAt ℝ (ambientRealScalarProfile f) p :=
  (Complex.reCLM.analyticAt (f (ambientRealCast p))).comp (f:=f ∘ ambientRealCast) (x:=p) (ambient_real_profile_analytic hf)

theorem nuclear_structured_rational_distance_C2_data
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A)
    (haxis : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (happrox : NuclearRationalDistanceC2ApproximationData u i ε (nuclearAmbientRetainedRadius M A)) :
    NuclearStructuredRationalDistanceC2Data u i ε (nuclearAmbientRetainedRadius M A) := by
  have hδ := nuclearAmbientRetainedRadius_pos (M:=M) hA
  have hprofiles := nuclearOriginalAmbient_profiles_analytic u i hε hA haxis
  have hpfull (p : Fin 3 → ℝ)
      (hp : ‖p-nuclearOriginalRealDistanceCenter ε‖≤ε*nuclearAmbientRetainedRadius M A/8) :
      ambientRealCast p∈nuclearOriginalDistancePolydisc ε (nuclearAmbientRetainedRadius M A) := by
    apply (nuclear_original_distance_ball_iff hε hδ _).mp
    rw [mem_ball,dist_eq_norm,←nuclear_real_distance_center_cast,←map_sub,ambientRealCast_norm]
    nlinarith [mul_pos hε hδ]
  have heq : ambientRealScalarProfile (nuclearOriginalAmbientFunction u i ε)=
      fun p : Fin 3 → ℝ =>
        ambientRealScalarProfile (nuclearOriginalAmbientA u i ε) p+
          p 0*ambientRealScalarProfile (nuclearOriginalAmbientB u i ε) p := by
    funext p
    simp only [ambientRealScalarProfile,nuclearOriginalAmbient_profiles_recombine u i hε,
      Complex.add_re,Complex.mul_re,ambientRealCast_apply,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
  apply rational_collision_structure_C2 (H:=ambientRealScalarProfile (nuclearOriginalAmbientFunction u i ε))
    0 (by positivity) (by simp [nuclearOriginalRealDistanceCenter]) ?_ ?_ ?_ ?_ heq
    happrox.1 happrox.2.1
  · intro p hp
    exact ambientRealScalarProfile_analytic (hprofiles.1 _ (hpfull p hp))
  · intro p hp
    exact ambientRealScalarProfile_analytic (hprofiles.2 _ (hpfull p hp))
  · intro p
    simp only [ambientRealScalarProfile,ambientRealCast_realDistanceReflect]
    rw [(nuclearOriginalAmbient_profiles_even u i ε (ambientRealCast p)).1]
  · intro p
    simp only [ambientRealScalarProfile,ambientRealCast_realDistanceReflect]
    rw [(nuclearOriginalAmbient_profiles_even u i ε (ambientRealCast p)).2]

theorem pair_structured_rational_distance_C2_data
    (u : Configuration 2 → ℂ) {ε M A F0 W δ : ℝ}
    (hε : 0<ε) (hδ : 0<δ)
    (hrec : PhysicalPairAmbientReconstruction u ε M A F0 W δ)
    (happrox : PairRationalDistanceC2ApproximationData u ε δ) :
    PairStructuredRationalDistanceC2Data u ε δ := by
  have hpfull (p : Fin 3 → ℝ)
      (hp : ‖p-pairOriginalRealDistanceCenter ε‖≤ε*δ/8) :
      ambientRealCast p∈pairOriginalDistancePolydisc ε δ := by
    apply (pair_original_distance_ball_iff hε hδ _).mp
    rw [mem_ball,dist_eq_norm,←pair_real_distance_center_cast,←map_sub,ambientRealCast_norm]
    nlinarith [mul_pos hε hδ]
  have heq : ambientRealScalarProfile (pairOriginalAmbientFunction u ε)=
      fun p : Fin 3 → ℝ =>
        ambientRealScalarProfile (pairOriginalAmbientA u ε) p+
          p 2*ambientRealScalarProfile (pairOriginalAmbientB u ε) p := by
    funext p
    simp only [ambientRealScalarProfile,pairOriginalAmbientFunction,Complex.add_re,
      Complex.mul_re,ambientRealCast_apply,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  apply rational_collision_structure_C2 (H:=ambientRealScalarProfile (pairOriginalAmbientFunction u ε))
    2 (by positivity) (by simp [pairOriginalRealDistanceCenter]) ?_ ?_ ?_ ?_ heq
    happrox.1 happrox.2.1
  · intro p hp
    exact ambientRealScalarProfile_analytic (hrec.1 _ (hpfull p hp))
  · intro p hp
    exact ambientRealScalarProfile_analytic (hrec.2.1 _ (hpfull p hp))
  · intro p
    simp only [ambientRealScalarProfile,ambientRealCast_realDistanceReflect]
    rw [(pairOriginalAmbient_profiles_even u ε (ambientRealCast p)).1]
  · intro p
    simp only [ambientRealScalarProfile,ambientRealCast_realDistanceReflect]
    rw [(pairOriginalAmbient_profiles_even u ε (ambientRealCast p)).2]

#print axioms nuclear_structured_rational_distance_C2_data
#print axioms pair_structured_rational_distance_C2_data
theorem twoElectron_scalar_ground_structured_rational_distance_C2_approximation
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
          NuclearStructuredRationalDistanceC2Data u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairStructuredRationalDistanceC2Data u ε (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,hRN,hRP⟩ :=
      twoElectron_scalar_ground_real_rational_distance_C2_approximation Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,hRN,hRP,?_,?_⟩
  · intro ε hε hlim i
    exact nuclear_structured_rational_distance_C2_data u i hε hA (hNA ε hε hlim i) (hRN ε hε hlim i)
  · intro ε hε hlim
    exact pair_structured_rational_distance_C2_data u hε hδP (hrec ε hε hlim) (hRP ε hε hlim)

#print axioms twoElectron_scalar_ground_structured_rational_distance_C2_approximation
end ManyBody.S8
