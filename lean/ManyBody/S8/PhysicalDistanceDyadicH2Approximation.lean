import ManyBody.S8.AmbientDyadicRationalDistanceDictionary
import ManyBody.S8.PhysicalDistanceTaylorH2Approximation
import ManyBody.S8.Internal.RealDistanceComplexError
import Mathlib.Tactic
/-! Actual local physical weak H2 approximation by finite dyadic rational distance polynomials.

The same actual scalar Coulomb ground witness is retained. Genuine full-ball
profile reality and the real-to-complex isometry transport the actual S8-050
value, first and second real Frechet error bounds to the complex profile.
The unchanged physical regularization, compact inverse-distance L2 domination
and weak-jet closure then derive all43 true weak error components across the
selected collision. No C2, weak-H2 or physical approximation input is assumed
by the principal, whose only premise is Z>=2.

A common cutoff constant and chart offset precede every precision p. The
literal canonical dictionary is rounded by the proved dyadic floor rule at
N=2(p+1)+m+2, denominator exponent15p+7m+33, with at mostN^3 monomials.
The actual43-component H2 error is at most7*C*budgetNorm*2^(-p) and becomes
smaller than any positive requested tolerance. The approximating H polynomial
is independent of rounded A/B; structural coupling, global density, effective
coefficient extraction or order selection, graph error and fullRung2 are not
claimed. Nuclear physical H2 coverage is index0 and the pair chart uses the
unchanged original coefficient1 normalization. Local cutoffs are the genuine
nonvacuous cutoffs from S8-041; admissible scales remain state-selected.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators NNReal
namespace ManyBody.S8
open TheoremT.Continuum

def physicalDyadicDistanceOrder (m p : ℕ) : ℕ := 2*(p+1)+m+2

def physicalDyadicDistanceBits (m p : ℕ) : ℕ := (p+1)+4+7*physicalDyadicDistanceOrder m p

def physicalDyadicDistanceSupport (h : (Fin 3 → ℂ) → ℂ) (a : Fin 3 → ℝ)
    (m p : ℕ) : Finset DistanceMultiIndex :=
  realTaylorDistanceDictionarySupport (ambientRealScalarProfile h) a (physicalDyadicDistanceOrder m p)

def physicalDyadicDistanceCoefficient (h : (Fin 3 → ℂ) → ℂ) (a : Fin 3 → ℝ)
    (m p : ℕ) (α : DistanceMultiIndex) : ℚ :=
  dyadicDistanceCoefficient (physicalDyadicDistanceBits m p)
    (realTaylorDistanceDictionaryCoefficient (ambientRealScalarProfile h) a (physicalDyadicDistanceOrder m p) α)

def physicalDyadicDistancePolynomial (h : (Fin 3 → ℂ) → ℂ) (a : Fin 3 → ℝ)
    (m p : ℕ) : (Fin 3 → ℝ) → ℝ :=
  realDistancePolynomial (physicalDyadicDistanceSupport h a m p)
    (fun α => (physicalDyadicDistanceCoefficient h a m p α : ℝ))

def physicalDyadicDistanceError (h : (Fin 3 → ℂ) → ℂ) (a : Fin 3 → ℝ)
    (m p : ℕ) : (Fin 3 → ℝ) → ℂ :=
  realDistanceComplexError (ambientRealScalarProfile h) (physicalDyadicDistancePolynomial h a m p)

def PhysicalDistanceDyadicH2Approximation (u : Configuration 2 → ℂ)
    (χ : Configuration 2 → ℝ) (hc : HasCompactSupport χ)
    (h : (Fin 3 → ℂ) → ℂ) (a : Fin 3 → ℝ) (R : ℝ) : Prop :=
  ∃C : ℝ,1≤C ∧ ∃m : ℕ,∀p : ℕ,
    (physicalDyadicDistanceSupport h a m p).card≤(physicalDyadicDistanceOrder m p)^3 ∧
    (∀α∈physicalDyadicDistanceSupport h a m p,(∑j : Fin 3,α j)<physicalDyadicDistanceOrder m p) ∧
    (∀α∈physicalDyadicDistanceSupport h a m p,∀j : Fin 3,α j<physicalDyadicDistanceOrder m p) ∧
    ContDiffOn ℝ ∞ (physicalDyadicDistanceError h a m p) (ball a R) ∧
    PhysicalDistanceCutoffH2ErrorData χ hc (physicalDyadicDistanceError h a m p) ((1/2:ℝ)^p) C ∧
    ∀x : Configuration 2,
      physicalCutoffDistanceValue χ (physicalDyadicDistanceError h a m p) x=
      χ x • (u x-(physicalDyadicDistancePolynomial h a m p (physicalDistanceTriple x) : ℂ))

theorem actual_physical_distance_dyadic_H2_approximation
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ}
    {aProf bProf h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hR : 0<R)
    (hhol : AnalyticOnNhd ℂ h (ball (ambientRealCast a) R))
    (hreal : ∀q∈ball a R,(h (ambientRealCast q)).im=0)
    (hdata : RealThreeProfilesDyadicRationalDictionaryData aProf bProf h a R)
    (hs : ∀x∈tsupport χ,physicalDistanceTriple x∈closedBall a (R/8))
    (hu : ∀x∈tsupport χ,u x=h (ambientRealCast (physicalDistanceTriple x))) :
    PhysicalDistanceDyadicH2Approximation u χ hc h a R := by
  obtain ⟨Cχ,hCχ,herr⟩ := actual_local_physical_distance_cutoff_H2_error hχ hc
  obtain ⟨m,hm⟩ := hdata
  have hg : ContDiffOn ℝ ∞ (ambientRealScalarProfile h) (ball a R) := by
    apply AnalyticOnNhd.contDiffOn_of_completeSpace
    intro q hq
    have hqc : ambientRealCast q∈ball (ambientRealCast a) R := by
      rw [mem_ball,dist_eq_norm,←map_sub,ambientRealCast_norm]
      simpa only [mem_ball,dist_eq_norm] using hq
    exact Complex.reCLM.analyticAt _ |>.comp (ambient_real_profile_analytic (hhol _ hqc))
  refine ⟨Cχ,hCχ,m,?_⟩
  intro p
  obtain ⟨hcard,hdegree,hcoord,herror⟩ := hm p 2
  change (physicalDyadicDistanceSupport h a m p).card≤(physicalDyadicDistanceOrder m p)^3 at hcard
  change ∀α∈physicalDyadicDistanceSupport h a m p,(∑j : Fin 3,α j)<physicalDyadicDistanceOrder m p at hdegree
  change ∀α∈physicalDyadicDistanceSupport h a m p,∀j : Fin 3,α j<physicalDyadicDistanceOrder m p at hcoord
  change ∀q : Fin 3 → ℝ,‖q-a‖≤R/8 → ∀k : Fin 3,
    ‖iteratedFDeriv ℝ (k:ℕ) (ambientRealScalarProfile h) q-
      iteratedFDeriv ℝ (k:ℕ) (physicalDyadicDistancePolynomial h a m p) q‖≤(1/2:ℝ)^p at herror
  have hP : ContDiff ℝ ∞ (physicalDyadicDistancePolynomial h a m p) :=
    realDistancePolynomial_contDiff _ _
  have hE := real_distance_complex_error_contDiffOn hg hP
  refine ⟨hcard,hdegree,hcoord,hE,herr _ a R ((1/2:ℝ)^p) hR (by positivity) hE hs ?_,?_⟩
  · intro x hx
    exact real_distance_complex_error_C2_bounds hR hg hP (hs x hx)
      (herror _ (by simpa only [mem_closedBall,dist_eq_norm] using hs x hx))
  · intro x
    by_cases hx : x∈tsupport χ
    · have hxb : physicalDistanceTriple x∈ball a R := by
        rw [mem_ball]
        have hh := hs x hx
        rw [mem_closedBall] at hh
        linarith
      have hvalue : (ambientRealScalarProfile h (physicalDistanceTriple x):ℂ)=
          h (ambientRealCast (physicalDistanceTriple x)) := by
        apply Complex.ext <;> simp [ambientRealScalarProfile,hreal _ hxb]
      simp only [physicalCutoffDistanceValue,physicalDyadicDistanceError,
        realDistanceComplexError,Complex.ofReal_sub,hvalue,hu x hx]
    · simp only [physicalCutoffDistanceValue,image_eq_zero_of_notMem_tsupport hx,zero_smul]

#print axioms actual_physical_distance_dyadic_H2_approximation

theorem physical_distance_dyadic_actual_H2_error_small
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {hc : HasCompactSupport χ}
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R : ℝ}
    (hdata : PhysicalDistanceDyadicH2Approximation u χ hc h a R)
    {η : ℝ} (hη : 0<η) (p0 : ℕ) :
    ∃m p : ℕ,∃F : SpatialL2 2,∃d : Coordinate 2 → SpatialL2 2,
    ∃e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
      p0≤p ∧
      F=ᵐ[volume] (fun x => χ x • (u x-
        (physicalDyadicDistancePolynomial h a m p (physicalDistanceTriple x):ℂ))) ∧
      (∀k,WeakPartial F (d k) k) ∧ (∀k j,WeakPartial (d k) (e k j) j) ∧
      HasH2 F ∧ physicalH2ComponentNorm F d e<η := by
  obtain ⟨C,hC,m,hm⟩ := hdata
  let B := ‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖
  have hlim : Tendsto (fun p : ℕ => 7*(1/2:ℝ)^p*C*B) atTop (𝓝 0) := by
    convert ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ))
      (by norm_num : (1/2:ℝ)<1)).const_mul 7).mul_const C |>.mul_const B using 1
    simp
  obtain ⟨p,hp0,hpη⟩ := ((eventually_ge_atTop p0).and (hlim.eventually (gt_mem_nhds hη))).exists
  obtain ⟨_,_,_,_,herr,hid⟩ := hm p
  obtain ⟨F,d,e,hF,_,_,hw1,hw2,hH2,_,_,_,hNorm,_⟩ := herr
  exact ⟨m,p,F,d,e,hp0,hF.trans (Eventually.of_forall hid),hw1,hw2,hH2,hNorm.trans_lt hpη⟩

theorem actual_nuclear_distance_dyadic_H2_approximation
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {ε M A F0 W : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hε : 0<ε)
    (hδ : 0<nuclearAmbientRetainedRadius M A)
    (hrec : PhysicalNuclearAmbientReconstruction u 0 ε (nuclearAmbientRetainedRadius M A)
      (nuclearAmbientNormalizedBound M A F0 W))
    (hreal : NuclearAmbientProfileRealityData u 0 ε (nuclearAmbientRetainedRadius M A))
    (hdata : NuclearDyadicRationalDistanceDictionaryData u 0 ε (nuclearAmbientRetainedRadius M A))
    (hs : ∀x∈tsupport χ,physicalDistanceTriple x∈closedBall (physicalNuclearDistanceCenter ε)
      (ε*nuclearAmbientRetainedRadius M A/8)) :
    PhysicalDistanceDyadicH2Approximation u χ hc (nuclearOriginalAmbientFunction u 0 ε)
      (physicalNuclearDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A) := by
  have hhol : AnalyticOnNhd ℂ (nuclearOriginalAmbientFunction u 0 ε)
      (ball (ambientRealCast (physicalNuclearDistanceCenter ε)) (ε*nuclearAmbientRetainedRadius M A)) := by
    rw [nuclear_distance_center_real_cast]
    intro q hq
    exact hrec.1 q ((nuclear_original_distance_ball_iff hε hδ q).mp hq)
  have hrealball : ∀q∈ball (physicalNuclearDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A),
      (nuclearOriginalAmbientFunction u 0 ε (ambientRealCast q)).im=0 := by
    intro q hq
    have hqc : ambientRealCast q∈ball (nuclearOriginalDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A) := by
      rw [←nuclear_distance_center_real_cast,mem_ball,dist_eq_norm,←map_sub,ambientRealCast_norm]
      simpa only [mem_ball,dist_eq_norm] using hq
    exact (hreal.2.2 q ((nuclear_original_distance_ball_iff hε hδ _).mp hqc)).2.1
  exact actual_physical_distance_dyadic_H2_approximation hχ hc (mul_pos hε hδ) hhol
    hrealball hdata hs
    (fun x hx => actual_nuclear_inner_distance_reconstruction hε hδ (min_le_left _ _) hrec (hs x hx))

theorem actual_pair_distance_dyadic_H2_approximation
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {ε M A F0 W δ : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hε : 0<ε) (hδ : 0<δ)
    (hrec : PhysicalPairAmbientReconstruction u ε M A F0 W δ)
    (hreal : PairAmbientProfileRealityData u ε δ)
    (hdata : PairDyadicRationalDistanceDictionaryData u ε δ)
    (hs : ∀x∈tsupport χ,physicalDistanceTriple x∈closedBall (physicalPairDistanceCenter ε) (ε*δ/8)) :
    PhysicalDistanceDyadicH2Approximation u χ hc (pairOriginalAmbientFunction u ε)
      (physicalPairDistanceCenter ε) (ε*δ) := by
  have hhol : AnalyticOnNhd ℂ (pairOriginalAmbientFunction u ε)
      (ball (ambientRealCast (physicalPairDistanceCenter ε)) (ε*δ)) := by
    rw [pair_distance_center_real_cast]
    intro q hq
    exact hrec.2.2.1 q ((pair_original_distance_ball_iff hε hδ q).mp hq)
  have hrealball : ∀q∈ball (physicalPairDistanceCenter ε) (ε*δ),
      (pairOriginalAmbientFunction u ε (ambientRealCast q)).im=0 := by
    intro q hq
    have hqc : ambientRealCast q∈ball (pairOriginalDistanceCenter ε) (ε*δ) := by
      rw [←pair_distance_center_real_cast,mem_ball,dist_eq_norm,←map_sub,ambientRealCast_norm]
      simpa only [mem_ball,dist_eq_norm] using hq
    exact (hreal.2.2 q ((pair_original_distance_ball_iff hε hδ _).mp hqc)).2.1
  exact actual_physical_distance_dyadic_H2_approximation hχ hc (mul_pos hε hδ) hhol
    hrealball hdata hs (fun x hx => actual_pair_inner_distance_reconstruction hε hδ hrec (hs x hx))

def PhysicalGroundDistanceDyadicH2Data (u : Configuration 2 → ℂ) (ε M A : ℝ) : Prop :=
  (∀(χ : Configuration 2 → ℝ) (_hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ),
    (∀x∈tsupport χ,physicalDistanceTriple x∈closedBall (physicalNuclearDistanceCenter ε)
      (ε*nuclearAmbientRetainedRadius M A/8)) →
    PhysicalDistanceDyadicH2Approximation u χ hc (nuclearOriginalAmbientFunction u 0 ε)
      (physicalNuclearDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A)) ∧
  (∀(χ : Configuration 2 → ℝ) (_hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ),
    (∀x∈tsupport χ,physicalDistanceTriple x∈closedBall (physicalPairDistanceCenter ε)
      (ε*pairAmbientDistanceRadius 1 M A/8)) →
    PhysicalDistanceDyadicH2Approximation u χ hc (pairOriginalAmbientFunction u ε)
      (physicalPairDistanceCenter ε) (ε*pairAmbientDistanceRadius 1 M A))

#print axioms physical_distance_dyadic_actual_H2_error_small
#print axioms actual_nuclear_distance_dyadic_H2_approximation
#print axioms actual_pair_distance_dyadic_H2_approximation
theorem twoElectron_scalar_ground_physical_distance_dyadic_H2_approximation
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
          PhysicalGroundDistanceDyadicH2Data u ε M A) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,
    hNR,hPR,hND,hPD,hNBD,hPBD,hNQR,hPQR⟩ :=
      twoElectron_scalar_ground_dyadic_rational_distance_dictionary Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,
    hNR,hPR,hND,hPD,hNBD,hPBD,hNQR,hPQR,?_⟩
  intro ε hε hlim
  refine ⟨?_,?_⟩
  · intro χ hχ hc hs
    exact actual_nuclear_distance_dyadic_H2_approximation hχ hc hε hδN
      (hNrecData ε hε hlim 0).1 (hNT ε hε hlim 0).2 (hNQR ε hε hlim 0) hs
  · intro χ hχ hc hs
    exact actual_pair_distance_dyadic_H2_approximation hχ hc hε hδP
      (hrec ε hε hlim) (hPT ε hε hlim).2 (hPQR ε hε hlim) hs

#print axioms twoElectron_scalar_ground_physical_distance_dyadic_H2_approximation
end ManyBody.S8