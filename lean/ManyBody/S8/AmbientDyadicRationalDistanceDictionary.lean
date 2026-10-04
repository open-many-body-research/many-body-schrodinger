import ManyBody.S8.AmbientBoundedDyadicDistanceDictionary
import ManyBody.S8.DyadicDistanceCoefficientApproximation
/-! Actual original collision profiles with quantitative finite dyadic rational
C2 approximation. One original chart offset precedes every precision. The
canonical dictionary at N=2(p+1)+m+2 and literal floor denominator exponent
b=(p+1)+4+7N give total value/gradient/Hessian error at most 2^(-p).
The same full actual ground witness is retained, with no supplied analytic,
Taylor, dictionary, rounding or error premise. The three rounded profiles
are independent polynomials; structural A+q_j B coupling is not asserted. -/
set_option autoImplicit false
noncomputable section
open TheoremT.Continuum
open MeasureTheory Metric
open scoped Topology NNReal BigOperators ContDiff
namespace ManyBody.S8

def RealThreeProfilesDyadicRationalDictionaryData (a b h : (Fin 3 → ℂ) → ℂ)
    (center : Fin 3 → ℝ) (R : ℝ) : Prop :=
  let fs : Fin 3 → (Fin 3 → ℂ) → ℂ := ![a,b,h]
  ∃ m : ℕ, ∀ p : ℕ, ∀ j : Fin 3,
    let g := ambientRealScalarProfile (fs j)
    let N := 2*(p+1)+m+2
    let bits := (p+1)+4+7*N
    let s := realTaylorDistanceDictionarySupport g center N
    let r := fun α => dyadicDistanceCoefficient bits (realTaylorDistanceDictionaryCoefficient g center N α)
    let P := realDistancePolynomial s (fun α => (r α : ℝ))
    s.card ≤ N^3 ∧
    (∀ α ∈ s, (∑ l : Fin 3, α l) < N) ∧
    (∀ α ∈ s, ∀ l : Fin 3, α l < N) ∧
    ∀ q : Fin 3 → ℝ, ‖q-center‖ ≤ R/8 → ∀ k : Fin 3,
      ‖iteratedFDeriv ℝ (k : ℕ) g q-iteratedFDeriv ℝ (k : ℕ) P q‖ ≤ (1/2 : ℝ)^p

def NuclearDyadicRationalDistanceDictionaryData (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε δ : ℝ) : Prop :=
  RealThreeProfilesDyadicRationalDictionaryData (nuclearOriginalAmbientA u i ε)
    (nuclearOriginalAmbientB u i ε) (nuclearOriginalAmbientFunction u i ε)
    (nuclearOriginalRealDistanceCenter ε) (ε*δ)

def PairDyadicRationalDistanceDictionaryData (u : Configuration 2 → ℂ)
    (ε δ : ℝ) : Prop :=
  RealThreeProfilesDyadicRationalDictionaryData (pairOriginalAmbientA u ε)
    (pairOriginalAmbientB u ε) (pairOriginalAmbientFunction u ε)
    (pairOriginalRealDistanceCenter ε) (ε*δ)

theorem dyadic_rational_distance_coefficient_grid (b : ℕ) (c : ℝ) :
    dyadicDistanceCoefficient b c*(2 : ℚ)^b=(⌊(2 : ℝ)^b*c⌋ : ℚ) := by
  unfold dyadicDistanceCoefficient
  exact div_mul_cancel₀ _ (pow_ne_zero b (by norm_num))

theorem dyadic_rational_dictionary_bits_linear (p m : ℕ) :
    (p+1)+4+7*(2*(p+1)+m+2)=15*p+7*m+33 := by omega

theorem real_three_profiles_dyadic_rational_dictionary
    {a b h : (Fin 3 → ℂ) → ℂ} {center : Fin 3 → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hbox : ∀ q : Fin 3 → ℝ, ‖q-center‖ ≤ R/8 → ‖q‖ ≤ 2)
    (hdata : RealThreeProfilesBoundedDyadicDictionaryData a b h center R) :
    RealThreeProfilesDyadicRationalDictionaryData a b h center R := by
  obtain ⟨m, hm⟩ := hdata
  refine ⟨m, ?_⟩
  intro p j
  let fs : Fin 3 → (Fin 3 → ℂ) → ℂ := ![a,b,h]
  let g := ambientRealScalarProfile (fs j)
  let N := 2*(p+1)+m+2
  obtain ⟨hcard, hdegree, hcoord, heq, herror⟩ := hm (p+1) j
  refine ⟨hcard, hdegree, hcoord, ?_⟩
  intro q hq k
  have hquarter : ‖q-center‖ < R/4 := by linarith
  have hTaylor := herror q hquarter k
  rw [←heq] at hTaylor
  have hround := realTaylor_dyadic_rounding_explicit_bits_C2 g center N (p+1) (hbox q hq) k
  calc
    _ ≤ ‖iteratedFDeriv ℝ (k : ℕ) g q-iteratedFDeriv ℝ (k : ℕ) (realTaylorPolynomial g center N) q‖+
        ‖iteratedFDeriv ℝ (k : ℕ) (realTaylorPolynomial g center N) q-
          iteratedFDeriv ℝ (k : ℕ) (realTaylorDyadicDistancePolynomial g center N ((p+1)+4+7*N)) q‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1/2 : ℝ)^(p+1)+(1/2 : ℝ)^(p+1) := add_le_add hTaylor hround
    _ = (1/2 : ℝ)^p := by rw [pow_succ]; ring

theorem dyadic_distance_inner_box_norm_le_two {center q : Fin 3 → ℝ} {R : ℝ}
    (hc : ‖center‖ ≤ 1) (hR : R ≤ 1) (hq : ‖q-center‖ ≤ R/8) : ‖q‖ ≤ 2 := by
  have hh := norm_add_le (q-center) center
  rw [sub_add_cancel] at hh
  linarith

theorem nuclear_dyadic_rational_distance_dictionary
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hdata : NuclearBoundedDyadicDistanceDictionaryData u i ε (nuclearAmbientRetainedRadius M A)) :
    NuclearDyadicRationalDistanceDictionaryData u i ε (nuclearAmbientRetainedRadius M A) := by
  have hδ := nuclearAmbientRetainedRadius_pos (M := M) hA
  have hc : ‖nuclearOriginalRealDistanceCenter ε‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    fin_cases j <;> simp [nuclearOriginalRealDistanceCenter, Real.norm_eq_abs, abs_of_pos hε, hε1]
  have hδb : nuclearAmbientRetainedRadius M A ≤ 1/4 := min_le_left _ _
  have hR : ε*nuclearAmbientRetainedRadius M A ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hδb hε.le
    nlinarith
  exact real_three_profiles_dyadic_rational_dictionary (mul_pos hε hδ)
    (fun _ hq => dyadic_distance_inner_box_norm_le_two hc hR hq) hdata

theorem pair_dyadic_rational_distance_dictionary
    (u : Configuration 2 → ℂ) {ε M A : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hdata : PairBoundedDyadicDistanceDictionaryData u ε (pairAmbientDistanceRadius 1 M A)) :
    PairDyadicRationalDistanceDictionaryData u ε (pairAmbientDistanceRadius 1 M A) := by
  have hδ := pairAmbientDistanceRadius_pos (M := M) (by norm_num : (0 : ℝ) < 1) hA
  have hc : ‖pairOriginalRealDistanceCenter ε‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    fin_cases j <;> simp [pairOriginalRealDistanceCenter, Real.norm_eq_abs, abs_of_pos hε, hε1]
  have hδb : pairAmbientDistanceRadius 1 M A ≤ 1/16 := (pairAmbientDistanceRadius_le 1 M A).1
  have hR : ε*pairAmbientDistanceRadius 1 M A ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hδb hε.le
    nlinarith
  exact real_three_profiles_dyadic_rational_dictionary (mul_pos hε hδ)
    (fun _ hq => dyadic_distance_inner_box_norm_le_two hc hR hq) hdata

theorem twoElectron_scalar_ground_dyadic_rational_distance_dictionary
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
          PairDyadicRationalDistanceDictionaryData u ε (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,hNR,hPR,hND,hPD,hNBD,hPBD⟩ :=
      twoElectron_scalar_ground_bounded_dyadic_distance_dictionary Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,hNR,hPR,hND,hPD,hNBD,hPBD,?_,?_⟩
  · intro ε hε hlim i
    exact nuclear_dyadic_rational_distance_dictionary u i hε (hlim.trans (min_le_left _ _)) hA
      (hNBD ε hε hlim i)
  · intro ε hε hlim
    exact pair_dyadic_rational_distance_dictionary u hε (hlim.trans (min_le_left _ _)) hA
      (hPBD ε hε hlim)

#print axioms dyadic_rational_distance_coefficient_grid
#print axioms dyadic_rational_dictionary_bits_linear
#print axioms real_three_profiles_dyadic_rational_dictionary
#print axioms nuclear_dyadic_rational_distance_dictionary
#print axioms pair_dyadic_rational_distance_dictionary
#print axioms twoElectron_scalar_ground_dyadic_rational_distance_dictionary
end ManyBody.S8
