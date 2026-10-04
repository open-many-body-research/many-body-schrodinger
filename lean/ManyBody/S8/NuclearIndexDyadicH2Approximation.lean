import ManyBody.S8.PhysicalDistanceDyadicH2Approximation
import ManyBody.S8.Internal.PhysicalPermutationH2Transport
import ManyBody.S8.Internal.PhysicalDistanceChartReconstruction
import TwoElectronTensorExchange_v1

/-! Actual selected-index-one physical distance coordinates, genuine exchanged
cutoffs, and permutation transport of the literal physical cutoff error.
The selected first two distances exchange the original electron labels;
the third is the unchanged original unnormalized pair distance. The SAME
original exchange-invariant physical ground state supplies a nuclear-index-one
dyadic rational approximation with genuine first/all ordered second weak
families and true H2 error. The index-zero canonical polynomial is reused in
these selected coordinate meanings; no separate index-one canonical coefficient
identity is assumed. Constants precede every requested precision. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff Topology NNReal
namespace ManyBody.S8
open TheoremT.Continuum

def physicalIndexOneDistanceTriple (x : Configuration 2) : Fin 3 → ℝ :=
  physicalDistanceTriple (permuteSpace twoElectronSwap x)

theorem physical_swap_involutive :
    Function.Involutive (permuteSpace twoElectronSwap : Configuration 2 → Configuration 2) := by
  intro x
  ext ⟨j,k⟩
  change x (twoElectronSwap (twoElectronSwap j),k)=x (j,k)
  simp [twoElectronSwap]

theorem physical_index_one_distances_eq_radii (x : Configuration 2) :
    physicalIndexOneDistanceTriple x=
      ![‖position x 1‖,‖position x 0‖,‖position x 0-position x 1‖] := by
  rw [physicalIndexOneDistanceTriple,physical_distance_triple_eq_radii]
  simp only [position_permuteSpace]
  simp only [twoElectronSwap,Equiv.swap_apply_left,Equiv.swap_apply_right,norm_sub_rev]

theorem physical_swapped_cutoff_smooth_compact {χ : Configuration 2 → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ContDiff ℝ ∞ (χ∘permuteSpace twoElectronSwap) ∧
      HasCompactSupport (χ∘permuteSpace twoElectronSwap) :=
  ⟨hχ.comp (permuteSpace twoElectronSwap).toContinuousLinearEquiv.contDiff,
    hc.comp_homeomorph (permuteSpace twoElectronSwap).toHomeomorph⟩

theorem physical_swapped_cutoff_chart {χ : Configuration 2 → ℝ}
    {a : Fin 3 → ℝ} {R : ℝ}
    (hs : ∀x∈tsupport χ,physicalIndexOneDistanceTriple x∈closedBall a R) :
    ∀y∈tsupport (χ∘permuteSpace twoElectronSwap),
      physicalDistanceTriple y∈closedBall a R := by
  intro y hy
  have hx : permuteSpace twoElectronSwap y∈tsupport χ :=
    (Set.ext_iff.mp (tsupport_comp_eq_preimage χ
      (permuteSpace twoElectronSwap).toHomeomorph) y).mp hy
  simpa only [physicalIndexOneDistanceTriple,physical_swap_involutive y] using
    hs (permuteSpace twoElectronSwap y) hx

theorem physical_index_one_cutoff_error_pullback
    (χ : Configuration 2 → ℝ) {u : Configuration 2 → ℂ}
    (P : (Fin 3 → ℝ) → ℂ)
    (hexchange : ∀x,u (permuteSpace twoElectronSwap x)=u x) (x : Configuration 2) :
    (χ∘permuteSpace twoElectronSwap) (permuteSpace twoElectronSwap x) •
      (u (permuteSpace twoElectronSwap x)-P (physicalDistanceTriple (permuteSpace twoElectronSwap x)))=
      χ x • (u x-P (physicalIndexOneDistanceTriple x)) := by
  simp only [Function.comp_apply,physical_swap_involutive x,hexchange,
    physicalIndexOneDistanceTriple]

theorem physical_index_one_weakH2_error_transport
    {χ : Configuration 2 → ℝ} {u : Configuration 2 → ℂ} {P : (Fin 3 → ℝ) → ℂ}
    {F : SpatialL2 2} (d : Coordinate 2 → SpatialL2 2)
    (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hexchange : ∀x,u (permuteSpace twoElectronSwap x)=u x)
    (hF : (F : Configuration 2 → ℂ)=ᵐ[volume]
      fun y => (χ∘permuteSpace twoElectronSwap) y • (u y-P (physicalDistanceTriple y)))
    (hd : ∀k,WeakPartial F (d k) k)
    (he : ∀k l,WeakPartial (d k) (e k l) l) :
    (pullback twoElectronSwap F : Configuration 2 → ℂ)=ᵐ[volume]
      (fun x => χ x • (u x-P (physicalIndexOneDistanceTriple x))) ∧
    (∀k,WeakPartial (pullback twoElectronSwap F)
      (physicalPermutationFirst twoElectronSwap d k) k) ∧
    (∀k l,WeakPartial (physicalPermutationFirst twoElectronSwap d k)
      (physicalPermutationSecond twoElectronSwap e k l) l) ∧
    HasH2 (pullback twoElectronSwap F) ∧
    physicalH2ComponentNorm (pullback twoElectronSwap F)
      (physicalPermutationFirst twoElectronSwap d) (physicalPermutationSecond twoElectronSwap e)=
      physicalH2ComponentNorm F d e := by
  have hAE := physical_permutation_representative_ae twoElectronSwap hF
  refine ⟨hAE.trans (Eventually.of_forall fun x =>
    physical_index_one_cutoff_error_pullback χ P hexchange x),?_⟩
  obtain ⟨h1,h2,hH2⟩ := physical_permutation_weak_families twoElectronSwap d e hd he
  exact ⟨h1,h2,hH2,physical_permutation_H2_component_norm twoElectronSwap F d e⟩

def PhysicalIndexOneDistanceDyadicH2Approximation (u : Configuration 2 → ℂ)
    (χ : Configuration 2 → ℝ) (h : (Fin 3 → ℂ) → ℂ)
    (a : Fin 3 → ℝ) (R : ℝ) : Prop :=
  ∃C : ℝ,1≤C ∧ ∃m : ℕ,∀p : ℕ,
    (physicalDyadicDistanceSupport h a m p).card≤(physicalDyadicDistanceOrder m p)^3 ∧
    (∀α∈physicalDyadicDistanceSupport h a m p,(∑j : Fin 3,α j)<physicalDyadicDistanceOrder m p) ∧
    (∀α∈physicalDyadicDistanceSupport h a m p,∀j : Fin 3,α j<physicalDyadicDistanceOrder m p) ∧
    ContDiffOn ℝ ∞ (physicalDyadicDistanceError h a m p) (ball a R) ∧
    ∃F : SpatialL2 2,∃d : Coordinate 2 → SpatialL2 2,
    ∃e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
      (F : Configuration 2 → ℂ)=ᵐ[volume]
        (fun x => χ x • (u x-(physicalDyadicDistancePolynomial h a m p
          (physicalIndexOneDistanceTriple x) : ℂ))) ∧
      (∀k,WeakPartial F (d k) k) ∧
      (∀k l,WeakPartial (d k) (e k l) l) ∧ HasH2 F ∧
      ‖F‖≤(1/2:ℝ)^p*C ∧
      (∀k,‖d k‖≤(1/2:ℝ)^p*C) ∧
      (∀k l,‖e k l‖≤(1/2:ℝ)^p*C) ∧
      physicalH2ComponentNorm F d e≤(1/2:ℝ)^p*C

set_option maxHeartbeats 300000 in
theorem actual_index_one_distance_dyadic_H2_transport
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ}
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R : ℝ}
    (hc : HasCompactSupport χ)
    (hexchange : ∀x,u (permuteSpace twoElectronSwap x)=u x)
    (hdata : PhysicalDistanceDyadicH2Approximation u (χ∘permuteSpace twoElectronSwap)
      (hc.comp_homeomorph (permuteSpace twoElectronSwap).toHomeomorph) h a R) :
    PhysicalIndexOneDistanceDyadicH2Approximation u χ h a R := by
  obtain ⟨C,hC,m,hm⟩ := hdata
  let B := ‖physicalDistanceCompactBudgetClass
    (tsupport (χ∘permuteSpace twoElectronSwap))
    (hc.comp_homeomorph (permuteSpace twoElectronSwap).toHomeomorph)‖
  let C1 := max 1 (7*C*B)
  refine ⟨C1,le_max_left _ _,m,?_⟩
  intro p
  obtain ⟨hcard,hdegree,hcoord,hE,herr,hid⟩ := hm p
  obtain ⟨F,d,e,hF,hdAE,heAE,hw1,hw2,hH2,h0,h1,h2,hnorm,hsum⟩ := herr
  have hFlit : (F : Configuration 2 → ℂ)=ᵐ[volume]
      fun y => (χ∘permuteSpace twoElectronSwap) y •
        (u y-(physicalDyadicDistancePolynomial h a m p (physicalDistanceTriple y) : ℂ)) :=
    hF.trans (Eventually.of_forall hid)
  obtain ⟨hAE,hD,hA,hH2',hNorm⟩ :=
    physical_index_one_weakH2_error_transport (χ:=χ) (u:=u)
      (P:=fun q => (physicalDyadicDistancePolynomial h a m p q : ℂ)) (F:=F)
      d e hexchange hFlit hw1 hw2
  have hfinal : physicalH2ComponentNorm (pullback twoElectronSwap F)
      (physicalPermutationFirst twoElectronSwap d) (physicalPermutationSecond twoElectronSwap e)≤
      (1/2:ℝ)^p*C1 := by
    calc
      _=physicalH2ComponentNorm F d e := hNorm
      _≤7*(1/2:ℝ)^p*C*B := hnorm
      _=(1/2:ℝ)^p*(7*C*B) := by ring
      _≤(1/2:ℝ)^p*C1 := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  refine ⟨hcard,hdegree,hcoord,hE,pullback twoElectronSwap F,
    physicalPermutationFirst twoElectronSwap d,physicalPermutationSecond twoElectronSwap e,
    hAE,hD,hA,hH2',?_,?_,?_,hfinal⟩
  · exact (physicalH2ComponentNorm_bounds _ _ _).1.trans hfinal
  · intro k
    exact (physicalH2ComponentNorm_first_le _ _ _ k).trans hfinal
  · intro k l
    exact (physicalH2ComponentNorm_bounds _ _ _).2.2 k l |>.trans hfinal

theorem actual_index_one_distance_chart_cutoff_exists
    {x : Configuration 2} {a : Fin 3 → ℝ} {R : ℝ}
    (hx : physicalIndexOneDistanceTriple x∈ball a (R/8)) :
    ∃r : ℝ,0<r ∧ ∃χ : Configuration 2 → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀y∈tsupport χ,physicalIndexOneDistanceTriple y∈closedBall a (R/8)) ∧
      ∀y∈ball x r,χ y=1 := by
  obtain ⟨r,hr,χ0,hχ0,hc0,hs,h1⟩ := actual_distance_chart_cutoff_exists hx
  obtain ⟨hχ,hc⟩ := physical_swapped_cutoff_smooth_compact hχ0 hc0
  refine ⟨r,hr,χ0∘permuteSpace twoElectronSwap,hχ,hc,?_,?_⟩
  · intro y hy
    have hy' : permuteSpace twoElectronSwap y∈tsupport χ0 :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage χ0
        (permuteSpace twoElectronSwap).toHomeomorph) y).mp hy
    exact hs (permuteSpace twoElectronSwap y) hy'
  · intro y hy
    have hy' : permuteSpace twoElectronSwap y∈
        ball (permuteSpace twoElectronSwap x) r := by
      simpa only [mem_ball,(permuteSpace twoElectronSwap).dist_map] using hy
    exact h1 (permuteSpace twoElectronSwap y) hy'

def PhysicalGroundIndexOneDistanceDyadicH2Data (u : Configuration 2 → ℂ)
    (ε M A : ℝ) : Prop :=
  ∀(χ : Configuration 2 → ℝ) (_hχ : ContDiff ℝ ∞ χ) (_hc : HasCompactSupport χ),
    (∀x∈tsupport χ,physicalIndexOneDistanceTriple x∈closedBall
      (physicalNuclearDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A/8)) →
    PhysicalIndexOneDistanceDyadicH2Approximation u χ (nuclearOriginalAmbientFunction u 0 ε)
      (physicalNuclearDistanceCenter ε) (ε*nuclearAmbientRetainedRadius M A)

theorem actual_ground_index_one_distance_dyadic_H2_data
    {u : Configuration 2 → ℂ} {ε M A : ℝ}
    (hexchange : ∀x,u (permuteSpace twoElectronSwap x)=u x)
    (hdata : PhysicalGroundDistanceDyadicH2Data u ε M A) :
    PhysicalGroundIndexOneDistanceDyadicH2Data u ε M A := by
  intro χ hχ hc hs
  obtain ⟨hχs,hcs⟩ := physical_swapped_cutoff_smooth_compact hχ hc
  exact actual_index_one_distance_dyadic_H2_transport hc hexchange
    (hdata.1 (χ∘permuteSpace twoElectronSwap) hχs hcs (physical_swapped_cutoff_chart hs))

theorem twoElectron_scalar_ground_both_nuclear_distance_dyadic_H2_approximation
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
          PhysicalGroundIndexOneDistanceDyadicH2Data u ε M A) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,
    hNR,hPR,hND,hPD,hNBD,hPBD,hNQR,hPQR,hActual⟩ :=
      twoElectron_scalar_ground_physical_distance_dyadic_H2_approximation Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,
    hNR,hPR,hND,hPD,hNBD,hPBD,hNQR,hPQR,hActual,?_⟩
  intro ε hε hlim
  exact actual_ground_index_one_distance_dyadic_H2_data hexchange (hActual ε hε hlim)

#print axioms physical_index_one_distances_eq_radii
#print axioms physical_swapped_cutoff_smooth_compact
#print axioms physical_swapped_cutoff_chart
#print axioms physical_index_one_weakH2_error_transport
#print axioms actual_index_one_distance_chart_cutoff_exists
#print axioms actual_index_one_distance_dyadic_H2_transport
#print axioms actual_ground_index_one_distance_dyadic_H2_data
#print axioms twoElectron_scalar_ground_both_nuclear_distance_dyadic_H2_approximation
end ManyBody.S8
