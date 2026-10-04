import ManyBody.S8.Internal.PhysicalFiniteSmoothPartition
import ManyBody.S8.Internal.PhysicalFiniteWeakH2Gluing
import ManyBody.S8.Internal.PhysicalCollisionDistanceCharts
import Mathlib.Tactic
/-! Genuine finite gluing of actual collision distance dyadic dictionaries.

The same complete actual scalar ground witness is retained. For every smooth
compact physical target cutoff whose support is geometrically covered by the
actual admissible nuclear-zero, nuclear-one and original pair inner patches,
actual bounded smooth bumps and a finite subcover derive a finite smooth
partition, without partition or local error data as a physical input.

One finite chart selector, smooth compact weights, finite vector of canonical
Taylor offsets, common upper offset and error constant precede every
precision. The literal finite weighted sum of true floor-dyadic rational
polynomials approximates the original cutoff wavefunction. Original weak
sum rules give actual first and all ordered second derivative families of
its error, actual H2 membership and a genuine43-component norm at mostC2^(-p).
Every local support has degree below the common linear order and at most
its cube monomials. Arbitrarily small actual error beyond any minimum
precision follows from genuine half-power convergence.

Coverage is the displayed geometric condition on actual physical compact
support. Full annular/bulk/triple-origin coverage, global density, effective
partition/coefficient/order selection, one global rational polynomial,
normalization or symmetry of the weighted dictionary, and fullRung2 remain
outside this declaration. The selected-index-one component uses the original
nuclear-zero canonical polynomial in true exchanged radius meanings.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators NNReal
namespace ManyBody.S8
open TheoremT.Continuum

abbrev PhysicalAdmissibleCollisionChart (R : ℝ) :=
  Fin 3 × {ε : ℝ // 0<ε ∧ ε≤min 1 (R/4)}

def physicalAdmissibleCollisionPatch (M A R : ℝ)
    (c : PhysicalAdmissibleCollisionChart R) : Set (Configuration 2) :=
  physicalCollisionChartPatch M A c.1 c.2.val

def physicalFiniteCollisionDictionary {n : ℕ} {R : ℝ} (u : Configuration 2 → ℂ)
    (χ : Configuration 2 → ℝ) (cs : Fin n → PhysicalAdmissibleCollisionChart R)
    (ρ : Fin n → Configuration 2 → ℝ) (ms : Fin n → ℕ) (p : ℕ)
    (x : Configuration 2) : ℂ :=
  ∑i,(χ x*ρ i x) • (physicalDyadicDistancePolynomial
    (physicalCollisionChartProfile u (cs i).1 (cs i).2.val)
    (physicalCollisionChartCenter (cs i).1 (cs i).2.val) (ms i) p
    (physicalCollisionChartDistances (cs i).1 x):ℂ)

def PhysicalFiniteCollisionDictionaryData (u : Configuration 2 → ℂ)
    (χ : Configuration 2 → ℝ) (M A R : ℝ) : Prop :=
  ∃n : ℕ,∃cs : Fin n → PhysicalAdmissibleCollisionChart R,
    ∃ρ : Fin n → Configuration 2 → ℝ,
      (∀i,ContDiff ℝ ∞ (ρ i)) ∧ (∀i,HasCompactSupport (ρ i)) ∧
      (∀i,tsupport (ρ i)⊆physicalAdmissibleCollisionPatch M A R (cs i)) ∧
      (∀i x,0≤ρ i x ∧ ρ i x≤1) ∧ (∀x∈tsupport χ,(∑i,ρ i x)=1) ∧
      ∃ms : Fin n → ℕ,∃m : ℕ,∃C : ℝ,1≤C ∧ (∀i,ms i≤m) ∧ ∀p : ℕ,
        (∀i,(physicalDyadicDistanceSupport
          (physicalCollisionChartProfile u (cs i).1 (cs i).2.val)
          (physicalCollisionChartCenter (cs i).1 (cs i).2.val) (ms i) p).card≤
            (physicalDyadicDistanceOrder m p)^3) ∧
        (∀i,∀α∈physicalDyadicDistanceSupport
          (physicalCollisionChartProfile u (cs i).1 (cs i).2.val)
          (physicalCollisionChartCenter (cs i).1 (cs i).2.val) (ms i) p,
          (∑j : Fin 3,α j)<physicalDyadicDistanceOrder m p ∧
            ∀j : Fin 3,α j<physicalDyadicDistanceOrder m p) ∧
        ∃F : SpatialL2 2,∃d : Coordinate 2 → SpatialL2 2,
        ∃e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
          (F : Configuration 2 → ℂ)=ᵐ[volume]
            (fun x => χ x • u x-physicalFiniteCollisionDictionary u χ cs ρ ms p x) ∧
          (∀k,WeakPartial F (d k) k) ∧ (∀k l,WeakPartial (d k) (e k l) l) ∧ HasH2 F ∧
          ‖F‖≤(1/2:ℝ)^p*C ∧ (∀k,‖d k‖≤(1/2:ℝ)^p*C) ∧
          (∀k l,‖e k l‖≤(1/2:ℝ)^p*C) ∧ physicalH2ComponentNorm F d e≤(1/2:ℝ)^p*C

theorem actual_physical_finite_collision_dictionary
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {M A R : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hPhys : ∀ε,0<ε → ε≤min 1 (R/4) → PhysicalGroundDistanceDyadicH2Data u ε M A)
    (hOne : ∀ε,0<ε → ε≤min 1 (R/4) → PhysicalGroundIndexOneDistanceDyadicH2Data u ε M A)
    (hcover : ∀x∈tsupport χ,∃c : PhysicalAdmissibleCollisionChart R,
      x∈physicalAdmissibleCollisionPatch M A R c) :
    PhysicalFiniteCollisionDictionaryData u χ M A R := by
  classical
  obtain ⟨n,cs,ρ,hρ,hcρ,hsρ,hbρ,hpsum⟩ :=
    physical_finite_smooth_partition_of_compact_cover hc (physicalAdmissibleCollisionPatch M A R)
      (fun c => physical_collision_chart_patch_open M A c.1 c.2.val) hcover
  let κ : Fin n → Configuration 2 → ℝ := fun i x => χ x*ρ i x
  have hκ (i : Fin n) : ContDiff ℝ ∞ (κ i) := hχ.mul (hρ i)
  have hcκ (i : Fin n) : HasCompactSupport (κ i) := hc.mul_right
  have hsκ (i : Fin n) : ∀x∈tsupport (κ i),physicalCollisionChartDistances (cs i).1 x∈closedBall
      (physicalCollisionChartCenter (cs i).1 (cs i).2.val)
      (physicalCollisionChartRadius (cs i).1 (cs i).2.val M A/8) := by
    intro x hx
    exact ball_subset_closedBall (hsρ i (tsupport_mul_subset_right hx))
  have hlocal (i : Fin n) := actual_physical_collision_chart_dyadic_data
    (hPhys (cs i).2.val (cs i).2.property.1 (cs i).2.property.2)
    (hOne (cs i).2.val (cs i).2.property.1 (cs i).2.property.2) (hκ i) (hcκ i) (cs i).1 (hsκ i)
  choose C hC ms hm using hlocal
  let m : ℕ := ∑i,ms i
  have hms (i : Fin n) : ms i≤m := Finset.single_le_sum (fun j _ => Nat.zero_le (ms j)) (Finset.mem_univ i)
  let Ctotal : ℝ := max 1 (7*(∑i,C i))
  have hCsum : 0≤∑i,C i := Finset.sum_nonneg fun i _ => (by norm_num : (0:ℝ)≤1).trans (hC i)
  have hCsumle : (∑i,C i)≤Ctotal := by
    have hh := le_max_right 1 (7*(∑i,C i))
    dsimp [Ctotal]
    linarith
  refine ⟨n,cs,ρ,hρ,hcρ,hsρ,hbρ,hpsum,ms,m,Ctotal,le_max_left _ _,hms,?_⟩
  intro p
  have horder (i : Fin n) : physicalDyadicDistanceOrder (ms i) p≤physicalDyadicDistanceOrder m p := by
    dsimp [physicalDyadicDistanceOrder]
    have := hms i
    omega
  have hcard (i : Fin n) := (hm i p).1
  have hdegree (i : Fin n) := (hm i p).2.1
  have hcoord (i : Fin n) := (hm i p).2.2.1
  have hweak (i : Fin n) := (hm i p).2.2.2
  choose F d e hF hd he hH2 h0 h1 h2 hNorm using hweak
  have hsum := physical_finite_weakH2_error_sum F d e
    (fun i x => κ i x • (u x-(physicalDyadicDistancePolynomial
      (physicalCollisionChartProfile u (cs i).1 (cs i).2.val)
      (physicalCollisionChartCenter (cs i).1 (cs i).2.val) (ms i) p
      (physicalCollisionChartDistances (cs i).1 x):ℂ))) (by positivity : 0≤(1/2:ℝ)^p)
    (fun i => (by norm_num : (0:ℝ)≤1).trans (hC i)) hF hd he h0 h1 h2
  obtain ⟨hAE,hw1,hw2,hH2sum,h0sum,h1sum,h2sum,hNormsum⟩ := hsum
  have hκsum (x : Configuration 2) : (∑i,κ i x)=χ x := by
    by_cases hx : x∈tsupport χ
    · change (∑i,χ x*ρ i x)=χ x
      rw [←Finset.mul_sum,hpsum x hx,mul_one]
    · simp only [κ,image_eq_zero_of_notMem_tsupport hx,zero_mul,Finset.sum_const_zero]
  have hid (x : Configuration 2) :
      (∑i,κ i x • (u x-(physicalDyadicDistancePolynomial
        (physicalCollisionChartProfile u (cs i).1 (cs i).2.val)
        (physicalCollisionChartCenter (cs i).1 (cs i).2.val) (ms i) p
        (physicalCollisionChartDistances (cs i).1 x):ℂ)))=
        χ x • u x-physicalFiniteCollisionDictionary u χ cs ρ ms p x := by
    simp only [smul_sub,Finset.sum_sub_distrib]
    rw [←Finset.sum_smul,hκsum]
    rfl
  refine ⟨?_,?_,∑i,F i,(fun k => ∑i,d i k),(fun k l => ∑i,e i k l),
    hAE.trans (Eventually.of_forall hid),hw1,hw2,hH2sum,?_,?_,?_,?_⟩
  · intro i
    apply (hcard i).trans
    exact Nat.pow_le_pow_left (horder i) 3
  · intro i α hα
    exact ⟨lt_of_lt_of_le (hdegree i α hα) (horder i),fun j => lt_of_lt_of_le (hcoord i α hα j) (horder i)⟩
  · exact h0sum.trans (mul_le_mul_of_nonneg_left hCsumle (by positivity))
  · intro k
    exact (h1sum k).trans (mul_le_mul_of_nonneg_left hCsumle (by positivity))
  · intro k l
    exact (h2sum k l).trans (mul_le_mul_of_nonneg_left hCsumle (by positivity))
  · calc _≤7*(1/2:ℝ)^p*(∑i,C i) := hNormsum
         _=(1/2:ℝ)^p*(7*(∑i,C i)) := by ring
         _≤(1/2:ℝ)^p*Ctotal := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

#print axioms actual_physical_finite_collision_dictionary

theorem physical_finite_collision_dictionary_actual_H2_error_small
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {M A R : ℝ}
    (hdata : PhysicalFiniteCollisionDictionaryData u χ M A R)
    {η : ℝ} (hη : 0<η) (p0 : ℕ) :
    ∃n : ℕ,∃cs : Fin n → PhysicalAdmissibleCollisionChart R,
      ∃ρ : Fin n → Configuration 2 → ℝ,∃ms : Fin n → ℕ,∃p : ℕ,
      ∃F : SpatialL2 2,∃d : Coordinate 2 → SpatialL2 2,
      ∃e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        p0≤p ∧ (F : Configuration 2 → ℂ)=ᵐ[volume]
          (fun x => χ x • u x-physicalFiniteCollisionDictionary u χ cs ρ ms p x) ∧
        (∀k,WeakPartial F (d k) k) ∧ (∀k l,WeakPartial (d k) (e k l) l) ∧
        HasH2 F ∧ physicalH2ComponentNorm F d e<η := by
  obtain ⟨n,cs,ρ,_,_,_,_,_,ms,_,C,_,_,hm⟩ := hdata
  have hlim : Tendsto (fun p : ℕ => (1/2:ℝ)^p*C) atTop (𝓝 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ))
      (by norm_num : (1/2:ℝ)<1)).mul_const C using 1
    simp
  obtain ⟨p,hp0,hpη⟩ := ((eventually_ge_atTop p0).and (hlim.eventually (gt_mem_nhds hη))).exists
  obtain ⟨_,_,F,d,e,hAE,hd,he,hH2,_,_,_,hNorm⟩ := hm p
  exact ⟨n,cs,ρ,ms,p,F,d,e,hp0,hAE,hd,he,hH2,hNorm.trans_lt hpη⟩

def PhysicalGroundFiniteCollisionDictionaryData (u : Configuration 2 → ℂ) (M A R : ℝ) : Prop :=
  ∀(χ : Configuration 2 → ℝ) (_hχ : ContDiff ℝ ∞ χ) (_hc : HasCompactSupport χ),
    (∀x∈tsupport χ,∃c : PhysicalAdmissibleCollisionChart R,
      x∈physicalAdmissibleCollisionPatch M A R c) →
    PhysicalFiniteCollisionDictionaryData u χ M A R

#print axioms physical_finite_collision_dictionary_actual_H2_error_small
theorem twoElectron_scalar_ground_finite_collision_dictionary
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
          PhysicalGroundIndexOneDistanceDyadicH2Data u ε M A) ∧
        PhysicalGroundFiniteCollisionDictionaryData u M A R := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,
    hNR,hPR,hND,hPD,hNBD,hPBD,hNQR,hPQR,hActual,hIndexOne⟩ :=
      twoElectron_scalar_ground_both_nuclear_distance_dyadic_H2_approximation Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,hNT,hPT,
    hNR,hPR,hND,hPD,hNBD,hPBD,hNQR,hPQR,hActual,hIndexOne,?_⟩
  intro χ hχ hc hcover
  exact actual_physical_finite_collision_dictionary hχ hc hActual hIndexOne hcover

#print axioms twoElectron_scalar_ground_finite_collision_dictionary
end ManyBody.S8