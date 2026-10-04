import ManyBody.S8.Internal.PairDistanceAmbientComposition
import PhysicalDistanceLinearMaps_v1
import Mathlib.Tactic

/-! Original unscaled pair ambient-distance reconstruction.

The literal profiles are A_original(q)=u(0)+epsilon*A_scaled(q/epsilon) and
B_original(q)=B_scaled(q/epsilon). Thus the original pair separation q_2
multiplies B_original with no extra epsilon factor. The positive rescaling
lemma proves analyticity and separate profile bounds on the full complex
distance polydisc centered at (epsilon,epsilon,0), and derives the identity
for every actual physical configuration from the normalized reconstruction.

The ground-state theorem has only Z>=2 as its hypothesis. It preserves every
conclusion of the actual scalar ground pair ambient descent endpoint,
including the common graph-derived physical representative, and adds
original unscaled reconstruction at all admissible scales. It uses the
original pair chart center plus/minus half the separation, with coefficient 1.
-/

set_option autoImplicit false
noncomputable section
open TheoremT.Continuum
open scoped ContDiff NNReal BigOperators Topology
open MeasureTheory Metric
namespace ManyBody.S8

def pairOriginalAmbientA (u : Configuration 2 → ℂ) (ε : ℝ)
    (q : Fin 3 → ℂ) : ℂ :=
  u 0+(ε:ℂ)*pairAmbientPhysicalA (originScaledDifference u ε) 1 ((ε:ℂ)⁻¹ • q)

def pairOriginalAmbientB (u : Configuration 2 → ℂ) (ε : ℝ)
    (q : Fin 3 → ℂ) : ℂ :=
  pairAmbientPhysicalB (originScaledDifference u ε) 1 ((ε:ℂ)⁻¹ • q)

def pairOriginalAmbientFunction (u : Configuration 2 → ℂ) (ε : ℝ)
    (q : Fin 3 → ℂ) : ℂ :=
  pairOriginalAmbientA u ε q+q 2*pairOriginalAmbientB u ε q

def pairAmbientNormalizedBound (M A F0 W δ : ℝ) : ℝ :=
  16*physicalKSPointwiseAmplitude M A F0 W+
    δ*((32*(7*physicalKSPointwiseRate M A)^2)*
      (16*physicalKSPointwiseAmplitude M A F0 W))

def PhysicalPairAmbientReconstruction (u : Configuration 2 → ℂ)
    (ε M A F0 W δ : ℝ) : Prop :=
  AnalyticOnNhd ℂ (pairOriginalAmbientA u ε)
    {q | ‖q 0-(ε:ℂ)‖<ε*δ ∧ ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2‖<ε*δ} ∧
  AnalyticOnNhd ℂ (pairOriginalAmbientB u ε)
    {q | ‖q 0-(ε:ℂ)‖<ε*δ ∧ ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2‖<ε*δ} ∧
  AnalyticOnNhd ℂ (pairOriginalAmbientFunction u ε)
    {q | ‖q 0-(ε:ℂ)‖<ε*δ ∧ ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2‖<ε*δ} ∧
  (∀ q : Fin 3 → ℂ, ‖q 0-(ε:ℂ)‖<ε*δ → ‖q 1-(ε:ℂ)‖<ε*δ → ‖q 2‖<ε*δ →
    ‖pairOriginalAmbientA u ε q‖≤‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W) ∧
    ‖pairOriginalAmbientB u ε q‖≤
      (32*(7*physicalKSPointwiseRate M A)^2)*(16*physicalKSPointwiseAmplitude M A F0 W) ∧
    ‖pairOriginalAmbientFunction u ε q‖≤‖u 0‖+ε*pairAmbientNormalizedBound M A F0 W δ) ∧
  (∀ x : Configuration 2, |‖position x 0‖-ε|<ε*δ → |‖position x 1‖-ε|<ε*δ →
    ‖position x 0-position x 1‖<ε*δ →
    u x=pairOriginalAmbientFunction u ε (fun i => (pairAmbientPhysicalDistances x i:ℂ)))

theorem pairAmbientPhysicalDistances_positive_smul
    (a : ℝ) (ha : 0<a) (x : Configuration 2) :
    pairAmbientPhysicalDistances (a • x)=a • pairAmbientPhysicalDistances x := by
  have hp (i : Fin 2) : position (a • x) i=a • position x i := by
    simpa only [electronPositionCLM_apply] using (electronPositionCLM i).map_smul a x
  ext j
  fin_cases j <;>
    simp [pairAmbientPhysicalDistances,hp,←smul_sub,norm_smul,
      Real.norm_eq_abs,abs_of_pos ha]

theorem pair_original_ambient_positive_rescaling
    (u : Configuration 2 → ℂ) {ε M A F0 W δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hdata : PairAmbientPhysicalAnalyticData (originScaledDifference u ε) 1 M A F0 W δ) :
    PhysicalPairAmbientReconstruction u ε M A F0 W δ := by
  obtain ⟨hAnA,hAnB,hBound,hId⟩ := hdata
  have hc : (ε:ℂ)≠0 := by exact_mod_cast hε.ne'
  have hnorm : ‖(ε:ℂ)⁻¹‖=ε⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  have hscale (q : Fin 3 → ℂ)
      (hr : ‖q 0-(ε:ℂ)‖<ε*δ) (hs : ‖q 1-(ε:ℂ)‖<ε*δ)
      (ht : ‖q 2‖<ε*δ) :
      ‖((ε:ℂ)⁻¹ • q) 0-1‖<δ ∧
      ‖((ε:ℂ)⁻¹ • q) 1-1‖<δ ∧ ‖((ε:ℂ)⁻¹ • q) 2‖<δ := by
    have h0 : ((ε:ℂ)⁻¹ • q) 0-1=(ε:ℂ)⁻¹*(q 0-(ε:ℂ)) := by
      change (ε:ℂ)⁻¹*q 0-1=(ε:ℂ)⁻¹*(q 0-(ε:ℂ))
      field_simp [hc]
    have h1 : ((ε:ℂ)⁻¹ • q) 1-1=(ε:ℂ)⁻¹*(q 1-(ε:ℂ)) := by
      change (ε:ℂ)⁻¹*q 1-1=(ε:ℂ)⁻¹*(q 1-(ε:ℂ))
      field_simp [hc]
    refine ⟨?_,?_,?_⟩
    · rw [h0,norm_mul,hnorm]
      exact (inv_mul_lt_iff₀ hε).mpr hr
    · rw [h1,norm_mul,hnorm]
      exact (inv_mul_lt_iff₀ hε).mpr hs
    · change ‖(ε:ℂ)⁻¹*q 2‖<δ
      rw [norm_mul,hnorm]
      exact (inv_mul_lt_iff₀ hε).mpr ht
  have hA (q : Fin 3 → ℂ)
      (hq : ‖q 0-(ε:ℂ)‖<ε*δ ∧ ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2‖<ε*δ) :
      AnalyticAt ℂ (pairOriginalAmbientA u ε) q := by
    obtain ⟨hr,hs,ht⟩ := hscale q hq.1 hq.2.1 hq.2.2
    have hlin : AnalyticAt ℂ (fun q : Fin 3 → ℂ => (ε:ℂ)⁻¹ • q) q :=
      (analyticAt_const : AnalyticAt ℂ (fun _ : Fin 3 → ℂ => (ε:ℂ)⁻¹) q).smul analyticAt_id
    exact analyticAt_const.add (analyticAt_const.mul ((hAnA _ ⟨hr,hs,ht⟩).comp hlin))
  have hB (q : Fin 3 → ℂ)
      (hq : ‖q 0-(ε:ℂ)‖<ε*δ ∧ ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2‖<ε*δ) :
      AnalyticAt ℂ (pairOriginalAmbientB u ε) q := by
    obtain ⟨hr,hs,ht⟩ := hscale q hq.1 hq.2.1 hq.2.2
    have hlin : AnalyticAt ℂ (fun q : Fin 3 → ℂ => (ε:ℂ)⁻¹ • q) q :=
      (analyticAt_const : AnalyticAt ℂ (fun _ : Fin 3 → ℂ => (ε:ℂ)⁻¹) q).smul analyticAt_id
    exact (hAnB _ ⟨hr,hs,ht⟩).comp hlin
  refine ⟨hA,hB,?_,?_,?_⟩
  · intro q hq
    have hcoord : AnalyticAt ℂ (fun q : Fin 3 → ℂ => q 2) q :=
      (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q
    exact (hA q hq).add (hcoord.mul (hB q hq))
  · intro q hr hs ht
    obtain ⟨hr',hs',ht'⟩ := hscale q hr hs ht
    obtain ⟨hbA,hbB⟩ := hBound _ hr' hs' ht'
    have hbAn : ‖pairOriginalAmbientA u ε q‖≤‖u 0‖+
        ε*(16*physicalKSPointwiseAmplitude M A F0 W) := by
      calc
        _≤‖u 0‖+‖(ε:ℂ)*pairAmbientPhysicalA (originScaledDifference u ε) 1
          ((ε:ℂ)⁻¹ • q)‖ := norm_add_le _ _
        _=‖u 0‖+ε*‖pairAmbientPhysicalA (originScaledDifference u ε) 1
          ((ε:ℂ)⁻¹ • q)‖ := by
            rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
        _≤_ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hbA hε.le)
    refine ⟨hbAn,hbB,?_⟩
    calc
      _≤‖pairOriginalAmbientA u ε q‖+‖q 2*pairOriginalAmbientB u ε q‖ := norm_add_le _ _
      _=‖pairOriginalAmbientA u ε q‖+‖q 2‖*‖pairOriginalAmbientB u ε q‖ := by rw [norm_mul]
      _≤(‖u 0‖+ε*(16*physicalKSPointwiseAmplitude M A F0 W))+
          ε*δ*((32*(7*physicalKSPointwiseRate M A)^2)*
            (16*physicalKSPointwiseAmplitude M A F0 W)) := by
        exact add_le_add hbAn (mul_le_mul ht.le hbB (norm_nonneg _) (mul_pos hε hδ).le)
      _=_ := by dsimp [pairAmbientNormalizedBound]; ring
  · intro x hr hs ht
    have hpos (i : Fin 2) : position (ε⁻¹ • x) i=ε⁻¹ • position x i := by
      simpa only [electronPositionCLM_apply] using (electronPositionCLM i).map_smul ε⁻¹ x
    have hnormR (v : Position) : ‖ε⁻¹ • v‖=ε⁻¹*‖v‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hε)]
    have hdist (v : Position) (hv : |‖v‖-ε|<ε*δ) : |‖ε⁻¹ • v‖-1|<δ := by
      rw [hnormR]
      have he : ε⁻¹*‖v‖-1=ε⁻¹*(‖v‖-ε) := by field_simp [hε.ne']
      rw [he,abs_mul,abs_of_pos (inv_pos.mpr hε)]
      exact (inv_mul_lt_iff₀ hε).mpr hv
    have h0 : |‖position (ε⁻¹ • x) 0‖-1|<δ := by rw [hpos]; exact hdist _ hr
    have h1 : |‖position (ε⁻¹ • x) 1‖-1|<δ := by rw [hpos]; exact hdist _ hs
    have hsep : ‖position (ε⁻¹ • x) 0-position (ε⁻¹ • x) 1‖<δ := by
      rw [hpos,hpos,←smul_sub,hnormR]
      exact (inv_mul_lt_iff₀ hε).mpr ht
    have hid := hId (ε⁻¹ • x) h0 h1 hsep
    have hq : (fun j => (pairAmbientPhysicalDistances (ε⁻¹ • x) j:ℂ)) =
        (ε:ℂ)⁻¹ • (fun j => (pairAmbientPhysicalDistances x j:ℂ)) := by
      rw [pairAmbientPhysicalDistances_positive_smul ε⁻¹ (inv_pos.mpr hε)]
      ext j
      simp [Complex.ofReal_inv,Complex.ofReal_mul]
    have hsepEq : (‖position (ε⁻¹ • x) 0-position (ε⁻¹ • x) 1‖:ℂ) =
        (ε:ℂ)⁻¹*(‖position x 0-position x 1‖:ℂ) := by
      rw [hpos,hpos,←smul_sub,hnormR]
      simp [Complex.ofReal_inv,Complex.ofReal_mul]
    rw [hq,hsepEq] at hid
    have hnormalized : originScaledDifference u ε (ε⁻¹ • x)=
        (ε:ℂ)⁻¹*(u x-u 0) := by
      simp [originScaledDifference,smul_smul,hε.ne',RCLike.real_smul_eq_coe_mul]
    rw [hnormalized] at hid
    change u x=u 0+(ε:ℂ)*pairAmbientPhysicalA (originScaledDifference u ε) 1
      ((ε:ℂ)⁻¹ • (fun j => (pairAmbientPhysicalDistances x j:ℂ)))+
      (‖position x 0-position x 1‖:ℂ)*pairAmbientPhysicalB (originScaledDifference u ε) 1
      ((ε:ℂ)⁻¹ • (fun j => (pairAmbientPhysicalDistances x j:ℂ)))
    field_simp [hc] at hid
    simp only [one_div] at hid
    linear_combination hid

#print axioms pair_original_ambient_positive_rescaling
#print axioms pairAmbientPhysicalDistances_positive_smul
theorem twoElectron_scalar_ground_pair_ambient_distance_reconstruction
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
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδ,hambient⟩ :=
      twoElectron_scalar_ground_pair_ambient_analytic_descent Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδ,hambient,?_⟩
  intro ε hε hlim
  exact pair_original_ambient_positive_rescaling u hε hδ (hambient ε hε hlim)

#print axioms twoElectron_scalar_ground_pair_ambient_distance_reconstruction

end ManyBody.S8

