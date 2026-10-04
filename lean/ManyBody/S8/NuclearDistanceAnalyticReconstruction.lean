import ManyBody.S8.Internal.NuclearDistancePhysicalReconstruction
import ManyBody.S8.Internal.PhysicalAnalyticDescentGermBridge
import ManyBody.S8.Internal.PhysicalDistanceConfigurationOrbit
import ManyBody.S8.Internal.PhysicalCollisionCoordinateScaling
import TwoElectronScalarGroundAxisAnalyticDescent_v1
/-! Ambient holomorphic reconstruction of the actual scalar ground function
in the three physical distances near an isolated nuclear collision.

The normalized distance variables are the selected nuclear distance r, the
other nuclear distance s, and the electron separation d. The genuine SO(2)
axis descent is evaluated at z=(r²+s²-d²)/(2s) and w=r²-z². These rational
coordinates are holomorphic on a full complex polydisc around (0,1,1), with
an explicit radius that lies inside the actual bounded axis domain.

The physical identity first uses the proved real canonical representative,
then the genuine two-vector O(3) orbit bridge. Collinear configurations and
the selected collision r=0 are included. Positive-scale rescaling gives the
literal original function u(0)+epsilon H(q/epsilon), holomorphic around
(0,epsilon,epsilon), with an explicit norm bound and the exact original
physical identity.

The final theorem consumes the recovered normalized scalar Coulomb ground
state at Z >= 2. It retains its original H² graph, spectral ground witness,
a.e. representative, real, exchange and O(3) laws. Its analytic/PDE premises
are discharged by that actual ground state's pointwise KS data. The other
nuclear and electron-pair collisions, the triple collision, pair-distance
reconstruction, and a complete Rung 2 assertion remain outside this claim.
-/
set_option autoImplicit false
noncomputable section
open scoped NNReal
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

def nuclearAmbientPhysicalRadius (M A : ℝ) : ℝ :=
  min ((physicalDescentNeighborhoodRadius M A)^2)
    (32*(7*physicalKSPointwiseRate M A)^2)⁻¹

def nuclearAmbientRetainedRadius (M A : ℝ) : ℝ :=
  min (1/4) (min (physicalKSAnalyticAxisRadius M A/8)
    (min (nuclearAmbientPhysicalRadius M A) (physicalDescentNeighborhoodRadius M A)))

theorem nuclearAmbientRetainedRadius_pos {M A : ℝ} (hA : 1≤A) :
    0<nuclearAmbientRetainedRadius M A := by
  have hS : 0<7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have haxis := physicalKSAnalyticAxisRadius_pos (M := M) hA
  dsimp only [nuclearAmbientRetainedRadius,nuclearAmbientPhysicalRadius,physicalDescentNeighborhoodRadius]
  positivity

theorem nuclear_rotation_invariant_ambient_descent
    (g : Configuration 2 → ℂ) (i : Fin 2) {M A F0 W : ℝ}
    (hA : 1≤A) (hF0 : 0≤F0)
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W)
    (hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
      g (configurationRotation 2 Q x)=g x) :
    0<nuclearAmbientRetainedRadius M A ∧
    AnalyticOnNhd ℂ
      (nuclearAmbientDescendedFunction
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (nuclearDistanceRealSpectator 1) 1)
      {q | ‖q 0‖<nuclearAmbientRetainedRadius M A ∧
        ‖q 1-1‖<nuclearAmbientRetainedRadius M A ∧
        ‖q 2-1‖<nuclearAmbientRetainedRadius M A} ∧
    (∀ q, ‖q 0‖<nuclearAmbientRetainedRadius M A →
      ‖q 1-1‖<nuclearAmbientRetainedRadius M A →
      ‖q 2-1‖<nuclearAmbientRetainedRadius M A →
      ‖nuclearAmbientDescendedFunction
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (nuclearDistanceRealSpectator 1) 1 q‖ ≤
        16*physicalKSPointwiseAmplitude M A F0 W+
          nuclearAmbientRetainedRadius M A*((32*(7*physicalKSPointwiseRate M A)^2)*
            (16*physicalKSPointwiseAmplitude M A F0 W))) ∧    ∀ r s u : ℝ, 0≤r → 0<s → 0≤u → |r-s|≤u → u≤r+s →
      r<nuclearAmbientRetainedRadius M A → |s-1|<nuclearAmbientRetainedRadius M A →
      |u-1|<nuclearAmbientRetainedRadius M A →
      g (nuclearKSPhysicalCoordinates i (nuclearDistanceRealSpatial r s u)
        (nuclearDistanceRealSpectator s)) =
      nuclearAmbientDescendedFunction
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (nuclearDistanceRealSpectator 1) 1 ![(r:ℂ),(s:ℂ),(u:ℂ)] := by
  have hh := physicalKSAnalyticAxisRadius_pos (M := M) hA
  have hδσ : nuclearAmbientRetainedRadius M A≤(1:ℝ)/4 := min_le_left _ _
  have hδh : nuclearAmbientRetainedRadius M A≤physicalKSAnalyticAxisRadius M A/8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδX : nuclearAmbientRetainedRadius M A≤nuclearAmbientPhysicalRadius M A :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδT : nuclearAmbientRetainedRadius M A≤physicalDescentNeighborhoodRadius M A :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbox := nuclearKSPhysicalAnalyticDescent_data g i hdata hA hF0
  have haxis := nuclearKSPhysicalAxisAnalyticDescent_data g i hdata hA hF0 hg hh le_rfl
  have hambient := physical_nuclear_ambient_axis_data haxis (by norm_num : 0<(1:ℝ)) hh hδσ hδh
  refine ⟨nuclearAmbientRetainedRadius_pos hA,hambient.1,hambient.2,?_⟩
  intro r s u hr hs hu hlo hhi hrδ hsδ huδ
  have hW := nuclearDistanceRealW_nonneg hr hs hu hlo hhi
  have hrh : r<physicalKSAnalyticAxisRadius M A := by
    have hrd := hrδ.trans_le hδh
    linarith
  have hsh : |s-1|<physicalKSAnalyticAxisRadius M A := by
    have hsd := hsδ.trans_le hδh
    linarith
  exact physical_nuclear_ambient_canonical_identity hbox haxis hr hW hh
    (hrδ.trans_le hδX) (hsδ.trans_le hδT) hrh hsh

#print axioms nuclearAmbientRetainedRadius_pos
#print axioms nuclear_rotation_invariant_ambient_descent

theorem nuclear_rotation_invariant_ambient_original
    (g : Configuration 2 → ℂ) (i : Fin 2) {M A F0 W : ℝ}
    (hA : 1≤A) (hF0 : 0≤F0)
    (hdata : PhysicalKSBoxPointwiseData
      ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W)
    (hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
      g (configurationRotation 2 Q x)=g x) :
    0<nuclearAmbientRetainedRadius M A ∧
    AnalyticOnNhd ℂ
      (nuclearAmbientDescendedFunction
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (nuclearDistanceRealSpectator 1) 1)
      {q | ‖q 0‖<nuclearAmbientRetainedRadius M A ∧
        ‖q 1-1‖<nuclearAmbientRetainedRadius M A ∧
        ‖q 2-1‖<nuclearAmbientRetainedRadius M A} ∧
    (∀ q, ‖q 0‖<nuclearAmbientRetainedRadius M A →
      ‖q 1-1‖<nuclearAmbientRetainedRadius M A →
      ‖q 2-1‖<nuclearAmbientRetainedRadius M A →
      ‖nuclearAmbientDescendedFunction
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (nuclearDistanceRealSpectator 1) 1 q‖ ≤
        16*physicalKSPointwiseAmplitude M A F0 W+
          nuclearAmbientRetainedRadius M A*((32*(7*physicalKSPointwiseRate M A)^2)*
            (16*physicalKSPointwiseAmplitude M A F0 W))) ∧
    ∀ X T : Position, 0<‖T‖ → ‖X‖<nuclearAmbientRetainedRadius M A →
      |‖T‖-1|<nuclearAmbientRetainedRadius M A →
      |‖X-T‖-1|<nuclearAmbientRetainedRadius M A →
      g (nuclearKSPhysicalCoordinates i X T) =
      nuclearAmbientDescendedFunction
        ((g ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
        (nuclearDistanceRealSpectator 1) 1 ![(‖X‖:ℂ),(‖T‖:ℂ),(‖X-T‖:ℂ)] := by
  obtain ⟨hδ,hAn,hBound,hCanon⟩ := nuclear_rotation_invariant_ambient_descent g i hA hF0 hdata hg
  refine ⟨hδ,hAn,hBound,?_⟩
  intro X T hTs hX hT hsep
  calc
    _ = g (nuclearKSPhysicalCoordinates i
        (nuclearDistanceRealSpatial ‖X‖ ‖T‖ ‖X-T‖) (nuclearDistanceRealSpectator ‖T‖)) :=
      nuclear_rotation_invariant_eq_canonical_distances g hg i X T hTs
    _ = _ := hCanon ‖X‖ ‖T‖ ‖X-T‖ (norm_nonneg X) hTs (norm_nonneg (X-T))
      (abs_norm_sub_norm_le X T) (norm_sub_le X T) hX hT hsep

#print axioms nuclear_rotation_invariant_ambient_original

def nuclearAmbientNormalizedBound (M A F0 W : ℝ) : ℝ :=
  16*physicalKSPointwiseAmplitude M A F0 W+
    nuclearAmbientRetainedRadius M A*((32*(7*physicalKSPointwiseRate M A)^2)*
      (16*physicalKSPointwiseAmplitude M A F0 W))

def nuclearOriginalAmbientFunction (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε : ℝ) (q : Fin 3 → ℂ) : ℂ :=
  u 0+(ε:ℂ)*nuclearAmbientDescendedFunction
    ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
    (nuclearDistanceRealSpectator 1) 1 ((ε:ℂ)⁻¹ • q)

def PhysicalNuclearAmbientReconstruction (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε δ B : ℝ) : Prop :=
  AnalyticOnNhd ℂ (nuclearOriginalAmbientFunction u i ε)
    {q | ‖q 0‖<ε*δ ∧ ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2-(ε:ℂ)‖<ε*δ} ∧
  (∀ q, ‖q 0‖<ε*δ → ‖q 1-(ε:ℂ)‖<ε*δ → ‖q 2-(ε:ℂ)‖<ε*δ →
    ‖nuclearOriginalAmbientFunction u i ε q‖≤‖u 0‖+ε*B) ∧
  ∀ X T : Position, 0<‖T‖ → ‖X‖<ε*δ → |‖T‖-ε|<ε*δ →
    |‖X-T‖-ε|<ε*δ → u (nuclearKSPhysicalCoordinates i X T)=
      nuclearOriginalAmbientFunction u i ε ![(‖X‖:ℂ),(‖T‖:ℂ),(‖X-T‖:ℂ)]

theorem nuclear_original_ambient_positive_rescaling
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A) (hF0 : 0≤F0)
    (hdata : PhysicalKSBoxPointwiseData
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W)
    (hu : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
      u (configurationRotation 2 Q x)=u x) :
    PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
      (nuclearAmbientNormalizedBound M A F0 W) := by
  have hg : ∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
      originScaledDifference u ε (configurationRotation 2 Q x)=originScaledDifference u ε x :=
    fun Q x => originScaledDifference_configurationRotation u Q (hu Q) ε x
  obtain ⟨_,hAn,hBound,hId⟩ :=
    nuclear_rotation_invariant_ambient_original (originScaledDifference u ε) i hA hF0 hdata hg
  have hc : (ε:ℂ)≠0 := by exact_mod_cast hε.ne'
  have hnorm : ‖(ε:ℂ)⁻¹‖=ε⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  have hscale (q : Fin 3 → ℂ)
      (hr : ‖q 0‖<ε*nuclearAmbientRetainedRadius M A)
      (hs : ‖q 1-(ε:ℂ)‖<ε*nuclearAmbientRetainedRadius M A)
      (ht : ‖q 2-(ε:ℂ)‖<ε*nuclearAmbientRetainedRadius M A) :
      ‖(((ε:ℂ)⁻¹ • q) 0)‖<nuclearAmbientRetainedRadius M A ∧
      ‖(((ε:ℂ)⁻¹ • q) 1)-1‖<nuclearAmbientRetainedRadius M A ∧
      ‖(((ε:ℂ)⁻¹ • q) 2)-1‖<nuclearAmbientRetainedRadius M A := by
    have h0 : (ε:ℂ)⁻¹*q 0=((ε:ℂ)⁻¹ • q) 0 := rfl
    have h1 : ((ε:ℂ)⁻¹ • q) 1-1=(ε:ℂ)⁻¹*(q 1-(ε:ℂ)) := by
      change (ε:ℂ)⁻¹*q 1-1=(ε:ℂ)⁻¹*(q 1-(ε:ℂ))
      field_simp [hc]
    have h2 : ((ε:ℂ)⁻¹ • q) 2-1=(ε:ℂ)⁻¹*(q 2-(ε:ℂ)) := by
      change (ε:ℂ)⁻¹*q 2-1=(ε:ℂ)⁻¹*(q 2-(ε:ℂ))
      field_simp [hc]
    refine ⟨?_,?_,?_⟩
    · rw [←h0,norm_mul,hnorm]
      exact (inv_mul_lt_iff₀ hε).mpr hr
    · rw [h1,norm_mul,hnorm]
      exact (inv_mul_lt_iff₀ hε).mpr hs
    · rw [h2,norm_mul,hnorm]
      exact (inv_mul_lt_iff₀ hε).mpr ht
  refine ⟨?_,?_,?_⟩
  · intro q hq
    obtain ⟨hr,hs,ht⟩ := hscale q hq.1 hq.2.1 hq.2.2
    have hlin : AnalyticAt ℂ (fun q : Fin 3 → ℂ => (ε:ℂ)⁻¹ • q) q :=
      (analyticAt_const : AnalyticAt ℂ (fun _ : Fin 3 → ℂ => (ε:ℂ)⁻¹) q).smul analyticAt_id
    have hcomp := (hAn ((ε:ℂ)⁻¹ • q) ⟨hr,hs,ht⟩).comp hlin
    exact analyticAt_const.add (analyticAt_const.mul hcomp)
  · intro q hr hs ht
    obtain ⟨hr',hs',ht'⟩ := hscale q hr hs ht
    have hb := hBound ((ε:ℂ)⁻¹ • q) hr' hs' ht'
    let v := nuclearAmbientDescendedFunction
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) 1 ((ε:ℂ)⁻¹ • q)
    have hbn : ‖v‖≤nuclearAmbientNormalizedBound M A F0 W := hb
    change ‖u 0+(ε:ℂ)*v‖≤‖u 0‖+ε*nuclearAmbientNormalizedBound M A F0 W
    calc
      _≤‖u 0‖+‖(ε:ℂ)*v‖ := norm_add_le _ _
      _=‖u 0‖+ε*‖v‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
      _≤_ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hbn hε.le)
  · intro X T hTpos hX hT hsep
    have hnormR (v : Position) : ‖ε⁻¹ • v‖=ε⁻¹*‖v‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hε)]
    have hX' : ‖ε⁻¹ • X‖<nuclearAmbientRetainedRadius M A := by
      rw [hnormR]; exact (inv_mul_lt_iff₀ hε).mpr hX
    have hT' : |‖ε⁻¹ • T‖-1|<nuclearAmbientRetainedRadius M A := by
      rw [hnormR]
      have heq : ε⁻¹*‖T‖-1=ε⁻¹*(‖T‖-ε) := by field_simp [hε.ne']
      rw [heq,abs_mul,abs_of_pos (inv_pos.mpr hε)]
      exact (inv_mul_lt_iff₀ hε).mpr hT
    have hsep' : |‖ε⁻¹ • X-ε⁻¹ • T‖-1|<nuclearAmbientRetainedRadius M A := by
      rw [←smul_sub,hnormR]
      have heq : ε⁻¹*‖X-T‖-1=ε⁻¹*(‖X-T‖-ε) := by field_simp [hε.ne']
      rw [heq,abs_mul,abs_of_pos (inv_pos.mpr hε)]
      exact (inv_mul_lt_iff₀ hε).mpr hsep
    have hTp : 0<‖ε⁻¹ • T‖ := by rw [hnormR]; exact mul_pos (inv_pos.mpr hε) hTpos
    have hid := hId (ε⁻¹ • X) (ε⁻¹ • T) hTp hX' hT' hsep'
    have hq : ![(‖ε⁻¹ • X‖:ℂ),(‖ε⁻¹ • T‖:ℂ),(‖ε⁻¹ • X-ε⁻¹ • T‖:ℂ)] =
        (ε:ℂ)⁻¹ • ![(‖X‖:ℂ),(‖T‖:ℂ),(‖X-T‖:ℂ)] := by
      ext j
      fin_cases j <;> simp [←smul_sub,hnormR,Complex.ofReal_inv,Complex.ofReal_mul]
    rw [hq] at hid
    have hp : ε • (ε⁻¹ • (X,T))=(X,T) := by simp [smul_smul,hε.ne']
    have hc0 : originalNuclearPhysicalCoordinatesCLM i 0=0 := map_zero _
    have hnormalized := originScaledDifference_comp_physical_coordinates u
      (originalNuclearPhysicalCoordinatesCLM i) ε (ε⁻¹ • (X,T))
    rw [hp,hc0] at hnormalized
    change originScaledDifference u ε
      (nuclearKSPhysicalCoordinates i (ε⁻¹ • X) (ε⁻¹ • T))=
      (u (nuclearKSPhysicalCoordinates i X T)-u 0)/(ε:ℂ) at hnormalized
    rw [hnormalized] at hid
    change u (nuclearKSPhysicalCoordinates i X T)=u 0+(ε:ℂ)*_
    rw [←hid]
    field_simp [hc]
    ring

#print axioms nuclear_original_ambient_positive_rescaling

theorem twoElectron_scalar_ground_nuclear_ambient_distance_reconstruction
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ C_H M A : ℝ, 1≤C_H ∧ 1≤M ∧ 1≤A ∧
    ∃ f : SpatialL2 2, ∃ u : Configuration 2 → ℂ, ∃ L : ℝ≥0, ∃ R : ℝ,
      ‖f‖=1 ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      spectralGroundEnergy 2 Z=((variationalGroundEnergy 2 Z).toReal:EReal) ∧
      (((variationalGroundEnergy 2 Z).toReal:ℂ) ∈
        TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z)) ∧
      (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
        (variationalGroundEnergy 2 Z).toReal≤z.re) ∧
      LocallyLipschitz u ∧ (f:Configuration 2 → ℂ)=ᵐ[MeasureTheory.volume]u ∧
      (∀ x, ‖u x‖≤coulombMoserBoundCoefficient 2 Z (variationalGroundEnergy 2 Z).toReal) ∧
      (∀ x, (u x).im=0) ∧ (∀ x, u (permuteSpace twoElectronSwap x)=u x) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, u (configurationRotation 2 Q x)=u x) ∧
      0<L ∧ 0<R ∧ LipschitzOnWith L u (Metric.ball 0 R) ∧
      0<nuclearAmbientRetainedRadius M A ∧
      ∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
        PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
          (nuclearAmbientNormalizedBound M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,_hW,_htail,hN,_hP,
    _haxis,_haxisN,_haxisP⟩ :=
    twoElectron_scalar_ground_axis_analytic_descent_with_H2_decay Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,nuclearAmbientRetainedRadius_pos hA,?_⟩
  intro ε hε hlim i
  have ht : ‖nuclearDistanceRealSpectator (1:ℝ)‖=1 :=
    nuclearDistanceRealSpectator_norm (by norm_num)
  exact nuclear_original_ambient_positive_rescaling u i hε hA hF0
    (hN ε hε hlim i _ ht).1.1.1 hrotation

#print axioms twoElectron_scalar_ground_nuclear_ambient_distance_reconstruction
end ManyBody.S8