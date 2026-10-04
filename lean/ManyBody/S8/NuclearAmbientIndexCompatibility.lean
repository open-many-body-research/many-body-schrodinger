import ManyBody.S8.AmbientCollisionProfileCompatibility
/-! Nuclear electron-index and scale compatibility of actual distance profiles.

The original coordinate map for index one is exactly the physical exchange
of the index-zero coordinate map, with the same selected position X and
spectator T. Original exchange symmetry therefore gives equality at every
actual reconstructed real configuration. A genuine feasible real triangle
ball and complex continuation transport that identity to the entire common
complex distance domain. Actual selected-distance parity then separates the
literal A/B profiles, including the collision axis. All complex germs and
all iterated Frechet jets agree at every overlap point.

Local distance coordinates mean selected nuclear radius, spectator nuclear
radius, and pair distance for each index. Thus comparison keeps these same
local meanings while exchanging original electron labels. The physical
endpoint retains the same actual normalized scalar Coulomb ground state,
its original graph/spectral/physical facts, and its already proved exchange
law. No profile equality or profile symmetry is assumed. The same explicit
positive, selected-state scale/overlap domains remain in force.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal
namespace ManyBody.S8
open TheoremT.Continuum

theorem nuclear_physical_coordinates_exchange (X T : Position) :
    permuteSpace twoElectronSwap (nuclearKSPhysicalCoordinates 0 X T)=
      nuclearKSPhysicalCoordinates 1 X T := by
  ext ⟨j,k⟩
  change (position (nuclearKSPhysicalCoordinates 0 X T) (twoElectronSwap j)) k=
    (position (nuclearKSPhysicalCoordinates 1 X T) j) k
  rw [position_nuclearKSPhysicalCoordinates,position_nuclearKSPhysicalCoordinates]
  fin_cases j <;> simp [twoElectronSwap]

theorem exchange_invariant_nuclear_coordinates
    {u : Configuration 2 → ℂ}
    (hexchange : ∀ x, u (permuteSpace twoElectronSwap x)=u x)
    (i₀ i₁ : Fin 2) (X T : Position) :
    u (nuclearKSPhysicalCoordinates i₀ X T)=u (nuclearKSPhysicalCoordinates i₁ X T) := by
  have h01 : u (nuclearKSPhysicalCoordinates 0 X T)=u (nuclearKSPhysicalCoordinates 1 X T) := by
    rw [←nuclear_physical_coordinates_exchange]
    exact (hexchange _).symm
  fin_cases i₀ <;> fin_cases i₁
  · rfl
  · exact h01
  · exact h01.symm
  · rfl

#print axioms nuclear_physical_coordinates_exchange
#print axioms exchange_invariant_nuclear_coordinates
theorem nuclear_ambient_index_and_scale_compatibility
    {u : Configuration 2 → ℂ} {i₀ i₁ : Fin 2} {ε₀ ε₁ δ₀ δ₁ B₀ B₁ σ : ℝ}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hδ₀ : 0<δ₀) (hδ₁ : 0<δ₁) (hσ : 0<σ)
    (hexchange : ∀ x, u (permuteSpace twoElectronSwap x)=u x)
    (hrec₀ : PhysicalNuclearAmbientReconstruction u i₀ ε₀ δ₀ B₀)
    (hrec₁ : PhysicalNuclearAmbientReconstruction u i₁ ε₁ δ₁ B₁)
    (hσ₀ : |σ-ε₀|<ε₀*δ₀) (hσ₁ : |σ-ε₁|<ε₁*δ₁) :
    EqOn (nuclearOriginalAmbientFunction u i₀ ε₀) (nuclearOriginalAmbientFunction u i₁ ε₁)
      (nuclearOriginalDistancePolydisc ε₀ δ₀∩nuclearOriginalDistancePolydisc ε₁ δ₁) ∧
    nuclearOriginalAmbientFunction u i₀ ε₀ =ᶠ[𝓝 ![0,(σ:ℂ),(σ:ℂ)]]
      nuclearOriginalAmbientFunction u i₁ ε₁ := by
  let U := nuclearOriginalDistancePolydisc ε₀ δ₀∩nuclearOriginalDistancePolydisc ε₁ δ₁
  have hUopen : IsOpen U :=
    (nuclearOriginalDistancePolydisc_open _ _).inter (nuclearOriginalDistancePolydisc_open _ _)
  have hUconn : IsPreconnected U :=
    ((nuclearOriginalDistancePolydisc_convex _ _).inter (nuclearOriginalDistancePolydisc_convex _ _)).isPreconnected
  have hrad₀ : 0<ε₀*δ₀ := mul_pos hε₀ hδ₀
  have hrad₁ : 0<ε₁*δ₁ := mul_pos hε₁ hδ₁
  let r : ℝ := min (ε₀*δ₀) (min (ε₁*δ₁) σ)/2
  have hr : 0<r := by dsimp [r]; positivity
  have hr₀ : r<ε₀*δ₀ := by
    have hh := min_le_left (ε₀*δ₀) (min (ε₁*δ₁) σ); dsimp [r]; linarith
  have hr₁ : r<ε₁*δ₁ := by
    have hh := (min_le_right (ε₀*δ₀) (min (ε₁*δ₁) σ)).trans (min_le_left (ε₁*δ₁) σ)
    dsimp [r]; linarith
  have hrσ : r<σ := by
    have hh := (min_le_right (ε₀*δ₀) (min (ε₁*δ₁) σ)).trans (min_le_right (ε₁*δ₁) σ)
    dsimp [r]; linarith
  let a : Fin 3 → ℝ := ![r,σ,σ]
  have haT : a∈strictPhysicalDistanceTriangles := by
    refine ⟨hr,hσ,hσ,?_,?_⟩
    · change |r-σ|<σ
      rw [abs_of_neg (sub_neg.mpr hrσ)]; linarith
    · change σ<r+σ; linarith
  have haU : ambientRealCast a∈U := by
    constructor <;> (refine ⟨?_,?_,?_⟩)
    · simpa only [a,ambientRealCast_apply,Matrix.cons_val_zero,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos hr] using hr₀
    · simpa [a,ambientRealCast_apply,←Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa [a,ambientRealCast_apply,←Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa only [a,ambientRealCast_apply,Matrix.cons_val_zero,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos hr] using hr₁
    · simpa [a,ambientRealCast_apply,←Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs] using hσ₁
    · simpa [a,ambientRealCast_apply,←Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs] using hσ₁
  have hreal : (fun p => nuclearOriginalAmbientFunction u i₀ ε₀ (ambientRealCast p))
      =ᶠ[𝓝 a] (fun p => nuclearOriginalAmbientFunction u i₁ ε₁ (ambientRealCast p)) := by
    filter_upwards [strictPhysicalDistanceTriangles_open.mem_nhds haT,
      (hUopen.preimage ambientRealCast.continuous).mem_nhds haU] with p hp hpU
    exact (nuclear_ambient_reconstruction_feasible hrec₀ p hp hpU.1).trans
      ((exchange_invariant_nuclear_coordinates hexchange i₀ i₁
        (nuclearDistanceRealSpatial (p 0) (p 1) (p 2)) (nuclearDistanceRealSpectator (p 1))).trans
        (nuclear_ambient_reconstruction_feasible hrec₁ p hp hpU.2).symm)
  have hnear := complex_real_germ_identity a (hrec₀.1 _ haU.1) (hrec₁.1 _ haU.2) hreal
  have hAn₀ : AnalyticOnNhd ℂ (nuclearOriginalAmbientFunction u i₀ ε₀) U :=
    fun q hq => hrec₀.1 q hq.1
  have hAn₁ : AnalyticOnNhd ℂ (nuclearOriginalAmbientFunction u i₁ ε₁) U :=
    fun q hq => hrec₁.1 q hq.2
  have hfull := hAn₀.eqOn_of_preconnected_of_eventuallyEq hAn₁ hUconn haU hnear
  refine ⟨hfull,?_⟩
  have hcenter : ![0,(σ:ℂ),(σ:ℂ)]∈U := by
    constructor <;> (refine ⟨?_,?_,?_⟩)
    · simpa only [Matrix.cons_val_zero,norm_zero] using hrad₀
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa only [Matrix.cons_val_zero,norm_zero] using hrad₁
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₁
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₁
  filter_upwards [hUopen.mem_nhds hcenter] with q hq
  exact hfull hq


#print axioms nuclear_ambient_index_and_scale_compatibility

def NuclearAmbientIndexProfilesCompatible (u : Configuration 2 → ℂ) (i₀ i₁ : Fin 2)
    (ε₀ ε₁ M A : ℝ) : Prop :=
  AmbientDistanceProfilesCompatible
    (nuclearOriginalAmbientA u i₀ ε₀) (nuclearOriginalAmbientB u i₀ ε₀)
    (nuclearOriginalAmbientFunction u i₀ ε₀)
    (nuclearOriginalAmbientA u i₁ ε₁) (nuclearOriginalAmbientB u i₁ ε₁)
    (nuclearOriginalAmbientFunction u i₁ ε₁)
    (nuclearOriginalDistancePolydisc ε₀ (nuclearAmbientRetainedRadius M A)∩
      nuclearOriginalDistancePolydisc ε₁ (nuclearAmbientRetainedRadius M A))

theorem nuclear_ambient_index_and_scale_profile_jets
    {u : Configuration 2 → ℂ} {i₀ i₁ : Fin 2} {ε₀ ε₁ M A F0 W B₀ B₁ σ : ℝ}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hA : 1≤A) (hσ : 0<σ)
    (hexchange : ∀ x, u (permuteSpace twoElectronSwap x)=u x)
    (hrec₀ : PhysicalNuclearAmbientReconstruction u i₀ ε₀ (nuclearAmbientRetainedRadius M A) B₀)
    (hrec₁ : PhysicalNuclearAmbientReconstruction u i₁ ε₁ (nuclearAmbientRetainedRadius M A) B₁)
    (haxis₀ : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε₀ ∘ nuclearKSLift i₀) ∘ (physicalSpectatorReindexAt i₀).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (haxis₁ : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε₁ ∘ nuclearKSLift i₁) ∘ (physicalSpectatorReindexAt i₁).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (hσ₀ : |σ-ε₀|<ε₀*nuclearAmbientRetainedRadius M A)
    (hσ₁ : |σ-ε₁|<ε₁*nuclearAmbientRetainedRadius M A) :
    NuclearAmbientIndexProfilesCompatible u i₀ i₁ ε₀ ε₁ M A := by
  have hδ := nuclearAmbientRetainedRadius_pos (M:=M) hA
  have hfull := (nuclear_ambient_index_and_scale_compatibility
    hε₀ hε₁ hδ hδ hσ hexchange hrec₀ hrec₁ hσ₀ hσ₁).1
  have hAn₀ := nuclearOriginalAmbient_profiles_analytic u i₀ hε₀ hA haxis₀
  have hAn₁ := nuclearOriginalAmbient_profiles_analytic u i₁ hε₁ hA haxis₁
  let U := nuclearOriginalDistancePolydisc ε₀ (nuclearAmbientRetainedRadius M A)∩
    nuclearOriginalDistancePolydisc ε₁ (nuclearAmbientRetainedRadius M A)
  have hB₀ : AnalyticOnNhd ℂ (nuclearOriginalAmbientB u i₀ ε₀) U := fun q hq => hAn₀.2 q hq.1
  have hB₁ : AnalyticOnNhd ℂ (nuclearOriginalAmbientB u i₁ ε₁) U := fun q hq => hAn₁.2 q hq.2
  have hreflect : ∀ q∈U, ambientCoordinateReflect 0 q∈U := by
    intro q hq
    simpa [U,nuclearOriginalDistancePolydisc,ambientCoordinateReflect] using hq
  have hopen : IsOpen U :=
    (nuclearOriginalDistancePolydisc_open _ _).inter (nuclearOriginalDistancePolydisc_open _ _)
  obtain ⟨ha,hb⟩ := holomorphic_even_profiles_compatible 0 hopen
    (((nuclearOriginalDistancePolydisc_convex _ _).inter (nuclearOriginalDistancePolydisc_convex _ _)).isPreconnected)
    hB₀ hB₁ hreflect
    (fun q _ => (nuclearOriginalAmbient_profiles_even u i₀ ε₀ q).1)
    (fun q _ => (nuclearOriginalAmbient_profiles_even u i₁ ε₁ q).1)
    (fun q _ => (nuclearOriginalAmbient_profiles_even u i₀ ε₀ q).2)
    (fun q _ => (nuclearOriginalAmbient_profiles_even u i₁ ε₁ q).2)
    (fun q _ => nuclearOriginalAmbient_profiles_recombine u i₀ hε₀ q)
    (fun q _ => nuclearOriginalAmbient_profiles_recombine u i₁ hε₁ q)
    hfull (nuclear_common_distance_polydisc_nonzero hε₀ hε₁ hδ hδ hσ₀ hσ₁)
  exact ambient_profiles_compatible_of_eqOn hopen ha hb hfull

#print axioms nuclear_ambient_index_and_scale_profile_jets
theorem twoElectron_scalar_ground_nuclear_index_coefficient_compatibility
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
      0<nuclearAmbientRetainedRadius M A ∧ 0<pairAmbientDistanceRadius 1 M A ∧
      (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
        PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
          (nuclearAmbientNormalizedBound M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H))) ∧
      (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
        PhysicalPairAmbientReconstruction u ε M A
          (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
          (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
      (∀ ε₀ ε₁ : ℝ, 0<ε₀ → ε₀≤min 1 (R/4) → 0<ε₁ → ε₁≤min 1 (R/4) →
        ∀ i₀ i₁ : Fin 2, ∀ σ : ℝ, 0<σ →
        |σ-ε₀|<ε₀*nuclearAmbientRetainedRadius M A →
        |σ-ε₁|<ε₁*nuclearAmbientRetainedRadius M A →
        NuclearAmbientIndexProfilesCompatible u i₀ i₁ ε₀ ε₁ M A) ∧
      (∀ ε₀ ε₁ : ℝ, 0<ε₀ → ε₀≤min 1 (R/4) → 0<ε₁ → ε₁≤min 1 (R/4) →
        ∀ σ : ℝ, 0<σ →
        |σ-ε₀|<ε₀*pairAmbientDistanceRadius 1 M A →
        |σ-ε₁|<ε₁*pairAmbientDistanceRadius 1 M A →
        PairAmbientProfilesCompatible u ε₀ (pairAmbientDistanceRadius 1 M A)
          ε₁ (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hOriginal⟩ :=
      twoElectron_scalar_ground_pair_ambient_distance_reconstruction Z hZ
  have hδN := nuclearAmbientRetainedRadius_pos (M:=M) hA
  have ht : ‖nuclearDistanceRealSpectator 1‖=1 := by
    simpa using nuclearDistanceRealSpectator_norm (by norm_num : 0≤(1:ℝ))
  have hNrec : ∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
      PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
        (nuclearAmbientNormalizedBound M A
          (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
          (((L:ℝ)^2+‖u 0‖^2)*C_H)) := by
    intro ε hε hlim i
    exact nuclear_original_ambient_positive_rescaling u i hε hA hF0
      (hN ε hε hlim i (nuclearDistanceRealSpectator 1) ht).1.1.1 hrotation
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hδN,hδP,hNrec,hOriginal,?_,?_⟩
  · intro ε₀ ε₁ hε₀ hlim₀ hε₁ hlim₁ i₀ i₁ σ hσ hσ₀ hσ₁
    exact nuclear_ambient_index_and_scale_profile_jets hε₀ hε₁ hA hσ hexchange
      (hNrec ε₀ hε₀ hlim₀ i₀) (hNrec ε₁ hε₁ hlim₁ i₁)
      (hNA ε₀ hε₀ hlim₀ i₀) (hNA ε₁ hε₁ hlim₁ i₁) hσ₀ hσ₁
  · intro ε₀ ε₁ hε₀ hlim₀ hε₁ hlim₁ σ hσ hσ₀ hσ₁
    exact pair_ambient_two_scale_profile_jets hε₀ hε₁ hδP hδP hσ
      (hOriginal ε₀ hε₀ hlim₀) (hOriginal ε₁ hε₁ hlim₁) hσ₀ hσ₁


#print axioms twoElectron_scalar_ground_nuclear_index_coefficient_compatibility
end ManyBody.S8