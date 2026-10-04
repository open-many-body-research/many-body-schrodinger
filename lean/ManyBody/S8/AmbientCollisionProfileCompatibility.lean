import ManyBody.S8.NuclearDistanceAmbientCompatibility
import ManyBody.S8.PairDistanceAnalyticReconstruction
import ManyBody.S8.Internal.EvenAmbientProfileUniqueness
import ManyBody.S8.Internal.NuclearOriginalAmbientProfiles
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace ManyBody.S8
open TheoremT.Continuum

def pairOriginalDistancePolydisc (ε δ : ℝ) : Set (Fin 3 → ℂ) :=
  {q | ‖q 0-(ε:ℂ)‖<ε*δ ∧ ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2‖<ε*δ}

theorem pairOriginalDistancePolydisc_open (ε δ : ℝ) :
    IsOpen (pairOriginalDistancePolydisc ε δ) :=
  (isOpen_lt ((continuous_apply 0).sub continuous_const).norm continuous_const).inter
    ((isOpen_lt ((continuous_apply 1).sub continuous_const).norm continuous_const).inter
      (isOpen_lt (continuous_apply 2).norm continuous_const))

theorem pairOriginalDistancePolydisc_convex (ε δ : ℝ) :
    Convex ℝ (pairOriginalDistancePolydisc ε δ) := by
  rintro x hx y hy a b ha hb hab
  have h0 := (convex_ball (ε:ℂ) (ε*δ))
    (by simpa only [mem_ball,dist_eq_norm] using hx.1)
    (by simpa only [mem_ball,dist_eq_norm] using hy.1) ha hb hab
  have h1 := (convex_ball (ε:ℂ) (ε*δ))
    (by simpa only [mem_ball,dist_eq_norm] using hx.2.1)
    (by simpa only [mem_ball,dist_eq_norm] using hy.2.1) ha hb hab
  have h2 := (convex_ball (0:ℂ) (ε*δ))
    (by simpa only [mem_ball,dist_zero_right] using hx.2.2)
    (by simpa only [mem_ball,dist_zero_right] using hy.2.2) ha hb hab
  exact ⟨by simpa only [Pi.add_apply,Pi.smul_apply,mem_ball,dist_eq_norm] using h0,
    by simpa only [Pi.add_apply,Pi.smul_apply,mem_ball,dist_eq_norm] using h1,
    by simpa only [Pi.add_apply,Pi.smul_apply,mem_ball,dist_zero_right] using h2⟩

theorem pair_ambient_reconstruction_feasible
    {u : Configuration 2 → ℂ} {ε M A F0 W δ : ℝ}
    (hrec : PhysicalPairAmbientReconstruction u ε M A F0 W δ)
    (p : Fin 3 → ℝ) (hp : p∈strictPhysicalDistanceTriangles)
    (hdom : ambientRealCast p∈pairOriginalDistancePolydisc ε δ) :
    pairOriginalAmbientFunction u ε (ambientRealCast p)=
      u (nuclearKSPhysicalCoordinates 0 (nuclearDistanceRealSpatial (p 0) (p 1) (p 2))
        (nuclearDistanceRealSpectator (p 1))) := by
  let x := nuclearKSPhysicalCoordinates (0:Fin 2)
    (nuclearDistanceRealSpatial (p 0) (p 1) (p 2)) (nuclearDistanceRealSpectator (p 1))
  obtain ⟨h0,h1,hsep⟩ := nuclearDistanceRealRepresentative_configuration_norms
    hp.1.le hp.2.1 hp.2.2.1.le hp.2.2.2.1.le hp.2.2.2.2.le
  have hpd : pairAmbientPhysicalDistances x=p := by
    ext j; fin_cases j
    · simpa [pairAmbientPhysicalDistances,x] using h0
    · simpa [pairAmbientPhysicalDistances] using h1
    · simpa [pairAmbientPhysicalDistances] using hsep
  have hr : |p 0-ε|<ε*δ := by
    simpa only [ambientRealCast_apply,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hdom.1
  have hs : |p 1-ε|<ε*δ := by
    simpa only [ambientRealCast_apply,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hdom.2.1
  have ht : p 2<ε*δ := by
    simpa only [ambientRealCast_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp.2.2.1] using hdom.2.2
  have hid := hrec.2.2.2.2 x (by rw [h0]; exact hr) (by rw [h1]; exact hs) (by rw [hsep]; exact ht)
  rw [hpd] at hid
  exact hid.symm

theorem pair_ambient_two_scale_compatibility
    {u : Configuration 2 → ℂ} {ε₀ ε₁ δ₀ δ₁ M₀ A₀ F₀ W₀ M₁ A₁ F₁ W₁ σ : ℝ}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hδ₀ : 0<δ₀) (hδ₁ : 0<δ₁) (hσ : 0<σ)
    (hrec₀ : PhysicalPairAmbientReconstruction u ε₀ M₀ A₀ F₀ W₀ δ₀)
    (hrec₁ : PhysicalPairAmbientReconstruction u ε₁ M₁ A₁ F₁ W₁ δ₁)
    (hσ₀ : |σ-ε₀|<ε₀*δ₀) (hσ₁ : |σ-ε₁|<ε₁*δ₁) :
    EqOn (pairOriginalAmbientFunction u ε₀) (pairOriginalAmbientFunction u ε₁)
      (pairOriginalDistancePolydisc ε₀ δ₀∩pairOriginalDistancePolydisc ε₁ δ₁) ∧
    pairOriginalAmbientFunction u ε₀ =ᶠ[𝓝 ![(σ:ℂ),(σ:ℂ),0]] pairOriginalAmbientFunction u ε₁ := by
  let U := pairOriginalDistancePolydisc ε₀ δ₀∩pairOriginalDistancePolydisc ε₁ δ₁
  have hUopen : IsOpen U :=
    (pairOriginalDistancePolydisc_open _ _).inter (pairOriginalDistancePolydisc_open _ _)
  have hUconn : IsPreconnected U :=
    ((pairOriginalDistancePolydisc_convex _ _).inter (pairOriginalDistancePolydisc_convex _ _)).isPreconnected
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
  let a : Fin 3 → ℝ := ![σ,σ,r]
  have haT : a∈strictPhysicalDistanceTriangles := by
    refine ⟨hσ,hσ,hr,?_,?_⟩
    · simpa [a] using hr
    · change r<σ+σ; linarith
  have haU : ambientRealCast a∈U := by
    constructor <;> (refine ⟨?_,?_,?_⟩)
    · simpa [a,ambientRealCast_apply,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa [a,ambientRealCast_apply,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa [a,ambientRealCast_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hr₀
    · simpa [a,ambientRealCast_apply,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₁
    · simpa [a,ambientRealCast_apply,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₁
    · simpa [a,ambientRealCast_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hr₁
  have hreal : (fun p => pairOriginalAmbientFunction u ε₀ (ambientRealCast p))
      =ᶠ[𝓝 a] (fun p => pairOriginalAmbientFunction u ε₁ (ambientRealCast p)) := by
    filter_upwards [strictPhysicalDistanceTriangles_open.mem_nhds haT,
      (hUopen.preimage ambientRealCast.continuous).mem_nhds haU] with p hp hpU
    exact (pair_ambient_reconstruction_feasible hrec₀ p hp hpU.1).trans
      (pair_ambient_reconstruction_feasible hrec₁ p hp hpU.2).symm
  have hnear := complex_real_germ_identity a (hrec₀.2.2.1 _ haU.1) (hrec₁.2.2.1 _ haU.2) hreal
  have hAn₀ : AnalyticOnNhd ℂ (pairOriginalAmbientFunction u ε₀) U := fun q hq => hrec₀.2.2.1 q hq.1
  have hAn₁ : AnalyticOnNhd ℂ (pairOriginalAmbientFunction u ε₁) U := fun q hq => hrec₁.2.2.1 q hq.2
  have hfull := hAn₀.eqOn_of_preconnected_of_eventuallyEq hAn₁ hUconn haU hnear
  refine ⟨hfull,?_⟩
  have hcenter : ![(σ:ℂ),(σ:ℂ),0]∈U := by
    constructor <;> (refine ⟨?_,?_,?_⟩)
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa using hrad₀
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₁
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₁
    · simpa using hrad₁
  filter_upwards [hUopen.mem_nhds hcenter] with q hq
  exact hfull hq

#print axioms pair_ambient_reconstruction_feasible
#print axioms pair_ambient_two_scale_compatibility

theorem pairAmbientDistanceInput_selected_even (σ : ℝ) (c : ℂ) (q : Fin 3 → ℂ) :
    pairAmbientDistanceInput σ (c • ambientCoordinateReflect 2 q)=pairAmbientDistanceInput σ (c • q) := by
  apply Prod.ext
  · simp [pairAmbientDistanceInput,pairAmbientAxisW,pairAmbientAxisZ,pairAmbientTau,
      pairAmbientCenterPolynomial,ambientCoordinateReflect,mul_neg]
  · ext j; fin_cases j <;>
      simp [pairAmbientDistanceInput,pairAmbientAxisW,pairAmbientAxisZ,pairAmbientTau,
        pairAmbientCenterPolynomial,ambientCoordinateReflect,mul_neg]

theorem pairOriginalAmbient_profiles_even (u : Configuration 2 → ℂ) (ε : ℝ) (q : Fin 3 → ℂ) :
    pairOriginalAmbientA u ε (ambientCoordinateReflect 2 q)=pairOriginalAmbientA u ε q ∧
    pairOriginalAmbientB u ε (ambientCoordinateReflect 2 q)=pairOriginalAmbientB u ε q := by
  constructor <;>
    simp only [pairOriginalAmbientA,pairOriginalAmbientB,pairAmbientPhysicalA,pairAmbientPhysicalB,
      Function.comp_apply,pairAmbientDistanceInput_selected_even]

theorem nuclear_common_distance_polydisc_nonzero
    {ε₀ ε₁ δ₀ δ₁ σ : ℝ} (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hδ₀ : 0<δ₀) (hδ₁ : 0<δ₁)
    (hσ₀ : |σ-ε₀|<ε₀*δ₀) (hσ₁ : |σ-ε₁|<ε₁*δ₁) :
    ∃ q∈nuclearOriginalDistancePolydisc ε₀ δ₀∩nuclearOriginalDistancePolydisc ε₁ δ₁, q 0≠0 := by
  let r : ℝ := min (ε₀*δ₀) (ε₁*δ₁)/2
  have hr : 0<r := by dsimp [r]; positivity
  have hr₀ : r<ε₀*δ₀ := by have hh := min_le_left (ε₀*δ₀) (ε₁*δ₁); dsimp [r]; nlinarith [mul_pos hε₀ hδ₀]
  have hr₁ : r<ε₁*δ₁ := by have hh := min_le_right (ε₀*δ₀) (ε₁*δ₁); dsimp [r]; nlinarith [mul_pos hε₁ hδ₁]
  refine ⟨![(r:ℂ),(σ:ℂ),(σ:ℂ)],⟨?_,?_⟩,?_⟩
  · refine ⟨?_,?_,?_⟩
    · simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hr₀
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₀
  · refine ⟨?_,?_,?_⟩
    · simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hr₁
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₁
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₁
  · simpa using (Complex.ofReal_ne_zero.mpr hr.ne')

theorem pair_common_distance_polydisc_nonzero
    {ε₀ ε₁ δ₀ δ₁ σ : ℝ} (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hδ₀ : 0<δ₀) (hδ₁ : 0<δ₁)
    (hσ₀ : |σ-ε₀|<ε₀*δ₀) (hσ₁ : |σ-ε₁|<ε₁*δ₁) :
    ∃ q∈pairOriginalDistancePolydisc ε₀ δ₀∩pairOriginalDistancePolydisc ε₁ δ₁, q 2≠0 := by
  let r : ℝ := min (ε₀*δ₀) (ε₁*δ₁)/2
  have hr : 0<r := by dsimp [r]; positivity
  have hr₀ : r<ε₀*δ₀ := by have hh := min_le_left (ε₀*δ₀) (ε₁*δ₁); dsimp [r]; nlinarith [mul_pos hε₀ hδ₀]
  have hr₁ : r<ε₁*δ₁ := by have hh := min_le_right (ε₀*δ₀) (ε₁*δ₁); dsimp [r]; nlinarith [mul_pos hε₁ hδ₁]
  refine ⟨![(σ:ℂ),(σ:ℂ),(r:ℂ)],⟨?_,?_⟩,?_⟩
  · refine ⟨?_,?_,?_⟩
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₀
    · simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hr₀
  · refine ⟨?_,?_,?_⟩
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₁
    · simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hσ₁
    · simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hr₁
  · simpa using (Complex.ofReal_ne_zero.mpr hr.ne')

theorem nuclear_ambient_two_scale_separate_profiles
    {u : Configuration 2 → ℂ} {i : Fin 2} {ε₀ ε₁ M A F0 W B₀ B₁ σ : ℝ}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hA : 1≤A) (hσ : 0<σ)
    (hrec₀ : PhysicalNuclearAmbientReconstruction u i ε₀ (nuclearAmbientRetainedRadius M A) B₀)
    (hrec₁ : PhysicalNuclearAmbientReconstruction u i ε₁ (nuclearAmbientRetainedRadius M A) B₁)
    (haxis₀ : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε₀ ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (haxis₁ : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε₁ ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (hσ₀ : |σ-ε₀|<ε₀*nuclearAmbientRetainedRadius M A)
    (hσ₁ : |σ-ε₁|<ε₁*nuclearAmbientRetainedRadius M A) :
    EqOn (nuclearOriginalAmbientA u i ε₀) (nuclearOriginalAmbientA u i ε₁)
      (nuclearOriginalDistancePolydisc ε₀ (nuclearAmbientRetainedRadius M A)∩
        nuclearOriginalDistancePolydisc ε₁ (nuclearAmbientRetainedRadius M A)) ∧
    EqOn (nuclearOriginalAmbientB u i ε₀) (nuclearOriginalAmbientB u i ε₁)
      (nuclearOriginalDistancePolydisc ε₀ (nuclearAmbientRetainedRadius M A)∩
        nuclearOriginalDistancePolydisc ε₁ (nuclearAmbientRetainedRadius M A)) := by
  have hδ := nuclearAmbientRetainedRadius_pos (M := M) hA
  have hfull := (nuclear_ambient_two_scale_compatibility hε₀ hε₁ hδ hδ hσ hrec₀ hrec₁ hσ₀ hσ₁).1
  have hAn₀ := nuclearOriginalAmbient_profiles_analytic u i hε₀ hA haxis₀
  have hAn₁ := nuclearOriginalAmbient_profiles_analytic u i hε₁ hA haxis₁
  let U := nuclearOriginalDistancePolydisc ε₀ (nuclearAmbientRetainedRadius M A)∩
    nuclearOriginalDistancePolydisc ε₁ (nuclearAmbientRetainedRadius M A)
  have hB₀ : AnalyticOnNhd ℂ (nuclearOriginalAmbientB u i ε₀) U := fun q hq => hAn₀.2 q hq.1
  have hB₁ : AnalyticOnNhd ℂ (nuclearOriginalAmbientB u i ε₁) U := fun q hq => hAn₁.2 q hq.2
  have hreflect : ∀ q∈U, ambientCoordinateReflect 0 q∈U := by
    intro q hq
    simpa [U,nuclearOriginalDistancePolydisc,ambientCoordinateReflect] using hq
  exact holomorphic_even_profiles_compatible 0
    ((nuclearOriginalDistancePolydisc_open _ _).inter (nuclearOriginalDistancePolydisc_open _ _))
    (((nuclearOriginalDistancePolydisc_convex _ _).inter (nuclearOriginalDistancePolydisc_convex _ _)).isPreconnected)
    hB₀ hB₁ hreflect
    (fun q _ => (nuclearOriginalAmbient_profiles_even u i ε₀ q).1)
    (fun q _ => (nuclearOriginalAmbient_profiles_even u i ε₁ q).1)
    (fun q _ => (nuclearOriginalAmbient_profiles_even u i ε₀ q).2)
    (fun q _ => (nuclearOriginalAmbient_profiles_even u i ε₁ q).2)
    (fun q _ => nuclearOriginalAmbient_profiles_recombine u i hε₀ q)
    (fun q _ => nuclearOriginalAmbient_profiles_recombine u i hε₁ q)
    hfull (nuclear_common_distance_polydisc_nonzero hε₀ hε₁ hδ hδ hσ₀ hσ₁)

theorem pair_ambient_two_scale_separate_profiles
    {u : Configuration 2 → ℂ} {ε₀ ε₁ δ₀ δ₁ M₀ A₀ F₀ W₀ M₁ A₁ F₁ W₁ σ : ℝ}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hδ₀ : 0<δ₀) (hδ₁ : 0<δ₁) (hσ : 0<σ)
    (hrec₀ : PhysicalPairAmbientReconstruction u ε₀ M₀ A₀ F₀ W₀ δ₀)
    (hrec₁ : PhysicalPairAmbientReconstruction u ε₁ M₁ A₁ F₁ W₁ δ₁)
    (hσ₀ : |σ-ε₀|<ε₀*δ₀) (hσ₁ : |σ-ε₁|<ε₁*δ₁) :
    EqOn (pairOriginalAmbientA u ε₀) (pairOriginalAmbientA u ε₁)
      (pairOriginalDistancePolydisc ε₀ δ₀∩pairOriginalDistancePolydisc ε₁ δ₁) ∧
    EqOn (pairOriginalAmbientB u ε₀) (pairOriginalAmbientB u ε₁)
      (pairOriginalDistancePolydisc ε₀ δ₀∩pairOriginalDistancePolydisc ε₁ δ₁) := by
  have hfull := (pair_ambient_two_scale_compatibility hε₀ hε₁ hδ₀ hδ₁ hσ hrec₀ hrec₁ hσ₀ hσ₁).1
  let U := pairOriginalDistancePolydisc ε₀ δ₀∩pairOriginalDistancePolydisc ε₁ δ₁
  have hB₀ : AnalyticOnNhd ℂ (pairOriginalAmbientB u ε₀) U := fun q hq => hrec₀.2.1 q hq.1
  have hB₁ : AnalyticOnNhd ℂ (pairOriginalAmbientB u ε₁) U := fun q hq => hrec₁.2.1 q hq.2
  have hreflect : ∀ q∈U, ambientCoordinateReflect 2 q∈U := by
    intro q hq
    simpa [U,pairOriginalDistancePolydisc,ambientCoordinateReflect] using hq
  exact holomorphic_even_profiles_compatible 2
    ((pairOriginalDistancePolydisc_open _ _).inter (pairOriginalDistancePolydisc_open _ _))
    (((pairOriginalDistancePolydisc_convex _ _).inter (pairOriginalDistancePolydisc_convex _ _)).isPreconnected)
    hB₀ hB₁ hreflect
    (fun q _ => (pairOriginalAmbient_profiles_even u ε₀ q).1)
    (fun q _ => (pairOriginalAmbient_profiles_even u ε₁ q).1)
    (fun q _ => (pairOriginalAmbient_profiles_even u ε₀ q).2)
    (fun q _ => (pairOriginalAmbient_profiles_even u ε₁ q).2)
    (fun _ _ => rfl) (fun _ _ => rfl) hfull
    (pair_common_distance_polydisc_nonzero hε₀ hε₁ hδ₀ hδ₁ hσ₀ hσ₁)

#print axioms pairOriginalAmbient_profiles_even
#print axioms nuclear_ambient_two_scale_separate_profiles
#print axioms pair_ambient_two_scale_separate_profiles

def AmbientDistanceProfilesCompatible
    (a₀ b₀ h₀ a₁ b₁ h₁ : (Fin 3 → ℂ) → ℂ) (U : Set (Fin 3 → ℂ)) : Prop :=
  EqOn a₀ a₁ U ∧ EqOn b₀ b₁ U ∧ EqOn h₀ h₁ U ∧
  ∀ q∈U, (a₀ =ᶠ[𝓝 q] a₁) ∧ (b₀ =ᶠ[𝓝 q] b₁) ∧ (h₀ =ᶠ[𝓝 q] h₁) ∧
    ∀ n : ℕ, iteratedFDeriv ℂ n a₀ q=iteratedFDeriv ℂ n a₁ q ∧
      iteratedFDeriv ℂ n b₀ q=iteratedFDeriv ℂ n b₁ q ∧
      iteratedFDeriv ℂ n h₀ q=iteratedFDeriv ℂ n h₁ q

theorem ambient_profiles_compatible_of_eqOn
    {a₀ b₀ h₀ a₁ b₁ h₁ : (Fin 3 → ℂ) → ℂ} {U : Set (Fin 3 → ℂ)}
    (hU : IsOpen U) (ha : EqOn a₀ a₁ U) (hb : EqOn b₀ b₁ U) (hh : EqOn h₀ h₁ U) :
    AmbientDistanceProfilesCompatible a₀ b₀ h₀ a₁ b₁ h₁ U := by
  refine ⟨ha,hb,hh,?_⟩
  intro q hq
  have hga : a₀ =ᶠ[𝓝 q] a₁ := by
    filter_upwards [hU.mem_nhds hq] with z hz; exact ha hz
  have hgb : b₀ =ᶠ[𝓝 q] b₁ := by
    filter_upwards [hU.mem_nhds hq] with z hz; exact hb hz
  have hgh : h₀ =ᶠ[𝓝 q] h₁ := by
    filter_upwards [hU.mem_nhds hq] with z hz; exact hh hz
  exact ⟨hga,hgb,hgh,fun n => ⟨(hga.iteratedFDeriv ℂ n).eq_of_nhds,
    (hgb.iteratedFDeriv ℂ n).eq_of_nhds,(hgh.iteratedFDeriv ℂ n).eq_of_nhds⟩⟩

def NuclearAmbientProfilesCompatible (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε₀ ε₁ M A : ℝ) : Prop :=
  AmbientDistanceProfilesCompatible
    (nuclearOriginalAmbientA u i ε₀) (nuclearOriginalAmbientB u i ε₀)
    (nuclearOriginalAmbientFunction u i ε₀)
    (nuclearOriginalAmbientA u i ε₁) (nuclearOriginalAmbientB u i ε₁)
    (nuclearOriginalAmbientFunction u i ε₁)
    (nuclearOriginalDistancePolydisc ε₀ (nuclearAmbientRetainedRadius M A)∩
      nuclearOriginalDistancePolydisc ε₁ (nuclearAmbientRetainedRadius M A))

def PairAmbientProfilesCompatible (u : Configuration 2 → ℂ) (ε₀ δ₀ ε₁ δ₁ : ℝ) : Prop :=
  AmbientDistanceProfilesCompatible
    (pairOriginalAmbientA u ε₀) (pairOriginalAmbientB u ε₀) (pairOriginalAmbientFunction u ε₀)
    (pairOriginalAmbientA u ε₁) (pairOriginalAmbientB u ε₁) (pairOriginalAmbientFunction u ε₁)
    (pairOriginalDistancePolydisc ε₀ δ₀∩pairOriginalDistancePolydisc ε₁ δ₁)

theorem nuclear_ambient_two_scale_profile_jets
    {u : Configuration 2 → ℂ} {i : Fin 2} {ε₀ ε₁ M A F0 W B₀ B₁ σ : ℝ}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hA : 1≤A) (hσ : 0<σ)
    (hrec₀ : PhysicalNuclearAmbientReconstruction u i ε₀ (nuclearAmbientRetainedRadius M A) B₀)
    (hrec₁ : PhysicalNuclearAmbientReconstruction u i ε₁ (nuclearAmbientRetainedRadius M A) B₁)
    (haxis₀ : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε₀ ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (haxis₁ : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε₁ ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (hσ₀ : |σ-ε₀|<ε₀*nuclearAmbientRetainedRadius M A)
    (hσ₁ : |σ-ε₁|<ε₁*nuclearAmbientRetainedRadius M A) :
    NuclearAmbientProfilesCompatible u i ε₀ ε₁ M A := by
  have hδ := nuclearAmbientRetainedRadius_pos (M:=M) hA
  obtain ⟨ha,hb⟩ := nuclear_ambient_two_scale_separate_profiles
    hε₀ hε₁ hA hσ hrec₀ hrec₁ haxis₀ haxis₁ hσ₀ hσ₁
  have hh := (nuclear_ambient_two_scale_compatibility
    hε₀ hε₁ hδ hδ hσ hrec₀ hrec₁ hσ₀ hσ₁).1
  exact ambient_profiles_compatible_of_eqOn
    ((nuclearOriginalDistancePolydisc_open _ _).inter (nuclearOriginalDistancePolydisc_open _ _)) ha hb hh

theorem pair_ambient_two_scale_profile_jets
    {u : Configuration 2 → ℂ} {ε₀ ε₁ δ₀ δ₁ M₀ A₀ F₀ W₀ M₁ A₁ F₁ W₁ σ : ℝ}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hδ₀ : 0<δ₀) (hδ₁ : 0<δ₁) (hσ : 0<σ)
    (hrec₀ : PhysicalPairAmbientReconstruction u ε₀ M₀ A₀ F₀ W₀ δ₀)
    (hrec₁ : PhysicalPairAmbientReconstruction u ε₁ M₁ A₁ F₁ W₁ δ₁)
    (hσ₀ : |σ-ε₀|<ε₀*δ₀) (hσ₁ : |σ-ε₁|<ε₁*δ₁) :
    PairAmbientProfilesCompatible u ε₀ δ₀ ε₁ δ₁ := by
  obtain ⟨ha,hb⟩ := pair_ambient_two_scale_separate_profiles
    hε₀ hε₁ hδ₀ hδ₁ hσ hrec₀ hrec₁ hσ₀ hσ₁
  have hh := (pair_ambient_two_scale_compatibility
    hε₀ hε₁ hδ₀ hδ₁ hσ hrec₀ hrec₁ hσ₀ hσ₁).1
  exact ambient_profiles_compatible_of_eqOn
    ((pairOriginalDistancePolydisc_open _ _).inter (pairOriginalDistancePolydisc_open _ _)) ha hb hh

open scoped NNReal

theorem twoElectron_scalar_ground_ambient_coefficient_compatibility
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
        ∀ i : Fin 2, ∀ σ : ℝ, 0<σ →
        |σ-ε₀|<ε₀*nuclearAmbientRetainedRadius M A →
        |σ-ε₁|<ε₁*nuclearAmbientRetainedRadius M A →
        NuclearAmbientProfilesCompatible u i ε₀ ε₁ M A) ∧
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
  · intro ε₀ ε₁ hε₀ hlim₀ hε₁ hlim₁ i σ hσ hσ₀ hσ₁
    exact nuclear_ambient_two_scale_profile_jets hε₀ hε₁ hA hσ
      (hNrec ε₀ hε₀ hlim₀ i) (hNrec ε₁ hε₁ hlim₁ i)
      (hNA ε₀ hε₀ hlim₀ i) (hNA ε₁ hε₁ hlim₁ i) hσ₀ hσ₁
  · intro ε₀ ε₁ hε₀ hlim₀ hε₁ hlim₁ σ hσ hσ₀ hσ₁
    exact pair_ambient_two_scale_profile_jets hε₀ hε₁ hδP hδP hσ
      (hOriginal ε₀ hε₀ hlim₀) (hOriginal ε₁ hε₁ hlim₁) hσ₀ hσ₁

#print axioms nuclear_ambient_two_scale_profile_jets
#print axioms pair_ambient_two_scale_profile_jets
#print axioms twoElectron_scalar_ground_ambient_coefficient_compatibility
end ManyBody.S8