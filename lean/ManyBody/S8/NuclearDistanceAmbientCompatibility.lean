import ManyBody.S8.NuclearDistanceAnalyticReconstruction
import ManyBody.S8.Internal.AmbientRealSliceUniqueness
/-! Literal holomorphic nuclear-distance compatibility across positive scales.

Two actual reconstructions of the same original physical u in the same
selected nuclear coordinate map agree on a nonempty real open subset of the
feasible triangle region near any shared collision-distance point. The
canonical representative proves this equality from their actual physical
identities. A real-slice uniqueness bridge then gives a complex germ, and
analytic continuation on the convex intersection gives equality throughout
the entire common complex polydisc. Every genuine complex Frechet jet at the
shared collision point agrees.

The principal ground consumer retains the same original normalized scalar
Coulomb ground state and all displayed graph/spectral/physical facts from
S8-018, at its explicit Z >= 2 charge range. No equality assumption, new
state, index change, collision-type transition, triple collision, or global
analytic atlas is inserted.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace ManyBody.S8
open TheoremT.Continuum

def nuclearOriginalDistancePolydisc (ε δ : ℝ) : Set (Fin 3 → ℂ) :=
  {q | ‖q 0‖<ε*δ ∧ ‖q 1-(ε:ℂ)‖<ε*δ ∧ ‖q 2-(ε:ℂ)‖<ε*δ}

theorem nuclearOriginalDistancePolydisc_open (ε δ : ℝ) :
    IsOpen (nuclearOriginalDistancePolydisc ε δ) :=
  (isOpen_lt (continuous_apply 0).norm continuous_const).inter
    ((isOpen_lt ((continuous_apply 1).sub continuous_const).norm continuous_const).inter
      (isOpen_lt ((continuous_apply 2).sub continuous_const).norm continuous_const))

theorem nuclearOriginalDistancePolydisc_convex (ε δ : ℝ) :
    Convex ℝ (nuclearOriginalDistancePolydisc ε δ) := by
  rintro x hx y hy a b ha hb hab
  have h0 := (convex_ball (0:ℂ) (ε*δ))
    (by simpa only [mem_ball,dist_zero_right] using hx.1)
    (by simpa only [mem_ball,dist_zero_right] using hy.1) ha hb hab
  have h1 := (convex_ball (ε:ℂ) (ε*δ))
    (by simpa only [mem_ball,dist_eq_norm] using hx.2.1)
    (by simpa only [mem_ball,dist_eq_norm] using hy.2.1) ha hb hab
  have h2 := (convex_ball (ε:ℂ) (ε*δ))
    (by simpa only [mem_ball,dist_eq_norm] using hx.2.2)
    (by simpa only [mem_ball,dist_eq_norm] using hy.2.2) ha hb hab
  exact ⟨by simpa only [Pi.add_apply,Pi.smul_apply,mem_ball,dist_zero_right] using h0,
    by simpa only [Pi.add_apply,Pi.smul_apply,mem_ball,dist_eq_norm] using h1,
    by simpa only [Pi.add_apply,Pi.smul_apply,mem_ball,dist_eq_norm] using h2⟩

def strictPhysicalDistanceTriangles : Set (Fin 3 → ℝ) :=
  {p | 0<p 0 ∧ 0<p 1 ∧ 0<p 2 ∧ |p 0-p 1|<p 2 ∧ p 2<p 0+p 1}

theorem strictPhysicalDistanceTriangles_open : IsOpen strictPhysicalDistanceTriangles :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        ((isOpen_lt ((continuous_apply 0).sub (continuous_apply 1)).abs (continuous_apply 2)).inter
          (isOpen_lt (continuous_apply 2) ((continuous_apply 0).add (continuous_apply 1))))))

theorem nuclear_ambient_reconstruction_feasible
    {u : Configuration 2 → ℂ} {i : Fin 2} {ε δ B : ℝ}
    (hrec : PhysicalNuclearAmbientReconstruction u i ε δ B)
    (p : Fin 3 → ℝ) (hp : p∈strictPhysicalDistanceTriangles)
    (hdom : ambientRealCast p∈nuclearOriginalDistancePolydisc ε δ) :
    nuclearOriginalAmbientFunction u i ε (ambientRealCast p)=
      u (nuclearKSPhysicalCoordinates i (nuclearDistanceRealSpatial (p 0) (p 1) (p 2))
        (nuclearDistanceRealSpectator (p 1))) := by
  obtain ⟨hw,hX,hT,hsep⟩ := nuclearDistanceRealRepresentative_norms
    hp.1.le hp.2.1 hp.2.2.1.le hp.2.2.2.1.le hp.2.2.2.2.le
  have hr : p 0<ε*δ := by simpa only [ambientRealCast_apply,Complex.norm_real,Real.norm_eq_abs,
    (abs_of_pos hp.1)] using hdom.1
  have hs : |p 1-ε|<ε*δ := by simpa only [ambientRealCast_apply,←Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] using hdom.2.1
  have hu : |p 2-ε|<ε*δ := by simpa only [ambientRealCast_apply,←Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] using hdom.2.2
  have hid := hrec.2.2 (nuclearDistanceRealSpatial (p 0) (p 1) (p 2))
    (nuclearDistanceRealSpectator (p 1)) (by rw [hT]; exact hp.2.1)
    (by rw [hX]; exact hr) (by rw [hT]; exact hs) (by rw [hsep]; exact hu)
  rw [hX,hT,hsep] at hid
  have hvec : ![((p 0):ℂ),((p 1):ℂ),((p 2):ℂ)]=ambientRealCast p := by
    ext j; fin_cases j <;> rfl
  rw [hvec] at hid
  exact hid.symm

theorem nuclear_ambient_two_scale_compatibility
    {u : Configuration 2 → ℂ} {i : Fin 2} {ε₀ ε₁ δ₀ δ₁ B₀ B₁ σ : ℝ}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hδ₀ : 0<δ₀) (hδ₁ : 0<δ₁) (hσ : 0<σ)
    (hrec₀ : PhysicalNuclearAmbientReconstruction u i ε₀ δ₀ B₀)
    (hrec₁ : PhysicalNuclearAmbientReconstruction u i ε₁ δ₁ B₁)
    (hσ₀ : |σ-ε₀|<ε₀*δ₀) (hσ₁ : |σ-ε₁|<ε₁*δ₁) :
    EqOn (nuclearOriginalAmbientFunction u i ε₀) (nuclearOriginalAmbientFunction u i ε₁)
      (nuclearOriginalDistancePolydisc ε₀ δ₀∩nuclearOriginalDistancePolydisc ε₁ δ₁) ∧
    nuclearOriginalAmbientFunction u i ε₀ =ᶠ[𝓝 ![0,(σ:ℂ),(σ:ℂ)]]
      nuclearOriginalAmbientFunction u i ε₁ := by
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
  have hreal : (fun p => nuclearOriginalAmbientFunction u i ε₀ (ambientRealCast p))
      =ᶠ[𝓝 a] (fun p => nuclearOriginalAmbientFunction u i ε₁ (ambientRealCast p)) := by
    filter_upwards [strictPhysicalDistanceTriangles_open.mem_nhds haT,
      (hUopen.preimage ambientRealCast.continuous).mem_nhds haU] with p hp hpU
    exact (nuclear_ambient_reconstruction_feasible hrec₀ p hp hpU.1).trans
      (nuclear_ambient_reconstruction_feasible hrec₁ p hp hpU.2).symm
  have hnear := complex_real_germ_identity a (hrec₀.1 _ haU.1) (hrec₁.1 _ haU.2) hreal
  have hAn₀ : AnalyticOnNhd ℂ (nuclearOriginalAmbientFunction u i ε₀) U :=
    fun q hq => hrec₀.1 q hq.1
  have hAn₁ : AnalyticOnNhd ℂ (nuclearOriginalAmbientFunction u i ε₁) U :=
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

#print axioms nuclearOriginalDistancePolydisc_convex
#print axioms nuclear_ambient_reconstruction_feasible
#print axioms nuclear_ambient_two_scale_compatibility

def NuclearAmbientDistanceCompatible (u : Configuration 2 → ℂ) (i : Fin 2)
    (ε₀ δ₀ ε₁ δ₁ σ : ℝ) : Prop :=
  EqOn (nuclearOriginalAmbientFunction u i ε₀) (nuclearOriginalAmbientFunction u i ε₁)
    (nuclearOriginalDistancePolydisc ε₀ δ₀∩nuclearOriginalDistancePolydisc ε₁ δ₁) ∧
  (nuclearOriginalAmbientFunction u i ε₀ =ᶠ[𝓝 ![0,(σ:ℂ),(σ:ℂ)]]
    nuclearOriginalAmbientFunction u i ε₁) ∧
  ∀ n : ℕ, iteratedFDeriv ℂ n (nuclearOriginalAmbientFunction u i ε₀) ![0,(σ:ℂ),(σ:ℂ)]=
    iteratedFDeriv ℂ n (nuclearOriginalAmbientFunction u i ε₁) ![0,(σ:ℂ),(σ:ℂ)]

theorem nuclear_ambient_two_scale_complex_jets
    {u : Configuration 2 → ℂ} {i : Fin 2} {ε₀ ε₁ δ₀ δ₁ B₀ B₁ σ : ℝ}
    (hε₀ : 0<ε₀) (hε₁ : 0<ε₁) (hδ₀ : 0<δ₀) (hδ₁ : 0<δ₁) (hσ : 0<σ)
    (hrec₀ : PhysicalNuclearAmbientReconstruction u i ε₀ δ₀ B₀)
    (hrec₁ : PhysicalNuclearAmbientReconstruction u i ε₁ δ₁ B₁)
    (hσ₀ : |σ-ε₀|<ε₀*δ₀) (hσ₁ : |σ-ε₁|<ε₁*δ₁) :
    NuclearAmbientDistanceCompatible u i ε₀ δ₀ ε₁ δ₁ σ := by
  obtain ⟨hfull,hgerm⟩ := nuclear_ambient_two_scale_compatibility
    hε₀ hε₁ hδ₀ hδ₁ hσ hrec₀ hrec₁ hσ₀ hσ₁
  exact ⟨hfull,hgerm,fun n => (hgerm.iteratedFDeriv ℂ n).eq_of_nhds⟩

theorem twoElectron_scalar_ground_nuclear_ambient_distance_compatibility
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
      (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
        PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
          (nuclearAmbientNormalizedBound M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H))) ∧
      ∀ ε₀ ε₁ : ℝ, 0<ε₀ → ε₀≤min 1 (R/4) → 0<ε₁ → ε₁≤min 1 (R/4) →
        ∀ i : Fin 2, ∀ σ : ℝ, 0<σ →
        |σ-ε₀|<ε₀*nuclearAmbientRetainedRadius M A →
        |σ-ε₁|<ε₁*nuclearAmbientRetainedRadius M A →
        NuclearAmbientDistanceCompatible u i ε₀ (nuclearAmbientRetainedRadius M A)
          ε₁ (nuclearAmbientRetainedRadius M A) σ := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hδ,hrec⟩ :=
    twoElectron_scalar_ground_nuclear_ambient_distance_reconstruction Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hδ,hrec,?_⟩
  intro ε₀ ε₁ hε₀ hlim₀ hε₁ hlim₁ i σ hσ hσ₀ hσ₁
  exact nuclear_ambient_two_scale_complex_jets hε₀ hε₁ hδ hδ hσ
    (hrec ε₀ hε₀ hlim₀ i) (hrec ε₁ hε₁ hlim₁ i) hσ₀ hσ₁

#print axioms nuclear_ambient_two_scale_complex_jets
#print axioms twoElectron_scalar_ground_nuclear_ambient_distance_compatibility
end ManyBody.S8