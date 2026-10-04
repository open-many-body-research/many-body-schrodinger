import ManyBody.S8.Internal.PhysicalNormalizationSymmetry
import ManyBody.S8.CoulombRadialCompactApproximation

/-! Actual norm-one radial compact physical H2 approximants and graph Rayleigh errors.
The prefactor is existential; its normalization threshold is explicit. The
cutoff representatives need not be smooth eigenfunctions or finite expansions. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalNormalizedRadialCompactState (R : ℝ) (hR : 0<R) (f : SpatialL2 2) : SpatialL2 2 :=
  physicalNormalizationScalar (physicalRadialCompactState R hR f) • physicalRadialCompactState R hR f

/-- The normalized literal compact representative, its true ordered weak H2
families, the combined H2 defect, and a genuine scalar Hamiltonian graph image
with an eigenvalue residual and a Rayleigh energy error. -/
def PhysicalNormalizedRadialCompactApproximationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z E a C R : ℝ) (hR : 1≤R) : Prop :=
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalRadialCompactState R hRp f
  let c := physicalNormalizationScalar F
  let v := physicalNormalizedRadialCompactState R hRp f
  let D := fun k => c • physicalRadialCompactFirst R hRp f (d k) k
  let A := fun k l => c • physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l
  1/2≤‖F‖ ∧ ‖v‖=1 ∧
  (v : Configuration 2 → ℂ) =ᵐ[volume] (fun x => c • (physicalRadialCompactCutoff R x • f x)) ∧
  HasCompactSupport (fun x => c • (physicalRadialCompactCutoff R x • f x)) ∧
  tsupport (fun x => c • (physicalRadialCompactCutoff R x • f x))⊆ball 0 (2*R) ∧
  (∀ k, WeakPartial v (D k) k) ∧ (∀ k l, WeakPartial (D k) (A k l) l) ∧
  (∀ k, WeakPartial (v-f) (D k-d k) k) ∧
  (∀ k l, WeakPartial (D k-d k) (A k l-e k l) l) ∧
  physicalH2ComponentNorm (v-f) (fun k => D k-d k) (fun k l => A k l-e k l)≤
    Real.exp (-a*R)*C ∧
  ∃ h : SpatialL2 2, scalarHamiltonianGraph 2 Z v h ∧
    ‖h-(E:ℂ) • v‖≤Real.exp (-a*R)*C ∧
    |(inner ℂ v h).re-E|≤Real.exp (-a*R)*C

theorem physical_radial_compact_residual_data_normalized {f : SpatialL2 2}
    {d : Coordinate 2 → SpatialL2 2} {e : Coordinate 2 → Coordinate 2 → SpatialL2 2}
    {Z E a C R : ℝ} {hR : 1≤R}
    (hf : ‖f‖=1) (hd : ∀ k, WeakPartial f (d k) k)
    (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (hC : 0≤C) (ha : 0<a)
    (hp : PhysicalRadialCompactHamiltonianResidualData f d e Z E a C R hR)
    (hlarge : physicalCompactNormalizationRadius a C≤R) :
    PhysicalNormalizedRadialCompactApproximationData f d e Z E a
      (16*(1+physicalH2ComponentNorm f d e)*C) R hR := by
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalRadialCompactState R hRp f
  let D := fun k => physicalRadialCompactFirst R hRp f (d k) k
  let A := fun k l => physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l
  let c := physicalNormalizationScalar F
  let T := physicalH2ComponentNorm f d e
  let δ := Real.exp (-a*R)*C
  have hT : 0≤T := Real.sqrt_nonneg _
  have hδ : 0≤δ := mul_nonneg (Real.exp_pos _).le hC
  have hhalf : δ≤1/2 := (physicalCompactNormalizationRadius_half ha hlarge).2
  rcases hp with ⟨⟨hrep,hcomp,hs,hD,hA,_,_,hb⟩,h,hh,hr⟩
  have hb' : physicalH2ComponentNorm (F-f) (fun k => D k-d k) (fun k l => A k l-e k l)≤δ := hb
  have hdist : ‖F-f‖≤δ := (physicalH2ComponentNorm_bounds (F-f)
    (fun k => D k-d k) (fun k l => A k l-e k l)).1.trans hb'
  obtain ⟨hlo,hc,hc1,hn⟩ := physical_normalization_scalar_bounds hf hdist hhalf
  have hnr : (c • F : SpatialL2 2) =ᵐ[volume]
      (fun x => c • (physicalRadialCompactCutoff R x • f x)) := by
    filter_upwards [Lp.coeFn_smul c F,hrep] with x hx hy
    change F x=physicalRadialCompactCutoff R x • f x at hy
    change (c • F : SpatialL2 2) x=c • F x at hx
    rw [hx,hy]
  have hnc : HasCompactSupport (fun x => c • (physicalRadialCompactCutoff R x • f x)) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hcomp ⊢
    exact hcomp.mono fun x hx => by
      change c • (physicalRadialCompactCutoff R x • f x)=0
      change physicalRadialCompactCutoff R x • f x=0 at hx
      rw [hx,smul_zero]
  have hns : tsupport (fun x => c • (physicalRadialCompactCutoff R x • f x))⊆ball 0 (2*R) :=
    (tsupport_smul_subset_right (fun _ => c) (fun x => physicalRadialCompactCutoff R x • f x)).trans hs
  have hnd (k : Coordinate 2) : WeakPartial (c • F) (c • D k) k := weakPartial_smul c (hD k)
  have hna (k l : Coordinate 2) : WeakPartial (c • D k) (c • A k l) l := weakPartial_smul c (hA k l)
  have hbound : 2≤16*(1+T) := by linarith
  have hH2 := physical_normalized_H2_defect_le D d A e hf hb' hhalf
  have hH2' : physicalH2ComponentNorm (c • F-f)
      (fun k => c • D k-d k) (fun k l => c • A k l-e k l)≤
      Real.exp (-a*R)*(16*(1+T)*C) := by
    calc _≤14*(1+T)*δ := hH2
         _≤16*(1+T)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ
         _=Real.exp (-a*R)*(16*(1+T)*C) := by dsimp [δ]; ring
  have hid : c • h-(E:ℂ) • (c • F)=c • (h-(E:ℂ) • F) := by
    rw [smul_sub,smul_comm c (E:ℂ) F]
  have hrn : ‖c • h-(E:ℂ) • (c • F)‖≤Real.exp (-a*R)*(16*(1+T)*C) := by
    calc _=‖c‖*‖h-(E:ℂ) • F‖ := by rw [hid,norm_smul]
         _≤2*δ := mul_le_mul hc hr (norm_nonneg _) (by norm_num)
         _≤(16*(1+T))*δ := mul_le_mul_of_nonneg_right hbound hδ
         _=Real.exp (-a*R)*(16*(1+T)*C) := by dsimp [δ]; ring
  exact ⟨hlo,hn,hnr,hnc,hns,hnd,hna,
    (fun k => weakPartial_sub_h1 (hnd k) (hd k)),
    (fun k l => weakPartial_sub_h1 (hna k l) (he k l)),hH2',
    c • h,scalar_graph_smul c hh,hrn,(normalized_physical_graph_rayleigh_error hn).trans hrn⟩

theorem physical_normalized_radial_compact_approximation_of_residual_family
    {f : SpatialL2 2} {d : Coordinate 2 → SpatialL2 2}
    {e : Coordinate 2 → Coordinate 2 → SpatialL2 2} {Z E a C0 : ℝ}
    (hf : ‖f‖=1) (hd : ∀ k, WeakPartial f (d k) k)
    (he : ∀ k l, WeakPartial (d k) (e k l) l) (ha : 0<a) (hC0 : 0≤C0)
    (hp : ∀ R : ℝ, ∀ hR : 1≤R, PhysicalRadialCompactHamiltonianResidualData f d e Z E a C0 R hR) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, physicalCompactNormalizationRadius a C≤R →
      ∃ hR : 1≤R, PhysicalNormalizedRadialCompactApproximationData f d e Z E a C R hR := by
  let C := 16*(1+physicalH2ComponentNorm f d e)*C0
  have hT : 0≤physicalH2ComponentNorm f d e := Real.sqrt_nonneg _
  have hC : 0≤C := by dsimp [C]; positivity
  have hC0C : C0≤C := by dsimp [C]; nlinarith
  refine ⟨C,hC,?_⟩
  intro R hlarge
  have hR : 1≤R := (physicalCompactNormalizationRadius_half ha hlarge).1
  have hbase : physicalCompactNormalizationRadius a C0≤R := by
    apply le_trans _ hlarge
    exact max_le_max le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hC0C (by norm_num)) ha.le)
  exact ⟨hR,physical_radial_compact_residual_data_normalized hf hd he hC0 ha (hp R hR) hbase⟩

theorem scalar_eigen_normalized_radial_compact_exponential_approximation
    {Z E a : ℝ} {f : SpatialL2 2} (hf : ‖f‖=1)
    (hg : scalarHamiltonianGraph 2 Z f ((E:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (ha : 0<a) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, physicalCompactNormalizationRadius a C≤R →
      ∃ hR : 1≤R, PhysicalNormalizedRadialCompactApproximationData f d e Z E a C R hR := by
  obtain ⟨C0,hC0,hp⟩ := scalar_eigen_radial_compact_Hamiltonian_exponential_residual hg d e hd he ha.le hw
  exact physical_normalized_radial_compact_approximation_of_residual_family hf hd he ha hC0 hp

theorem twoElectron_ground_normalized_radial_compact_exponential_approximation_of_graph
    (Z : ℝ) (hZ : 2≤Z) {f : SpatialL2 2} (hf : ‖f‖=1)
    (hg : scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {a : ℝ} (ha : 0<a) (hgap : a^2<Z^2/112) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, physicalCompactNormalizationRadius a C≤R →
      ∃ hR : 1≤R, PhysicalNormalizedRadialCompactApproximationData f d e Z
        (variationalGroundEnergy 2 Z).toReal a C R hR :=
  scalar_eigen_normalized_radial_compact_exponential_approximation hf hg d e hd he ha
    (twoElectron_ground_exponential_decay Z hZ hg ha.le hgap)

theorem twoElectron_physical_ground_with_normalized_radial_compact_exponential_approximation
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ f : SpatialL2 2, ‖f‖=1 ∧ pullback twoElectronSwap f=f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      (∀ᵐ x, (f x).im=0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0<a → a^2<Z^2/112 → ∃ C : ℝ, 0≤C ∧
          ∀ R : ℝ, physicalCompactNormalizationRadius a C≤R →
            ∃ hR : 1≤R, PhysicalNormalizedRadialCompactApproximationData f d e Z
              (variationalGroundEnergy 2 Z).toReal a C R hR := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,_⟩ := twoElectron_ground_real_symmetric_rotation_decay Z hZ
  have hgcopy := hg
  obtain ⟨d,e,hd,he,_⟩ := hgcopy
  exact ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,fun a ha hgap =>
    twoElectron_ground_normalized_radial_compact_exponential_approximation_of_graph Z hZ hf hg d e hd he ha hgap⟩

#print axioms physical_radial_compact_residual_data_normalized
#print axioms physical_normalized_radial_compact_approximation_of_residual_family
#print axioms scalar_eigen_normalized_radial_compact_exponential_approximation
#print axioms twoElectron_ground_normalized_radial_compact_exponential_approximation_of_graph
#print axioms twoElectron_physical_ground_with_normalized_radial_compact_exponential_approximation
def PhysicalNormalizedRadialSymmetricCompactApproximationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z E a C R : ℝ) (hR : 1≤R) : Prop :=
  let v := physicalNormalizedRadialCompactState R (lt_of_lt_of_le zero_lt_one hR) f
  PhysicalNormalizedRadialCompactApproximationData f d e Z E a C R hR ∧
  pullback twoElectronSwap v=v ∧ (∀ᵐ x, (v x).im=0) ∧
  (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q v=v)

theorem physical_normalized_radial_data_symmetric {f : SpatialL2 2}
    {d : Coordinate 2 → SpatialL2 2} {e : Coordinate 2 → Coordinate 2 → SpatialL2 2}
    {Z E a C R : ℝ} {hR : 1≤R}
    (hp : PhysicalNormalizedRadialCompactApproximationData f d e Z E a C R hR)
    (hs : pullback twoElectronSwap f=f) (hr : ∀ᵐ x, (f x).im=0)
    (hrot : ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) :
    PhysicalNormalizedRadialSymmetricCompactApproximationData f d e Z E a C R hR :=
  ⟨hp,physical_normalization_permutation twoElectronSwap
      (physicalRadialCompactState_permutation twoElectronSwap hs R _),
    physical_normalization_real (physicalRadialCompactState_real hr R _),
    fun Q => physical_normalization_rotation Q (physicalRadialCompactState_rotation Q (hrot Q) R _)⟩

theorem twoElectron_ground_normalized_radial_symmetric_compact_approximation_of_graph
    (Z : ℝ) (hZ : 2≤Z) {f : SpatialL2 2} (hf : ‖f‖=1)
    (hg : scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f))
    (hs : pullback twoElectronSwap f=f) (hr : ∀ᵐ x, (f x).im=0)
    (hrot : ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {a : ℝ} (ha : 0<a) (hgap : a^2<Z^2/112) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, physicalCompactNormalizationRadius a C≤R →
      ∃ hR : 1≤R, PhysicalNormalizedRadialSymmetricCompactApproximationData f d e Z
        (variationalGroundEnergy 2 Z).toReal a C R hR := by
  obtain ⟨C,hC,hp⟩ := twoElectron_ground_normalized_radial_compact_exponential_approximation_of_graph
    Z hZ hf hg d e hd he ha hgap
  refine ⟨C,hC,?_⟩
  intro R hlarge
  obtain ⟨hR,hdata⟩ := hp R hlarge
  exact ⟨hR,physical_normalized_radial_data_symmetric hdata hs hr hrot⟩

theorem twoElectron_physical_ground_with_normalized_radial_symmetric_compact_approximation
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ f : SpatialL2 2, ‖f‖=1 ∧ pullback twoElectronSwap f=f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      (∀ᵐ x, (f x).im=0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0<a → a^2<Z^2/112 → ∃ C : ℝ, 0≤C ∧
          ∀ R : ℝ, physicalCompactNormalizationRadius a C≤R →
            ∃ hR : 1≤R, PhysicalNormalizedRadialSymmetricCompactApproximationData f d e Z
              (variationalGroundEnergy 2 Z).toReal a C R hR := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,hp⟩ :=
    twoElectron_physical_ground_with_normalized_radial_compact_exponential_approximation Z hZ
  refine ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,?_⟩
  intro a ha hgap
  obtain ⟨C,hC,hdata⟩ := hp a ha hgap
  refine ⟨C,hC,?_⟩
  intro R hlarge
  obtain ⟨hR,hdatum⟩ := hdata R hlarge
  exact ⟨hR,physical_normalized_radial_data_symmetric hdatum hs hr hrot⟩

#print axioms physical_normalized_radial_data_symmetric
#print axioms twoElectron_ground_normalized_radial_symmetric_compact_approximation_of_graph
#print axioms twoElectron_physical_ground_with_normalized_radial_symmetric_compact_approximation
end ManyBody.S8
