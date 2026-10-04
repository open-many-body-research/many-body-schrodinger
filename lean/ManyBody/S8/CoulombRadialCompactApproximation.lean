import ManyBody.S8.Internal.PhysicalRadialCompactH2Truncation
import ManyBody.S8.Internal.PhysicalHamiltonianResidualBounds
import ManyBody.S8.CoulombH2PolynomialMoments
import CoulombH1Continuity_v1

/-! Literal norm-radial cutoff: actual weak H2 derivatives, exponential defect,
true Coulomb residual, and preservation of actual ground reality, exchange and
simultaneous O(3) invariance. Constants precede all real radii. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum


/-- The literal cutoff representative, its actual weak derivative families,
and the combined H2 defect norm. Compact support is asserted for the supplied
AE representative rather than for an arbitrary chosen Lp representative. -/
def PhysicalRadialCompactH2TruncationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (a C R : ℝ) (hR : 1≤R) : Prop :=
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalRadialCompactState R hRp f
  let D := fun k => physicalRadialCompactFirst R hRp f (d k) k
  let E := fun k l => physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l
  (F : Configuration 2 → ℂ) =ᵐ[volume] (fun x => physicalRadialCompactCutoff R x • f x) ∧
  HasCompactSupport (fun x => physicalRadialCompactCutoff R x • f x) ∧
  tsupport (fun x => physicalRadialCompactCutoff R x • f x)⊆ball 0 (2*R) ∧
  (∀ k, WeakPartial F (D k) k) ∧ (∀ k l, WeakPartial (D k) (E k l) l) ∧
  (∀ k, WeakPartial (F-f) (D k-d k) k) ∧
  (∀ k l, WeakPartial (D k-d k) (E k l-e k l) l) ∧
  physicalRadialCompactH2DefectNorm R hRp f d e≤Real.exp (-a*R)*C

theorem physical_radial_compact_H2_truncation_of_tail
    (f : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (a Ctail : ℝ) (hCtail : 0≤Ctail)
    (htail : ∀ R : ℝ, weakH2ExteriorNorm f d e R≤Real.exp (-a*R)*Ctail) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, ∀ hR : 1≤R,
      PhysicalRadialCompactH2TruncationData f d e a C R hR := by
  obtain ⟨B1,B2,hB1,hB2,hbound⟩ := physicalRadialCompactCutoff_derivative_bounds
  let K := 7*(1+2*B1+B2)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨K*Ctail,mul_nonneg hK hCtail,?_⟩
  intro R hR
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hcompact : HasCompactSupport (fun x => physicalRadialCompactCutoff R x • f x) :=
    (physicalRadialCompactCutoff_hasCompactSupport hRp).smul_right
  have hsupport : tsupport (fun x => physicalRadialCompactCutoff R x • f x)⊆ball 0 (2*R) :=
    (tsupport_smul_subset_left (physicalRadialCompactCutoff R) (fun x => f x)).trans
      (physicalRadialCompactCutoff_tsupport_subset hRp)
  have hfirst (k : Coordinate 2) := physicalRadialCompactFirst_weakPartial (hd k) R hRp
  have hsecond (k l : Coordinate 2) := physicalRadialCompactSecond_weakPartial (k:=k) (hd l) (he k l) R hRp
  refine ⟨physicalRadialCompactState_ae R hRp f,hcompact,hsupport,hfirst,hsecond,
    (fun k => weakPartial_sub_h1 (hfirst k) (hd k)),
    (fun k l => weakPartial_sub_h1 (hsecond k l) (he k l)),?_⟩
  calc physicalRadialCompactH2DefectNorm R hRp f d e≤K*weakH2ExteriorNorm f d e R :=
      physicalRadialCompactH2DefectNorm_le B1 B2 hB1 hB2 hbound f d e R hR
       _≤K*(Real.exp (-a*R)*Ctail) := mul_le_mul_of_nonneg_left (htail R) hK
       _=Real.exp (-a*R)*(K*Ctail) := by ring

theorem scalar_eigen_radial_compact_H2_exponential_truncation
    {Z E a : ℝ} {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f ((E:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (ha : 0≤a) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, ∀ hR : 1≤R,
      PhysicalRadialCompactH2TruncationData f d e a C R hR := by
  obtain ⟨C,hC,htail⟩ := scalar_eigen_H2_exponential_tail hg d e hd he ha hw
  exact physical_radial_compact_H2_truncation_of_tail f d e hd he a C hC htail

theorem twoElectron_ground_radial_compact_H2_exponential_truncation_of_graph
    (Z : ℝ) (hZ : 2≤Z) {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f
      (((variationalGroundEnergy 2 Z).toReal:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {a : ℝ} (ha : 0<a) (hgap : a^2<Z^2/112) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, ∀ hR : 1≤R,
      PhysicalRadialCompactH2TruncationData f d e a C R hR :=
  scalar_eigen_radial_compact_H2_exponential_truncation hg d e hd he ha.le
    (twoElectron_ground_exponential_decay Z hZ hg ha.le hgap)

theorem twoElectron_physical_ground_with_radial_compact_H2_exponential_truncation
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ f : SpatialL2 2, ‖f‖=1 ∧ pullback twoElectronSwap f=f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      (∀ᵐ x, (f x).im=0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0<a → a^2<Z^2/112 → ∃ C : ℝ, 0≤C ∧
          ∀ R : ℝ, ∀ hR : 1≤R, PhysicalRadialCompactH2TruncationData f d e a C R hR := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,_⟩ := twoElectron_ground_real_symmetric_rotation_decay Z hZ
  have hgcopy := hg
  obtain ⟨d,e,hd,he,_⟩ := hgcopy
  exact ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,fun a ha hgap =>
    twoElectron_ground_radial_compact_H2_exponential_truncation_of_graph Z hZ hg d e hd he ha hgap⟩


theorem scalar_eigen_radial_compact_residual_le_H2 {Z E : ℝ} {f h : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f ((E:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (R : ℝ) (hR : 0<R)
    (hh : scalarHamiltonianGraph 2 Z (physicalRadialCompactState R hR f) h) :
    ‖h-(E:ℂ) • physicalRadialCompactState R hR f‖≤
      (3+2*(2*|Z|+1)+|E|)*physicalRadialCompactH2DefectNorm R hR f d e := by
  let F := physicalRadialCompactState R hR f
  let D := fun k => physicalRadialCompactFirst R hR f (d k) k
  let A := fun k l => physicalRadialCompactSecond R hR f (d k) (d l) (e k l) k l
  have hfd (k : Coordinate 2) : WeakPartial (F-f) (D k-d k) k :=
    weakPartial_sub_h1 (physicalRadialCompactFirst_weakPartial (hd k) R hR) (hd k)
  have hfe (k l : Coordinate 2) : WeakPartial (D k-d k) (A k l-e k l) l :=
    weakPartial_sub_h1 (physicalRadialCompactSecond_weakPartial (k:=k) (hd l) (he k l) R hR) (he k l)
  have hsub : scalarHamiltonianGraph 2 Z (F-f) (h-(E:ℂ) • f) := by
    simpa only [neg_one_smul,sub_eq_add_neg] using scalar_graph_add hh (scalar_graph_smul (-1:ℂ) hg)
  have hb := scalar_graph_norm_le_physicalH2 Z hsub (fun k => D k-d k)
    (fun k l => A k l-e k l) hfd hfe
  have h0 := (physicalH2ComponentNorm_bounds (F-f) (fun k => D k-d k)
    (fun k l => A k l-e k l)).1
  have hid : h-(E:ℂ) • F=(h-(E:ℂ) • f)-(E:ℂ) • (F-f) := by
    rw [smul_sub]; abel
  change ‖h-(E:ℂ) • F‖≤_
  rw [hid]
  have hn : ‖(E:ℂ)‖=|E| := by simp [Real.norm_eq_abs]
  have hs := norm_sub_le (h-(E:ℂ) • f) ((E:ℂ) • (F-f))
  rw [norm_smul,hn] at hs
  have hm := mul_le_mul_of_nonneg_left h0 (abs_nonneg E)
  have hT : physicalH2ComponentNorm (F-f) (fun k => D k-d k)
      (fun k l => A k l-e k l)=physicalRadialCompactH2DefectNorm R hR f d e := rfl
  rw [hT] at hb hm
  nlinarith


def PhysicalRadialCompactHamiltonianResidualData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z E a C R : ℝ) (hR : 1≤R) : Prop :=
  PhysicalRadialCompactH2TruncationData f d e a C R hR ∧
  ∃ h : SpatialL2 2,
    scalarHamiltonianGraph 2 Z
      (physicalRadialCompactState R (lt_of_lt_of_le zero_lt_one hR) f) h ∧
    ‖h-(E:ℂ) • physicalRadialCompactState R (lt_of_lt_of_le zero_lt_one hR) f‖≤
      Real.exp (-a*R)*C

theorem physical_radial_compact_H2_data_mono {f : SpatialL2 2}
    {d : Coordinate 2 → SpatialL2 2} {e : Coordinate 2 → Coordinate 2 → SpatialL2 2}
    {a C C' R : ℝ} {hR : 1≤R}
    (hp : PhysicalRadialCompactH2TruncationData f d e a C R hR) (hC : C≤C') :
    PhysicalRadialCompactH2TruncationData f d e a C' R hR := by
  rcases hp with ⟨ha,hc,hs,hd,he,hdf,hde,hb⟩
  exact ⟨ha,hc,hs,hd,he,hdf,hde,hb.trans
    (mul_le_mul_of_nonneg_left hC (Real.exp_pos _).le)⟩

theorem scalar_eigen_radial_compact_Hamiltonian_exponential_residual
    {Z E a : ℝ} {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f ((E:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (ha : 0≤a) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, ∀ hR : 1≤R,
      PhysicalRadialCompactHamiltonianResidualData f d e Z E a C R hR := by
  obtain ⟨C0,hC0,htr⟩ := scalar_eigen_radial_compact_H2_exponential_truncation hg d e hd he ha hw
  let K := 3+2*(2*|Z|+1)+|E|
  have hK : 0≤K := by dsimp [K]; positivity
  have hCC : C0≤(1+K)*C0 := by nlinarith [mul_nonneg hK hC0]
  refine ⟨(1+K)*C0,mul_nonneg (by positivity) hC0,?_⟩
  intro R hR
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalRadialCompactState R hRp f
  let D := fun k => physicalRadialCompactFirst R hRp f (d k) k
  let A := fun k l => physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l
  have hfd (k : Coordinate 2) : WeakPartial F (D k) k :=
    physicalRadialCompactFirst_weakPartial (hd k) R hRp
  have hfe (k l : Coordinate 2) : WeakPartial (D k) (A k l) l :=
    physicalRadialCompactSecond_weakPartial (k:=k) (hd l) (he k l) R hRp
  have hH2 : HasH2 F := ⟨D,hfd,fun k l => ⟨A k l,hfe k l⟩⟩
  obtain ⟨h,hh⟩ := scalar_graph_exists_of_coulombProductL2 hH2 (coulombProductL2_of_hasH2 Z hH2)
  refine ⟨physical_radial_compact_H2_data_mono (htr R hR) hCC,h,hh,?_⟩
  have hb := scalar_eigen_radial_compact_residual_le_H2 hg d e hd he R hRp hh
  have ht : physicalRadialCompactH2DefectNorm R hRp f d e≤Real.exp (-a*R)*C0 :=
    (htr R hR).2.2.2.2.2.2.2
  calc ‖h-(E:ℂ) • F‖≤K*physicalRadialCompactH2DefectNorm R hRp f d e := hb
       _≤K*(Real.exp (-a*R)*C0) := mul_le_mul_of_nonneg_left ht hK
       _≤Real.exp (-a*R)*((1+K)*C0) := by nlinarith [Real.exp_pos (-a*R)]

theorem twoElectron_ground_radial_compact_Hamiltonian_exponential_residual_of_graph
    (Z : ℝ) (hZ : 2≤Z) {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f
      (((variationalGroundEnergy 2 Z).toReal:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {a : ℝ} (ha : 0<a) (hgap : a^2<Z^2/112) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, ∀ hR : 1≤R,
      PhysicalRadialCompactHamiltonianResidualData f d e Z
        (variationalGroundEnergy 2 Z).toReal a C R hR :=
  scalar_eigen_radial_compact_Hamiltonian_exponential_residual hg d e hd he ha.le
    (twoElectron_ground_exponential_decay Z hZ hg ha.le hgap)

theorem twoElectron_physical_ground_with_radial_compact_Hamiltonian_exponential_residual
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ f : SpatialL2 2, ‖f‖=1 ∧ pullback twoElectronSwap f=f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      (∀ᵐ x, (f x).im=0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0<a → a^2<Z^2/112 → ∃ C : ℝ, 0≤C ∧
          ∀ R : ℝ, ∀ hR : 1≤R,
            PhysicalRadialCompactHamiltonianResidualData f d e Z
              (variationalGroundEnergy 2 Z).toReal a C R hR := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,_⟩ := twoElectron_ground_real_symmetric_rotation_decay Z hZ
  have hgcopy := hg
  obtain ⟨d,e,hd,he,_⟩ := hgcopy
  exact ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,fun a ha hgap =>
    twoElectron_ground_radial_compact_Hamiltonian_exponential_residual_of_graph Z hZ hg d e hd he ha hgap⟩


def PhysicalRadialSymmetricCompactApproximationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z E a C R : ℝ) (hR : 1≤R) : Prop :=
  let F := physicalRadialCompactState R (lt_of_lt_of_le zero_lt_one hR) f
  PhysicalRadialCompactHamiltonianResidualData f d e Z E a C R hR ∧
  pullback twoElectronSwap F=F ∧ (∀ᵐ x, (F x).im=0) ∧
  (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q F=F)

theorem physical_radial_compact_residual_data_symmetric {f : SpatialL2 2}
    {d : Coordinate 2 → SpatialL2 2} {e : Coordinate 2 → Coordinate 2 → SpatialL2 2}
    {Z E a C R : ℝ} {hR : 1≤R}
    (hp : PhysicalRadialCompactHamiltonianResidualData f d e Z E a C R hR)
    (hs : pullback twoElectronSwap f=f) (hr : ∀ᵐ x, (f x).im=0)
    (hrot : ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) :
    PhysicalRadialSymmetricCompactApproximationData f d e Z E a C R hR :=
  ⟨hp,physicalRadialCompactState_permutation twoElectronSwap hs R _,
    physicalRadialCompactState_real hr R _,fun Q => physicalRadialCompactState_rotation Q (hrot Q) R _⟩

theorem twoElectron_physical_ground_with_radial_symmetric_compact_approximation
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ f : SpatialL2 2, ‖f‖=1 ∧ pullback twoElectronSwap f=f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      (∀ᵐ x, (f x).im=0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0<a → a^2<Z^2/112 → ∃ C : ℝ, 0≤C ∧
          ∀ R : ℝ, ∀ hR : 1≤R,
            PhysicalRadialSymmetricCompactApproximationData f d e Z
              (variationalGroundEnergy 2 Z).toReal a C R hR := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,happ⟩ :=
    twoElectron_physical_ground_with_radial_compact_Hamiltonian_exponential_residual Z hZ
  refine ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,?_⟩
  intro a ha hgap
  obtain ⟨C,hC,hdata⟩ := happ a ha hgap
  exact ⟨C,hC,fun R hR => physical_radial_compact_residual_data_symmetric (hdata R hR) hs hr hrot⟩

#print axioms physical_radial_compact_H2_truncation_of_tail
#print axioms scalar_eigen_radial_compact_H2_exponential_truncation
#print axioms twoElectron_ground_radial_compact_H2_exponential_truncation_of_graph
#print axioms twoElectron_physical_ground_with_radial_compact_H2_exponential_truncation
#print axioms scalar_eigen_radial_compact_residual_le_H2
#print axioms physical_radial_compact_H2_data_mono
#print axioms scalar_eigen_radial_compact_Hamiltonian_exponential_residual
#print axioms twoElectron_ground_radial_compact_Hamiltonian_exponential_residual_of_graph
#print axioms twoElectron_physical_ground_with_radial_compact_Hamiltonian_exponential_residual
#print axioms physical_radial_compact_residual_data_symmetric
#print axioms twoElectron_physical_ground_with_radial_symmetric_compact_approximation
end ManyBody.S8
