import ManyBody.S8.Internal.PhysicalHamiltonianResidualBounds

/-! Actual scalar Coulomb graph residuals of genuine compact physical H2
truncations. The ground state and all original weak derivatives are retained;
finite constants precede every real cutoff radius. No computable prefactor
or finite dictionary approximation is asserted. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem scalar_eigen_compact_residual_le_H2 {Z E : ℝ} {f h : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f ((E:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (R : ℝ) (hR : 0<R)
    (hh : scalarHamiltonianGraph 2 Z (physicalCompactState R hR f) h) :
    ‖h-(E:ℂ) • physicalCompactState R hR f‖≤
      (3+2*(2*|Z|+1)+|E|)*physicalCompactH2DefectNorm R hR f d e := by
  let F := physicalCompactState R hR f
  let D := fun k => physicalCompactFirst R hR f (d k) k
  let A := fun k l => physicalCompactSecond R hR f (d k) (d l) (e k l) k l
  have hfd (k : Coordinate 2) : WeakPartial (F-f) (D k-d k) k :=
    weakPartial_sub_h1 (physicalCompactFirst_weakPartial (hd k) R hR) (hd k)
  have hfe (k l : Coordinate 2) : WeakPartial (D k-d k) (A k l-e k l) l :=
    weakPartial_sub_h1 (physicalCompactSecond_weakPartial (k:=k) (hd l) (he k l) R hR) (he k l)
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
      (fun k l => A k l-e k l)=physicalCompactH2DefectNorm R hR f d e := rfl
  rw [hT] at hb hm
  nlinarith


def PhysicalCompactHamiltonianResidualData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z E a C R : ℝ) (hR : 1≤R) : Prop :=
  PhysicalCompactH2TruncationData f d e a C R hR ∧
  ∃ h : SpatialL2 2,
    scalarHamiltonianGraph 2 Z
      (physicalCompactState R (lt_of_lt_of_le zero_lt_one hR) f) h ∧
    ‖h-(E:ℂ) • physicalCompactState R (lt_of_lt_of_le zero_lt_one hR) f‖≤
      Real.exp (-a*R)*C

theorem physical_compact_H2_data_mono {f : SpatialL2 2}
    {d : Coordinate 2 → SpatialL2 2} {e : Coordinate 2 → Coordinate 2 → SpatialL2 2}
    {a C C' R : ℝ} {hR : 1≤R}
    (hp : PhysicalCompactH2TruncationData f d e a C R hR) (hC : C≤C') :
    PhysicalCompactH2TruncationData f d e a C' R hR := by
  rcases hp with ⟨ha,hc,hs,hd,he,hdf,hde,hb⟩
  exact ⟨ha,hc,hs,hd,he,hdf,hde,hb.trans
    (mul_le_mul_of_nonneg_left hC (Real.exp_pos _).le)⟩

theorem scalar_eigen_compact_Hamiltonian_exponential_residual
    {Z E a : ℝ} {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f ((E:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (ha : 0≤a) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, ∀ hR : 1≤R,
      PhysicalCompactHamiltonianResidualData f d e Z E a C R hR := by
  obtain ⟨C0,hC0,htr⟩ := scalar_eigen_compact_H2_exponential_truncation hg d e hd he ha hw
  let K := 3+2*(2*|Z|+1)+|E|
  have hK : 0≤K := by dsimp [K]; positivity
  have hCC : C0≤(1+K)*C0 := by nlinarith [mul_nonneg hK hC0]
  refine ⟨(1+K)*C0,mul_nonneg (by positivity) hC0,?_⟩
  intro R hR
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalCompactState R hRp f
  let D := fun k => physicalCompactFirst R hRp f (d k) k
  let A := fun k l => physicalCompactSecond R hRp f (d k) (d l) (e k l) k l
  have hfd (k : Coordinate 2) : WeakPartial F (D k) k :=
    physicalCompactFirst_weakPartial (hd k) R hRp
  have hfe (k l : Coordinate 2) : WeakPartial (D k) (A k l) l :=
    physicalCompactSecond_weakPartial (k:=k) (hd l) (he k l) R hRp
  have hH2 : HasH2 F := ⟨D,hfd,fun k l => ⟨A k l,hfe k l⟩⟩
  obtain ⟨h,hh⟩ := scalar_graph_exists_of_coulombProductL2 hH2 (coulombProductL2_of_hasH2 Z hH2)
  refine ⟨physical_compact_H2_data_mono (htr R hR) hCC,h,hh,?_⟩
  have hb := scalar_eigen_compact_residual_le_H2 hg d e hd he R hRp hh
  have ht : physicalCompactH2DefectNorm R hRp f d e≤Real.exp (-a*R)*C0 :=
    (htr R hR).2.2.2.2.2.2.2
  calc ‖h-(E:ℂ) • F‖≤K*physicalCompactH2DefectNorm R hRp f d e := hb
       _≤K*(Real.exp (-a*R)*C0) := mul_le_mul_of_nonneg_left ht hK
       _≤Real.exp (-a*R)*((1+K)*C0) := by nlinarith [Real.exp_pos (-a*R)]

theorem twoElectron_ground_compact_Hamiltonian_exponential_residual_of_graph
    (Z : ℝ) (hZ : 2≤Z) {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f
      (((variationalGroundEnergy 2 Z).toReal:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {a : ℝ} (ha : 0<a) (hgap : a^2<Z^2/112) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, ∀ hR : 1≤R,
      PhysicalCompactHamiltonianResidualData f d e Z
        (variationalGroundEnergy 2 Z).toReal a C R hR :=
  scalar_eigen_compact_Hamiltonian_exponential_residual hg d e hd he ha.le
    (twoElectron_ground_exponential_decay Z hZ hg ha.le hgap)

theorem twoElectron_physical_ground_with_compact_Hamiltonian_exponential_residual
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ f : SpatialL2 2, ‖f‖=1 ∧ pullback twoElectronSwap f=f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      (∀ᵐ x, (f x).im=0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0<a → a^2<Z^2/112 → ∃ C : ℝ, 0≤C ∧
          ∀ R : ℝ, ∀ hR : 1≤R,
            PhysicalCompactHamiltonianResidualData f d e Z
              (variationalGroundEnergy 2 Z).toReal a C R hR := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,_⟩ := twoElectron_ground_real_symmetric_rotation_decay Z hZ
  have hgcopy := hg
  obtain ⟨d,e,hd,he,_⟩ := hgcopy
  exact ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,fun a ha hgap =>
    twoElectron_ground_compact_Hamiltonian_exponential_residual_of_graph Z hZ hg d e hd he ha hgap⟩

#print axioms scalar_eigen_compact_residual_le_H2
#print axioms physical_compact_H2_data_mono
#print axioms scalar_eigen_compact_Hamiltonian_exponential_residual
#print axioms twoElectron_ground_compact_Hamiltonian_exponential_residual_of_graph
#print axioms twoElectron_physical_ground_with_compact_Hamiltonian_exponential_residual
end ManyBody.S8
