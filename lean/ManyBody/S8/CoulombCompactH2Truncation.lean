import ManyBody.S8.Internal.PhysicalCompactH2Truncation
import ManyBody.S8.CoulombH2PolynomialMoments
import CoulombH1Continuity_v1

/-! Exponentially accurate compact truncation of the actual physical H2 graph.
The cutoff is a single fixed smooth plateau scaled by R. All first and ordered
second derivatives of both the truncated state and the defect are genuine weak
L2 derivatives. Constants are existential, and no computable prefactor or
smoothness of the truncated eigenfunction is asserted. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

/-- The literal cutoff representative, its actual weak derivative families,
and the combined H2 defect norm. Compact support is asserted for the supplied
AE representative rather than for an arbitrary chosen Lp representative. -/
def PhysicalCompactH2TruncationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (a C R : ℝ) (hR : 1≤R) : Prop :=
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalCompactState R hRp f
  let D := fun k => physicalCompactFirst R hRp f (d k) k
  let E := fun k l => physicalCompactSecond R hRp f (d k) (d l) (e k l) k l
  (F : Configuration 2 → ℂ) =ᵐ[volume] (fun x => physicalCompactCutoff R x • f x) ∧
  HasCompactSupport (fun x => physicalCompactCutoff R x • f x) ∧
  tsupport (fun x => physicalCompactCutoff R x • f x)⊆ball 0 (2*R) ∧
  (∀ k, WeakPartial F (D k) k) ∧ (∀ k l, WeakPartial (D k) (E k l) l) ∧
  (∀ k, WeakPartial (F-f) (D k-d k) k) ∧
  (∀ k l, WeakPartial (D k-d k) (E k l-e k l) l) ∧
  physicalCompactH2DefectNorm R hRp f d e≤Real.exp (-a*R)*C

theorem physical_compact_H2_truncation_of_tail
    (f : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (a Ctail : ℝ) (hCtail : 0≤Ctail)
    (htail : ∀ R : ℝ, weakH2ExteriorNorm f d e R≤Real.exp (-a*R)*Ctail) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, ∀ hR : 1≤R,
      PhysicalCompactH2TruncationData f d e a C R hR := by
  obtain ⟨B1,B2,hB1,hB2,hbound⟩ := physicalCompactCutoff_derivative_bounds
  let K := 7*(1+2*B1+B2)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨K*Ctail,mul_nonneg hK hCtail,?_⟩
  intro R hR
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hcompact : HasCompactSupport (fun x => physicalCompactCutoff R x • f x) :=
    (physicalCompactCutoff_hasCompactSupport hRp).smul_right
  have hsupport : tsupport (fun x => physicalCompactCutoff R x • f x)⊆ball 0 (2*R) :=
    (tsupport_smul_subset_left (physicalCompactCutoff R) (fun x => f x)).trans
      (physicalCompactCutoff_tsupport_subset hRp)
  have hfirst (k : Coordinate 2) := physicalCompactFirst_weakPartial (hd k) R hRp
  have hsecond (k l : Coordinate 2) := physicalCompactSecond_weakPartial (k:=k) (hd l) (he k l) R hRp
  refine ⟨physicalCompactState_ae R hRp f,hcompact,hsupport,hfirst,hsecond,
    (fun k => weakPartial_sub_h1 (hfirst k) (hd k)),
    (fun k l => weakPartial_sub_h1 (hsecond k l) (he k l)),?_⟩
  calc physicalCompactH2DefectNorm R hRp f d e≤K*weakH2ExteriorNorm f d e R :=
      physicalCompactH2DefectNorm_le B1 B2 hB1 hB2 hbound f d e R hR
       _≤K*(Real.exp (-a*R)*Ctail) := mul_le_mul_of_nonneg_left (htail R) hK
       _=Real.exp (-a*R)*(K*Ctail) := by ring

theorem scalar_eigen_compact_H2_exponential_truncation
    {Z E a : ℝ} {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f ((E:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (ha : 0≤a) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, ∀ hR : 1≤R,
      PhysicalCompactH2TruncationData f d e a C R hR := by
  obtain ⟨C,hC,htail⟩ := scalar_eigen_H2_exponential_tail hg d e hd he ha hw
  exact physical_compact_H2_truncation_of_tail f d e hd he a C hC htail

theorem twoElectron_ground_compact_H2_exponential_truncation_of_graph
    (Z : ℝ) (hZ : 2≤Z) {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f
      (((variationalGroundEnergy 2 Z).toReal:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {a : ℝ} (ha : 0<a) (hgap : a^2<Z^2/112) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, ∀ hR : 1≤R,
      PhysicalCompactH2TruncationData f d e a C R hR :=
  scalar_eigen_compact_H2_exponential_truncation hg d e hd he ha.le
    (twoElectron_ground_exponential_decay Z hZ hg ha.le hgap)

theorem twoElectron_physical_ground_with_compact_H2_exponential_truncation
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ f : SpatialL2 2, ‖f‖=1 ∧ pullback twoElectronSwap f=f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      (∀ᵐ x, (f x).im=0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0<a → a^2<Z^2/112 → ∃ C : ℝ, 0≤C ∧
          ∀ R : ℝ, ∀ hR : 1≤R, PhysicalCompactH2TruncationData f d e a C R hR := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,_⟩ := twoElectron_ground_real_symmetric_rotation_decay Z hZ
  have hgcopy := hg
  obtain ⟨d,e,hd,he,_⟩ := hgcopy
  exact ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,fun a ha hgap =>
    twoElectron_ground_compact_H2_exponential_truncation_of_graph Z hZ hg d e hd he ha hgap⟩

#print axioms physical_compact_H2_truncation_of_tail
#print axioms scalar_eigen_compact_H2_exponential_truncation
#print axioms twoElectron_ground_compact_H2_exponential_truncation_of_graph
#print axioms twoElectron_physical_ground_with_compact_H2_exponential_truncation
end ManyBody.S8