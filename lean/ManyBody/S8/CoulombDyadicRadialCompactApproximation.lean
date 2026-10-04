import ManyBody.S8.Internal.DyadicPhysicalCutoffRadius

/-! A literal radius linear in requested dyadic precision controls normalized
radial compact physical H2, scalar Hamiltonian residual and Rayleigh errors. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def PhysicalNormalizedRadialDyadicApproximationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z E a C : ℝ) (p : ℕ) (R : ℝ) (hR : 1≤R) : Prop :=
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalRadialCompactState R hRp f
  let c := physicalNormalizationScalar F
  let v := physicalNormalizedRadialCompactState R hRp f
  let D := fun k => c • physicalRadialCompactFirst R hRp f (d k) k
  let A := fun k l => c • physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l
  PhysicalNormalizedRadialSymmetricCompactApproximationData f d e Z E a C R hR ∧
  ‖v-f‖≤(1/2:ℝ)^p ∧
  physicalH2ComponentNorm (v-f) (fun k => D k-d k) (fun k l => A k l-e k l)≤(1/2:ℝ)^p ∧
  ∃ H : SpatialL2 2, scalarHamiltonianGraph 2 Z v H ∧
    ‖H-(E:ℂ) • v‖≤(1/2:ℝ)^p ∧ |(inner ℂ v H).re-E|≤(1/2:ℝ)^p

theorem physical_normalized_radial_dyadic_data
    {f : SpatialL2 2} {d : Coordinate 2 → SpatialL2 2}
    {e : Coordinate 2 → Coordinate 2 → SpatialL2 2} {Z E a C R : ℝ}
    {p : ℕ} {hR : 1≤R}
    (hdata : PhysicalNormalizedRadialSymmetricCompactApproximationData f d e Z E a C R hR)
    (hb : Real.exp (-a*R)*C≤(1/2:ℝ)^p) :
    PhysicalNormalizedRadialDyadicApproximationData f d e Z E a C p R hR := by
  have hcopy := hdata.1
  dsimp only [PhysicalNormalizedRadialCompactApproximationData] at hcopy
  rcases hcopy with ⟨_,_,_,_,_,_,_,_,_,hH2,H,hH,hr,hRay⟩
  refine ⟨hdata,?_,hH2.trans hb,H,hH,hr.trans hb,hRay.trans hb⟩
  exact (physicalH2ComponentNorm_bounds _ _ _).1.trans (hH2.trans hb)

theorem twoElectron_ground_dyadic_radial_compact_approximation_of_graph
    (Z : ℝ) (hZ : 2≤Z) {f : SpatialL2 2} (hf : ‖f‖=1)
    (hg : scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f))
    (hs : pullback twoElectronSwap f=f) (hr : ∀ᵐ x, (f x).im=0)
    (hrot : ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {a : ℝ} (ha : 0<a) (hgap : a^2<Z^2/112) :
    ∃ C : ℝ, 0≤C ∧ ∀ p : ℕ,
      ∃ hR : 1≤physicalDyadicCutoffRadius a C (physicalCompactNormalizationRadius a C) p,
        PhysicalNormalizedRadialDyadicApproximationData f d e Z
          (variationalGroundEnergy 2 Z).toReal a C p
          (physicalDyadicCutoffRadius a C (physicalCompactNormalizationRadius a C) p) hR := by
  obtain ⟨C,hC,hp⟩ := twoElectron_ground_normalized_radial_symmetric_compact_approximation_of_graph
    Z hZ hf hg hs hr hrot d e hd he ha hgap
  refine ⟨C,hC,?_⟩
  intro p
  have hbudget := physical_dyadic_cutoff_radius_budget (Rmin:=physicalCompactNormalizationRadius a C) ha hC p
  obtain ⟨hR,hdata⟩ := hp _ hbudget.1
  exact ⟨hR,physical_normalized_radial_dyadic_data hdata hbudget.2⟩

theorem twoElectron_physical_ground_dyadic_radial_symmetric_compact_approximation
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ f : SpatialL2 2, ‖f‖=1 ∧ pullback twoElectronSwap f=f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      (∀ᵐ x, (f x).im=0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0<a → a^2<Z^2/112 → ∃ C : ℝ, 0≤C ∧ ∀ p : ℕ,
          ∃ hR : 1≤physicalDyadicCutoffRadius a C (physicalCompactNormalizationRadius a C) p,
            PhysicalNormalizedRadialDyadicApproximationData f d e Z
              (variationalGroundEnergy 2 Z).toReal a C p
              (physicalDyadicCutoffRadius a C (physicalCompactNormalizationRadius a C) p) hR := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,hp⟩ :=
    twoElectron_physical_ground_with_normalized_radial_symmetric_compact_approximation Z hZ
  refine ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,?_⟩
  intro a ha hgap
  obtain ⟨C,hC,hdata⟩ := hp a ha hgap
  refine ⟨C,hC,?_⟩
  intro p
  have hbudget := physical_dyadic_cutoff_radius_budget (Rmin:=physicalCompactNormalizationRadius a C) ha hC p
  obtain ⟨hR,hdatum⟩ := hdata _ hbudget.1
  exact ⟨hR,physical_normalized_radial_dyadic_data hdatum hbudget.2⟩

#print axioms physical_normalized_radial_dyadic_data
#print axioms twoElectron_ground_dyadic_radial_compact_approximation_of_graph
#print axioms twoElectron_physical_ground_dyadic_radial_symmetric_compact_approximation
end ManyBody.S8
