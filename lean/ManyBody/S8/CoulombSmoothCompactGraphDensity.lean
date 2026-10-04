import ManyBody.S8.Internal.PhysicalH2GraphCore

/-! Smooth compact approximation of the actual scalar Coulomb graph for every
physical domain state, without an eigenvalue, charge-range or decay premise. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def PhysicalSmoothCompactH2GraphApproximationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z : ℝ) (h : SpatialL2 2) (ε : ℝ) (g : SpatialL2 2)
    (dg : Coordinate 2 → SpatialL2 2) (eg : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (u : Configuration 2 → ℂ) (H : SpatialL2 2) : Prop :=
  ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
  (g : Configuration 2 → ℂ)=ᵐ[volume] u ∧
  (∀ k, (dg k : Configuration 2 → ℂ)=ᵐ[volume] smoothPartial u k) ∧
  (∀ k l, (eg k l : Configuration 2 → ℂ)=ᵐ[volume] smoothPartial (smoothPartial u k) l) ∧
  (∀ k, WeakPartial g (dg k) k) ∧ (∀ k l, WeakPartial (dg k) (eg k l) l) ∧
  (∀ k, WeakPartial (g-f) (dg k-d k) k) ∧
  (∀ k l, WeakPartial (dg k-d k) (eg k l-e k l) l) ∧
  physicalH2ComponentNorm (g-f) (fun k => dg k-d k) (fun k l => eg k l-e k l)≤ε ∧
  HasH2 g ∧ scalarHamiltonianGraph 2 Z g H ∧ ‖H-h‖≤ε

theorem scalar_graph_difference_le_physicalH2 (Z : ℝ) {f h g H : SpatialL2 2}
    (hf : scalarHamiltonianGraph 2 Z f h) (hg : scalarHamiltonianGraph 2 Z g H)
    (d dg : Coordinate 2 → SpatialL2 2)
    (e eg : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (hdg : ∀ k, WeakPartial g (dg k) k) (heg : ∀ k l, WeakPartial (dg k) (eg k l) l) :
    ‖H-h‖≤(3+2*(2*|Z|+1))*
      physicalH2ComponentNorm (g-f) (fun k => dg k-d k) (fun k l => eg k l-e k l) := by
  have hsub : scalarHamiltonianGraph 2 Z (g-f) (H-h) := by
    simpa only [neg_one_smul,sub_eq_add_neg] using scalar_graph_add hg (scalar_graph_smul (-1:ℂ) hf)
  exact scalar_graph_norm_le_physicalH2 Z hsub (fun k => dg k-d k)
    (fun k l => eg k l-e k l) (fun k => weakPartial_sub_h1 (hdg k) (hd k))
    (fun k l => weakPartial_sub_h1 (heg k l) (he k l))

theorem scalar_Coulomb_smooth_compact_H2_graph_approximation (Z : ℝ) {f h : SpatialL2 2}
    (hf : scalarHamiltonianGraph 2 Z f h)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {ε : ℝ} (hε : 0<ε) :
    ∃ g : SpatialL2 2, ∃ dg : Coordinate 2 → SpatialL2 2,
    ∃ eg : Coordinate 2 → Coordinate 2 → SpatialL2 2,
    ∃ u : Configuration 2 → ℂ, ∃ H : SpatialL2 2,
      PhysicalSmoothCompactH2GraphApproximationData f d e Z h ε g dg eg u H := by
  let K := 3+2*(2*|Z|+1)
  have hK : 0≤K := by dsimp [K]; positivity
  let δ := ε/(1+K)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hid : δ*(1+K)=ε := by dsimp [δ]; field_simp
  have hδle : δ≤ε := by nlinarith [mul_nonneg hδ.le hK]
  have hKδ : K*δ≤ε := by nlinarith
  obtain ⟨R,hR,happ⟩ := physical_smooth_compact_H2_approximation f d e hd he hδ
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalCompactState R hRp f
  let D := fun k => physicalCompactFirst R hRp f (d k) k
  let A := fun k l => physicalCompactSecond R hRp f (d k) (d l) (e k l) k l
  obtain ⟨m,hdata,herror⟩ := happ.exists
  let g := mollifyLp m F
  let dg := fun k => mollifyLp m (D k)
  let eg := fun k l => mollifyLp m (A k l)
  let u := mollify (mollifierKernel 2 m) F
  rcases hdata with ⟨hu,hcompact,_,hae,hdae,heae,hdg,heg⟩
  have hH2 : HasH2 g := ⟨dg,hdg,fun k l => ⟨eg k l,heg k l⟩⟩
  obtain ⟨H,hH⟩ := scalar_graph_exists_of_coulombProductL2 hH2 (coulombProductL2_of_hasH2 Z hH2)
  have hb := scalar_graph_difference_le_physicalH2 Z hf hH d dg e eg hd he hdg heg
  refine ⟨g,dg,eg,u,H,hu,hcompact,hae,hdae,heae,hdg,heg,
    (fun k => weakPartial_sub_h1 (hdg k) (hd k)),
    (fun k l => weakPartial_sub_h1 (heg k l) (he k l)),herror.trans hδle,hH2,hH,?_⟩
  exact hb.trans ((mul_le_mul_of_nonneg_left herror hK).trans hKδ)

theorem twoElectron_scalar_Coulomb_smooth_compact_graph_density (Z : ℝ) {f h : SpatialL2 2}
    (hf : scalarHamiltonianGraph 2 Z f h) :
    ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
      (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
      ∀ ε : ℝ, 0<ε → ∃ g : SpatialL2 2, ∃ dg : Coordinate 2 → SpatialL2 2,
        ∃ eg : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        ∃ u : Configuration 2 → ℂ, ∃ H : SpatialL2 2,
          PhysicalSmoothCompactH2GraphApproximationData f d e Z h ε g dg eg u H := by
  have hcopy := hf
  obtain ⟨d,e,hd,he,_⟩ := hcopy
  exact ⟨d,e,hd,he,fun ε hε => scalar_Coulomb_smooth_compact_H2_graph_approximation Z hf d e hd he hε⟩

#print axioms scalar_graph_difference_le_physicalH2
#print axioms scalar_Coulomb_smooth_compact_H2_graph_approximation
#print axioms twoElectron_scalar_Coulomb_smooth_compact_graph_density
end ManyBody.S8
