import ManyBody.S8.Internal.PhysicalRadialGraphCore

/-! Norm-one symmetric smooth compact approximation of every actual normalized
scalar Coulomb graph pair at any real charge, with true H2, graph difference
and Rayleigh difference errors. No eigenvalue, decay or gap premise is added. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def PhysicalNormalizedRadialSmoothGraphApproximationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z : ℝ) (h : SpatialL2 2) (ε R : ℝ) (hR : 1≤R) (m : ℕ) : Prop :=
  let F := physicalRadialCompactState R (lt_of_lt_of_le zero_lt_one hR) f
  let D := fun k => physicalRadialCompactFirst R (lt_of_lt_of_le zero_lt_one hR) f (d k) k
  let A := fun k l => physicalRadialCompactSecond R (lt_of_lt_of_le zero_lt_one hR) f (d k) (d l) (e k l) k l
  let g := physicalRadialMollifyLp m F
  let c := physicalNormalizationScalar g
  let u := fun x => c • mollify (physicalRadialMollifierKernel m) F x
  let v := c • g
  let dv := fun k => c • physicalRadialMollifyLp m (D k)
  let ev := fun k l => c • physicalRadialMollifyLp m (A k l)
  1/2≤‖g‖ ∧ ‖v‖=1 ∧ ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
  tsupport u⊆closedBall 0 (2*R+2) ∧
  (v : Configuration 2 → ℂ)=ᵐ[volume] u ∧
  (∀ k, (dv k : Configuration 2 → ℂ)=ᵐ[volume] smoothPartial u k) ∧
  (∀ k l, (ev k l : Configuration 2 → ℂ)=ᵐ[volume] smoothPartial (smoothPartial u k) l) ∧
  (∀ k, WeakPartial v (dv k) k) ∧ (∀ k l, WeakPartial (dv k) (ev k l) l) ∧
  (∀ k, WeakPartial (v-f) (dv k-d k) k) ∧
  (∀ k l, WeakPartial (dv k-d k) (ev k l-e k l) l) ∧
  HasH2 v ∧ ‖v-f‖≤ε ∧
  physicalH2ComponentNorm (v-f) (fun k => dv k-d k) (fun k l => ev k l-e k l)≤ε ∧
  (∃ H : SpatialL2 2, scalarHamiltonianGraph 2 Z v H ∧ ‖H-h‖≤ε ∧
    |(inner ℂ v H).re-(inner ℂ f h).re|≤ε) ∧
  pullback twoElectronSwap v=v ∧ (∀ᵐ x, (v x).im=0) ∧
  (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q v=v) ∧
  (∀ x, u (permuteSpace twoElectronSwap x)=u x) ∧
  (∀ x, (u x).im=0) ∧
  (∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, u (configurationRotation 2 Q x)=u x)

theorem scalar_graph_normalized_radial_symmetric_smooth_approximation
    (Z : ℝ) {f h : SpatialL2 2} (hf : ‖f‖=1) (hg : scalarHamiltonianGraph 2 Z f h)
    (hs : pullback twoElectronSwap f=f) (hreal : ∀ᵐ x, (f x).im=0)
    (hrot : ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {ε : ℝ} (hε : 0<ε) :
    ∃ R : ℝ, ∃ hR : 1≤R, ∀ᶠ m : ℕ in atTop,
      PhysicalNormalizedRadialSmoothGraphApproximationData f d e Z h ε R hR m := by
  let H0 := physicalH2ComponentNorm f d e
  let K := 3+2*(2*|Z|+1)
  let δ := min (1/2) (ε/(16*(1+H0)*(1+K+‖h‖)))
  have hH0 : 0≤H0 := Real.sqrt_nonneg _
  have hK : 0≤K := by dsimp [K]; positivity
  have hden : 0<16*(1+H0)*(1+K+‖h‖) := by positivity
  have hδ : 0<δ := lt_min (by norm_num) (div_pos hε hden)
  have hhalf : δ≤1/2 := min_le_left _ _
  have hδε : δ*(16*(1+H0)*(1+K+‖h‖))≤ε := (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨R,hR,hraw⟩ := physical_radial_smooth_compact_H2_approximation f d e hd he hδ
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalRadialCompactState R hRp f
  let D := fun k => physicalRadialCompactFirst R hRp f (d k) k
  let A := fun k l => physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l
  refine ⟨R,hR,hraw.mono ?_⟩
  intro m hm
  rcases hm with ⟨hdata,hdef⟩
  let g := physicalRadialMollifyLp m F
  let dg := fun k => physicalRadialMollifyLp m (D k)
  let eg := fun k l => physicalRadialMollifyLp m (A k l)
  have hdist : ‖g-f‖≤δ := (physicalH2ComponentNorm_bounds (g-f)
    (fun k => dg k-d k) (fun k l => eg k l-e k l)).1.trans hdef
  obtain ⟨hlo,_,_,hn⟩ := physical_normalization_scalar_bounds hf hdist hhalf
  let c := physicalNormalizationScalar g
  let U := mollify (physicalRadialMollifierKernel m) F
  rcases hdata with ⟨hU,hUc,hUs,hgAE,hdAE,heAE,hdg,heg⟩
  have hnu : ContDiff ℝ ∞ (fun x => c • U x) := ContDiff.const_smul c hU
  have hnc : HasCompactSupport (fun x => c • U x) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hUc ⊢
    exact hUc.mono fun x hx => by change c • U x=0; change U x=0 at hx; rw [hx,smul_zero]
  have hns : tsupport (fun x => c • U x)⊆closedBall 0 (2*R+2) :=
    (tsupport_smul_subset_right (fun _ => c) U).trans hUs
  have hnvAE : (c • g : SpatialL2 2)=ᵐ[volume] (fun x => c • U x) := by
    filter_upwards [Lp.coeFn_smul c g,hgAE] with x hx hy
    change g x=U x at hy
    change (c • g : SpatialL2 2) x=c • g x at hx
    rw [hx,hy]
  have hndAE (k : Coordinate 2) : (c • dg k : SpatialL2 2)=ᵐ[volume]
      smoothPartial (fun x => c • U x) k := by
    rw [physical_smoothPartial_const_smul c hU k]
    filter_upwards [Lp.coeFn_smul c (dg k),hdAE k] with x hx hy
    change dg k x=smoothPartial U k x at hy
    change (c • dg k : SpatialL2 2) x=c • dg k x at hx
    rw [hx,hy]
  have hneAE (k l : Coordinate 2) : (c • eg k l : SpatialL2 2)=ᵐ[volume]
      smoothPartial (smoothPartial (fun x => c • U x) k) l := by
    rw [physical_smoothSecond_const_smul c hU k l]
    filter_upwards [Lp.coeFn_smul c (eg k l),heAE k l] with x hx hy
    change eg k l x=smoothPartial (smoothPartial U k) l x at hy
    change (c • eg k l : SpatialL2 2) x=c • eg k l x at hx
    rw [hx,hy]
  have hnd (k : Coordinate 2) : WeakPartial (c • g) (c • dg k) k := weakPartial_smul c (hdg k)
  have hne (k l : Coordinate 2) : WeakPartial (c • dg k) (c • eg k l) l := weakPartial_smul c (heg k l)
  let T := physicalH2ComponentNorm (c • g-f) (fun k => c • dg k-d k) (fun k l => c • eg k l-e k l)
  have hT : 0≤T := Real.sqrt_nonneg _
  have hTN : T≤14*(1+H0)*δ := physical_normalized_H2_defect_le dg d eg e hf hdef hhalf
  have htotal : (1+K+‖h‖)*T≤ε := by
    calc _≤(1+K+‖h‖)*(14*(1+H0)*δ) := mul_le_mul_of_nonneg_left hTN (by positivity)
         _≤(1+K+‖h‖)*(16*(1+H0)*δ) := mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_right (by linarith : 14*(1+H0)≤16*(1+H0)) hδ.le) (by positivity)
         _=δ*(16*(1+H0)*(1+K+‖h‖)) := by ring
         _≤ε := hδε
  have hTeps : T≤ε := by nlinarith [mul_nonneg hK hT,mul_nonneg (norm_nonneg h) hT]
  have hstate : ‖c • g-f‖≤T := (physicalH2ComponentNorm_bounds (c • g-f)
    (fun k => c • dg k-d k) (fun k l => c • eg k l-e k l)).1
  have hH2 : HasH2 (c • g) := ⟨(fun k => c • dg k),hnd,fun k l => ⟨c • eg k l,hne k l⟩⟩
  obtain ⟨H,hH⟩ := scalar_graph_exists_of_coulombProductL2 hH2 (coulombProductL2_of_hasH2 Z hH2)
  have hgraph : ‖H-h‖≤K*T := scalar_graph_difference_le_physicalH2 Z hg hH d (fun k => c • dg k)
    e (fun k l => c • eg k l) hd he hnd hne
  have hgraphε : ‖H-h‖≤ε := hgraph.trans (by nlinarith [mul_nonneg (norm_nonneg h) hT])
  have hRay : |(inner ℂ (c • g) H).re-(inner ℂ f h).re|≤ε := by
    calc _≤‖H-h‖+‖c • g-f‖*‖h‖ := normalized_physical_pair_rayleigh_difference hn
         _≤K*T+T*‖h‖ := add_le_add hgraph (mul_le_mul_of_nonneg_right hstate (norm_nonneg h))
         _≤(1+K+‖h‖)*T := by nlinarith
         _≤ε := htotal
  exact ⟨hlo,hn,hnu,hnc,hns,hnvAE,hndAE,hneAE,hnd,hne,
    (fun k => weakPartial_sub_h1 (hnd k) (hd k)),
    (fun k l => weakPartial_sub_h1 (hne k l) (he k l)),hH2,hstate.trans hTeps,hTeps,
    ⟨H,hH,hgraphε,hRay⟩,physical_radial_normalized_smooth_symmetries hs hreal hrot R hRp m⟩

theorem twoElectron_normalized_symmetric_scalar_graph_smooth_approximation
    (Z : ℝ) {f h : SpatialL2 2} (hg : scalarHamiltonianGraph 2 Z f h) (hf : ‖f‖=1)
    (hs : pullback twoElectronSwap f=f) (hreal : ∀ᵐ x, (f x).im=0)
    (hrot : ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) :
    ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
      (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
      ∀ ε : ℝ, 0<ε → ∃ R : ℝ, ∃ hR : 1≤R, ∀ᶠ m : ℕ in atTop,
        PhysicalNormalizedRadialSmoothGraphApproximationData f d e Z h ε R hR m := by
  have hcopy := hg
  obtain ⟨d,e,hd,he,_⟩ := hcopy
  exact ⟨d,e,hd,he,fun ε hε => scalar_graph_normalized_radial_symmetric_smooth_approximation
    Z hf hg hs hreal hrot d e hd he hε⟩

#print axioms scalar_graph_normalized_radial_symmetric_smooth_approximation
#print axioms twoElectron_normalized_symmetric_scalar_graph_smooth_approximation
end ManyBody.S8
