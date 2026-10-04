import ManyBody.S8.Internal.PhysicalRadialMollification
import ManyBody.S8.CoulombNormalizedSmoothCompactApproximation

/-! Actual norm-one symmetric smooth compact physical H2 approximants from a
literal radial normalized approximate identity and explicit radial cutoffs.
The prefactor and sufficiently late index are existential; support, genuine
weak/classical derivatives, graph/residual/Rayleigh and symmetries are proved. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

/-- A literal normalized mollification of the actual compact physical H2 jet.
The weak families and their smooth derivative representatives are supplied,
as is a genuine scalar Coulomb graph image, residual and Rayleigh error. -/
def PhysicalNormalizedRadialSmoothCompactApproximationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z E ε R : ℝ) (hR : 1≤R) (m : ℕ) : Prop :=
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalRadialCompactState R hRp f
  let D := fun k => physicalRadialCompactFirst R hRp f (d k) k
  let A := fun k l => physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l
  let g := physicalRadialMollifyLp m F
  let c := physicalNormalizationScalar g
  let u := fun x => c • mollify (physicalRadialMollifierKernel m) F x
  let v := c • g
  let dv := fun k => c • physicalRadialMollifyLp m (D k)
  let ev := fun k l => c • physicalRadialMollifyLp m (A k l)
  1/2≤‖g‖ ∧ ‖v‖=1 ∧ ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
  tsupport u⊆closedBall 0 (2*R+2) ∧
  (v : Configuration 2 → ℂ) =ᵐ[volume] u ∧
  (∀ k, (dv k : Configuration 2 → ℂ) =ᵐ[volume] smoothPartial u k) ∧
  (∀ k l, (ev k l : Configuration 2 → ℂ) =ᵐ[volume] smoothPartial (smoothPartial u k) l) ∧
  (∀ k, WeakPartial v (dv k) k) ∧ (∀ k l, WeakPartial (dv k) (ev k l) l) ∧
  (∀ k, WeakPartial (v-f) (dv k-d k) k) ∧
  (∀ k l, WeakPartial (dv k-d k) (ev k l-e k l) l) ∧
  physicalH2ComponentNorm (v-f) (fun k => dv k-d k) (fun k l => ev k l-e k l)≤ε ∧
  ∃ h : SpatialL2 2, scalarHamiltonianGraph 2 Z v h ∧
    ‖h-(E:ℂ) • v‖≤ε ∧ |(inner ℂ v h).re-E|≤ε

theorem physical_normalized_radial_smooth_compact_approximation_of_residual_family
    {f : SpatialL2 2} {d : Coordinate 2 → SpatialL2 2}
    {e : Coordinate 2 → Coordinate 2 → SpatialL2 2} {Z E a C : ℝ}
    (hf : ‖f‖=1) (hg : scalarHamiltonianGraph 2 Z f ((E:ℂ) • f))
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (ha : 0<a)
    (hp : ∀ R : ℝ, ∀ hR : 1≤R, PhysicalRadialCompactHamiltonianResidualData f d e Z E a C R hR)
    {ε : ℝ} (hε : 0<ε) :
    let δ := physicalSmoothApproximationTolerance Z E (physicalH2ComponentNorm f d e) ε
    let R := physicalSmoothCutoffRadius a C (δ/14)
    ∃ hR : 1≤R, ∀ᶠ m : ℕ in atTop,
      PhysicalNormalizedRadialSmoothCompactApproximationData f d e Z E ε R hR m := by
  let H := physicalH2ComponentNorm f d e
  let K := 3+2*(2*|Z|+1)+|E|
  let δ := physicalSmoothApproximationTolerance Z E H ε
  let τ := δ/14
  let R := physicalSmoothCutoffRadius a C τ
  have hH : 0≤H := Real.sqrt_nonneg _
  have hK : 0≤K := by dsimp [K]; positivity
  have hden : 0<16*(1+H)*(1+K) := by positivity
  have hδ : 0<δ := lt_min (by norm_num) (div_pos hε hden)
  have hhalf : δ≤1/2 := min_le_left _ _
  have hδε : δ*(16*(1+H)*(1+K))≤ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hτ : 0<τ := by dsimp [τ]; positivity
  obtain ⟨hR,htail⟩ := physicalSmoothCutoffRadius_tail ha hτ (C:=C)
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalRadialCompactState R hRp f
  let D := fun k => physicalRadialCompactFirst R hRp f (d k) k
  let A := fun k l => physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l
  have hraw := hp R hR
  have hb : physicalH2ComponentNorm (F-f) (fun k => D k-d k) (fun k l => A k l-e k l)≤τ :=
    hraw.1.2.2.2.2.2.2.2.trans htail
  have hfd (k : Coordinate 2) : WeakPartial F (D k) k := hraw.1.2.2.2.1 k
  have hfe (k l : Coordinate 2) : WeakPartial (D k) (A k l) l := hraw.1.2.2.2.2.1 k l
  have hraw0 : ‖F-f‖≤τ := (physicalH2ComponentNorm_bounds (F-f)
    (fun k => D k-d k) (fun k l => A k l-e k l)).1.trans hb
  have hraw1 (k : Coordinate 2) : ‖D k-d k‖≤τ :=
    (physicalH2ComponentNorm_first_le (F-f) (fun k => D k-d k)
      (fun k l => A k l-e k l) k).trans hb
  have hraw2 (k l : Coordinate 2) : ‖A k l-e k l‖≤τ :=
    ((physicalH2ComponentNorm_bounds (F-f) (fun k => D k-d k)
      (fun k l => A k l-e k l)).2.2 k l).trans hb
  refine ⟨hR,?_⟩
  apply (physical_radial_H2_mollification_components_eventually F D A hτ).mono
  intro m hm
  let g := physicalRadialMollifyLp m F
  let dg := fun k => physicalRadialMollifyLp m (D k)
  let eg := fun k l => physicalRadialMollifyLp m (A k l)
  have h0 : ‖g-f‖≤2*τ := by
    have ht : ‖g-f‖≤‖g-F‖+‖F-f‖ := by simpa only [dist_eq_norm] using dist_triangle g F f
    linarith [hm.1]
  have h1 (k : Coordinate 2) : ‖dg k-d k‖≤2*τ := by
    have ht : ‖dg k-d k‖≤‖dg k-D k‖+‖D k-d k‖ := by
      simpa only [dist_eq_norm] using dist_triangle (dg k) (D k) (d k)
    linarith [hm.2.1 k,hraw1 k]
  have h2 (k l : Coordinate 2) : ‖eg k l-e k l‖≤2*τ := by
    have ht : ‖eg k l-e k l‖≤‖eg k l-A k l‖+‖A k l-e k l‖ := by
      simpa only [dist_eq_norm] using dist_triangle (eg k l) (A k l) (e k l)
    linarith [hm.2.2 k l,hraw2 k l]
  have hdef : physicalH2ComponentNorm (g-f) (fun k => dg k-d k) (fun k l => eg k l-e k l)≤δ := by
    have hb1 := physicalH2ComponentNorm_le_common (g-f) (fun k => dg k-d k)
      (fun k l => eg k l-e k l) (2*τ) (by positivity) h0 h1 h2
    dsimp [τ] at hb1
    nlinarith
  have hdist : ‖g-f‖≤δ := (physicalH2ComponentNorm_bounds (g-f)
    (fun k => dg k-d k) (fun k l => eg k l-e k l)).1.trans hdef
  obtain ⟨hlo,_,_,hn⟩ := physical_normalization_scalar_bounds hf hdist hhalf
  let c := physicalNormalizationScalar g
  let U := mollify (physicalRadialMollifierKernel m) F
  obtain ⟨hU,hUc,hUs,hgAE,hdAE,heAE,hdg,heg⟩ := physical_radial_smooth_mollification_data F D A
    hfd hfe (physicalRadialCompactState_ae_support f R hRp) m
  have hnu : ContDiff ℝ ∞ (fun x => c • U x) := ContDiff.const_smul c hU
  have hnc : HasCompactSupport (fun x => c • U x) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hUc ⊢
    exact hUc.mono fun x hx => by change c • U x=0; change U x=0 at hx; rw [hx,smul_zero]
  have hns : tsupport (fun x => c • U x)⊆closedBall 0 (2*R+2) :=
    (tsupport_smul_subset_right (fun _ => c) U).trans hUs
  have hnvAE : (c • g : SpatialL2 2) =ᵐ[volume] (fun x => c • U x) := by
    filter_upwards [Lp.coeFn_smul c g,hgAE] with x hx hy
    change g x=U x at hy
    change (c • g : SpatialL2 2) x=c • g x at hx
    rw [hx,hy]
  have hndAE (k : Coordinate 2) : (c • dg k : SpatialL2 2) =ᵐ[volume]
      smoothPartial (fun x => c • U x) k := by
    rw [physical_smoothPartial_const_smul c hU k]
    filter_upwards [Lp.coeFn_smul c (dg k),hdAE k] with x hx hy
    change dg k x=smoothPartial U k x at hy
    change (c • dg k : SpatialL2 2) x=c • dg k x at hx
    rw [hx,hy]
  have hneAE (k l : Coordinate 2) : (c • eg k l : SpatialL2 2) =ᵐ[volume]
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
  have hTN : T≤14*(1+H)*δ := physical_normalized_H2_defect_le dg d eg e hf hdef hhalf
  have htotal : (1+K)*T≤ε := by
    calc _≤(1+K)*(14*(1+H)*δ) := mul_le_mul_of_nonneg_left hTN (by positivity)
         _≤(1+K)*(16*(1+H)*δ) := mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_right (by linarith : 14*(1+H)≤16*(1+H)) hδ.le) (by positivity)
         _=δ*(16*(1+H)*(1+K)) := by ring
         _≤ε := hδε
  have hTeps : T≤ε := by nlinarith [mul_nonneg hK hT]
  have hH2 : HasH2 (c • g) := ⟨(fun k => c • dg k),hnd,fun k l => ⟨c • eg k l,hne k l⟩⟩
  obtain ⟨h,hh⟩ := scalar_graph_exists_of_coulombProductL2 hH2 (coulombProductL2_of_hasH2 Z hH2)
  have hr : ‖h-(E:ℂ) • (c • g)‖≤ε := by
    have hb1 := scalar_eigen_H2_graph_residual_le hg hh d (fun k => c • dg k)
      e (fun k l => c • eg k l) hd he hnd hne
    calc _≤K*T := hb1
         _≤(1+K)*T := by nlinarith
         _≤ε := htotal
  exact ⟨hlo,hn,hnu,hnc,hns,hnvAE,hndAE,hneAE,hnd,hne,
    (fun k => weakPartial_sub_h1 (hnd k) (hd k)),
    (fun k l => weakPartial_sub_h1 (hne k l) (he k l)),hTeps,
    h,hh,hr,(normalized_physical_graph_rayleigh_error hn).trans hr⟩

theorem scalar_eigen_normalized_radial_smooth_compact_exponential_approximation
    {Z E a : ℝ} {f : SpatialL2 2} (hf : ‖f‖=1)
    (hg : scalarHamiltonianGraph 2 Z f ((E:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (ha : 0<a) (hw : MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume) :
    ∃ C : ℝ, 0≤C ∧ ∀ ε : ℝ, 0<ε →
      let δ := physicalSmoothApproximationTolerance Z E (physicalH2ComponentNorm f d e) ε
      let R := physicalSmoothCutoffRadius a C (δ/14)
      ∃ hR : 1≤R, ∀ᶠ m : ℕ in atTop,
        PhysicalNormalizedRadialSmoothCompactApproximationData f d e Z E ε R hR m := by
  obtain ⟨C,hC,hp⟩ := scalar_eigen_radial_compact_Hamiltonian_exponential_residual hg d e hd he ha.le hw
  exact ⟨C,hC,fun ε hε =>
    physical_normalized_radial_smooth_compact_approximation_of_residual_family hf hg hd he ha hp hε⟩

theorem twoElectron_ground_normalized_radial_smooth_compact_exponential_approximation_of_graph
    (Z : ℝ) (hZ : 2≤Z) {f : SpatialL2 2} (hf : ‖f‖=1)
    (hg : scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f))
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {a : ℝ} (ha : 0<a) (hgap : a^2<Z^2/112) :
    ∃ C : ℝ, 0≤C ∧ ∀ ε : ℝ, 0<ε →
      let δ := physicalSmoothApproximationTolerance Z (variationalGroundEnergy 2 Z).toReal
        (physicalH2ComponentNorm f d e) ε
      let R := physicalSmoothCutoffRadius a C (δ/14)
      ∃ hR : 1≤R, ∀ᶠ m : ℕ in atTop,
        PhysicalNormalizedRadialSmoothCompactApproximationData f d e Z
          (variationalGroundEnergy 2 Z).toReal ε R hR m :=
  scalar_eigen_normalized_radial_smooth_compact_exponential_approximation hf hg d e hd he ha
    (twoElectron_ground_exponential_decay Z hZ hg ha.le hgap)

theorem twoElectron_physical_ground_with_normalized_radial_smooth_compact_exponential_approximation
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ f : SpatialL2 2, ‖f‖=1 ∧ pullback twoElectronSwap f=f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      (∀ᵐ x, (f x).im=0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0<a → a^2<Z^2/112 → ∃ C : ℝ, 0≤C ∧
          ∀ ε : ℝ, 0<ε →
            let δ := physicalSmoothApproximationTolerance Z (variationalGroundEnergy 2 Z).toReal
              (physicalH2ComponentNorm f d e) ε
            let R := physicalSmoothCutoffRadius a C (δ/14)
            ∃ hR : 1≤R, ∀ᶠ m : ℕ in atTop,
              PhysicalNormalizedRadialSmoothCompactApproximationData f d e Z
                (variationalGroundEnergy 2 Z).toReal ε R hR m := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,_⟩ := twoElectron_ground_real_symmetric_rotation_decay Z hZ
  have hgcopy := hg
  obtain ⟨d,e,hd,he,_⟩ := hgcopy
  exact ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,fun a ha hgap =>
    twoElectron_ground_normalized_radial_smooth_compact_exponential_approximation_of_graph Z hZ hf hg d e hd he ha hgap⟩

#print axioms physical_normalized_radial_smooth_compact_approximation_of_residual_family
#print axioms scalar_eigen_normalized_radial_smooth_compact_exponential_approximation
#print axioms twoElectron_ground_normalized_radial_smooth_compact_exponential_approximation_of_graph
#print axioms twoElectron_physical_ground_with_normalized_radial_smooth_compact_exponential_approximation

def PhysicalNormalizedRadialSymmetricSmoothApproximationData (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (Z E ε R : ℝ) (hR : 1≤R) (m : ℕ) : Prop :=
  let F := physicalRadialCompactState R (lt_of_lt_of_le zero_lt_one hR) f
  let g := physicalRadialMollifyLp m F
  let c := physicalNormalizationScalar g
  let v := c • g
  let u := fun x => c • mollify (physicalRadialMollifierKernel m) F x
  PhysicalNormalizedRadialSmoothCompactApproximationData f d e Z E ε R hR m ∧
  pullback twoElectronSwap v=v ∧ (∀ᵐ x, (v x).im=0) ∧
  (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q v=v) ∧
  (∀ x, u (permuteSpace twoElectronSwap x)=u x) ∧
  (∀ x, (u x).im=0) ∧
  (∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x, u (configurationRotation 2 Q x)=u x)

theorem physical_normalized_radial_smooth_data_symmetric {f : SpatialL2 2}
    {d : Coordinate 2 → SpatialL2 2} {e : Coordinate 2 → Coordinate 2 → SpatialL2 2}
    {Z E ε R : ℝ} {hR : 1≤R} {m : ℕ}
    (hp : PhysicalNormalizedRadialSmoothCompactApproximationData f d e Z E ε R hR m)
    (hs : pullback twoElectronSwap f=f) (hr : ∀ᵐ x, (f x).im=0)
    (hrot : ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) :
    PhysicalNormalizedRadialSymmetricSmoothApproximationData f d e Z E ε R hR m := by
  let hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let F := physicalRadialCompactState R hRp f
  let g := physicalRadialMollifyLp m F
  let c := physicalNormalizationScalar g
  have hFs : pullback twoElectronSwap F=F := physicalRadialCompactState_permutation twoElectronSwap hs R hRp
  have hFr : ∀ᵐ x, (F x).im=0 := physicalRadialCompactState_real hr R hRp
  have hFQ (Q : Position ≃ₗᵢ[ℝ] Position) : spatialRotation 2 Q F=F :=
    physicalRadialCompactState_rotation Q (hrot Q) R hRp
  refine ⟨hp,physical_normalization_permutation twoElectronSwap
      (physicalRadialMollifyLp_permutation m twoElectronSwap hFs),
    physical_normalization_real (physicalRadialMollifyLp_real m hFr),
    (fun Q => physical_normalization_rotation Q (physicalRadialMollifyLp_rotation m Q (hFQ Q))),?_,?_,?_⟩
  · intro x
    exact congrArg (fun z : ℂ => c • z)
      (physicalRadialMollify_isometry m (permuteSpace twoElectronSwap) hFs x)
  · intro x
    change (c • mollify (physicalRadialMollifierKernel m) F x).im=0
    have hreal := physicalRadialMollify_real m hFr x
    simp only [c,physicalNormalizationScalar,smul_eq_mul,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,hreal,mul_zero,zero_mul,add_zero]
  · intro Q x
    exact congrArg (fun z : ℂ => c • z)
      (physicalRadialMollify_isometry m (configurationRotation 2 Q) (hFQ Q) x)

theorem twoElectron_ground_normalized_radial_symmetric_smooth_approximation_of_graph
    (Z : ℝ) (hZ : 2≤Z) {f : SpatialL2 2} (hf : ‖f‖=1)
    (hg : scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f))
    (hs : pullback twoElectronSwap f=f) (hr : ∀ᵐ x, (f x).im=0)
    (hrot : ∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    {a : ℝ} (ha : 0<a) (hgap : a^2<Z^2/112) :
    ∃ C : ℝ, 0≤C ∧ ∀ ε : ℝ, 0<ε →
      let δ := physicalSmoothApproximationTolerance Z (variationalGroundEnergy 2 Z).toReal
        (physicalH2ComponentNorm f d e) ε
      let R := physicalSmoothCutoffRadius a C (δ/14)
      ∃ hR : 1≤R, ∀ᶠ m : ℕ in atTop,
        PhysicalNormalizedRadialSymmetricSmoothApproximationData f d e Z
          (variationalGroundEnergy 2 Z).toReal ε R hR m := by
  obtain ⟨C,hC,hp⟩ := twoElectron_ground_normalized_radial_smooth_compact_exponential_approximation_of_graph
    Z hZ hf hg d e hd he ha hgap
  refine ⟨C,hC,?_⟩
  intro ε hε
  obtain ⟨hR,hm⟩ := hp ε hε
  exact ⟨hR,hm.mono fun m hdata => physical_normalized_radial_smooth_data_symmetric hdata hs hr hrot⟩

theorem twoElectron_physical_ground_with_normalized_radial_symmetric_smooth_approximation
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ f : SpatialL2 2, ‖f‖=1 ∧ pullback twoElectronSwap f=f ∧ HasH2 f ∧
      scalarHamiltonianGraph 2 Z f (((variationalGroundEnergy 2 Z).toReal:ℂ) • f) ∧
      (∀ᵐ x, (f x).im=0) ∧
      (∀ Q : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 Q f=f) ∧
      ∃ d : Coordinate 2 → SpatialL2 2, ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
        (∀ k, WeakPartial f (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ a : ℝ, 0<a → a^2<Z^2/112 → ∃ C : ℝ, 0≤C ∧
          ∀ ε : ℝ, 0<ε →
            let δ := physicalSmoothApproximationTolerance Z (variationalGroundEnergy 2 Z).toReal
              (physicalH2ComponentNorm f d e) ε
            let R := physicalSmoothCutoffRadius a C (δ/14)
            ∃ hR : 1≤R, ∀ᶠ m : ℕ in atTop,
              PhysicalNormalizedRadialSymmetricSmoothApproximationData f d e Z
                (variationalGroundEnergy 2 Z).toReal ε R hR m := by
  obtain ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,hp⟩ :=
    twoElectron_physical_ground_with_normalized_radial_smooth_compact_exponential_approximation Z hZ
  refine ⟨f,hf,hs,hH2,hg,hr,hrot,d,e,hd,he,?_⟩
  intro a ha hgap
  obtain ⟨C,hC,hdata⟩ := hp a ha hgap
  refine ⟨C,hC,?_⟩
  intro ε hε
  obtain ⟨hR,hm⟩ := hdata ε hε
  exact ⟨hR,hm.mono fun m hdatum => physical_normalized_radial_smooth_data_symmetric hdatum hs hr hrot⟩

#print axioms physical_normalized_radial_smooth_data_symmetric
#print axioms twoElectron_ground_normalized_radial_symmetric_smooth_approximation_of_graph
#print axioms twoElectron_physical_ground_with_normalized_radial_symmetric_smooth_approximation
end ManyBody.S8
