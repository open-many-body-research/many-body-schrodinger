import ScalarCoulombForm_v1
import CoulombH1Continuity_v1
import HardyH1ScalarDensity_v2
import SpectralBottom_v2

/-! The actual scalar weak-H¹ form lower bounds equal the actual weak-H²
operator lower bounds. Compact smooth approximation is proved infrastructure,
not a new density hypothesis. No ground-state attainment is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology LinearPMap
namespace TheoremT.Continuum

theorem scalar_coulomb_product_sub {N : ℕ} {Z : ℝ} {f g v w : SpatialL2 N}
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x)
    (hw : w =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * g x) :
    (v - w : SpatialL2 N) =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ) * (f - g : SpatialL2 N) x := by
  filter_upwards [hv,hw,Lp.coeFn_sub v w,Lp.coeFn_sub f g] with x hvx hwx hx hfx
  simp only [Pi.sub_apply] at hx hfx
  rw [hx,hfx,hvx,hwx,mul_sub]

theorem scalar_coulomb_product_tendsto {N : ℕ} (Z : ℝ)
    (fn : ℕ → SpatialL2 N) (f : SpatialL2 N)
    (dn : ℕ → Coordinate N → SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (vn : ℕ → SpatialL2 N) (v : SpatialL2 N)
    (hdn : ∀ n k, WeakPartial (fn n) (dn n k) k)
    (hd : ∀ k, WeakPartial f (d k) k)
    (hvn : ∀ n, vn n =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ) * fn n x)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x)
    (hdt : ∀ k, Tendsto (fun n => dn n k) atTop (𝓝 (d k))) :
    Tendsto vn atTop (𝓝 v) := by
  have hD : Tendsto (fun n => ∑ k : Coordinate N, ‖dn n k - d k‖^2)
      atTop (𝓝 0) := by
    have hh := tendsto_finset_sum Finset.univ (fun k _ =>
      (((hdt k).sub_const (d k)).norm.pow 2))
    simpa using hh
  have hs : Tendsto (fun n =>
      (2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ))) *
        Real.sqrt (∑ k : Coordinate N, ‖dn n k - d k‖^2)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hD).const_mul
      (2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)))
  have hsub : Tendsto (fun n => vn n - v) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hs
    exact coulomb_product_norm_le Z (fn n - f) (fun k => dn n k - d k)
      (fun k => weakPartial_sub_h1 (hdn n k) (hd k)) (vn n - v)
      (scalar_coulomb_product_sub (hvn n) hv)
  simpa only [sub_add_cancel,zero_add] using hsub.add_const v

theorem scalarCoulombH1Energy_tendsto {N : ℕ} (Z : ℝ)
    (fn : ℕ → SpatialL2 N) (f : SpatialL2 N)
    (dn : ℕ → Coordinate N → SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (vn : ℕ → SpatialL2 N) (v : SpatialL2 N)
    (hdn : ∀ n k, WeakPartial (fn n) (dn n k) k)
    (hd : ∀ k, WeakPartial f (d k) k)
    (hvn : ∀ n, vn n =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ) * fn n x)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x)
    (hft : Tendsto fn atTop (𝓝 f))
    (hdt : ∀ k, Tendsto (fun n => dn n k) atTop (𝓝 (d k))) :
    Tendsto (fun n => scalarCoulombH1Energy (fn n) (dn n) (vn n))
      atTop (𝓝 (scalarCoulombH1Energy f d v)) := by
  have hD := tendsto_finset_sum Finset.univ (fun k _ => (hdt k).norm.pow 2)
  have hV := scalar_coulomb_product_tendsto Z fn f dn d vn v hdn hd hvn hv hdt
  unfold scalarCoulombH1Energy
  simp_rw [← spatialL2_real_inner_eq_re]
  exact (hD.const_mul (1 / 2 : ℝ)).add (hft.inner hV)

def scalarCoulombH1LowerBounds (N : ℕ) (Z : ℝ) : Set ℝ :=
  {a | ∀ f q, scalarCoulombH1FormValue N Z f q → a * ‖f‖^2 ≤ q}

theorem scalar_operatorLowerBound_on_graph {N : ℕ} {Z a : ℝ}
    (ha : a ∈ TheoremT.OperatorTheory.operatorLowerBounds (scalarCoulombOperator N Z))
    {f h : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f h) :
    a * ‖f‖^2 ≤ (inner ℂ f h).re := by
  have hdom : f ∈ (scalarCoulombOperator N Z).domain :=
    (scalarCoulombOperator_domain_iff N Z f).mpr ⟨h,hg⟩
  let x : (scalarCoulombOperator N Z).domain := ⟨f,hdom⟩
  have heq : scalarCoulombOperator N Z x = h :=
    scalar_graph_unique (scalarCoulombOperator_apply_graph N Z x) hg
  have hb := ha x
  change a * ‖f‖^2 ≤ (inner ℂ f (scalarCoulombOperator N Z x)).re at hb
  rwa [heq] at hb

theorem scalar_operatorLowerBound_on_h1Form {N : ℕ} {Z a : ℝ}
    (ha : a ∈ TheoremT.OperatorTheory.operatorLowerBounds (scalarCoulombOperator N Z)) :
    a ∈ scalarCoulombH1LowerBounds N Z := by
  rintro f q ⟨d,v,hd,hv,rfl⟩
  obtain ⟨u,fn,dn,hu,hc,hfu,hdfu,hdn,hH2,hft,hdt⟩ :=
    weakH1_smooth_compact_graph_sequence d hd
  have hvex (n : ℕ) := coulombProductL2_of_hasH1 Z (h2_implies_h1 (hH2 n))
  let vn : ℕ → SpatialL2 N := fun n => (hvex n).toLp _
  have hvn : ∀ n, vn n =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ) * fn n x := fun n => (hvex n).coeFn_toLp
  have hE := scalarCoulombH1Energy_tendsto Z fn f dn d vn v hdn hd hvn hv hft hdt
  have hn := (hft.norm.pow 2).const_mul a
  apply le_of_tendsto_of_tendsto' hn hE
  intro n
  obtain ⟨h,hg⟩ := scalar_graph_exists_of_coulombProductL2 (hH2 n) (hvex n)
  have hform : scalarCoulombH1FormValue N Z (fn n)
      (scalarCoulombH1Energy (fn n) (dn n) (vn n)) :=
    ⟨dn n,vn n,hdn n,hvn n,rfl⟩
  rw [scalarCoulombH1FormValue_eq_graph_energy hform hg]
  exact scalar_operatorLowerBound_on_graph ha hg

theorem scalarCoulombH1LowerBounds_eq_operatorLowerBounds (N : ℕ) (Z : ℝ) :
    scalarCoulombH1LowerBounds N Z =
      TheoremT.OperatorTheory.operatorLowerBounds (scalarCoulombOperator N Z) := by
  ext a
  constructor
  · intro ha x
    have hg := scalarCoulombOperator_apply_graph N Z x
    exact ha x.val (inner ℂ x.val (scalarCoulombOperator N Z x)).re
      (scalarHamiltonianGraph_formValue hg)
  · exact scalar_operatorLowerBound_on_h1Form

#print axioms scalar_coulomb_product_tendsto
#print axioms scalarCoulombH1Energy_tendsto
#print axioms scalar_operatorLowerBound_on_h1Form
#print axioms scalarCoulombH1LowerBounds_eq_operatorLowerBounds
end TheoremT.Continuum
