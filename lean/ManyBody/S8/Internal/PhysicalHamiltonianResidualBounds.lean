import ManyBody.S8.CoulombCompactH2Truncation
import WeakCoulombNorm_v2

/-! The actual two-electron scalar Coulomb graph is bounded by the literal
state/first/ordered-second weak H2 component norm. This yields a genuine
Hamiltonian eigenvalue residual bound for physical compact truncations. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalH2ComponentNorm (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2) : ℝ :=
  Real.sqrt (‖f‖^2+(∑ k, ‖d k‖^2)+(∑ k, ∑ l, ‖e k l‖^2))

theorem physicalH2ComponentNorm_bounds (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2) :
    ‖f‖≤physicalH2ComponentNorm f d e ∧
    Real.sqrt (∑ k, ‖d k‖^2)≤physicalH2ComponentNorm f d e ∧
    ∀ k l, ‖e k l‖≤physicalH2ComponentNorm f d e := by
  have h1 : 0≤∑ k, ‖d k‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0≤∑ k, ∑ l, ‖e k l‖^2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  dsimp [physicalH2ComponentNorm]
  refine ⟨Real.le_sqrt_of_sq_le (by linarith),Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖f‖]),?_⟩
  intro k l
  have hl := Finset.single_le_sum (s:=Finset.univ) (fun l _ => sq_nonneg ‖e k l‖)
    (Finset.mem_univ l)
  have hk : (∑ l, ‖e k l‖^2)≤∑ k, ∑ l, ‖e k l‖^2 :=
    Finset.single_le_sum (s:=Finset.univ)
      (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg ‖e k l‖)) (Finset.mem_univ k)
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖f‖])

theorem scalar_graph_norm_le_physicalH2 (Z : ℝ) {f h : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f h)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l) :
    ‖h‖≤(3+2*(2*|Z|+1))*physicalH2ComponentNorm f d e := by
  have hv : MemLp (fun x => (coulombPotential 2 Z x:ℂ)*f x) 2 volume :=
    coulombProductL2_of_hasH1 Z ⟨d,hd⟩
  let v : SpatialL2 2 := hv.toLp (fun x => (coulombPotential 2 Z x:ℂ)*f x)
  let H : SpatialL2 2 := (-((1:ℂ)/2)) • (∑ k, e k k)+v
  have hH : scalarHamiltonianGraph 2 Z f H := by
    refine ⟨d,e,hd,he,?_⟩
    have hs : (∑ k, e k k : SpatialL2 2)=ᵐ[volume] (fun x => ∑ k, e k k x) :=
      Lp.coeFn_fun_finsetSum Finset.univ (fun k => e k k)
    filter_upwards [Lp.coeFn_add ((-((1:ℂ)/2)) • (∑ k,e k k)) v,
      Lp.coeFn_smul (-((1:ℂ)/2)) (∑ k,e k k),hs,hv.coeFn_toLp] with x hx hy hz hw
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hx hy
    change ((-((1:ℂ)/2)) • (∑ k,e k k)+v : SpatialL2 2) x=_
    rw [hx,hy,hz]
    change (-((1:ℂ)/2))*(∑ k,e k k x)+v x=_
    rw [hw]
  have hEq : h=H := scalar_graph_unique hg hH
  rw [hEq]
  have hc := physicalH2ComponentNorm_bounds f d e
  have hs : ‖∑ k, e k k‖≤6*physicalH2ComponentNorm f d e := by
    calc _≤∑ k, ‖e k k‖ := norm_sum_le _ _
         _≤∑ _k : Coordinate 2, physicalH2ComponentNorm f d e :=
           Finset.sum_le_sum (fun k _ => hc.2.2 k k)
         _=6*physicalH2ComponentNorm f d e := by simp [Coordinate]
  have hvb : ‖v‖≤2*(2*|Z|+1)*physicalH2ComponentNorm f d e := by
    have hb := coulomb_product_norm_le Z f d hd v hv.coeFn_toLp
    norm_num only [Nat.choose_self,Nat.cast_ofNat] at hb
    have hbc : 0≤2*(2*|Z|+1) := by positivity
    calc _≤2*(2*|Z|+1)*Real.sqrt (∑ k, ‖d k‖^2) := by nlinarith [hb]
         _≤2*(2*|Z|+1)*physicalH2ComponentNorm f d e :=
           mul_le_mul_of_nonneg_left hc.2.1 hbc
  have hm : ‖(-((1:ℂ)/2))‖=(1/2:ℝ) := by norm_num
  dsimp only [H]
  calc _≤‖(-((1:ℂ)/2)) • (∑ k,e k k)‖+‖v‖ := norm_add_le _ _
       _=(1/2:ℝ)*‖∑ k,e k k‖+‖v‖ := by rw [norm_smul,hm]
       _≤(1/2:ℝ)*(6*physicalH2ComponentNorm f d e)+
           2*(2*|Z|+1)*physicalH2ComponentNorm f d e :=
         add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num)) hvb
       _=(3+2*(2*|Z|+1))*physicalH2ComponentNorm f d e := by ring

#print axioms physicalH2ComponentNorm_bounds
#print axioms scalar_graph_norm_le_physicalH2
end ManyBody.S8
