import ManyBody.S8.Internal.PhysicalCompactCutoff
import CoulombH2Decay_v1

/-! Actual product-rule first and all ordered second weak derivatives of compact
physical truncations, and their H2 defect controlled by the original component tail. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalCompactState (R : ℝ) (hR : 0<R) (f : SpatialL2 2) : SpatialL2 2 :=
  cutoffMul (physicalCompactCutoff R) (physicalCompactCutoff_contDiff R).continuous
    (physicalCompactCutoff_hasCompactSupport hR) f

def physicalCompactFirstError (R : ℝ) (hR : 0<R) (f : SpatialL2 2)
    (k : Coordinate 2) : SpatialL2 2 :=
  cutoffMul (physicalCompactCutoffPartial R k) (physicalCompactCutoffPartial_contDiff R k).continuous
    (physicalCompactCutoffPartial_hasCompactSupport hR k) f

def physicalCompactSecondError (R : ℝ) (hR : 0<R) (f : SpatialL2 2)
    (k l : Coordinate 2) : SpatialL2 2 :=
  cutoffMul (physicalCompactCutoffSecond R k l) (physicalCompactCutoffSecond_contDiff R k l).continuous
    (physicalCompactCutoffSecond_hasCompactSupport hR k l) f

def physicalCompactFirst (R : ℝ) (hR : 0<R) (f dk : SpatialL2 2)
    (k : Coordinate 2) : SpatialL2 2 :=
  physicalCompactState R hR dk+physicalCompactFirstError R hR f k

def physicalCompactSecond (R : ℝ) (hR : 0<R) (f dk dl e : SpatialL2 2)
    (k l : Coordinate 2) : SpatialL2 2 :=
  (physicalCompactState R hR e+physicalCompactFirstError R hR dk l)+
    (physicalCompactFirstError R hR dl k+physicalCompactSecondError R hR f k l)

theorem physicalCompactState_ae (R : ℝ) (hR : 0<R) (f : SpatialL2 2) :
    physicalCompactState R hR f =ᵐ[volume] (fun x => physicalCompactCutoff R x • f x) :=
  cutoffMul_ae _ _ _ _

theorem physicalCompactFirst_weakPartial {f dk : SpatialL2 2} {k : Coordinate 2}
    (hd : WeakPartial f dk k) (R : ℝ) (hR : 0<R) :
    WeakPartial (physicalCompactState R hR f) (physicalCompactFirst R hR f dk k) k :=
  weakPartial_cutoff hd _ (physicalCompactCutoff_contDiff R)
    (physicalCompactCutoff_hasCompactSupport hR)

theorem physicalCompactSecond_weakPartial {f dk dl e : SpatialL2 2} {k l : Coordinate 2}
    (hdl : WeakPartial f dl l) (he : WeakPartial dk e l) (R : ℝ) (hR : 0<R) :
    WeakPartial (physicalCompactFirst R hR f dk k)
      (physicalCompactSecond R hR f dk dl e k l) l :=
  weakPartial_add
    (weakPartial_cutoff he _ (physicalCompactCutoff_contDiff R)
      (physicalCompactCutoff_hasCompactSupport hR))
    (weakPartial_cutoff hdl _ (physicalCompactCutoffPartial_contDiff R k)
      (physicalCompactCutoffPartial_hasCompactSupport hR k))

theorem norm_cutoffMul_le_exterior (χ : Configuration 2 → ℝ)
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (f : SpatialL2 2)
    (R B : ℝ) (_hB : 0≤B) (hb : ∀ x, ‖χ x‖≤B)
    (hz : ∀ x, ‖x‖<R → χ x=0) :
    ‖cutoffMul χ hχ hcχ f‖≤B*‖exteriorL2 R f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [cutoffMul_ae χ hχ hcχ f,exteriorL2_ae R f] with x hx hy
  rw [hx,hy]
  by_cases hr : R≤‖x‖
  · rw [Set.indicator_of_mem (show x∈{x : Configuration 2 | R≤‖x‖} from hr),norm_smul]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  · rw [hz x (lt_of_not_ge hr),zero_smul,norm_zero,
      Set.indicator_of_notMem (show x∉{x : Configuration 2 | R≤‖x‖} from hr),norm_zero,mul_zero]

theorem physicalCompactState_defect_le (R : ℝ) (hR : 0<R) (f : SpatialL2 2) :
    ‖physicalCompactState R hR f-f‖≤‖exteriorL2 R f‖ := by
  have h : ‖physicalCompactState R hR f-f‖≤1*‖exteriorL2 R f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (physicalCompactState R hR f) f,
      physicalCompactState_ae R hR f,exteriorL2_ae R f] with x hx hy hz
    rw [hx]
    change ‖physicalCompactState R hR f x-f x‖≤_
    rw [hy,hz]
    by_cases hr : R≤‖x‖
    · rw [Set.indicator_of_mem (show x∈{x : Configuration 2 | R≤‖x‖} from hr)]
      have heq : physicalCompactCutoff R x • f x-f x=
          (physicalCompactCutoff R x-1) • f x := by simp only [sub_smul,one_smul]
      rw [heq,norm_smul,Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (physicalCompactCutoff_le_one R x))]
      have hc := physicalCompactCutoff_nonneg R x
      nlinarith [norm_nonneg (f x)]
    · rw [physicalCompactCutoff_eq_one hR (lt_of_not_ge hr).le,one_smul,sub_self,norm_zero]
      positivity
  simpa only [one_mul] using h

theorem physicalCompactFirstError_norm_bound (R : ℝ) (hR : 0<R)
    (f : SpatialL2 2) (k : Coordinate 2) (B : ℝ) (hB : 0≤B)
    (hb : ∀ x, ‖physicalCompactCutoffPartial R k x‖≤B) :
    ‖physicalCompactFirstError R hR f k‖≤B*‖exteriorL2 R f‖ :=
  norm_cutoffMul_le_exterior _ _ _ _ _ B hB hb
    (fun _x hx => physicalCompactCutoffPartial_zero_inner hR hx k)

theorem physicalCompactSecondError_norm_bound (R : ℝ) (hR : 0<R)
    (f : SpatialL2 2) (k l : Coordinate 2) (B : ℝ) (hB : 0≤B)
    (hb : ∀ x, ‖physicalCompactCutoffSecond R k l x‖≤B) :
    ‖physicalCompactSecondError R hR f k l‖≤B*‖exteriorL2 R f‖ :=
  norm_cutoffMul_le_exterior _ _ _ _ _ B hB hb
    (fun _x hx => physicalCompactCutoffSecond_zero_inner hR hx k l)

theorem weakH2ExteriorNorm_components_le (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2)
    (R : ℝ) :
    ‖exteriorL2 R f‖≤weakH2ExteriorNorm f d e R ∧
      (∀ k, ‖exteriorL2 R (d k)‖≤weakH2ExteriorNorm f d e R) ∧
      (∀ k l, ‖exteriorL2 R (e k l)‖≤weakH2ExteriorNorm f d e R) := by
  have h1 : 0≤∑ k, ‖exteriorL2 R (d k)‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0≤∑ k, ∑ l, ‖exteriorL2 R (e k l)‖^2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  dsimp [weakH2ExteriorNorm]
  refine ⟨Real.le_sqrt_of_sq_le (by linarith),?_,?_⟩
  · intro k
    have hk := Finset.single_le_sum (s:=Finset.univ) (fun k _ => sq_nonneg ‖exteriorL2 R (d k)‖)
      (Finset.mem_univ k)
    exact Real.le_sqrt_of_sq_le (by linarith [sq_nonneg ‖exteriorL2 R f‖])
  · intro k l
    have hl := Finset.single_le_sum (s:=Finset.univ) (fun l _ => sq_nonneg ‖exteriorL2 R (e k l)‖)
      (Finset.mem_univ l)
    have hk : (∑ l, ‖exteriorL2 R (e k l)‖^2)≤∑ k, ∑ l, ‖exteriorL2 R (e k l)‖^2 :=
      Finset.single_le_sum (s:=Finset.univ)
      (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg ‖exteriorL2 R (e k l)‖))
      (Finset.mem_univ k)
    exact Real.le_sqrt_of_sq_le (by linarith [sq_nonneg ‖exteriorL2 R f‖])

def physicalCompactH2DefectNorm (R : ℝ) (hR : 0<R) (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2) : ℝ :=
  Real.sqrt (‖physicalCompactState R hR f-f‖^2+
    (∑ k, ‖physicalCompactFirst R hR f (d k) k-d k‖^2)+
    (∑ k, ∑ l, ‖physicalCompactSecond R hR f (d k) (d l) (e k l) k l-e k l‖^2))

theorem physicalCompactH2DefectNorm_le (B1 B2 : ℝ) (hB1 : 0≤B1) (hB2 : 0≤B2)
    (hbound : ∀ R : ℝ, 0<R → ∀ x : Configuration 2,
      (∀ k, ‖physicalCompactCutoffPartial R k x‖≤B1/R) ∧
      (∀ k l, ‖physicalCompactCutoffSecond R k l x‖≤B2/R^2))
    (f : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (e : Coordinate 2 → Coordinate 2 → SpatialL2 2) (R : ℝ) (hR : 1≤R) :
    physicalCompactH2DefectNorm R (lt_of_lt_of_le zero_lt_one hR) f d e≤
      (7*(1+2*B1+B2))*weakH2ExteriorNorm f d e R := by
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hR2 : 1≤R^2 := by nlinarith
  have hb1 (x : Configuration 2) (k : Coordinate 2) :
      ‖physicalCompactCutoffPartial R k x‖≤B1 :=
    ((hbound R hRp x).1 k).trans (div_le_self hB1 hR)
  have hb2 (x : Configuration 2) (k l : Coordinate 2) :
      ‖physicalCompactCutoffSecond R k l x‖≤B2 :=
    ((hbound R hRp x).2 k l).trans (div_le_self hB2 hR2)
  let T := weakH2ExteriorNorm f d e R
  let c := 1+2*B1+B2
  have hT : 0≤T := Real.sqrt_nonneg _
  have hc : 1≤c := by dsimp [c]; linarith
  obtain ⟨hf,hd,he⟩ := weakH2ExteriorNorm_components_le f d e R
  have h0 : ‖physicalCompactState R hRp f-f‖≤c*T :=
    (physicalCompactState_defect_le R hRp f).trans (hf.trans (by nlinarith))
  have h1 (k : Coordinate 2) : ‖physicalCompactFirst R hRp f (d k) k-d k‖≤c*T := by
    have hid : physicalCompactFirst R hRp f (d k) k-d k=
        (physicalCompactState R hRp (d k)-d k)+physicalCompactFirstError R hRp f k := by
      dsimp [physicalCompactFirst]; abel
    rw [hid]
    have ha := physicalCompactState_defect_le R hRp (d k)
    have hb := physicalCompactFirstError_norm_bound R hRp f k B1 hB1 (fun x => hb1 x k)
    have ht := norm_add_le (physicalCompactState R hRp (d k)-d k)
      (physicalCompactFirstError R hRp f k)
    dsimp [c,T] at *
    nlinarith [hd k,mul_le_mul_of_nonneg_left hf hB1,mul_nonneg hB1 hT,mul_nonneg hB2 hT]
  have h2 (k l : Coordinate 2) :
      ‖physicalCompactSecond R hRp f (d k) (d l) (e k l) k l-e k l‖≤c*T := by
    have hid : physicalCompactSecond R hRp f (d k) (d l) (e k l) k l-e k l=
        ((physicalCompactState R hRp (e k l)-e k l)+physicalCompactFirstError R hRp (d k) l)+
        (physicalCompactFirstError R hRp (d l) k+physicalCompactSecondError R hRp f k l) := by
      dsimp [physicalCompactSecond]; abel
    rw [hid]
    have ha := physicalCompactState_defect_le R hRp (e k l)
    have hb := physicalCompactFirstError_norm_bound R hRp (d k) l B1 hB1 (fun x => hb1 x l)
    have hc1 := physicalCompactFirstError_norm_bound R hRp (d l) k B1 hB1 (fun x => hb1 x k)
    have hd1 := physicalCompactSecondError_norm_bound R hRp f k l B2 hB2 (fun x => hb2 x k l)
    have ht : ‖((physicalCompactState R hRp (e k l)-e k l)+physicalCompactFirstError R hRp (d k) l)+
        (physicalCompactFirstError R hRp (d l) k+physicalCompactSecondError R hRp f k l)‖≤
        (‖physicalCompactState R hRp (e k l)-e k l‖+‖physicalCompactFirstError R hRp (d k) l‖)+
        (‖physicalCompactFirstError R hRp (d l) k‖+‖physicalCompactSecondError R hRp f k l‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    dsimp [c,T] at *
    nlinarith [ht,he k l,mul_le_mul_of_nonneg_left (hd k) hB1,
      mul_le_mul_of_nonneg_left (hd l) hB1,mul_le_mul_of_nonneg_left hf hB2]
  have hs0 := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have hs1 := Finset.sum_le_sum (s:=Finset.univ)
    (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (h1 k) 2)
  have hs2 := Finset.sum_le_sum (s:=Finset.univ) (fun k _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun l _ => pow_le_pow_left₀ (norm_nonneg _) (h2 k l) 2))
  have hcard : Fintype.card (Coordinate 2)=6 := by simp [Coordinate]
  simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul] at hs1 hs2
  norm_num only [Nat.cast_ofNat] at hs1 hs2
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · change ‖physicalCompactState R hRp f-f‖^2+
      (∑ k, ‖physicalCompactFirst R hRp f (d k) k-d k‖^2)+
      (∑ k, ∑ l, ‖physicalCompactSecond R hRp f (d k) (d l) (e k l) k l-e k l‖^2)≤_
    change _≤(7*c*T)^2
    nlinarith [sq_nonneg (c*T)]

#print axioms physicalCompactFirst_weakPartial
#print axioms physicalCompactSecond_weakPartial
#print axioms physicalCompactH2DefectNorm_le
end ManyBody.S8