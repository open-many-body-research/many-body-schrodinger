import ManyBody.S8.Internal.PhysicalRadialCompactCutoff
import ManyBody.S8.Internal.PhysicalCompactH2Truncation
import CoulombRotation_v1
import CoulombH2Decay_v1

/-! Actual product-rule first and all ordered second weak derivatives of compact
physical truncations, and their H2 defect controlled by the original component tail. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalRadialCompactState (R : ℝ) (hR : 0<R) (f : SpatialL2 2) : SpatialL2 2 :=
  cutoffMul (physicalRadialCompactCutoff R) (physicalRadialCompactCutoff_contDiff R).continuous
    (physicalRadialCompactCutoff_hasCompactSupport hR) f

def physicalRadialCompactFirstError (R : ℝ) (hR : 0<R) (f : SpatialL2 2)
    (k : Coordinate 2) : SpatialL2 2 :=
  cutoffMul (physicalRadialCompactCutoffPartial R k) (physicalRadialCompactCutoffPartial_contDiff R k).continuous
    (physicalRadialCompactCutoffPartial_hasCompactSupport hR k) f

def physicalRadialCompactSecondError (R : ℝ) (hR : 0<R) (f : SpatialL2 2)
    (k l : Coordinate 2) : SpatialL2 2 :=
  cutoffMul (physicalRadialCompactCutoffSecond R k l) (physicalRadialCompactCutoffSecond_contDiff R k l).continuous
    (physicalRadialCompactCutoffSecond_hasCompactSupport hR k l) f

def physicalRadialCompactFirst (R : ℝ) (hR : 0<R) (f dk : SpatialL2 2)
    (k : Coordinate 2) : SpatialL2 2 :=
  physicalRadialCompactState R hR dk+physicalRadialCompactFirstError R hR f k

def physicalRadialCompactSecond (R : ℝ) (hR : 0<R) (f dk dl e : SpatialL2 2)
    (k l : Coordinate 2) : SpatialL2 2 :=
  (physicalRadialCompactState R hR e+physicalRadialCompactFirstError R hR dk l)+
    (physicalRadialCompactFirstError R hR dl k+physicalRadialCompactSecondError R hR f k l)

theorem physicalRadialCompactState_ae (R : ℝ) (hR : 0<R) (f : SpatialL2 2) :
    physicalRadialCompactState R hR f =ᵐ[volume] (fun x => physicalRadialCompactCutoff R x • f x) :=
  cutoffMul_ae _ _ _ _

theorem physicalRadialCompactFirst_weakPartial {f dk : SpatialL2 2} {k : Coordinate 2}
    (hd : WeakPartial f dk k) (R : ℝ) (hR : 0<R) :
    WeakPartial (physicalRadialCompactState R hR f) (physicalRadialCompactFirst R hR f dk k) k :=
  weakPartial_cutoff hd _ (physicalRadialCompactCutoff_contDiff R)
    (physicalRadialCompactCutoff_hasCompactSupport hR)

theorem physicalRadialCompactSecond_weakPartial {f dk dl e : SpatialL2 2} {k l : Coordinate 2}
    (hdl : WeakPartial f dl l) (he : WeakPartial dk e l) (R : ℝ) (hR : 0<R) :
    WeakPartial (physicalRadialCompactFirst R hR f dk k)
      (physicalRadialCompactSecond R hR f dk dl e k l) l :=
  weakPartial_add
    (weakPartial_cutoff he _ (physicalRadialCompactCutoff_contDiff R)
      (physicalRadialCompactCutoff_hasCompactSupport hR))
    (weakPartial_cutoff hdl _ (physicalRadialCompactCutoffPartial_contDiff R k)
      (physicalRadialCompactCutoffPartial_hasCompactSupport hR k))

theorem physicalRadialCompactState_defect_le (R : ℝ) (hR : 0<R) (f : SpatialL2 2) :
    ‖physicalRadialCompactState R hR f-f‖≤‖exteriorL2 R f‖ := by
  have h : ‖physicalRadialCompactState R hR f-f‖≤1*‖exteriorL2 R f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (physicalRadialCompactState R hR f) f,
      physicalRadialCompactState_ae R hR f,exteriorL2_ae R f] with x hx hy hz
    rw [hx]
    change ‖physicalRadialCompactState R hR f x-f x‖≤_
    rw [hy,hz]
    by_cases hr : R≤‖x‖
    · rw [Set.indicator_of_mem (show x∈{x : Configuration 2 | R≤‖x‖} from hr)]
      have heq : physicalRadialCompactCutoff R x • f x-f x=
          (physicalRadialCompactCutoff R x-1) • f x := by simp only [sub_smul,one_smul]
      rw [heq,norm_smul,Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (physicalRadialCompactCutoff_le_one R x))]
      have hc := physicalRadialCompactCutoff_nonneg R x
      nlinarith [norm_nonneg (f x)]
    · rw [physicalRadialCompactCutoff_eq_one hR (lt_of_not_ge hr).le,one_smul,sub_self,norm_zero]
      positivity
  simpa only [one_mul] using h

theorem physicalRadialCompactFirstError_norm_bound (R : ℝ) (hR : 0<R)
    (f : SpatialL2 2) (k : Coordinate 2) (B : ℝ) (hB : 0≤B)
    (hb : ∀ x, ‖physicalRadialCompactCutoffPartial R k x‖≤B) :
    ‖physicalRadialCompactFirstError R hR f k‖≤B*‖exteriorL2 R f‖ :=
  norm_cutoffMul_le_exterior _ _ _ _ _ B hB hb
    (fun _x hx => physicalRadialCompactCutoffPartial_zero_inner hR hx k)

theorem physicalRadialCompactSecondError_norm_bound (R : ℝ) (hR : 0<R)
    (f : SpatialL2 2) (k l : Coordinate 2) (B : ℝ) (hB : 0≤B)
    (hb : ∀ x, ‖physicalRadialCompactCutoffSecond R k l x‖≤B) :
    ‖physicalRadialCompactSecondError R hR f k l‖≤B*‖exteriorL2 R f‖ :=
  norm_cutoffMul_le_exterior _ _ _ _ _ B hB hb
    (fun _x hx => physicalRadialCompactCutoffSecond_zero_inner hR hx k l)

def physicalRadialCompactH2DefectNorm (R : ℝ) (hR : 0<R) (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (e : Coordinate 2 → Coordinate 2 → SpatialL2 2) : ℝ :=
  Real.sqrt (‖physicalRadialCompactState R hR f-f‖^2+
    (∑ k, ‖physicalRadialCompactFirst R hR f (d k) k-d k‖^2)+
    (∑ k, ∑ l, ‖physicalRadialCompactSecond R hR f (d k) (d l) (e k l) k l-e k l‖^2))

theorem physicalRadialCompactH2DefectNorm_le (B1 B2 : ℝ) (hB1 : 0≤B1) (hB2 : 0≤B2)
    (hbound : ∀ R : ℝ, 0<R → ∀ x : Configuration 2,
      (∀ k, ‖physicalRadialCompactCutoffPartial R k x‖≤B1/R) ∧
      (∀ k l, ‖physicalRadialCompactCutoffSecond R k l x‖≤B2/R^2))
    (f : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (e : Coordinate 2 → Coordinate 2 → SpatialL2 2) (R : ℝ) (hR : 1≤R) :
    physicalRadialCompactH2DefectNorm R (lt_of_lt_of_le zero_lt_one hR) f d e≤
      (7*(1+2*B1+B2))*weakH2ExteriorNorm f d e R := by
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hR2 : 1≤R^2 := by nlinarith
  have hb1 (x : Configuration 2) (k : Coordinate 2) :
      ‖physicalRadialCompactCutoffPartial R k x‖≤B1 :=
    ((hbound R hRp x).1 k).trans (div_le_self hB1 hR)
  have hb2 (x : Configuration 2) (k l : Coordinate 2) :
      ‖physicalRadialCompactCutoffSecond R k l x‖≤B2 :=
    ((hbound R hRp x).2 k l).trans (div_le_self hB2 hR2)
  let T := weakH2ExteriorNorm f d e R
  let c := 1+2*B1+B2
  have hT : 0≤T := Real.sqrt_nonneg _
  have hc : 1≤c := by dsimp [c]; linarith
  obtain ⟨hf,hd,he⟩ := weakH2ExteriorNorm_components_le f d e R
  have h0 : ‖physicalRadialCompactState R hRp f-f‖≤c*T :=
    (physicalRadialCompactState_defect_le R hRp f).trans (hf.trans (by nlinarith))
  have h1 (k : Coordinate 2) : ‖physicalRadialCompactFirst R hRp f (d k) k-d k‖≤c*T := by
    have hid : physicalRadialCompactFirst R hRp f (d k) k-d k=
        (physicalRadialCompactState R hRp (d k)-d k)+physicalRadialCompactFirstError R hRp f k := by
      dsimp [physicalRadialCompactFirst]; abel
    rw [hid]
    have ha := physicalRadialCompactState_defect_le R hRp (d k)
    have hb := physicalRadialCompactFirstError_norm_bound R hRp f k B1 hB1 (fun x => hb1 x k)
    have ht := norm_add_le (physicalRadialCompactState R hRp (d k)-d k)
      (physicalRadialCompactFirstError R hRp f k)
    dsimp [c,T] at *
    nlinarith [hd k,mul_le_mul_of_nonneg_left hf hB1,mul_nonneg hB1 hT,mul_nonneg hB2 hT]
  have h2 (k l : Coordinate 2) :
      ‖physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l-e k l‖≤c*T := by
    have hid : physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l-e k l=
        ((physicalRadialCompactState R hRp (e k l)-e k l)+physicalRadialCompactFirstError R hRp (d k) l)+
        (physicalRadialCompactFirstError R hRp (d l) k+physicalRadialCompactSecondError R hRp f k l) := by
      dsimp [physicalRadialCompactSecond]; abel
    rw [hid]
    have ha := physicalRadialCompactState_defect_le R hRp (e k l)
    have hb := physicalRadialCompactFirstError_norm_bound R hRp (d k) l B1 hB1 (fun x => hb1 x l)
    have hc1 := physicalRadialCompactFirstError_norm_bound R hRp (d l) k B1 hB1 (fun x => hb1 x k)
    have hd1 := physicalRadialCompactSecondError_norm_bound R hRp f k l B2 hB2 (fun x => hb2 x k l)
    have ht : ‖((physicalRadialCompactState R hRp (e k l)-e k l)+physicalRadialCompactFirstError R hRp (d k) l)+
        (physicalRadialCompactFirstError R hRp (d l) k+physicalRadialCompactSecondError R hRp f k l)‖≤
        (‖physicalRadialCompactState R hRp (e k l)-e k l‖+‖physicalRadialCompactFirstError R hRp (d k) l‖)+
        (‖physicalRadialCompactFirstError R hRp (d l) k‖+‖physicalRadialCompactSecondError R hRp f k l‖) :=
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
  · change ‖physicalRadialCompactState R hRp f-f‖^2+
      (∑ k, ‖physicalRadialCompactFirst R hRp f (d k) k-d k‖^2)+
      (∑ k, ∑ l, ‖physicalRadialCompactSecond R hRp f (d k) (d l) (e k l) k l-e k l‖^2)≤_
    change _≤(7*c*T)^2
    nlinarith [sq_nonneg (c*T)]

theorem physicalRadialCompactState_isometry (R : ℝ) (hR : 0<R)
    (Q : Configuration 2 ≃ₗᵢ[ℝ] Configuration 2) (f : SpatialL2 2) :
    configurationIsometryPull Q (physicalRadialCompactState R hR f)=
      physicalRadialCompactState R hR (configurationIsometryPull Q f) := by
  apply Lp.ext
  have hc := Q.measurePreserving.quasiMeasurePreserving.ae
    (physicalRadialCompactState_ae R hR f)
  filter_upwards [configurationIsometryPull_ae Q (physicalRadialCompactState R hR f),
    hc,physicalRadialCompactState_ae R hR (configurationIsometryPull Q f),
    configurationIsometryPull_ae Q f] with x hQ hcomp hcut hsrc
  simp only [Function.comp_apply] at *
  rw [hQ,hcomp,hcut,hsrc,physicalRadialCompactCutoff_isometry]

theorem physicalRadialCompactState_permutation {f : SpatialL2 2}
    (π : Equiv.Perm (Fin 2)) (hf : pullback π f=f) (R : ℝ) (hR : 0<R) :
    pullback π (physicalRadialCompactState R hR f)=physicalRadialCompactState R hR f := by
  have h := physicalRadialCompactState_isometry R hR (permuteSpace π) f
  change pullback π (physicalRadialCompactState R hR f)=
    physicalRadialCompactState R hR (pullback π f) at h
  simpa only [hf] using h

theorem physicalRadialCompactState_rotation {f : SpatialL2 2}
    (Q : Position ≃ₗᵢ[ℝ] Position) (hf : spatialRotation 2 Q f=f) (R : ℝ) (hR : 0<R) :
    spatialRotation 2 Q (physicalRadialCompactState R hR f)=physicalRadialCompactState R hR f := by
  simpa only [hf] using physicalRadialCompactState_isometry R hR (configurationRotation 2 Q) f

theorem physicalRadialCompactState_real {f : SpatialL2 2}
    (hf : ∀ᵐ x, (f x).im=0) (R : ℝ) (hR : 0<R) :
    ∀ᵐ x, (physicalRadialCompactState R hR f x).im=0 := by
  filter_upwards [physicalRadialCompactState_ae R hR f,hf] with x hx hr
  rw [hx]
  change Complex.imCLM (physicalRadialCompactCutoff R x • f x)=0
  change Complex.imCLM (f x)=0 at hr
  rw [map_smul,hr,smul_zero]

#print axioms physicalRadialCompactFirst_weakPartial
#print axioms physicalRadialCompactSecond_weakPartial
#print axioms physicalRadialCompactH2DefectNorm_le
#print axioms physicalRadialCompactState_isometry
#print axioms physicalRadialCompactState_permutation
#print axioms physicalRadialCompactState_rotation
#print axioms physicalRadialCompactState_real
end ManyBody.S8
