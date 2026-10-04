import ManyBody.S8.Internal.PhysicalCompactCutoff
import ConfigurationRotation_v1
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! An explicitly norm-radial compact cutoff. Unlike a generically chosen
ContDiffBump base, this literal function has proved invariance under every
physical configuration linear isometry, before state or radius choices. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalRadialCompactCutoffBase (x : Configuration 2) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace (Configuration 2)).toFun (3/2) x

theorem physicalRadialCompactCutoffBase_contDiff :
    ContDiff ℝ ∞ physicalRadialCompactCutoffBase := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let B := ContDiffBumpBase.ofInnerProductSpace (Configuration 2)
  have hmem : ((3/2:ℝ),x)∈Ioi (1:ℝ)×ˢ(univ : Set (Configuration 2)) :=
    ⟨by norm_num,mem_univ x⟩
  have hb := (B.smooth ((3/2:ℝ),x) hmem).contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
  have hc : ContDiffAt ℝ ∞ (fun y : Configuration 2 => ((3/2:ℝ),y)) x := by fun_prop
  exact hb.comp x hc

theorem physicalRadialCompactCutoffBase_eq_zero {x : Configuration 2}
    (hx : (3/2:ℝ)≤‖x‖) : physicalRadialCompactCutoffBase x=0 := by
  by_contra hne
  have hs : x∈Function.support ((ContDiffBumpBase.ofInnerProductSpace (Configuration 2)).toFun (3/2)) := hne
  rw [(ContDiffBumpBase.ofInnerProductSpace (Configuration 2)).support (3/2) (by norm_num)] at hs
  have hh := mem_ball_zero_iff.mp hs
  linarith

theorem physicalRadialCompactCutoffBase_hasCompactSupport :
    HasCompactSupport physicalRadialCompactCutoffBase := by
  have hs : tsupport physicalRadialCompactCutoffBase⊆closedBall 0 (3/2:ℝ) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    rw [mem_closedBall_zero_iff]
    by_contra hn
    exact hx (physicalRadialCompactCutoffBase_eq_zero (lt_of_not_ge hn).le)
  exact (isCompact_closedBall (0 : Configuration 2) (3/2:ℝ)).of_isClosed_subset isClosed_closure hs

def physicalRadialCompactCutoff (R : ℝ) (x : Configuration 2) : ℝ :=
  physicalRadialCompactCutoffBase (R⁻¹ • x)

theorem physicalRadialCompactCutoff_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (physicalRadialCompactCutoff R) :=
  physicalRadialCompactCutoffBase_contDiff.comp (contDiff_const_smul R⁻¹)

theorem physicalRadialCompactCutoff_hasCompactSupport {R : ℝ} (hR : 0<R) :
    HasCompactSupport (physicalRadialCompactCutoff R) :=
  physicalRadialCompactCutoffBase_hasCompactSupport.comp_smul (inv_ne_zero hR.ne')

theorem physicalRadialCompactCutoff_nonneg (R : ℝ) (x : Configuration 2) :
    0≤physicalRadialCompactCutoff R x :=
  ((ContDiffBumpBase.ofInnerProductSpace (Configuration 2)).mem_Icc (3/2) (R⁻¹ • x)).1

theorem physicalRadialCompactCutoff_le_one (R : ℝ) (x : Configuration 2) :
    physicalRadialCompactCutoff R x≤1 :=
  ((ContDiffBumpBase.ofInnerProductSpace (Configuration 2)).mem_Icc (3/2) (R⁻¹ • x)).2

theorem physicalRadialCompactCutoff_eq_one {R : ℝ} (hR : 0<R)
    {x : Configuration 2} (hx : ‖x‖≤R) : physicalRadialCompactCutoff R x=1 := by
  apply (ContDiffBumpBase.ofInnerProductSpace (Configuration 2)).eq_one (3/2) (by norm_num)
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
  calc R⁻¹*‖x‖≤R⁻¹*R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
       _=1 := inv_mul_cancel₀ hR.ne'

theorem physicalRadialCompactCutoff_eq_zero {R : ℝ} (hR : 0<R)
    {x : Configuration 2} (hx : (3/2)*R≤‖x‖) : physicalRadialCompactCutoff R x=0 := by
  apply physicalRadialCompactCutoffBase_eq_zero
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
  calc (3/2:ℝ)=R⁻¹*((3/2)*R) := by field_simp
       _≤R⁻¹*‖x‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)

theorem physicalRadialCompactCutoff_tsupport_subset {R : ℝ} (hR : 0<R) :
    tsupport (physicalRadialCompactCutoff R)⊆ball 0 (2*R) := by
  have hs : tsupport (physicalRadialCompactCutoff R)⊆closedBall 0 ((3/2)*R) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    rw [mem_closedBall_zero_iff]
    by_contra hn
    exact hx (physicalRadialCompactCutoff_eq_zero hR (lt_of_not_ge hn).le)
  intro x hx
  have hn : ‖x‖≤(3/2)*R := by simpa only [mem_closedBall_zero_iff] using hs hx
  rw [mem_ball_zero_iff]
  linarith

theorem physicalRadialCompactCutoff_isometry (R : ℝ)
    (Q : Configuration 2 ≃ₗᵢ[ℝ] Configuration 2) (x : Configuration 2) :
    physicalRadialCompactCutoff R (Q x)=physicalRadialCompactCutoff R x := by
  simp [physicalRadialCompactCutoff,physicalRadialCompactCutoffBase,
    ContDiffBumpBase.ofInnerProductSpace,norm_smul,Q.norm_map]

def physicalRadialCompactCutoffPartial (R : ℝ) (k : Coordinate 2) (x : Configuration 2) : ℝ :=
  fderiv ℝ (physicalRadialCompactCutoff R) x (coordinateVector k)

theorem physicalRadialCompactCutoffPartial_contDiff (R : ℝ) (k : Coordinate 2) :
    ContDiff ℝ ∞ (physicalRadialCompactCutoffPartial R k) :=
  ((physicalRadialCompactCutoff_contDiff R).fderiv_right
    (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const

theorem physicalRadialCompactCutoffPartial_hasCompactSupport {R : ℝ} (hR : 0<R)
    (k : Coordinate 2) : HasCompactSupport (physicalRadialCompactCutoffPartial R k) :=
  (physicalRadialCompactCutoff_hasCompactSupport hR).fderiv_apply ℝ (coordinateVector k)

def physicalRadialCompactCutoffSecond (R : ℝ) (k l : Coordinate 2) (x : Configuration 2) : ℝ :=
  fderiv ℝ (physicalRadialCompactCutoffPartial R k) x (coordinateVector l)

theorem physicalRadialCompactCutoffSecond_contDiff (R : ℝ) (k l : Coordinate 2) :
    ContDiff ℝ ∞ (physicalRadialCompactCutoffSecond R k l) :=
  ((physicalRadialCompactCutoffPartial_contDiff R k).fderiv_right
    (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const

theorem physicalRadialCompactCutoffSecond_hasCompactSupport {R : ℝ} (hR : 0<R)
    (k l : Coordinate 2) : HasCompactSupport (physicalRadialCompactCutoffSecond R k l) :=
  (physicalRadialCompactCutoffPartial_hasCompactSupport hR k).fderiv_apply ℝ (coordinateVector l)

theorem physicalRadialCompactCutoffPartial_scale (R : ℝ) (k : Coordinate 2) (x : Configuration 2) :
    physicalRadialCompactCutoffPartial R k x=
      R⁻¹*fderiv ℝ physicalRadialCompactCutoffBase (R⁻¹ • x) (coordinateVector k) := by
  have hbase : ContDiff ℝ ∞ physicalRadialCompactCutoffBase := physicalRadialCompactCutoffBase_contDiff
  have hb := (hbase.differentiable
    (by simp) (R⁻¹ • x)).hasFDerivAt
  have hh := hb.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).const_smul R⁻¹)
  change HasFDerivAt (𝕜:=ℝ) (fun y => physicalRadialCompactCutoffBase (R⁻¹ • y)) _ x at hh
  change fderiv ℝ (fun y => physicalRadialCompactCutoffBase (R⁻¹ • y)) x _=_
  rw [hh.fderiv]
  simp

theorem physicalRadialCompactCutoffSecond_scale (R : ℝ) (k l : Coordinate 2) (x : Configuration 2) :
    physicalRadialCompactCutoffSecond R k l x=R⁻¹^2*
      fderiv ℝ (fun y => fderiv ℝ physicalRadialCompactCutoffBase y (coordinateVector k))
        (R⁻¹ • x) (coordinateVector l) := by
  have he : physicalRadialCompactCutoffPartial R k=
      fun y => R⁻¹ • fderiv ℝ physicalRadialCompactCutoffBase (R⁻¹ • y) (coordinateVector k) := by
    funext y
    exact physicalRadialCompactCutoffPartial_scale R k y
  change fderiv ℝ (physicalRadialCompactCutoffPartial R k) x _=_
  rw [he]
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ physicalRadialCompactCutoffBase y (coordinateVector k)) :=
    (physicalRadialCompactCutoffBase_contDiff.fderiv_right
      (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const
  have hb := (hd.differentiable (by simp) (R⁻¹ • x)).hasFDerivAt
  have hh := (hb.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).const_smul R⁻¹)).const_smul R⁻¹
  change HasFDerivAt (𝕜:=ℝ) (fun y => R⁻¹ •
    fderiv ℝ physicalRadialCompactCutoffBase (R⁻¹ • y) (coordinateVector k)) _ x at hh
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  ring

theorem physicalRadialCompactCutoff_derivative_bounds :
    ∃ B1 B2 : ℝ, 0≤B1 ∧ 0≤B2 ∧ ∀ R : ℝ, 0<R → ∀ x : Configuration 2,
      (∀ k, ‖physicalRadialCompactCutoffPartial R k x‖≤B1/R) ∧
      (∀ k l, ‖physicalRadialCompactCutoffSecond R k l x‖≤B2/R^2) := by
  classical
  have hbase : ContDiff ℝ ∞ physicalRadialCompactCutoffBase := physicalRadialCompactCutoffBase_contDiff
  obtain ⟨B1,hB1⟩ := (physicalRadialCompactCutoffBase_hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hbase.continuous_fderiv (by simp))
  have hB10 : 0≤B1 := (norm_nonneg _).trans (hB1 0)
  have hex (k : Coordinate 2) : ∃ C : ℝ, ∀ x : Configuration 2,
      ‖fderiv ℝ (fun y => fderiv ℝ physicalRadialCompactCutoffBase y (coordinateVector k)) x‖≤C :=
    ((physicalRadialCompactCutoffBase_hasCompactSupport.fderiv_apply ℝ (coordinateVector k)).fderiv ℝ).exists_bound_of_continuous
        (((physicalRadialCompactCutoffBase_contDiff.fderiv_right
          (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const).continuous_fderiv (by simp))
  choose C hC using hex
  have hC0 (k : Coordinate 2) : 0≤C k := (norm_nonneg _).trans (hC k 0)
  refine ⟨B1,∑ k,C k,hB10,Finset.sum_nonneg (fun k _ => hC0 k),?_⟩
  intro R hR x
  have hunit (k : Coordinate 2) : ‖coordinateVector k‖=1 := by simp [coordinateVector]
  constructor
  · intro k
    rw [physicalRadialCompactCutoffPartial_scale,norm_mul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
    have hb : ‖fderiv ℝ physicalRadialCompactCutoffBase (R⁻¹ • x) (coordinateVector k)‖≤B1 := by
      calc _≤‖fderiv ℝ physicalRadialCompactCutoffBase (R⁻¹ • x)‖*‖coordinateVector k‖ :=
          ContinuousLinearMap.le_opNorm _ _
           _≤B1 := by simpa [hunit] using hB1 (R⁻¹ • x)
    simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hR.le)
  · intro k l
    rw [physicalRadialCompactCutoffSecond_scale,norm_mul,norm_pow,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
    have hb : ‖fderiv ℝ (fun y => fderiv ℝ physicalRadialCompactCutoffBase y (coordinateVector k))
        (R⁻¹ • x) (coordinateVector l)‖≤∑ k,C k := by
      calc _≤‖fderiv ℝ (fun y => fderiv ℝ physicalRadialCompactCutoffBase y (coordinateVector k)) (R⁻¹ • x)‖*‖coordinateVector l‖ := ContinuousLinearMap.le_opNorm _ _
           _≤C k := by simpa [hunit] using hC k (R⁻¹ • x)
           _≤∑ k,C k := Finset.single_le_sum (fun k _ => hC0 k) (Finset.mem_univ k)
    simpa [div_eq_mul_inv,inv_pow,mul_comm] using mul_le_mul_of_nonneg_left hb (sq_nonneg R⁻¹)

theorem physicalRadialCompactCutoffPartial_zero_inner {R : ℝ} (hR : 0<R)
    {x : Configuration 2} (hx : ‖x‖<R) (k : Coordinate 2) :
    physicalRadialCompactCutoffPartial R k x=0 := by
  change fderiv ℝ (physicalRadialCompactCutoff R) x _=0
  rw [fderiv_zero_of_constant_open isOpen_ball
    (fun y hy => physicalRadialCompactCutoff_eq_one hR (mem_ball_zero_iff.mp hy).le)
    (mem_ball_zero_iff.mpr hx)]
  rfl

theorem physicalRadialCompactCutoffSecond_zero_inner {R : ℝ} (hR : 0<R)
    {x : Configuration 2} (hx : ‖x‖<R) (k l : Coordinate 2) :
    physicalRadialCompactCutoffSecond R k l x=0 := by
  change fderiv ℝ (physicalRadialCompactCutoffPartial R k) x _=0
  rw [fderiv_zero_of_constant_open isOpen_ball
    (fun y hy => physicalRadialCompactCutoffPartial_zero_inner hR (mem_ball_zero_iff.mp hy) k)
    (mem_ball_zero_iff.mpr hx)]
  rfl

#print axioms physicalRadialCompactCutoffBase_contDiff
#print axioms physicalRadialCompactCutoff_tsupport_subset
#print axioms physicalRadialCompactCutoff_isometry
#print axioms physicalRadialCompactCutoff_derivative_bounds
#print axioms physicalRadialCompactCutoffSecond_zero_inner
end ManyBody.S8
