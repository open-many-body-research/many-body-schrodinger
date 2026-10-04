import ScaledCutoffSecond_v2
import ConstantOpenDerivative_v1

/-! One genuine compact smooth cutoff in the actual physical configuration space,
with a strict support margin and first/second derivative scaling before any state. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalCompactCutoffBase : ContDiffBump (0 : Configuration 2) :=
  ⟨1, 3/2, by norm_num, by norm_num⟩

def physicalCompactCutoff (R : ℝ) (x : Configuration 2) : ℝ :=
  physicalCompactCutoffBase (R⁻¹ • x)

theorem physicalCompactCutoff_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (physicalCompactCutoff R) :=
  physicalCompactCutoffBase.contDiff.comp (contDiff_const_smul R⁻¹)

theorem physicalCompactCutoff_hasCompactSupport {R : ℝ} (hR : 0<R) :
    HasCompactSupport (physicalCompactCutoff R) :=
  physicalCompactCutoffBase.hasCompactSupport.comp_smul (inv_ne_zero hR.ne')

theorem physicalCompactCutoff_nonneg (R : ℝ) (x : Configuration 2) :
    0≤physicalCompactCutoff R x := physicalCompactCutoffBase.nonneg

theorem physicalCompactCutoff_le_one (R : ℝ) (x : Configuration 2) :
    physicalCompactCutoff R x≤1 := physicalCompactCutoffBase.le_one

theorem physicalCompactCutoff_eq_one {R : ℝ} (hR : 0<R)
    {x : Configuration 2} (hx : ‖x‖≤R) : physicalCompactCutoff R x=1 := by
  apply physicalCompactCutoffBase.one_of_mem_closedBall
  change dist (R⁻¹ • x) 0≤(1:ℝ)
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
  calc R⁻¹*‖x‖≤R⁻¹*R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
       _=1 := inv_mul_cancel₀ hR.ne'

theorem physicalCompactCutoff_eq_zero {R : ℝ} (hR : 0<R)
    {x : Configuration 2} (hx : (3/2)*R≤‖x‖) : physicalCompactCutoff R x=0 := by
  apply physicalCompactCutoffBase.zero_of_le_dist
  change (3/2:ℝ)≤dist (R⁻¹ • x) 0
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
  calc (3/2:ℝ)=R⁻¹*((3/2)*R) := by field_simp
       _≤R⁻¹*‖x‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)

theorem physicalCompactCutoff_tsupport_subset {R : ℝ} (hR : 0<R) :
    tsupport (physicalCompactCutoff R)⊆ball 0 (2*R) := by
  have hs : tsupport (physicalCompactCutoff R)⊆closedBall 0 ((3/2)*R) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    rw [mem_closedBall_zero_iff]
    by_contra hn
    exact hx (physicalCompactCutoff_eq_zero hR (lt_of_not_ge hn).le)
  intro x hx
  have hn : ‖x‖≤(3/2)*R := by simpa only [mem_closedBall_zero_iff] using hs hx
  rw [mem_ball_zero_iff]
  linarith

def physicalCompactCutoffPartial (R : ℝ) (k : Coordinate 2) (x : Configuration 2) : ℝ :=
  fderiv ℝ (physicalCompactCutoff R) x (coordinateVector k)

theorem physicalCompactCutoffPartial_contDiff (R : ℝ) (k : Coordinate 2) :
    ContDiff ℝ ∞ (physicalCompactCutoffPartial R k) :=
  ((physicalCompactCutoff_contDiff R).fderiv_right
    (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const

theorem physicalCompactCutoffPartial_hasCompactSupport {R : ℝ} (hR : 0<R)
    (k : Coordinate 2) : HasCompactSupport (physicalCompactCutoffPartial R k) :=
  (physicalCompactCutoff_hasCompactSupport hR).fderiv_apply ℝ (coordinateVector k)

def physicalCompactCutoffSecond (R : ℝ) (k l : Coordinate 2) (x : Configuration 2) : ℝ :=
  fderiv ℝ (physicalCompactCutoffPartial R k) x (coordinateVector l)

theorem physicalCompactCutoffSecond_contDiff (R : ℝ) (k l : Coordinate 2) :
    ContDiff ℝ ∞ (physicalCompactCutoffSecond R k l) :=
  ((physicalCompactCutoffPartial_contDiff R k).fderiv_right
    (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const

theorem physicalCompactCutoffSecond_hasCompactSupport {R : ℝ} (hR : 0<R)
    (k l : Coordinate 2) : HasCompactSupport (physicalCompactCutoffSecond R k l) :=
  (physicalCompactCutoffPartial_hasCompactSupport hR k).fderiv_apply ℝ (coordinateVector l)

theorem physicalCompactCutoffPartial_scale (R : ℝ) (k : Coordinate 2) (x : Configuration 2) :
    physicalCompactCutoffPartial R k x=
      R⁻¹*fderiv ℝ physicalCompactCutoffBase (R⁻¹ • x) (coordinateVector k) := by
  have hbase : ContDiff ℝ ∞ physicalCompactCutoffBase := physicalCompactCutoffBase.contDiff
  have hb := (hbase.differentiable
    (by simp) (R⁻¹ • x)).hasFDerivAt
  have hh := hb.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).const_smul R⁻¹)
  change HasFDerivAt (𝕜:=ℝ) (fun y => physicalCompactCutoffBase (R⁻¹ • y)) _ x at hh
  change fderiv ℝ (fun y => physicalCompactCutoffBase (R⁻¹ • y)) x _=_
  rw [hh.fderiv]
  simp

theorem physicalCompactCutoffSecond_scale (R : ℝ) (k l : Coordinate 2) (x : Configuration 2) :
    physicalCompactCutoffSecond R k l x=R⁻¹^2*
      fderiv ℝ (fun y => fderiv ℝ physicalCompactCutoffBase y (coordinateVector k))
        (R⁻¹ • x) (coordinateVector l) := by
  have he : physicalCompactCutoffPartial R k=
      fun y => R⁻¹ • fderiv ℝ physicalCompactCutoffBase (R⁻¹ • y) (coordinateVector k) := by
    funext y
    exact physicalCompactCutoffPartial_scale R k y
  change fderiv ℝ (physicalCompactCutoffPartial R k) x _=_
  rw [he]
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ physicalCompactCutoffBase y (coordinateVector k)) :=
    (physicalCompactCutoffBase.contDiff.fderiv_right
      (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const
  have hb := (hd.differentiable (by simp) (R⁻¹ • x)).hasFDerivAt
  have hh := (hb.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).const_smul R⁻¹)).const_smul R⁻¹
  change HasFDerivAt (𝕜:=ℝ) (fun y => R⁻¹ •
    fderiv ℝ physicalCompactCutoffBase (R⁻¹ • y) (coordinateVector k)) _ x at hh
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  ring

theorem physicalCompactCutoff_derivative_bounds :
    ∃ B1 B2 : ℝ, 0≤B1 ∧ 0≤B2 ∧ ∀ R : ℝ, 0<R → ∀ x : Configuration 2,
      (∀ k, ‖physicalCompactCutoffPartial R k x‖≤B1/R) ∧
      (∀ k l, ‖physicalCompactCutoffSecond R k l x‖≤B2/R^2) := by
  classical
  have hbase : ContDiff ℝ ∞ physicalCompactCutoffBase := physicalCompactCutoffBase.contDiff
  obtain ⟨B1,hB1⟩ := (physicalCompactCutoffBase.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hbase.continuous_fderiv (by simp))
  have hB10 : 0≤B1 := (norm_nonneg _).trans (hB1 0)
  have hex (k : Coordinate 2) : ∃ C : ℝ, ∀ x : Configuration 2,
      ‖fderiv ℝ (fun y => fderiv ℝ physicalCompactCutoffBase y (coordinateVector k)) x‖≤C :=
    ((physicalCompactCutoffBase.hasCompactSupport.fderiv_apply ℝ (coordinateVector k)).fderiv ℝ).exists_bound_of_continuous
        (((physicalCompactCutoffBase.contDiff.fderiv_right
          (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiff_const).continuous_fderiv (by simp))
  choose C hC using hex
  have hC0 (k : Coordinate 2) : 0≤C k := (norm_nonneg _).trans (hC k 0)
  refine ⟨B1,∑ k,C k,hB10,Finset.sum_nonneg (fun k _ => hC0 k),?_⟩
  intro R hR x
  have hunit (k : Coordinate 2) : ‖coordinateVector k‖=1 := by simp [coordinateVector]
  constructor
  · intro k
    rw [physicalCompactCutoffPartial_scale,norm_mul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
    have hb : ‖fderiv ℝ physicalCompactCutoffBase (R⁻¹ • x) (coordinateVector k)‖≤B1 := by
      calc _≤‖fderiv ℝ physicalCompactCutoffBase (R⁻¹ • x)‖*‖coordinateVector k‖ :=
          ContinuousLinearMap.le_opNorm _ _
           _≤B1 := by simpa [hunit] using hB1 (R⁻¹ • x)
    simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hR.le)
  · intro k l
    rw [physicalCompactCutoffSecond_scale,norm_mul,norm_pow,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
    have hb : ‖fderiv ℝ (fun y => fderiv ℝ physicalCompactCutoffBase y (coordinateVector k))
        (R⁻¹ • x) (coordinateVector l)‖≤∑ k,C k := by
      calc _≤‖fderiv ℝ (fun y => fderiv ℝ physicalCompactCutoffBase y (coordinateVector k)) (R⁻¹ • x)‖*‖coordinateVector l‖ := ContinuousLinearMap.le_opNorm _ _
           _≤C k := by simpa [hunit] using hC k (R⁻¹ • x)
           _≤∑ k,C k := Finset.single_le_sum (fun k _ => hC0 k) (Finset.mem_univ k)
    simpa [div_eq_mul_inv,inv_pow,mul_comm] using mul_le_mul_of_nonneg_left hb (sq_nonneg R⁻¹)

theorem physicalCompactCutoffPartial_zero_inner {R : ℝ} (hR : 0<R)
    {x : Configuration 2} (hx : ‖x‖<R) (k : Coordinate 2) :
    physicalCompactCutoffPartial R k x=0 := by
  change fderiv ℝ (physicalCompactCutoff R) x _=0
  rw [fderiv_zero_of_constant_open isOpen_ball
    (fun y hy => physicalCompactCutoff_eq_one hR (mem_ball_zero_iff.mp hy).le)
    (mem_ball_zero_iff.mpr hx)]
  rfl

theorem physicalCompactCutoffSecond_zero_inner {R : ℝ} (hR : 0<R)
    {x : Configuration 2} (hx : ‖x‖<R) (k l : Coordinate 2) :
    physicalCompactCutoffSecond R k l x=0 := by
  change fderiv ℝ (physicalCompactCutoffPartial R k) x _=0
  rw [fderiv_zero_of_constant_open isOpen_ball
    (fun y hy => physicalCompactCutoffPartial_zero_inner hR (mem_ball_zero_iff.mp hy) k)
    (mem_ball_zero_iff.mpr hx)]
  rfl

#print axioms physicalCompactCutoff_tsupport_subset
#print axioms physicalCompactCutoff_derivative_bounds
#print axioms physicalCompactCutoffSecond_zero_inner
end ManyBody.S8