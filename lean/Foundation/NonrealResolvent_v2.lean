import UnboundedResolvent_v2
import CoerciveClosedInverse_v2

/-! Nonreal points belong to the ordinary bounded-inverse resolvent of an
actual self-adjoint partial operator. No spectral-measure theorem is assumed. -/
noncomputable section
open scoped InnerProductSpace ComplexConjugate LinearPMap
namespace TheoremT.OperatorTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem operatorShift_isClosed (A : E →ₗ.[ℂ] E) (hA : A.IsClosed) (z : ℂ) :
    (operatorShift A z).IsClosed := by
  have heq : ((operatorShift A z).graph : Set (E × E)) =
      (fun p : E × E => (p.1,p.2+z•p.1)) ⁻¹' (A.graph : Set (E × E)) := by
    ext p
    change p ∈ (operatorShift A z).graph ↔ (p.1,p.2+z•p.1) ∈ A.graph
    rw [LinearPMap.mem_graph_iff,LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨x,hx,hy⟩
      refine ⟨x,hx,?_⟩
      change A x-z•(x:E)=p.2 at hy
      rw [← hx]
      exact (sub_eq_iff_eq_add).mp hy
    · rintro ⟨x,hx,hy⟩
      refine ⟨x,hx,?_⟩
      change A x-z•(x:E)=p.2
      rw [← hx] at hy
      exact (sub_eq_iff_eq_add).mpr hy
  change _root_.IsClosed ((operatorShift A z).graph : Set (E × E))
  rw [heq]
  exact hA.preimage (continuous_fst.prodMk (continuous_snd.add (continuous_fst.const_smul z)))

theorem symmetric_inner_self_im_zero (A : E →ₗ.[ℂ] E) (hsym : A.IsFormalAdjoint A)
    (x : A.domain) : (inner ℂ (x : E) (A x)).im = 0 := by
  have h := inner_im_symm (𝕜 := ℂ) (x : E) (A x)
  rw [hsym x x] at h
  change (inner ℂ (x:E) (A x)).im = -(inner ℂ (x:E) (A x)).im at h
  linarith

theorem nonreal_shift_norm_bound (A : E →ₗ.[ℂ] E) (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : E)‖ ≤ ‖operatorShift A z x‖ := by
  have hi : (inner ℂ (x : E) (operatorShift A z x)).im = -z.im*‖(x:E)‖^2 := by
    rw [operatorShift_apply,inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K]
    simp [symmetric_inner_self_im_zero A hsym x,← Complex.ofReal_pow]
  have hb := (Complex.abs_im_le_norm (inner ℂ (x:E) (operatorShift A z x))).trans
    (norm_inner_le_norm (x:E) (operatorShift A z x))
  rw [hi,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg ‖(x:E)‖)] at hb
  by_cases hx : ‖(x:E)‖=0
  · simp only [hx,mul_zero]
    exact norm_nonneg _
  · have hxpos : 0<‖(x:E)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    nlinarith

theorem nonreal_shift_dense_range (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) : Dense ((operatorShift A z).toFun.range : Set E) := by
  let S := operatorShift A z
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff,Submodule.eq_bot_iff]
  intro y hy
  have hy0 : ∀ x : A.domain, inner ℂ y (A x) = z*inner ℂ y (x:E) := by
    intro x
    have h := (S.toFun.range.mem_orthogonal' y).1 hy (S x) ⟨x,rfl⟩
    change inner ℂ y (A x-z•(x:E))=0 at h
    rw [inner_sub_right,inner_smul_right] at h
    exact sub_eq_zero.mp h
  have hym : y ∈ A.adjoint.domain := by
    apply A.mem_adjoint_domain_of_exists y
    refine ⟨(starRingEnd ℂ z)•y,?_⟩
    intro x
    simp only [inner_smul_left,starRingEnd_self_apply,hy0 x]
  have hya : A.adjoint ⟨y,hym⟩ = (starRingEnd ℂ z)•y := by
    apply A.adjoint_apply_eq hA.dense_domain
    intro x
    simp only [inner_smul_left,starRingEnd_self_apply,hy0 x]
  have hle : A.adjoint ≤ A := le_of_eq (LinearPMap.isSelfAdjoint_def.mp hA)
  have hymA : y ∈ A.domain := hle.1 hym
  have heq : A ⟨y,hymA⟩ = (starRingEnd ℂ z)•y := (hle.2 rfl).symm.trans hya
  have hb := nonreal_shift_norm_bound A (selfAdjoint_formalAdjoint hA)
    (starRingEnd ℂ z) ⟨y,hymA⟩
  rw [operatorShift_apply,heq,sub_self,norm_zero] at hb
  simp only [Complex.conj_im,abs_neg] at hb
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg y]

theorem nonreal_mem_unboundedResolventSet (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) : z ∈ unboundedResolventSet A := by
  obtain ⟨R,hR,hr,hl,_⟩ := coercive_closed_dense_bounded_inverse (operatorShift A z)
    (operatorShift_isClosed A hA.isClosed z) (nonreal_shift_dense_range A hA z hz)
    (abs_pos.mpr hz) (nonreal_shift_norm_bound A (selfAdjoint_formalAdjoint hA) z)
  exact ⟨R,hR,hr,hl⟩

theorem unboundedSpectrum_im_eq_zero (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z ∈ unboundedSpectrum A) : z.im = 0 := by
  by_contra h
  exact hz (nonreal_mem_unboundedResolventSet A hA z h)

#print axioms operatorShift_isClosed
#print axioms nonreal_mem_unboundedResolventSet
#print axioms unboundedSpectrum_im_eq_zero
end TheoremT.OperatorTheory
