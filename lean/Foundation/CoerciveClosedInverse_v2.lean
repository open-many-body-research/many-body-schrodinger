import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! A closed actual operator with dense range and positive lower norm bound
has a bounded everywhere-defined two-sided inverse. This generalizes the
previous self-adjoint lemma to nonreal shifts without assuming surjectivity. -/
noncomputable section
open Filter
open scoped Topology LinearPMap
namespace TheoremT.OperatorTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Positive lower norm control gives an actual continuous linear inverse,
with a domain witness and both inverse identities, and its operator norm bound.
No range, inverse, or closed-range conclusion is assumed. -/
theorem coercive_closed_dense_bounded_inverse (A : E →ₗ.[ℂ] E)
    (hclosed : A.IsClosed) (hrange : Dense (A.toFun.range : Set E))
    {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ x : A.domain, δ * ‖(x : E)‖ ≤ ‖A x‖) :
    ∃ R : E →L[ℂ] E, ∃ hR : ∀ y : E, R y ∈ A.domain,
      (∀ y : E, A ⟨R y,hR y⟩ = y) ∧
      (∀ x : A.domain, R (A x) = (x : E)) ∧ ‖R‖ ≤ δ⁻¹ := by
  have hk : A.ker = ⊥ := by
    rw [LinearPMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    apply norm_eq_zero.1
    have hb := hbound x
    rw [hx, norm_zero] at hb
    nlinarith [norm_nonneg (x : E)]
  have hIdense : Dense (A.inverse.domain : Set E) := by
    simpa only [LinearPMap.inverse_domain] using hrange
  have hinv (y : A.inverse.domain) : ‖A.inverse y‖ ≤ δ⁻¹ * ‖y‖ := by
    have hy : (y : E) ∈ A.toFun.range := by
      simpa only [LinearPMap.inverse_domain] using y.property
    obtain ⟨x,hx⟩ := hy
    have hxy : A x = (y : E) := hx
    rw [A.inverse_apply_eq hk hxy]
    have hb := hbound x
    rw [hxy] at hb
    calc
      ‖(x : E)‖ ≤ ‖(y : E)‖ / δ := (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hb)
      _ = δ⁻¹ * ‖y‖ := by rw [div_eq_mul_inv, mul_comm]; rfl
  let B : A.inverse.domain →L[ℂ] E := A.inverse.toFun.mkContinuous (δ⁻¹) hinv
  let R : E →L[ℂ] E := B.extend A.inverse.domain.subtypeL
  have hRe (y : A.inverse.domain) : R (y : E) = A.inverse y :=
    ContinuousLinearMap.extend_eq B hIdense.denseRange_val
      isUniformEmbedding_subtype_val.isUniformInducing y
  have hRbound : ∀ y : E, ‖R y‖ ≤ δ⁻¹ * ‖y‖ := by
    intro y
    refine hIdense.induction (P := fun z => ‖R z‖ ≤ δ⁻¹ * ‖z‖) ?_ ?_ y
    · intro y hy
      have hh := hinv ⟨y,hy⟩
      rwa [← hRe ⟨y,hy⟩] at hh
    · exact isClosed_le R.continuous.norm (continuous_const.mul continuous_norm)
  have hgraph : ∀ y : E, (R y,y) ∈ A.graph := by
    intro y
    refine hIdense.induction (P := fun z => (R z,z) ∈ A.graph) ?_ ?_ y
    · intro y hy
      change y ∈ A.inverse.domain at hy
      have hyt : y ∈ A.toFun.range := by
        simpa only [LinearPMap.inverse_domain] using hy
      obtain ⟨x,hx⟩ := hyt
      have hxy : A x = y := hx
      have hRy : R y = (x : E) :=
        (hRe ⟨y,hy⟩).trans (A.inverse_apply_eq hk hxy)
      rw [hRy, ← hxy]
      exact A.mem_graph x
    · exact hclosed.preimage (R.continuous.prodMk continuous_id)
  have hRdom : ∀ y : E, R y ∈ A.domain :=
    fun y => LinearPMap.mem_domain_of_mem_graph (hgraph y)
  refine ⟨R,hRdom,?_,?_,?_⟩
  · intro y
    exact ((LinearPMap.image_iff (hRdom y)).2 (hgraph y)).symm
  · intro x
    have hy : A x ∈ A.inverse.domain := by
      rw [LinearPMap.inverse_domain]
      exact ⟨x,rfl⟩
    exact (hRe ⟨A x,hy⟩).trans (A.inverse_apply_eq hk rfl)
  · exact ContinuousLinearMap.opNorm_le_bound R (inv_nonneg.mpr hδ.le) hRbound

set_option pp.proofs false in
#print coercive_closed_dense_bounded_inverse
#print axioms coercive_closed_dense_bounded_inverse
end TheoremT.OperatorTheory
