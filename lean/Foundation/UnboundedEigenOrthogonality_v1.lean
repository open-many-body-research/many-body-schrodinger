import NonrealResolvent_v2

/-! Orthogonality for genuine domain eigenvectors of a symmetric partial
operator; no finite-dimensional eigenbasis or second-domain premise. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.OperatorTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem symmetric_domain_eigenvectors_orthogonal (A : E →ₗ.[ℂ] E)
    (hsym : A.IsFormalAdjoint A) (g u : A.domain) (a b : ℝ) (hab : a ≠ b)
    (hAg : A g = (a : ℂ) • (g : E)) (hAu : A u = (b : ℂ) • (u : E)) :
    inner ℂ (g : E) (u : E) = 0 := by
  have h := hsym g u
  rw [hAg,hAu,inner_smul_left,inner_smul_right,Complex.conj_ofReal] at h
  by_contra hi
  exact hab (Complex.ofReal_inj.mp (mul_right_cancel₀ hi h))

#print axioms symmetric_domain_eigenvectors_orthogonal
end TheoremT.OperatorTheory
