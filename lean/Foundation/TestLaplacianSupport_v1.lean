import LocalWeakLaplacian_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem realTestLaplacian_tsupport_subset {N : ℕ} (φ : Configuration N → ℝ) :
    tsupport (realTestLaplacian φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hd (k : Coordinate N) : x ∉ tsupport (fun y => fderiv ℝ φ y (coordinateVector k)) :=
    fun h => hn (tsupport_fderiv_apply_subset ℝ (coordinateVector k) h)
  apply hx
  simp [realTestLaplacian,fun k => fderiv_of_notMem_tsupport ℝ (hd k)]

#print axioms realTestLaplacian_tsupport_subset
end TheoremT.Continuum
