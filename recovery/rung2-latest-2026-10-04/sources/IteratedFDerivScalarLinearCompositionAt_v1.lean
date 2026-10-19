import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Scalar-field-general local right composition of iterated derivatives.
This extends the separate complex-only continuation lemma to allow real
coordinate embeddings, preserving its final source unchanged. -/
noncomputable section
set_option autoImplicit false
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem iteratedFDeriv_comp_right_of_contDiffAt_scalar
    (g : G →L[𝕜] E) (f : E → F) (x : G) (n : ℕ)
    (hf : ContDiffAt 𝕜 n f (g x)) :
    iteratedFDeriv 𝕜 n (f ∘ g) x =
      (iteratedFDeriv 𝕜 n f (g x)).compContinuousLinearMap (fun _ => g) := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn (m := (n : ℕ∞ω)) le_rfl (by simp)
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  have hpre : IsOpen (g ⁻¹' V) := hV.preimage g.continuous
  have heq := g.iteratedFDerivWithin_comp_right
    (hfU.mono hVU) hV.uniqueDiffOn hpre.uniqueDiffOn hxV (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpre hxV,
    iteratedFDerivWithin_of_isOpen n hV hxV] at heq
  exact heq

end TheoremT.Continuum
