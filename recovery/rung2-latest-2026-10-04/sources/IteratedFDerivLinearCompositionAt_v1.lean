import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

/-! Local right composition of an iterated derivative with a continuous
linear map. The hypothesis is only ContDiffAt at the actual image point.
An open neighborhood permits application of the pinned within-set chain
rule without requiring global smoothness. -/
noncomputable section
set_option autoImplicit false
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem iteratedFDeriv_comp_right_of_contDiffAt
    (g : G →L[ℂ] E) (f : E → F) (x : G) (n : ℕ)
    (hf : ContDiffAt ℂ n f (g x)) :
    iteratedFDeriv ℂ n (f ∘ g) x =
      (iteratedFDeriv ℂ n f (g x)).compContinuousLinearMap (fun _ => g) := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn (m := (n : ℕ∞ω)) le_rfl (by simp)
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  have hpre : IsOpen (g ⁻¹' V) := hV.preimage g.continuous
  have heq := g.iteratedFDerivWithin_comp_right
    (hfU.mono hVU) hV.uniqueDiffOn hpre.uniqueDiffOn hxV (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpre hxV,
    iteratedFDerivWithin_of_isOpen n hV hxV] at heq
  exact heq

end TheoremT.Continuum
