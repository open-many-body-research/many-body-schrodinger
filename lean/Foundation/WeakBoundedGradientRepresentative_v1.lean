import BoundedGradientMollifier_v1
import ComplexLipschitzExtension_v1

/-! A genuine globally Lipschitz representative of an actual L2 weak Sobolev
function whose actual first derivatives are essentially bounded. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace TheoremT.Continuum

theorem weak_bounded_gradient_lipschitz_representative {N : ℕ}
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k)
    (hdtop : ∀ k, MemLp (d k) ⊤ volume) :
    ∃ K : ℝ≥0, ∃ u : Configuration N → ℂ,
      LipschitzWith K u ∧ (f : Configuration N → ℂ) =ᵐ[volume] u := by
  obtain ⟨K,hK⟩ := weak_gradient_mollifications_uniform_lipschitz f d hd hdtop
  let S : Set (Configuration N) := {x | Tendsto
    (fun n => mollify (mollifierKernel N n) f x) atTop (𝓝 (f x))}
  have hS : ∀ᵐ x ∂volume, x ∈ S := mollifyKernel_ae_tendsto f
  have hLip : LipschitzOnWith K (f : Configuration N → ℂ) S :=
    uniform_lipschitz_pointwise_limit_on hK (fun x hx => hx)
  obtain ⟨u,hu,hEq⟩ := complex_lipschitzOn_extension hLip
  exact ⟨K+K,u,hu,hS.mono (fun x hx => hEq hx)⟩

#print axioms weak_bounded_gradient_lipschitz_representative
end TheoremT.Continuum
