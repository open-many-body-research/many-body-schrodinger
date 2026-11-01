import TensorBoxUniformLimit_v1
import SmoothCoordinateSubsetFields7_v1
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Finite coordinate uniform limits give an actual Frechet derivative limit
on open subsets of the seven-coordinate box. The full derivative is assembled
by the exact continuous linear piRing equivalence, not an assumed gradient. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

def coordinateDerivativeMap7 (h : Fin 7 → ℂ) : (Fin 7 → ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℂ) (Fin 7)).symm h

theorem coordinateDerivativeMap7_fderiv (f : (Fin 7 → ℝ) → ℂ) (x : Fin 7 → ℝ) :
    coordinateDerivativeMap7 (fun i => fderiv ℝ f x (Pi.single i (1 : ℝ))) = fderiv ℝ f x :=
  (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℂ) (Fin 7)).symm_apply_apply _

theorem tensor_box7_uniformly_pi
    {a b : Fin 7 → ℝ} {f : ℕ → (Fin 7 → ℝ) → Fin 7 → ℂ}
    {g : (Fin 7 → ℝ) → Fin 7 → ℂ}
    (h : ∀ i, TendstoUniformlyOn (fun n x => f n x i) (fun x => g x i)
      atTop (tensorClosedBox7 a b)) :
    TendstoUniformlyOn f g atTop (tensorClosedBox7 a b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hi : ∀ i, ∀ᶠ n in atTop, ∀ x ∈ tensorClosedBox7 a b,
      dist (g x i) (f n x i) < ε :=
    fun i => Metric.tendstoUniformlyOn_iff.mp (h i) ε hε
  filter_upwards [Filter.eventually_all.mpr hi] with n hn x hx
  exact (dist_pi_lt_iff hε).mpr (fun i => hn i x hx)

theorem tensor_box7_fderiv_uniform_limit
    {a b : Fin 7 → ℝ} (f : ℕ → (Fin 7 → ℝ) → ℂ)
    {h : (Fin 7 → ℝ) → Fin 7 → ℂ}
    (hD : ∀ i, TendstoUniformlyOn
      (fun n x => fderiv ℝ (f n) x (Pi.single i (1 : ℝ))) (fun x => h x i)
      atTop (tensorClosedBox7 a b)) :
    TendstoUniformlyOn (fun n => fderiv ℝ (f n)) (fun x => coordinateDerivativeMap7 (h x))
      atTop (tensorClosedBox7 a b) := by
  have hp := tensor_box7_uniformly_pi hD
  have he := ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℂ) (Fin 7)).symm.toContinuousLinearMap.uniformContinuous).comp_tendstoUniformlyOn hp
  change TendstoUniformlyOn (fun n x => coordinateDerivativeMap7
    (fun i => fderiv ℝ (f n) x (Pi.single i (1 : ℝ))))
    (fun x => coordinateDerivativeMap7 (h x)) atTop (tensorClosedBox7 a b) at he
  simpa only [coordinateDerivativeMap7_fderiv] using he

theorem tensor_box7_limit_hasFDerivAt
    {a b : Fin 7 → ℝ} {U : Set (Fin 7 → ℝ)} (hU : IsOpen U)
    (hUK : U ⊆ tensorClosedBox7 a b)
    (f : ℕ → (Fin 7 → ℝ) → ℂ) (hf : ∀ n x, x ∈ U → DifferentiableAt ℝ (f n) x)
    {g : (Fin 7 → ℝ) → ℂ}
    (hg : TendstoUniformlyOn f g atTop (tensorClosedBox7 a b))
    {h : (Fin 7 → ℝ) → Fin 7 → ℂ}
    (hD : ∀ i, TendstoUniformlyOn
      (fun n x => fderiv ℝ (f n) x (Pi.single i (1 : ℝ))) (fun x => h x i)
      atTop (tensorClosedBox7 a b))
    {x : Fin 7 → ℝ} (hx : x ∈ U) :
    HasFDerivAt g (coordinateDerivativeMap7 (h x)) x := by
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn hU
    ((tensor_box7_fderiv_uniform_limit f hD).mono hUK).tendstoLocallyUniformlyOn
    (fun n y hy => (hf n y hy).hasFDerivAt)
    (fun y hy => hg.tendsto_at (hUK hy)) hx

end TheoremT.Continuum
