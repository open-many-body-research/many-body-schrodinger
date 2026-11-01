import SmoothComplexMixedSourceBounds_v1
import Mathlib.Data.List.OfFn

/-! Actual ordered complex directional derivatives indexed by a finite array.
Smoothness on the open region is explicit. This is an array/list compatibility
endpoint for the existing actual iterated Frechet derivative, not an arbitrary
jet family or an assumption about an operator norm. -/
set_option autoImplicit false
noncomputable section
open scoped Topology ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem complexDirectionalWordDeriv_ofFn_eq_iteratedFDeriv {ι : Type}
    (dirs : ι → Space κ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {f : Space κ → ℂ} (hf : ContDiffOn ℝ ∞ f Ω)
    {k : ℕ} (a : Fin k → ι) {x : Space κ} (hx : x ∈ Ω) :
    complexDirectionalWordDeriv dirs f (List.ofFn a) x =
      iteratedFDeriv ℝ k f x (fun j => dirs (a j)) := by
  induction k generalizing x with
  | zero => simp [List.ofFn_zero, complexDirectionalWordDeriv, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ]
    have heq : complexDirectionalWordDeriv dirs f (List.ofFn (fun i => a i.succ)) =ᶠ[𝓝 x]
        (fun q => iteratedFDeriv ℝ k f q (fun i => dirs (a i.succ))) := by
      filter_upwards [hΩ.mem_nhds hx] with q hq
      exact ih (fun i => a i.succ) hq
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
      (hf.contDiffAt (hΩ.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top k)
    change fderiv ℝ (complexDirectionalWordDeriv dirs f (List.ofFn (fun i => a i.succ)))
      x (dirs (a 0)) = _
    rw [heq.fderiv_eq]
    symm
    exact hd.iteratedFDeriv_succ_apply_left' (m := fun i => dirs (a i))

end TheoremT.Continuum.WeakGrushin
