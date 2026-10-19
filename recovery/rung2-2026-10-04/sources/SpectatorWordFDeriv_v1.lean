import SpectatorWordSplits_v1
import GrushinRescaledCutoffCoefficients_v1
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! Actual ordered spectator derivatives are evaluations of the iterated
Frechet derivative on the corresponding ordered tuple of unit directions.
The resulting norm comparison introduces no word length or dimension factor.
Only the coefficient is smooth; no solution regularity is a premise. -/
noncomputable section
open scoped Topology ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def spectatorWordDirections : (w : List κ) → Fin w.length → Space κ
  | [] => Fin.elim0
  | j :: w => Fin.cons (tDir j) (spectatorWordDirections w)

theorem spectatorWordDirections_norm (w : List κ) (i : Fin w.length) :
    ‖spectatorWordDirections w i‖ = 1 := by
  induction w with
  | nil => exact Fin.elim0 i
  | cons j w ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · exact cutoff_tDir_norm j
    · exact ih k

theorem spectatorWordDeriv_eq_iteratedFDeriv {Ω : Set (Space κ)}
    (hΩ : IsOpen Ω) {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    (w : List κ) {p : Space κ} (hp : p ∈ Ω) :
    spectatorWordDeriv B w p =
      iteratedFDeriv ℝ w.length B p (spectatorWordDirections w) := by
  induction w generalizing p with
  | nil => rfl
  | cons j w ih =>
    have heq : spectatorWordDeriv B w =ᶠ[𝓝 p]
        (fun q => iteratedFDeriv ℝ w.length B q (spectatorWordDirections w)) := by
      filter_upwards [hΩ.mem_nhds hp] with q hq
      exact ih hq
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length B) p :=
      (hB.contDiffAt (hΩ.mem_nhds hp)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top w.length)
    change fderiv ℝ (spectatorWordDeriv B w) p (tDir j) = _
    rw [heq.fderiv_eq]
    symm
    simpa only [List.length_cons, spectatorWordDirections, Fin.cons_zero,
      Fin.tail_cons] using
      (hd.iteratedFDeriv_succ_apply_left'
        (m := Fin.cons (tDir j) (spectatorWordDirections w)))

theorem spectatorWordDeriv_abs_le_iteratedFDeriv {Ω : Set (Space κ)}
    (hΩ : IsOpen Ω) {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    (w : List κ) {p : Space κ} (hp : p ∈ Ω) :
    |spectatorWordDeriv B w p| ≤ ‖iteratedFDeriv ℝ w.length B p‖ := by
  rw [spectatorWordDeriv_eq_iteratedFDeriv hΩ hB w hp]
  simpa only [Real.norm_eq_abs, spectatorWordDirections_norm,
    Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ w.length B p).le_opNorm (spectatorWordDirections w)

theorem spectatorWordDeriv_finite_bound {Ω : Set (Space κ)}
    (hΩ : IsOpen Ω) {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {S : Set (Space κ)} (hS : S ⊆ Ω) {m : ℕ} {M : ℝ}
    (hM : ∀ k ≤ m, ∀ p ∈ S, ‖iteratedFDeriv ℝ k B p‖ ≤ M) :
    ∀ w : List κ, w.length ≤ m → ∀ p ∈ S,
      |spectatorWordDeriv B w p| ≤ M := by
  intro w hw p hp
  exact (spectatorWordDeriv_abs_le_iteratedFDeriv hΩ hB w (hS hp)).trans
    (hM w.length hw p hp)

#print axioms spectatorWordDirections_norm
#print axioms spectatorWordDeriv_eq_iteratedFDeriv
#print axioms spectatorWordDeriv_abs_le_iteratedFDeriv
#print axioms spectatorWordDeriv_finite_bound
end TheoremT.Continuum.WeakGrushin
