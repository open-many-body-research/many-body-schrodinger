import ProductDirectionalWordLeibniz_v1
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! Ordered derivatives in supplied constant directions are evaluations
of the actual iterated Frechet derivative. Directions of norm at most one
give the operator-norm bound with factor one. Only the real coefficient
is smooth on the displayed open region. -/
noncomputable section
open scoped Topology ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def directionalWordDirections {ι : Type} (dirs : ι → Space κ) :
    (w : List ι) → Fin w.length → Space κ
  | [] => Fin.elim0
  | i :: w => Fin.cons (dirs i) (directionalWordDirections dirs w)

theorem directionalWordDirections_norm_le {ι : Type} (dirs : ι → Space κ)
    (hdirs : ∀ i, ‖dirs i‖ ≤ 1) (w : List ι) (i : Fin w.length) :
    ‖directionalWordDirections dirs w i‖ ≤ 1 := by
  induction w with
  | nil => exact Fin.elim0 i
  | cons j w ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hdirs j
    · exact ih k

theorem directionalWordDeriv_eq_iteratedFDeriv {ι : Type} (dirs : ι → Space κ)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) (w : List ι) {p : Space κ} (hp : p ∈ Ω) :
    directionalWordDeriv dirs B w p =
      iteratedFDeriv ℝ w.length B p (directionalWordDirections dirs w) := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    have heq : directionalWordDeriv dirs B w =ᶠ[𝓝 p]
        (fun q => iteratedFDeriv ℝ w.length B q (directionalWordDirections dirs w)) := by
      filter_upwards [hΩ.mem_nhds hp] with q hq
      exact ih hq
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length B) p :=
      (hB.contDiffAt (hΩ.mem_nhds hp)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top w.length)
    change fderiv ℝ (directionalWordDeriv dirs B w) p (dirs i) = _
    rw [heq.fderiv_eq]
    symm
    simpa only [List.length_cons,directionalWordDirections,Fin.cons_zero,Fin.tail_cons] using
      (hd.iteratedFDeriv_succ_apply_left'
        (m := Fin.cons (dirs i) (directionalWordDirections dirs w)))

theorem directionalWordDeriv_abs_le_iteratedFDeriv {ι : Type} (dirs : ι → Space κ)
    (hdirs : ∀ i, ‖dirs i‖ ≤ 1) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    (w : List ι) {p : Space κ} (hp : p ∈ Ω) :
    |directionalWordDeriv dirs B w p| ≤ ‖iteratedFDeriv ℝ w.length B p‖ := by
  rw [directionalWordDeriv_eq_iteratedFDeriv dirs hΩ hB w hp]
  have hprod : (∏ i : Fin w.length, ‖directionalWordDirections dirs w i‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun i _ => directionalWordDirections_norm_le dirs hdirs w i)
  have hnorm := (iteratedFDeriv ℝ w.length B p).le_opNorm (directionalWordDirections dirs w)
  rw [Real.norm_eq_abs] at hnorm
  exact hnorm.trans (mul_le_of_le_one_right (norm_nonneg _) hprod)

theorem directionalWordDeriv_finite_bound {ι : Type} (dirs : ι → Space κ)
    (hdirs : ∀ i, ‖dirs i‖ ≤ 1) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {S : Set (Space κ)} (hS : S ⊆ Ω) {m : ℕ} {M : ℝ}
    (hM : ∀ k ≤ m, ∀ p ∈ S, ‖iteratedFDeriv ℝ k B p‖ ≤ M) :
    ∀ w : List ι, w.length ≤ m → ∀ p ∈ S, |directionalWordDeriv dirs B w p| ≤ M := by
  intro w hw p hp
  exact (directionalWordDeriv_abs_le_iteratedFDeriv dirs hdirs hΩ hB w (hS hp)).trans
    (hM w.length hw p hp)

end TheoremT.Continuum.WeakGrushin
