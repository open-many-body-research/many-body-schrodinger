import SpectatorWordCommutatorL2Bound_v1

/-! The actual inhomogeneous word source F minus the proper commutator is
locally L2, has an integrable squared norm on every compact interior set,
and inherits an explicit bound from integral source and lower-word budgets.
No pointwise solution bounds are used. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spectatorWordEquationSource_L2_bound
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ} (G : List κ → Space κ → ℂ)
    (hG : ∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω)
    {F : Space κ → ℂ} (hF : ProductLocallyL2On F Ω)
    {S : Set (Space κ)} (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (w : List κ) (hw : w.length ≤ m)
    {K W H : ℝ} (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hCoeff : ∀ ab ∈ spectatorWordProperSplits w, ∀ p ∈ S,
      |spectatorWordDeriv B ab.1 p| ≤ K)
    (hBudget : ∀ ab ∈ spectatorWordProperSplits w,
      (∫ p in S, ‖G ab.2 p‖^2) ≤ W)
    (hSource : (∫ p in S, ‖F p‖^2) ≤ H) :
    ProductLocallyL2On (fun p => F p - spectatorWordCommutator B G w p) Ω ∧
    Integrable (fun p => ‖F p - spectatorWordCommutator B G w p‖^2)
      (volume.restrict S) ∧
    (∫ p in S, ‖F p - spectatorWordCommutator B G w p‖^2) ≤
      2*H+2*(((2^w.length-1 : ℕ) : ℝ)^2)*K^2*W := by
  have hR : ProductLocallyL2On
      (fun p => F p - spectatorWordCommutator B G w p) Ω :=
    product_locallyL2On_sub hF (spectatorWordCommutator_locallyL2 hΩ hB G hG w hw)
  have hRsq : Integrable (fun p => ‖F p - spectatorWordCommutator B G w p‖^2)
      (volume.restrict S) := (hR S hS hSΩ).integrable_norm_pow (by norm_num)
  have hFsq : Integrable (fun p => ‖F p‖^2) (volume.restrict S) :=
    (hF S hS hSΩ).integrable_norm_pow (by norm_num)
  have hCsq := spectatorWordCommutator_integrable_norm_sq hΩ hB G hG hS hSΩ w hw
  have hCbound := spectatorWordCommutator_integral_norm_sq_le hΩ hB G hG hS hSΩ
    w hw hK hW hCoeff hBudget
  refine ⟨hR,hRsq,?_⟩
  calc
    _ ≤ ∫ p in S, 2*‖F p‖^2+2*‖spectatorWordCommutator B G w p‖^2 := by
      apply integral_mono_ae hRsq ((hFsq.const_mul 2).fun_add (hCsq.const_mul 2))
      exact Filter.Eventually.of_forall (fun p => by
        simpa only [sub_eq_add_neg,norm_neg] using
          norm_add_sq_le_twice (F p) (-spectatorWordCommutator B G w p))
    _ = 2*(∫ p in S, ‖F p‖^2)+2*(∫ p in S, ‖spectatorWordCommutator B G w p‖^2) := by
      rw [integral_add (hFsq.const_mul 2) (hCsq.const_mul 2),
        integral_const_mul,integral_const_mul]
    _ ≤ 2*H+2*((((2^w.length-1 : ℕ) : ℝ)^2)*K^2*W) :=
      add_le_add (mul_le_mul_of_nonneg_left hSource (by norm_num))
        (mul_le_mul_of_nonneg_left hCbound (by norm_num))
    _ = _ := by ring

#print axioms spectatorWordEquationSource_L2_bound
end TheoremT.Continuum.WeakGrushin
