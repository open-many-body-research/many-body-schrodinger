import SpectatorWordProduct_v1
import LocalSpectatorDerivativeAlgebra_v1
import ProductLocalWeakDirectionalLeibniz_v1

/-! Finite ordered Leibniz identities for genuine local weak derivative
families.  Only derivative words within the stated finite order are assumed.
The coefficient is an actual smooth real function. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spectatorWordProduct_locallyL2
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ} (G : List κ → Space κ → ℂ)
    (hG : ∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω)
    (w : List κ) (hw : w.length ≤ m) :
    ProductLocallyL2On (spectatorWordProduct B G w) Ω := by
  apply productLocallyL2On_list_sum
  intro ab hab
  have hn := spectatorWordSplits_length_sum hab
  exact product_smooth_coefficient_locallyL2_raw hΩ
    (spectatorWordDeriv_contDiffOn hΩ hB ab.1) (hG ab.2 (by omega))

theorem spectatorWordCommutator_locallyL2
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ} (G : List κ → Space κ → ℂ)
    (hG : ∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω)
    (w : List κ) (hw : w.length ≤ m) :
    ProductLocallyL2On (spectatorWordCommutator B G w) Ω := by
  apply productLocallyL2On_list_sum
  intro ab hab
  have hn := spectatorWordProperSplits_strict hab
  exact product_smooth_coefficient_locallyL2_raw hΩ
    (spectatorWordDeriv_contDiffOn hΩ hB ab.1) (hG ab.2 (by omega))

theorem spectatorWordProduct_localD
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ} (G : List κ → Space κ → ℂ)
    (hG : ∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω)
    (hD : ∀ w j, w.length < m → LocalSpectatorD Ω (G w) (G (j :: w)) j)
    (w : List κ) (j : κ) (hw : w.length < m) :
    LocalSpectatorD Ω (spectatorWordProduct B G w)
      (spectatorWordProduct B G (j :: w)) j := by
  let f := fun ab : List κ × List κ => fun p : Space κ =>
    spectatorWordDeriv B ab.1 p • G ab.2 p
  let a := fun ab : List κ × List κ => fun p : Space κ =>
    spectatorWordDeriv B ab.1 p • G (j :: ab.2) p +
      fderiv ℝ (spectatorWordDeriv B ab.1) p (tDir j) • G ab.2 p
  have hL (ab : List κ × List κ) (hab : ab ∈ spectatorWordSplits w) := by
    have hn := spectatorWordSplits_length_sum hab
    have hb : ab.2.length < m := by omega
    exact product_local_weak_directional_leibniz hΩ
      (spectatorWordDeriv_contDiffOn hΩ hB ab.1)
      (hG ab.2 (by omega)) (hG (j :: ab.2) (by simp only [List.length_cons]; omega))
      (hD ab.2 j hb)
  have hs := LocalSpectatorD.list_sum (spectatorWordSplits w) f a
    (fun ab hab => (hL ab hab).1)
    (fun ab hab => (hL ab hab).2.1)
    (fun ab hab φ hφ hc hφΩ => ((hL ab hab).2.2 φ hφ hc hφΩ).2.2)
  have he : (fun p => ((spectatorWordSplits w).map (fun ab => a ab p)).sum) =
      spectatorWordProduct B G (j :: w) := by
    funext p
    rw [spectatorWordProduct_cons]
    simp only [a, add_comm]
  rw [he] at hs
  exact hs

#print axioms spectatorWordProduct_locallyL2
#print axioms spectatorWordCommutator_locallyL2
#print axioms spectatorWordProduct_localD
end TheoremT.Continuum.WeakGrushin
