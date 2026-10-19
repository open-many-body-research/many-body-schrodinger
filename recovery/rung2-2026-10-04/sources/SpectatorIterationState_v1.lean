import WeakGrushinExplicitFiniteSpectatorReserve_v1
import WeakGrushinPotentialCompactConstants_v1

/-! Actual finite iteration data on a region, with an integral squared L2
budget. The Y-first and ordered YY reserve is retained for every previously
processed tangential word. All derivatives are genuine weak test identities. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def RegionL2Budget (f : Space κ → ℂ) (Ω : Set (Space κ)) (W : ℝ) : Prop :=
  MemLp f 2 (volume.restrict Ω) ∧ (∫ p in Ω, ‖f p‖^2) ≤ W

theorem RegionL2Budget.restrict {f : Space κ → ℂ} {Ω O : Set (Space κ)} {W U : ℝ}
    (hf : RegionL2Budget f Ω W) (hO : O ⊆ Ω) (hWU : W ≤ U) : RegionL2Budget f O U := by
  refine ⟨hf.1.mono_measure (Measure.restrict_mono hO le_rfl),?_⟩
  apply le_trans ?_ (hf.2.trans hWU)
  exact setIntegral_mono_set (hf.1.integrable_norm_pow (by norm_num))
    (Eventually.of_forall (fun p => sq_nonneg _)) (Eventually.of_forall hO)

theorem RegionL2Budget.local {f : Space κ → ℂ} {Ω : Set (Space κ)} {W : ℝ}
    (hf : RegionL2Budget f Ω W) : ProductLocallyL2On f Ω :=
  fun K _ hK => hf.1.mono_measure (Measure.restrict_mono hK le_rfl)

theorem regionL2Budget_of_global (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (Ω : Set (Space κ)) {W : ℝ} (hf : ‖f‖^2 ≤ W) : RegionL2Budget f Ω W :=
  ⟨(Lp.memLp f).mono_measure Measure.restrict_le_self,
    (l2_setIntegral_norm_sq_le f Ω).trans hf⟩

def LocalYDerivative (Ω : Set (Space κ)) (f g : Space κ → ℂ) (i : Fin 4) : Prop :=
  ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ p, φ p • g p) = -(∫ p, fderiv ℝ φ p (yDir i) • f p)

theorem LocalYDerivative.mono {Ω O : Set (Space κ)} {f g : Space κ → ℂ} {i : Fin 4}
    (hf : LocalYDerivative Ω f g i) (hO : O ⊆ Ω) : LocalYDerivative O f g i :=
  fun φ hφ hc hs => hf φ hφ hc (hs.trans hO)

def SpectatorFiniteState (Ω : Set (Space κ)) (f : Space κ → ℂ) (m : ℕ) (W : ℝ) : Prop :=
  ∃ G : List κ → Space κ → ℂ,
  ∃ gy : List κ → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
  ∃ hyy : List κ → Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
    G [] = f ∧
    (∀ w, w.length ≤ m → RegionL2Budget (G w) Ω W) ∧
    (∀ w j, w.length < m → LocalSpectatorD Ω (G w) (G (j :: w)) j) ∧
    ∀ w, w.length < m →
      (∑ i, ‖gy w i‖^2) ≤ W ∧ (∑ i, ∑ j, ‖hyy w i j‖^2) ≤ W ∧
      (∀ i, LocalYDerivative Ω (G w) (gy w i) i) ∧
      ∀ i j, WeakProductL2Directional (gy w i) (hyy w i j) (yDir j)

theorem spectatorFiniteState_zero {Ω : Set (Space κ)} {f : Space κ → ℂ} {W : ℝ}
    (hf : RegionL2Budget f Ω W) : SpectatorFiniteState Ω f 0 W := by
  refine ⟨(fun _ => f),(fun _ _ => 0),(fun _ _ _ => 0),rfl,?_,?_,?_⟩
  · intro w _
    exact hf
  · intro w j hw
    omega
  · intro w hw
    omega

#print axioms RegionL2Budget.restrict
#print axioms RegionL2Budget.local
#print axioms regionL2Budget_of_global
#print axioms LocalYDerivative.mono
#print axioms spectatorFiniteState_zero
end TheoremT.Continuum.WeakGrushin
