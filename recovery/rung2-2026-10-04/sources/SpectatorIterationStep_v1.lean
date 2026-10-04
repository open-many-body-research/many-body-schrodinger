import SpectatorIterationState_v1
import SpectatorFiniteFamilyExtension_v1
import SpectatorIterationBudget_v1

/-! One actual finite iteration step, including propagation of a region L2
budget and preservation of every earlier Y/YY reserve. The explicit potential
gain constructs all new top derivatives. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 1200000 in
theorem spectatorFiniteState_step
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ η : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {W : Set (Space κ)} (hW : IsOpen W) (hχW : tsupport χ ⊆ W)
    (hη1 : ∀ p ∈ W, η p = 1)
    (M A B D Q : ℝ) (hB0 : 0 ≤ B) (hD0 : 0 ≤ D) (hQ0 : 0 ≤ Q)
    (hM : ∀ p, |χ p| ≤ M)
    (hA : ∀ p ∈ tsupport χ, |combinedCutoffScalar c χ p| ≤ A)
    (hB : ∀ p ∈ tsupport χ, cutoffGradientWeight c χ p ≤ B)
    (hD : ∀ p, (η p)^2 ≤ D) (hQ : ∀ p, grushinCutoffWeight c η p ≤ Q)
    {O : Set (Space κ)} (hχ1 : ∀ p ∈ O, χ p = 1)
    {P : Space κ → ℝ} (hP : ContDiffOn ℝ ∞ P Ω)
    (m : ℕ) (f : Space κ → ℂ) (F : List κ → Space κ → ℂ) (K0 W0 H0 : ℝ)
    (hK0 : 0 ≤ K0) (hW0 : 0 ≤ W0) (hH0 : 0 ≤ H0)
    (hf : SpectatorFiniteState Ω f m W0)
    (hF : ∀ w, w.length ≤ m → RegionL2Budget (F w) Ω H0)
    (hFD : ∀ w j, w.length < m → LocalSpectatorD Ω (F w) (F (j :: w)) j)
    (hCoeff : ∀ w, w.length ≤ m → ∀ p ∈ Ω, |spectatorWordDeriv P w p| ≤ K0)
    (hEq : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis P φ p • f p) = ∫ p, φ p • F [] p) :
    SpectatorFiniteState O f (m+1)
      (spectatorIterationNext c M A B D Q K0 H0 m W0) := by
  obtain ⟨G,gy,hyy,hGeq,hG,hGD,hRes⟩ := hf
  obtain ⟨K,V,hK,hKΩ,hV,hηV,hVK,hχK,hgain⟩ :=
    weak_grushin_explicit_finite_spectator_reserve hc hΩ hχ hcχ hη hcη hηΩ
      hW hχW hη1 M A B D Q hB0 hD0 hQ0 hM hA hB hD hQ hχ1
  have hOΩ : O ⊆ Ω := by
    intro p hp
    apply hKΩ
    apply hχK
    apply subset_tsupport χ
    change χ p ≠ 0
    rw [hχ1 p hp]
    norm_num
  obtain ⟨hJ,hN,hWN,hYn,hTn,hYYn⟩ :=
    spectatorIterationBudget_bounds c M A B D Q K0 H0 m W0 hc hB0 hD0 hQ0 hK0 hH0 hW0
  let N := spectatorIterationNext c M A B D Q K0 H0 m W0
  have hnew : ∀ w : List κ,
      ∃ yn : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ tn : κ → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ yyn : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
      w.length = m →
        (∑ i, ‖yn i‖^2) ≤ N ∧ (∑ j, ‖tn j‖^2) ≤ N ∧
        (∑ i, ∑ j, ‖yyn i j‖^2) ≤ N ∧
        (∀ i, LocalYDerivative O (G w) (yn i) i) ∧
        (∀ j, LocalSpectatorD O (G w) (tn j) j) ∧
        ∀ i j, WeakProductL2Directional (yn i) (yyn i j) (yDir j) := by
    intro w
    by_cases hw : w.length = m
    · have hwm : w.length ≤ m := hw.le
      obtain ⟨yn,tn,yyn,hy,ht,hyyN,hUy,hUt,hYY⟩ := hgain P hP m G F K0 W0 H0 hK0 hW0
        (fun q hq => (hG q hq).local) (fun q hq => (hF q hq).local) hGD hFD
        (fun q hq p hp => hCoeff q hq p (hKΩ hp))
        (fun q hq => ((hG q hq).restrict hKΩ le_rfl).2)
        (fun q hq => ((hF q hq).restrict hKΩ le_rfl).2)
        (by simpa only [hGeq] using hEq) w hwm
      simp only [hw] at hy ht hyyN
      refine ⟨yn,tn,yyn,fun _ => ⟨?_,?_,?_,hUy,hUt,hYY⟩⟩
      · exact hy.trans (by simpa only [N,spectatorIterationJ,mul_assoc] using hYn)
      · exact ht.trans hTn
      · exact hyyN.trans hYYn
    · exact ⟨fun _ => 0,fun _ => 0,fun _ _ => 0,fun h => (hw h).elim⟩
  choose yn tn yyn hn using hnew
  let T := fun w j => (tn w j : Space κ → ℂ)
  let Gnext := spectatorFamilyExtend G T m
  let gyNext := fun w => if w.length < m then gy w else yn w
  let hyyNext := fun w => if w.length < m then hyy w else yyn w
  have hTG (w : List κ) (j : κ) (hw : w.length = m) :
      RegionL2Budget (T w j) O N := by
    apply regionL2Budget_of_global
    exact (Finset.single_le_sum (fun q _ => sq_nonneg ‖tn w q‖)
      (Finset.mem_univ j)).trans (hn w hw).2.1
  have hGnext (w : List κ) (hw : w.length ≤ m+1) : RegionL2Budget (Gnext w) O N := by
    by_cases hold : w.length ≤ m
    · rw [show Gnext w = G w from spectatorFamilyExtend_old G T m w hold]
      exact (hG w hold).restrict hOΩ hWN
    · cases w with
      | nil => simp at hold
      | cons j w =>
        have ht : w.length = m := by simp only [List.length_cons] at hw hold; omega
        rw [show Gnext (j :: w) = T w j from spectatorFamilyExtend_top G T m w j ht]
        exact hTG w j ht
  have hDnext := (spectatorFamilyExtend_genuine G T m
    (fun w hw => ((hG w hw).restrict hOΩ hWN).local)
    (fun w j hw => (hGD w j hw).mono hOΩ)
    (fun w j hw => (hTG w j hw).local)
    (fun w j hw => (hn w hw).2.2.2.2.1 j)).2
  refine ⟨Gnext,gyNext,hyyNext,?_,hGnext,hDnext,?_⟩
  · exact hGeq
  · intro w hw
    have hold : w.length ≤ m := by omega
    have heq : Gnext w = G w := spectatorFamilyExtend_old G T m w hold
    by_cases hlt : w.length < m
    · obtain ⟨hy,hyyN,hY,hYY⟩ := hRes w hlt
      simp only [gyNext,hyyNext,if_pos hlt,heq]
      exact ⟨hy.trans hWN,hyyN.trans hWN,fun i => (hY i).mono hOΩ,hYY⟩
    · have ht : w.length = m := by omega
      obtain ⟨hy,_ht,hyyN,hY,_hT,hYY⟩ := hn w ht
      simp only [gyNext,hyyNext,if_neg hlt,heq]
      exact ⟨hy,hyyN,hY,hYY⟩

#print axioms spectatorFiniteState_step
end TheoremT.Continuum.WeakGrushin
