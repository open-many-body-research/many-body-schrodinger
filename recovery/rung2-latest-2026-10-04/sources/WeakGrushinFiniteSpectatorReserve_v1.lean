import WeakGrushinFiniteSpectatorEquation_v1
import LocalWeakGrushinPotentialGain_v1

/-! The anisotropic reserve produced at each finite spectator stage.  In
particular the Y-first derivatives at spectator order eleven are retained;
they must not be lost in an even-Y-only H12 initialization. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weak_directional_of_cutoff_weakD
    {f : Space κ → ℂ} {χ : Space κ → ℝ}
    {U d : Lp ℂ 2 (volume : Measure (Space κ))}
    (hU : (U : Space κ → ℂ) =ᵐ[volume] (fun p => χ p • f p))
    {V : Set (Space κ)} (hχ1 : ∀ p ∈ V, χ p = 1)
    {v : Space κ} (hD : WeakProductL2Directional U d v) :
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, φ p • d p) = -(∫ p, fderiv ℝ φ p v • f p) := by
  intro φ hφ hc hs
  rw [hD φ hφ hc]
  apply congrArg Neg.neg
  apply integral_congr_ae
  filter_upwards [hU] with p hp
  by_cases hmem : p ∈ tsupport φ
  · rw [hp,hχ1 p (hs hmem),one_smul]
  · simp only [fderiv_of_notMem_tsupport ℝ hmem,
      ContinuousLinearMap.zero_apply,zero_smul]

set_option maxHeartbeats 800000 in
theorem weak_grushin_finite_spectator_reserve
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) {V : Set (Space κ)} (hχ1 : ∀ p ∈ V, χ p = 1) :
    ∃ K : Set (Space κ), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ Ω ∧ 0 ≤ C ∧
      ∀ (B : Space κ → ℝ), ContDiffOn ℝ ∞ B Ω →
      ∀ (m : ℕ) (G F : List κ → Space κ → ℂ),
        (∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω) →
        (∀ w, w.length ≤ m → ProductLocallyL2On (F w) Ω) →
        (∀ w j, w.length < m → LocalSpectatorD Ω (G w) (G (j :: w)) j) →
        (∀ w j, w.length < m → LocalSpectatorD Ω (F w) (F (j :: w)) j) →
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
          (∫ p, splitGrushin c oscillatorBasis B φ p • G [] p) = ∫ p, φ p • F [] p) →
        ∀ w, w.length ≤ m →
          let W := ∫ p in K, ‖G w p‖^2
          let M := ∫ p in K, ‖F w p - spectatorWordProduct B G w p‖^2
          ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
          ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
          ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
            (∑ i, ‖gy i‖^2) ≤ 2*(C*W)+(3/4 : ℝ)*(C*(W+M)) ∧
            (∑ j, ‖gt j‖^2) ≤ (C*(W+M))/(16*c) ∧
            (∑ i, ∑ j, ‖hyy i j‖^2) ≤ (3/2 : ℝ)*(C*(W+M)) ∧
            (∀ i, ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
              (∫ p, φ p • gy i p) = -(∫ p, fderiv ℝ φ p (yDir i) • G w p)) ∧
            (∀ j, LocalSpectatorD V (G w) (gt j) j) ∧
            ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  obtain ⟨K,C,hK,hχK,hKΩ,hC,hgain⟩ :=
    local_weak_grushin_potential_cutoff_gain hc hΩ hχ hcχ hχΩ
  refine ⟨K,C,hK,hχK,hKΩ,hC,?_⟩
  intro B hB m G F hG hF hGD hFD hP w hw
  have he := weak_grushin_finite_spectator_equations c hΩ hB m G F hG hF hGD hFD hP w hw
  obtain ⟨U,gy,gt,hyy,hU,hy,ht,hyyN,hUy,hUt,hY⟩ := hgain B (G w)
    (fun p => F w p - spectatorWordCommutator B G w p) hB.continuousOn
    (hG w hw) he.1 (fun φ hφ hc hs => (he.2 φ hφ hc hs).2.2)
  refine ⟨gy,gt,hyy,?_,?_,?_,?_,?_,hY⟩
  · simpa only [spectatorWordProduct_eq_commutator_add,sub_add_eq_sub_sub] using hy
  · simpa only [spectatorWordProduct_eq_commutator_add,sub_add_eq_sub_sub] using ht
  · simpa only [spectatorWordProduct_eq_commutator_add,sub_add_eq_sub_sub] using hyyN
  · exact fun i => local_weak_directional_of_cutoff_weakD hU hχ1 (hUy i)
  · exact fun j => local_weak_directional_of_cutoff_weakD hU hχ1 (hUt j)

#print axioms local_weak_directional_of_cutoff_weakD
#print axioms weak_grushin_finite_spectator_reserve
end TheoremT.Continuum.WeakGrushin
