import LocalWeakGrushinOneStepLocalData_v1
import GrushinLocalPotentialReduction_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weak_grushin_potential_cutoff_gain {c : ℝ} (hc : 0 < c)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    ∃ K : Set (Space κ), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ Ω ∧ 0 ≤ C ∧
      ∀ (B : Space κ → ℝ) (f g : Space κ → ℂ),
        ContinuousOn B Ω → ProductLocallyL2On f Ω → ProductLocallyL2On g Ω →
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
          (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p, φ p • g p) →
        let F : ℝ := ∫ p in K, ‖f p‖^2
        let M : ℝ := ∫ p in K, ‖g p - B p • f p‖^2
        ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
          U =ᵐ[volume] (fun p => χ p • f p) ∧
          (∑ i, ‖gy i‖^2) ≤ 2*(C*F)+(3/4 : ℝ)*(C*(F+M)) ∧
          (∑ j, ‖gt j‖^2) ≤ (C*(F+M))/(16*c) ∧
          (∑ i, ∑ j, ‖hyy i j‖^2) ≤ (3/2 : ℝ)*(C*(F+M)) ∧
          (∀ i, WeakProductL2Directional U (gy i) (yDir i)) ∧
          (∀ j, WeakProductL2Directional U (gt j) (tDir j)) ∧
          ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  obtain ⟨K,C,hK,hχK,hKΩ,hC,hgain⟩ :=
    local_weak_grushin_cutoff_one_step_local_data hc hΩ hχ hcχ hχΩ
  refine ⟨K,C,hK,hχK,hKΩ,hC,?_⟩
  intro B f g hB hf hg hP
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  obtain ⟨hh,hweak⟩ := grushin_local_potential_reduction c (EuclideanSpace.basisFun κ ℝ)
    hB f g hf hg (by simpa only [hBasis] using hP)
  rw [hBasis] at hweak
  exact hgain f (fun p => g p-B p • f p) hf hh hweak

#print axioms local_weak_grushin_potential_cutoff_gain
end TheoremT.Continuum.WeakGrushin
