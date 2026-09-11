import LocalWeakGrushinCaccioppoli_v1
import GrushinCutoffCoefficients_v1

/-! Cutoff constants are independent of the local weak H2 input and its PDE
output. This supplies bounds uniform along actual L2-bounded solution families.
No modulus or effective computation of the automatically selected constant is claimed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem cutoff_squared_l2_bound
    {η : Space κ → ℝ} (hη : Continuous η) (hcη : HasCompactSupport η)
    (D : ℝ) (hD : ∀ p, (η p)^2 ≤ D)
    (f : Lp ℂ 2 (volume : Measure (Space κ))) :
    (∫ p, (η p)^2*‖f p‖^2) ≤ D*‖f‖^2 := by
  have hf := (Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hsq : HasCompactSupport (fun p => (η p)^2) := by
    apply hcη.mono
    intro p hp hz
    exact hp (by simp [hz])
  have hi : Integrable (fun p => (η p)^2*‖f p‖^2) := by
    simpa only [smul_eq_mul,Pi.pow_apply,Pi.mul_apply] using
      hf.locallyIntegrable.integrable_smul_left_of_hasCompactSupport (hη.pow 2) hsq
  rw [l2_norm_sq_integral,← integral_const_mul]
  exact integral_mono hi (hf.const_mul D)
    (fun p => mul_le_mul_of_nonneg_right (hD p) (sq_nonneg _))

theorem cutoff_squared_exists_bound
    {η : Space κ → ℝ} (hη : Continuous η) (hcη : HasCompactSupport η) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p, (η p)^2 ≤ D := by
  obtain ⟨D,hD⟩ := hcη.exists_bound_of_continuousOn (hη.pow 2).continuousOn
  refine ⟨max D 0,le_max_right _ _,fun p => ?_⟩
  by_cases hp : p ∈ tsupport η
  · exact (le_abs_self _).trans ((hD p hp).trans (le_max_left _ _))
  · rw [image_eq_zero_of_notMem_tsupport hp,zero_pow (by decide : 2 ≠ 0)]
    exact le_max_right _ _

theorem local_weakH2_cutoff_norm_bound (c D C : ℝ)
    {f h U : Lp ℂ 2 (volume : Measure (Space κ))} {Ω : Set (Space κ)}
    (hΩ : IsOpen Ω) (hf : ProductLocalWeakH2On (f : Space κ → ℂ) Ω)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hD : ∀ p, (η p)^2 ≤ D) (hC : ∀ p, grushinCutoffWeight c η p ≤ C)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    {a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hU : (U : Space κ → ℂ) =ᵐ[volume] (fun p => η p • f p))
    (ha : ∀ v, WeakProductL2Directional U (a v) v) :
    firstEnergy c a ≤ (D/2+C)*‖f‖^2+(D/2)*‖h‖^2 := by
  have he := local_weakH2_cutoff_caccioppoli_of_weak_jet c hΩ hf hη hcη hηΩ hP hU ha
  have hF := cutoff_squared_l2_bound hη.continuous hcη D hD f
  have hH := cutoff_squared_l2_bound hη.continuous hcη D hD h
  have hW := grushin_cutoff_energy_norm_sq_bound c C hη hcη hC f
  linarith

theorem local_weakH2_cutoff_uniform_bound (c : ℝ)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ {f h U : Lp ℂ 2 (volume : Measure (Space κ))} {Ω : Set (Space κ)},
    IsOpen Ω → ProductLocalWeakH2On (f : Space κ → ℂ) Ω → tsupport η ⊆ Ω →
    (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) →
    ∀ {a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))},
    (U : Space κ → ℂ) =ᵐ[volume] (fun p => η p • f p) →
    (∀ v, WeakProductL2Directional U (a v) v) →
    firstEnergy c a ≤ C*(‖f‖^2+‖h‖^2) := by
  obtain ⟨D,hD0,hD⟩ := cutoff_squared_exists_bound hη.continuous hcη
  obtain ⟨W,hW0,hW⟩ := grushinCutoffWeight_exists_bound c hη hcη
  refine ⟨D/2+W,by positivity,?_⟩
  intro f h U Ω hΩ hf hηΩ hP a hU ha
  have hb := local_weakH2_cutoff_norm_bound c D W hΩ hf hη hcη hηΩ hD hW hP hU ha
  nlinarith [mul_nonneg hW0 (sq_nonneg ‖h‖)]

end TheoremT.Continuum.WeakGrushin
