import WeakGrushinFiniteSpectatorReserve_v1
import SpectatorWordEquationSourceL2Bound_v1
import LocalWeakGrushinExplicitPotentialOneStep_v1

/-! Explicit finite spectator reserve from common integral solution/source
budgets and a common coefficient-derivative bound on the geometry-selected
compact set. Geometry and cutoff constants precede potential and data.
The derivative witnesses are those of the genuine raw weak solution. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 1000000 in
theorem weak_grushin_explicit_finite_spectator_reserve
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
    {O : Set (Space κ)} (hχ1 : ∀ p ∈ O, χ p = 1) :
    ∃ K V : Set (Space κ),
      IsCompact K ∧ K ⊆ Ω ∧ IsOpen V ∧ tsupport η ⊆ V ∧ V ⊆ K ∧ tsupport χ ⊆ K ∧
      ∀ (P : Space κ → ℝ), ContDiffOn ℝ ∞ P Ω →
      ∀ (m : ℕ) (G F : List κ → Space κ → ℂ) (K0 W0 H0 : ℝ),
        0 ≤ K0 → 0 ≤ W0 →
        (∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω) →
        (∀ w, w.length ≤ m → ProductLocallyL2On (F w) Ω) →
        (∀ w j, w.length < m → LocalSpectatorD Ω (G w) (G (j :: w)) j) →
        (∀ w j, w.length < m → LocalSpectatorD Ω (F w) (F (j :: w)) j) →
        (∀ w, w.length ≤ m → ∀ p ∈ K, |spectatorWordDeriv P w p| ≤ K0) →
        (∀ w, w.length ≤ m → (∫ p in K, ‖G w p‖^2) ≤ W0) →
        (∀ w, w.length ≤ m → (∫ p in K, ‖F w p‖^2) ≤ H0) →
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
          (∫ p, splitGrushin c oscillatorBasis P φ p • G [] p) = ∫ p, φ p • F [] p) →
        ∀ w, w.length ≤ m →
          let C0 : ℝ := 4*A^2+16*B*(D/2+Q)
          let C1 : ℝ := 2*M^2+8*B*D
          let J : ℝ := (C0+2*C1*K0^2)*W0 +
            2*C1*(2*H0+2*(((2^w.length-1 : ℕ) : ℝ)^2)*K0^2*W0)
          ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
          ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
          ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
            (∑ i, ‖gy i‖^2) ≤ 2*(M^2*W0)+(3/4 : ℝ)*J ∧
            (∑ j, ‖gt j‖^2) ≤ J/(16*c) ∧
            (∑ i, ∑ j, ‖hyy i j‖^2) ≤ (3/2 : ℝ)*J ∧
            (∀ i, ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
              (∫ p, φ p • gy i p) = -(∫ p, fderiv ℝ φ p (yDir i) • G w p)) ∧
            (∀ j, LocalSpectatorD O (G w) (gt j) j) ∧
            ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  obtain ⟨K,V,hK,hKΩ,hV,hηV,hVK,hχK,hgain⟩ :=
    local_weak_grushin_explicit_potential_one_step hc hΩ hχ hcχ hη hcη hηΩ
      hW hχW hη1 M A B D Q hB0 hD0 hQ0 hM hA hB hD hQ
  refine ⟨K,V,hK,hKΩ,hV,hηV,hVK,hχK,?_⟩
  intro P hP m G F K0 W0 H0 hK0 hW0 hG hF hGD hFD hCoeff hGB hFB hEq w hw
  have he := weak_grushin_finite_spectator_equations c hΩ hP m G F hG hF hGD hFD hEq w hw
  have hP0 : ∀ p ∈ K, |P p| ≤ K0 := by
    intro p hp
    exact hCoeff [] (by simp) p hp
  have hcoeff : ∀ ab ∈ spectatorWordProperSplits w, ∀ p ∈ K,
      |spectatorWordDeriv P ab.1 p| ≤ K0 := by
    intro ab hab p hp
    have hn := spectatorWordProperSplits_strict hab
    exact hCoeff ab.1 (by omega) p hp
  have hbudget : ∀ ab ∈ spectatorWordProperSplits w,
      (∫ p in K, ‖G ab.2 p‖^2) ≤ W0 := by
    intro ab hab
    have hn := spectatorWordProperSplits_strict hab
    exact hGB ab.2 (by omega)
  have hs := spectatorWordEquationSource_L2_bound hΩ hP G hG (hF w hw)
    hK hKΩ w hw hK0 hW0 hcoeff hbudget (hFB w hw)
  obtain ⟨U,gy,gt,hyy,hU,_hUn,hy,ht,hyyn,hUy,hUt,hYY⟩ := hgain P (G w)
    (fun p => F w p - spectatorWordCommutator P G w p) K0 hP.continuousOn
    (hG w hw) hs.1 hP0 (fun φ hφ hc hsφ => (he.2 φ hφ hc hsφ).2.2)
  let C0 : ℝ := 4*A^2+16*B*(D/2+Q)
  let C1 : ℝ := 2*M^2+8*B*D
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hJ : (C0+2*C1*K0^2)*(∫ p in K, ‖G w p‖^2) +
      2*C1*(∫ p in K, ‖F w p-spectatorWordCommutator P G w p‖^2) ≤
      (C0+2*C1*K0^2)*W0 +
      2*C1*(2*H0+2*(((2^w.length-1 : ℕ) : ℝ)^2)*K0^2*W0) := by
    exact add_le_add (mul_le_mul_of_nonneg_left (hGB w hw) (by positivity))
      (mul_le_mul_of_nonneg_left hs.2.2 (by positivity))
  refine ⟨gy,gt,hyy,?_,?_,?_,?_,?_,hYY⟩
  · apply hy.trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGB w hw) (sq_nonneg M))
        (by norm_num))
      (mul_le_mul_of_nonneg_left hJ (by norm_num))
  · exact ht.trans (div_le_div_of_nonneg_right hJ (by positivity))
  · exact hyyn.trans (mul_le_mul_of_nonneg_left hJ (by norm_num))
  · exact fun i => local_weak_directional_of_cutoff_weakD hU hχ1 (hUy i)
  · exact fun j => local_weak_directional_of_cutoff_weakD hU hχ1 (hUt j)

#print axioms weak_grushin_explicit_finite_spectator_reserve
end TheoremT.Continuum.WeakGrushin
