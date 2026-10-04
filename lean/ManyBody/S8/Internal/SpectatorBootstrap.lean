import WeakGrushinPotentialDerivative_v1
import WeakGrushinSpectatorDifferentiateLp_v1
import LocalWeakGrushinPotentialGain_v1

/-!
First spectator bootstrap for an actual local homogeneous Grushin equation.

The input is one genuine first spectator weak derivative of a global L2
representative, together with its homogeneous equation on an open region.
The differentiated equation and local L2 source are proved from the frozen
Leibniz and commutation theorems. Applying the existing local gain to that
derivative yields Y, T, and ordered YY derivatives of its inner cutoff.

The quantitative budget below is the full principal forcing norm
`‖-(D_T B) U - B d‖²`, not just the differentiated source norm. No second
derivative is assumed, and no joint H2, H12, or analyticity is asserted.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem weak_grushin_homogeneous_spectator_equation
    (c : ℝ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {U d : Lp ℂ 2 (volume : Measure (Space κ))} (j : κ)
    (hD : WeakProductL2Directional U d (tDir j))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0) :
    ProductLocallyL2On (fun p => -(fderiv ℝ B p (tDir j) • U p)) Ω ∧
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • d p) =
        ∫ p, φ p • -(fderiv ℝ B p (tDir j) • U p) := by
  have hUl : ProductLocallyL2On (U : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp U).mono_measure Measure.restrict_le_self
  have hdl : ProductLocallyL2On (d : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp d).mono_measure Measure.restrict_le_self
  have hsource : ProductLocallyL2On
      (fun p => -(fderiv ℝ B p (tDir j) • U p)) Ω := by
    intro K hK hKΩ
    have hmD := (smooth_coefficient_and_directional_memLp_top_restrict_compact
      (μ := volume) hΩ hK hKΩ hB (tDir j)).2
    exact (((Lp.memLp U).mono_measure Measure.restrict_le_self).smul hmD).neg
  obtain ⟨hBU, hleibL2, hleib⟩ :=
    weakProduct_spectator_local_potential_leibniz hD hΩ hB
  have hnegBU : ProductLocallyL2On (fun p => -(B p • U p)) Ω :=
    fun K hK hKΩ => (hBU K hK hKΩ).neg
  have hnegLeib : ProductLocallyL2On
      (fun p => -(B p • d p + fderiv ℝ B p (tDir j) • U p)) Ω :=
    fun K hK hKΩ => (hleibL2 K hK hKΩ).neg
  have hzero : ProductLocallyL2On (fun _ : Space κ => (0 : ℂ)) Ω :=
    fun _ _ _ => MemLp.zero
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) =
      oscillatorBasis := by
    funext k
    exact EuclideanSpace.basisFun_apply κ ℝ k
  have hP0 : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) =
        ∫ p, φ p • -(B p • U p) := by
    have hz : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ p, splitGrushin c (EuclideanSpace.basisFun κ ℝ) B φ p • U p) =
          ∫ p, φ p • (0 : ℂ) := by
      intro φ hφ hcφ hsφ
      simpa only [hBasis, smul_zero, integral_zero] using hP φ hφ hcφ hsφ
    simpa only [hBasis, zero_sub] using
      (grushin_local_potential_reduction_iff c (EuclideanSpace.basisFun κ ℝ)
        hB.continuousOn U (fun _ => 0) hUl hzero).mp hz
  have hhD : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • -(B p • d p + fderiv ℝ B p (tDir j) • U p)) =
        -(∫ p, fderiv ℝ φ p (tDir j) • -(B p • U p)) := by
    intro φ hφ hcφ hsφ
    simpa only [tDir, smul_neg, integral_neg, neg_neg] using
      congrArg Neg.neg (hleib φ hφ hcφ hsφ).2.2
  have hdiff := weak_grushin_spectator_differentiate c
    (fun p => -(B p • U p))
    (fun p => -(B p • d p + fderiv ℝ B p (tDir j) • U p))
    hnegBU hnegLeib (oscillatorBasis j) hD hP0 hhD
  refine ⟨hsource, ?_⟩
  intro φ hφ hcφ hsφ
  have hiff := grushin_local_potential_test_iff c (EuclideanSpace.basisFun κ ℝ)
    hB.continuousOn d (fun p => -(fderiv ℝ B p (tDir j) • U p))
    hdl hsource hφ hcφ hsφ
  rw [hBasis] at hiff
  apply hiff.mpr
  convert hdiff φ hφ hcφ hsφ using 1
  congr 1
  funext p
  rw [neg_add, sub_eq_add_neg, add_comm]

theorem local_weak_grushin_spectator_cutoff_gain
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    ∃ K : Set (Space κ), ∃ C : ℝ,
      IsCompact K ∧ tsupport χ ⊆ K ∧ K ⊆ Ω ∧ 0 ≤ C ∧
      ∀ (B : Space κ → ℝ) (U d : Lp ℂ 2 (volume : Measure (Space κ))) (j : κ),
        ContDiffOn ℝ ∞ B Ω → WeakProductL2Directional U d (tDir j) →
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
          (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0) →
        let F : ℝ := ∫ p in K, ‖d p‖ ^ 2
        let M : ℝ := ∫ p in K, ‖-(fderiv ℝ B p (tDir j) • U p) - B p • d p‖ ^ 2
        ∃ W : Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
          W =ᵐ[volume] (fun p => χ p • d p) ∧
          (∑ i, ‖gy i‖ ^ 2) ≤ 2 * (C * F) + (3 / 4 : ℝ) * (C * (F + M)) ∧
          (∑ k, ‖gt k‖ ^ 2) ≤ (C * (F + M)) / (16 * c) ∧
          (∑ i, ∑ k, ‖hyy i k‖ ^ 2) ≤ (3 / 2 : ℝ) * (C * (F + M)) ∧
          (∀ i, WeakProductL2Directional W (gy i) (yDir i)) ∧
          (∀ k, WeakProductL2Directional W (gt k) (tDir k)) ∧
          ∀ i k, WeakProductL2Directional (gy i) (hyy i k) (yDir k) := by
  obtain ⟨K, C, hK, hχK, hKΩ, hC, hgain⟩ :=
    local_weak_grushin_potential_cutoff_gain hc hΩ hχ hcχ hχΩ
  refine ⟨K, C, hK, hχK, hKΩ, hC, ?_⟩
  intro B U d j hB hD hP
  obtain ⟨hsource, hdiff⟩ :=
    weak_grushin_homogeneous_spectator_equation c hΩ hB j hD hP
  have hdl : ProductLocallyL2On (d : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp d).mono_measure Measure.restrict_le_self
  exact hgain B d (fun p => -(fderiv ℝ B p (tDir j) • U p))
    hB.continuousOn hdl hsource hdiff

#print axioms weak_grushin_homogeneous_spectator_equation
#print axioms local_weak_grushin_spectator_cutoff_gain

end ManyBody.S8


