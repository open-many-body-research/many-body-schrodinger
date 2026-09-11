import ContinuumFoundation_v1
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Classical compactly supported functions inhabit the ACTUAL weak Sobolev
domains already defined in ContinuumFoundation_v1. This is not a density theorem. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem classicalDerivative_to_WeakPartial {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ 1 u) (k : Coordinate N)
    (hf : MemLp u 2 volume)
    (hd : MemLp (fun x => fderiv ℝ u x (coordinateVector k)) 2 volume) :
    WeakPartial (hf.toLp u) (hd.toLp (fun x => fderiv ℝ u x (coordinateVector k))) k := by
  intro φ hφ hcφ
  have hdu : Continuous (fun x => fderiv ℝ u x (coordinateVector k)) :=
    (hu.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hdφ : Continuous (fun x => fderiv ℝ φ x (coordinateVector k)) :=
    (hφ.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hibp : (∫ x, φ x • fderiv ℝ u x (coordinateVector k)) =
      -(∫ x, fderiv ℝ φ x (coordinateVector k) • u x) := by
    apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    · exact (hdφ.smul hu.continuous).integrable_of_hasCompactSupport
        (hcφ.fderiv_apply ℝ (coordinateVector k)).smul_right
    · exact (hφ.continuous.smul hdu).integrable_of_hasCompactSupport hcφ.smul_right
    · exact (hφ.continuous.smul hu.continuous).integrable_of_hasCompactSupport hcφ.smul_right
    · intro x _
      exact hφ.differentiable (by norm_num) x
    · intro x _
      exact hu.differentiable (by norm_num) x
  calc
    (∫ x, φ x • (hd.toLp (fun x => fderiv ℝ u x (coordinateVector k))) x) =
        (∫ x, φ x • fderiv ℝ u x (coordinateVector k)) := by
      apply integral_congr_ae
      filter_upwards [hd.coeFn_toLp] with x hx
      rw [hx]
    _ = -(∫ x, fderiv ℝ φ x (coordinateVector k) • u x) := hibp
    _ = -(∫ x, fderiv ℝ φ x (coordinateVector k) • (hf.toLp u) x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]

theorem compact_c1_hasH1 {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (hf : MemLp u 2 volume) :
    HasH1 (hf.toLp u) := by
  have hdm : ∀ k : Coordinate N,
      MemLp (fun x => fderiv ℝ u x (coordinateVector k)) 2 volume := by
    intro k
    have hc : Continuous (fun x => fderiv ℝ u x (coordinateVector k)) :=
      (hu.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
    exact hc.memLp_of_hasCompactSupport (huc.fderiv_apply ℝ (coordinateVector k))
  refine ⟨fun k => (hdm k).toLp (fun x => fderiv ℝ u x (coordinateVector k)), ?_⟩
  intro k
  exact classicalDerivative_to_WeakPartial hu k hf (hdm k)

theorem compact_c2_hasH2 {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (hf : MemLp u 2 volume) :
    HasH2 (hf.toLp u) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hdc : ∀ k : Coordinate N,
      ContDiff ℝ 1 (fun x => fderiv ℝ u x (coordinateVector k)) := by
    intro k
    exact (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const
  have hdm : ∀ k : Coordinate N,
      MemLp (fun x => fderiv ℝ u x (coordinateVector k)) 2 volume := by
    intro k
    exact (hdc k).continuous.memLp_of_hasCompactSupport
      (huc.fderiv_apply ℝ (coordinateVector k))
  refine ⟨fun k => (hdm k).toLp (fun x => fderiv ℝ u x (coordinateVector k)), ?_, ?_⟩
  · intro k
    exact classicalDerivative_to_WeakPartial hu1 k hf (hdm k)
  · intro k l
    obtain ⟨e, he⟩ := compact_c1_hasH1 (hdc k)
      (huc.fderiv_apply ℝ (coordinateVector k)) (hdm k)
    exact ⟨e l, he l⟩

theorem compact_c2_in_weakH2 {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    HasH2 ((hu.continuous.memLp_of_hasCompactSupport (p := 2) huc).toLp u) :=
  compact_c2_hasH2 hu huc _

#print axioms classicalDerivative_to_WeakPartial
#print axioms compact_c1_hasH1
#print axioms compact_c2_hasH2
#print axioms compact_c2_in_weakH2
end TheoremT.Continuum
