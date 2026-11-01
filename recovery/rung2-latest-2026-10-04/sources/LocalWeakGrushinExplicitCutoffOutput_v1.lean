import LocalWeakGrushinExplicitEnergyData_v1
import WeakGrushinCutoffOutputNorm_v1

/-! Actual local weak H2 cutoff output with fully exposed cutoff coefficients.
For supplied inner chi and middle eta, the source coefficients are
4A²+16B(D/2+Q) and 2M²+8BD. Auxiliary plateau choices do not enter them. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weakH2_explicit_cutoff_output {c : ℝ} (hc : 0 ≤ c)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ η : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {W : Set (Space κ)} (hW : IsOpen W) (hχW : tsupport χ ⊆ W)
    (hη1 : ∀ p ∈ W, η p = 1)
    (M A B D Q : ℝ) (hB0 : 0 ≤ B)
    (hM : ∀ p, |χ p| ≤ M)
    (hA : ∀ p ∈ tsupport χ, |combinedCutoffScalar c χ p| ≤ A)
    (hB : ∀ p ∈ tsupport χ, cutoffGradientWeight c χ p ≤ B)
    (hD : ∀ p, (η p)^2 ≤ D) (hQ : ∀ p, grushinCutoffWeight c η p ≤ Q)
    (f h : Lp ℂ 2 (volume : Measure (Space κ)))
    (hf : ProductLocalWeakH2On (f : Space κ → ℂ) Ω)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    ∃ U H : Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ a : Space κ → Lp ℂ 2 (volume : Measure (Space κ)), ∃ b : Jet κ,
      U =ᵐ[volume] (fun p => χ p • f p) ∧
      (∀ v, WeakProductL2Directional U (a v) v) ∧
      (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
      (∀ᵐ p ∂volume, p ∉ tsupport χ → U p = 0) ∧
      H =ᵐ[volume] principal c b ∧
      (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) = ∫ p, φ p • H p) ∧
      ‖U‖^2 ≤ M^2*‖f‖^2 ∧
      ‖H‖^2 ≤ (4*A^2+16*B*(D/2+Q))*‖f‖^2+(2*M^2+8*B*D)*‖h‖^2 := by
  obtain ⟨F,d,e,V,hV,hχV,hVO,hFeq,hd,he,hPV,hFn,hEn⟩ :=
    local_weakH2_explicit_compact_jet_energy_data hc hcχ.isCompact hΩ hη hcη hηΩ
      hW hχW hη1 D Q hD hQ f h hf hP
  obtain ⟨U,H,a,b,ha,hb,hU,hUs,hHb,hHformula,hTests,hHn⟩ :=
    compact_cutoff_weak_grushin_local_output_norm_sq hc hχ hcχ hd he hV hχV hPV
      hcχ.isCompact (Set.Subset.refl _) M A B hM hA hB
  have hUf : U =ᵐ[volume] (fun p => χ p • f p) := by
    filter_upwards [hU,hFeq] with p hp heq
    rw [hp]
    by_cases ht : p ∈ tsupport χ
    · rw [heq (hχV ht)]
    · simp only [image_eq_zero_of_notMem_tsupport ht,zero_smul]
  have hUn : ‖U‖^2 ≤ M^2*‖f‖^2 := by
    have hnorm : ‖U‖^2 = ∫ p, ‖χ p • f p‖^2 := by
      rw [l2_norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [hUf] with p hp
      rw [hp]
    have hM2 : ∀ p, (χ p)^2 ≤ M^2 := by
      intro p
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hM p) 2
    rw [hnorm]
    simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using
      cutoff_squared_l2_bound hχ.continuous hcχ (M^2) hM2 f
  refine ⟨U,H,a,b,hUf,ha,hb,hUs,hHb,hTests,hUn,?_⟩
  have hFbound := mul_le_mul_of_nonneg_left hFn (by positivity : 0 ≤ 4*A^2)
  have hEbound := mul_le_mul_of_nonneg_left hEn (by positivity : 0 ≤ 16*B)
  nlinarith

#print axioms local_weakH2_explicit_cutoff_output
end TheoremT.Continuum.WeakGrushin
