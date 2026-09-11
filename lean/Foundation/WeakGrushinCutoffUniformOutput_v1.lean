import WeakGrushinCutoffLocalData_v1
import WeakGrushinCutoffOutputNorm_v1
import WeakGrushinCutoffNormCoefficients_v1

/-! Uniform compact cutoff output bound for local weak H2 solutions of the
actual weak Grushin equation. The constant is selected before both input
functions; all cutoff jets and the principal output are constructed from their
compact-test definitions. No input first-derivative bound is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weakH2_cutoff_uniform_output {c : ℝ} (hc : 0 ≤ c)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f h : Lp ℂ 2 (volume : Measure (Space κ))),
      ProductLocalWeakH2On (f : Space κ → ℂ) Ω →
      (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) →
      ∃ U H : Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ a : Space κ → Lp ℂ 2 (volume : Measure (Space κ)), ∃ b : Jet κ,
        U =ᵐ[volume] (fun p => χ p • f p) ∧
        (∀ v, WeakProductL2Directional U (a v) v) ∧
        (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
        (∀ᵐ p ∂volume, p ∉ tsupport χ → U p = 0) ∧
        H =ᵐ[volume] principal c b ∧
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) = ∫ p, φ p • H p) ∧
        ‖U‖^2 ≤ C*‖f‖^2 ∧ ‖H‖^2 ≤ C*(‖f‖^2+‖h‖^2) := by
  obtain ⟨M₀,hM₀⟩ := hcχ.exists_bound_of_continuousOn hχ.continuous.continuousOn
  let M := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ p, |χ p| ≤ M := by
    intro p
    by_cases hp : p ∈ tsupport χ
    · exact (hM₀ p hp).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hp,abs_zero]
      exact hM0
  have hM2 : ∀ p, (χ p)^2 ≤ M^2 := by
    intro p
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hM p) 2
  obtain ⟨A,B,hA0,hB0,hA,hB⟩ := weak_cutoff_coefficient_bounds c hχ hcχ
  obtain ⟨E,hE0,hE⟩ := local_weakH2_compact_jet_energy_data hc hcχ.isCompact hΩ hχΩ
  let C := 3*M^2+4*A^2+16*B*E
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hMC : M^2 ≤ C := by dsimp [C]; nlinarith [mul_nonneg hB0 hE0]
  refine ⟨C,hC0,?_⟩
  intro f h hf hP
  obtain ⟨F,d,e,V,hV,hKV,hVO,hFeq,hd,he,hPV,hFn,hEn⟩ := hE f h hf hP
  obtain ⟨U,H,a,b,ha,hb,hU,hUs,hHb,hHformula,hTests,hHn⟩ :=
    compact_cutoff_weak_grushin_local_output_norm_sq hc hχ hcχ hd he hV hKV hPV
      hcχ.isCompact (Set.Subset.refl _) M A B hM (fun p _ => hA p) (fun p _ => hB p)
  have hUf : U =ᵐ[volume] (fun p => χ p • f p) := by
    filter_upwards [hU,hFeq] with p hp heq
    rw [hp]
    by_cases ht : p ∈ tsupport χ
    · rw [heq (hKV ht)]
    · simp only [image_eq_zero_of_notMem_tsupport ht,zero_smul]
  have hUn : ‖U‖^2 ≤ M^2*‖f‖^2 := by
    have hnorm : ‖U‖^2 = ∫ p, ‖χ p • f p‖^2 := by
      rw [l2_norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [hUf] with p hp
      rw [hp]
    rw [hnorm]
    simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using
      cutoff_squared_l2_bound hχ.continuous hcχ (M^2) hM2 f
  refine ⟨U,H,a,b,hUf,ha,hb,hUs,hHb,hTests,
    hUn.trans (mul_le_mul_of_nonneg_right hMC (sq_nonneg _)),?_⟩
  have hFbound := mul_le_mul_of_nonneg_left hFn (by positivity : 0 ≤ 4*A^2)
  have hEbound := mul_le_mul_of_nonneg_left hEn (by positivity : 0 ≤ 16*B)
  have hp1 := mul_nonneg (sq_nonneg M) (sq_nonneg ‖f‖)
  have hp2 := mul_nonneg (sq_nonneg A) (sq_nonneg ‖h‖)
  have hp3 := mul_nonneg (sq_nonneg M) (sq_nonneg ‖h‖)
  dsimp [C]
  nlinarith

#print axioms local_weakH2_cutoff_uniform_output
end TheoremT.Continuum.WeakGrushin
