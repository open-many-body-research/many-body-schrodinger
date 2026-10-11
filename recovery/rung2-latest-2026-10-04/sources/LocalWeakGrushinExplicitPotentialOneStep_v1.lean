import LocalWeakGrushinExplicitOneStepLocalData_v1
import GrushinLocalPotentialReduction_v1
import WeakGrushinPotentialForcingPointwise_v1

/-! The inhomogeneous explicit local gain needed by the normalized KS difference.
The actual potential is moved to the right side only after local integrability
is established. Both input and source norms retain displayed coefficients. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem potential_reduction_integral_norm_sq_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (P : α → ℝ) (f g : α → ℂ)
    (hP : MemLp P ⊤ μ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {b : ℝ} (hb : ∀ᵐ p ∂μ, |P p| ≤ b) :
    (∫ p, ‖g p-P p • f p‖^2 ∂μ) ≤
      2*(∫ p, ‖g p‖^2 ∂μ)+2*b^2*(∫ p, ‖f p‖^2 ∂μ) := by
  have hi := (hg.sub (hf.smul hP)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hf2 := hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hg2 := hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  calc
    _ ≤ ∫ p, 2*‖g p‖^2+2*b^2*‖f p‖^2 ∂μ := by
      apply integral_mono_ae hi ((hg2.const_mul 2).add (hf2.const_mul (2*b^2)))
      filter_upwards [hb] with p hp
      have ht := norm_add_sq_le_twice (g p) (-(P p • f p))
      have hm := potential_smul_norm_sq_le (f p) hp
      simp only [norm_neg] at ht
      change ‖g p + -(P p • f p)‖^2 ≤ 2*‖g p‖^2+2*b^2*‖f p‖^2
      nlinarith
    _ = _ := by
      rw [integral_add (hg2.const_mul 2) (hf2.const_mul (2*b^2)),
        integral_const_mul,integral_const_mul]

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weak_grushin_explicit_potential_one_step {c : ℝ} (hc : 0 < c)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {χ η : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {W : Set (Space κ)} (hW : IsOpen W) (hχW : tsupport χ ⊆ W)
    (hη1 : ∀ p ∈ W, η p = 1)
    (M A B D Q : ℝ) (hB0 : 0 ≤ B) (hD0 : 0 ≤ D) (hQ0 : 0 ≤ Q)
    (hM : ∀ p, |χ p| ≤ M)
    (hA : ∀ p ∈ tsupport χ, |combinedCutoffScalar c χ p| ≤ A)
    (hB : ∀ p ∈ tsupport χ, cutoffGradientWeight c χ p ≤ B)
    (hD : ∀ p, (η p)^2 ≤ D) (hQ : ∀ p, grushinCutoffWeight c η p ≤ Q) :
    ∃ K V : Set (Space κ),
      IsCompact K ∧ K ⊆ Ω ∧ IsOpen V ∧ tsupport η ⊆ V ∧ V ⊆ K ∧ tsupport χ ⊆ K ∧
      ∀ (P : Space κ → ℝ) (rawG source : Space κ → ℂ) (b : ℝ),
        ContinuousOn P Ω → ProductLocallyL2On rawG Ω → ProductLocallyL2On source Ω →
        (∀ p ∈ K, |P p| ≤ b) →
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
          (∫ p, splitGrushin c oscillatorBasis P φ p • rawG p) = ∫ p, φ p • source p) →
        let F : ℝ := ∫ p in K, ‖rawG p‖^2
        let S : ℝ := ∫ p in K, ‖source p‖^2
        let C0 : ℝ := 4*A^2+16*B*(D/2+Q)
        let C1 : ℝ := 2*M^2+8*B*D
        let J : ℝ := (C0+2*C1*b^2)*F+2*C1*S
        ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
        ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
          U =ᵐ[volume] (fun p => χ p • rawG p) ∧ ‖U‖^2 ≤ M^2*F ∧
          (∑ i, ‖gy i‖^2) ≤ 2*(M^2*F)+(3/4 : ℝ)*J ∧
          (∑ j, ‖gt j‖^2) ≤ J/(16*c) ∧
          (∑ i, ∑ j, ‖hyy i j‖^2) ≤ (3/2 : ℝ)*J ∧
          (∀ i, WeakProductL2Directional U (gy i) (yDir i)) ∧
          (∀ j, WeakProductL2Directional U (gt j) (tDir j)) ∧
          ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  obtain ⟨K,V,hK,hKΩ,hV,hηV,hVK,hχK,hgain⟩ :=
    local_weak_grushin_explicit_one_step_local_data hc hΩ hχ hcχ hη hcη hηΩ
      hW hχW hη1 M A B D Q hB0 hD0 hQ0 hM hA hB hD hQ
  refine ⟨K,V,hK,hKΩ,hV,hηV,hVK,hχK,?_⟩
  intro P rawG source b hP hG hsource hb hEq
  dsimp only
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  obtain ⟨hh,hweak⟩ := grushin_local_potential_reduction c (EuclideanSpace.basisFun κ ℝ)
    hP rawG source hG hsource (by simpa only [hBasis] using hEq)
  rw [hBasis] at hweak
  obtain ⟨U,gy,gt,hyy,hU,hUn,hY,hT,hYY,hgy,hgt,hhyy⟩ :=
    hgain rawG (fun p => source p-P p • rawG p) hG hh hweak
  have hforce := potential_reduction_integral_norm_sq_le P rawG source
    (product_continuousOn_memLp_top_restrict hP hK hKΩ) (hG K hK hKΩ)
    (hsource K hK hKΩ) (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      exact hb p hp)
  let F : ℝ := ∫ p in K, ‖rawG p‖^2
  let S : ℝ := ∫ p in K, ‖source p‖^2
  let C0 : ℝ := 4*A^2+16*B*(D/2+Q)
  let C1 : ℝ := 2*M^2+8*B*D
  let J : ℝ := C0*F+C1*(∫ p in K, ‖source p-P p • rawG p‖^2)
  let J' : ℝ := (C0+2*C1*b^2)*F+2*C1*S
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hJ : J ≤ J' := by
    dsimp [J,J']
    calc
      _ ≤ C0*F+C1*(2*S+2*b^2*F) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hforce hC1)
      _ = _ := by ring
  refine ⟨U,gy,gt,hyy,hU,hUn,?_,?_,?_,hgy,hgt,hhyy⟩
  · exact hY.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hJ (by norm_num : (0 : ℝ) ≤ 3/4)))
  · exact hT.trans (div_le_div_of_nonneg_right hJ (by positivity))
  · exact hYY.trans (mul_le_mul_of_nonneg_left hJ (by norm_num : (0 : ℝ) ≤ 3/2))

#print axioms potential_reduction_integral_norm_sq_le
#print axioms local_weak_grushin_explicit_potential_one_step
end TheoremT.Continuum.WeakGrushin
