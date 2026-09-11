import LocalWeakGrushinPlateau_v1
import ProductCompactCutoffWeakJet_v1

/-! Exact local weak H2 energy in terms of actual derivatives of ηf, without
global weak H2 or compact-support assumptions on f. All L2 outputs are genuine
compact-test derivative witnesses. An outer plateau cutoff is constructed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def firstEnergy (c : ℝ) (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) : ℝ :=
  (∑ i : Fin 4, ∫ p, ‖d (yDir i) p‖^2) +
    c*(∑ j : κ, ∫ p, ‖p.1‖^2*‖d (tDir j) p‖^2)

theorem weak_directional_unique
    {f d e : Lp ℂ 2 (volume : Measure (Space κ))} {v : Space κ}
    (hd : WeakProductL2Directional f d v) (he : WeakProductL2Directional f e v) : d = e := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp d).locallyIntegrable (by norm_num))
    ((Lp.memLp e).locallyIntegrable (by norm_num))
  intro φ hφ hcφ
  rw [hd φ hφ hcφ,he φ hφ hcφ]

theorem firstEnergy_eq_cutoffGradient (c : ℝ)
    {η : Space κ → ℝ} {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {d a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (ha : ∀ v, (a v : Space κ → ℂ) =ᵐ[volume] cutoffDirectional η f d v) :
    firstEnergy c a = cutoffGradient c η f d := by
  unfold firstEnergy cutoffGradient
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [ha (yDir i)] with p hp
    rw [hp]
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [ha (tDir j)] with p hp
    rw [hp]

theorem plateau_cutoff_mul_ae
    {χ η : Space κ → ℝ} {f U : Lp ℂ 2 (volume : Measure (Space κ))}
    (hU : (U : Space κ → ℂ) =ᵐ[volume] (fun p => χ p • f p))
    {V : Set (Space κ)} (hηV : tsupport η ⊆ V) (hχ1 : ∀ p ∈ V, χ p = 1) :
    (fun p => η p • U p) =ᵐ[volume] (fun p => η p • f p) := by
  filter_upwards [hU] with p hp
  by_cases hz : η p = 0
  · simp only [hz,zero_smul]
  · have ht : p ∈ tsupport η := subset_closure hz
    rw [hp,hχ1 p (hηV ht),one_smul]

theorem plateau_cutoff_derivative_mul_ae
    {χ η : Space κ → ℝ} {f U : Lp ℂ 2 (volume : Measure (Space κ))}
    (hU : (U : Space κ → ℂ) =ᵐ[volume] (fun p => χ p • f p))
    {V : Set (Space κ)} (hηV : tsupport η ⊆ V) (hχ1 : ∀ p ∈ V, χ p = 1)
    (v : Space κ) :
    (fun p => fderiv ℝ η p v • U p) =ᵐ[volume] (fun p => fderiv ℝ η p v • f p) :=
  plateau_cutoff_mul_ae hU ((tsupport_fderiv_apply_subset ℝ v).trans hηV) hχ1

theorem plateau_cutoff_error_eq (c : ℝ)
    {χ η : Space κ → ℝ} {f U : Lp ℂ 2 (volume : Measure (Space κ))}
    (hU : (U : Space κ → ℂ) =ᵐ[volume] (fun p => χ p • f p))
    {V : Set (Space κ)} (hηV : tsupport η ⊆ V) (hχ1 : ∀ p ∈ V, χ p = 1) :
    grushinCutoffEnergy c η U = grushinCutoffEnergy c η f := by
  unfold grushinCutoffEnergy
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [plateau_cutoff_derivative_mul_ae hU hηV hχ1 (yDir i)] with p hp
    change ‖fderiv ℝ η p (yDir i) • U p‖^2 = ‖fderiv ℝ η p (yDir i) • f p‖^2
    rw [hp]
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [plateau_cutoff_derivative_mul_ae hU hηV hχ1 (tDir j)] with p hp
    change ‖p.1‖^2*‖fderiv ℝ η p (tDir j) • U p‖^2 = ‖p.1‖^2*‖fderiv ℝ η p (tDir j) • f p‖^2
    rw [hp]

theorem local_weakH2_cutoff_energy (c : ℝ)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))} {Ω : Set (Space κ)}
    (hΩ : IsOpen Ω) (hf : ProductLocalWeakH2On (f : Space κ → ℂ) Ω)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ a : Space κ → Lp ℂ 2 (volume : Measure (Space κ)), ∃ b : Jet κ,
      (U : Space κ → ℂ) =ᵐ[volume] (fun p => η p • f p) ∧
      (∀ v, WeakProductL2Directional U (a v) v) ∧
      (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
      (∀ᵐ p ∂volume, p ∉ tsupport η → U p = 0) ∧
      firstEnergy c a = (∫ p, inner ℝ ((η p)^2 • f p) (h p)) + grushinCutoffEnergy c η f := by
  obtain ⟨χ,hχ,hcχ,hsχ,V,hV,hηV,hVO,hχ1,F,d,e,hF,hd,he,hFs⟩ :=
    local_weakH2_plateau_data hΩ hf hcη.isCompact hηΩ
  have hPV := weak_output_on_plateau c hF hVO hχ1 hP
  have hE := compact_weakH2_cutoff_energy_local_output c hη hcη d e hd he
    hcχ.isCompact hFs hV hηV hPV
  obtain ⟨U,a,b,ha,hb,hU,hA,hB⟩ := product_compact_cutoff_weak_jet hη hcη hd he
  have hUF : (U : Space κ → ℂ) =ᵐ[volume] (fun p => η p • f p) :=
    hU.trans (plateau_cutoff_mul_ae hF hηV hχ1)
  have hPair : (∫ p, inner ℝ ((η p)^2 • F p) (h p)) = ∫ p, inner ℝ ((η p)^2 • f p) (h p) := by
    apply integral_congr_ae
    have hsquare : tsupport (fun p => (η p)^2) ⊆ V := by
      apply (tsupport_comp_subset (g := fun x : ℝ => x^2) (by simp) η).trans hηV
    filter_upwards [plateau_cutoff_mul_ae hF hsquare hχ1] with p hp
    rw [hp]
  refine ⟨U,a,b,hUF,ha,hb,?_,?_⟩
  · filter_upwards [hUF] with p hp ho
    rw [hp,image_eq_zero_of_notMem_tsupport ho,zero_smul]
  · rw [firstEnergy_eq_cutoffGradient c hA,hE,hPair,plateau_cutoff_error_eq c hF hηV hχ1]

end TheoremT.Continuum.WeakGrushin
