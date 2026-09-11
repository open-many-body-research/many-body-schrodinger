import LocalWeakGrushinPlateauJets_v1

/-! Local weak H2 data represented near an arbitrary compact set by actual
whole-space weak H2 jets whose restricted energy is uniformly controlled by
the original solution and source. The middle plateau is chosen before the
input functions, so its constant is uniform over the solution family. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weakH2_compact_jet_energy_data {c : ℝ} (hc : 0 ≤ c)
    {K Ω : Set (Space κ)} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f h : Lp ℂ 2 (volume : Measure (Space κ))),
      ProductLocalWeakH2On (f : Space κ → ℂ) Ω →
      (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) →
      ∃ F : Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)), ∃ e : Jet κ,
      ∃ V : Set (Space κ), IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
        (∀ᵐ p ∂volume, p ∈ V → F p = f p) ∧
        (∀ v, WeakProductL2Directional F (d v) v) ∧
        (∀ v w, WeakProductL2Directional (d v) (e v w) w) ∧
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
          (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • F p) = ∫ p, φ p • h p) ∧
        ((∫ p in K, ‖F p‖^2) ≤ ‖f‖^2) ∧
        firstJetEnergyOn c K d ≤ C*(‖f‖^2+‖h‖^2) := by
  obtain ⟨η,hη,hcη,hηΩ,W,hW,hKW,hWO,hη1⟩ := exists_outer_plateau hK hΩ hKO
  obtain ⟨C,hC0,hC⟩ := local_weakH2_cutoff_uniform_bound c hη hcη
  refine ⟨C,hC0,?_⟩
  intro f h hf hP
  obtain ⟨θ,hθ,hcθ,hθΩ,V,hV,hηV,hVO,hθ1,F,d,e,hF,hd,he,hFs⟩ :=
    local_weakH2_plateau_data hΩ hf hcη.isCompact hηΩ
  have hKη : K ⊆ tsupport η := by
    intro p hp
    apply subset_closure
    change η p ≠ 0
    rw [hη1 p (hKW hp)]
    norm_num
  have hKV : K ⊆ V := hKη.trans hηV
  have hFeq : ∀ᵐ p ∂volume, p ∈ V → F p = f p := by
    filter_upwards [hF] with p hp hv
    rw [hp,hθ1 p hv,one_smul]
  have hPV := weak_output_on_plateau c hF hVO hθ1 hP
  obtain ⟨U,a,b,ha,hb,hU,hA,hB⟩ := product_compact_cutoff_weak_jet hη hcη hd he
  have hUf : (U : Space κ → ℂ) =ᵐ[volume] (fun p => η p • f p) :=
    hU.trans (plateau_cutoff_mul_ae hF hηV hθ1)
  have hEnergy := (plateau_firstJetEnergyOn_le hc hcη hK.measurableSet hW hKW hη1 hA).trans
    (hC hΩ hf hηΩ hP hUf ha)
  refine ⟨F,d,e,V,hV,hKV,hVO,hFeq,hd,he,hPV,?_,hEnergy⟩
  calc
    (∫ p in K, ‖F p‖^2) = ∫ p in K, ‖f p‖^2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hFeq,ae_restrict_mem hK.measurableSet] with p hp hm
      rw [hp (hKV hm)]
    _ ≤ ∫ p, ‖f p‖^2 := setIntegral_le_integral
      ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      (Eventually.of_forall (fun p => sq_nonneg _))
    _ = ‖f‖^2 := (l2_norm_sq_integral f).symm

#print axioms local_weakH2_compact_jet_energy_data
end TheoremT.Continuum.WeakGrushin
