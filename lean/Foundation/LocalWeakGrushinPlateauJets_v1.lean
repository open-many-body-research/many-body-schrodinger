import LocalWeakGrushinUniformEnergy_v1
import WeakGrushinCutoffNormEnergy_v1

/-! Exact compatibility on a plateau and restriction of actual first-jet
energy. Compact support of the cutoff first jets proves integrability of the
unbounded spectator weight before comparison with the whole-space integral. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem plateau_directional_zero
    {η : Space κ → ℝ} {V : Set (Space κ)} (hV : IsOpen V)
    (hη1 : ∀ p ∈ V, η p = 1) {p : Space κ} (hp : p ∈ V) (v : Space κ) :
    fderiv ℝ η p v = 0 := by
  have hN : ∀ᶠ q in 𝓝 p, q ∈ V := hV.mem_nhds hp
  have he : η =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := hN.mono (fun q hq => hη1 q hq)
  rw [he.fderiv_eq]
  simp only [fderiv_const_apply,ContinuousLinearMap.zero_apply]

theorem cutoff_first_jet_eq_on_plateau
    {η : Space κ → ℝ} {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {d a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    {V : Set (Space κ)} (hV : IsOpen V) (hη1 : ∀ p ∈ V, η p = 1)
    (hA : ∀ v, (a v : Space κ → ℂ) =ᵐ[volume] cutoffDirectional η f d v) :
    ∀ v, ∀ᵐ p ∂volume, p ∈ V → a v p = d v p := by
  intro v
  filter_upwards [hA v] with p hp hv
  rw [hp]
  simp only [cutoffDirectional,hη1 p hv,plateau_directional_zero hV hη1 hv v,
    one_smul,zero_smul,add_zero]

theorem cutoff_first_jet_support
    {η : Space κ → ℝ} {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {d a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hA : ∀ v, (a v : Space κ → ℂ) =ᵐ[volume] cutoffDirectional η f d v) :
    ∀ v, ∀ᵐ p ∂volume, p ∉ tsupport η → a v p = 0 := by
  intro v
  filter_upwards [hA v] with p hp ho
  rw [hp]
  simp only [cutoffDirectional,image_eq_zero_of_notMem_tsupport ho,
    fderiv_of_notMem_tsupport ℝ ho,ContinuousLinearMap.zero_apply,zero_smul,add_zero]

theorem firstJetEnergyOn_congr (c : ℝ)
    {K : Set (Space κ)} (hK : MeasurableSet K)
    {d a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (ha : ∀ v, ∀ᵐ p ∂volume, p ∈ K → d v p = a v p) :
    firstJetEnergyOn c K d = firstJetEnergyOn c K a := by
  unfold firstJetEnergyOn
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (ha (yDir i)),ae_restrict_mem hK] with p hp hm
    rw [hp hm]
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (ha (tDir j)),ae_restrict_mem hK] with p hp hm
    rw [hp hm]

theorem firstJetEnergyOn_le_firstEnergy_of_support {c : ℝ} (hc : 0 ≤ c)
    (K : Set (Space κ)) {L : Set (Space κ)} (hL : IsCompact L)
    (a : Space κ → Lp ℂ 2 (volume : Measure (Space κ)))
    (hs : ∀ v, ∀ᵐ p ∂volume, p ∉ L → a v p = 0) :
    firstJetEnergyOn c K a ≤ firstEnergy c a := by
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact setIntegral_le_integral ((Lp.memLp (a (yDir i))).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)) (Eventually.of_forall (fun p => sq_nonneg _))
  · apply mul_le_mul_of_nonneg_left _ hc
    apply Finset.sum_le_sum
    intro j _
    have hw := compact_support_weight_memLp hL (fun p : Space κ => ‖p.1‖)
      (by fun_prop) (a (tDir j)) (hs (tDir j))
    have hi : Integrable (fun p : Space κ => ‖p.1‖^2*‖a (tDir j) p‖^2) volume := by
      simpa only [norm_smul,Real.norm_eq_abs,abs_norm,mul_pow] using
        hw.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    exact setIntegral_le_integral hi
      (Eventually.of_forall (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem plateau_firstJetEnergyOn_le {c : ℝ} (hc : 0 ≤ c)
    {η : Space κ → ℝ} (hcη : HasCompactSupport η)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {d a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    {K V : Set (Space κ)} (hK : MeasurableSet K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hη1 : ∀ p ∈ V, η p = 1)
    (hA : ∀ v, (a v : Space κ → ℂ) =ᵐ[volume] cutoffDirectional η f d v) :
    firstJetEnergyOn c K d ≤ firstEnergy c a := by
  have he : firstJetEnergyOn c K d = firstJetEnergyOn c K a := by
    apply firstJetEnergyOn_congr c hK
    intro v
    filter_upwards [cutoff_first_jet_eq_on_plateau hV hη1 hA v] with p hp hm
    exact (hp (hKV hm)).symm
  rw [he]
  exact firstJetEnergyOn_le_firstEnergy_of_support hc K hcη.isCompact a
    (cutoff_first_jet_support hA)

end TheoremT.Continuum.WeakGrushin
