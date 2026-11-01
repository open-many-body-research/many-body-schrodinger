import ProductLocalDiagonalWeakH2_v1
import LocalWeakGrushinPlateau_v1
import WeakGrushinCompactCutoff_v1
import GrushinFactorialRawCommutatorL2_v1

/-! Actual compact cutoff of raw local weak data. The output formula follows
from the local PDE and uniqueness of genuine first weak derivatives. No
pointwise derivative identity or global input L2 membership is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem principal_ae_eq_of_raw_local_output (c : ℝ)
    {f : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω) (h : Space (Fin 3) → ℂ)
    (hh : ProductLocallyL2On h Ω)
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    ∀ᵐ p ∂volume, p ∈ Ω → principal c e p = h p := by
  have hpli := principal_locallyIntegrable c e
  have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hpli.locallyIntegrableOn Ω).sub (productLocallyL2On_locallyIntegrableOn hΩ hh))
    (fun φ hφ hc hs => by
      simp only [Pi.sub_apply,smul_sub]
      rw [integral_sub (hpli.integrable_smul_left_of_hasCompactSupport hφ.continuous hc)
        (product_raw_locallyL2_compact_smul_integrable hh hφ.continuous hc hs),
        principal_compact_test c d e hd he hφ hc,hP φ hφ hc hs,sub_self])
  filter_upwards [hz] with p hp hpin
  exact sub_eq_zero.mp (hp hpin)

theorem rawGrushinCutoffError_zero_off (c : ℝ) (χ : Space (Fin 3) → ℝ)
    (f : Space (Fin 3) → ℂ) (gy : Fin 4 → Space (Fin 3) → ℂ)
    (gt : Fin 3 → Space (Fin 3) → ℂ) {p : Space (Fin 3)} (hp : p ∉ tsupport χ) :
    rawGrushinCutoffError c χ f gy gt p = 0 := by
  have hD (v : Space (Fin 3)) : fderiv ℝ χ p v = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ hp]; rfl
  have hDD (v w : Space (Fin 3)) : fderiv ℝ (fun q => fderiv ℝ χ q v) p w = 0 := by
    have hz : p ∉ tsupport (fun q => fderiv ℝ χ q v) :=
      fun hh => hp ((tsupport_fderiv_apply_subset ℝ v) hh)
    rw [fderiv_of_notMem_tsupport ℝ hz]; rfl
  simp only [rawGrushinCutoffError,hD,hDD,zero_smul,smul_zero,Finset.sum_const_zero,add_zero]

theorem raw_local_weakH2_grushin_cutoff (c : ℝ)
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω) (f h : Space (Fin 3) → ℂ)
    (hf : ProductLocalWeakH2On f Ω) (hh : ProductLocallyL2On h Ω)
    (gy : Fin 4 → Space (Fin 3) → ℂ) (gt : Fin 3 → Space (Fin 3) → ℂ)
    (hy : ∀ i, ProductLocalWeakDirectional Ω f (gy i) (yDir i))
    (ht : ∀ j, ProductLocalWeakDirectional Ω f (gt j) (tDir j))
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    ∃ U H : Lp ℂ 2 (volume : Measure (Space (Fin 3))),
    ∃ a : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))), ∃ b : Jet (Fin 3),
      U =ᵐ[volume] (fun p => χ p • f p) ∧
      (∀ v, WeakProductL2Directional U (a v) v) ∧
      (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
      (∀ᵐ p ∂volume, p ∉ tsupport χ → U p = 0) ∧
      H =ᵐ[volume] principal c b ∧
      H =ᵐ[volume] (fun p => χ p • h p - rawGrushinCutoffError c χ f gy gt p) ∧
      (∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) = ∫ p, φ p • H p) := by
  obtain ⟨ψ,hψ,hcψ,hsψ,V,hV,hχV,hVO,hψ1⟩ := exists_outer_plateau hcχ.isCompact hΩ hsχ
  obtain ⟨F,d,hF,hd,hdd⟩ := hf ψ hψ hcψ hsψ
  choose e he using hdd
  have hFv : ∀ᵐ p ∂volume, p ∈ V → F p = f p := by
    filter_upwards [hF] with p hp hv
    rw [hp,hψ1 p hv,one_smul]
  have hPF : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • F p) = ∫ p, φ p • h p := by
    intro φ hφ hc hs
    calc
      _ = ∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p := by
        apply integral_congr_ae
        filter_upwards [hFv] with p hp
        by_cases hpin : p ∈ tsupport φ
        · rw [hp (hs hpin)]
        · simp only [splitGrushin_zero_off_test c oscillatorBasis (fun _ => 0) hpin,zero_smul]
      _ = _ := hP φ hφ hc (hs.trans hVO)
  have hhV : ProductLocallyL2On h V := fun K hK hs => hh K hK (hs.trans hVO)
  have hprincipal := principal_ae_eq_of_raw_local_output c d e hd he hV h hhV hPF
  have hdy (i : Fin 4) : ∀ᵐ p ∂volume, p ∈ V → d (yDir i) p = gy i p := by
    apply ProductLocalWeakDirectional.unique hV
      ((ProductLocalWeakDirectional.of_global (hd (yDir i)) V).congr_ae_local hFv (Eventually.of_forall (fun _ _ => rfl)))
      ((hy i).mono hVO)
  have hdt (j : Fin 3) : ∀ᵐ p ∂volume, p ∈ V → d (tDir j) p = gt j p := by
    apply ProductLocalWeakDirectional.unique hV
      ((ProductLocalWeakDirectional.of_global (hd (tDir j)) V).congr_ae_local hFv (Eventually.of_forall (fun _ _ => rfl)))
      ((ht j).mono hVO)
  obtain ⟨U,H,a,b,ha,hb,hU,hHb,hH,hTests⟩ := compact_cutoff_weak_grushin_output c hχ hcχ hd he
  have hUf : U =ᵐ[volume] (fun p => χ p • f p) := by
    filter_upwards [hU,hFv] with p hp hv
    rw [hp]
    by_cases hpin : p ∈ tsupport χ
    · rw [hv (hχV hpin)]
    · simp only [image_eq_zero_of_notMem_tsupport hpin,zero_smul]
  refine ⟨U,H,a,b,hUf,ha,hb,?_,hHb,?_,fun φ hφ hc => (hTests φ hφ hc).symm⟩
  · filter_upwards [hUf] with p hp hpin
    rw [hp,image_eq_zero_of_notMem_tsupport hpin,zero_smul]
  · filter_upwards [hH,hprincipal,hFv,ae_all_iff.mpr hdy,ae_all_iff.mpr hdt] with p hp hq hf hdY hdT
    have heq : rawGrushinCutoffError c χ F (fun i => d (yDir i)) (fun j => d (tDir j)) p =
        rawGrushinCutoffError c χ f gy gt p := by
      by_cases hpin : p ∈ tsupport χ
      · simp only [rawGrushinCutoffError,hf (hχV hpin),fun i => hdY i (hχV hpin),
          fun j => hdT j (hχV hpin)]
      · rw [rawGrushinCutoffError_zero_off c χ F _ _ hpin,
          rawGrushinCutoffError_zero_off c χ f gy gt hpin]
    have hchi : χ p • principal c e p = χ p • h p := by
      by_cases hpin : p ∈ tsupport χ
      · rw [hq (hχV hpin)]
      · simp only [image_eq_zero_of_notMem_tsupport hpin,zero_smul]
    rw [hp,hchi]
    rw [← heq,rawGrushinCutoffError_eq_combined]
    unfold combinedCutoffError
    abel

end TheoremT.Continuum.WeakGrushin
