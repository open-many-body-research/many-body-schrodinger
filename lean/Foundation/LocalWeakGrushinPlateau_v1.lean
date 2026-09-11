import CompactWeakGrushinLocalOutput_v1
import ProductLocalEllipticH2_v1
import FiniteDimSmoothCutoff_v1

/-! Outer plateau cutoffs for local weak H2 data and exact preservation of the
weak Grushin equation on the plateau. No global H2 input is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem exists_outer_plateau {K Ω : Set (Space κ)}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKO : K ⊆ Ω) :
    ∃ χ : Space κ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      ∃ V : Set (Space κ), IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧ ∀ p ∈ V, χ p = 1 := by
  obtain ⟨χ,hχ,hcχ,hsχ,hχ1⟩ := finiteDim_compact_exists_smooth_cutoff hK hΩ hKO
  let V := Ω ∩ interior {p | χ p = 1}
  refine ⟨χ,hχ,hcχ,hsχ,V,hΩ.inter isOpen_interior,?_,Set.inter_subset_left,?_⟩
  · intro p hp
    refine ⟨hKO hp,?_⟩
    exact mem_interior_iff_mem_nhds.mpr (hχ1 p hp)
  · intro p hp
    change p ∈ {q | χ q = 1}
    exact interior_subset hp.2

theorem weak_output_on_plateau (c : ℝ)
    {f h U : Lp ℂ 2 (volume : Measure (Space κ))} {χ : Space κ → ℝ}
    (hU : (U : Space κ → ℂ) =ᵐ[volume] (fun p => χ p • f p))
    {V Ω : Set (Space κ)} (hVO : V ⊆ Ω) (hχ1 : ∀ p ∈ V, χ p = 1)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) = ∫ p, φ p • h p := by
  intro φ hφ hcφ hsφ
  calc
    _ = ∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p := by
      apply integral_congr_ae
      filter_upwards [hU] with p hp
      by_cases ht : p ∈ tsupport φ
      · rw [hp,hχ1 p (hsφ ht),one_smul]
      · rw [splitGrushin_zero_off_test c oscillatorBasis (fun _ => 0) ht]
        simp only [zero_smul]
    _ = _ := hP φ hφ hcφ (hsφ.trans hVO)

theorem local_weakH2_plateau_data
    {f : Lp ℂ 2 (volume : Measure (Space κ))} {Ω : Set (Space κ)}
    (hΩ : IsOpen Ω) (hf : ProductLocalWeakH2On (f : Space κ → ℂ) Ω)
    {K : Set (Space κ)} (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ χ : Space κ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      ∃ V : Set (Space κ), IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧ (∀ p ∈ V, χ p = 1) ∧
      ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)), ∃ e : Jet κ,
        (U : Space κ → ℂ) =ᵐ[volume] (fun p => χ p • f p) ∧
        (∀ v, WeakProductL2Directional U (d v) v) ∧
        (∀ v w, WeakProductL2Directional (d v) (e v w) w) ∧
        (∀ᵐ p ∂volume, p ∉ tsupport χ → U p = 0) := by
  obtain ⟨χ,hχ,hcχ,hsχ,V,hV,hKV,hVO,hχ1⟩ := exists_outer_plateau hK hΩ hKO
  obtain ⟨U,d,hU,hd,hdd⟩ := hf χ hχ hcχ hsχ
  choose e he using hdd
  refine ⟨χ,hχ,hcχ,hsχ,V,hV,hKV,hVO,hχ1,U,d,e,hU,hd,he,?_⟩
  filter_upwards [hU] with p hp ht
  rw [hp,image_eq_zero_of_notMem_tsupport ht,zero_smul]

end TheoremT.Continuum.WeakGrushin
