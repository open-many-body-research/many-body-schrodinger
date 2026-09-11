import LocalWeakGrushinEnergy_v1

/-! Local weak H2 Caccioppoli estimates. The input need not have compact support
or global weak H2 regularity. The estimate applies to every actual L2 first-jet
representation of the cutoff, by uniqueness of genuine weak derivatives. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem local_weakH2_cutoff_energy_of_weak_jet (c : ℝ)
    {f h U : Lp ℂ 2 (volume : Measure (Space κ))} {Ω : Set (Space κ)}
    (hΩ : IsOpen Ω) (hf : ProductLocalWeakH2On (f : Space κ → ℂ) Ω)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    {a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hU : (U : Space κ → ℂ) =ᵐ[volume] (fun p => η p • f p))
    (ha : ∀ v, WeakProductL2Directional U (a v) v) :
    firstEnergy c a = (∫ p, inner ℝ ((η p)^2 • f p) (h p)) + grushinCutoffEnergy c η f := by
  obtain ⟨U',a',b',hU',ha',hb',hs',hE⟩ := local_weakH2_cutoff_energy c hΩ hf hη hcη hηΩ hP
  have hEqU : U' = U := Lp.ext (hU'.trans hU.symm)
  have hEqa : a' = a := by
    funext v
    exact weak_directional_unique (hEqU ▸ ha' v) (ha v)
  simpa only [hEqa] using hE

theorem local_weakH2_cutoff_caccioppoli_of_weak_jet (c : ℝ)
    {f h U : Lp ℂ 2 (volume : Measure (Space κ))} {Ω : Set (Space κ)}
    (hΩ : IsOpen Ω) (hf : ProductLocalWeakH2On (f : Space κ → ℂ) Ω)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    {a : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hU : (U : Space κ → ℂ) =ᵐ[volume] (fun p => η p • f p))
    (ha : ∀ v, WeakProductL2Directional U (a v) v) :
    firstEnergy c a ≤
      ((∫ p, (η p)^2*‖f p‖^2)+(∫ p, (η p)^2*‖h p‖^2))/2 + grushinCutoffEnergy c η f := by
  rw [local_weakH2_cutoff_energy_of_weak_jet c hΩ hf hη hcη hηΩ hP hU ha]
  exact add_le_add (cutoff_l2_pairing_le_half hη.continuous hcη f (Lp.memLp h)) (le_refl _)

theorem local_weakH2_cutoff_caccioppoli (c : ℝ)
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
      firstEnergy c a ≤
        ((∫ p, (η p)^2*‖f p‖^2)+(∫ p, (η p)^2*‖h p‖^2))/2 + grushinCutoffEnergy c η f := by
  obtain ⟨U,a,b,hU,ha,hb,hs,hE⟩ := local_weakH2_cutoff_energy c hΩ hf hη hcη hηΩ hP
  exact ⟨U,a,b,hU,ha,hb,hs,local_weakH2_cutoff_caccioppoli_of_weak_jet c hΩ hf hη hcη hηΩ hP hU ha⟩

end TheoremT.Continuum.WeakGrushin
