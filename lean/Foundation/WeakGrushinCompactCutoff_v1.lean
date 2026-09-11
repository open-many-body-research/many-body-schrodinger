import ProductCompactCutoffWeakJet_v1
import WeakGrushinCutoffPrincipalMemLp_v1
import WeakGrushinPrincipalTests_v1

/-! A genuine compact weak H2 cutoff has actual L2 Grushin output and the
explicit weak cutoff commutator. Every input first and second derivative is
verified against all real smooth compact product tests. The original weighted
principal expression need not be globally L2. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_cutoff_weak_grushin (c : ℝ)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))} {e : Jet κ}
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w) :
    ∃ U : Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ a : Space κ → Lp ℂ 2 (volume : Measure (Space κ)), ∃ b : Jet κ,
      (∀ v, WeakProductL2Directional U (a v) v) ∧
      (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
      U =ᵐ[volume] (fun p => χ p • f p) ∧
      (∀ v, a v =ᵐ[volume] (fun p => χ p • d v p + fderiv ℝ χ p v • f p)) ∧
      (∀ v w, b v w =ᵐ[volume] (fun p =>
        (χ p • e v w p + fderiv ℝ χ p w • d v p) +
        (fderiv ℝ χ p v • d w p +
          fderiv ℝ (fun q => fderiv ℝ χ q v) p w • f p))) ∧
      (principal c b =ᵐ[volume] (fun p => χ p • principal c e p -
        cutoffYError χ f d p - (c*‖p.1‖^2) • cutoffTError χ f d p)) ∧
      MemLp (principal c b) 2 volume := by
  obtain ⟨U,a,b,hUa,hab,hU,ha,hb⟩ := product_compact_cutoff_weak_jet hχ hcχ hd he
  exact ⟨U,a,b,hUa,hab,hU,ha,hb,
    principal_cutoff_of_second_jet_formula c χ f d e b hb,
    principal_cutoff_memLp_of_second_jet_formula c hχ hcχ f d e b hb⟩

theorem compact_cutoff_weak_grushin_output (c : ℝ)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))} {e : Jet κ}
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w) :
    ∃ U H : Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ a : Space κ → Lp ℂ 2 (volume : Measure (Space κ)), ∃ b : Jet κ,
      (∀ v, WeakProductL2Directional U (a v) v) ∧
      (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
      U =ᵐ[volume] (fun p => χ p • f p) ∧
      H =ᵐ[volume] principal c b ∧
      H =ᵐ[volume] (fun p => χ p • principal c e p -
        cutoffYError χ f d p - (c*‖p.1‖^2) • cutoffTError χ f d p) ∧
      (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ p, φ p • H p) =
          ∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) := by
  obtain ⟨U,a,b,hUa,hab,hU,_,_,hP,hm⟩ := compact_cutoff_weak_grushin c hχ hcχ hd he
  let H := hm.toLp (principal c b)
  have hH : H =ᵐ[volume] principal c b := MemLp.coeFn_toLp hm
  refine ⟨U,H,a,b,hUa,hab,hU,hH,hH.trans hP,?_⟩
  intro φ hφ hcφ
  calc
    (∫ p, φ p • H p) = ∫ p, φ p • principal c b p := by
      apply integral_congr_ae
      filter_upwards [hH] with p hp
      rw [hp]
    _ = _ := principal_compact_test c a b hUa hab hφ hcφ

#print axioms compact_cutoff_weak_grushin
#print axioms compact_cutoff_weak_grushin_output
end TheoremT.Continuum.WeakGrushin
