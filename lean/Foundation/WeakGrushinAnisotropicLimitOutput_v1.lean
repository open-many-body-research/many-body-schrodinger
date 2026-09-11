import WeakGrushinAnisotropicLimitEventually_v1
import CompactWeakGrushinAnisotropicBounds_v1

/-! Anisotropic strong-L2 closure from actual compact weak Grushin outputs.
Only eventual approximating full weak-H2 witnesses and uniform input/output
L2 bounds are assumed. No derivative of the limit is a premise. This theorem
does not produce the bounded approximating outputs for an arbitrary local
weak solution; that separate localization obligation remains explicit.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem anisotropic_limit_of_eventual_compact_weakH2_outputs
    {c : ℝ} (hc : 0 < c)
    (u h : ℕ → Lp ℂ 2 (volume : Measure (Space κ)))
    (f : Lp ℂ 2 (volume : Measure (Space κ))) (hf : Tendsto u atTop (𝓝 f))
    {F M : ℝ}
    (ha : ∀ᶠ n : ℕ in atTop,
      ∃ d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ e : Jet κ, ∃ K : Set (Space κ),
        (∀ v, WeakProductL2Directional (u n) (d v) v) ∧
        (∀ v w, WeakProductL2Directional (d v) (e v w) w) ∧
        IsCompact K ∧ (∀ᵐ p ∂volume, p ∉ K → u n p = 0) ∧
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • u n p) =
            ∫ p, φ p • h n p) ∧
        ‖u n‖^2 ≤ F ∧ ‖h n‖^2 ≤ M) :
    ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
      (∑ i, ‖gy i‖^2) ≤ 2*F+(3/4 : ℝ)*M ∧
      (∑ j, ‖gt j‖^2) ≤ M/(16*c) ∧
      (∑ i, ∑ j, ‖hyy i j‖^2) ≤ (3/2 : ℝ)*M ∧
      (∀ i, WeakProductL2Directional f (gy i) (yDir i)) ∧
      (∀ j, WeakProductL2Directional f (gt j) (tDir j)) ∧
      ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  have h16 : 0 < 16*c := by positivity
  have hjets : ∀ᶠ n : ℕ in atTop,
      ∃ dy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ dt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ eyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        (∀ i, WeakProductL2Directional (u n) (dy i) (yDir i)) ∧
        (∀ j, WeakProductL2Directional (u n) (dt j) (tDir j)) ∧
        (∀ i j, WeakProductL2Directional (dy i) (eyy i j) (yDir j)) ∧
        ((∑ i, ‖dy i‖^2) + (∑ j, ‖dt j‖^2) + (∑ i, ∑ j, ‖eyy i j‖^2) ≤
          (2*F+(3/4 : ℝ)*M) + M/(16*c) + (3/2 : ℝ)*M) ∧
        (∑ i, ‖dy i‖^2) ≤ 2*F+(3/4 : ℝ)*M ∧
        (∑ j, ‖dt j‖^2) ≤ M/(16*c) ∧
        (∑ i, ∑ j, ‖eyy i j‖^2) ≤ (3/2 : ℝ)*M := by
    filter_upwards [ha] with n hn
    obtain ⟨d,e,K,hd,he,hK,hs,hP,hF,hM⟩ := hn
    obtain ⟨hy,ht,hyy⟩ := compact_weakH2_anisotropic_output_bounds hc d e hd he hK hs hP
    have hy' : (∑ i : Fin 4, ‖d (yDir i)‖^2) ≤ 2*F+(3/4 : ℝ)*M := by nlinarith
    have ht' : (∑ j : κ, ‖d (tDir j)‖^2) ≤ M/(16*c) :=
      ht.trans (div_le_div_of_nonneg_right hM h16.le)
    have hyy' : (∑ i : Fin 4, ∑ j : Fin 4, ‖e (yDir i) (yDir j)‖^2) ≤
        (3/2 : ℝ)*M := by nlinarith
    exact ⟨(fun i => d (yDir i)),(fun j => d (tDir j)),
      (fun i j => e (yDir i) (yDir j)),(fun i => hd (yDir i)),
      (fun j => hd (tDir j)),(fun i j => he (yDir i) (yDir j)),
      add_le_add (add_le_add hy' ht') hyy',hy',ht',hyy'⟩
  obtain ⟨gy,gt,hyy,_,hY,hT,hYY,hgy,hgt,hhyy⟩ :=
    weakProductL2_anisotropic_jets_preserve_bounds_eventually
      (fun i : Fin 4 => oscillatorBasis i) (fun j : κ => oscillatorBasis j) u f hf hjets
  exact ⟨gy,gt,hyy,hY,hT,hYY,hgy,hgt,hhyy⟩

#print axioms anisotropic_limit_of_eventual_compact_weakH2_outputs
end TheoremT.Continuum.WeakGrushin
