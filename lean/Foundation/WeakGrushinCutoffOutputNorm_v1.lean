import WeakGrushinCutoffOutputNormAux_v1
import WeakGrushinCompactCutoff_v1

/-! A local weak Grushin equation and genuine global weak H2 jets produce an
actual compact cutoff and an actual L2 principal output with explicit squared
norm control. The commutator formula is derived from the local equation, not
assumed. The original weighted principal expression need not be globally L2. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_cutoff_weak_grushin_local_output_norm_sq {c : ℝ} (hc : 0 ≤ c)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    {d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))} {e : Jet κ}
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {V : Set (Space κ)} (hV : IsOpen V) (hχV : tsupport χ ⊆ V)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    {K : Set (Space κ)} (hK : IsCompact K) (hs : tsupport χ ⊆ K)
    (M A B : ℝ) (hM : ∀ p, |χ p| ≤ M)
    (hA : ∀ p ∈ K, |combinedCutoffScalar c χ p| ≤ A)
    (hB : ∀ p ∈ K, cutoffGradientWeight c χ p ≤ B) :
    ∃ U H : Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ a : Space κ → Lp ℂ 2 (volume : Measure (Space κ)), ∃ b : Jet κ,
      (∀ v, WeakProductL2Directional U (a v) v) ∧
      (∀ v w, WeakProductL2Directional (a v) (b v w) w) ∧
      U =ᵐ[volume] (fun p => χ p • f p) ∧
      (∀ᵐ p ∂volume, p ∉ tsupport χ → U p = 0) ∧
      H =ᵐ[volume] principal c b ∧
      H =ᵐ[volume] (fun p => χ p • h p - combinedCutoffError c χ f d p) ∧
      (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) = ∫ p, φ p • H p) ∧
      ‖H‖^2 ≤ 2*M^2*‖h‖^2 + 4*A^2*(∫ p in K, ‖f p‖^2) +
        16*B*firstJetEnergyOn c K d := by
  obtain ⟨U,H,a,b,hUa,hab,hU,hHb,hH,hTests⟩ :=
    compact_cutoff_weak_grushin_output c hχ hcχ hd he
  have hlocal := principal_ae_eq_of_weak_output_local c d e hd he hV hP
  have hformula : H =ᵐ[volume] (fun p => χ p • h p - combinedCutoffError c χ f d p) := by
    filter_upwards [hH,hlocal] with p hp hloc
    rw [hp]
    by_cases hv : p ∈ V
    · rw [hloc hv]
      unfold combinedCutoffError
      abel
    · have hz : χ p = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hv (hχV ht))
      simp only [hz,zero_smul,combinedCutoffError]
      abel
  have hsupport : ∀ᵐ p ∂volume, p ∉ tsupport χ → U p = 0 := by
    filter_upwards [hU] with p hp hn
    rw [hp,image_eq_zero_of_notMem_tsupport hn,zero_smul]
  exact ⟨U,H,a,b,hUa,hab,hU,hsupport,hHb,hformula,
    (fun φ hφ hcφ => (hTests φ hφ hcφ).symm),
    cutoff_output_norm_sq_le_of_ae hc hχ hcχ f h d hK hs M A B hM hA hB H hformula⟩

#print axioms compact_cutoff_weak_grushin_local_output_norm_sq
end TheoremT.Continuum.WeakGrushin
