import CompactSmoothFactorialRadialBound_v1
import CompactGrushinSlabGraphBounds_v1
import GrushinFactorialOuterAssembly_v1
import GrushinFactorialOuterCardinality_v1

/-! The full exact 498-term outer norm of genuine smooth derivatives is
bounded by the actual Grushin output.  The finite L2 representatives are
constructed here, rather than assumed.  This is a compact graph estimate,
not an eigenfunction regularity or factorial recurrence theorem. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem compact_smooth_factorial_outer_graph_bound
    {c : ℝ} (hc : 0 < c) {G : Space (Fin 3) → ℂ}
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (i₀ : Fin 4) {R : ℝ} (hR : 0 < R)
    (hs : ∀ p, G p ≠ 0 → |p.1 i₀| ≤ R)
    (S : ℝ) (hS : 1 ≤ S) (hSG : ∀ p ∈ tsupport G, ‖p.1‖ ≤ S) :
    ∃ H : Lp ℂ 2 (volume : Measure (Space (Fin 3))),
      H =ᵐ[volume] euclideanGrushin c G ∧
      ∃ W : FactorialOuterIndex → Lp ℂ 2 (volume : Measure (Space (Fin 3))),
        FactorialOuterL2Rep (smoothFactorialJet G) W ∧
        factorialOuterNorm W ≤ 498*S^2*(factorialGraphCoefficient R c)*‖H‖ := by
  have hP : MemLp (euclideanGrushin c G) 2 (volume : Measure (Space (Fin 3))) :=
    (euclideanGrushin_contDiff c hG).continuous.memLp_of_hasCompactSupport
      (euclideanGrushin_hasCompactSupport c hcG)
  let H : Lp ℂ 2 (volume : Measure (Space (Fin 3))) := hP.toLp _
  have hH : H =ᵐ[volume] euclideanGrushin c G := MemLp.coeFn_toLp hP
  have hC : 0 ≤ factorialGraphCoefficient R c :=
    (by norm_num : (0:ℝ) ≤ 2).trans (factorialGraphCoefficient_bounds hR hc).2.2.1
  have hD (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
      AEStronglyMeasurable (smoothFactorialJet G α β) (volume : Measure (Space (Fin 3))) :=
    (smoothFactorialJet_contDiff hG α β).continuous.aestronglyMeasurable
  have hDs (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) :
      ∀ᵐ p ∂(volume : Measure (Space (Fin 3))), smoothFactorialJet G α β p ≠ 0 → ‖p.1‖ ≤ S := by
    exact Eventually.of_forall (fun p hp => hSG p
      (smoothFactorialJet_tsupport_subset G α β (subset_tsupport _ hp)))
  have hcomp (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
      (ho : (∑ i, α i)+(∑ j, β j) ≤ 2) :
      ∃ U : Lp ℂ 2 (volume : Measure (Space (Fin 3))),
        U =ᵐ[volume] (fun p => (‖p.1‖^(factorialOuterRadialOrder α β) : ℝ) • smoothFactorialJet G α β p) ∧
        ‖U‖ ≤ factorialGraphCoefficient R c*‖H‖ := by
    let f := fun p : Space (Fin 3) => (‖p.1‖^(factorialOuterRadialOrder α β) : ℝ) • smoothFactorialJet G α β p
    have hf : Continuous f := (continuous_fst.norm.pow _).smul (smoothFactorialJet_contDiff hG α β).continuous
    have hfc : HasCompactSupport f := by
      apply (smoothFactorialJet_hasCompactSupport hcG α β).mono
      intro p hp hz
      exact hp (by simp [f,hz])
    have hf2 : MemLp f 2 (volume : Measure (Space (Fin 3))) := hf.memLp_of_hasCompactSupport hfc
    let U : Lp ℂ 2 (volume : Measure (Space (Fin 3))) := hf2.toLp f
    refine ⟨U,MemLp.coeFn_toLp hf2,?_⟩
    have hslab := compact_grushin_slab_graph_bounds hc.le i₀ hG hcG hR hs
    have hn := compact_smooth_factorial_radial_integral_bound hc hG hcG hR hslab.1 hslab.2.2 α β ho
    change (∫ p, ‖f p‖^2) ≤ _ at hn
    rw [← actual_l2_toLp_norm_sq_integral hf2,← actual_l2_toLp_norm_sq_integral hP] at hn
    change ‖U‖^2 ≤ (factorialGraphCoefficient R c)^2*‖H‖^2 at hn
    nlinarith [norm_nonneg U,norm_nonneg H,mul_nonneg hC (norm_nonneg H)]
  obtain ⟨W,hW,hWn⟩ := factorial_outer_L2_assembly (smoothFactorialJet G)
    S (factorialGraphCoefficient R c*‖H‖) hS (fun α β _ => hD α β)
    (fun α β _ => hDs α β) hcomp
  refine ⟨H,hH,W,hW,?_⟩
  simpa only [factorialOuterIndices_card,Nat.cast_ofNat,mul_assoc] using hWn

end TheoremT.Continuum.WeakGrushin
