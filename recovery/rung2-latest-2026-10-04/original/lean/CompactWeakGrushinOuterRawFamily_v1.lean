import CompactWeakGrushinOuterMaximal_v1

/-! Transfer of the maximal bound to an independently constructed raw
natural derivative family. Its exact local compact-test identities and
support are checked inputs; all global L2 memberships and the outer norm
bound are conclusions obtained by genuine weak derivative uniqueness. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem compact_weak_grushin_outer_raw_family_bound
    {c : ℝ} (hc : 0 < c)
    {f h : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K Ω : Set (Space (Fin 3))} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    (i₀ : Fin 4) {R : ℝ} (hR : 0 < R) (hslab : ∀ p ∈ K, |p.1 i₀| ≤ R)
    (S : ℝ) (hS : 1 ≤ S) (hSK : ∀ p ∈ K, ‖p.1‖ ≤ S)
    (D : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (hD : ∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 → ProductLocallyL2On (D α β) Ω)
    (hDs : ∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 →
      ∀ᵐ p ∂volume, p ∉ K → D α β p = 0)
    (hTest : ∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 →
      ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ p, φ p • D α β p) = ((-1 : ℝ)^((∑ i, α i)+(∑ j, β j))) •
          (∫ p, productCoordinateTestWord (mixedMultiIndexWord α β) φ p • f p)) :
    (∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 → MemLp (D α β) 2 volume) ∧
      ∃ W : FactorialOuterIndex → Lp ℂ 2 (volume : Measure (Space (Fin 3))),
        FactorialOuterL2Rep D W ∧
        factorialOuterNorm W ≤ 498*S^2*(4*R^2+2*R+2+2/c)*‖h‖ := by
  have hEq (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
      (ho : (∑ i, α i)+(∑ j, β j) ≤ 2) :
      D α β =ᵐ[volume] (weakFactorialJet f d e α β : Space (Fin 3) → ℂ) :=
    weakFactorialJet_ae_eq_of_local_tests_support f d e hd he α β ho hK.isClosed hΩ hKΩ hs
      (hD α β ho) (hDs α β ho) (hTest α β ho)
  refine ⟨fun α β ho => (Lp.memLp (weakFactorialJet f d e α β)).ae_eq (hEq α β ho).symm,?_⟩
  obtain ⟨W,hW,hWn⟩ := compact_weak_factorial_outer_graph_bound hc d e hd he hK hs hP
    i₀ hR hslab S hS hSK
  exact ⟨W,hW.congr_ae (fun α β ho => (hEq α β ho).symm),hWn⟩

end TheoremT.Continuum.WeakGrushin
