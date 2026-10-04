import GrushinFactorialMonomialBound_v1

/-! Construction of every outer weighted L2 component from the actual
radial components.  The derivative family is still explicit here: the
functional statement neither assumes the outer norm nor identifies an
arbitrary indexed family with derivatives of one function. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_outer_component_L2 {μ : Measure (Space (Fin 3))}
    {f : Space (Fin 3) → ℂ} (hf : AEStronglyMeasurable f μ)
    {m : FactorialOuterIndex} (hm : m ∈ factorialOuterIndices)
    (R : ℝ) (hR : 1 ≤ R)
    (hs : ∀ᵐ p ∂μ, f p ≠ 0 → ‖p.1‖ ≤ R)
    (U : Lp ℂ 2 μ)
    (hU : U =ᵐ[μ] (fun p => (‖p.1‖^(factorialOuterRadialOrder m.1 m.2.1) : ℝ) • f p)) :
    ∃ W : Lp ℂ 2 μ,
      W =ᵐ[μ] (fun p => factorialYMonomial m.2.2 p.1 • f p) ∧ ‖W‖ ≤ R^2*‖U‖ := by
  have hmeas : AEStronglyMeasurable (fun p : Space (Fin 3) => factorialYMonomial m.2.2 p.1) μ :=
    ((factorialYMonomial_continuous m.2.2).comp continuous_fst).aestronglyMeasurable
  have hb : ∀ᵐ p ∂μ, ‖factorialYMonomial m.2.2 p.1 • f p‖ ≤ R^2*‖U p‖ := by
    filter_upwards [hs,hU] with p hsp hup
    rw [hup]
    by_cases hz : f p = 0
    · simp [hz]
    · have h := factorial_outer_monomial_bound hm R hR p.1 (hsp hz)
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ ‖p.1‖^(factorialOuterRadialOrder m.1 m.2.1))]
      nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg (f p))]
  have hw : MemLp (fun p => factorialYMonomial m.2.2 p.1 • f p) 2 μ :=
    (Lp.memLp U).of_le_mul (hmeas.smul hf) hb
  let W : Lp ℂ 2 μ := hw.toLp _
  have hW : W =ᵐ[μ] (fun p => factorialYMonomial m.2.2 p.1 • f p) := MemLp.coeFn_toLp hw
  refine ⟨W,hW,Lp.norm_le_mul_norm_of_ae_le_mul ?_⟩
  filter_upwards [hW,hb] with p hwp hbp
  rwa [hwp]

theorem factorial_outer_L2_assembly {μ : Measure (Space (Fin 3))}
    (D : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ)
    (R C : ℝ) (hR : 1 ≤ R)
    (hD : ∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 → AEStronglyMeasurable (D α β) μ)
    (hs : ∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 →
      ∀ᵐ p ∂μ, D α β p ≠ 0 → ‖p.1‖ ≤ R)
    (hcomp : ∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 →
      ∃ U : Lp ℂ 2 μ,
        U =ᵐ[μ] (fun p => (‖p.1‖^(factorialOuterRadialOrder α β) : ℝ) • D α β p) ∧ ‖U‖ ≤ C) :
    ∃ W : FactorialOuterIndex → Lp ℂ 2 μ,
      FactorialOuterL2Rep D W ∧
      factorialOuterNorm W ≤ (factorialOuterIndices.card : ℝ)*R^2*C := by
  classical
  have hex (m : FactorialOuterIndex) : ∃ W : Lp ℂ 2 μ,
      (m ∈ factorialOuterIndices → W =ᵐ[μ] (fun p => factorialYMonomial m.2.2 p.1 • D m.1 m.2.1 p)) ∧
      (m ∈ factorialOuterIndices → ‖W‖ ≤ R^2*C) := by
    by_cases hm : m ∈ factorialOuterIndices
    · have hn := ((factorialOuterIndices_mem m).mp hm).1
      obtain ⟨U,hU,hUn⟩ := hcomp m.1 m.2.1 hn
      obtain ⟨W,hW,hWn⟩ := factorial_outer_component_L2 (hD _ _ hn) hm R hR (hs _ _ hn) U hU
      exact ⟨W,fun _ => hW,fun _ => hWn.trans (mul_le_mul_of_nonneg_left hUn (sq_nonneg R))⟩
    · exact ⟨0,fun h => False.elim (hm h),fun h => False.elim (hm h)⟩
  choose W hW hWn using hex
  refine ⟨W,hW,?_⟩
  calc
    factorialOuterNorm W ≤ ∑ m ∈ factorialOuterIndices, R^2*C :=
      Finset.sum_le_sum (fun m hm => hWn m hm)
    _ = _ := by simp [mul_assoc]

end TheoremT.Continuum.WeakGrushin
