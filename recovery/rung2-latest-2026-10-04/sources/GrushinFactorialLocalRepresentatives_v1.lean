import GrushinFactorialLocalProfile_v1
import GrushinFactorialUnweightedComponent_v1

/-! The finite local profile supplies the actual shifted weighted L2
representatives consumed by the indexed commutator estimates. Norms are
identified exactly with the profile's restricted eLpNorm expressions. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_shifted_outer_norm_eq_local
    (D : FactorialRawJetFamily) (Ω : Set (Space (Fin 3)))
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 (volume.restrict Ω))
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (hW : FactorialShiftedOuterL2Rep D W a b) :
    factorialOuterNorm (W a b) = factorialLocalOuterNorm D Ω a b := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [Lp.norm_def,eLpNorm_congr_ae (hW m hm)]
  rfl

theorem factorialLocalProfile_representatives
    {D : FactorialRawJetFamily} {Ω : Set (Space (Fin 3))} {r : ℕ}
    (h : FactorialLocalMemLp D Ω r) :
    ∃ W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 (volume.restrict Ω),
      ∀ a b, factorialMultiDerivativeCost a b ≤ r →
        FactorialShiftedOuterL2Rep D W a b ∧
        factorialOuterNorm (W a b) = factorialLocalOuterNorm D Ω a b ∧
        factorialOuterNorm (W a b) ≤ factorialLocalProfile D Ω r := by
  classical
  have hex (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (m : FactorialOuterIndex) :
      ∃ U : Lp ℂ 2 (volume.restrict Ω), factorialMultiDerivativeCost a b ≤ r →
        m ∈ factorialOuterIndices → U =ᵐ[volume.restrict Ω] factorialShiftedWeightedField D a b m := by
    by_cases hab : factorialMultiDerivativeCost a b ≤ r
    · by_cases hm : m ∈ factorialOuterIndices
      · exact ⟨(h a b hab m hm).toLp _,fun _ _ => MemLp.coeFn_toLp _⟩
      · exact ⟨0,fun _ hmem => False.elim (hm hmem)⟩
    · exact ⟨0,fun hc _ => False.elim (hab hc)⟩
  choose W hW using hex
  refine ⟨W,?_⟩
  intro a b hab
  have hrep : FactorialShiftedOuterL2Rep D W a b := fun m hm => hW a b m hab hm
  have hn := factorial_shifted_outer_norm_eq_local D Ω W a b hrep
  exact ⟨hrep,hn,hn.le.trans (factorialLocalOuterNorm_le_profile D Ω r a b hab)⟩

theorem factorialLocalProfile_unweighted_L2
    {D : FactorialRawJetFamily} {Ω : Set (Space (Fin 3))} {r : ℕ}
    (h : FactorialLocalMemLp D Ω r)
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (hab : factorialMultiDerivativeCost a b ≤ r) :
    ∃ U : Lp ℂ 2 (volume.restrict Ω), U =ᵐ[volume.restrict Ω] D a b ∧
      ‖U‖ ≤ factorialLocalProfile D Ω r := by
  obtain ⟨W,hW⟩ := factorialLocalProfile_representatives h
  exact factorial_unweighted_component_L2 D W r (factorialLocalProfile D Ω r)
    (fun a b hc => (hW a b hc).1) (fun a b hc => (hW a b hc).2.2) a b hab

theorem factorialLocalProfile_lower_unweighted_L2
    {D : FactorialRawJetFamily} {Ω : Set (Space (Fin 3))} {r : ℕ}
    (hr : 1 ≤ r) (h : FactorialLocalMemLp D Ω (r-1))
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (hab : factorialMultiDerivativeCost a b ≤ r) :
    ∃ U : Lp ℂ 2 (volume.restrict Ω), U =ᵐ[volume.restrict Ω] D a b ∧
      ‖U‖ ≤ factorialLocalProfile D Ω (r-1) := by
  obtain ⟨W,hW⟩ := factorialLocalProfile_representatives h
  exact factorial_unweighted_lower_order_L2 D W r (factorialLocalProfile D Ω (r-1)) hr
    (fun a b hc => (hW a b hc).1) (fun a b hc => (hW a b hc).2.2) a b hab

end TheoremT.Continuum.WeakGrushin
