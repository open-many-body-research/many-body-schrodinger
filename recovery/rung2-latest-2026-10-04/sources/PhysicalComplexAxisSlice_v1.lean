import PhysicalKSTaylorAnalyticDescentData_v1
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Literal complex coordinate restriction to an axial spectator increment.
All norms here are finite-coordinate Pi sup norms; no identification with
the physical Euclidean Position norm is made. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

def physicalComplexAxisSlice (z : Fin 4 → ℂ) : Fin 3 ⊕ Fin 3 → ℂ :=
  Sum.elim ![z 0,z 1,z 2] ![0,0,z 3]

def physicalComplexAxisSliceCLM : (Fin 4 → ℂ) →L[ℂ] (Fin 3 ⊕ Fin 3 → ℂ) :=
  ({ toFun := physicalComplexAxisSlice
     map_add' := by
       intro x y
       funext j
       cases j with
       | inl i => fin_cases i <;> simp [physicalComplexAxisSlice]
       | inr i => fin_cases i <;> simp [physicalComplexAxisSlice]
     map_smul' := by
       intro c x
       funext j
       cases j with
       | inl i => fin_cases i <;> simp [physicalComplexAxisSlice]
       | inr i => fin_cases i <;> simp [physicalComplexAxisSlice] } :
    (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 ⊕ Fin 3 → ℂ)).toContinuousLinearMap

theorem physicalComplexAxisSliceCLM_apply (z : Fin 4 → ℂ) :
    physicalComplexAxisSliceCLM z = physicalComplexAxisSlice z := rfl

theorem physicalComplexAxisSlice_left (z : Fin 4 → ℂ) :
    (fun i : Fin 3 => physicalComplexAxisSlice z (.inl i)) = ![z 0,z 1,z 2] := rfl

theorem physicalComplexAxisSlice_right (z : Fin 4 → ℂ) :
    (fun i : Fin 3 => physicalComplexAxisSlice z (.inr i)) = ![0,0,z 3] := rfl

theorem physicalComplexAxisSlice_right_norm (z : Fin 4 → ℂ) :
    ‖fun i : Fin 3 => physicalComplexAxisSlice z (.inr i)‖ = ‖z 3‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (z 3))).mpr
    intro i
    fin_cases i <;> simp [physicalComplexAxisSlice]
  · simpa [physicalComplexAxisSlice] using
      norm_le_pi_norm (fun i : Fin 3 => physicalComplexAxisSlice z (.inr i)) 2

theorem physicalComplexAxisSlice_norm (z : Fin 4 → ℂ) :
    ‖physicalComplexAxisSlice z‖ = ‖z‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro j
    cases j with
    | inl i =>
      fin_cases i
      · simpa [physicalComplexAxisSlice] using norm_le_pi_norm z 0
      · simpa [physicalComplexAxisSlice] using norm_le_pi_norm z 1
      · simpa [physicalComplexAxisSlice] using norm_le_pi_norm z 2
    | inr i =>
      fin_cases i
      · simp [physicalComplexAxisSlice]
      · simp [physicalComplexAxisSlice]
      · simpa [physicalComplexAxisSlice] using norm_le_pi_norm z 3
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (physicalComplexAxisSlice z))).mpr
    intro i
    fin_cases i
    · simpa [physicalComplexAxisSlice] using norm_le_pi_norm (physicalComplexAxisSlice z) (.inl 0)
    · simpa [physicalComplexAxisSlice] using norm_le_pi_norm (physicalComplexAxisSlice z) (.inl 1)
    · simpa [physicalComplexAxisSlice] using norm_le_pi_norm (physicalComplexAxisSlice z) (.inl 2)
    · simpa [physicalComplexAxisSlice] using norm_le_pi_norm (physicalComplexAxisSlice z) (.inr 2)

theorem physicalComplexAxisSlice_domain_iff (D S : ℝ) (z : Fin 4 → ℂ) :
    (D*‖fun i : Fin 3 => physicalComplexAxisSlice z (.inl i)‖ < 1 ∧
      S*‖fun i : Fin 3 => physicalComplexAxisSlice z (.inr i)‖ < 1) ↔
    (D*‖![z 0,z 1,z 2]‖ < 1 ∧ S*‖z 3‖ < 1) := by
  rw [physicalComplexAxisSlice_left,physicalComplexAxisSlice_right_norm]

end TheoremT.Continuum
