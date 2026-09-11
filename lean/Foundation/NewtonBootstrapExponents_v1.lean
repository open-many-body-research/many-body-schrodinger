import Mathlib.Basic.Real.ConjExponents
import Mathlib.Tactic

noncomputable section
namespace TheoremT.Continuum

def newtonBootstrapKernelExponent (D : ℝ) : ℝ := 2*D/(2*D-1)
def newtonBootstrapExponent (D t : ℝ) : ℝ := 2*D/(D-t)

theorem newtonBootstrapKernelExponent_bounds {D : ℝ} (hD : 3 ≤ D) :
    1 < newtonBootstrapKernelExponent D ∧ newtonBootstrapKernelExponent D ≤ 2 ∧
      (D-1)*newtonBootstrapKernelExponent D < D := by
  have hp : 0 < 2*D-1 := by linarith
  unfold newtonBootstrapKernelExponent
  refine ⟨(lt_div_iff₀ hp).mpr (by linarith), (div_le_iff₀ hp).mpr (by linarith), ?_⟩
  rw [← mul_div_assoc, div_lt_iff₀ hp]
  nlinarith

theorem newtonBootstrapExponent_lower {D t : ℝ} (hD : 3 ≤ D) (ht : 0 ≤ t) (htD : t < D) :
    2 ≤ newtonBootstrapExponent D t := by
  unfold newtonBootstrapExponent
  rw [le_div_iff₀ (by linarith : 0 < D-t)]
  linarith

theorem newtonBootstrapExponent_young_step {D t : ℝ} (hD : 3 ≤ D) (ht : 0 ≤ t) (htD : t+1 < D) :
    0 < newtonBootstrapKernelExponent D ∧ 0 < newtonBootstrapExponent D t ∧
      0 < newtonBootstrapExponent D (t+1) ∧
      newtonBootstrapKernelExponent D ≤ newtonBootstrapExponent D (t+1) ∧
      newtonBootstrapExponent D t ≤ newtonBootstrapExponent D (t+1) ∧
      1/newtonBootstrapKernelExponent D+1/newtonBootstrapExponent D t =
        1+1/newtonBootstrapExponent D (t+1) := by
  have hk := newtonBootstrapKernelExponent_bounds hD
  have hq := newtonBootstrapExponent_lower hD ht (by linarith)
  have hr := newtonBootstrapExponent_lower hD (by linarith : 0 ≤ t+1) htD
  refine ⟨by linarith [hk.1],by linarith,by linarith,hk.2.1.trans hr,?_,?_⟩
  · unfold newtonBootstrapExponent
    apply div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  · unfold newtonBootstrapKernelExponent newtonBootstrapExponent
    field_simp
    <;> ring

theorem newtonBootstrapExponent_zero {D : ℝ} (hD : 0 < D) : newtonBootstrapExponent D 0=2 := by
  simp only [newtonBootstrapExponent,sub_zero]
  field_simp

theorem newtonBootstrapExponent_last (D : ℝ) : newtonBootstrapExponent D (D-1)=2*D := by
  simp [newtonBootstrapExponent]

theorem newtonBootstrapExponent_endpoint {D : ℝ} (hD : 3 ≤ D) :
    (newtonBootstrapKernelExponent D).HolderConjugate (2*D) := by
  rw [Real.holderConjugate_iff]
  refine ⟨(newtonBootstrapKernelExponent_bounds hD).1,?_⟩
  unfold newtonBootstrapKernelExponent
  field_simp
  <;> ring

#print axioms newtonBootstrapExponent_young_step
#print axioms newtonBootstrapExponent_endpoint
end TheoremT.Continuum
