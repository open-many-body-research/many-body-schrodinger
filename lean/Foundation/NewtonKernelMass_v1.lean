import AtomicSobolevExponent_v1
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! The positive integrable mass kernel for regularized Newton potentials.
The normalizing integral is retained as an exact mathematical real constant. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

def newtonMassKernel (N : ℕ) (x : Configuration N) : ℝ :=
  (3*N:ℝ)*(1+‖x‖^2)^(-((3*N:ℝ)+2)/2)

def newtonMass (N : ℕ) : ℝ := ∫ x, newtonMassKernel N x

theorem newtonMassKernel_integrable (N : ℕ) : Integrable (newtonMassKernel N) volume := by
  have hh := integrable_rpow_neg_one_add_norm_sq (E := Configuration N) (μ := volume)
    (r := (3*N:ℝ)+2) (by rw [configuration_finrank]; push_cast; linarith)
  exact hh.const_mul (3*N:ℝ)

theorem newtonMassKernel_pos {N : ℕ} (hN : 0 < N) (x : Configuration N) :
    0 < newtonMassKernel N x := by unfold newtonMassKernel; positivity

theorem newtonMass_pos {N : ℕ} (hN : 0 < N) : 0 < newtonMass N := by
  apply (integral_pos_iff_support_of_nonneg
    (fun x => (newtonMassKernel_pos hN x).le) (newtonMassKernel_integrable N)).mpr
  have hs : Function.support (newtonMassKernel N)=Set.univ := by
    ext x
    simp only [Function.mem_support,Set.mem_univ,iff_true]
    exact (newtonMassKernel_pos hN x).ne'
  rw [hs]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

#print axioms newtonMassKernel_integrable
#print axioms newtonMass_pos
end TheoremT.Continuum
