import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

theorem locally_lipschitz_real_smul {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {g : X → ℂ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => f x • g x) := by
  have hm : ContDiff ℝ 1 (fun z : ℝ × ℂ => z.1 • z.2) := contDiff_fst.smul contDiff_snd
  exact hm.locallyLipschitz.comp (hf.prodMk hg)

theorem locally_lipschitz_real_mul {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => f x*g x) := by
  have hm : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1*z.2) := contDiff_fst.mul contDiff_snd
  exact hm.locallyLipschitz.comp (hf.prodMk hg)

theorem locally_lipschitz_finset_sum {X I E : Type*} [PseudoMetricSpace X]
    [SeminormedAddCommGroup E] (s : Finset I) (f : I → X → E)
    (hf : ∀ i ∈ s, LocallyLipschitz (f i)) : LocallyLipschitz (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LocallyLipschitz.const (0:E))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

#print axioms locally_lipschitz_real_smul
#print axioms locally_lipschitz_real_mul
#print axioms locally_lipschitz_finset_sum
end TheoremT.Continuum
