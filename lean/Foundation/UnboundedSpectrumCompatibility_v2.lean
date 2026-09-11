import UnboundedResolvent_v2
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-! The new ordinary bounded-inverse spectrum agrees with mathlib's spectrum
when the actual operator is bounded and everywhere defined. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.OperatorTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem hasBoundedInverse_toPMap_iff_isUnit (A : E →L[ℂ] E) :
    HasBoundedInverse (A.toPMap ⊤) ↔ IsUnit A := by
  rw [isUnit_iff_exists]
  constructor
  · rintro ⟨R,hR,hr,hl⟩
    refine ⟨R,?_,?_⟩
    · ext y
      exact hr y
    · ext x
      exact hl ⟨x,Submodule.mem_top⟩
  · rintro ⟨R,hr,hl⟩
    refine ⟨R,fun _ => Submodule.mem_top,?_,?_⟩
    · intro y
      exact DFunLike.congr_fun hr y
    · intro x
      exact DFunLike.congr_fun hl (x : E)

theorem operatorShift_toPMap (A : E →L[ℂ] E) (z : ℂ) :
    operatorShift (A.toPMap ⊤) z = (A-z•1).toPMap ⊤ := by
  apply LinearPMap.ext rfl
  intro x hx hy
  rfl

theorem unboundedSpectrum_toPMap_eq_spectrum (A : E →L[ℂ] E) :
    unboundedSpectrum (A.toPMap ⊤) = spectrum ℂ A := by
  ext z
  rw [mem_unboundedSpectrum_iff, operatorShift_toPMap,
    hasBoundedInverse_toPMap_iff_isUnit]
  change (¬ IsUnit (A-z•1)) ↔ ¬ IsUnit (algebraMap ℂ (E →L[ℂ] E) z - A)
  rw [Algebra.algebraMap_eq_smul_one]
  exact not_congr (by simpa only [neg_sub] using (IsUnit.neg_iff (a := A-z•1)).symm)

#print axioms hasBoundedInverse_toPMap_iff_isUnit
#print axioms unboundedSpectrum_toPMap_eq_spectrum
end TheoremT.OperatorTheory
