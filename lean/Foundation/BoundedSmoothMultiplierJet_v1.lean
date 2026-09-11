import BoundedSmoothMultiplier_v1
import WeakH2JetClosure_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem boundedRealMul_second_weakPartial {N : ℕ}
    {f dk dl e : SpatialL2 N} {k l : Coordinate N}
    (hl : WeakPartial f dl l) (he : WeakPartial dk e l)
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hm : MemLp χ (⊤ : ENNReal) volume)
    (hk : MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) (⊤ : ENNReal) volume)
    (hd : MemLp (fun x => fderiv ℝ χ x (coordinateVector l)) (⊤ : ENNReal) volume)
    (hkl : MemLp (fun x => fderiv ℝ
      (fun y => fderiv ℝ χ y (coordinateVector k)) x (coordinateVector l)) (⊤ : ENNReal) volume) :
    WeakPartial
      (boundedRealMul χ hm dk+boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) hk f)
      ((boundedRealMul χ hm e+boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector l)) hd dk)+
        (boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector k)) hk dl+
          boundedRealMul (fun x => fderiv ℝ
            (fun y => fderiv ℝ χ y (coordinateVector k)) x (coordinateVector l)) hkl f)) l := by
  have hc : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (coordinateVector k)) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  exact weakPartial_add (weakPartial_boundedRealMul he χ hχ hm hd)
    (weakPartial_boundedRealMul hl _ hc hk hkl)

#print axioms boundedRealMul_second_weakPartial
end TheoremT.Continuum
