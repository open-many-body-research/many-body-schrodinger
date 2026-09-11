import ActualWeakOrderCutoff_v1
import KSHoleSupport_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem nested_cutoff_weakPartial_eq {N : ℕ} {f d a : SpatialL2 N} {k : Coordinate N}
    (hd : WeakPartial f d k)
    {χ η : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (h1 : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1)
    (ha : WeakPartial (cutoffMul η hη.continuous hcη f) a k) :
    cutoffMul χ hχ.continuous hcχ a=cutoffMul χ hχ.continuous hcχ d := by
  have hD : ContDiff ℝ ∞ (fun x => fderiv ℝ η x (coordinateVector k)) :=
    (hη.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  let e := cutoffMul η hη.continuous hcη d+
    cutoffMul (fun x => fderiv ℝ η x (coordinateVector k)) hD.continuous
      (hcη.fderiv_apply ℝ (coordinateVector k)) f
  have he : a=e := weakPartial_unique ha (weakPartial_cutoff hd η hη hcη)
  have heval : ∀ᵐ x ∂volume, a x=η x • d x+fderiv ℝ η x (coordinateVector k) • f x := by
    rw [he]
    filter_upwards [Lp.coeFn_add (cutoffMul η hη.continuous hcη d)
      (cutoffMul (fun x => fderiv ℝ η x (coordinateVector k)) hD.continuous
        (hcη.fderiv_apply ℝ (coordinateVector k)) f),
      cutoffMul_ae η hη.continuous hcη d,
      cutoffMul_ae (fun x => fderiv ℝ η x (coordinateVector k)) hD.continuous
        (hcη.fderiv_apply ℝ (coordinateVector k)) f] with x hx hdx hfx
    change (cutoffMul η hη.continuous hcη d+_ ) x=_
    simpa only [hx,Pi.add_apply,hdx,hfx]
  apply Lp.ext
  filter_upwards [cutoffMul_ae χ hχ.continuous hcχ a,cutoffMul_ae χ hχ.continuous hcχ d,heval] with x hxa hxd hax
  rw [hxa,hxd,hax]
  by_cases hx : x ∈ tsupport χ
  · have hηx : η x=1 := (h1 x hx).self_of_nhds
    have hDx := (locally_constant_first_second_zero (h1 x hx) (coordinateVector k) 0).1
    simp only [hηx,hDx,one_smul,zero_smul,add_zero]
  · simp only [image_eq_zero_of_notMem_tsupport hx,zero_smul]

#print axioms nested_cutoff_weakPartial_eq
end TheoremT.Continuum
