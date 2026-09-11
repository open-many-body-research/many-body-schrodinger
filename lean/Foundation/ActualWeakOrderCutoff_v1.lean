import ActualWeakOrder_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem HasWeakOrder.cutoff {N : ℕ} {n : ℕ} {f : SpatialL2 N}
    (hf : HasWeakOrder f n) (χ : Configuration N → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    HasWeakOrder (cutoffMul χ hχ.continuous hc f) n := by
  induction n generalizing f χ with
  | zero => trivial
  | succ n ih =>
    have hf0 := hf.pred
    obtain ⟨d,hd,he⟩ := hf
    have hD (k : Coordinate N) : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (coordinateVector k)) :=
      (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
    refine ⟨fun k => cutoffMul χ hχ.continuous hc (d k)+
      cutoffMul (fun x => fderiv ℝ χ x (coordinateVector k)) (hD k).continuous
        (hc.fderiv_apply ℝ (coordinateVector k)) f,?_,?_⟩
    · intro k
      exact weakPartial_cutoff (hd k) χ hχ hc
    · intro k
      exact (ih (he k) χ hχ hc).add
        (ih hf0 _ (hD k) (hc.fderiv_apply ℝ (coordinateVector k)))

theorem HasWeakOrder.compact_product_rep {N : ℕ} {n : ℕ} {f : SpatialL2 N}
    (hf : HasWeakOrder f n) {χ : Configuration N → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ g : SpatialL2 N, HasWeakOrder g n ∧ g =ᵐ[volume] (fun x => χ x • f x) :=
  ⟨cutoffMul χ hχ.continuous hc f,hf.cutoff χ hχ hc,cutoffMul_ae χ hχ.continuous hc f⟩

#print axioms HasWeakOrder.cutoff
end TheoremT.Continuum
