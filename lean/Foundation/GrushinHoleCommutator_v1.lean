import FstDirectionalJet_v1
import SecondDirectionalProduct_v1
import KSHoleSupport_v1

noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]

def splitGrushin (c : ℝ) (v : ι → F) (B : KSSpace × F → ℝ)
    (φ : KSSpace × F → ℝ) (q : KSSpace × F) : ℝ :=
  -(∑ k : Fin 4, fderiv ℝ (fun x => fderiv ℝ φ x (ksBasis k,0)) q (ksBasis k,0))-
  c*‖q.1‖^2*(∑ j, fderiv ℝ (fun x => fderiv ℝ φ x (0,v j)) q (0,v j))+B q*φ q

def ksHoleCommutator (δ : ℝ) (φ : KSSpace × F → ℝ) (q : KSSpace × F) : ℝ :=
  -(∑ k : Fin 4,
    (fderiv ℝ (fun y => fderiv ℝ (ksHole δ) y (ksBasis k)) q.1 (ksBasis k)*φ q+
    2*fderiv ℝ (ksHole δ) q.1 (ksBasis k)*fderiv ℝ φ q (ksBasis k,0)))

theorem splitGrushin_hole_product (δ c : ℝ) (v : ι → F) (B : KSSpace × F → ℝ)
    {φ : KSSpace × F → ℝ} (hφ : ContDiff ℝ ∞ φ) (q : KSSpace × F) :
    splitGrushin c v B (fun x => ksHole δ x.1*φ x) q =
      ksHole δ q.1*splitGrushin c v B φ q+ksHoleCommutator δ φ q := by
  have hh : ContDiff ℝ ∞ (fun x : KSSpace × F => ksHole δ x.1) :=
    (ksHole_contDiff δ).comp contDiff_fst
  have hfirst (w : KSSpace × F) := first_directional_fst
    ((ksHole_contDiff δ).differentiable (by simp)) q w
  have hsecond (w : KSSpace × F) := second_directional_fst (ksHole_contDiff δ) q w w
  simp only [splitGrushin,ksHoleCommutator,second_directional_product hh hφ,
    hfirst,hsecond,ContinuousLinearMap.map_zero,map_zero,zero_mul,mul_zero,zero_add,
    Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  ring_nf
  simp only [← Finset.sum_mul]
  ring

theorem ksHoleCommutator_zero_outer {δ : ℝ} (hδ : 0 < δ)
    (φ : KSSpace × F → ℝ) {q : KSSpace × F} (hq : 2*δ < ‖q.1‖) :
    ksHoleCommutator δ φ q=0 := by
  have hh (k : Fin 4) := ksHole_jet_zero_outer hδ hq (ksBasis k) (ksBasis k)
  simp [ksHoleCommutator,fun k => (hh k).1,fun k => (hh k).2]

#print axioms splitGrushin_hole_product
#print axioms ksHoleCommutator_zero_outer
end TheoremT.Continuum
