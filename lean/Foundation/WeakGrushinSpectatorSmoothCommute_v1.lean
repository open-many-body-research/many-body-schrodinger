import CompactHessianCross_v1
import GrushinTestSupport_v1

/-! Actual smooth spectator differentiation commutes with the zero-potential
Grushin principal operator. The coefficient c|y|² has zero spectator derivative,
and third directional derivatives are permuted using proved second-derivative
symmetry. Arbitrary finite spectator families and real c are permitted. -/
noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem smooth_third_same_directional_commute
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {u : E → G} (hu : ContDiff ℝ ∞ u) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun y => fderiv ℝ u y v) z w) x w =
      fderiv ℝ (fun z => fderiv ℝ (fun y => fderiv ℝ u y w) z w) x v := by
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ u y w) :=
    (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hh : (fun z => fderiv ℝ (fun y => fderiv ℝ u y v) z w) =
      (fun z => fderiv ℝ (fun y => fderiv ℝ u y w) z v) := by
    funext z
    exact smooth_second_directional_commute hu z v w
  rw [hh]
  exact smooth_second_directional_commute hd x v w

theorem finite_second_sum_directional_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) (x w : E) :
    fderiv ℝ (fun q => ∑ i : ι, fderiv ℝ (fun z => fderiv ℝ u z (v i)) q (v i)) x w =
      ∑ i : ι, fderiv ℝ (fun q => fderiv ℝ (fun z => fderiv ℝ u z w) q (v i)) x (v i) := by
  have hd (i : ι) : ContDiff ℝ ∞ (fun q => fderiv ℝ
      (fun z => fderiv ℝ u z (v i)) q (v i)) :=
    ((((hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const)
  rw [fderiv_fun_sum (fun i _ => (hd i).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact (smooth_third_same_directional_commute hu x w (v i)).symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]

theorem splitGrushin_zero_contDiff (c : ℝ) (v : ι → F)
    {φ : KSSpace × F → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (splitGrushin c v (fun _ => 0) φ) := by
  have h2 (w : KSSpace × F) : ContDiff ℝ ∞
      (fun q => fderiv ℝ (fun z => fderiv ℝ φ z w) q w) :=
    ((((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const)
  have hy := ContDiff.sum (fun i (_ : i ∈ Finset.univ) => h2 (ksBasis i,0))
  have ht := ContDiff.sum (fun j (_ : j ∈ Finset.univ) => h2 (0,v j))
  have ha : ContDiff ℝ ∞ (fun p : KSSpace × F => c*‖p.1‖^2) :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_fst)
  unfold splitGrushin
  simpa only [zero_mul,add_zero,Pi.neg_def,Pi.sub_def,Pi.mul_def] using
    hy.neg.sub (ha.mul ht)

theorem grushin_weight_spectator_derivative_zero (c : ℝ) (w : F) (p : KSSpace × F) :
    fderiv ℝ (fun q : KSSpace × F => c*‖q.1‖^2) p (0,w) = 0 := by
  have hh : ContDiff ℝ ∞ (fun y : KSSpace => c*‖y‖^2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  rw [first_directional_fst (hh.differentiable (by simp)) p (0,w)]
  simp

theorem splitGrushin_spectator_directional_commute (c : ℝ) (v : ι → F) (w : F)
    {φ : KSSpace × F → ℝ} (hφ : ContDiff ℝ ∞ φ) (p : KSSpace × F) :
    splitGrushin c v (fun _ => 0) (fun q => fderiv ℝ φ q (0,w)) p =
      fderiv ℝ (splitGrushin c v (fun _ => 0) φ) p (0,w) := by
  let Ly := fun q : KSSpace × F => ∑ i : Fin 4,
    fderiv ℝ (fun z => fderiv ℝ φ z (ksBasis i,0)) q (ksBasis i,0)
  let Lt := fun q : KSSpace × F => ∑ j : ι,
    fderiv ℝ (fun z => fderiv ℝ φ z (0,v j)) q (0,v j)
  let a := fun q : KSSpace × F => c*‖q.1‖^2
  have h2 (u : KSSpace × F) : ContDiff ℝ ∞
      (fun q => fderiv ℝ (fun z => fderiv ℝ φ z u) q u) :=
    ((((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).fderiv_right
      (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const)
  have hy : ContDiff ℝ ∞ Ly := ContDiff.sum (fun i _ => h2 (ksBasis i,0))
  have ht : ContDiff ℝ ∞ Lt := ContDiff.sum (fun j _ => h2 (0,v j))
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_fst)
  have heq : splitGrushin c v (fun _ => 0) φ = (fun q => -Ly q-a q*Lt q) := by
    funext q
    simp only [splitGrushin,Ly,Lt,a,zero_mul,add_zero]
  have hD := ((hy.differentiable (by simp) p).hasFDerivAt.neg).sub
    ((ha.differentiable (by simp) p).hasFDerivAt.mul (ht.differentiable (by simp) p).hasFDerivAt)
  change HasFDerivAt (𝕜 := ℝ) (fun q => -Ly q-a q*Lt q) _ p at hD
  rw [heq,hD.fderiv]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  have hz : fderiv ℝ a p (0,w) = 0 := grushin_weight_spectator_derivative_zero c w p
  rw [hz,mul_zero,add_zero]
  have hyD := finite_second_sum_directional_commute (fun i : Fin 4 => (ksBasis i,(0 : F))) hφ p (0,w)
  have htD := finite_second_sum_directional_commute (fun j : ι => ((0 : KSSpace),v j)) hφ p (0,w)
  change fderiv ℝ Ly p (0,w) = _ at hyD
  change fderiv ℝ Lt p (0,w) = _ at htD
  rw [hyD,htD]
  simp only [splitGrushin,a,zero_mul,add_zero]

#print axioms smooth_third_same_directional_commute
#print axioms finite_second_sum_directional_commute
#print axioms splitGrushin_zero_contDiff
#print axioms grushin_weight_spectator_derivative_zero
#print axioms splitGrushin_spectator_directional_commute
end TheoremT.Continuum.WeakGrushin
