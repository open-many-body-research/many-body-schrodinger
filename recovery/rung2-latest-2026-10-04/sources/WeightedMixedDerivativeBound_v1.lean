import WeakMixedLaplacianNorm_v1
import WeakLaplacianDistribution_v1
import BoundedMultiplierNormComparison_v1

/-! An actual weak H² weighted estimate, controlling every ordered mixed
derivative by a weighted Laplacian, weighted first derivatives and weight
derivatives. No regularity or norm conclusion is hidden in an existence premise. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem weak_weighted_mixed_bound {N : ℕ} {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l)
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hm : MemLp χ ⊤ volume)
    (hdm : ∀ k : Coordinate N, MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) ⊤ volume)
    (hddm : ∀ k l : Coordinate N, MemLp
      (fun x => fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector k)) x
        (coordinateVector l)) ⊤ volume)
    {A B C0 C1 CΔ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ x k, |fderiv ℝ χ x (coordinateVector k)| ≤ A*|χ x|)
    (hsecond : ∀ x k l, |fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector k))
      x (coordinateVector l)| ≤ B*|χ x|)
    (h0 : ‖boundedRealMul χ hm f‖ ≤ C0)
    (h1 : ∀ k, ‖boundedRealMul χ hm (d k)‖ ≤ C1)
    (hΔ : ‖boundedRealMul χ hm (∑ k, e k k)‖ ≤ CΔ) (k l : Coordinate N) :
    ‖boundedRealMul χ hm (e k l)‖ ≤
      CΔ+((Fintype.card (Coordinate N) : ℝ)+1)*(2*A*C1+B*C0) := by
  classical
  let M := boundedRealMul χ hm
  let P (i : Coordinate N) := boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector i)) (hdm i)
  let Q (i j : Coordinate N) := boundedRealMul
    (fun x => fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector i)) x (coordinateVector j)) (hddm i j)
  let D (i : Coordinate N) := M (d i)+P i f
  let R (i j : Coordinate N) := P j (d i)+P i (d j)+Q i j f
  let F (i j : Coordinate N) := M (e i j)+R i j
  have hD (i : Coordinate N) : WeakPartial (M f) (D i) i :=
    weakPartial_boundedRealMul (hd i) χ hχ hm (hdm i)
  have hF (i j : Coordinate N) : WeakPartial (D i) (F i j) j := by
    have hχi : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (coordinateVector i)) :=
      (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
    have hh := weakPartial_add
      (weakPartial_boundedRealMul (he i j) χ hχ hm (hdm j))
      (weakPartial_boundedRealMul (hd j) _ hχi (hdm i) (hddm i j))
    convert! hh using 1
    dsimp [F,R]
    abel
  have hP (i j : Coordinate N) : ‖P i (d j)‖ ≤ A*C1 :=
    (boundedRealMul_norm_le_relative _ χ (hdm i) hm A (fun x => hfirst x i) (d j)).trans
      (mul_le_mul_of_nonneg_left (h1 j) hA)
  have hQ (i j : Coordinate N) : ‖Q i j f‖ ≤ B*C0 :=
    (boundedRealMul_norm_le_relative _ χ (hddm i j) hm B (fun x => hsecond x i j) f).trans
      (mul_le_mul_of_nonneg_left h0 hB)
  have hR (i j : Coordinate N) : ‖R i j‖ ≤ 2*A*C1+B*C0 := by
    have hh := (norm_add_le (P j (d i)+P i (d j)) (Q i j f)).trans
      (add_le_add (norm_add_le (P j (d i)) (P i (d j))) le_rfl)
    change ‖P j (d i)+P i (d j)+Q i j f‖ ≤ _
    nlinarith [hP j i,hP i j,hQ i j]
  have hsum : (∑ i, F i i) = M (∑ i, e i i)+(∑ i, R i i) := by
    simp only [F,Finset.sum_add_distrib]
    dsimp only [M]
    rw [boundedRealMul_sum]
  have hsumR : ‖∑ i, R i i‖ ≤ (Fintype.card (Coordinate N) : ℝ)*(2*A*C1+B*C0) := by
    apply (norm_sum_le _ _).trans
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hR i i)
  have hsumF : ‖∑ i, F i i‖ ≤ CΔ+(Fintype.card (Coordinate N) : ℝ)*(2*A*C1+B*C0) := by
    rw [hsum]
    exact (norm_add_le _ _).trans (add_le_add hΔ hsumR)
  have hfbound := weak_mixed_norm_le_laplacian (hD k) (hF k l)
    (distribution_laplacian_eq_sum_of_weakPartial D (fun i => F i i) hD (fun i => hF i i))
  have hsplit : M (e k l) = F k l-R k l := by dsimp [F]; abel
  have hh : ‖M (e k l)‖ ≤ ‖F k l‖+‖R k l‖ := hsplit ▸ norm_sub_le _ _
  change ‖M (e k l)‖ ≤ _
  nlinarith [hR k l]

#print axioms weak_weighted_mixed_bound
end TheoremT.Continuum
