import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! Explicit all-order Frechet estimates for complex formal multilinear series with
the literal coefficient budget M * choose(n+3,3). Translation on the quarter
ball is bounded by the exact geometric sum 16*M. The factorial comes from
the actual derivative permutation formula, and composition by an invertible
linear map retains one norm factor for every direction. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped NNReal ENNReal BigOperators
namespace ManyBody.S8.MixedAnalytic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def translationMajorant (p : FormalMultilinearSeries ℂ E F)
    (r s : ℝ≥0) : ℝ≥0 :=
  ∑' t : Σ k l : ℕ, {a : Finset (Fin (k+l)) // a.card=l},
    ‖p (t.1+t.2.1)‖₊ * r^t.2.1 * s^t.1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace F] in
theorem translationMajorant_eq (p : FormalMultilinearSeries ℂ E F)
    {r s : ℝ≥0} (hrs : (r+s : ℝ≥0∞) < p.radius) :
    translationMajorant p r s = ∑' n : ℕ, ‖p n‖₊ * (r+s)^n := by
  rw [translationMajorant, ← FormalMultilinearSeries.changeOriginIndexEquiv.symm.tsum_eq]
  dsimp only [Function.comp_def,
    FormalMultilinearSeries.changeOriginIndexEquiv_symm_apply_fst,
    FormalMultilinearSeries.changeOriginIndexEquiv_symm_apply_snd_fst]
  have hsum (n : ℕ) :
      HasSum (fun a : Finset (Fin n) =>
        ‖p (n-a.card+a.card)‖₊ * r^a.card * s^(n-a.card))
        (‖p n‖₊ * (r+s)^n) := by
    convert_to HasSum (fun a : Finset (Fin n) =>
        ‖p n‖₊ * (r^a.card * s^(n-a.card))) _ using 1
    · ext a
      rw [tsub_add_cancel_of_le (card_finset_fin_le a), mul_assoc]
    rw [← Fin.sum_pow_mul_eq_add_pow]
    exact (hasSum_fintype _).mul_left _
  have hs := p.changeOriginSeries_summable_aux₁ hrs
  rw [← FormalMultilinearSeries.changeOriginIndexEquiv.symm.summable_iff] at hs
  dsimp only [Function.comp_def,
    FormalMultilinearSeries.changeOriginIndexEquiv_symm_apply_fst,
    FormalMultilinearSeries.changeOriginIndexEquiv_symm_apply_snd_fst] at hs
  exact (hs.hasSum.sigma hsum).tsum_eq.symm

omit [CompleteSpace F] in
theorem changeOrigin_uniform_nnnorm
    (p : FormalMultilinearSeries ℂ E F) {r s : ℝ≥0}
    (hrs : (r+s : ℝ≥0∞) < p.radius) {x : E} (hx : ‖x‖₊ ≤ r) (k : ℕ) :
    ‖p.changeOrigin x k‖₊ * s^k ≤ translationMajorant p r s := by
  have hr : (r : ℝ≥0∞) < p.radius := (le_add_of_nonneg_right (by positivity)).trans_lt hrs
  have hxr : (‖x‖₊ : ℝ≥0∞) < p.radius := (ENNReal.coe_le_coe.mpr hx).trans_lt hr
  have hsum := p.changeOriginSeries_summable_aux₁ (r := r) (r' := s) hrs
  have hleft : Summable (fun t : Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l} =>
      ‖p (k+t.1)‖₊ * ‖x‖₊^t.1 * s^k) :=
    (p.changeOriginSeries_summable_aux₂ hxr k).mul_right (s^k)
  have hright : Summable (fun t : Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l} =>
      ‖p (k+t.1)‖₊ * r^t.1 * s^k) := (NNReal.summable_sigma.mp hsum).1 k
  let insertIndex : (Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l}) →
      (Σ k l : ℕ, {a : Finset (Fin (k+l)) // a.card=l}) := fun t => ⟨k,t⟩
  have hi : Function.Injective insertIndex := by
    intro a b hab
    exact eq_of_heq (Sigma.mk.inj_iff.mp hab).2
  calc
    ‖p.changeOrigin x k‖₊ * s^k ≤
        (∑' t : Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l},
          ‖p (k+t.1)‖₊ * ‖x‖₊^t.1) * s^k :=
      mul_le_mul_of_nonneg_right (p.nnnorm_changeOrigin_le k hxr) (by positivity)
    _ = ∑' t : Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l},
        ‖p (k+t.1)‖₊ * ‖x‖₊^t.1 * s^k := (NNReal.tsum_mul_right _ _).symm
    _ ≤ ∑' t : Σ l : ℕ, {a : Finset (Fin (k+l)) // a.card=l},
        ‖p (k+t.1)‖₊ * r^t.1 * s^k := by
      apply hleft.tsum_le_tsum _ hright
      intro t
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left' hx t.1) (by positivity)) (by positivity)
    _ ≤ translationMajorant p r s := by
      simpa only [insertIndex,translationMajorant] using
        NNReal.tsum_comp_le_tsum_of_inj (i := insertIndex) hsum hi

theorem norm_iteratedFDeriv_le_factorial_coeff
    {f : E → F} {p : FormalMultilinearSeries ℂ E F} {x : E} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x R) (k : ℕ) :
    ‖iteratedFDeriv ℂ k f x‖ ≤ (k.factorial : ℝ) * ‖p k‖ := by
  have heq : iteratedFDeriv ℂ k f x =
      ∑ sigma : Equiv.Perm (Fin k), (p k).domDomCongr sigma := by
    ext v
    simpa only [sum_apply, ContinuousMultilinearMap.domDomCongr_apply]
      using hf.iteratedFDeriv_eq_sum_of_completeSpace v
  rw [heq]
  calc
    ‖∑ sigma : Equiv.Perm (Fin k), (p k).domDomCongr sigma‖ ≤
        ∑ sigma : Equiv.Perm (Fin k), ‖(p k).domDomCongr sigma‖ := norm_sum_le _ _
    _ = (k.factorial : ℝ) * ‖p k‖ := by
      simp [ContinuousMultilinearMap.norm_domDomCongr, Fintype.card_perm]

#print axioms translationMajorant_eq
#print axioms changeOrigin_uniform_nnnorm
#print axioms norm_iteratedFDeriv_le_factorial_coeff

omit [CompleteSpace F] in
theorem radius_ge_three_quarters
    (p : FormalMultilinearSeries ℂ E F) {M : ℝ} (_hM : 0 ≤ M)
    (hp : ∀ n, ‖p n‖ ≤ M*((n+3).choose 3 : ℝ)) :
    ((3/4 : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
  apply p.le_radius_of_summable
  have hg := (summable_choose_mul_geometric_of_norm_lt_one 3
    (by norm_num : ‖(3/4 : ℝ)‖ < 1)).mul_left M
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hg
  simpa only [mul_assoc, NNReal.coe_div, NNReal.coe_ofNat] using
    mul_le_mul_of_nonneg_right (hp n) (by positivity : (0:ℝ) ≤ (3/4)^n)

omit [CompleteSpace F] in
theorem translationMajorant_quarter_le
    (p : FormalMultilinearSeries ℂ E F) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ n, ‖p n‖ ≤ M*((n+3).choose 3 : ℝ)) :
    (translationMajorant p (1/4) (1/4) : ℝ) ≤ 16*M := by
  have hrs : ((1/4:ℝ≥0)+(1/4:ℝ≥0) : ℝ≥0∞) < p.radius :=
    lt_of_lt_of_le (by exact_mod_cast (show (1/4:ℝ≥0)+(1/4:ℝ≥0) < (3/4:ℝ≥0) by norm_num)) (radius_ge_three_quarters p hM hp)
  rw [translationMajorant_eq p hrs, NNReal.coe_tsum]
  simp only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm,
    NNReal.coe_add, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  have hg := (summable_choose_mul_geometric_of_norm_lt_one 3
    (by norm_num : ‖(1/4+1/4 : ℝ)‖ < 1)).mul_left M
  calc
    ∑' n, ‖p n‖ * (1/4+1/4 : ℝ)^n ≤
        ∑' n, M*((n+3).choose 3 : ℝ)*(1/4+1/4 : ℝ)^n :=
      Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (hp n) (by positivity))
        (p.summable_norm_mul_pow hrs) (by simpa [mul_assoc] using hg)
    _ = 16*M := by
      simp_rw [mul_assoc]
      rw [tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one 3
        (by norm_num : ‖(1/4+1/4 : ℝ)‖ < 1)]
      ring

theorem iteratedFDeriv_sum_quarter_le
    (p : FormalMultilinearSeries ℂ E F) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ n, ‖p n‖ ≤ M*((n+3).choose 3 : ℝ))
    {x : E} (hx : ‖x‖ ≤ 1/4) (n : ℕ) :
    ‖iteratedFDeriv ℂ n p.sum x‖ ≤ 16*M*4^n*(n.factorial : ℝ) := by
  have hrs : ((1/4:ℝ≥0)+(1/4:ℝ≥0) : ℝ≥0∞) < p.radius :=
    lt_of_lt_of_le (by exact_mod_cast (show (1/4:ℝ≥0)+(1/4:ℝ≥0) < (3/4:ℝ≥0) by norm_num)) (radius_ge_three_quarters p hM hp)
  have hxNN : ‖x‖₊ ≤ (1/4:ℝ≥0) := by exact_mod_cast hx
  have hxr : (‖x‖₊ : ℝ≥0∞) < p.radius :=
    (ENNReal.coe_le_coe.mpr hxNN).trans_lt
      (lt_of_lt_of_le (by exact_mod_cast (show (1/4:ℝ≥0) < (3/4:ℝ≥0) by norm_num)) (radius_ge_three_quarters p hM hp))
  have hnorm : ‖p.changeOrigin x n‖ * (1/4 : ℝ)^n ≤ 16*M := by
    have h := changeOrigin_uniform_nnnorm p hrs hxNN n
    exact (show ‖p.changeOrigin x n‖ * (1/4 : ℝ)^n ≤
        (translationMajorant p (1/4) (1/4) : ℝ) by exact_mod_cast h).trans
      (translationMajorant_quarter_le p hM hp)
  have hc : ‖p.changeOrigin x n‖ ≤ 16*M*4^n := by
    have heq : (1/4 : ℝ)^n * 4^n = 1 := by rw [← mul_pow]; norm_num
    have h := mul_le_mul_of_nonneg_right hnorm (by positivity : (0:ℝ) ≤ 4^n)
    simpa only [mul_assoc, heq, mul_one] using h
  have hf := (p.hasFPowerSeriesOnBall hxr.pos).changeOrigin hxr
  have hd := norm_iteratedFDeriv_le_factorial_coeff (by simpa only [zero_add] using hf) n
  calc
    ‖iteratedFDeriv ℂ n p.sum x‖ ≤ (n.factorial : ℝ)*‖p.changeOrigin x n‖ := hd
    _ ≤ (n.factorial : ℝ)*(16*M*4^n) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

#print axioms radius_ge_three_quarters
#print axioms translationMajorant_quarter_le
#print axioms iteratedFDeriv_sum_quarter_le


variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace F] in
theorem iteratedFDeriv_comp_equiv
    (e : G ≃L[ℂ] E) (f : E → F) (x : G) (n : ℕ) :
    iteratedFDeriv ℂ n (f ∘ e) x =
      (iteratedFDeriv ℂ n f (e x)).compContinuousLinearMap (fun _ => e.toContinuousLinearMap) := by
  simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using
    e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (e x)) n

theorem iteratedFDeriv_sum_scaled_quarter_le
    (p : FormalMultilinearSeries ℂ E F) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ n, ‖p n‖ ≤ M*((n+3).choose 3 : ℝ))
    (e : G ≃L[ℂ] E) {x : G} (hx : ‖e x‖ ≤ 1/4) (n : ℕ) (v : Fin n → G) :
    ‖iteratedFDeriv ℂ n (p.sum ∘ e) x v‖ ≤
      16*M*4^n*(n.factorial : ℝ)*∏ i, ‖e (v i)‖ := by
  rw [iteratedFDeriv_comp_equiv, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact ((iteratedFDeriv ℂ n p.sum (e x)).le_opNorm (fun i => e (v i))).trans
    (mul_le_mul_of_nonneg_right (iteratedFDeriv_sum_quarter_le p hM hp hx n)
      (by positivity))

#print axioms iteratedFDeriv_comp_equiv
#print axioms iteratedFDeriv_sum_scaled_quarter_le

end ManyBody.S8.MixedAnalytic
