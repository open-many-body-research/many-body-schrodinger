import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact positive-rate exponential radial moments, improper tails, and the two-radius Newton integral. All interval splits and integral subtraction use proved integrability. These are analytic identities, without any assumed physical moment. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ManyBody.S2.Internal.ExponentialRadial

theorem integrable_moment (n : ℕ) (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => r^n * Real.exp (-b*r)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n : ℝ)) (p := 1) (b := b) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) (by norm_num) hb
  simpa only [Real.rpow_natCast,Real.rpow_one] using h

theorem integral_moment (n : ℕ) (b : ℝ) (hb : 0 < b) :
    (∫ r : ℝ in Ioi 0, r^n * Real.exp (-b*r)) =
      (n.factorial : ℝ)/b^(n+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ)+1) (r := b) (by positivity) hb
  simp only [add_sub_cancel_right,Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial,← neg_mul] at h
  rw [h]
  have he : (n : ℝ)+1 = ((n+1 : ℕ) : ℝ) := by simp
  rw [he,Real.rpow_natCast]
  simp only [div_pow,one_pow]
  ring

theorem tendsto_moment_zero (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun r : ℝ => r^n * Real.exp (-b*r)) atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast] using
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) b hb

theorem integral_tail_one (b : ℝ) (hb : 0 < b) (s : ℝ) (hs : 0 ≤ s) :
    (∫ r : ℝ in Ioi s, r * Real.exp (-b*r)) =
      Real.exp (-b*s) * (s/b+1/b^2) := by
  have hd (r : ℝ) (_hr : r ∈ Ici s) :
      HasDerivAt (fun r : ℝ => -(Real.exp (-b*r)*(r/b+1/b^2)))
        (r*Real.exp (-b*r)) r := by
    have h := (((hasDerivAt_id r).const_mul (-b)).exp).mul
      (((hasDerivAt_id r).div_const b).add_const (1/b^2))
    convert! h.neg using 1
    dsimp
    field_simp [hb.ne']
    ring
  have hi : IntegrableOn (fun r : ℝ => r*Real.exp (-b*r)) (Ioi s) := by
    simpa only [pow_one] using (integrable_moment 1 b hb).mono_set (Ioi_subset_Ioi hs)
  have ht : Tendsto (fun r : ℝ => -(Real.exp (-b*r)*(r/b+1/b^2))) atTop (𝓝 0) := by
    have h := ((tendsto_moment_zero 1 b hb).div_const b).add
      ((tendsto_moment_zero 0 b hb).div_const (b^2))
    convert! h.neg using 1
    · funext r
      simp only [pow_one,pow_zero,one_mul]
      ring
    · simp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  simpa using h

theorem integral_tail_two (b : ℝ) (hb : 0 < b) (s : ℝ) (hs : 0 ≤ s) :
    (∫ r : ℝ in Ioi s, r^2 * Real.exp (-b*r)) =
      Real.exp (-b*s) * (s^2/b+2*s/b^2+2/b^3) := by
  have hd (r : ℝ) (_hr : r ∈ Ici s) :
      HasDerivAt (fun r : ℝ => -(Real.exp (-b*r)*(r^2/b+2*r/b^2+2/b^3)))
        (r^2*Real.exp (-b*r)) r := by
    have h := (((hasDerivAt_id r).const_mul (-b)).exp).mul
      ((((hasDerivAt_pow 2 r).div_const b).add
        (((hasDerivAt_id r).const_mul 2).div_const (b^2))).add_const (2/b^3))
    convert! h.neg using 1
    dsimp
    field_simp [hb.ne']
    ring
  have hi := (integrable_moment 2 b hb).mono_set (Ioi_subset_Ioi hs)
  have ht : Tendsto (fun r : ℝ => -(Real.exp (-b*r)*(r^2/b+2*r/b^2+2/b^3))) atTop (𝓝 0) := by
    have h := (((tendsto_moment_zero 2 b hb).div_const b).add
      (((tendsto_moment_zero 1 b hb).const_mul 2).div_const (b^2))).add
      (((tendsto_moment_zero 0 b hb).const_mul 2).div_const (b^3))
    convert! h.neg using 1
    · funext r
      simp only [pow_one,pow_zero,one_mul]
      ring
    · simp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  simpa using h

#print axioms integral_moment
#print axioms integral_tail_one
#print axioms integral_tail_two

/-- The exact radial Newton potential for an unnormalized exponential density. -/
theorem integral_newton_radial (b : ℝ) (hb : 0 < b) (s : ℝ) (hs : 0 < s) :
    (∫ r : ℝ in Ioi 0, r^2*Real.exp (-b*r)/max r s) =
      2/(b^3*s)-Real.exp (-b*s)*(1/b^2+2/(b^3*s)) := by
  let F := fun r : ℝ => r^2*Real.exp (-b*r)/max r s
  have hl : IntegrableOn F (Ioc 0 s) := by
    have hi : IntegrableOn (fun r : ℝ => r^2*Real.exp (-b*r)/s) (Ioc 0 s) :=
      ((integrable_moment 2 b hb).mono_set Ioc_subset_Ioi_self).div_const s
    apply hi.congr_fun _ measurableSet_Ioc
    intro r hr
    dsimp [F]
    rw [max_eq_right hr.2]
  have hh : IntegrableOn F (Ioi s) := by
    have h := (integrable_moment 1 b hb).mono_set (Ioi_subset_Ioi hs.le)
    apply h.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp [F]
    rw [max_eq_left hr.le]
    have h0 : r ≠ 0 := (hs.trans hr).ne'
    field_simp [h0]
  have hu := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hl hh
  rw [Ioc_union_Ioi_eq_Ioi hs.le] at hu
  have heL : (∫ r : ℝ in Ioc 0 s, F r) =
      (1/s) * ∫ r : ℝ in Ioc 0 s, r^2*Real.exp (-b*r) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp [F]
    rw [max_eq_right hr.2]
    ring
  have heH : (∫ r : ℝ in Ioi s, F r) =
      ∫ r : ℝ in Ioi s, r*Real.exp (-b*r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp [F]
    rw [max_eq_left hr.le]
    have h0 : r ≠ 0 := (hs.trans hr).ne'
    field_simp [h0]
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (integrable_moment 2 b hb) ((integrable_moment 2 b hb).mono_set (Ioi_subset_Ioi hs.le))
  rw [intervalIntegral.integral_of_le hs.le,integral_moment 2 b hb,
    integral_tail_two b hb s hs.le] at hsplit
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.reduceAdd] at hsplit
  have hlow : (∫ r : ℝ in Ioc 0 s, r^2*Real.exp (-b*r)) =
      2/b^3-Real.exp (-b*s)*(s^2/b+2*s/b^2+2/b^3) := by linarith
  change (∫ r : ℝ in Ioi 0, F r) = _
  rw [hu,heL,heH,hlow,integral_tail_one b hb s hs.le]
  field_simp [hb.ne',hs.ne']
  ring

#print axioms integral_newton_radial

/-- The exact two-radius Coulomb exponential integral. -/
theorem integral_newton_double_radial (b : ℝ) (hb : 0 < b) :
    (∫ s : ℝ in Ioi 0, s^2*Real.exp (-b*s) *
      ∫ r : ℝ in Ioi 0, r^2*Real.exp (-b*r)/max r s) = 5/(4*b^5) := by
  let G := fun s : ℝ => (2/b^3)*(s*Real.exp (-b*s)) -
    (1/b^2)*(s^2*Real.exp (-(2*b)*s)) - (2/b^3)*(s*Real.exp (-(2*b)*s))
  have he : (∫ s : ℝ in Ioi 0, s^2*Real.exp (-b*s) *
      ∫ r : ℝ in Ioi 0, r^2*Real.exp (-b*r)/max r s) =
      ∫ s : ℝ in Ioi 0, G s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [integral_newton_radial b hb s hs]
    have hpow : Real.exp (-b*s)*Real.exp (-b*s) = Real.exp (-(2*b)*s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp [G]
    rw [← hpow]
    field_simp [hb.ne',(mem_Ioi.mp hs).ne']
    ring
  have hi1 : IntegrableOn (fun s : ℝ => s*Real.exp (-b*s)) (Ioi 0) := by
    simpa only [pow_one] using integrable_moment 1 b hb
  have hi2 := integrable_moment 2 (2*b) (by positivity : 0 < 2*b)
  have hi3 : IntegrableOn (fun s : ℝ => s*Real.exp (-(2*b)*s)) (Ioi 0) := by
    simpa only [pow_one] using integrable_moment 1 (2*b) (by positivity : 0 < 2*b)
  rw [he]
  dsimp only [G]
  have hsub1 := integral_sub ((hi1.const_mul (2/b^3)).sub (hi2.const_mul (1/b^2)))
    (hi3.const_mul (2/b^3))
  have hsub2 := integral_sub (hi1.const_mul (2/b^3)) (hi2.const_mul (1/b^2))
  dsimp only [Pi.sub_apply] at hsub1 hsub2
  rw [hsub1,hsub2,integral_const_mul,integral_const_mul,integral_const_mul]
  have h1 := integral_moment 1 b hb
  have h3 := integral_moment 1 (2*b) (by positivity : 0 < 2*b)
  simp only [pow_one] at h1 h3
  rw [h1,integral_moment 2 (2*b) (by positivity),h3]
  norm_num only [Nat.factorial,Nat.cast_ofNat,Nat.reduceAdd]
  field_simp [hb.ne']
  ring

#print axioms integral_newton_double_radial
end ManyBody.S2.Internal.ExponentialRadial