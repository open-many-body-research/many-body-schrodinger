import ManyBody.S8.Internal.RealTaylorCoefficientMagnitude
import ManyBody.S8.Internal.DyadicDistanceRounding
import ManyBody.S8.Internal.RealRationalAmbientProfile
import Mathlib.Algebra.Order.Archimedean.Basic
/-! True raw integer numerator bounds for the literal dyadic Taylor dictionary.

The genuine center jet bound is derived from actual complex Taylor data and
real derivative transport. Fixed dyadic growth/amplitude offsets precede all
Taylor orders, denominator exponents and monomials; a common pair of offsets
controls all three actual profiles. No coefficient evaluation algorithm or
reduced rational numerator convention is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ManyBody.S8

def realTaylorDyadicRawNumerator (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ)
    (N b : ℕ) (α : DistanceMultiIndex) : ℤ :=
  ⌊(2:ℝ)^b*realTaylorDistanceDictionaryCoefficient f a N α⌋

theorem floor_abs_le_abs_add_one (x : ℝ) :
    |(⌊x⌋ : ℝ)| ≤ |x|+1 := by
  apply abs_le.mpr
  constructor
  · have hh := Int.lt_floor_add_one x
    linarith [neg_abs_le x]
  · exact (Int.floor_le x).trans (by linarith [le_abs_self x])

theorem realTaylorDyadicRawNumerator_dyadic_bound
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hjet : ∀ n, ‖iteratedFDeriv ℝ n f a‖ ≤ M*L^n*(n.factorial:ℝ)) :
    ∃ k k0 : ℕ, ∀ N b : ℕ, ∀ α : DistanceMultiIndex,
      (realTaylorDyadicRawNumerator f a N b α).natAbs ≤
        2^(b+(k+1)*N+k0+1) := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt
    (realTaylorCoefficientGrowthBase L a) (by norm_num : (1:ℝ)<2)
  obtain ⟨k0,hk0⟩ := pow_unbounded_of_one_lt M (by norm_num : (1:ℝ)<2)
  refine ⟨k,k0,?_⟩
  intro N b α
  have hcoef := realTaylorDistanceDictionaryCoefficient_bound f a hM hL hjet N α
  have hN : (N:ℝ) ≤ (2:ℝ)^N := by
    exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
  have hbase := pow_le_pow_left₀
    ((by norm_num : (0:ℝ)≤1).trans (realTaylorCoefficientGrowthBase_one_le L a)) hk.le N
  have hcb : |realTaylorDistanceDictionaryCoefficient f a N α| ≤
      (2:ℝ)^(k0+(k+1)*N) := by
    calc
      _ ≤ M*N*(realTaylorCoefficientGrowthBase L a)^N := hcoef
      _ ≤ (2:ℝ)^k0*(2:ℝ)^N*((2:ℝ)^k)^N :=
        mul_le_mul (mul_le_mul hk0.le hN (by positivity) (by positivity))
          hbase (pow_nonneg ((by norm_num : (0:ℝ)≤1).trans
            (realTaylorCoefficientGrowthBase_one_le L a)) N) (by positivity)
      _ = (2:ℝ)^(k0+(k+1)*N) := by
        rw [←pow_mul,←pow_add,←pow_add]
        congr 1
        ring
  have hfloor := floor_abs_le_abs_add_one
    ((2:ℝ)^b*realTaylorDistanceDictionaryCoefficient f a N α)
  have hraw : |(realTaylorDyadicRawNumerator f a N b α:ℝ)| ≤
      (2:ℝ)^(b+(k+1)*N+k0+1) := by
    apply hfloor.trans
    rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(2:ℝ)^b)]
    calc
      _ ≤ (2:ℝ)^b*(2:ℝ)^(k0+(k+1)*N)+1 :=
        add_le_add (mul_le_mul_of_nonneg_left hcb (by positivity : (0:ℝ)≤(2:ℝ)^b)) le_rfl
      _ = (2:ℝ)^(b+(k+1)*N+k0)+1 := by
        rw [←pow_add]
        congr 2
        omega
      _ ≤ (2:ℝ)^(b+(k+1)*N+k0+1) := by
        rw [pow_succ]
        have hp : (1:ℝ) ≤ 2^(b+(k+1)*N+k0) := one_le_pow₀ (by norm_num)
        linarith
  have hcast : ((realTaylorDyadicRawNumerator f a N b α).natAbs:ℝ) =
      |(realTaylorDyadicRawNumerator f a N b α:ℝ)| := by
    rw [Nat.cast_natAbs,Int.cast_abs]
  rw [←hcast] at hraw
  exact_mod_cast hraw

theorem ambientRealScalarProfile_center_jet_bound
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R C : ℝ} (hR : 0<R)
    (hdata : ComplexDistanceTaylorData h (ambientRealCast a) R C) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (ambientRealScalarProfile h) a‖ ≤
      (3*|C|)*(2*Real.exp 1/R)^n*(n.factorial:ℝ) := by
  have hf : AnalyticAt ℂ h (ambientRealCast a) :=
    ⟨hdata.1.choose,hdata.1.choose_spec.1⟩
  have hb := (hdata.2.2 n (ambientRealCast a) (by simp; linarith)).2 0
  have hb' : ‖iteratedFDeriv ℂ n h (ambientRealCast a)‖ ≤
      3*C*(2*Real.exp 1/R)^n*(n.factorial:ℝ) := by
    simpa [complexTaylorPolynomial] using hb
  have hr' : ‖iteratedFDeriv ℝ n (ambientRealScalarProfile h) a‖ ≤
      ‖iteratedFDeriv ℂ n h (ambientRealCast a)‖ := by
    apply (iteratedFDeriv ℝ n (ambientRealScalarProfile h) a).opNorm_le_bound (norm_nonneg _)
    intro v
    rw [ambientRealScalarProfile_iteratedFDeriv hf]
    calc
      _ ≤ ‖iteratedFDeriv ℂ n h (ambientRealCast a) (fun j => ambientRealCast (v j))‖ :=
        by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _
      _ ≤ _ := by
        simpa only [ambientRealCast_norm] using
          (iteratedFDeriv ℂ n h (ambientRealCast a)).le_opNorm (fun j => ambientRealCast (v j))
  apply (hr'.trans hb').trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self C) (by norm_num))
      (by positivity)) (by positivity)


theorem ambientRealScalarProfile_dyadic_raw_numerator_bound
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R C : ℝ} (hR : 0<R)
    (hdata : ComplexDistanceTaylorData h (ambientRealCast a) R C) :
    ∃ k k0 : ℕ, ∀ N b : ℕ, ∀ α : DistanceMultiIndex,
      (realTaylorDyadicRawNumerator (ambientRealScalarProfile h) a N b α).natAbs ≤
        2^(b+(k+1)*N+k0+1) :=
  realTaylorDyadicRawNumerator_dyadic_bound _ a (by positivity) (by positivity)
    (ambientRealScalarProfile_center_jet_bound hR hdata)

theorem realTaylor_dyadic_grid_raw_numerator
    (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ) (N b : ℕ) (α : DistanceMultiIndex) :
    dyadicDistanceCoefficient b (realTaylorDistanceDictionaryCoefficient f a N α)*(2:ℚ)^b =
      (realTaylorDyadicRawNumerator f a N b α:ℚ) := by
  unfold dyadicDistanceCoefficient realTaylorDyadicRawNumerator
  exact div_mul_cancel₀ _ (pow_ne_zero b (by norm_num))

def RealThreeProfilesDyadicNumeratorData (a b h : (Fin 3 → ℂ) → ℂ)
    (center : Fin 3 → ℝ) : Prop :=
  let fs : Fin 3 → (Fin 3 → ℂ) → ℂ := ![a,b,h]
  ∃ k k0 : ℕ, ∀ N bits : ℕ, ∀ j : Fin 3, ∀ α : DistanceMultiIndex,
    (realTaylorDyadicRawNumerator (ambientRealScalarProfile (fs j)) center N bits α).natAbs ≤
      2^(bits+(k+1)*N+k0+1)

theorem real_three_profiles_dyadic_raw_numerator
    {a b h : (Fin 3 → ℂ) → ℂ} {center : Fin 3 → ℝ} {R : ℝ}
    (C : Fin 3 → ℝ) (hR : 0<R)
    (hdata : ∀ j : Fin 3, ComplexDistanceTaylorData (![a,b,h] j) (ambientRealCast center) R (C j)) :
    RealThreeProfilesDyadicNumeratorData a b h center := by
  classical
  have hex (j : Fin 3) := ambientRealScalarProfile_dyadic_raw_numerator_bound hR (hdata j)
  choose k k0 hk using hex
  let K := Finset.univ.sup k
  let K0 := Finset.univ.sup k0
  refine ⟨K,K0,?_⟩
  intro N bits j α
  have hkj : k j≤K := Finset.le_sup (f:=k) (Finset.mem_univ j)
  have hk0j : k0 j≤K0 := Finset.le_sup (f:=k0) (Finset.mem_univ j)
  have hm := Nat.mul_le_mul_right N (Nat.add_le_add_right hkj 1)
  exact (hk j N bits α).trans (Nat.pow_le_pow_right (by omega : 1≤2) (by omega))

theorem dyadic_raw_numerator_schedule_exponent (p m k k0 : ℕ) :
    (15*p+7*m+33)+(k+1)*(2*p+m+4)+k0+1 =
      (2*k+17)*p+(k+8)*m+4*k+k0+38 := by ring

#print axioms dyadic_raw_numerator_schedule_exponent
#print axioms real_three_profiles_dyadic_raw_numerator
#print axioms realTaylor_dyadic_grid_raw_numerator
#print axioms realTaylorDyadicRawNumerator_dyadic_bound
#print axioms ambientRealScalarProfile_center_jet_bound
end ManyBody.S8
