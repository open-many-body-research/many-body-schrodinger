import HardyH1ClosedGraph_v1

/-! Quantitative equivalence of the shifted actual Coulomb quadratic form and
the genuine first-weak-derivative Hilbert norm. This is uniform in the vector;
its explicit constant depends on N and Z. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

def h1FormShift (N : ℕ) (Z : ℝ) : ℝ :=
  1 + (2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)))^2

def h1FormNormUpper (N : ℕ) (Z : ℝ) : ℝ :=
  1 + 2 * (2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)))^2

theorem coulombH1Energy_shift_bounds {N : ℕ} (Z : ℝ) (ψ : SpinSpace N)
    (d : Coordinate N → SpinSpace N) (v : SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) :
    (1 / 4 : ℝ) * (‖ψ‖^2 + ∑ k, ‖d k‖^2) ≤
        coulombH1Energy ψ d v + h1FormShift N Z * ‖ψ‖^2 ∧
      coulombH1Energy ψ d v + h1FormShift N Z * ‖ψ‖^2 ≤
        h1FormNormUpper N Z * (‖ψ‖^2 + ∑ k, ‖d k‖^2) := by
  let D : ℝ := ∑ k : Coordinate N, ‖d k‖^2
  let C : ℝ := 2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ))
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ => sq_nonneg ‖d k‖)
  have hV : ‖v‖ ≤ C * Real.sqrt D := coulomb_product_spin_norm_le Z ψ d hd v hv
  have hi := abs_real_inner_le_norm ψ v
  have hn := mul_le_mul_of_nonneg_left hV (norm_nonneg ψ)
  have hs := sq_nonneg (Real.sqrt D / 2 - C * ‖ψ‖)
  simp only [sub_sq, div_pow, mul_pow, Real.sq_sqrt hD] at hs
  have hab : |inner ℝ ψ v| ≤ D / 4 + C^2 * ‖ψ‖^2 := by nlinarith
  have hlo := neg_le_of_abs_le hab
  have hup := le_of_abs_le hab
  change (1 / 4 : ℝ) * (‖ψ‖^2 + D) ≤
      (1 / 2 : ℝ) * D + inner ℝ ψ v + (1 + C^2) * ‖ψ‖^2 ∧
    (1 / 2 : ℝ) * D + inner ℝ ψ v + (1 + C^2) * ‖ψ‖^2 ≤
      (1 + 2 * C^2) * (‖ψ‖^2 + D)
  constructor
  · nlinarith [sq_nonneg ‖ψ‖]
  · nlinarith [mul_nonneg (sq_nonneg C) hD]

/-- Quantitative comparison on the actual complete fermionic weak-H¹ graph.
The supplied q is only required to be the already verified physical form value. -/
theorem fermionicH1Graph_form_shift_bounds {N : ℕ} {Z q : ℝ}
    (a : fermionicH1Graph N) (hq : coulombH1FormValue N Z (a.val none) q) :
    (1 / 4 : ℝ) * ‖a‖^2 ≤ q + h1FormShift N Z * ‖a.val none‖^2 ∧
      q + h1FormShift N Z * ‖a.val none‖^2 ≤ h1FormNormUpper N Z * ‖a‖^2 := by
  obtain ⟨_, d, v, hd, hv, rfl⟩ := hq
  have heq : d = fun k => a.val (some k) := spin_weak_derivative_unique hd a.property.2
  subst d
  rw [fermionicH1Graph_norm_sq]
  exact coulombH1Energy_shift_bounds Z _ _ _ a.property.2 hv

def fermionicH1FormEnergy {N : ℕ} (Z : ℝ) (a : fermionicH1Graph N) : ℝ :=
  Classical.choose ((coulombH1FormValue_exists_iff Z (a.val none)).mpr
    (fermionicH1Graph_value_mem a))

theorem fermionicH1FormEnergy_spec {N : ℕ} (Z : ℝ) (a : fermionicH1Graph N) :
    coulombH1FormValue N Z (a.val none) (fermionicH1FormEnergy Z a) :=
  Classical.choose_spec ((coulombH1FormValue_exists_iff Z (a.val none)).mpr
    (fermionicH1Graph_value_mem a))

theorem fermionicH1FormEnergy_shift_bounds {N : ℕ} (Z : ℝ) (a : fermionicH1Graph N) :
    (1 / 4 : ℝ) * ‖a‖^2 ≤
        fermionicH1FormEnergy Z a + h1FormShift N Z * ‖a.val none‖^2 ∧
      fermionicH1FormEnergy Z a + h1FormShift N Z * ‖a.val none‖^2 ≤
        h1FormNormUpper N Z * ‖a‖^2 :=
  fermionicH1Graph_form_shift_bounds a (fermionicH1FormEnergy_spec Z a)

#print axioms coulombH1Energy_shift_bounds
#print axioms fermionicH1Graph_form_shift_bounds
#print axioms fermionicH1FormEnergy_spec
#print axioms fermionicH1FormEnergy_shift_bounds
end TheoremT.Continuum
