import DirectionalCoulombNorm_v1

/-! Finite spin summation preserves the sqrt(N) Coulomb multiplier coefficient
in the exact PiLp 2 norm of the physical spin space. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

/-- A quantitative bound on the full finite fermionic spin ambient space,
before restricting to its antisymmetric subspace. The spin multiplicity costs
no extra factor because its norm is the sum-of-squares norm. -/
theorem coulomb_product_spin_directional_norm_le {N : ℕ} (Z : ℝ)
    (ψ : SpinSpace N) (d : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (v : SpinSpace N)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) :
    ‖v‖ ≤ (Real.sqrt (N : ℝ) * (2*|Z| + (N : ℝ) - 1)) *
      Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) := by
  let C : ℝ := (Real.sqrt (N : ℝ) * (2*|Z| + (N : ℝ) - 1))
  have hC : 0 ≤ C := coulomb_directional_coefficient_nonneg N Z
  have hσ (σ : SpinConfiguration N) :
      ‖v σ‖^2 ≤ C^2 * (∑ k : Coordinate N, ‖d k σ‖^2) := by
    have h := coulomb_product_directional_norm_le Z (ψ σ) (fun k => d k σ) (hd σ) (v σ) (hv σ)
    have hh := pow_le_pow_left₀ (norm_nonneg (v σ)) h 2
    have hDσ : 0 ≤ ∑ k : Coordinate N, ‖d k σ‖^2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg ‖d k σ‖)
    simpa only [C, mul_pow, Real.sq_sqrt hDσ]
      using hh
  have hsum : ‖v‖^2 ≤ C^2 * (∑ k : Coordinate N, ‖d k‖^2) := by
    calc
      ‖v‖^2 = ∑ σ : SpinConfiguration N, ‖v σ‖^2 := PiLp.norm_sq_eq_of_L2 _ v
      _ ≤ ∑ σ : SpinConfiguration N, C^2 * (∑ k : Coordinate N, ‖d k σ‖^2) :=
        Finset.sum_le_sum (fun σ _ => hσ σ)
      _ = C^2 * (∑ k : Coordinate N, ‖d k‖^2) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [← PiLp.norm_sq_eq_of_L2]
  have hD : 0 ≤ ∑ k : Coordinate N, ‖d k‖^2 := Finset.sum_nonneg (fun k _ => sq_nonneg ‖d k‖)
  have hs := Real.sq_sqrt hD
  have hn := Real.sqrt_nonneg (∑ k : Coordinate N, ‖d k‖^2)
  change ‖v‖ ≤ C * Real.sqrt (∑ k : Coordinate N, ‖d k‖^2)
  nlinarith [norm_nonneg v, mul_nonneg hC hn]

/-- Existence of an actual full-spin L² Coulomb product with the proved bound.
This is a mathematical L² construction, not a claim of an executable numerical solver. -/
theorem spin_coulomb_product_exists_directional_bound {N : ℕ} (Z : ℝ)
    (ψ : SpinSpace N) (d : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k) :
    ∃ v : SpinSpace N,
      (∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) ∧
      ‖v‖ ≤ (Real.sqrt (N : ℝ) * (2*|Z| + (N : ℝ) - 1)) *
        Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) := by
  let hm := fun σ => coulombProductL2_of_hasH1 Z ⟨fun k => d k σ, hd σ⟩
  let v : SpinSpace N := WithLp.toLp 2 (fun σ => (hm σ).toLp
    (fun x => (coulombPotential N Z x : ℂ) * ψ σ x))
  have hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x :=
    fun σ => (hm σ).coeFn_toLp
  exact ⟨v, hv, coulomb_product_spin_directional_norm_le Z ψ d hd v hv⟩

/-- Exact displayed specification coefficient on the full finite spin space. -/
theorem coulomb_product_spin_specification_norm_le {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z)
    (ψ : SpinSpace N) (d : Coordinate N → SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (v : SpinSpace N)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) :
    ‖v‖ ≤ (Real.sqrt (N : ℝ) * (2*Z + (N : ℝ) - 1)) *
      Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) := by
  simpa only [abs_of_nonneg hZ] using
    coulomb_product_spin_directional_norm_le Z ψ d hd v hv

#print axioms coulomb_product_spin_directional_norm_le
#print axioms spin_coulomb_product_exists_directional_bound
#print axioms coulomb_product_spin_specification_norm_le
end TheoremT.Continuum
