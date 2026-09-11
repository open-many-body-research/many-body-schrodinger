import CollisionNull_v2

/-!
Exact permutation invariance of the original Coulomb potential on the actual
configuration space. The pair sum remains the original i < j sum; a proved
finite-sum identity permits reindexing without assuming a permutation preserves
the index order. Singular-point inverse conventions are retained unchanged.

Historical source context is recorded in CollisionNull_v2. No frozen or earlier
audit file is modified. This file does not assert weak-derivative covariance or
fermionic preservation of the full Hamiltonian output.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace TheoremT.Continuum

theorem position_permuteSpace {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) (i : Fin N) :
    position (permuteSpace π x) i = position x (π i) := by
  rfl

/-- Every symmetric real pair kernel vanishing on the diagonal satisfies the
ordered-versus-unordered counting identity. -/
theorem two_mul_strict_pair_sum {N : ℕ} (a : Fin N → Fin N → ℝ)
    (hsym : ∀ i j, a i j = a j i) (hdiag : ∀ i, a i i = 0) :
    2 * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j), a i j) =
      ∑ i : Fin N, ∑ j : Fin N, a i j := by
  have hterm (i j : Fin N) :
      a i j = (if i < j then a i j else 0) + (if j < i then a j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst j
      simp [hdiag]
    · simp [h, not_lt.mpr h.le, hsym]
  have hfull : (∑ i : Fin N, ∑ j : Fin N, a i j) =
      (∑ i : Fin N, ∑ j : Fin N, if i < j then a i j else 0) +
      (∑ i : Fin N, ∑ j : Fin N, if j < i then a j i else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hterm i j
  have hswap : (∑ i : Fin N, ∑ j : Fin N, if j < i then a j i else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if i < j then a i j else 0) := by
    rw [Finset.sum_comm]
  rw [hswap] at hfull
  simp only [Finset.sum_filter]
  linarith

/-- The original positive pair repulsion equals half the full ordered sum,
including on collisions because the totalized inverse of zero is zero. -/
theorem pair_repulsion_eq_half_ordered_sum {N : ℕ} (x : Configuration N) :
    (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
      ‖position x i - position x j‖⁻¹) =
      (1 / 2 : ℝ) * (∑ i : Fin N, ∑ j : Fin N,
        ‖position x i - position x j‖⁻¹) := by
  have h := two_mul_strict_pair_sum
    (fun i j : Fin N => ‖position x i - position x j‖⁻¹)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  linarith

/-- Permuting all electron positions preserves the potential pointwise,
without collision-free or charge restrictions. -/
theorem coulombPotential_permuteSpace {N : ℕ} (Z : ℝ)
    (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    coulombPotential N Z (permuteSpace π x) = coulombPotential N Z x := by
  unfold coulombPotential
  rw [pair_repulsion_eq_half_ordered_sum, pair_repulsion_eq_half_ordered_sum]
  simp only [position_permuteSpace]
  have hn : (∑ i : Fin N, ‖position x (π i)‖⁻¹) =
      ∑ i : Fin N, ‖position x i‖⁻¹ :=
    Equiv.sum_comp π (fun i : Fin N => ‖position x i‖⁻¹)
  have hp : (∑ i : Fin N, ∑ j : Fin N, ‖position x (π i) - position x (π j)‖⁻¹) =
      ∑ i : Fin N, ∑ j : Fin N, ‖position x i - position x j‖⁻¹ := by
    calc
      _ = ∑ i : Fin N, ∑ j : Fin N, ‖position x (π i) - position x j‖⁻¹ := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp π (fun j : Fin N => ‖position x (π i) - position x j‖⁻¹)
      _ = _ := Equiv.sum_comp π
        (fun i : Fin N => ∑ j : Fin N, ‖position x i - position x j‖⁻¹)
  rw [hn, hp]

theorem collisionFree_permuteSpace_iff {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) : collisionFree (permuteSpace π x) ↔ collisionFree x := by
  simp only [collisionFree, position_permuteSpace]
  constructor
  · rintro ⟨hn, hp⟩
    constructor
    · intro i
      simpa using hn (π.symm i)
    · intro i j hij
      have hne : π.symm i ≠ π.symm j := fun h => hij (π.symm.injective h)
      simpa using hp (π.symm i) (π.symm j) hne
  · rintro ⟨hn, hp⟩
    exact ⟨fun i => hn (π i), fun i j hij => hp (π i) (π j) (π.injective.ne hij)⟩

/-- The L2 quotient pullback has its expected representative almost everywhere. -/
theorem pullback_coeFn_ae {N : ℕ} (π : Equiv.Perm (Fin N)) (f : SpatialL2 N) :
    (fun x => pullback π f x) =ᵐ[volume] (fun x => f (permuteSpace π x)) :=
  Lp.coeFn_compMeasurePreserving f (permuteSpace π).measurePreserving

/-- Coulomb multiplication commutes with electron permutation whenever an L2
representative of the product exists. Existence for all H2 inputs is not assumed. -/
theorem coulomb_product_pullback {N : ℕ} {Z : ℝ}
    (π : Equiv.Perm (Fin N)) {f g : SpatialL2 N}
    (hg : ∀ᵐ x : Configuration N, g x = (coulombPotential N Z x : ℂ) * f x) :
    ∀ᵐ x : Configuration N,
      pullback π g x = (coulombPotential N Z x : ℂ) * pullback π f x := by
  have hcomp := (permuteSpace π).measurePreserving.quasiMeasurePreserving.ae hg
  filter_upwards [pullback_coeFn_ae π g, pullback_coeFn_ae π f, hcomp]
    with x hpg hpf hx
  rw [hpg, hpf]
  simpa only [coulombPotential_permuteSpace] using hx

/-- The Coulomb part preserves the full simultaneous spin-space fermionic
symmetry if each component product has an L2 representative. This is not a
claim that the product exists for every H2 spinor or that the full graph exists. -/
theorem coulomb_product_fermionic {N : ℕ} {Z : ℝ} {ψ χ : SpinSpace N}
    (hψ : ψ ∈ fermionicSubspace N)
    (hχ : ∀ σ, ∀ᵐ x : Configuration N,
      χ σ x = (coulombPotential N Z x : ℂ) * ψ σ x) :
    χ ∈ fermionicSubspace N := by
  intro π σ
  apply Lp.ext
  have hp := coulomb_product_pullback π (hχ (permuteSpin π σ))
  rw [hψ π σ] at hp
  filter_upwards [hp, Lp.coeFn_smul (permutationSign π) (ψ σ), hχ σ,
    Lp.coeFn_smul (permutationSign π) (χ σ)] with x hx hψx hχx hsx
  rw [hx, hψx, hsx]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hχx]
  ring

#print axioms position_permuteSpace
#print axioms two_mul_strict_pair_sum
#print axioms pair_repulsion_eq_half_ordered_sum
#print axioms coulombPotential_permuteSpace
#print axioms collisionFree_permuteSpace_iff
#print axioms pullback_coeFn_ae
#print axioms coulomb_product_pullback
#print axioms coulomb_product_fermionic

end TheoremT.Continuum
