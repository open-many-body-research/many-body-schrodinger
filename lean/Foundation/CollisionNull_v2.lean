import ContinuumFoundation_v1
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
Collision nullity for the actual continuum configuration space, version 2.
This extends the preserved audit's ContinuumFoundation_v1 and changes no definitions.
The proofs use Lebesgue (Haar) measure on EuclideanSpace, not a discrete model.

Historical project context: THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md,
SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066,
commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660,
tag theorem-t-proof-freeze-2026-09-09. No proof claim from that report is assumed.
Actual imported definition source: post-freeze AUDIT_2026-09-09_v1/lean/
ContinuumFoundation_v1.lean, SHA-256
4404491d04595f9a4361b07371ebcb4d1e015c011000d0456d0455c67865698e.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace TheoremT.Continuum

/-- A single coordinate hyperplane has zero physical configuration volume. -/
theorem coordinate_hyperplane_null {N : ℕ} (k : Coordinate N) :
    volume {x : Configuration N | x k = 0} = 0 := by
  let ℓ : Configuration N →ₗ[ℝ] ℝ := (EuclideanSpace.proj k).toLinearMap
  have hproper : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have hv : coordinateVector k ∈ LinearMap.ker ℓ := by rw [h]; trivial
    have he : ℓ (coordinateVector k) = 0 := hv
    simp [ℓ, coordinateVector] at he
  exact Measure.addHaar_submodule volume (LinearMap.ker ℓ) hproper

/-- Equality of two distinct scalar coordinates defines a null hyperplane. -/
theorem coordinate_diagonal_null {N : ℕ} (k l : Coordinate N) (hkl : k ≠ l) :
    volume {x : Configuration N | x k = x l} = 0 := by
  let ℓ : Configuration N →ₗ[ℝ] ℝ :=
    (EuclideanSpace.proj k).toLinearMap - (EuclideanSpace.proj l).toLinearMap
  have hproper : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have hv : coordinateVector k ∈ LinearMap.ker ℓ := by rw [h]; trivial
    have he : ℓ (coordinateVector k) = 0 := hv
    simp [ℓ, coordinateVector, Ne.symm hkl] at he
  have hnull := Measure.addHaar_submodule volume (LinearMap.ker ℓ) hproper
  have hset : (LinearMap.ker ℓ : Set (Configuration N)) =
      {x : Configuration N | x k = x l} := by
    ext x
    change x k - x l = 0 ↔ x k = x l
    exact sub_eq_zero
  rw [hset] at hnull
  exact hnull

/-- An electron at the point nucleus is a Lebesgue-null configuration event. -/
theorem nuclear_collision_null {N : ℕ} (i : Fin N) :
    volume {x : Configuration N | position x i = 0} = 0 := by
  apply measure_mono_null (t := {x : Configuration N | x (i, 0) = 0})
  · intro x hx
    exact congrArg (fun v : Position => v 0) hx
  · exact coordinate_hyperplane_null (i, 0)

/-- Coincident positions of distinct electrons are a Lebesgue-null event. -/
theorem pair_collision_null {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    volume {x : Configuration N | position x i = position x j} = 0 := by
  apply measure_mono_null (t := {x : Configuration N | x (i, 0) = x (j, 0)})
  · intro x hx
    exact congrArg (fun v : Position => v 0) hx
  · exact coordinate_diagonal_null (i, 0) (j, 0) (by simpa using hij)

/-- Almost every physical configuration avoids all nuclear and pair collisions.
Includes the empty-electron case without a positivity hypothesis on N. -/
theorem ae_collisionFree (N : ℕ) :
    ∀ᵐ x : Configuration N, collisionFree x := by
  have hn : ∀ᵐ x : Configuration N, ∀ i, position x i ≠ 0 := by
    apply ae_all_iff.mpr
    intro i
    simpa only [ae_iff, not_not] using nuclear_collision_null i
  have hp : ∀ᵐ x : Configuration N, ∀ i j, i ≠ j → position x i ≠ position x j := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (by intro x h; exact (h hij).elim)
    · have h := pair_collision_null i j hij
      have ha : ∀ᵐ x : Configuration N, position x i ≠ position x j := by
        simpa only [ae_iff, not_not] using h
      exact ha.mono (fun x hx _ => hx)
  exact hn.and hp

theorem collision_set_null (N : ℕ) :
    volume {x : Configuration N | ¬collisionFree x} = 0 :=
  ae_iff.mp (ae_collisionFree N)

/-- Arbitrary definitions at collision points give the same almost-everywhere
representative if the functions agree on collision-free configurations. -/
theorem ae_eq_of_eq_on_collisionFree {N : ℕ} {α : Type*}
    {f g : Configuration N → α}
    (h : ∀ x, collisionFree x → f x = g x) : f =ᵐ[volume] g := by
  filter_upwards [ae_collisionFree N] with x hx using h x hx

/-- Multiplication by any collision-modified potential is the same a.e.
operation on every scalar wavefunction. This asserts no L2 integrability. -/
theorem coulomb_mul_ae_eq_of_collisionFree {N : ℕ} {Z : ℝ}
    (V : Configuration N → ℝ)
    (hV : ∀ x, collisionFree x → V x = coulombPotential N Z x)
    (f : Configuration N → ℂ) :
    (fun x => (V x : ℂ) * f x) =ᵐ[volume]
      (fun x => (coulombPotential N Z x : ℂ) * f x) := by
  apply ae_eq_of_eq_on_collisionFree
  intro x hx
  rw [hV x hx]

/-- Reading a physical electron position is continuous in the Euclidean topology. -/
theorem continuous_position {N : ℕ} (i : Fin N) :
    Continuous (fun x : Configuration N => position x i) := by
  unfold position
  fun_prop

/-- The totalized real Coulomb potential is Borel measurable on all configurations. -/
theorem measurable_coulombPotential (N : ℕ) (Z : ℝ) :
    Measurable (coulombPotential N Z) := by
  unfold coulombPotential
  apply Measurable.add
  · apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    exact (continuous_position i).measurable.norm.inv
  · apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact ((continuous_position i).sub (continuous_position j)).measurable.norm.inv

/-- Continuity is asserted precisely off the physical collision sets. -/
theorem continuousAt_coulombPotential {N : ℕ} (Z : ℝ) {x : Configuration N}
    (hx : collisionFree x) : ContinuousAt (coulombPotential N Z) x := by
  unfold coulombPotential
  apply ContinuousAt.add
  · apply ContinuousAt.const_mul
    apply tendsto_finsetSum
    intro i _
    exact (continuous_position i).continuousAt.norm.inv₀ (norm_ne_zero_iff.mpr (hx.1 i))
  · apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j hj
    have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
    exact ((continuous_position i).sub (continuous_position j)).continuousAt.norm.inv₀
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hx.2 i j hij)))

theorem continuousOn_coulombPotential (N : ℕ) (Z : ℝ) :
    ContinuousOn (coulombPotential N Z) {x | collisionFree x} :=
  fun _ hx => (continuousAt_coulombPotential Z hx).continuousWithinAt

/-- The exact scalar weak-derivative Hamiltonian graph is independent of all
pointwise conventions for the potential on collisions. No existence assertion
for the graph or Coulomb multiplication bound is used in this equivalence. -/
theorem scalarHamiltonianGraph_iff_collision_representative {N : ℕ} {Z : ℝ}
    (V : Configuration N → ℝ)
    (hV : ∀ x, collisionFree x → V x = coulombPotential N Z x)
    (f h : SpatialL2 N) :
    scalarHamiltonianGraph N Z f h ↔
      ∃ d : Coordinate N → SpatialL2 N,
      ∃ e : Coordinate N → Coordinate N → SpatialL2 N,
        (∀ k, WeakPartial f (d k) k) ∧
        (∀ k l, WeakPartial (d k) (e k l) l) ∧
        ∀ᵐ x : Configuration N,
          h x = (-((1 : ℂ) / 2)) * (∑ k, e k k x) + (V x : ℂ) * f x := by
  have hva := coulomb_mul_ae_eq_of_collisionFree V hV f
  constructor
  · rintro ⟨d, e, hd, he, hg⟩
    refine ⟨d, e, hd, he, ?_⟩
    filter_upwards [hg, hva] with x hx hmul
    rw [hmul]
    exact hx
  · rintro ⟨d, e, hd, he, hg⟩
    refine ⟨d, e, hd, he, ?_⟩
    filter_upwards [hg, hva] with x hx hmul
    rw [← hmul]
    exact hx

#print axioms coordinate_hyperplane_null
#print axioms coordinate_diagonal_null
#print axioms nuclear_collision_null
#print axioms pair_collision_null
#print axioms ae_collisionFree
#print axioms collision_set_null
#print axioms ae_eq_of_eq_on_collisionFree
#print axioms coulomb_mul_ae_eq_of_collisionFree
#print axioms continuous_position
#print axioms measurable_coulombPotential
#print axioms continuousAt_coulombPotential
#print axioms continuousOn_coulombPotential
#print axioms scalarHamiltonianGraph_iff_collision_representative

end TheoremT.Continuum
