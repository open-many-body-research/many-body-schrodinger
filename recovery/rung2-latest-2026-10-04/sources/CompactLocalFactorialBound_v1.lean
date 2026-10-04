import FiniteFactorialMajorant_v1
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Basic

/-! Conditional finite-cover assembly of local factorial bounds. The family
J need not be continuous, and its normed target may depend on the order k.
All analytic content remains in the explicit neighborhood-bound hypotheses.
The finite positive-sum majorants work also for an empty compact set. -/
noncomputable section
open scoped Topology BigOperators
namespace TheoremT.Continuum

theorem compact_factorial_bound_of_neighborhood_family
    {X : Type*} [TopologicalSpace X] {F : ℕ → Type*} [∀ k, Norm (F k)]
    {K : Set X} (hK : IsCompact K) (J : ∀ k, X → F k)
    (U : K → Set X) (C A : K → ℝ)
    (hU : ∀ x : K, U x ∈ 𝓝 (x : X))
    (hC : ∀ x : K, 0 ≤ C x) (hA : ∀ x : K, 0 ≤ A x)
    (hJ : ∀ x : K, ∀ y ∈ U x, ∀ k,
      ‖J k y‖ ≤ C x * A x ^ k * (k.factorial : ℝ)) :
    ∃ s : Finset K, (⋃ x ∈ s, U x) ∈ 𝓝ˢ K ∧
      1 ≤ finiteFactorialC s C ∧ 1 ≤ finiteFactorialA s A ∧
      ∀ y ∈ ⋃ x ∈ s, U x, ∀ k,
        ‖J k y‖ ≤ finiteFactorialC s C * finiteFactorialA s A ^ k * (k.factorial : ℝ) := by
  classical
  obtain ⟨s,hs⟩ := hK.elim_nhds_subcover_nhdsSet'
    (fun x hx => U ⟨x,hx⟩) (fun x hx => hU ⟨x,hx⟩)
  obtain ⟨hCs,hAs,hmajor⟩ := finite_factorial_common_bound s C A
    (fun x _ => hC x) (fun x _ => hA x)
  refine ⟨s,hs,hCs,hAs,?_⟩
  intro y hy k
  obtain ⟨x,hxs,hyx⟩ := Set.mem_iUnion₂.mp hy
  exact (hJ x y hyx k).trans (hmajor x hxs k)

theorem compact_local_factorial_bound_uniform_nhds
    {X : Type*} [TopologicalSpace X] {F : ℕ → Type*} [∀ k, Norm (F k)]
    {K : Set X} (hK : IsCompact K) (J : ∀ k, X → F k)
    (hlocal : ∀ x ∈ K, ∃ U : Set X, U ∈ 𝓝 x ∧
      ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
        ∀ y ∈ U, ∀ k, ‖J k y‖ ≤ C * A ^ k * (k.factorial : ℝ)) :
    ∃ U : Set X, U ∈ 𝓝ˢ K ∧ ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ y ∈ U, ∀ k, ‖J k y‖ ≤ C * A ^ k * (k.factorial : ℝ) := by
  classical
  have hl : ∀ x : K, ∃ U : Set X, U ∈ 𝓝 (x : X) ∧
      ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
        ∀ y ∈ U, ∀ k, ‖J k y‖ ≤ C * A ^ k * (k.factorial : ℝ) :=
    fun x => hlocal x x.property
  choose U hU C A hC hA hJ using hl
  obtain ⟨s,hs,hCs,hAs,hbound⟩ := compact_factorial_bound_of_neighborhood_family hK J U C A
    hU (fun x => (hC x).le) (fun x => (hA x).le) hJ
  exact ⟨⋃ x ∈ s, U x,hs,finiteFactorialC s C,finiteFactorialA s A,hCs,hAs,hbound⟩

theorem compact_local_factorial_bound_uniform
    {X : Type*} [TopologicalSpace X] {F : ℕ → Type*} [∀ k, Norm (F k)]
    {K : Set X} (hK : IsCompact K) (J : ∀ k, X → F k)
    (hlocal : ∀ x ∈ K, ∃ U : Set X, U ∈ 𝓝 x ∧
      ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
        ∀ y ∈ U, ∀ k, ‖J k y‖ ≤ C * A ^ k * (k.factorial : ℝ)) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ x ∈ K, ∀ k, ‖J k x‖ ≤ C * A ^ k * (k.factorial : ℝ) := by
  obtain ⟨U,hU,C,A,hC,hA,hbound⟩ := compact_local_factorial_bound_uniform_nhds hK J hlocal
  exact ⟨C,A,hC,hA,fun x hx k => hbound x (subset_of_mem_nhdsSet hU hx) k⟩

#print axioms compact_factorial_bound_of_neighborhood_family
#print axioms compact_local_factorial_bound_uniform_nhds
#print axioms compact_local_factorial_bound_uniform
end TheoremT.Continuum
