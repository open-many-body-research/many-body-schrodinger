import GroupedHomogeneousSpectatorPolynomial_v1
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Data.Fin.Tuple.Basic

/-! Exact reindexing of the literal polynomial/spectator term family by
joint total degree. Summability is an explicit hypothesis on the original
product-index family; the grouping equality itself is proved. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*} {d : ℕ}

def spectatorDegreeIndexEquiv (d : ℕ) :
    (Fin (d+1) →₀ ℕ) ≃ ℕ × (Fin d → ℕ) :=
  Finsupp.equivFunOnFinite.trans (Fin.consEquiv (fun _ : Fin (d+1) => ℕ)).symm

theorem spectatorDegreeIndexEquiv_apply (w : Fin (d+1) →₀ ℕ) :
    spectatorDegreeIndexEquiv d w = (w 0, fun i : Fin d => w i.succ) := rfl

theorem spectator_total_degree_grouping_hasSum
    (f : ℕ × (Fin d → ℕ) → ℂ) (hf : Summable f) :
    HasSum (fun n => ∑ w ∈ spectatorTotalDegreeIndices d n,
      f (w 0, fun i : Fin d => w i.succ)) (∑' z, f z) := by
  classical
  let degree : (Fin (d+1) →₀ ℕ) → ℕ := fun w => w 0 + ∑ i : Fin d, w i.succ
  have hw : HasSum (f ∘ spectatorDegreeIndexEquiv d) (∑' z, f z) :=
    (spectatorDegreeIndexEquiv d).hasSum_iff.mpr hf.hasSum
  have hgroup := hw.tsum_fiberwise degree
  have heq (n : ℕ) :
      (∑' w : degree ⁻¹' {n}, (f ∘ spectatorDegreeIndexEquiv d) w) =
      ∑ w ∈ spectatorTotalDegreeIndices d n, f (w 0, fun i : Fin d => w i.succ) := by
    have hset : degree ⁻¹' {n} = (spectatorTotalDegreeIndices d n : Set (Fin (d+1) →₀ ℕ)) := by
      ext w
      exact (mem_spectatorTotalDegreeIndices_iff d n w).symm
    rw [hset, Finset.tsum_subtype']
    simp only [Function.comp_apply, spectatorDegreeIndexEquiv_apply]
  simpa only [heq] using hgroup

theorem groupedHomogeneousSpectatorPolynomial_hasSum
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ) (X : σ → ℂ) (s : Fin d → ℂ)
    (h : Summable (fun z : ℕ × (Fin d → ℕ) =>
      MvPolynomial.eval X (A z.1 z.2) * ∏ i : Fin d, s i ^ z.2 i)) :
    HasSum (fun n => MvPolynomial.eval (Sum.elim X s)
      (groupedHomogeneousSpectatorPolynomial A n))
      (∑' z : ℕ × (Fin d → ℕ),
        MvPolynomial.eval X (A z.1 z.2) * ∏ i : Fin d, s i ^ z.2 i) := by
  simpa only [groupedHomogeneousSpectatorPolynomial, map_sum,
    homogeneousSpectatorPolynomial_eval] using
    spectator_total_degree_grouping_hasSum
      (fun z : ℕ × (Fin d → ℕ) =>
        MvPolynomial.eval X (A z.1 z.2) * ∏ i : Fin d, s i ^ z.2 i) h

theorem groupedHomogeneousSpectatorPolynomial_tsum_eq
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ) (X : σ → ℂ) (s : Fin d → ℂ)
    (h : Summable (fun z : ℕ × (Fin d → ℕ) =>
      MvPolynomial.eval X (A z.1 z.2) * ∏ i : Fin d, s i ^ z.2 i)) :
    (∑' n, MvPolynomial.eval (Sum.elim X s) (groupedHomogeneousSpectatorPolynomial A n)) =
      ∑' z : ℕ × (Fin d → ℕ),
        MvPolynomial.eval X (A z.1 z.2) * ∏ i : Fin d, s i ^ z.2 i :=
  (groupedHomogeneousSpectatorPolynomial_hasSum A X s h).tsum_eq

end TheoremT.Continuum
