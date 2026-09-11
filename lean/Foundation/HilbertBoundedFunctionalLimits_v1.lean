import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Compactness.Compact

/-!
A bounded Hilbert sequence has a norm-controlled vector reproducing every
continuous-linear functional limit that exists along the entire sequence.
The proof uses Banach-Alaoglu and Riesz; no separability or subsequence premise
is required, and no convergence of the original sequence is asserted.
-/
noncomputable section
open Filter Metric
open scoped Topology InnerProductSpace
namespace TheoremT.Continuum
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem hilbert_exists_bounded_vector_of_functional_limits
    (u : ℕ → H) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ g : H, ‖g‖ ≤ C ∧ ∀ (L : StrongDual ℂ H) (z : ℂ),
      Tendsto (fun n => L (u n)) atTop (𝓝 z) → L g = z := by
  let d (n : ℕ) : WeakDual ℂ H := StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (u n))
  have hb : ∀ n, d n ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℂ H) C := by
    intro n
    simpa only [Set.mem_preimage, mem_closedBall, dist_zero_right, d,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hu n
  have hb' : Filter.map d atTop ≤ 𝓟 (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℂ H) C) := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ n in atTop, d n ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℂ H) C
    exact Eventually.of_forall hb
  obtain ⟨l,hl,hcluster⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) C).exists_mapClusterPt hb' 
  let g := (InnerProductSpace.toDual ℂ H).symm l.toStrongDual
  have hnorm : ‖g‖ ≤ C := by
    simpa only [g, LinearIsometryEquiv.norm_map, Set.mem_preimage, mem_closedBall, dist_zero_right] using hl
  refine ⟨g,hnorm,?_⟩
  intro L z hz
  let q := (InnerProductSpace.toDual ℂ H).symm L
  have hq (x : H) : inner ℂ q x = L x := InnerProductSpace.toDual_symm_apply
  have hdq (n : ℕ) : d n q = starRingEnd ℂ (L (u n)) := by
    change inner ℂ (u n) q = _
    rw [← inner_conj_symm (u n) q, hq]
  have hlim : Tendsto (fun n => d n q) atTop (𝓝 (starRingEnd ℂ z)) := by
    simpa only [hdq, Function.comp_def] using (Complex.continuous_conj.tendsto z).comp hz
  have ht : Tendsto (fun x : WeakDual ℂ H => x q) (Filter.map d atTop)
      (𝓝 (starRingEnd ℂ z)) := by
    simpa only [Filter.tendsto_map'_iff, Function.comp_def] using hlim
  have he : l q = starRingEnd ℂ z :=
    eq_of_nhds_neBot (hcluster.map (WeakDual.eval_continuous q).continuousAt ht)
  have hg : inner ℂ g q = l q := InnerProductSpace.toDual_symm_apply
  have he' : starRingEnd ℂ (L g) = starRingEnd ℂ z := by
    rw [← he, ← hg, ← hq g]
    exact inner_conj_symm g q
  exact (starRingEnd ℂ).injective he'

#print axioms hilbert_exists_bounded_vector_of_functional_limits
end TheoremT.Continuum
