import ActualWeakOrder_v1
import SobolevLaplacianGain_v1

noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian BigOperators
namespace TheoremT.Continuum

theorem memSobolev_finset_sum_distribution {N : ℕ} {s : ℝ} {ι : Type*}
    (t : Finset ι) (f : ι → 𝓢'(Configuration N,ℂ))
    (hf : ∀ j ∈ t, MemSobolev s 2 (f j)) : MemSobolev s 2 (∑ j ∈ t,f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
    rw [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self _ _)).add (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

theorem HasWeakOrder.memSobolev_even {N : ℕ} (m : ℕ) {f : SpatialL2 N}
    (hf : HasWeakOrder f (2*m)) : MemSobolev (2*(m:ℝ)) 2 (f : 𝓢'(Configuration N,ℂ)) := by
  induction m generalizing f with
  | zero =>
    simp only [Nat.cast_zero,mul_zero]
    exact memSobolev_zero_iff.mpr ⟨f,rfl⟩
  | succ m ih =>
    have hf0 : HasWeakOrder f (2*m) := hf.mono (by omega)
    have hff : HasWeakOrder f ((2*m+1)+1) := by convert hf using 1 <;> omega
    obtain ⟨d,hd,hdo⟩ := hff
    have hdex (k : Coordinate N) : ∃ e : Coordinate N → SpatialL2 N,
        (∀ l,WeakPartial (d k) (e l) l) ∧ ∀ l,HasWeakOrder (e l) (2*m) := hdo k
    choose e he heO using hdex
    have hΔ := distribution_laplacian_eq_sum_of_weakPartial d (fun k => e k k) hd (fun k => he k k)
    have hsum : MemSobolev (2*(m:ℝ)) 2 ((∑ k : Coordinate N,e k k : SpatialL2 N) : 𝓢'(Configuration N,ℂ)) := by
      simp only [← Lp.toTemperedDistributionCLM_apply,map_sum]
      exact memSobolev_finset_sum_distribution Finset.univ _ (fun k _ => ih (heO k k))
    have hgain := memSobolev_add_two_of_laplacian (ih hf0) (by rw [hΔ];exact hsum)
    convert hgain using 1 <;> push_cast <;> ring

#print axioms HasWeakOrder.memSobolev_even
end TheoremT.Continuum
