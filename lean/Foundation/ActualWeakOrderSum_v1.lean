import ActualWeakOrder_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem hasWeakOrder_zero (N n : ℕ) : HasWeakOrder (0 : SpatialL2 N) n := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨fun _ => 0,weakPartial_zero,fun _ => ih⟩

theorem hasWeakOrder_finset_sum {N n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → SpatialL2 N) (hf : ∀ j ∈ s, HasWeakOrder (f j) n) :
    HasWeakOrder (∑ j ∈ s,f j) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasWeakOrder_zero N n
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self _ _)).add (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

#print axioms hasWeakOrder_finset_sum
end TheoremT.Continuum
