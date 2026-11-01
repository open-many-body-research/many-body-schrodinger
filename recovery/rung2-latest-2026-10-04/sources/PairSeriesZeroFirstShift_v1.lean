import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Basic

/-! Restore the first natural index of an actual product-index series.
The entire zero slice vanishes explicitly. Absolute summability of the
successor-indexed family transfers through its injective index map, whose
complement is precisely that zero slice. No infinite reindexing equality
or iterated-sum identity is assumed. The spectator type may in particular
be `Fin d → ℕ`, including dimension zero. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {ι : Type*}

theorem pair_series_zero_first_shift
    (f : ℕ × ι → ℂ) (h0 : ∀ γ, f (0, γ) = 0)
    (hshift : Summable (fun k : ℕ × ι => ‖f (k.1 + 1, k.2)‖)) :
    Summable (fun k => ‖f k‖) ∧ Summable f ∧
      (∑' k, f k) = ∑' k : ℕ × ι, f (k.1 + 1, k.2) := by
  let s : ℕ × ι → ℕ × ι := fun k => (k.1 + 1, k.2)
  have hs : Function.Injective s := by
    intro a b hab
    change (a.1 + 1, a.2) = (b.1 + 1, b.2) at hab
    apply Prod.ext
    · exact Nat.add_right_cancel (Prod.mk.inj hab).1
    · exact (Prod.mk.inj hab).2
  have hzero (k : ℕ × ι) (hk : k ∉ Set.range s) : f k = 0 := by
    rcases k with ⟨n, γ⟩
    cases n with
    | zero => exact h0 γ
    | succ n => exact False.elim (hk ⟨(n, γ), rfl⟩)
  have habs : Summable (fun k => ‖f k‖) :=
    (hs.summable_iff (f := fun k => ‖f k‖)
      (fun k hk => by rw [hzero k hk, norm_zero])).mp hshift
  have hsum : HasSum f (∑' k : ℕ × ι, f (k.1 + 1, k.2)) :=
    (hs.hasSum_iff hzero).mp hshift.of_norm.hasSum
  exact ⟨habs, habs.of_norm, hsum.tsum_eq⟩

end TheoremT.Continuum
