import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A finitely supported natural exponent family admits a word with precisely
its total length, whose coordinate product is the associated monomial.
The list representative uses classical choice; no executable implementation
or complexity claim is attached to this construction. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem monomial_exponent_word_exists {σ M : Type*} [CommMonoid M]
    (d : σ →₀ ℕ) (n : ℕ) (hn : d.sum (fun _ e => e) = n) :
    ∃ w : Fin n → σ, ∀ z : σ → M,
      (∏ j : Fin n, z (w j)) = ∏ i ∈ d.support, z i ^ d i := by
  classical
  let l := d.toMultiset.toList
  have hlen : l.length = n := by
    simpa only [l, Multiset.length_toList, Finsupp.card_toMultiset, Function.id_def] using hn
  rw [← hlen]
  refine ⟨fun j => l[j.val], ?_⟩
  intro z
  rw [Fin.prod_univ_fun_getElem]
  have hprod : (l.map z).prod = (d.toMultiset.map z).prod := by
    rw [← Multiset.coe_toList d.toMultiset]
    rfl
  rw [hprod, Finset.prod_multiset_map_count]
  simp only [Finsupp.toFinset_toMultiset, Finsupp.count_toMultiset]

end TheoremT.Continuum
