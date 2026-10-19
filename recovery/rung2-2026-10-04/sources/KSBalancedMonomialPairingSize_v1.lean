import KSBalancedMonomialPairing_v1

/-! Exact output-size facts for the executable balanced exponent pairing.
The total number of quadratic factors is the balanced degree, and every
returned exponent is at most that degree. No machine cost model is assumed. -/
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem ksBalancedMonomialPairing_total {a1 a2 b1 b2 : ℕ}
    (h : a1+a2=b1+b2) :
    (∑ i : Fin 2, ∑ j : Fin 2, ksBalancedMonomialPairing a1 a2 b1 b2 i j) =
      a1+a2 := by
  simp only [ksBalancedMonomialPairing_row_sum h,Fin.sum_univ_two]
  norm_num

theorem ksBalancedMonomialPairing_four_total {a1 a2 b1 b2 : ℕ}
    (h : a1+a2=b1+b2) :
    ksBalancedMonomialPairing a1 a2 b1 b2 0 0 +
      ksBalancedMonomialPairing a1 a2 b1 b2 0 1 +
      ksBalancedMonomialPairing a1 a2 b1 b2 1 0 +
      ksBalancedMonomialPairing a1 a2 b1 b2 1 1 = a1+a2 := by
  obtain ⟨hr1,hr2,_,_⟩ := ksBalancedMonomialPairing_margins h
  omega

theorem ksBalancedMonomialPairing_entry_le_total {a1 a2 b1 b2 : ℕ}
    (h : a1+a2=b1+b2) (i j : Fin 2) :
    ksBalancedMonomialPairing a1 a2 b1 b2 i j ≤ a1+a2 := by
  calc
    _ ≤ ∑ j' : Fin 2, ksBalancedMonomialPairing a1 a2 b1 b2 i j' :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin 2, ∑ j' : Fin 2,
        ksBalancedMonomialPairing a1 a2 b1 b2 i' j' :=
      Finset.single_le_sum (fun i' _ => Nat.zero_le
        (∑ j' : Fin 2, ksBalancedMonomialPairing a1 a2 b1 b2 i' j'))
        (Finset.mem_univ i)
    _ = _ := ksBalancedMonomialPairing_total h

end TheoremT.Continuum
