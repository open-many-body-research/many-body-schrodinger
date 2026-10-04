import KSBalancedMonomialPairing_v1

/-! Execution diagnostics for the already proved Nat exponent procedure.
These evaluations demonstrate actual execution, including a large integer.
The universal margin theorem, not these sample outputs, proves correctness.
No native_decide or external computation is used in a mathematical proof. -/
open TheoremT.Continuum

#eval ([(0,0,0,0), (2,3,4,1), (4,1,2,3),
    (100000000000000000000,7,99999999999999999999,8)] :
      List (Nat × Nat × Nat × Nat)).map fun (a1,a2,b1,b2) =>
  ((a1,a2,b1,b2),
    [[ksBalancedMonomialPairing a1 a2 b1 b2 0 0,
      ksBalancedMonomialPairing a1 a2 b1 b2 0 1],
     [ksBalancedMonomialPairing a1 a2 b1 b2 1 0,
      ksBalancedMonomialPairing a1 a2 b1 b2 1 1]])
