import HydrogenExactSolver_v1
import Lean

/-! A small command-line adapter for the verified pure one-electron solver.
Decimal natural inputs Z and p are parsed at runtime. The mathematical guarantee
is HydrogenExactSolver_v1; serialization and timings are runtime diagnostics. -/

private def rationalJSON (q : ℚ) : Lean.Json :=
  Lean.Json.mkObj [("numerator", Lean.toJson (toString q.num)),
    ("denominator", Lean.toJson (toString q.den))]

def main (args : List String) : IO UInt32 := do
  match args with
  | [zText, pText] =>
    match zText.toNat?, pText.toNat? with
    | some Z, some p =>
      let I := TheoremT.Continuum.hydrogenExactSolver Z p
      let accepted := TheoremT.Continuum.hydrogenExactCertificateCheck Z I
      let result := Lean.Json.mkObj [
        ("electron_count", Lean.toJson (1 : Nat)),
        ("charge", Lean.toJson (toString Z)),
        ("precision", Lean.toJson (toString p)),
        ("lower", rationalJSON I.1),
        ("upper", rationalJSON I.2),
        ("width", rationalJSON (I.2 - I.1)),
        ("certificate_accepted", Lean.toJson accepted)]
      IO.println result.compress
      return 0
    | _, _ =>
      IO.eprintln "Z and p must be decimal natural numbers."
      return 2
  | _ =>
    IO.eprintln "Usage: HydrogenExactSolverCLI_v1.lean Z p"
    return 2
