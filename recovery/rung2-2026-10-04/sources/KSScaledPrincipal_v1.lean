import NuclearKSPrincipalIBP_v1

/-! Actual KS principal operators with a supplied real spectator coefficient.
The value four recovers the preserved nuclear definitions. No positivity of
the coefficient is needed for these definitions or their test identities. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def ksScaledPrincipal {N : ℕ} (i : Fin N) (c : ℝ)
    (u : NuclearKSSpace i → ℂ) (q : NuclearKSSpace i) : ℂ :=
  (∑ k : Fin 4, fderiv ℝ (fun z => fderiv ℝ u z (ksBasis k,0)) q (ksBasis k,0)) +
    (c*‖q.1‖^2) • ∑ k : SpectatorCoordinate i,
      fderiv ℝ (fun z => fderiv ℝ u z (0,spectatorBasis k)) q (0,spectatorBasis k)

def ksScaledRealPrincipal {N : ℕ} (i : Fin N) (c : ℝ)
    (φ : NuclearKSSpace i → ℝ) (q : NuclearKSSpace i) : ℝ :=
  (∑ k : Fin 4, fderiv ℝ (fun z => fderiv ℝ φ z (ksBasis k,0)) q (ksBasis k,0)) +
    c*‖q.1‖^2*(∑ k : SpectatorCoordinate i,
      fderiv ℝ (fun z => fderiv ℝ φ z (0,spectatorBasis k)) q (0,spectatorBasis k))

theorem ksScaledPrincipal_four {N : ℕ} (i : Fin N)
    (u : NuclearKSSpace i → ℂ) (q : NuclearKSSpace i) :
    ksScaledPrincipal i 4 u q = nuclearKSPrincipal i u q := rfl

theorem ksScaledRealPrincipal_four {N : ℕ} (i : Fin N)
    (φ : NuclearKSSpace i → ℝ) (q : NuclearKSSpace i) :
    ksScaledRealPrincipal i 4 φ q = nuclearKSRealPrincipal i φ q := rfl

#print axioms ksScaledPrincipal_four
#print axioms ksScaledRealPrincipal_four
end TheoremT.Continuum
