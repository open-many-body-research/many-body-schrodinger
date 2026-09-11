import CoulombRankOneBranch_v1

/-! A conditional interval theorem for the actual continuum spectral infimum.
The only spectral structural input is an explicit rank-one form comparison;
ground attainment and the complement separator are derived from the certified
unit trial's upper mean. This is not an executable certificate producer. -/
noncomputable section
open scoped LinearPMap
namespace TheoremT.Continuum

theorem coulomb_rankOne_directed_spectral_enclosure (N : ℕ) (Z : ℝ)
    (l : FermionicSpace N →L[ℂ] ℂ) (β C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x : (coulombPartialOperator N Z).domain,
      β * ‖(x : FermionicSpace N)‖^2 ≤
        (inner ℂ (x : FermionicSpace N) (coulombPartialOperator N Z x)).re +
          C * ‖l (x : FermionicSpace N)‖^2)
    (ψ : (coulombPartialOperator N Z).domain) (hψ : ‖(ψ : FermionicSpace N)‖ = 1)
    (L U r : ℝ)
    (hL : L ≤ (inner ℂ (ψ : FermionicSpace N) (coulombPartialOperator N Z ψ)).re)
    (hU : (inner ℂ (ψ : FermionicSpace N) (coulombPartialOperator N Z ψ)).re ≤ U)
    (hUβ : U < β)
    (hr : ‖coulombPartialOperator N Z ψ -
      ((inner ℂ (ψ : FermionicSpace N) (coulombPartialOperator N Z ψ)).re : ℂ) •
        (ψ : FermionicSpace N)‖^2 ≤ r) :
    ((L-r/(β-U) : ℝ) : EReal) ≤ spectralGroundEnergy N Z ∧
      spectralGroundEnergy N Z ≤ (U : EReal) := by
  obtain ⟨heβ,g,hg,hAg,hcomp,_⟩ := coulomb_rankOne_ground_branch N Z l β C hC hbound
    ψ hψ (hU.trans_lt hUβ)
  have ht := TheoremT.OperatorTheory.unbounded_temple_directed_enclosure
    (coulombPartialOperator N Z)
    (TheoremT.OperatorTheory.selfAdjoint_formalAdjoint (coulombPartialOperator_selfAdjoint N Z))
    g hg (variationalGroundEnergy N Z).toReal β hAg heβ hcomp ψ hψ L U r hL hU hUβ hr
  have hf := variational_ground_energy_finite N Z
  have he : spectralGroundEnergy N Z = ((variationalGroundEnergy N Z).toReal : EReal) :=
    (spectralGroundEnergy_eq_variationalGroundEnergy N Z).trans (EReal.coe_toReal hf.1 hf.2).symm
  rw [he]
  constructor
  · exact_mod_cast ht.1
  · exact_mod_cast ht.2

#print axioms coulomb_rankOne_directed_spectral_enclosure
end TheoremT.Continuum
