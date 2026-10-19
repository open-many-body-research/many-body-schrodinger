import NuclearKSLift_v1
import CoulombLipschitzPointBound_v1

/-! The actual physical representative has a well-defined KS pullback,
locally Lipschitz and locally L2 even on the lifted collision set. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem scalar_coulomb_nuclear_KS_pullback_regular {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f)) :
    ∃ u : Configuration N → ℂ, LocallyLipschitz u ∧
      (f : Configuration N → ℂ) =ᵐ[volume] u ∧
      ∀ i : Fin N, LocallyLipschitz (u ∘ nuclearKSLift i) ∧
        (∀ q, ‖u (nuclearKSLift i q)‖ ≤ coulombMoserBoundCoefficient N Z E*‖f‖) ∧
        MemLp (u ∘ nuclearKSLift i) ⊤ volume ∧
        ∀ S : Set (NuclearKSSpace i), IsCompact S →
          MemLp (u ∘ nuclearKSLift i) 2 (volume.restrict S) := by
  obtain ⟨u,hu,hEq,hb⟩ := scalar_coulomb_bounded_locally_lipschitz_representative hN hg
  refine ⟨u,hu,hEq,?_⟩
  intro i
  have hLip := hu.comp (nuclearKSLift_locallyLipschitz i)
  have ht : MemLp (u ∘ nuclearKSLift i) ⊤ volume :=
    memLp_top_of_bound hLip.continuous.aestronglyMeasurable _ (Eventually.of_forall (fun q => hb _))
  refine ⟨hLip,fun q => hb _,ht,?_⟩
  intro S hS
  letI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact (ht.mono_measure Measure.restrict_le_self).mono_exponent le_top

#print axioms scalar_coulomb_nuclear_KS_pullback_regular
end TheoremT.Continuum
