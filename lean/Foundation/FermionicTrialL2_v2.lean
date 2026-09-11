import FermionicTrialPolynomial_v2
import CoulombDomainTotal_v2
import CoulombSemibounded_v2
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Nonzero actual fermionic H² states, normalized graph trials, and finiteness
of the original variational infimum. No eigenstate or spectral identification
is inferred. The symmetric spin factor is constant across the finite spin basis. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff

namespace TheoremT.Continuum

def fermionicTrialAmplitude (N : ℕ) : Configuration N → ℂ :=
  compactAlternatingAmplitude N (‖lineConfiguration N‖ + 1)

theorem fermionicTrialAmplitude_memLp (N : ℕ) : MemLp (fermionicTrialAmplitude N) 2 volume :=
  (compactAlternatingAmplitude_contDiff N _).continuous.memLp_of_hasCompactSupport
    (compactAlternatingAmplitude_compact (by positivity))

def fermionicTrialSpatial (N : ℕ) : SpatialL2 N :=
  (fermionicTrialAmplitude_memLp N).toLp (fermionicTrialAmplitude N)

theorem fermionicTrialSpatial_hasH2 (N : ℕ) : HasH2 (fermionicTrialSpatial N) :=
  compact_c2_hasH2 ((compactAlternatingAmplitude_contDiff N _).of_le (by simp))
    (compactAlternatingAmplitude_compact (by positivity)) (fermionicTrialAmplitude_memLp N)

theorem fermionicTrialSpatial_ne_zero (N : ℕ) : fermionicTrialSpatial N ≠ 0 := by
  intro hz
  have ha : fermionicTrialAmplitude N =ᵐ[volume] (fun _ => (0 : ℂ)) := by
    have h := (fermionicTrialAmplitude_memLp N).coeFn_toLp
    change fermionicTrialSpatial N =ᵐ[volume] fermionicTrialAmplitude N at h
    rw [hz] at h
    exact h.symm.trans (Lp.coeFn_zero ℂ 2 volume)
  have heq := MeasureTheory.Measure.eq_of_ae_eq ha
    (compactAlternatingAmplitude_contDiff N _).continuous continuous_const
  exact compactAlternatingAmplitude_nonzero N (congrFun heq (lineConfiguration N))

theorem fermionicTrialSpatial_pullback (N : ℕ) (π : Equiv.Perm (Fin N)) :
    pullback π (fermionicTrialSpatial N) = permutationSign π • fermionicTrialSpatial N := by
  apply Lp.ext
  have hc := (fermionicTrialAmplitude_memLp N).coeFn_toLp
  change fermionicTrialSpatial N =ᵐ[volume] fermionicTrialAmplitude N at hc
  have hcp := (permuteSpace π).measurePreserving.quasiMeasurePreserving.ae hc
  filter_upwards [pullback_ae π (fermionicTrialSpatial N),
    Lp.coeFn_smul (permutationSign π) (fermionicTrialSpatial N), hc, hcp]
    with x hpx hsx hcx hcpx
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hpx hsx
  rw [hpx, hsx, hcx, hcpx]
  exact compactAlternatingAmplitude_permute _ π x

def fermionicTrialSpin (N : ℕ) : SpinSpace N :=
  WithLp.toLp 2 (fun _ => fermionicTrialSpatial N)

theorem fermionicTrialSpin_mem_target (N : ℕ) : fermionicTrialSpin N ∈ targetDomain N := by
  constructor
  · intro π σ
    exact fermionicTrialSpatial_pullback N π
  · intro σ
    exact fermionicTrialSpatial_hasH2 N

theorem fermionicTrialSpin_ne_zero (N : ℕ) : fermionicTrialSpin N ≠ 0 := by
  intro hz
  have h := congrArg (fun ψ : SpinSpace N => ψ (fun _ => 0)) hz
  exact fermionicTrialSpatial_ne_zero N h

theorem fermionicSpace_nontrivial (N : ℕ) : Nontrivial (FermionicSpace N) := by
  let ψ : FermionicSpace N := ⟨fermionicTrialSpin N, (fermionicTrialSpin_mem_target N).1⟩
  apply nontrivial_of_ne ψ 0
  intro h
  exact fermionicTrialSpin_ne_zero N (congrArg Subtype.val h)

/-- Every finite N and real Z has an actual normalized fermionic H² graph trial.
This is a mathematical existence construction, not an energy certificate solver. -/
theorem normalized_hamiltonian_graph_nonempty (N : ℕ) (Z : ℝ) :
    ∃ ψ h : SpinSpace N, ‖ψ‖ = 1 ∧ hamiltonianGraph N Z ψ h := by
  let ψ₀ : SpinSpace N := fermionicTrialSpin N
  let c : ℂ := (‖ψ₀‖ : ℂ)⁻¹
  let ψ : SpinSpace N := c • ψ₀
  have hnorm : ‖ψ‖ = 1 := by
    dsimp [ψ, c]
    rw [_root_.norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (fermionicTrialSpin_ne_zero N))]
  have hmem : ψ ∈ targetDomain N :=
    (targetDomainSubmodule N).smul_mem c (fermionicTrialSpin_mem_target N)
  obtain ⟨h, hh, _⟩ := hamiltonian_graph_existsUnique_of_targetDomain (Z := Z) hmem
  exact ⟨ψ, h, hnorm, hh⟩

theorem variational_ground_energy_finite (N : ℕ) (Z : ℝ) :
    variationalGroundEnergy N Z ≠ ⊤ ∧ variationalGroundEnergy N Z ≠ ⊥ := by
  obtain ⟨ψ, h, hn, hg⟩ := normalized_hamiltonian_graph_nonempty N Z
  have hup := variational_ground_le_trial hn hg
  have hlo := variational_ground_energy_lower_bound N Z
  constructor
  · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
  · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo

theorem variational_ground_energy_is_real (N : ℕ) (Z : ℝ) :
    ∃ E : ℝ, variationalGroundEnergy N Z = (E : EReal) := by
  have h := variational_ground_energy_finite N Z
  exact ⟨(variationalGroundEnergy N Z).toReal, (EReal.coe_toReal h.1 h.2).symm⟩

#print axioms fermionicTrialAmplitude_memLp
#print axioms fermionicTrialSpatial_hasH2
#print axioms fermionicTrialSpatial_ne_zero
#print axioms fermionicTrialSpatial_pullback
#print axioms fermionicTrialSpin_mem_target
#print axioms fermionicTrialSpin_ne_zero
#print axioms fermionicSpace_nontrivial
#print axioms normalized_hamiltonian_graph_nonempty
#print axioms variational_ground_energy_finite
#print axioms variational_ground_energy_is_real

end TheoremT.Continuum
