import CompactCoulombL2_v2
import ScaledCutoff_v2

/-! Actual local integrability of nuclear/pair inverse distances, obtained from
already proved compact Hardy inequalities and a cutoff equal to one. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

theorem compact_real_cutoff_one {N : ℕ} {K : Set (Configuration N)} (hK : IsCompact K) :
    ∃ χ : Configuration N → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  refine ⟨scaledCutoff N (max R 1),scaledCutoff_contDiff _ _,
    scaledCutoff_hasCompactSupport _ (lt_of_lt_of_le zero_lt_one (le_max_right _ _)),?_⟩
  intro x hx
  exact scaledCutoff_eq_one (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    ((hR x hx).trans (le_max_left _ _))

theorem nuclear_inverse_memLp_two_on_compact {N : ℕ} (i : Fin N)
    {K : Set (Configuration N)} (hK : IsCompact K) :
    MemLp (fun x => ‖position x i‖⁻¹) 2 (volume.restrict K) := by
  obtain ⟨χ,hχ,hc,h1⟩ := compact_real_cutoff_one hK
  have hu : ContDiff ℝ 1 (fun x => (χ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.of_le (by simp))
  have huc : HasCompactSupport (fun x => (χ x : ℂ)) := hc.comp_left (g := fun t : ℝ => (t : ℂ)) rfl
  have hm := ((compact_nuclear_memLp_two_and_bound i hu huc).1.norm).restrict K
  apply hm.ae_eq
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simp [h1 x hx,norm_div,Complex.norm_real]

theorem pair_inverse_memLp_two_on_compact {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    {K : Set (Configuration N)} (hK : IsCompact K) :
    MemLp (fun x => ‖position x i-position x j‖⁻¹) 2 (volume.restrict K) := by
  obtain ⟨χ,hχ,hc,h1⟩ := compact_real_cutoff_one hK
  have hu : ContDiff ℝ 1 (fun x => (χ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.of_le (by simp))
  have huc : HasCompactSupport (fun x => (χ x : ℂ)) := hc.comp_left (g := fun t : ℝ => (t : ℂ)) rfl
  have hm := ((compact_pair_memLp_two_and_bound i j hij hu huc).1.norm).restrict K
  apply hm.ae_eq
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simp [h1 x hx,norm_div,Complex.norm_real]

theorem nuclear_inverse_locallyIntegrable {N : ℕ} (i : Fin N) :
    LocallyIntegrable (fun x => ‖position x i‖⁻¹) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using (hK.measure_lt_top (μ := volume))⟩
  exact (nuclear_inverse_memLp_two_on_compact i hK).integrable (by norm_num)

theorem pair_inverse_locallyIntegrable {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    LocallyIntegrable (fun x => ‖position x i-position x j‖⁻¹) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using (hK.measure_lt_top (μ := volume))⟩
  exact (pair_inverse_memLp_two_on_compact i j hij hK).integrable (by norm_num)

#print axioms nuclear_inverse_locallyIntegrable
#print axioms pair_inverse_locallyIntegrable
end TheoremT.Continuum
