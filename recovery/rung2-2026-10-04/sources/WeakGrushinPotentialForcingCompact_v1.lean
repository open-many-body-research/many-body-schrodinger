import WeakGrushinPotentialForcingIntegral_v1
import WeakGrushinPotentialDerivativeLocalL2_v1

/-! Compact local forcing bounds for continuous finite coefficient families,
followed by the actual smooth-potential spectator derivative specialization.
No number-of-directions factor is added to the aggregate estimates.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem compact_continuous_potential_forcing_bounds
    {ι : Type*} [Fintype ι] {Ω K : Set (Y × T)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (B : Y × T → ℝ) (A : ι → Y × T → ℝ)
    (G : Y × T → ℂ) (d : ι → Y × T → ℂ)
    (hB : ContinuousOn B Ω) (hA : ∀ j, ContinuousOn (A j) Ω)
    (hG : ProductLocallyL2On G Ω) (hd : ∀ j, ProductLocallyL2On (d j) Ω)
    {b b1 : ℝ} (hb : ∀ x ∈ K, |B x| ≤ b)
    (hb1 : ∀ x ∈ K, (∑ j, |A j x|^2) ≤ b1^2) :
    MemLp (fun x => B x • G x) 2 (volume.restrict K) ∧
    (∀ j, MemLp (fun x => -(A j x • G x) - B x • d j x) 2 (volume.restrict K)) ∧
    Integrable (fun x => ‖B x • G x‖^2) (volume.restrict K) ∧
    (∀ j, Integrable (fun x => ‖-(A j x • G x) - B x • d j x‖^2) (volume.restrict K)) ∧
    (∫ x in K, ‖B x • G x‖^2) ≤ b^2*(∫ x in K, ‖G x‖^2) ∧
    (∑ j, ∫ x in K, ‖-(A j x • G x) - B x • d j x‖^2) ≤
      2*b1^2*(∫ x in K, ‖G x‖^2) + 2*b^2*(∑ j, ∫ x in K, ‖d j x‖^2) := by
  apply potential_forcing_integral_bounds B A G d
    (product_continuousOn_memLp_top_restrict hB hK hKΩ)
    (fun j => product_continuousOn_memLp_top_restrict (hA j) hK hKΩ)
    (hG K hK hKΩ) (fun j => hd j K hK hKΩ)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hb x hx
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hb1 x hx

theorem compact_spectator_potential_forcing_bounds
    {ι : Type*} [Fintype ι] {Ω K : Set (Y × T)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {B : Y × T → ℝ} (hB : ContDiffOn ℝ ∞ B Ω) (v : ι → T)
    (G : Lp ℂ 2 (volume : Measure (Y × T)))
    (d : ι → Lp ℂ 2 (volume : Measure (Y × T)))
    {b b1 : ℝ} (hb : ∀ x ∈ K, |B x| ≤ b)
    (hb1 : ∀ x ∈ K, (∑ j, |fderiv ℝ B x (0,v j)|^2) ≤ b1^2) :
    MemLp (fun x => B x • G x) 2 (volume.restrict K) ∧
    (∀ j, MemLp (fun x => -(fderiv ℝ B x (0,v j) • G x) - B x • d j x)
      2 (volume.restrict K)) ∧
    Integrable (fun x => ‖B x • G x‖^2) (volume.restrict K) ∧
    (∀ j, Integrable (fun x => ‖-(fderiv ℝ B x (0,v j) • G x) - B x • d j x‖^2)
      (volume.restrict K)) ∧
    (∫ x in K, ‖B x • G x‖^2) ≤ b^2*(∫ x in K, ‖G x‖^2) ∧
    (∑ j, ∫ x in K, ‖-(fderiv ℝ B x (0,v j) • G x) - B x • d j x‖^2) ≤
      2*b1^2*(∫ x in K, ‖G x‖^2) + 2*b^2*(∑ j, ∫ x in K, ‖d j x‖^2) := by
  apply compact_continuous_potential_forcing_bounds hK hKΩ B
    (fun j x => fderiv ℝ B x (0,v j)) G (fun j => d j) hB.continuousOn
  · intro j x hx
    exact (local_contDiffAt_directional_derivative (hB.contDiffAt (hΩ.mem_nhds hx))
      ((0 : Y),v j)).continuousAt.continuousWithinAt
  · intro L hL hLΩ
    exact (Lp.memLp G).mono_measure Measure.restrict_le_self
  · intro j L hL hLΩ
    exact (Lp.memLp (d j)).mono_measure Measure.restrict_le_self
  · exact hb
  · exact hb1

#print axioms compact_continuous_potential_forcing_bounds
#print axioms compact_spectator_potential_forcing_bounds
end TheoremT.Continuum.WeakGrushin
