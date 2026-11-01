import LocalProductDirectionalWeakUnique_v1

/-! Attaching recovered second jets to earlier local weak representatives,
and extracting genuine raw local jets on a cutoff plateau. Compatibility is
proved using local almost-everywhere uniqueness, not assumed pointwise.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem ProductLocalWeakDirectional.second_of_compatible_first
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω)
    {f d g e : Y × T → ℂ} {v w : Y × T}
    (hd : ProductLocalWeakDirectional Ω f d v)
    (hg : ProductLocalWeakDirectional Ω f g v)
    (he : ProductLocalWeakDirectional Ω g e w) :
    ProductLocalWeakDirectional Ω d e w := by
  exact he.congr_ae_local (hg.unique hΩ hd) (Eventually.of_forall (fun _ _ => rfl))

theorem ProductLocalWeakDirectional.of_cutoff_plateau
    {Ω : Set (Y × T)} {f : Y × T → ℂ} {χ : Y × T → ℝ}
    {U d : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T}
    (hU : (U : Y × T → ℂ) =ᵐ[volume] fun p => χ p • f p)
    (hχ : ∀ p ∈ Ω, χ p = 1) (hD : WeakProductL2Directional U d v) :
    ProductLocalWeakDirectional Ω f d v := by
  apply (ProductLocalWeakDirectional.of_global hD Ω).congr_ae_local
  · filter_upwards [hU] with p hp hmem
    simpa only [hχ p hmem,one_smul] using hp
  · exact Eventually.of_forall (fun _ _ => rfl)

#print axioms ProductLocalWeakDirectional.second_of_compatible_first
#print axioms ProductLocalWeakDirectional.of_cutoff_plateau
end TheoremT.Continuum
