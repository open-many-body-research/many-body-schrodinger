import ProductLocalEllipticH2_v1

/-! Actual local L2 closure under a real coefficient continuous on the domain.
Neither the coefficient nor the raw functions need global integrability or
global measurability. All multiplier estimates use compact restricted volume. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem product_continuousOn_memLp_top_restrict
    {Ω K : Set (Y × T)} {B : Y × T → ℝ}
    (hB : ContinuousOn B Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    MemLp B ⊤ (volume.restrict K) := by
  have hBK : ContinuousOn B K := hB.mono hKΩ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hBK
  apply memLp_top_of_bound (hBK.aestronglyMeasurable hK.measurableSet) C
  filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
  exact hC p hp

theorem product_locallyL2On_smul_of_continuousOn
    {Ω : Set (Y × T)} {B : Y × T → ℝ} {f : Y × T → ℂ}
    (hB : ContinuousOn B Ω) (hf : ProductLocallyL2On f Ω) :
    ProductLocallyL2On (fun p => B p • f p) Ω := by
  intro K hK hKΩ
  exact (hf K hK hKΩ).smul (product_continuousOn_memLp_top_restrict hB hK hKΩ)

theorem product_locallyL2On_sub
    {Ω : Set (Y × T)} {f g : Y × T → ℂ}
    (hf : ProductLocallyL2On f Ω) (hg : ProductLocallyL2On g Ω) :
    ProductLocallyL2On (fun p => f p - g p) Ω := by
  intro K hK hKΩ
  exact (hf K hK hKΩ).sub (hg K hK hKΩ)

theorem product_locallyL2On_sub_smul
    {Ω : Set (Y × T)} {B : Y × T → ℝ} {f g : Y × T → ℂ}
    (hB : ContinuousOn B Ω) (hf : ProductLocallyL2On f Ω)
    (hg : ProductLocallyL2On g Ω) :
    ProductLocallyL2On (fun p => g p - B p • f p) Ω :=
  product_locallyL2On_sub hg (product_locallyL2On_smul_of_continuousOn hB hf)

#print axioms product_locallyL2On_smul_of_continuousOn
#print axioms product_locallyL2On_sub_smul
end TheoremT.Continuum
