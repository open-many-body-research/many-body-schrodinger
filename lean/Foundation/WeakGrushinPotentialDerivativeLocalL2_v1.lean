import ProductLocalEllipticH2_v1
import SmoothLocalTestProduct_v1
import FiniteDimSmoothCutoff_v1

/-! Local L2 potential products and their candidate spectator Leibniz output.
The real coefficient is smooth only on the advertised open set. On each
compact subset a smooth plateau cutoff produces a globally smooth compact
coefficient with the same value and derivative there. These are integrability
statements; the weak product identity is a separate obligation. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem smooth_coefficient_and_directional_memLp_top_restrict_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {Ω K : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {B : E → ℝ} (hB : ContDiffOn ℝ ∞ B Ω) (v : E) :
    MemLp B ⊤ (μ.restrict K) ∧
      MemLp (fun p => fderiv ℝ B p v) ⊤ (μ.restrict K) := by
  obtain ⟨η,hη,hcη,hsη,h1⟩ := finiteDim_compact_exists_smooth_cutoff hK hΩ hKΩ
  let C : E → ℝ := fun p => η p * B p
  have hC : ContDiff ℝ ∞ C := smooth_mul_of_smooth_on_tsupport hη
    (fun p hp => hB.contDiffAt (hΩ.mem_nhds (hsη hp)))
  have hcC : HasCompactSupport C := hcη.mul_right
  have hCB (p : E) (hp : p ∈ K) : C =ᶠ[𝓝 p] B := by
    filter_upwards [h1 p hp] with q hq
    simp only [C,hq,one_mul]
  have hmC : MemLp C ⊤ (μ.restrict K) :=
    (hC.continuous.memLp_top_of_hasCompactSupport hcC μ).mono_measure Measure.restrict_le_self
  have hdC : Continuous (fun p => fderiv ℝ C p v) :=
    (hC.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmD : MemLp (fun p => fderiv ℝ C p v) ⊤ (μ.restrict K) :=
    (hdC.memLp_top_of_hasCompactSupport (hcC.fderiv_apply ℝ v) μ).mono_measure Measure.restrict_le_self
  constructor
  · apply hmC.ae_eq
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact (hCB p hp).self_of_nhds
  · apply hmD.ae_eq
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact congrArg (fun L : E →L[ℝ] ℝ => L v) (hCB p hp).fderiv_eq

variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem product_smooth_coefficient_locallyL2
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    ProductLocallyL2On (fun p => B p • f p) Ω := by
  intro K hK hKΩ
  have hm := (smooth_coefficient_and_directional_memLp_top_restrict_compact
    (μ := volume) hΩ hK hKΩ hB (0 : Y × T)).1
  exact ((Lp.memLp f).mono_measure Measure.restrict_le_self).smul hm

theorem product_spectator_potential_leibniz_locallyL2
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω)
    (f d : Lp ℂ 2 (volume : Measure (Y × T))) (v : T) :
    ProductLocallyL2On (fun p => B p • d p + (fderiv ℝ B p (0,v)) • f p) Ω := by
  intro K hK hKΩ
  obtain ⟨hmB,hmD⟩ := smooth_coefficient_and_directional_memLp_top_restrict_compact
    (μ := volume) hΩ hK hKΩ hB ((0 : Y),v)
  have hd : MemLp (fun p => B p • d p) 2 (volume.restrict K) :=
    ((Lp.memLp d).mono_measure Measure.restrict_le_self).smul hmB
  have hf : MemLp (fun p => (fderiv ℝ B p (0,v)) • f p) 2 (volume.restrict K) :=
    ((Lp.memLp f).mono_measure Measure.restrict_le_self).smul hmD
  exact hd.add hf

#print axioms smooth_coefficient_and_directional_memLp_top_restrict_compact
#print axioms product_smooth_coefficient_locallyL2
#print axioms product_spectator_potential_leibniz_locallyL2
end TheoremT.Continuum
