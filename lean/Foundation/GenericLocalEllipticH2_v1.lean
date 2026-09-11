import GenericNestedCutoffH2_v1
import FiniteDimSmoothCutoff_v1

/-! Local elliptic H² gain on every finite real Euclidean space, with actual
local L² data and genuine compact-test equations. The required outer cutoff
is constructed by the existing finite smooth bump covering theorem.
Local L² is expressed by L² on every compact subset; local weak H² is expressed
by genuine global weak H² for every smooth compact cutoff. -/
noncomputable section
open MeasureTheory Filter
open scoped Laplacian ContDiff Topology
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def GenericLocallyL2On (f : E → ℂ) (Ω : Set E) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K)

def GenericLocalWeakH2On (f : E → ℂ) (Ω : Set E) : Prop :=
  ∀ χ : E → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
    ∃ U : Lp ℂ 2 (volume : Measure E),
      U =ᵐ[volume] (fun x => χ x • f x) ∧ HasWeakL2Order U 2

theorem generic_local_elliptic_h2_cutoff
    {Ω : Set E} (hΩ : IsOpen Ω) (f w : E → ℂ)
    (hf : GenericLocallyL2On f Ω) (hw : GenericLocallyL2On w Ω)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, Δ φ x • f x) = ∫ x, φ x • w x)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω) :
    ∃ U : Lp ℂ 2 (volume : Measure E),
      U =ᵐ[volume] (fun x => χ x • f x) ∧ HasWeakL2Order U 2 := by
  obtain ⟨η,hη,hcη,hsη,h1⟩ :=
    finiteDim_compact_exists_smooth_cutoff hcχ.isCompact hΩ hsχ
  exact generic_nested_cutoff_h2 f w h hη hcη hsη
    (hf _ hcη.isCompact hsη) (hw _ hcη.isCompact hsη) hχ hcχ
    (fun x hx => (h1 x hx).self_of_nhds)

theorem generic_local_elliptic_h2_on
    {Ω : Set E} (hΩ : IsOpen Ω) (f w : E → ℂ)
    (hf : GenericLocallyL2On f Ω) (hw : GenericLocallyL2On w Ω)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, Δ φ x • f x) = ∫ x, φ x • w x) :
    GenericLocalWeakH2On f Ω := by
  intro χ hχ hcχ hsχ
  exact generic_local_elliptic_h2_cutoff hΩ f w hf hw h hχ hcχ hsχ

theorem generic_local_elliptic_h2_jets
    {Ω : Set E} (hΩ : IsOpen Ω) (f w : E → ℂ)
    (hf : GenericLocallyL2On f Ω) (hw : GenericLocallyL2On w Ω)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, Δ φ x • f x) = ∫ x, φ x • w x)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω) :
    ∃ U : Lp ℂ 2 (volume : Measure E), ∃ d : E → Lp ℂ 2 (volume : Measure E),
      U =ᵐ[volume] (fun x => χ x • f x) ∧
      (∀ v, WeakL2Directional U (d v) v) ∧
      ∀ v q : E, ∃ e : Lp ℂ 2 (volume : Measure E), WeakL2Directional (d v) e q := by
  obtain ⟨U,hU,d,hd,hdd⟩ := generic_local_elliptic_h2_cutoff hΩ f w hf hw h hχ hcχ hsχ
  refine ⟨U,d,hU,hd,fun v q => ?_⟩
  obtain ⟨e,he,_⟩ := hdd v
  exact ⟨e q,he q⟩

#print axioms generic_local_elliptic_h2_cutoff
#print axioms generic_local_elliptic_h2_on
#print axioms generic_local_elliptic_h2_jets
end TheoremT.Continuum
