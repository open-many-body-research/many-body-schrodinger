import BoundedSmoothMultiplierJet_v1

/-! A conditional multiplier-limit theorem. The strong L2 multiplication limits
are explicit premises; the physical cusp instantiation must discharge them.
No limiting weak-H2 premise is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem weakH2_multiplier_of_smooth_limits {N : ℕ}
    (χ : ℕ → Configuration N → ℝ) (hc : ∀ n, ContDiff ℝ ∞ (χ n))
    (hm : ∀ n, MemLp (χ n) (⊤ : ENNReal) volume)
    (hdm : ∀ n k, MemLp (fun x => fderiv ℝ (χ n) x (coordinateVector k)) (⊤ : ENNReal) volume)
    (hem : ∀ n k l, MemLp (fun x => fderiv ℝ
      (fun y => fderiv ℝ (χ n) y (coordinateVector k)) x (coordinateVector l)) (⊤ : ENNReal) volume)
    (U : SpatialL2 N → SpatialL2 N)
    (D : Coordinate N → SpatialL2 N → SpatialL2 N)
    (E : Coordinate N → Coordinate N → SpatialL2 N → SpatialL2 N)
    (hU : ∀ g : SpatialL2 N, Tendsto (fun n => boundedRealMul (χ n) (hm n) g) atTop (𝓝 (U g)))
    (hD : ∀ k (g : SpatialL2 N), Tendsto
      (fun n => boundedRealMul (fun x => fderiv ℝ (χ n) x (coordinateVector k)) (hdm n k) g)
      atTop (𝓝 (D k g)))
    (hE : ∀ k l (g : SpatialL2 N), HasH1 g → Tendsto
      (fun n => boundedRealMul (fun x => fderiv ℝ
        (fun y => fderiv ℝ (χ n) y (coordinateVector k)) x (coordinateVector l)) (hem n k l) g)
      atTop (𝓝 (E k l g)))
    {f : SpatialL2 N} (hf : HasH2 f) : HasH2 (U f) := by
  obtain ⟨d,hd,he⟩ := hf
  have h1 : HasH1 f := ⟨d,hd⟩
  refine ⟨fun k => U (d k)+D k f,?_,?_⟩
  · intro k
    exact WeakPartial.of_tendsto
      (fun n => weakPartial_boundedRealMul (hd k) (χ n) (hc n) (hm n) (hdm n k))
      (hU f) ((hU (d k)).add (hD k f))
  · intro k l
    obtain ⟨e,he⟩ := he k l
    refine ⟨(U e+D l (d k))+(D k (d l)+E k l f),?_⟩
    exact WeakPartial.of_tendsto
      (fun n => boundedRealMul_second_weakPartial (hd l) he (χ n) (hc n)
        (hm n) (hdm n k) (hdm n l) (hem n k l))
      ((hU (d k)).add (hD k f))
      (((hU e).add (hD l (d k))).add ((hD k (d l)).add (hE k l f h1)))

#print axioms weakH2_multiplier_of_smooth_limits
end TheoremT.Continuum
