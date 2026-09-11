import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
An L2-product bridge for unbounded temperate multipliers.

This requires the product to belong to L2, not the multiplier by itself.
It does not establish a Sobolev/Fourier characterization or any Hamiltonian claim.
New post-freeze work; no historical source is changed.
Frozen baseline: commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660,
tag theorem-t-proof-freeze-2026-09-09; frozen RWA_REPORT.md SHA-256
2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace TheoremT.Continuum

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure E} [μ.HasTemperateGrowth]

/-- Distribution multiplication agrees with the actual pointwise product when
that product is in L2. The multiplier itself need not belong to any Lp space. -/
theorem toTemperedDistribution_smul_of_product_memLp
    (f : Lp F 2 μ) {m : E → ℂ} (hm : m.HasTemperateGrowth)
    (hprod : MemLp (fun x => m x • f x) 2 μ) :
    ((hprod.toLp (fun x => m x • f x) : Lp F 2 μ) : 𝓢'(E, F)) =
      TemperedDistribution.smulLeftCLM F m f := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply,
    TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [hprod.coeFn_toLp] with x hx
  simp [hx, hm, smul_smul, mul_comm]

#print axioms toTemperedDistribution_smul_of_product_memLp

end TheoremT.Continuum
