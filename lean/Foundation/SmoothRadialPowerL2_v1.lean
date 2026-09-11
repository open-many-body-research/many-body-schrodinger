import SmoothRadialPowerIdentities_v1
import WeakH1C1Chain_v1

/-! The concrete smooth radial maps act on the actual L2 and weak H1 spaces.
Their Lipschitz constants are finite real powers, not numerical certificates. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace TheoremT.Continuum

def smoothRadialPowerConstant (b r : ℝ) : ℝ≥0 := ((1+2*r)*b^r).toNNReal

theorem smoothRadialPower_lipschitz {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) :
    LipschitzWith (smoothRadialPowerConstant b r) (smoothRadialPower a b r) :=
  boundedC1_lipschitz _ ((smoothRadialPower_contDiff ha hab).of_le (by simp)) _
    (fun z => (smoothRadialPower_fderiv_norm ha hab hr z).trans (Real.le_coe_toNNReal _))

def smoothRadialPowerL2 {N : ℕ} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (f : SpatialL2 N) : SpatialL2 N :=
  (smoothRadialPower_lipschitz ha hab hr).compLp (smoothRadialPower_zero a b r) f

def smoothRadialPowerDerivativeL2 {N : ℕ} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (f d : SpatialL2 N) : SpatialL2 N :=
  nonlinearFieldL2 (fderiv ℝ (smoothRadialPower a b r))
    ((smoothRadialPower_contDiff ha hab).continuous_fderiv (by simp)) (smoothRadialPowerConstant b r)
    (fun z => (smoothRadialPower_fderiv_norm ha hab hr z).trans (Real.le_coe_toNNReal _)) f d

theorem smoothRadialPowerL2_ae {N : ℕ} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (f : SpatialL2 N) :
    smoothRadialPowerL2 ha hab hr f =ᵐ[volume] (fun x => smoothRadialPower a b r (f x)) :=
  (smoothRadialPower_lipschitz ha hab hr).coeFn_compLp _ f

theorem smoothRadialPowerDerivativeL2_ae {N : ℕ} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) (f d : SpatialL2 N) :
    smoothRadialPowerDerivativeL2 ha hab hr f d =ᵐ[volume]
      (fun x => fderiv ℝ (smoothRadialPower a b r) (f x) (d x)) :=
  nonlinearFieldL2_ae _ _ _ _ _ _

theorem weakH1_smoothRadialPower {N : ℕ} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) {f : SpatialL2 N}
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k) (k : Coordinate N) :
    WeakPartial (smoothRadialPowerL2 ha hab hr f)
      (smoothRadialPowerDerivativeL2 ha hab hr f (d k)) k :=
  weakH1_C1_chain _ ((smoothRadialPower_contDiff ha hab).of_le (by simp))
    (smoothRadialPower_zero a b r) (smoothRadialPowerConstant b r)
    (fun z => (smoothRadialPower_fderiv_norm ha hab hr z).trans (Real.le_coe_toNNReal _)) d hd k

theorem HasH1.smoothRadialPower {N : ℕ} {a b r : ℝ} {f : SpatialL2 N}
    (hf : HasH1 f) (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) :
    HasH1 (smoothRadialPowerL2 ha hab hr f) := by
  obtain ⟨d,hd⟩ := hf
  exact ⟨fun k => smoothRadialPowerDerivativeL2 ha hab hr f (d k),
    fun k => weakH1_smoothRadialPower ha hab hr d hd k⟩

#print axioms smoothRadialPower_lipschitz
#print axioms weakH1_smoothRadialPower
#print axioms HasH1.smoothRadialPower
end TheoremT.Continuum
