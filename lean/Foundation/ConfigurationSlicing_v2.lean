import CollisionNull_v2
import Mathlib.MeasureTheory.Integral.Prod

/-!
Exact electron/spectator coordinate splitting of the actual configuration space.
The first product is equipped with its L2 norm, so it is a linear isometry; the
ordinary Cartesian product is used only for its equivalent topology and product
Lebesgue measure. No Jacobian or spin-counting factor is introduced.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff

namespace TheoremT.Continuum

abbrev SpectatorCoordinate {N : ℕ} (i : Fin N) := {k : Coordinate N // k.1 ≠ i}
abbrev SpectatorConfiguration {N : ℕ} (i : Fin N) :=
  EuclideanSpace ℝ (SpectatorCoordinate i)

def electronCoordinateSplit {N : ℕ} (i : Fin N) :
    Coordinate N ≃ Fin 3 ⊕ SpectatorCoordinate i where
  toFun k := if h : k.1 = i then Sum.inl k.2 else Sum.inr ⟨k, h⟩
  invFun
    | Sum.inl k => (i, k)
    | Sum.inr k => k.val
  left_inv k := by
    rcases k with ⟨j, k⟩
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  right_inv k := by
    cases k with
    | inl k => simp
    | inr k => simp [k.property]

def configurationSplit {N : ℕ} (i : Fin N) :
    Configuration N ≃ₗᵢ[ℝ] WithLp 2 (Position × SpectatorConfiguration i) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (electronCoordinateSplit i)).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 3 ⊕ SpectatorCoordinate i => ℝ))

theorem configurationSplit_fst {N : ℕ} (i : Fin N) (x : Configuration N) :
    (configurationSplit i x).ofLp.1 = position x i := rfl

theorem configurationSplit_snd_apply {N : ℕ} (i : Fin N) (x : Configuration N)
    (k : SpectatorCoordinate i) : (configurationSplit i x).ofLp.2 k = x k.val := rfl

def configurationProductEquiv {N : ℕ} (i : Fin N) :
    Configuration N ≃L[ℝ] Position × SpectatorConfiguration i :=
  (configurationSplit i).toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ Position (SpectatorConfiguration i))

def configurationReassemble {N : ℕ} (i : Fin N) (y : Position)
    (s : SpectatorConfiguration i) : Configuration N :=
  (configurationSplit i).symm (WithLp.toLp 2 (y, s))

theorem configurationReassemble_position {N : ℕ} (i : Fin N) (y : Position)
    (s : SpectatorConfiguration i) : position (configurationReassemble i y s) i = y := by
  rw [← configurationSplit_fst i]
  simp [configurationReassemble]

theorem configurationReassemble_spectator {N : ℕ} (i : Fin N) (y : Position)
    (s : SpectatorConfiguration i) (k : SpectatorCoordinate i) :
    configurationReassemble i y s k.val = s k := by
  rw [← configurationSplit_snd_apply i]
  simp [configurationReassemble]

theorem configurationSplit_measurePreserving {N : ℕ} (i : Fin N) :
    MeasurePreserving (configurationSplit i) := (configurationSplit i).measurePreserving

theorem configurationProduct_measurePreserving {N : ℕ} (i : Fin N) :
    MeasurePreserving (configurationProductEquiv i) volume
      ((volume : Measure Position).prod (volume : Measure (SpectatorConfiguration i))) :=
  (WithLp.volume_preserving_ofLp Position (SpectatorConfiguration i)).comp
    (configurationSplit i).measurePreserving

theorem configurationReassemble_measurePreserving {N : ℕ} (i : Fin N) :
    MeasurePreserving
      (fun ys : Position × SpectatorConfiguration i => configurationReassemble i ys.1 ys.2)
      ((volume : Measure Position).prod (volume : Measure (SpectatorConfiguration i))) volume :=
  (configurationSplit i).symm.measurePreserving.comp
    (WithLp.volume_preserving_toLp Position (SpectatorConfiguration i))

/-- Tonelli slicing with the physical electron coordinate integrated first.
This holds for every nonnegative measurable integrand, including infinite values. -/
theorem lintegral_configuration_slicing {N : ℕ} (i : Fin N)
    (F : Configuration N → ENNReal) (hF : Measurable F) :
    (∫⁻ x : Configuration N, F x) =
      ∫⁻ s : SpectatorConfiguration i, ∫⁻ y : Position, F (configurationReassemble i y s) := by
  rw [← (configurationReassemble_measurePreserving i).lintegral_comp hF]
  exact lintegral_prod_symm _
    (hF.comp (configurationReassemble_measurePreserving i).measurable).aemeasurable

#print axioms configurationSplit_fst
#print axioms configurationSplit_snd_apply
#print axioms configurationReassemble_position
#print axioms configurationReassemble_spectator
#print axioms configurationSplit_measurePreserving
#print axioms configurationProduct_measurePreserving
#print axioms configurationReassemble_measurePreserving
#print axioms lintegral_configuration_slicing

end TheoremT.Continuum
