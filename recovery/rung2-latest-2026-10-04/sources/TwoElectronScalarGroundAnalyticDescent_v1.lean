import TwoElectronPointwiseGround_v1
import CoulombSpectralFoundation_v3
import PhysicalKSBoxAnalyticDescentData_v2

/-! One normalized scalar two-electron ground function and its same continuous
representative carry pointwise reality, exchange and orthogonal rotation
symmetry, genuine weak H2 exterior bounds, and the actual analytic distance
decomposition with mixed derivative bounds in every normalized physical KS
chart. The energy is identified with the full fermionic continuum spectrum.
The source and H12 budgets below belong to this scalar representative. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal BigOperators Topology
namespace TheoremT.Continuum
open WeakGrushin

theorem twoElectron_scalar_ground_analytic_descent_with_H2_decay
    (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ C_H M A : ℝ, 1 ≤ C_H ∧ 1 ≤ M ∧ 1 ≤ A ∧
      ∃ f : SpatialL2 2, ∃ u : Configuration 2 → ℂ,
      ∃ L : ℝ≥0, ∃ R : ℝ,
        ‖f‖ = 1 ∧ HasH2 f ∧
        scalarHamiltonianGraph 2 Z f
          (((variationalGroundEnergy 2 Z).toReal : ℂ) • f) ∧
        spectralGroundEnergy 2 Z = ((variationalGroundEnergy 2 Z).toReal : EReal) ∧
        (((variationalGroundEnergy 2 Z).toReal : ℂ) ∈
          TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z)) ∧
        (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
          (variationalGroundEnergy 2 Z).toReal ≤ z.re) ∧
        LocallyLipschitz u ∧ (f : Configuration 2 → ℂ) =ᵐ[volume] u ∧
        (∀ x, ‖u x‖ ≤
          coulombMoserBoundCoefficient 2 Z (variationalGroundEnergy 2 Z).toReal) ∧
        (∀ x, (u x).im = 0) ∧
        (∀ x, u (permuteSpace twoElectronSwap x) = u x) ∧
        (∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
          u (configurationRotation 2 Q x) = u x) ∧
        0 < L ∧ 0 < R ∧ LipschitzOnWith L u (ball 0 R) ∧
        0 ≤ M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume ∧
        0 ≤ (((L : ℝ)^2+‖u 0‖^2)*C_H) ∧
        (∃ d : Coordinate 2 → SpatialL2 2,
          ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
          (∀ k, WeakPartial f (d k) k) ∧
          (∀ k l, WeakPartial (d k) (e k l) l) ∧
          ∀ a : ℝ, 0 ≤ a → a^2 < Z^2/112 →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
              weakH2ExteriorNorm f d e r ≤ Real.exp (-a*r)*C) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentDerivativeData
              ((originScaledDifference u ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference u ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L : ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ t0 : Position, ‖t0‖ = 1 →
            PhysicalKSBoxAnalyticDescentDerivativeData
              ((originScaledDifference u ε ∘ pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference u ε (pairKSPhysicalCoordinates X T))
              t0 M A (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L : ℝ)^2+‖u 0‖^2)*C_H)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,hgain⟩ :=
    scalar_coulomb_all_physical_box_pointwise Z (variationalGroundEnergy 2 Z).toReal
  obtain ⟨f,u,hf,hH2,hgraph,hu,hAE,hbound,hreal,hexchange,hrotation,htail⟩ :=
    twoElectron_physical_pointwise_ground_with_H2_decay Z hZ
  obtain ⟨K,U,hU,hKU⟩ := hu 0
  obtain ⟨R,hR,hRU⟩ := Metric.mem_nhds_iff.mp hU
  let L : ℝ≥0 := K+1
  have hL : 0 < L := by dsimp [L]; positivity
  have hKL : K ≤ L := by dsimp [L]; exact le_add_of_nonneg_right zero_le_one
  have hLip : LipschitzOnWith L u (ball 0 R) := (hKU.weaken hKL).mono hRU
  have hCH0 : 0 ≤ C_H := zero_le_one.trans hCH
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hF0 : 0 ≤ M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume := by positivity
  have hW : 0 ≤ (((L : ℝ)^2+‖u 0‖^2)*C_H) := by positivity
  have hfinite := variational_ground_energy_finite 2 Z
  have hspectrum : spectralGroundEnergy 2 Z =
      ((variationalGroundEnergy 2 Z).toReal : EReal) :=
    (spectralGroundEnergy_eq_variationalGroundEnergy 2 Z).trans
      (EReal.coe_toReal hfinite.1 hfinite.2).symm
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,
    coulomb_variational_energy_mem_spectrum 2 Z,
    fun z hz => coulomb_spectrum_re_lower_bound 2 Z hz,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,?_,?_⟩
  · intro ε hε hlim i t0 ht0
    exact nuclearKSPhysicalAnalyticDescent_derivative_data (originScaledDifference u ε) i
      ((hgain f hgraph u hu.continuous hAE L R ε hLip hε hlim).1 i t0 ht0) hA hF0
  · intro ε hε hlim t0 ht0
    exact pairKSPhysicalAnalyticDescent_derivative_data (originScaledDifference u ε)
      ((hgain f hgraph u hu.continuous hAE L R ε hLip hε hlim).2 t0 ht0) hA hF0

end TheoremT.Continuum
