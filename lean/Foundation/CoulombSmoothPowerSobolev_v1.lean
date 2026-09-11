import CoulombSmoothPowerEnergy_v1
import WeakH1SobolevEnergy_v1

/-! A critical-Lq bound for actual nonlinear tests of Coulomb eigenfunctions,
uniform in the regularization and cap. No eigenfunction boundedness or higher
integrability is a premise. Removing the truncation and iterating remain separate. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace TheoremT.Continuum

def smoothPowerEnergyCoefficient (N : ℕ) (Z E r : ℝ) : ℝ :=
  4*(1+4*r^2)*|E| +4*(1+4*r^2)^2*(2*(|Z| *(N : ℝ)+(N.choose 2 : ℝ)))^2

theorem smoothPowerEnergyCoefficient_nonneg (N : ℕ) (Z E r : ℝ) :
    0 ≤ smoothPowerEnergyCoefficient N Z E r := by unfold smoothPowerEnergyCoefficient; positivity

def smoothPowerSobolevCoefficient (N : ℕ) (Z E r : ℝ) : ℝ :=
  (configurationSobolevConstant N : ℝ)*Real.sqrt ((3*N : ℝ)*smoothPowerEnergyCoefficient N Z E r)

theorem smoothPowerSobolevCoefficient_nonneg (N : ℕ) (Z E r : ℝ) :
    0 ≤ smoothPowerSobolevCoefficient N Z E r := by unfold smoothPowerSobolevCoefficient; positivity

theorem scalar_eigen_smooth_power_sobolev {N : ℕ} (hN : 0 < N)
    {Z E a b r : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 ≤ r) :
    eLpNorm (smoothRadialPowerL2 ha hab hr f) (atomicSobolevExponent N) volume ≤
      ENNReal.ofReal (smoothPowerSobolevCoefficient N Z E r*‖smoothRadialPowerL2 ha hab hr f‖) := by
  obtain ⟨d,hd,_hdd⟩ := scalar_graph_hasH2 hg
  exact weakH1_sobolev_of_gradient_bound hN
    (fun k => smoothRadialPowerDerivativeL2 ha hab hr f (d k))
    (fun k => weakH1_smoothRadialPower ha hab hr d hd k)
    (smoothPowerEnergyCoefficient_nonneg N Z E r)
    (scalar_eigen_smooth_power_energy hg ha hab hr d hd)

#print axioms scalar_eigen_smooth_power_sobolev
end TheoremT.Continuum
