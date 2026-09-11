import UncappedRadialPower_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace TheoremT.Continuum

theorem radialPower_memLp {N : ℕ} {r : ℝ} (hr : 0 ≤ r) {f : SpatialL2 N}
    (hf : MemLp f (2*ENNReal.ofReal (2*r+1)) volume) :
    MemLp (fun x => radialPower r (f x)) 2 volume := by
  refine ⟨(radialPower_continuous hr).comp_aestronglyMeasurable (Lp.aestronglyMeasurable f),?_⟩
  rw [radialPower_eLpNorm hr]
  exact ENNReal.rpow_lt_top_of_nonneg (by linarith) hf.2.ne

def radialPowerL2 {N : ℕ} {r : ℝ} (hr : 0 ≤ r) {f : SpatialL2 N}
    (hf : MemLp f (2*ENNReal.ofReal (2*r+1)) volume) : SpatialL2 N :=
  (radialPower_memLp hr hf).toLp (fun x => radialPower r (f x))

theorem radialPowerL2_ae {N : ℕ} {r : ℝ} (hr : 0 ≤ r) {f : SpatialL2 N}
    (hf : MemLp f (2*ENNReal.ofReal (2*r+1)) volume) :
    radialPowerL2 hr hf =ᵐ[volume] (fun x => radialPower r (f x)) := MemLp.coeFn_toLp _

theorem cappedRadialPowerL2_tendsto {N : ℕ} {r : ℝ} (hr : 0 ≤ r) {f : SpatialL2 N}
    (hf : MemLp f (2*ENNReal.ofReal (2*r+1)) volume) :
    Tendsto (fun n : ℕ => cappedRadialPowerL2 (by positivity : 0 < (n:ℝ)+1) hr f)
      atTop (𝓝 (radialPowerL2 hr hf)) := by
  apply configuration_L2_tendsto_dominated _ _ (fun x => ‖radialPower r (f x)‖)
    (radialPower_memLp hr hf).norm
  · intro n
    filter_upwards [cappedRadialPowerL2_ae (by positivity : 0 < (n:ℝ)+1) hr f] with x hx
    rw [hx,Real.norm_eq_abs,abs_norm]
    exact cappedRadialPower_norm_le_power (by positivity) hr (f x)
  · filter_upwards [radialPowerL2_ae hr hf] with x hx
    rw [hx,Real.norm_eq_abs,abs_norm]
  · have hseq : ∀ᵐ x, ∀ n : ℕ, cappedRadialPowerL2
        (by positivity : 0 < (n:ℝ)+1) hr f x = smoothRadialPower 0 ((n:ℝ)+1) r (f x) := by
      rw [ae_all_iff]
      exact fun n => cappedRadialPowerL2_ae (by positivity : 0 < (n:ℝ)+1) hr f
    filter_upwards [hseq,radialPowerL2_ae hr hf] with x hx hx0
    simp_rw [hx,hx0]
    exact cappedRadialPower_tendsto hr (f x)

theorem scalar_eigen_radial_power_sobolev {N : ℕ} (hN : 0 < N)
    {Z E r : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (hr : 0 ≤ r) (hf : MemLp f (2*ENNReal.ofReal (2*r+1)) volume) :
    eLpNorm (radialPowerL2 hr hf) (atomicSobolevExponent N) volume ≤
      ENNReal.ofReal (smoothPowerSobolevCoefficient N Z E r*‖radialPowerL2 hr hf‖) := by
  have hl := cappedRadialPowerL2_tendsto hr hf
  apply eLpNorm_le_of_L2_tendsto_bound _ hl
    (fun n : ℕ => smoothPowerSobolevCoefficient N Z E r*
      ‖cappedRadialPowerL2 (by positivity : 0 < (n:ℝ)+1) hr f‖)
    (tendsto_const_nhds.mul hl.norm)
  exact fun n => scalar_eigen_capped_power_sobolev hN hg (by positivity) hr

#print axioms cappedRadialPowerL2_tendsto
#print axioms scalar_eigen_radial_power_sobolev
end TheoremT.Continuum
