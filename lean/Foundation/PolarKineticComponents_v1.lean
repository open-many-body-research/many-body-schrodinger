import PolarKineticIntegrability_v1

/-! Integrability of the actual radial and tangential kinetic components in
polar coordinates. Domination is derived from the Euclidean orthogonal split,
not assumed as an analytic input. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Polar

def polarRadialDensity (f : EnergyR3 → ℂ) (r : ℝ) (w : EnergySphere) : ℝ :=
  ‖fderiv ℝ f (r • w.val) w.val‖ ^ 2

def polarTangentialDensity (f : EnergyR3 → ℂ) (i : Fin 3)
    (r : ℝ) (w : EnergySphere) : ℝ :=
  ‖fderiv ℝ f (r • w.val) (EuclideanSpace.single i 1) -
    w.val i • fderiv ℝ f (r • w.val) w.val‖ ^ 2

theorem polarRadialDensity_continuous {f : EnergyR3 → ℂ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun p : ℝ × EnergySphere => polarRadialDensity f p.1 p.2) := by
  exact (((hf.continuous_fderiv (by simp)).comp
    (continuous_fst.smul continuous_snd.subtype_val)).clm_apply
      continuous_snd.subtype_val).norm.pow 2

theorem polarTangentialDensity_continuous {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    Continuous (fun p : ℝ × EnergySphere => polarTangentialDensity f i p.1 p.2) := by
  have hd := (hf.continuous_fderiv (by simp)).comp
    (continuous_fst.smul continuous_snd.subtype_val :
      Continuous (fun p : ℝ × EnergySphere => p.1 • p.2.val))
  exact ((hd.clm_apply continuous_const).sub
    (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp
      continuous_snd.subtype_val).smul (hd.clm_apply continuous_snd.subtype_val))).norm.pow 2

theorem polarRadialDensity_sphere_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    Integrable (polarRadialDensity f r) (volume : Measure EnergyR3).toSphere :=
  ((polarRadialDensity_continuous hf).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem polarTangentialDensity_sphere_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) (i : Fin 3) :
    Integrable (polarTangentialDensity f i r) (volume : Measure EnergyR3).toSphere :=
  ((polarTangentialDensity_continuous hf i).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fullKineticDensity_polar_split (f : EnergyR3 → ℂ) (r : ℝ) (w : EnergySphere) :
    fullKineticDensity f (r • w.val) = polarRadialDensity f r w +
      ∑ i : Fin 3, polarTangentialDensity f i r w := by
  exact euclidean_unit_direction_decomposition (fderiv ℝ f (r • w.val)) w.val
    (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)

theorem polarRadialDensity_le (f : EnergyR3 → ℂ) (r : ℝ) (w : EnergySphere) :
    polarRadialDensity f r w ≤ fullKineticDensity f (r • w.val) := by
  rw [fullKineticDensity_polar_split]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sq_nonneg _))

theorem polarTangentialDensity_le (f : EnergyR3 → ℂ) (r : ℝ) (w : EnergySphere) (i : Fin 3) :
    polarTangentialDensity f i r w ≤ fullKineticDensity f (r • w.val) := by
  rw [fullKineticDensity_polar_split]
  calc
    polarTangentialDensity f i r w ≤ ∑ j : Fin 3, polarTangentialDensity f j r w :=
      Finset.single_le_sum (fun j _ => (show 0 ≤ polarTangentialDensity f j r w from sq_nonneg _))
        (Finset.mem_univ i)
    _ ≤ _ := le_add_of_nonneg_left (sq_nonneg _)

theorem polarRadialDensity_product_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun p : EnergySphere × Ioi (0 : ℝ) => polarRadialDensity f p.2.val p.1)
      ((volume : Measure EnergyR3).toSphere.prod (Measure.volumeIoiPow 2)) := by
  apply (fullKineticDensity_polar_integrable hf hc).mono'
    (((polarRadialDensity_continuous hf).comp
      (continuous_snd.subtype_val.prodMk continuous_fst)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact polarRadialDensity_le f p.2.val p.1

theorem polarTangentialDensity_product_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (i : Fin 3) :
    Integrable (fun p : EnergySphere × Ioi (0 : ℝ) => polarTangentialDensity f i p.2.val p.1)
      ((volume : Measure EnergyR3).toSphere.prod (Measure.volumeIoiPow 2)) := by
  apply (fullKineticDensity_polar_integrable hf hc).mono'
    (((polarTangentialDensity_continuous hf i).comp
      (continuous_snd.subtype_val.prodMk continuous_fst)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact polarTangentialDensity_le f p.2.val p.1 i

theorem polarRadialEnergy_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    IntegrableOn (fun r : ℝ => r ^ 2 *
      ∫ w : EnergySphere, polarRadialDensity f r w ∂(volume : Measure EnergyR3).toSphere) (Ioi 0) :=
  (integrable_volumeIoiPow_iff_weighted 2 _).mp
    (polarRadialDensity_product_integrable hf hc).integral_prod_right

theorem polarTangentialEnergy_integrable {f : EnergyR3 → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (i : Fin 3) :
    IntegrableOn (fun r : ℝ => r ^ 2 *
      ∫ w : EnergySphere, polarTangentialDensity f i r w ∂(volume : Measure EnergyR3).toSphere) (Ioi 0) :=
  (integrable_volumeIoiPow_iff_weighted 2 _).mp
    (polarTangentialDensity_product_integrable hf hc i).integral_prod_right

end TheoremT.Polar
