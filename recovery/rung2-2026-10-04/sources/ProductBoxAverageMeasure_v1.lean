import IntervalPointwiseAverage_v1
import IntervalPointwiseL2_v1
import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact normalization of finite product interval averages and the resulting
volume-dependent L2 bounds. The box and its volume precede the function; the
L2 hypothesis is for actual restricted product volume. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι]

def productBoxVolume (a b : ι → ℝ) : ℝ := ∏ i, (b i-a i)

theorem productBoxVolume_pos {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    0 < productBoxVolume a b :=
  Finset.prod_pos (fun i _ => sub_pos.mpr (hab i))

theorem volume_product_closed_box (a b : ι → ℝ) :
    volume (Set.pi Set.univ (fun i => Icc (a i) (b i))) =
      ∏ i, ENNReal.ofReal (b i-a i) := by
  rw [volume_pi_pi]
  simp only [Real.volume_Icc]

theorem volume_product_closed_box_of_lt {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    volume (Set.pi Set.univ (fun i => Icc (a i) (b i))) =
      ENNReal.ofReal (productBoxVolume a b) := by
  rw [volume_product_closed_box,productBoxVolume,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => (sub_pos.mpr (hab i)).le)]

theorem product_interval_average_measure_eq {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    Measure.pi (fun i => intervalAverageMeasure (a i) (b i)) =
      (∏ i, ENNReal.ofReal (b i-a i))⁻¹ •
        volume.restrict (Set.pi Set.univ (fun i => Icc (a i) (b i))) := by
  let : ∀ i, IsProbabilityMeasure (intervalAverageMeasure (a i) (b i)) :=
    fun i => ⟨intervalAverageMeasure_univ (hab i)⟩
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply,Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib,volume_pi_pi]
  simp only [intervalAverageMeasure,Measure.smul_apply,Measure.restrict_apply (hs _),
    smul_eq_mul]
  rw [Finset.prod_mul_distrib,ENNReal.prod_inv_distrib
    (fun _ _ _ _ _ => Or.inr ENNReal.ofReal_ne_top)]

theorem product_box_average_integral_norm_le_L2
    {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    {F : Type*} [NormedAddCommGroup F] {g : (ι → ℝ) → F}
    (hg : MemLp g 2 (volume.restrict (Set.pi Set.univ (fun i => Icc (a i) (b i))))) :
    (∫ x, ‖g x‖ ∂Measure.pi (fun i => intervalAverageMeasure (a i) (b i))) ≤
      (Real.sqrt (productBoxVolume a b))⁻¹ *
        Real.sqrt (∫ x in Set.pi Set.univ (fun i => Icc (a i) (b i)), ‖g x‖^2) := by
  have hV := productBoxVolume_pos hab
  have hvol := volume_product_closed_box_of_lt hab
  let : IsFiniteMeasure
      (volume.restrict (Set.pi Set.univ (fun i => Icc (a i) (b i)))) :=
    ⟨by rw [Measure.restrict_apply_univ,hvol]; exact ENNReal.ofReal_lt_top⟩
  have h := mul_le_mul_of_nonneg_left (finite_measure_integral_norm_le_sqrt hg)
    (inv_nonneg.mpr hV.le)
  rw [Measure.restrict_apply_univ,hvol,ENNReal.toReal_ofReal hV.le] at h
  have hid : (productBoxVolume a b)⁻¹ * Real.sqrt (productBoxVolume a b) =
      (Real.sqrt (productBoxVolume a b))⁻¹ := by
    have hs := Real.sqrt_pos.mpr hV
    field_simp
    exact Real.sq_sqrt hV.le
  rw [product_interval_average_measure_eq hab,
    ← volume_product_closed_box a b,hvol,integral_smul_measure,
    ENNReal.toReal_inv,ENNReal.toReal_ofReal hV.le,smul_eq_mul]
  simpa only [← mul_assoc,hid] using h

theorem product_box_average_lintegral_enorm_le_L2
    {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    {F : Type*} [NormedAddCommGroup F] {g : (ι → ℝ) → F}
    (hg : MemLp g 2 (volume.restrict (Set.pi Set.univ (fun i => Icc (a i) (b i))))) :
    (∫⁻ x, ‖g x‖ₑ ∂Measure.pi (fun i => intervalAverageMeasure (a i) (b i))) ≤
      ENNReal.ofReal ((Real.sqrt (productBoxVolume a b))⁻¹ *
        Real.sqrt (∫ x in Set.pi Set.univ (fun i => Icc (a i) (b i)), ‖g x‖^2)) := by
  let : ∀ i, IsProbabilityMeasure (intervalAverageMeasure (a i) (b i)) :=
    fun i => ⟨intervalAverageMeasure_univ (hab i)⟩
  have hV := productBoxVolume_pos hab
  have hvol := volume_product_closed_box_of_lt hab
  have hga : MemLp g 2 (Measure.pi (fun i => intervalAverageMeasure (a i) (b i))) := by
    rw [product_interval_average_measure_eq hab,← volume_product_closed_box a b,hvol]
    exact hg.smul_measure (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hV)))
  have hgi : Integrable (fun x => ‖g x‖)
      (Measure.pi (fun i => intervalAverageMeasure (a i) (b i))) :=
    (hga.integrable (by norm_num)).norm
  have he := ofReal_integral_eq_lintegral_ofReal hgi
    (Filter.Eventually.of_forall (fun x => norm_nonneg (g x)))
  have h := ENNReal.ofReal_le_ofReal (product_box_average_integral_norm_le_L2 hab hg)
  simpa only [he,ofReal_norm] using h

theorem product_box_average_lintegral_indicator_enorm_le_L2
    {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    {F : Type*} [NormedAddCommGroup F] {g : (ι → ℝ) → F}
    (hg : MemLp g 2 (volume.restrict (Set.pi Set.univ (fun i => Icc (a i) (b i))))) :
    (∫⁻ x, (Set.pi Set.univ (fun i => Icc (a i) (b i))).indicator
      (fun y => ‖g y‖ₑ) x ∂Measure.pi (fun i => intervalAverageMeasure (a i) (b i))) ≤
      ENNReal.ofReal ((Real.sqrt (productBoxVolume a b))⁻¹ *
        Real.sqrt (∫ x in Set.pi Set.univ (fun i => Icc (a i) (b i)), ‖g x‖^2)) := by
  apply le_trans (lintegral_mono (fun x => ?_))
    (product_box_average_lintegral_enorm_le_L2 hab hg)
  by_cases hx : x ∈ Set.pi Set.univ (fun i => Icc (a i) (b i))
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

end TheoremT.Continuum
