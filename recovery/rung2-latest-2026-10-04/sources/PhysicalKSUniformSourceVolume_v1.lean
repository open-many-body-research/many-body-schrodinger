import KSCommonAnnulusFactorialWords_v1

/-! A fixed finite volume bound for every physical unit-center coefficient
box in the canonical 4+3 coordinate space. This constant is independent of
the selected chart, center, scale, derivative word and complex amplitude. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
open WeakGrushin

def physicalKSUniformSourceVolume : ℝ :=
  (volume (Metric.closedBall (0 : Space (Fin 3)) 2)).toReal

theorem physicalKSUniformSourceVolume_nonneg : 0 ≤ physicalKSUniformSourceVolume :=
  ENNReal.toReal_nonneg

theorem physicalKS_box_subset_fixed_ball {t0 : Position} (ht0 : ‖t0‖ = 1) :
    rectangularOpenBox (0,t0) (1/128) (1/128) ⊆
      Metric.closedBall (0 : Space (Fin 3)) 2 := by
  intro p hp
  have hc := rectangularOpenBox_subset_closedBox (0,t0) (1/128) (1/128) hp
  have hy := rectangularClosedBox_y_norm (0,t0) (by norm_num : (0:ℝ) ≤ 1/128) hc
  have ht := rectangularClosedBox_t_norm (0,t0) (by norm_num : (0:ℝ) ≤ 1/128) hc
  have hn := norm_sub_norm_le p.2 t0
  simp only [Prod.fst,Prod.snd,sub_zero] at hy ht
  rw [ht0] at hn
  rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def]
  exact max_le (by linarith) (by linarith)

theorem physicalKS_box_volume_bound {t0 : Position} (ht0 : ‖t0‖ = 1) :
    volume (rectangularOpenBox (0,t0) (1/128) (1/128)) < ⊤ ∧
      (volume (rectangularOpenBox (0,t0) (1/128) (1/128))).toReal ≤
        physicalKSUniformSourceVolume := by
  have hm : volume (rectangularOpenBox (0,t0) (1/128) (1/128)) ≤
      volume (Metric.closedBall (0 : Space (Fin 3)) 2) :=
    measure_mono (physicalKS_box_subset_fixed_ball ht0)
  have hf : volume (Metric.closedBall (0 : Space (Fin 3)) 2) < ⊤ :=
    (isCompact_closedBall (0 : Space (Fin 3)) (2 : ℝ)).measure_lt_top
  exact ⟨hm.trans_lt hf,ENNReal.toReal_mono hf.ne hm⟩

end TheoremT.Continuum
