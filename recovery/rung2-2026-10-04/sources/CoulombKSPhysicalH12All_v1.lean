import CoulombKSPhysicalH12DataAll_v1
import CoulombKSScaledFiniteReserve_v1
import KSScaledFiveYReserve_v1
import ProductCoordinateWeakHk_v1

/-! Both selected nuclear charts in their actual spectator domains. Constants
are selected on the fixed chart-specific annulus before the center, solution
and dilation. The proof uses actual scalar Coulomb and KS equations directly;
no exchange of electrons or identification of spectator measures is assumed. -/
noncomputable section
open MeasureTheory Metric
open scoped ContDiff NNReal
namespace TheoremT.Continuum
open WeakGrushin

set_option maxHeartbeats 1600000 in
theorem scalar_coulomb_nuclear_physical_coordinate_h12 (i : Fin 2) (Z E C1 C2 : ℝ)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2) :
    ∃ KT KY QY : ℝ, 1 ≤ KT ∧ 1 ≤ KY ∧ 0 ≤ QY ∧
      0 ≤ ksH12MixedBudgetAt i 4 C1 C2 KT KY QY ∧
      ∀ t0 : SpectatorConfiguration i, ‖t0‖ = 1 →
      ∀ f : SpatialL2 2, scalarHamiltonianGraph 2 Z f ((E : ℂ) • f) →
      ∀ g : Configuration 2 → ℂ, Continuous g → (f : Configuration 2 → ℂ) =ᵐ[volume] g →
      ∀ (L : ℝ≥0) (R ε : ℝ), LipschitzOnWith L g (ball 0 R) →
        0 < ε → ε ≤ min 1 (R/4) →
        ProductCoordinateWeakHk
          ((physicalSpectatorReindexAt i) ⁻¹' rectangularOpenBox (0,(twoElectronSpectatorPositionEquiv i) t0) (1/128) (1/128))
          (originScaledDifference g ε ∘ (nuclearKSLift i)) 12
          (((L : ℝ)^2+‖g 0‖^2)*ksH12MixedBudgetAt i 4 C1 C2 KT KY QY) := by
  have hbox : ∀ q ∈ (ksCommonAnnulusRegionAt i),
      ‖q.1‖ ≤ (1/4 : ℝ) ∧ ‖q.2‖ ≤ (5/4 : ℝ) := by
    intro q hq
    obtain ⟨hy,_,ht⟩ := (ksCommonAnnulusRegionAt_mem_iff i q).mp hq
    exact ⟨hy,ht⟩
  obtain ⟨KT,hKT,hTgain⟩ := scalar_coulomb_nuclear_scaled_finite_reserve i Z E
    (ksCommonAnnulusRegionAt_isCompact i) (ksCommonAnnulusRegionAt_subset_nuclear_patch i) hbox 12
  obtain ⟨KY,QY,hKY,hQY,hYgain⟩ := nuclearKS_scaled_five_y_reserve i Z E
    (ksCommonAnnulusRegionAt_isCompact i) (ksCommonAnnulusRegionAt_subset_nuclear_patch i)
  have hKT0 : 0 ≤ KT := le_trans (by norm_num) hKT
  have hCT : 0 ≤ ksH12SpectatorBudgetAt i 4 C1 C2 KT :=
    ksH12SpectatorBudgetAt_nonneg i (by norm_num) C1 C2 KT hKT0
  have hCY : 0 ≤ ksH12MixedBudgetAt i 4 C1 C2 KT KY QY :=
    ksH12MixedBudgetAt_nonneg i (by norm_num) C1 C2 KT KY QY hKT0
  refine ⟨KT,KY,QY,hKT,hKY,hQY,hCY,?_⟩
  intro t0 ht0 f hgraph g hg hfg L R ε hLip hε hεlim
  have hε1 : ε ≤ 1 := hεlim.trans (min_le_left _ _)
  have hεR : ε ≤ R/4 := hεlim.trans (min_le_right _ _)
  have hR : 0 < R := by linarith
  let t := (twoElectronSpectatorPositionEquiv i) t0
  let ΩT := physicalH12ScheduleRegion i t 0
  let ΩY := physicalH12ScheduleRegion i t 24
  let amp : ℝ := (L : ℝ)^2+‖g 0‖^2
  have hamp : 0 ≤ amp := by positivity
  have hTΩ : ΩT 0 ⊆ ksCommonAnnulusRegionAt i := physicalH12Schedule_subset_commonAnnulusAt i ht0 0 0
  have hYΩ : ΩY 0 ⊆ ksCommonAnnulusRegionAt i := physicalH12Schedule_subset_commonAnnulusAt i ht0 24 0
  have hwT : 0 ≤ ksH12CutoffWeight 4 C1 := ksH12CutoffWeight_nonneg (by norm_num) C1
  have hwY : 0 ≤ ksH12CutoffWeight 0 C1 := ksH12CutoffWeight_nonneg (by norm_num) C1
  obtain ⟨_hTr,hT⟩ := hTgain ΩT (physicalH12ScheduleMiddle i t 0)
    (physicalH12ScheduleInnerCutoff i t 0)
    (physicalH12ScheduleEnergyCutoff i t 0)
    (fun _ => 1) (fun _ => ksH12CutoffScalar 4 C1 C2)
    (fun _ => ksH12CutoffWeight 4 C1) (fun _ => 1) (fun _ => ksH12CutoffWeight 4 C1)
    (physical_h12_T12_geometry i t (by norm_num) hC1 hC2)
    (physicalH12ScheduleRegion_measurableSet i t 0 0) hTΩ
    f hgraph g hg hfg L R ε hR hLip hε hε1 hεR
  have hTC : SpectatorFiniteState (ΩT 12) (originScaledDifference g ε ∘ (nuclearKSLift i)) 12
      (amp*ksH12SpectatorBudgetAt i 4 C1 C2 KT) := by
    apply hT.mono_budget
    exact spectatorIterationBudgetSeq_common_bound 4 _ _ _ _ _ KT (by norm_num)
      (ksH12_source_amplitude_bound_at i KT L (g 0) hTΩ)
      (ksH12_initial_amplitude_bound_at i L (g 0)) 12
      (fun _ _ => hwT) (fun _ _ => by norm_num) (fun _ _ => hwT)
  have hJoin : ΩT 12 = ΩY 0 := physicalH12Schedule_T12_Y5_join i t
  rw [hJoin] at hTC
  have hEq : ∀ φ : (NuclearKSSpace i) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ΩY 0 →
      (∫ p, splitGrushin 4 oscillatorBasis
        (epsilonNuclearKSPotential i ε Z E) φ p •
          (originScaledDifference g ε ∘ (nuclearKSLift i)) p) =
      ∫ p, φ p • ((nuclearKSPotential i Z (ε*E)) p • (-g 0)) := by
    intro φ hφ hc hs
    have he := (scalar_coulomb_epsilon_nuclear_KS_difference_weak i hε hgraph hg hfg hφ hc
      (hs.trans (hYΩ.trans (ksCommonAnnulusRegionAt_subset_nuclear_patch i)))).2.2
    have hBasis : (spectatorBasis : SpectatorCoordinate i →
        SpectatorConfiguration i) = oscillatorBasis := by
      funext j
      simp only [spectatorBasis,oscillatorBasis,EuclideanSpace.single,PiLp.single]
    rw [hBasis] at he
    simpa only [Function.comp_apply,Complex.real_smul,smul_neg,mul_neg] using he
  obtain ⟨_hYr,hY⟩ := hYgain ΩY (physicalH12ScheduleMiddle i t 24)
    (physicalH12ScheduleInnerCutoff i t 24)
    (physicalH12ScheduleEnergyCutoff i t 24)
    (fun _ => 1) (fun _ => ksH12CutoffScalar 0 C1 C2)
    (fun _ => ksH12CutoffWeight 0 C1) (fun _ => 1) (fun _ => ksH12CutoffWeight 0 C1)
    (physical_h12_Y5_geometry i t hC1 hC2)
    (fun k _ => physicalH12ScheduleRegion_isOpen i t 24 (k+1)) hYΩ
    ε hε.le hε1 (g 0) (originScaledDifference g ε ∘ (nuclearKSLift i))
    (amp*ksH12SpectatorBudgetAt i 4 C1 C2 KT) (mul_nonneg hamp hCT) hTC hEq
  rw [twoElectronSpectatorCoordinate_card] at hY
  have hYC : MixedTriangularState (ΩY 5) (originScaledDifference g ε ∘ (nuclearKSLift i)) 12 12
      (amp*ksH12MixedBudgetAt i 4 C1 C2 KT KY QY) := by
    apply hY.restrict Set.Subset.rfl
    exact mixedYIterationBudgetSeq_common_bound 4 _ _ _ _ _ KY QY 12 3 hamp
      (ksH12_source_amplitude_bound_at i KY L (g 0) hYΩ) le_rfl 5
      (fun _ _ => hwY) (fun _ _ => by norm_num) (fun _ _ => hwY)
  have hEnd : ΩY 5 = (physicalSpectatorReindexAt i) ⁻¹'
      rectangularOpenBox (0,(twoElectronSpectatorPositionEquiv i) t0) (1/128) (1/128) := by
    exact physicalH12Schedule_terminal i t
  have hW := mixedTriangularState_coordinateWeakHk hYC
  rw [hEnd] at hW
  exact hW

end TheoremT.Continuum
