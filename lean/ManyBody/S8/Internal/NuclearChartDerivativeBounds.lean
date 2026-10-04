import ManyBody.S8.Internal.NuclearChartBounds
import WeakGrushinJetFields_v1
import NuclearKSPotentialSmooth_v1
import Mathlib.Analysis.Calculus.FDeriv.Norm
/-!
Actual first spectator-direction bounds for the existing two-electron nuclear
KS coefficient on the fixed unit spectator chart.

The existing physical position maps determine the derivative: the selected
KS position and its radial prefactor are constant in a pure spectator
direction, while the other electron position has unit basis derivative.
The norm/inverse chain rules give
`|D_T B| ≤ 8 ‖Y‖² (|Z| / ‖T‖² + 1 / ‖KS(Y) - T‖²)`.
The chart distances 3/4 and 11/16 and the bound ‖Y‖² ≤ 1/16 give
`|D_T B| ≤ (8/9)|Z| + 128/121`, including Y = 0.

No transformed potential or derivative formula is introduced as a premise.
This is a coefficient bound, not a regularity or analyticity conclusion.
-/
noncomputable section
open scoped ContDiff
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin
namespace ManyBody.S8

/-- The actual other-electron position map on the existing spectator coordinates. -/
def spectatorPositionCLM :
    SpectatorConfiguration (0 : Fin 2) →L[ℝ] Position :=
  (electronPositionCLM (1 : Fin 2)).comp
    ((configurationProductEquiv (0 : Fin 2)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ Position (SpectatorConfiguration (0 : Fin 2))))

theorem nuclearKSLift_other_position (q : NuclearKSSpace (0 : Fin 2)) :
    position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) = spectatorPositionCLM q.2 := by
  change position (configurationReassemble (0 : Fin 2) (ksMap q.1) q.2) (1 : Fin 2) =
    position (configurationReassemble (0 : Fin 2) 0 q.2) (1 : Fin 2)
  ext k
  change configurationReassemble (0 : Fin 2) (ksMap q.1) q.2 (1,k) =
    configurationReassemble (0 : Fin 2) 0 q.2 (1,k)
  rw [configurationReassemble_spectator (0 : Fin 2) (ksMap q.1) q.2 ⟨(1,k), by change (1 : Fin 2) ≠ 0; decide⟩,
    configurationReassemble_spectator (0 : Fin 2) 0 q.2 ⟨(1,k), by change (1 : Fin 2) ≠ 0; decide⟩]

theorem spectatorPositionCLM_basis_norm (j : SpectatorCoordinate (0 : Fin 2)) :
    ‖spectatorPositionCLM (oscillatorBasis j)‖ = 1 := by
  have hj : j.val.1 = (1 : Fin 2) := by
    rcases j with ⟨⟨a,b⟩,ha⟩
    fin_cases a
    · exact False.elim (ha rfl)
    · rfl
  have heq : spectatorPositionCLM (oscillatorBasis j) = oscillatorBasis j.val.2 := by
    ext k
    change configurationReassemble (0 : Fin 2) 0 (oscillatorBasis j) (1,k) = _
    rw [configurationReassemble_spectator (0 : Fin 2) 0
      (oscillatorBasis j) ⟨(1,k), by change (1 : Fin 2) ≠ 0; decide⟩]
    simp only [oscillatorBasis, EuclideanSpace.single, PiLp.single_apply]
    have hiff : (⟨(1,k), by change (1 : Fin 2) ≠ 0; decide⟩ : SpectatorCoordinate (0 : Fin 2)) = j ↔ k = j.val.2 := by
      constructor
      · intro h
        exact congrArg (fun a : SpectatorCoordinate (0 : Fin 2) => a.val.2) h
      · intro h
        apply Subtype.ext
        exact Prod.ext hj.symm h
    simp only [hiff]
  rw [heq]
  simp only [oscillatorBasis, EuclideanSpace.single, PiLp.norm_single, norm_one]

theorem inv_norm_directional_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : G → Position} {q : G} (hF : DifferentiableAt ℝ F q) (hne : F q ≠ 0)
    (v : G) (hv : ‖fderiv ℝ F q v‖ ≤ 1) :
    |fderiv ℝ (fun p => ‖F p‖⁻¹) q v| ≤ (‖F q‖ ^ 2)⁻¹ := by
  have hn : DifferentiableAt ℝ (norm : Position → ℝ) (F q) :=
    (contDiffAt_norm ℝ (n := 1) hne).differentiableAt one_ne_zero
  have hnf : DifferentiableAt ℝ (fun p => ‖F p‖) q := hn.comp q hF
  have hnd : |fderiv ℝ (fun p => ‖F p‖) q v| ≤ 1 := by
    change ‖fderiv ℝ ((norm : Position → ℝ) ∘ F) q v‖ ≤ 1
    rw [fderiv_comp q hn hF, ContinuousLinearMap.comp_apply]
    have hh := (fderiv ℝ (norm : Position → ℝ) (F q)).le_opNorm (fderiv ℝ F q v)
    rw [norm_fderiv_norm hn, one_mul] at hh
    exact hh.trans hv
  change |fderiv ℝ ((fun t : ℝ => t⁻¹) ∘ (fun p => ‖F p‖)) q v| ≤ _
  rw [fderiv_comp q (differentiableAt_inv_iff.mpr (norm_ne_zero_iff.mpr hne)) hnf,
    fderiv_inv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [smul_eq_mul, abs_mul, abs_neg, abs_inv, abs_pow, abs_norm]
  exact (mul_le_mul_of_nonneg_right hnd (by positivity)).trans_eq (one_mul _)

/-- The coefficient derivative bound also holds on the closed geometric chart. -/
theorem nuclearKSPotential_spectator_abs_le_of_closed_chart
    (Z E : ℝ) (t0 : Position) (ht0 : ‖t0‖ = 1)
    {q : NuclearKSSpace (0 : Fin 2)}
    (hY : ‖q.1‖ ≤ (1 / 4 : ℝ))
    (hTchart : ‖position (nuclearKSLift (0 : Fin 2) q) (1 : Fin 2) - t0‖ ≤ (1 / 4 : ℝ))
    (j : SpectatorCoordinate (0 : Fin 2)) :
    |fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E) q (tDir j)| ≤
      (8 / 9 : ℝ) * |Z| + 128 / 121 := by
  let T : NuclearKSSpace (0 : Fin 2) → Position := fun p => spectatorPositionCLM p.2
  let P : NuclearKSSpace (0 : Fin 2) → Position := fun p => ksMap p.1 - T p
  let R : NuclearKSSpace (0 : Fin 2) → ℝ := fun p => ‖p.1‖ ^ 2
  let V : NuclearKSSpace (0 : Fin 2) → ℝ := fun p => -Z * ‖T p‖⁻¹ + ‖P p‖⁻¹ - E
  have hTeq : ∀ p : NuclearKSSpace (0 : Fin 2),
      position (nuclearKSLift (0 : Fin 2) p) (1 : Fin 2) = T p :=
    nuclearKSLift_other_position
  have hPeq : ∀ p : NuclearKSSpace (0 : Fin 2),
      position (nuclearKSLift (0 : Fin 2) p) (0 : Fin 2) -
        position (nuclearKSLift (0 : Fin 2) p) (1 : Fin 2) = P p := by
    intro p
    rw [nuclearKSLift_selected_position, hTeq]
  obtain ⟨htl, _, _, hpl⟩ := nuclearChart_closed_geometry t0 ht0 hY hTchart
  rw [hTeq] at htl
  rw [hPeq] at hpl
  have hTne : T q ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) htl)
  have hPne : P q ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 11 / 16) hpl)
  have hTd : HasFDerivAt T
      (spectatorPositionCLM.comp (ContinuousLinearMap.snd ℝ KSSpace (SpectatorConfiguration (0 : Fin 2)))) q :=
    spectatorPositionCLM.hasFDerivAt.comp q hasFDerivAt_snd
  have hX : DifferentiableAt ℝ (fun p : NuclearKSSpace (0 : Fin 2) => ksMap p.1) q :=
    (ksMap_contDiff.differentiable (by norm_num)).differentiableAt.comp q
      hasFDerivAt_fst.differentiableAt
  have hX0 : fderiv ℝ (fun p : NuclearKSSpace (0 : Fin 2) => ksMap p.1) q (tDir j) = 0 := by
    change fderiv ℝ (ksMap ∘ Prod.fst) q (tDir j) = 0
    rw [fderiv_comp q (ksMap_contDiff.differentiable (by norm_num)).differentiableAt
      hasFDerivAt_fst.differentiableAt, ContinuousLinearMap.comp_apply, fderiv_fst]
    change (fderiv ℝ _ _) 0 = 0
    exact map_zero _
  have hTder : ‖fderiv ℝ T q (tDir j)‖ = 1 := by
    rw [hTd.fderiv]
    change ‖spectatorPositionCLM (oscillatorBasis j)‖ = 1
    exact spectatorPositionCLM_basis_norm j
  have hPd : DifferentiableAt ℝ P q := hX.sub hTd.differentiableAt
  have hPder : ‖fderiv ℝ P q (tDir j)‖ = 1 := by
    change ‖fderiv ℝ ((fun p : NuclearKSSpace (0 : Fin 2) => ksMap p.1) - T) q (tDir j)‖ = 1
    rw [fderiv_sub hX hTd.differentiableAt, sub_apply, hX0, zero_sub, norm_neg]
    exact hTder
  have hTi : DifferentiableAt ℝ (fun p => ‖T p‖⁻¹) q :=
    (hTd.differentiableAt.norm ℝ hTne).inv (norm_ne_zero_iff.mpr hTne)
  have hPi : DifferentiableAt ℝ (fun p => ‖P p‖⁻¹) q :=
    (hPd.norm ℝ hPne).inv (norm_ne_zero_iff.mpr hPne)
  have hTinv := inv_norm_directional_le hTd.differentiableAt hTne (tDir j) hTder.le
  have hPinv := inv_norm_directional_le hPd hPne (tDir j) hPder.le
  have hV : DifferentiableAt ℝ V q := ((hTi.const_mul (-Z)).add hPi).sub_const E
  have hVder : fderiv ℝ V q (tDir j) =
      -Z * fderiv ℝ (fun p => ‖T p‖⁻¹) q (tDir j) +
        fderiv ℝ (fun p => ‖P p‖⁻¹) q (tDir j) := by
    dsimp only [V]
    rw [fderiv_sub_const E, fderiv_fun_add (hTi.const_mul (-Z)) hPi, fderiv_const_mul hTi (-Z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hVbound : |fderiv ℝ V q (tDir j)| ≤
      |Z| * (‖T q‖ ^ 2)⁻¹ + (‖P q‖ ^ 2)⁻¹ := by
    rw [hVder]
    calc
      _ ≤ |-Z * fderiv ℝ (fun p => ‖T p‖⁻¹) q (tDir j)| +
          |fderiv ℝ (fun p => ‖P p‖⁻¹) q (tDir j)| := abs_add_le _ _
      _ = |Z| * |fderiv ℝ (fun p => ‖T p‖⁻¹) q (tDir j)| +
          |fderiv ℝ (fun p => ‖P p‖⁻¹) q (tDir j)| := by rw [abs_mul, abs_neg]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hTinv (abs_nonneg Z)) hPinv
  have hR : DifferentiableAt ℝ R q :=
    (hasFDerivAt_fst (𝕜 := ℝ) (E := KSSpace)
      (F := SpectatorConfiguration (0 : Fin 2)) (p := q)).norm_sq.differentiableAt
  have hRzero : fderiv ℝ R q (tDir j) = 0 := by
    change fderiv ℝ ((fun y : KSSpace => ‖y‖ ^ 2) ∘ Prod.fst) q (tDir j) = 0
    rw [fderiv_comp q (hasStrictFDerivAt_norm_sq q.1).differentiableAt
      hasFDerivAt_fst.differentiableAt, ContinuousLinearMap.comp_apply, fderiv_fst]
    change (fderiv ℝ _ _) 0 = 0
    exact map_zero _
  have hBfun : nuclearKSPotential (0 : Fin 2) Z E =
      fun p => -8 * Z + (8 * R p) * V p := by
    funext p
    dsimp only [nuclearKSPotential, R, V]
    rw [coulombWithoutSelectedNucleus_two_electrons, hPeq, hTeq]
  have hBder : fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E) q (tDir j) =
      8 * R q * fderiv ℝ V q (tDir j) := by
    rw [hBfun, fderiv_const_add]
    rw [fderiv_fun_mul (hR.const_mul 8) hV, fderiv_const_mul hR 8]
    simp only [add_apply, smul_apply, smul_eq_mul, hRzero,
      mul_zero, add_zero]
  have hTinvSq : (‖T q‖ ^ 2)⁻¹ ≤ (16 / 9 : ℝ) := by
    have htpos : 0 < ‖T q‖ := norm_pos_iff.mpr hTne
    have htsq : (9 / 16 : ℝ) ≤ ‖T q‖ ^ 2 := by nlinarith [sq_nonneg (‖T q‖ - 3 / 4)]
    have hh := (inv_le_inv₀ (by positivity : 0 < ‖T q‖ ^ 2) (by norm_num : (0 : ℝ) < 9 / 16)).mpr htsq
    norm_num at hh
    exact hh
  have hPinvSq : (‖P q‖ ^ 2)⁻¹ ≤ (256 / 121 : ℝ) := by
    have hppos : 0 < ‖P q‖ := norm_pos_iff.mpr hPne
    have hpsq : (121 / 256 : ℝ) ≤ ‖P q‖ ^ 2 := by nlinarith [sq_nonneg (‖P q‖ - 11 / 16)]
    have hh := (inv_le_inv₀ (by positivity : 0 < ‖P q‖ ^ 2) (by norm_num : (0 : ℝ) < 121 / 256)).mpr hpsq
    norm_num at hh
    exact hh
  have hRbound : 8 * R q ≤ (1 / 2 : ℝ) := by
    have hsq := (sq_le_sq₀ (norm_nonneg q.1) (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hY
    dsimp only [R]
    nlinarith
  rw [hBder, abs_mul]
  have hRnonneg : 0 ≤ 8 * R q := by dsimp only [R]; positivity
  rw [abs_of_nonneg hRnonneg]
  calc
    _ ≤ 8 * R q * (|Z| * (‖T q‖ ^ 2)⁻¹ + (‖P q‖ ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hVbound hRnonneg
    _ ≤ 8 * R q * (|Z| * (16 / 9 : ℝ) + 256 / 121) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hTinvSq (abs_nonneg Z)) hPinvSq) hRnonneg
    _ ≤ (1 / 2 : ℝ) * (|Z| * (16 / 9 : ℝ) + 256 / 121) :=
      mul_le_mul_of_nonneg_right hRbound (by positivity)
    _ = _ := by ring

theorem nuclearKSPotential_spectator_abs_le_of_mem_nuclearChartOpen
    (Z E : ℝ) (t0 : Position) (ht0 : ‖t0‖ = 1)
    {q : NuclearKSSpace (0 : Fin 2)} (hq : q ∈ nuclearChartOpen t0)
    (j : SpectatorCoordinate (0 : Fin 2)) :
    |fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E) q (tDir j)| ≤
      (8 / 9 : ℝ) * |Z| + 128 / 121 :=
  nuclearKSPotential_spectator_abs_le_of_closed_chart Z E t0 ht0 hq.1.le hq.2.le j

#print axioms nuclearKSLift_other_position
#print axioms spectatorPositionCLM_basis_norm
#print axioms inv_norm_directional_le
#print axioms nuclearKSPotential_spectator_abs_le_of_closed_chart
#print axioms nuclearKSPotential_spectator_abs_le_of_mem_nuclearChartOpen

end ManyBody.S8

