import ManyBody.S8.Internal.NuclearChartDerivativeBounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-!
Mixed second spectator derivatives of the actual two-electron nuclear KS
coefficient. All derivatives are taken of the existing physical potential.
-/
noncomputable section
open scoped ContDiff
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin
namespace ManyBody.S8

private theorem hasFDerivAt_position_norm (x : Position) (hx : x ≠ 0) :
    HasFDerivAt (norm : Position → ℝ) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have hf : (fun y : Position => Real.sqrt (‖y‖ ^ 2)) = norm := by
    funext y
    exact Real.sqrt_sq (norm_nonneg y)
  rw [hf, Real.sqrt_sq (norm_nonneg x)] at h
  have heq : ‖x‖⁻¹ • innerSL ℝ x =
      (1 / (2 * ‖x‖)) • (2 • innerSL ℝ x) := by
    ext v
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, two_smul, add_apply]
    field_simp
    ring
  rw [heq]
  exact h

private theorem inv_norm_directional_eq
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : G → Position} {q : G} (hF : DifferentiableAt ℝ F q) (hne : F q ≠ 0)
    (v : G) :
    fderiv ℝ (fun p => ‖F p‖⁻¹) q v =
      -inner ℝ (F q) (fderiv ℝ F q v) * (‖F q‖⁻¹) ^ 3 := by
  have hn := (hasFDerivAt_position_norm (F q) hne).comp q hF.hasFDerivAt
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hne)).comp_hasFDerivAt q hn
  change fderiv ℝ ((fun y : ℝ => y⁻¹) ∘ norm ∘ F) q v = _
  rw [hi.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  field_simp

private theorem inv_norm_gradient_directional_eq
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : G → Position} {q : G} (hF : DifferentiableAt ℝ F q) (hne : F q ≠ 0)
    (v : Position) (w : G) :
    fderiv ℝ (fun p => -inner ℝ (F p) v * (‖F p‖⁻¹) ^ 3) q w =
      -inner ℝ (fderiv ℝ F q w) v * (‖F q‖⁻¹) ^ 3 +
      3 * inner ℝ (F q) v * inner ℝ (F q) (fderiv ℝ F q w) * (‖F q‖⁻¹) ^ 5 := by
  have hd : DifferentiableAt ℝ (fun p => inner ℝ (F p) v) q :=
    hF.inner ℝ (differentiableAt_const v)
  have hi : DifferentiableAt ℝ (fun p => ‖F p‖⁻¹) q :=
    (hF.norm ℝ hne).inv (norm_ne_zero_iff.mpr hne)
  have hdneg : DifferentiableAt ℝ (fun p => -inner ℝ (F p) v) q := hd.neg
  have hipow : DifferentiableAt ℝ (fun p => (‖F p‖⁻¹) ^ 3) q := hi.pow 3
  rw [fderiv_fun_mul hdneg hipow]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_fun_neg, fderiv_fun_pow 3 hi]
  simp only [neg_apply, smul_apply, smul_eq_mul]
  rw [fderiv_inner_apply ℝ hF (differentiableAt_const v) w,
    inv_norm_directional_eq hF hne]
  simp only [fderiv_const_apply, zero_apply, inner_zero_right, zero_add]
  ring

private theorem inv_norm_directional_differentiableAt
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : G → Position} {q : G} {Ω : Set G} (hΩ : IsOpen Ω) (hq : q ∈ Ω)
    (hF : DifferentiableOn ℝ F Ω) (hne : ∀ p ∈ Ω, F p ≠ 0)
    (v : G) (a : Position) (ha : ∀ p ∈ Ω, fderiv ℝ F p v = a) :
    DifferentiableAt ℝ (fun p => fderiv ℝ (fun z => ‖F z‖⁻¹) p v) q := by
  have hFq := (hF q hq).differentiableAt (hΩ.mem_nhds hq)
  have hi : DifferentiableAt ℝ (fun p => ‖F p‖⁻¹) q :=
    (hFq.norm ℝ (hne q hq)).inv (norm_ne_zero_iff.mpr (hne q hq))
  have hd : DifferentiableAt ℝ (fun p => -inner ℝ (F p) a * (‖F p‖⁻¹) ^ 3) q :=
    ((hFq.inner ℝ (differentiableAt_const a)).neg).mul (hi.pow 3)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hΩ.mem_nhds hq] with p hp
  rw [inv_norm_directional_eq ((hF p hp).differentiableAt (hΩ.mem_nhds hp))
    (hne p hp), ha p hp]

/-- The inverse-distance mixed Hessian bound follows from the explicit physical
inner-product derivative, when the first directional map is locally constant. -/
theorem inv_norm_second_directional_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : G → Position} {q : G} {Ω : Set G} (hΩ : IsOpen Ω) (hq : q ∈ Ω)
    (hF : DifferentiableOn ℝ F Ω) (hne : ∀ p ∈ Ω, F p ≠ 0)
    (v w : G) (a : Position)
    (ha : ∀ p ∈ Ω, fderiv ℝ F p v = a) (han : ‖a‖ ≤ 1)
    (hwn : ‖fderiv ℝ F q w‖ ≤ 1) :
    |fderiv ℝ (fun p => fderiv ℝ (fun z => ‖F z‖⁻¹) p v) q w| ≤
      4 * (‖F q‖⁻¹) ^ 3 := by
  have hFq := (hF q hq).differentiableAt (hΩ.mem_nhds hq)
  have heq : (fun p => fderiv ℝ (fun z => ‖F z‖⁻¹) p v) =ᶠ[nhds q]
      (fun p => -inner ℝ (F p) a * (‖F p‖⁻¹) ^ 3) := by
    filter_upwards [hΩ.mem_nhds hq] with p hp
    rw [inv_norm_directional_eq ((hF p hp).differentiableAt (hΩ.mem_nhds hp))
      (hne p hp), ha p hp]
  rw [heq.fderiv_eq, inv_norm_gradient_directional_eq hFq (hne q hq)]
  have hn : 0 < ‖F q‖ := norm_pos_iff.mpr (hne q hq)
  have hi1 : |inner ℝ (fderiv ℝ F q w) a| ≤ 1 :=
    (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul hwn han (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have hi2 : |inner ℝ (F q) a| ≤ ‖F q‖ :=
    (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left han (norm_nonneg _)).trans_eq (mul_one _))
  have hi3 : |inner ℝ (F q) (fderiv ℝ F q w)| ≤ ‖F q‖ :=
    (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left hwn (norm_nonneg _)).trans_eq (mul_one _))
  calc
    _ ≤ |-inner ℝ (fderiv ℝ F q w) a * (‖F q‖⁻¹) ^ 3| +
        |3 * inner ℝ (F q) a * inner ℝ (F q) (fderiv ℝ F q w) * (‖F q‖⁻¹) ^ 5| :=
      abs_add_le _ _
    _ = |inner ℝ (fderiv ℝ F q w) a| * (‖F q‖⁻¹) ^ 3 +
        3 * |inner ℝ (F q) a| * |inner ℝ (F q) (fderiv ℝ F q w)| * (‖F q‖⁻¹) ^ 5 := by
      simp only [abs_mul, abs_neg, abs_pow, abs_inv, abs_norm, show |(3 : ℝ)| = 3 by norm_num]
    _ ≤ 1 * (‖F q‖⁻¹) ^ 3 + 3 * ‖F q‖ * ‖F q‖ * (‖F q‖⁻¹) ^ 5 := by
      gcongr
    _ = 4 * (‖F q‖⁻¹) ^ 3 := by
      field_simp
      ring

/-- Actual mixed second spectator derivatives on the unit nuclear chart. -/
theorem nuclearKSPotential_second_spectator_abs_le_of_mem_nuclearChartOpen
    (Z E : ℝ) (t0 : Position) (ht0 : ‖t0‖ = 1)
    {q : NuclearKSSpace (0 : Fin 2)} (hq : q ∈ nuclearChartOpen t0)
    (j k : SpectatorCoordinate (0 : Fin 2)) :
    |fderiv ℝ (fun p => fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E) p (tDir j))
      q (tDir k)| ≤ (128 / 27 : ℝ) * |Z| + 8192 / 1331 := by
  let Ω := nuclearChartOpen t0
  let T : NuclearKSSpace (0 : Fin 2) → Position := fun p => spectatorPositionCLM p.2
  let P : NuclearKSSpace (0 : Fin 2) → Position := fun p => ksMap p.1 - T p
  let R : NuclearKSSpace (0 : Fin 2) → ℝ := fun p => ‖p.1‖ ^ 2
  let IT := fun p => ‖T p‖⁻¹
  let IP := fun p => ‖P p‖⁻¹
  let V := fun p => -Z * IT p + IP p - E
  have hΩ : IsOpen Ω := nuclearChartOpen_isOpen t0
  have hTeq : ∀ p : NuclearKSSpace (0 : Fin 2),
      position (nuclearKSLift (0 : Fin 2) p) (1 : Fin 2) = T p :=
    nuclearKSLift_other_position
  have hPeq : ∀ p : NuclearKSSpace (0 : Fin 2),
      position (nuclearKSLift (0 : Fin 2) p) (0 : Fin 2) -
        position (nuclearKSLift (0 : Fin 2) p) (1 : Fin 2) = P p := by
    intro p
    rw [nuclearKSLift_selected_position, hTeq]
  have hdist : ∀ p ∈ Ω, (3 / 4 : ℝ) ≤ ‖T p‖ ∧ (11 / 16 : ℝ) ≤ ‖P p‖ := by
    intro p hp
    obtain ⟨ht, _, _, hpair⟩ := nuclearChart_closed_geometry t0 ht0 hp.1.le hp.2.le
    rw [hTeq] at ht
    rw [hPeq] at hpair
    exact ⟨ht, hpair⟩
  have hTne : ∀ p ∈ Ω, T p ≠ 0 := by
    intro p hp
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) (hdist p hp).1)
  have hPne : ∀ p ∈ Ω, P p ≠ 0 := by
    intro p hp
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 11 / 16) (hdist p hp).2)
  have hTd : ∀ p, HasFDerivAt T
      (spectatorPositionCLM.comp (ContinuousLinearMap.snd ℝ KSSpace (SpectatorConfiguration (0 : Fin 2)))) p := by
    intro p
    exact spectatorPositionCLM.hasFDerivAt.comp p hasFDerivAt_snd
  have hX : Differentiable ℝ (fun p : NuclearKSSpace (0 : Fin 2) => ksMap p.1) := by
    intro p
    exact (ksMap_contDiff.differentiable (by norm_num)).differentiableAt.comp p
      hasFDerivAt_fst.differentiableAt
  have hX0 : ∀ p (l : SpectatorCoordinate (0 : Fin 2)),
      fderiv ℝ (fun z : NuclearKSSpace (0 : Fin 2) => ksMap z.1) p (tDir l) = 0 := by
    intro p l
    change fderiv ℝ (ksMap ∘ Prod.fst) p (tDir l) = 0
    rw [fderiv_comp p (ksMap_contDiff.differentiable (by norm_num)).differentiableAt
      hasFDerivAt_fst.differentiableAt, ContinuousLinearMap.comp_apply, fderiv_fst]
    change (fderiv ℝ _ _) 0 = 0
    exact map_zero _
  have hTder : ∀ p (l : SpectatorCoordinate (0 : Fin 2)),
      fderiv ℝ T p (tDir l) = spectatorPositionCLM (oscillatorBasis l) := by
    intro p l
    rw [(hTd p).fderiv]
    rfl
  have hPd : Differentiable ℝ P := fun p => (hX p).sub (hTd p).differentiableAt
  have hPder : ∀ p (l : SpectatorCoordinate (0 : Fin 2)),
      fderiv ℝ P p (tDir l) = -spectatorPositionCLM (oscillatorBasis l) := by
    intro p l
    change fderiv ℝ ((fun z : NuclearKSSpace (0 : Fin 2) => ksMap z.1) - T) p (tDir l) = _
    rw [fderiv_sub (hX p) (hTd p).differentiableAt, sub_apply, hX0, zero_sub, hTder]
  have hR : Differentiable ℝ R := by
    intro p
    exact (hasFDerivAt_fst (𝕜 := ℝ) (E := KSSpace)
      (F := SpectatorConfiguration (0 : Fin 2)) (p := p)).norm_sq.differentiableAt
  have hRzero : ∀ p (l : SpectatorCoordinate (0 : Fin 2)), fderiv ℝ R p (tDir l) = 0 := by
    intro p l
    change fderiv ℝ ((fun y : KSSpace => ‖y‖ ^ 2) ∘ Prod.fst) p (tDir l) = 0
    rw [fderiv_comp p (hasStrictFDerivAt_norm_sq p.1).differentiableAt
      hasFDerivAt_fst.differentiableAt, ContinuousLinearMap.comp_apply, fderiv_fst]
    change (fderiv ℝ _ _) 0 = 0
    exact map_zero _
  have hTi : ∀ p ∈ Ω, DifferentiableAt ℝ IT p := by
    intro p hp
    exact ((hTd p).differentiableAt.norm ℝ (hTne p hp)).inv (norm_ne_zero_iff.mpr (hTne p hp))
  have hPi : ∀ p ∈ Ω, DifferentiableAt ℝ IP p := by
    intro p hp
    exact ((hPd p).norm ℝ (hPne p hp)).inv (norm_ne_zero_iff.mpr (hPne p hp))
  have hV : ∀ p ∈ Ω, DifferentiableAt ℝ V p := by
    intro p hp
    exact (((hTi p hp).const_mul (-Z)).add (hPi p hp)).sub_const E
  have hBfun : nuclearKSPotential (0 : Fin 2) Z E =
      fun p => -8 * Z + (8 * R p) * V p := by
    funext p
    dsimp only [nuclearKSPotential, R, V, IT, IP]
    rw [coulombWithoutSelectedNucleus_two_electrons, hPeq, hTeq]
  have hBder : ∀ p ∈ Ω,
      fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E) p (tDir j) =
        8 * R p * (-Z * fderiv ℝ IT p (tDir j) + fderiv ℝ IP p (tDir j)) := by
    intro p hp
    rw [hBfun, fderiv_const_add, fderiv_fun_mul ((hR p).const_mul 8) (hV p hp),
      fderiv_const_mul (hR p) 8]
    simp only [add_apply, smul_apply, smul_eq_mul, hRzero, mul_zero, add_zero]
    change 8 * R p * fderiv ℝ (fun z => -Z * IT z + IP z - E) p (tDir j) = _
    rw [fderiv_sub_const E, fderiv_fun_add ((hTi p hp).const_mul (-Z)) (hPi p hp),
      fderiv_const_mul (hTi p hp) (-Z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hITj : DifferentiableAt ℝ (fun p => fderiv ℝ IT p (tDir j)) q :=
    inv_norm_directional_differentiableAt hΩ hq
      (fun p _ => (hTd p).differentiableAt.differentiableWithinAt) hTne
      (tDir j) (spectatorPositionCLM (oscillatorBasis j)) (fun p _ => hTder p j)
  have hIPj : DifferentiableAt ℝ (fun p => fderiv ℝ IP p (tDir j)) q :=
    inv_norm_directional_differentiableAt hΩ hq hPd.differentiableOn hPne
      (tDir j) (-spectatorPositionCLM (oscillatorBasis j)) (fun p _ => hPder p j)
  have hT2 := inv_norm_second_directional_le hΩ hq
    (fun p _ => (hTd p).differentiableAt.differentiableWithinAt) hTne
    (tDir j) (tDir k) (spectatorPositionCLM (oscillatorBasis j))
    (fun p _ => hTder p j) (spectatorPositionCLM_basis_norm j).le
    (by rw [hTder, spectatorPositionCLM_basis_norm])
  have hP2 := inv_norm_second_directional_le hΩ hq hPd.differentiableOn hPne
    (tDir j) (tDir k) (-spectatorPositionCLM (oscillatorBasis j))
    (fun p _ => hPder p j) (by rw [norm_neg, spectatorPositionCLM_basis_norm])
    (by rw [hPder, norm_neg, spectatorPositionCLM_basis_norm])
  have heq : (fun p => fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E) p (tDir j)) =ᶠ[nhds q]
      (fun p => 8 * R p * (-Z * fderiv ℝ IT p (tDir j) + fderiv ℝ IP p (tDir j))) := by
    filter_upwards [hΩ.mem_nhds hq] with p hp
    exact hBder p hp
  have hB2 : fderiv ℝ (fun p => fderiv ℝ (nuclearKSPotential (0 : Fin 2) Z E) p (tDir j)) q (tDir k) =
      8 * R q * (-Z * fderiv ℝ (fun p => fderiv ℝ IT p (tDir j)) q (tDir k) +
        fderiv ℝ (fun p => fderiv ℝ IP p (tDir j)) q (tDir k)) := by
    have hsum : DifferentiableAt ℝ
        (fun p => -Z * fderiv ℝ IT p (tDir j) + fderiv ℝ IP p (tDir j)) q :=
      (hITj.const_mul (-Z)).add hIPj
    rw [heq.fderiv_eq, fderiv_fun_mul ((hR q).const_mul 8) hsum,
      fderiv_const_mul (hR q) 8]
    simp only [add_apply, smul_apply, smul_eq_mul, hRzero, mul_zero, add_zero]
    rw [fderiv_fun_add (hITj.const_mul (-Z)) hIPj, fderiv_const_mul hITj (-Z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hTinv : ‖T q‖⁻¹ ≤ (4 / 3 : ℝ) := by
    have hh := (inv_le_inv₀ (norm_pos_iff.mpr (hTne q hq)) (by norm_num : (0 : ℝ) < 3 / 4)).mpr (hdist q hq).1
    norm_num at hh
    exact hh
  have hPinv : ‖P q‖⁻¹ ≤ (16 / 11 : ℝ) := by
    have hh := (inv_le_inv₀ (norm_pos_iff.mpr (hPne q hq)) (by norm_num : (0 : ℝ) < 11 / 16)).mpr (hdist q hq).2
    norm_num at hh
    exact hh
  have hTcube : (‖T q‖⁻¹) ^ 3 ≤ (64 / 27 : ℝ) := by
    calc
      _ ≤ (4 / 3 : ℝ) ^ 3 := by gcongr
      _ = _ := by norm_num
  have hPcube : (‖P q‖⁻¹) ^ 3 ≤ (4096 / 1331 : ℝ) := by
    calc
      _ ≤ (16 / 11 : ℝ) ^ 3 := by gcongr
      _ = _ := by norm_num
  have hRbound : 8 * R q ≤ (1 / 2 : ℝ) := by
    have hsq := (sq_le_sq₀ (norm_nonneg q.1) (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hq.1.le
    dsimp only [R]
    nlinarith
  have hRnonneg : 0 ≤ 8 * R q := by dsimp only [R]; positivity
  rw [hB2, abs_mul, abs_of_nonneg hRnonneg]
  calc
    _ ≤ 8 * R q * (|Z| * |fderiv ℝ (fun p => fderiv ℝ IT p (tDir j)) q (tDir k)| +
        |fderiv ℝ (fun p => fderiv ℝ IP p (tDir j)) q (tDir k)|) := by
      apply mul_le_mul_of_nonneg_left _ hRnonneg
      simpa only [abs_mul, abs_neg] using abs_add_le
        (-Z * fderiv ℝ (fun p => fderiv ℝ IT p (tDir j)) q (tDir k))
        (fderiv ℝ (fun p => fderiv ℝ IP p (tDir j)) q (tDir k))
    _ ≤ 8 * R q * (|Z| * (4 * (‖T q‖⁻¹) ^ 3) + 4 * (‖P q‖⁻¹) ^ 3) := by
      gcongr
    _ ≤ (1 / 2 : ℝ) * (|Z| * (4 * (64 / 27 : ℝ)) + 4 * (4096 / 1331 : ℝ)) := by
      gcongr
    _ = _ := by ring

#print axioms inv_norm_second_directional_le
#print axioms nuclearKSPotential_second_spectator_abs_le_of_mem_nuclearChartOpen

end ManyBody.S8
