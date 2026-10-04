import ManyBody.S8.Internal.HigherSpectatorRegularity
import WeakProductSecondTest_v1
import WeakGrushinSpectatorSmoothCommute_v1

/-!
# Actual Y commutation for the weak Grushin equation

The variable principal coefficient contributes the positive commutator source
(2c\langle Y,w\rangle\Delta_T U).  This source is constructed from genuine
TT diagonal weak derivatives, with all local integrability proved.  Applying the
published one-step gain gives new pure Y third derivatives, without input third
derivatives or an assumed differentiated equation.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8
variable {κ : Type} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem grushin_weight_y_directional (c : ℝ) (w : KSSpace) (p : Space κ) :
    fderiv ℝ (fun q : Space κ => c * ‖q.1‖ ^ 2) p (w, 0) =
      2 * c * inner ℝ p.1 w := by
  have hh : ContDiff ℝ ∞ (fun y : KSSpace => c * ‖y‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  rw [first_directional_fst (hh.differentiable (by simp))]
  have hn : ContDiff ℝ ∞ (fun y : KSSpace => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  rw [fderiv_const_mul (hn.differentiable (by simp) p.1) c]
  simp only [smul_apply, smul_eq_mul, fderiv_norm_sq_apply,
    innerSL_apply_apply]
  ring

theorem splitGrushin_y_directional_commute (c : ℝ) (w : KSSpace)
    {φ : Space κ → ℝ} (hφ : ContDiff ℝ ∞ φ) (p : Space κ) :
    splitGrushin c oscillatorBasis (fun _ => 0) (fun q => fderiv ℝ φ q (w, 0)) p =
      fderiv ℝ (splitGrushin c oscillatorBasis (fun _ => 0) φ) p (w, 0) +
      (2 * c * inner ℝ p.1 w) *
        ∑ j : κ, fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j) := by
  let Ly := fun q : Space κ => ∑ i : Fin 4,
    fderiv ℝ (fun z => fderiv ℝ φ z (ksBasis i, 0)) q (ksBasis i, 0)
  let Lt := fun q : Space κ => ∑ j : κ,
    fderiv ℝ (fun z => fderiv ℝ φ z (tDir j)) q (tDir j)
  let a := fun q : Space κ => c * ‖q.1‖ ^ 2
  have h2 (u : Space κ) : ContDiff ℝ ∞
      (fun q => fderiv ℝ (fun z => fderiv ℝ φ z u) q u) :=
    ((((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const).fderiv_right
      (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const)
  have hy : ContDiff ℝ ∞ Ly := ContDiff.sum (fun i _ => h2 (ksBasis i, 0))
  have ht : ContDiff ℝ ∞ Lt := ContDiff.sum (fun j _ => h2 (tDir j))
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_fst)
  have heq : splitGrushin c oscillatorBasis (fun _ => 0) φ =
      (fun q => -Ly q - a q * Lt q) := by
    funext q
    simp only [splitGrushin, Ly, Lt, a, tDir, zero_mul, add_zero]
  have hD := ((hy.differentiable (by simp) p).hasFDerivAt.neg).sub
    ((ha.differentiable (by simp) p).hasFDerivAt.mul (ht.differentiable (by simp) p).hasFDerivAt)
  change HasFDerivAt (𝕜 := ℝ) (fun q => -Ly q - a q * Lt q) _ p at hD
  rw [heq, hD.fderiv]
  simp only [sub_apply, neg_apply,
    add_apply, smul_apply, smul_eq_mul]
  have hz : fderiv ℝ a p (w, 0) = 2 * c * inner ℝ p.1 w :=
    grushin_weight_y_directional c w p
  rw [hz]
  have hyD := finite_second_sum_directional_commute
    (fun i : Fin 4 => (ksBasis i, (0 : EuclideanSpace ℝ κ))) hφ p (w, 0)
  have htD := finite_second_sum_directional_commute (tDir : κ → Space κ) hφ p (w, 0)
  change fderiv ℝ Ly p (w, 0) = _ at hyD
  change fderiv ℝ Lt p (w, 0) = _ at htD
  rw [hyD, htD]
  simp only [splitGrushin, a, Lt, tDir, zero_mul, add_zero]
  ring

#print axioms grushin_weight_y_directional
#print axioms splitGrushin_y_directional_commute

theorem weak_grushin_homogeneous_y_equation
    (c : ℝ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {U d : Lp ℂ 2 (volume : Measure (Space κ))} (w : KSSpace)
    (hD : WeakProductL2Directional U d (w, 0))
    {dt et : κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hdt : ∀ j, WeakProductL2Directional U (dt j) (tDir j))
    (het : ∀ j, WeakProductL2Directional (dt j) (et j) (tDir j))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0) :
    ProductLocallyL2On
      (fun p => (2 * c * inner ℝ p.1 w) • (∑ j, et j p) -
        fderiv ℝ B p (w, 0) • U p) Ω ∧
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • d p) =
        ∫ p, φ p • ((2 * c * inner ℝ p.1 w) • (∑ j, et j p) -
          fderiv ℝ B p (w, 0) • U p) := by
  let a : KSSpace → ℝ := fun y => 2 * c * inner ℝ y w
  let E : Space κ → ℂ := fun p => ∑ j, et j p
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul (contDiff_id.inner (𝕜 := ℝ) contDiff_const)
  have hUl : ProductLocallyL2On (U : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp U).mono_measure Measure.restrict_le_self
  have hdl : ProductLocallyL2On (d : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp d).mono_measure Measure.restrict_le_self
  have hEl : ProductLocallyL2On E Ω := by
    intro K hK hKΩ
    simpa only [E] using memLp_finsetSum Finset.univ
      (fun j _ => (Lp.memLp (et j)).mono_measure (Measure.restrict_le_self : volume.restrict K ≤ volume))
  have haE : ProductLocallyL2On (fun p => a p.1 • E p) Ω :=
    product_locallyL2On_smul_of_continuousOn (ha.comp contDiff_fst).continuous.continuousOn hEl
  have hDB : ContDiffOn ℝ ∞ (fun p => fderiv ℝ B p (w, 0)) Ω := by
    intro p hp
    exact (local_contDiffAt_directional_derivative (hB.contDiffAt (hΩ.mem_nhds hp))
      (w, 0)).contDiffWithinAt
  have hDBU := product_locallyL2On_smul_of_continuousOn hDB.continuousOn hUl
  have hsource := product_locallyL2On_sub haE hDBU
  have hBU := product_locallyL2On_smul_of_continuousOn hB.continuousOn hUl
  have hBd := product_locallyL2On_smul_of_continuousOn hB.continuousOn hdl
  have hleib : ProductLocallyL2On
      (fun p => B p • d p + fderiv ℝ B p (w, 0) • U p) Ω := by
    intro K hK hKΩ
    exact (hBd K hK hKΩ).add (hDBU K hK hKΩ)
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) =
      oscillatorBasis := funext (EuclideanSpace.basisFun_apply κ ℝ)
  have hP0 : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) =
        ∫ p, φ p • (-(B p • U p)) := by
    intro φ hφ hcφ hsφ
    have hiff := grushin_local_potential_test_iff c (EuclideanSpace.basisFun κ ℝ)
      hB.continuousOn U (fun _ => 0) hUl
      (fun K hK hKΩ => MemLp.zero) hφ hcφ hsφ
    rw [hBasis] at hiff
    simpa only [zero_sub, smul_zero, integral_zero] using hiff.mp (by simpa only [smul_zero, integral_zero] using hP φ hφ hcφ hsφ)
  refine ⟨hsource, ?_⟩
  intro φ hφ hcφ hsφ
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p (w, 0)) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  have hcDφ := hcφ.fderiv_apply ℝ (w, 0)
  have hsDφ := (tsupport_fderiv_apply_subset ℝ (w, 0)).trans hsφ
  have hφP := splitGrushin_zero_contDiff c oscillatorBasis hφ
  have hcφP := splitGrushin_compact c oscillatorBasis (fun _ => 0) hcφ
  have hDP := hD _ hφP hcφP
  have hcomm (p : Space κ) :
      fderiv ℝ (splitGrushin c oscillatorBasis (fun _ => 0) φ) p (w, 0) =
        splitGrushin c oscillatorBasis (fun _ => 0) (fun q => fderiv ℝ φ q (w, 0)) p -
          a p.1 * ∑ j : κ, fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j) := by
    have hh := splitGrushin_y_directional_commute c w hφ p
    change _ = _ + a p.1 * _ at hh
    linarith
  have hiP := product_locallyL2_compact_smul_integrable U hUl
    (splitGrushin_zero_contDiff c oscillatorBasis hDφ).continuous
    (splitGrushin_compact c oscillatorBasis (fun _ => 0) hcDφ)
    ((splitGrushin_test_tsupport_subset c _).trans hsDφ)
  have h2φ (v : Space κ) : ContDiff ℝ ∞
      (fun p => fderiv ℝ (fun q => fderiv ℝ φ q v) p v) :=
    ((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
      |>.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  have hiT (j : κ) : Integrable
      (fun p => (a p.1 * fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j)) • U p) :=
    ((Lp.memLp U).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((ha.comp contDiff_fst).mul (h2φ (tDir j))).continuous
      (((hcφ.fderiv_apply ℝ (tDir j)).fderiv_apply ℝ (tDir j)).mul_left)
  have hiE (j : κ) : Integrable (fun p => (a p.1 * φ p) • et j p) :=
    ((Lp.memLp (et j)).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((ha.comp contDiff_fst).mul hφ).continuous hcφ.mul_left
  have hweight :
      (∫ p, (a p.1 * ∑ j : κ, fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j)) • U p) =
        ∫ p, φ p • (a p.1 • E p) := by
    simp_rw [Finset.mul_sum, Finset.sum_smul, E, Finset.smul_sum, ← mul_smul]
    rw [integral_finsetSum _ (fun j _ => hiT j),
      integral_finsetSum _ (fun j _ => by simpa only [mul_comm (φ _) (a _)] using hiE j)]
    apply Finset.sum_congr rfl
    intro j hj
    have he := spectator_invariant_weight_second_test (hdt j) (het j) ha hφ hcφ
    simpa only [tDir, mul_comm (φ _) (a _)] using he.symm
  have hiTrace : Integrable
      (fun p => (a p.1 * ∑ j : κ, fderiv ℝ (fun q => fderiv ℝ φ q (tDir j)) p (tDir j)) • U p) := by
    simp_rw [Finset.mul_sum, Finset.sum_smul]
    exact integrable_finsetSum _ (fun j _ => hiT j)
  have he0 :
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • d p) =
        -(∫ p, φ p • (B p • d p + fderiv ℝ B p (w, 0) • U p)) +
          ∫ p, φ p • (a p.1 • E p) := by
    rw [hDP]
    simp_rw [hcomm, sub_smul]
    rw [integral_sub hiP hiTrace, neg_sub, hP0 _ hDφ hcDφ hsDφ, hweight]
    have hLeib := (weakProduct_directional_local_potential_test hD hΩ hB hφ hcφ hsφ).2.2
    simp_rw [smul_neg, integral_neg]
    rw [← hLeib]
    abel
  have hiff := grushin_local_potential_test_iff c (EuclideanSpace.basisFun κ ℝ)
    hB.continuousOn d (fun p => a p.1 • E p - fderiv ℝ B p (w, 0) • U p)
    hdl hsource hφ hcφ hsφ
  rw [hBasis] at hiff
  apply hiff.mpr
  have hiLeib := product_locallyL2_compact_smul_integrable _ hleib hφ.continuous hcφ hsφ
  have hiBd := product_locallyL2_compact_smul_integrable _ hBd hφ.continuous hcφ hsφ
  have hiDB := product_locallyL2_compact_smul_integrable _ hDBU hφ.continuous hcφ hsφ
  have hiaE := product_locallyL2_compact_smul_integrable _ haE hφ.continuous hcφ hsφ
  rw [he0]
  simp_rw [smul_sub, smul_add]
  rw [integral_add hiBd hiDB]
  change _ = ∫ p, (((fun q => φ q • (a q.1 • E q)) -
    (fun q => φ q • (fderiv ℝ B q (w, 0) • U q))) -
    (fun q => φ q • (B q • d q))) p
  rw [integral_sub' (hiaE.sub hiDB) hiBd, integral_sub' hiaE hiDB]
  abel

#print axioms weak_grushin_homogeneous_y_equation

/-- A genuine first Y derivative gains first Y/T and second YY derivatives
from the actual differentiated equation.  Only genuine TT diagonal derivatives
of the original solution are required; no third derivatives are assumed. -/
theorem local_homogeneous_grushin_y_cutoff_gain
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {U d : Lp ℂ 2 (volume : Measure (Space κ))} (w : KSSpace)
    (hD : WeakProductL2Directional U d (w, 0))
    {dt et : κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hdt : ∀ j, WeakProductL2Directional U (dt j) (tDir j))
    (het : ∀ j, WeakProductL2Directional (dt j) (et j) (tDir j))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    ∃ W : Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
      W =ᵐ[volume] (fun p => χ p • d p) ∧
      (∀ i, WeakProductL2Directional W (gy i) (yDir i)) ∧
      (∀ j, WeakProductL2Directional W (gt j) (tDir j)) ∧
      ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  obtain ⟨hsource, hdiff⟩ := weak_grushin_homogeneous_y_equation c hΩ hB w hD hdt het hP
  obtain ⟨K, C, hK, hχK, hKΩ, hC, hgain⟩ :=
    local_weak_grushin_potential_cutoff_gain hc hΩ hχ hcχ hχΩ
  have hdl : ProductLocallyL2On (d : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp d).mono_measure Measure.restrict_le_self
  obtain ⟨W, gy, gt, hyy, hW, _, _, _, hgy, hgt, hhyy⟩ :=
    hgain B d
      (fun p => (2 * c * inner ℝ p.1 w) • (∑ j, et j p) -
        fderiv ℝ B p (w, 0) • U p)
      hB.continuousOn hdl hsource hdiff
  exact ⟨W, gy, gt, hyy, hW, hgy, hgt, hhyy⟩

#print axioms local_homogeneous_grushin_y_cutoff_gain

end ManyBody.S8

