import ManyBody.S8.Internal.JointWeakH2Initialization
import SmoothLocalTestProduct_v1

/-!
# Actual first-spectator higher regularity for smooth Grushin potentials

The differentiated equation is proved from the weak equation and the genuine weak
first derivative.  No differentiated PDE or second derivatives are assumed.  The
last theorem gives local joint H² of every first spectator derivative, hence third
weak derivatives containing a spectator direction.  It does not assert full H³,
uniform quantitative estimates, or arbitrary-order regularity.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8
variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Differentiate the actual inhomogeneous weak equation in a spectator direction,
using a genuine local weak derivative of its source. -/
theorem weak_grushin_inhomogeneous_spectator_equation
    (c : ℝ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {U d : Lp ℂ 2 (volume : Measure (Space κ))} (j : κ)
    (hD : WeakProductL2Directional U d (tDir j))
    (g k : Space κ → ℂ) (hg : ProductLocallyL2On g Ω) (hk : ProductLocallyL2On k Ω)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = ∫ p, φ p • g p)
    (hgD : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • k p) = -(∫ p, fderiv ℝ φ p (tDir j) • g p)) :
    ProductLocallyL2On (fun p => k p - fderiv ℝ B p (tDir j) • U p) Ω ∧
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • d p) =
        ∫ p, φ p • (k p - fderiv ℝ B p (tDir j) • U p) := by
  have hUl : ProductLocallyL2On (U : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp U).mono_measure Measure.restrict_le_self
  have hdl : ProductLocallyL2On (d : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp d).mono_measure Measure.restrict_le_self
  have hDBU : ProductLocallyL2On (fun p => fderiv ℝ B p (tDir j) • U p) Ω := by
    intro K hK hKΩ
    have hmD := (smooth_coefficient_and_directional_memLp_top_restrict_compact
      (μ := volume) hΩ hK hKΩ hB (tDir j)).2
    exact ((Lp.memLp U).mono_measure Measure.restrict_le_self).smul hmD
  have hsource := product_locallyL2On_sub hk hDBU
  obtain ⟨hBU, hleibL2, hleib⟩ := weakProduct_spectator_local_potential_leibniz hD hΩ hB
  have hh := product_locallyL2On_sub hg hBU
  have hkl : ProductLocallyL2On
      (fun p => k p - (B p • d p + fderiv ℝ B p (tDir j) • U p)) Ω :=
    product_locallyL2On_sub hk hleibL2
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) =
      oscillatorBasis := funext (EuclideanSpace.basisFun_apply κ ℝ)
  have hP0 : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • U p) =
        ∫ p, φ p • (g p - B p • U p) := by
    have hh := (grushin_local_potential_reduction_iff c (EuclideanSpace.basisFun κ ℝ)
      hB.continuousOn U g hUl hg)
    rw [hBasis] at hh
    exact hh.mp hP
  have hhD : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • (k p - (B p • d p + fderiv ℝ B p (tDir j) • U p))) =
        -(∫ p, fderiv ℝ φ p (tDir j) • (g p - B p • U p)) := by
    intro φ hφ hcφ hsφ
    have hik := product_locallyL2_compact_smul_integrable k hk hφ.continuous hcφ hsφ
    have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p (tDir j)) :=
      (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
    have hig := product_locallyL2_compact_smul_integrable g hg hDφ.continuous
      (hcφ.fderiv_apply ℝ (tDir j)) ((tsupport_fderiv_apply_subset ℝ (tDir j)).trans hsφ)
    obtain ⟨hileib, hiBU, hleibEq⟩ := hleib φ hφ hcφ hsφ
    have hiL : Integrable (fun p => φ p • (B p • d p + fderiv ℝ B p (tDir j) • U p)) := by
      simpa only [tDir] using hileib
    have hiB : Integrable (fun p => fderiv ℝ φ p (tDir j) • (B p • U p)) := by
      simpa only [tDir] using hiBU
    have heL : (∫ p, φ p • (B p • d p + fderiv ℝ B p (tDir j) • U p)) =
        -(∫ p, fderiv ℝ φ p (tDir j) • (B p • U p)) := by
      simpa only [tDir] using hleibEq
    simp_rw [smul_sub]
    rw [integral_sub hik hiL, integral_sub hig hiB, hgD φ hφ hcφ hsφ, heL]
    abel
  have hdiff := weak_grushin_spectator_differentiate c
    (fun p => g p - B p • U p)
    (fun p => k p - (B p • d p + fderiv ℝ B p (tDir j) • U p))
    hh hkl (oscillatorBasis j) hD hP0 hhD
  refine ⟨hsource, ?_⟩
  intro φ hφ hcφ hsφ
  have hiff := grushin_local_potential_test_iff c (EuclideanSpace.basisFun κ ℝ)
    hB.continuousOn d (fun p => k p - fderiv ℝ B p (tDir j) • U p)
    hdl hsource hφ hcφ hsφ
  rw [hBasis] at hiff
  apply hiff.mpr
  convert hdiff φ hφ hcφ hsφ using 1
  congr 1
  funext p
  abel_nf

#print axioms weak_grushin_inhomogeneous_spectator_equation

/-- The actual inhomogeneous equation supplies the missing spectator diagonal
second derivatives; the frozen factor-diagonal theorem then constructs all ordered
arbitrary-direction second weak derivatives of the same cutoff function. -/
theorem local_inhomogeneous_grushin_joint_cutoff_h2
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω)
    {U : Lp ℂ 2 (volume : Measure (Space κ))}
    {gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ))}
    {gt : κ → Lp ℂ 2 (volume : Measure (Space κ))}
    {hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ))}
    (hgy : ∀ i, WeakProductL2Directional U (gy i) (yDir i))
    (hgt : ∀ j, WeakProductL2Directional U (gt j) (tDir j))
    (hhyy : ∀ i k, WeakProductL2Directional (gy i) (hyy i k) (yDir k))
    (g : Space κ → ℂ) (k : κ → Space κ → ℂ)
    (hg : ProductLocallyL2On g Ω) (hk : ∀ j, ProductLocallyL2On (k j) Ω)
    (hgD : ∀ j, ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • k j p) = -(∫ p, fderiv ℝ φ p (tDir j) • g p))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = ∫ p, φ p • g p) :
    ∃ W : Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ a : Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ b : Space κ → Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
      W =ᵐ[volume] (fun p => χ p • U p) ∧
      (∀ v, WeakProductL2Directional W (a v) v) ∧
      ∀ v w, WeakProductL2Directional (a v) (b v w) w := by
  have hm : MemLp χ ⊤ volume := hχ.continuous.memLp_top_of_hasCompactSupport hcχ volume
  have hDχ (v : Space κ) : ContDiff ℝ ∞ (fun p => fderiv ℝ χ p v) :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDm (v : Space κ) : MemLp (fun p => fderiv ℝ χ p v) ⊤ volume :=
    (hDχ v).continuous.memLp_top_of_hasCompactSupport (hcχ.fderiv_apply ℝ v) volume
  have hDDm (v : Space κ) : MemLp (fun p => fderiv ℝ (fun q => fderiv ℝ χ q v) p v) ⊤ volume :=
    (((hDχ v).fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const).continuous.memLp_top_of_hasCompactSupport
      ((hcχ.fderiv_apply ℝ v).fderiv_apply ℝ v) volume
  let M := productBoundedRealMul χ hm
  let D (v : Space κ) := productBoundedRealMul (fun p => fderiv ℝ χ p v) (hDm v)
  let DD (v : Space κ) := productBoundedRealMul
    (fun p => fderiv ℝ (fun q => fderiv ℝ χ q v) p v) (hDDm v)
  obtain ⟨K, C, hK, hχK, hKΩ, hC, hgain⟩ :=
    local_weak_grushin_potential_cutoff_gain hc hΩ hχ hcχ hχΩ
  have hs : ∀ j : κ,
      ∃ Wj : Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ ty : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ tt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ tyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
        Wj =ᵐ[volume] (fun p => χ p • gt j p) ∧
        (∀ i, WeakProductL2Directional Wj (ty i) (yDir i)) ∧
        (∀ k, WeakProductL2Directional Wj (tt k) (tDir k)) ∧
        ∀ i k, WeakProductL2Directional (ty i) (tyy i k) (yDir k) := by
    intro j
    obtain ⟨hsource, hdiff⟩ := weak_grushin_inhomogeneous_spectator_equation c hΩ hB
      j (hgt j) g (k j) hg (hk j) hP (hgD j)
    have hgtloc : ProductLocallyL2On (gt j : Space κ → ℂ) Ω :=
      fun _ _ _ => (Lp.memLp (gt j)).mono_measure Measure.restrict_le_self
    obtain ⟨Wj, ty, tt, tyy, hWj, _, _, _, hty, htt, htyy⟩ :=
      hgain B (gt j) (fun p => k j p - fderiv ℝ B p (tDir j) • U p)
        hB.continuousOn hgtloc hsource hdiff
    exact ⟨Wj, ty, tt, tyy, hWj, hty, htt, htyy⟩
  choose Wj ty tt tyy hWj hty htt htyy using hs
  let dY (i : Fin 4) := M (gy i) + D (yDir i) U
  let eY (i : Fin 4) := (M (hyy i i) + D (yDir i) (gy i)) +
    (D (yDir i) (gy i) + DD (yDir i) U)
  let dT (j : κ) := M (gt j) + D (tDir j) U
  let eT (j : κ) := tt j j + (D (tDir j) (gt j) + DD (tDir j) U)
  have hdY : ∀ i, WeakProductL2Directional (M U) (dY i) (yDir i) :=
    fun i => weak_product_bounded_real_mul (hgy i) χ hχ hm (hDm (yDir i))
  have heY : ∀ i, WeakProductL2Directional (dY i) (eY i) (yDir i) := by
    intro i
    exact weak_product_directional_add
      (weak_product_bounded_real_mul (hhyy i i) χ hχ hm (hDm (yDir i)))
      (weak_product_bounded_real_mul (hgy i) _ (hDχ (yDir i)) (hDm (yDir i)) (hDDm (yDir i)))
  have hdT : ∀ j, WeakProductL2Directional (M U) (dT j) (tDir j) :=
    fun j => weak_product_bounded_real_mul (hgt j) χ hχ hm (hDm (tDir j))
  have heT : ∀ j, WeakProductL2Directional (dT j) (eT j) (tDir j) := by
    intro j
    have hMj : M (gt j) = Wj j := Lp.ext ((productBoundedRealMul_ae χ hm (gt j)).trans (hWj j).symm)
    have hdiag : WeakProductL2Directional (M (gt j)) (tt j j) (tDir j) := by
      rw [hMj]
      exact htt j j
    exact weak_product_directional_add hdiag
      (weak_product_bounded_real_mul (hgt j) _ (hDχ (tDir j)) (hDm (tDir j)) (hDDm (tDir j)))
  have hBasisY : (EuclideanSpace.basisFun (Fin 4) ℝ : Fin 4 → KSSpace) = oscillatorBasis :=
    funext (EuclideanSpace.basisFun_apply (Fin 4) ℝ)
  have hBasisT : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis :=
    funext (EuclideanSpace.basisFun_apply κ ℝ)
  obtain ⟨a, b, ha, hb, _, _, _, _⟩ :=
    product_weakH2_of_factor_diagonal_jets (EuclideanSpace.basisFun (Fin 4) ℝ)
      (EuclideanSpace.basisFun κ ℝ) dY eY dT eT
      (by simpa only [hBasisY, yDir] using hdY)
      (by simpa only [hBasisY, yDir] using heY)
      (by simpa only [hBasisT, tDir] using hdT)
      (by simpa only [hBasisT, tDir] using heT)
  exact ⟨M U, a, b, productBoundedRealMul_ae χ hm U, ha, hb⟩


#print axioms local_inhomogeneous_grushin_joint_cutoff_h2
/-- Every genuine first spectator derivative of a homogeneous solution has local
joint H².  Source derivatives are derived by the local weak Leibniz rule. -/
theorem homogeneous_grushin_first_spectator_local_h2
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {U : Lp ℂ 2 (volume : Measure (Space κ))}
    {d : κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hd : ∀ j, WeakProductL2Directional U (d j) (tDir j))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0) :
    ∀ j, ProductLocalWeakH2On (d j : Space κ → ℂ) Ω := by
  intro j χ hχ hcχ hχΩ
  let A : Space κ → ℝ := fun p => fderiv ℝ B p (tDir j)
  let g : Space κ → ℂ := fun p => -(A p • U p)
  let k (l : κ) : Space κ → ℂ :=
    fun p => -(A p • d l p + fderiv ℝ A p (tDir l) • U p)
  have hA : ContDiffOn ℝ ∞ A Ω := by
    intro p hp
    exact (local_contDiffAt_directional_derivative (hB.contDiffAt (hΩ.mem_nhds hp))
      (tDir j)).contDiffWithinAt
  obtain ⟨hg, hPj⟩ := weak_grushin_homogeneous_spectator_equation c hΩ hB j (hd j) hP
  have hk : ∀ l, ProductLocallyL2On (k l) Ω := by
    intro l K hK hKΩ
    have hh := product_spectator_potential_leibniz_locallyL2 hΩ hA U (d l) (oscillatorBasis l)
    exact (hh K hK hKΩ).neg
  have hgD : ∀ l, ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • k l p) = -(∫ p, fderiv ℝ φ p (tDir l) • g p) := by
    intro l φ hφ hcφ hsφ
    have hh := (weakProduct_directional_local_potential_test (hd l) hΩ hA hφ hcφ hsφ).2.2
    simpa only [k, g, tDir, smul_neg, integral_neg, neg_neg] using congrArg Neg.neg hh
  obtain ⟨η, hη, hcη, hsη, V, hV, hχV, hVO, hη1⟩ :=
    exists_outer_plateau hcχ hΩ hχΩ
  obtain ⟨K, C, hK, hηK, hKΩ, hC, hgain⟩ :=
    local_weak_grushin_potential_cutoff_gain hc hΩ hη hcη hsη
  have hdl : ProductLocallyL2On (d j : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp (d j)).mono_measure Measure.restrict_le_self
  obtain ⟨Wouter, gy, gt, hyy, hWouter, _, _, _, hgy, hgt, hhyy⟩ :=
    hgain B (d j) g hB.continuousOn hdl hg hPj
  have hPouter : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, splitGrushin c oscillatorBasis B φ p • Wouter p) = ∫ p, φ p • g p := by
    intro φ hφ hcφ hsφ
    calc
      _ = ∫ p, splitGrushin c oscillatorBasis B φ p • d j p := by
        apply integral_congr_ae
        filter_upwards [hWouter] with p hp
        by_cases ht : p ∈ tsupport φ
        · rw [hp, hη1 p (hsφ ht), one_smul]
        · rw [splitGrushin_zero_off_test c oscillatorBasis B ht]
          simp only [zero_smul]
      _ = _ := hPj φ hφ hcφ (hsφ.trans hVO)
  have hgV : ProductLocallyL2On g V := fun K hK hKV => hg K hK (hKV.trans hVO)
  have hkV : ∀ l, ProductLocallyL2On (k l) V :=
    fun l K hK hKV => hk l K hK (hKV.trans hVO)
  have hgDV : ∀ l, ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ p, φ p • k l p) = -(∫ p, fderiv ℝ φ p (tDir l) • g p) :=
    fun l φ hφ hcφ hsφ => hgD l φ hφ hcφ (hsφ.trans hVO)
  obtain ⟨W, a, b, hW, ha, hb⟩ := local_inhomogeneous_grushin_joint_cutoff_h2
    hc hV (hB.mono hVO) hχ hcχ hχV hgy hgt hhyy g k hgV hkV hgDV hPouter
  refine ⟨W, a, ?_, ha, fun v w => ⟨b v w, hb v w⟩⟩
  filter_upwards [hW, hWouter] with p hp hw
  rw [hp]
  by_cases ht : p ∈ tsupport χ
  · rw [hw, hη1 p (hχV ht), one_smul]
  · simp only [image_eq_zero_of_notMem_tsupport ht, zero_smul]

#print axioms homogeneous_grushin_first_spectator_local_h2

end ManyBody.S8

