import ManyBody.S8.Internal.GrushinYCommutator
import ManyBody.S8.Internal.WeakProductLocalCompatibility

/-!
# Joint local H² of genuine first Y derivatives

The Y equation supplies the new YY derivatives.  First spectator derivatives
have joint local H² by the actual spectator recurrence.  Local weak mixed
commutation and a common plateau turn their YT derivatives into the required TT
diagonals of the same first Y derivative.  The frozen diagonal reconstruction
then supplies all ordered arbitrary-direction second derivatives.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem homogeneous_grushin_first_y_local_h2
    {c : ℝ} (hc : 0 < c) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {U d : Lp ℂ 2 (volume : Measure (Space κ))} (w : KSSpace)
    (hD : WeakProductL2Directional U d (w, 0))
    {dt et : κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hdt : ∀ j, WeakProductL2Directional U (dt j) (tDir j))
    (het : ∀ j, WeakProductL2Directional (dt j) (et j) (tDir j))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • U p) = 0) :
    ProductLocalWeakH2On (d : Space κ → ℂ) Ω := by
  intro χ hχ hcχ hχΩ
  have htH2 := homogeneous_grushin_first_spectator_local_h2 hc hΩ hB hdt hP
  obtain ⟨η, hη, hcη, hsη, V, hV, hχV, hVO, hη1⟩ :=
    exists_outer_plateau hcχ hΩ hχΩ
  have hs : ∀ j : κ,
      ∃ Wj : Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ a : Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ b : Space κ → Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
        Wj =ᵐ[volume] (fun p => η p • dt j p) ∧
        (∀ v, WeakProductL2Directional Wj (a v) v) ∧
        ∀ v u, WeakProductL2Directional (a v) (b v u) u := by
    intro j
    obtain ⟨Wj, a, hWj, ha, hb⟩ := htH2 j η hη hcη hsη
    choose b hb using hb
    exact ⟨Wj, a, b, hWj, ha, hb⟩
  choose Wj a b hWj ha hb using hs
  have hDTd (j : κ) : ProductWeakDirectionalOn (d : Space κ → ℂ)
      (a j (w, 0) : Space κ → ℂ) (tDir j) V := by
    have hDT : ProductWeakDirectionalOn (U : Space κ → ℂ)
        (dt j : Space κ → ℂ) (tDir j) V :=
      fun φ hφ hcφ _ => hdt j φ hφ hcφ
    have hDY : ProductWeakDirectionalOn (U : Space κ → ℂ)
        (d : Space κ → ℂ) (w, 0) V :=
      fun φ hφ hcφ _ => hD φ hφ hcφ
    exact weak_product_local_mixed_commute hDT hDY
      (weak_product_on_plateau (hWj j) hη1 (ha j (w, 0)))
  have hm : MemLp χ ⊤ volume := hχ.continuous.memLp_top_of_hasCompactSupport hcχ volume
  have hDχ (v : Space κ) : ContDiff ℝ ∞ (fun p => fderiv ℝ χ p v) :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDm (v : Space κ) : MemLp (fun p => fderiv ℝ χ p v) ⊤ volume :=
    (hDχ v).continuous.memLp_top_of_hasCompactSupport (hcχ.fderiv_apply ℝ v) volume
  have hDDm (v : Space κ) : MemLp
      (fun p => fderiv ℝ (fun q => fderiv ℝ χ q v) p v) ⊤ volume :=
    (((hDχ v).fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const).continuous.memLp_top_of_hasCompactSupport
      ((hcχ.fderiv_apply ℝ v).fderiv_apply ℝ v) volume
  let M := productBoundedRealMul χ hm
  let D (v : Space κ) := productBoundedRealMul (fun p => fderiv ℝ χ p v) (hDm v)
  let DD (v : Space κ) := productBoundedRealMul
    (fun p => fderiv ℝ (fun q => fderiv ℝ χ q v) p v) (hDDm v)
  let dT (j : κ) := M (a j (w, 0)) + D (tDir j) d
  let eT (j : κ) := (M (b j (w, 0) (tDir j)) + D (tDir j) (a j (w, 0))) +
    (D (tDir j) (a j (w, 0)) + DD (tDir j) d)
  have hdT : ∀ j, WeakProductL2Directional (M d) (dT j) (tDir j) := by
    intro j
    exact weak_product_local_cutoff (hDTd j) hχ hcχ hχV hm (hDm (tDir j))
  have heT : ∀ j, WeakProductL2Directional (dT j) (eT j) (tDir j) := by
    intro j
    apply weak_product_directional_add
    · exact weak_product_bounded_real_mul (hb j (w, 0) (tDir j)) χ hχ hm (hDm (tDir j))
    · exact weak_product_local_cutoff (hDTd j) (hDχ (tDir j))
        (hcχ.fderiv_apply ℝ (tDir j))
        ((tsupport_fderiv_apply_subset ℝ (tDir j)).trans hχV)
        (hDm (tDir j)) (hDDm (tDir j))
  obtain ⟨W, gy, gt, hyy, hW, hgy, hgt, hhyy⟩ :=
    local_homogeneous_grushin_y_cutoff_gain hc hΩ hB w hD hdt het hP hχ hcχ hχΩ
  have hMW : M d = W := Lp.ext ((productBoundedRealMul_ae χ hm d).trans hW.symm)
  have hdY : ∀ i, WeakProductL2Directional (M d) (gy i) (yDir i) := by
    rw [hMW]
    exact hgy
  have heY : ∀ i, WeakProductL2Directional (gy i) (hyy i i) (yDir i) :=
    fun i => hhyy i i
  have hBasisY : (EuclideanSpace.basisFun (Fin 4) ℝ : Fin 4 → KSSpace) = oscillatorBasis :=
    funext (EuclideanSpace.basisFun_apply (Fin 4) ℝ)
  have hBasisT : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis :=
    funext (EuclideanSpace.basisFun_apply κ ℝ)
  obtain ⟨ay, byy, hay, hby, _, _, _, _⟩ :=
    product_weakH2_of_factor_diagonal_jets (EuclideanSpace.basisFun (Fin 4) ℝ)
      (EuclideanSpace.basisFun κ ℝ) gy (fun i => hyy i i) dT eT
      (by simpa only [hBasisY, yDir] using hdY)
      (by simpa only [hBasisY, yDir] using heY)
      (by simpa only [hBasisT, tDir] using hdT)
      (by simpa only [hBasisT, tDir] using heT)
  exact ⟨M d, ay, productBoundedRealMul_ae χ hm d, hay, fun v u => ⟨byy v u, hby v u⟩⟩

#print axioms homogeneous_grushin_first_y_local_h2
end ManyBody.S8

