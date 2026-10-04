import SmoothCutoffRescaleQuantitative_v1
import GrushinCoordinateCutoffBounds_v1

/-!
The actual translated and rescaled cutoff on Euclidean four-space times
Euclidean three-space has explicit Grushin coefficient bounds. The product
uses its ordinary maximum norm. The fixed base cutoff and its first two
operator-norm derivative bounds are supplied; no computed base cutoff or
unknown solution derivative is introduced by this transport theorem.
-/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem cutoff_yDir_norm {κ : Type} [Fintype κ] [DecidableEq κ] (i : Fin 4) :
    ‖(yDir i : Space κ)‖ = 1 := by
  simp [yDir, oscillatorBasis]

theorem cutoff_tDir_norm {κ : Type} [Fintype κ] [DecidableEq κ] (j : κ) :
    ‖(tDir j : Space κ)‖ = 1 := by
  simp [tDir, oscillatorBasis]

theorem cutoffRescale_y_radius
    {κ : Type} [Fintype κ] [DecidableEq κ]
    {η : Space κ → ℝ} {Rout : ℝ}
    (hs : tsupport η ⊆ Metric.closedBall (0 : Space κ) Rout)
    (a : Space κ) {r : ℝ} (hr : 0 < r) :
    ∀ p ∈ tsupport (cutoffRescale η a r), ‖p.1‖ ≤ ‖a.1‖ + r*Rout := by
  intro p hp
  have hb := cutoffRescale_tsupport_closedBall hs a hr hp
  have hnorm : ‖p-a‖ ≤ r*Rout := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hb
  have hfst : ‖p.1-a.1‖ ≤ ‖p-a‖ := by
    exact le_max_left _ _
  calc
    ‖p.1‖ = ‖(p.1-a.1)+a.1‖ := by rw [sub_add_cancel]
    _ ≤ ‖p.1-a.1‖+‖a.1‖ := norm_add_le _ _
    _ ≤ r*Rout+‖a.1‖ := add_le_add (hfst.trans hnorm) (le_refl _)
    _ = _ := by ring

theorem cutoffRescale_grushin_family
    {η : Space (Fin 3) → ℝ} (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η)
    {Rin Rout M L1 L2 R c : ℝ} (hc : 0 ≤ c)
    (hs : tsupport η ⊆ Metric.closedBall (0 : Space (Fin 3)) Rout)
    (hp : ∀ x ∈ Metric.closedBall (0 : Space (Fin 3)) Rin, η x = 1)
    (hM : ∀ x, |η x| ≤ M)
    (hL1 : ∀ x, ‖fderiv ℝ η x‖ ≤ L1)
    (hL2 : ∀ x, ‖fderiv ℝ (fderiv ℝ η) x‖ ≤ L2)
    (a : Space (Fin 3)) {r : ℝ} (hr : 0 < r)
    (hR : ‖a.1‖ + r*Rout ≤ R) :
    ContDiff ℝ ∞ (cutoffRescale η a r) ∧
    HasCompactSupport (cutoffRescale η a r) ∧
    tsupport (cutoffRescale η a r) ⊆ Metric.closedBall a (r*Rout) ∧
    (∀ x ∈ Metric.closedBall a (r*Rin), cutoffRescale η a r x = 1) ∧
    (∀ x, |cutoffRescale η a r x| ≤ M) ∧
    (∀ p, cutoffGradientWeight c (cutoffRescale η a r) p ≤
      (4+3*c*R^2)*(L1/r)^2) ∧
    ∀ p, |combinedCutoffScalar c (cutoffRescale η a r) p| ≤
      (4+3*c*R^2)*(L2/r^2) := by
  have hy (p : Space (Fin 3)) (i : Fin 4) :
      |fderiv ℝ (cutoffRescale η a r) p (yDir i)| ≤ L1/r := by
    simpa only [cutoff_yDir_norm,mul_one] using
      cutoffRescale_first_bound hη hL1 a hr p (yDir i)
  have ht (p : Space (Fin 3)) (j : Fin 3) :
      |fderiv ℝ (cutoffRescale η a r) p (tDir j)| ≤ L1/r := by
    simpa only [cutoff_tDir_norm,mul_one] using
      cutoffRescale_first_bound hη hL1 a hr p (tDir j)
  have hyy (p : Space (Fin 3)) (i : Fin 4) :
      |fderiv ℝ (fun q => fderiv ℝ (cutoffRescale η a r) q (yDir i)) p
        (yDir i)| ≤ L2/r^2 := by
    simpa only [cutoff_yDir_norm,mul_one] using
      cutoffRescale_second_bound hη hL2 a hr p (yDir i) (yDir i)
  have htt (p : Space (Fin 3)) (j : Fin 3) :
      |fderiv ℝ (fun q => fderiv ℝ (cutoffRescale η a r) q (tDir j)) p
        (tDir j)| ≤ L2/r^2 := by
    simpa only [cutoff_tDir_norm,mul_one] using
      cutoffRescale_second_bound hη hL2 a hr p (tDir j) (tDir j)
  have hradius : ∀ p ∈ tsupport (cutoffRescale η a r), ‖p.1‖ ≤ R := by
    intro p hp'
    exact (cutoffRescale_y_radius hs a hr p hp').trans hR
  have hL2nonneg : 0 ≤ L2 :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ η) 0)).trans (hL2 0)
  refine ⟨cutoffRescale_contDiff hη a r,
    cutoffRescale_hasCompactSupport hcη a hr.ne',
    cutoffRescale_tsupport_closedBall hs a hr,
    cutoffRescale_plateau_closedBall hp a hr,
    cutoffRescale_value_bound hM a r,?_,?_⟩
  · intro p
    have hb := cutoffGradientWeight_coordinate_bound hc (L1/r) R
      (cutoffRescale η a r) hy ht hradius p
    simpa only [Fintype.card_fin,Nat.cast_ofNat,mul_comm,mul_left_comm,mul_assoc] using hb
  · intro p
    have hb := combinedCutoffScalar_coordinate_bound hc (L2/r^2) R
      (div_nonneg hL2nonneg (sq_nonneg r))
      (cutoffRescale η a r) hyy htt hradius p
    simpa only [Fintype.card_fin,Nat.cast_ofNat,mul_comm,mul_left_comm,mul_assoc] using hb

#print axioms cutoff_yDir_norm
#print axioms cutoff_tDir_norm
#print axioms cutoffRescale_y_radius
#print axioms cutoffRescale_grushin_family
end TheoremT.Continuum.WeakGrushin
