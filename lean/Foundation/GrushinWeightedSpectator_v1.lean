import EuclideanGrushinPrincipal_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def grushinWeightedT (c : ℝ) (G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) : ℂ :=
  (c*‖p.1‖^2) • grushinTLaplacian G p

theorem grushinWeightedT_contDiff (c : ℝ) {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (grushinWeightedT c G) :=
  ((contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_fst)).smul (grushinTLaplacian_contDiff hG))

theorem grushinWeightedT_hasCompactSupport (c : ℝ) {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hc : HasCompactSupport G) : HasCompactSupport (grushinWeightedT c G) := by
  apply (grushinTLaplacian_hasCompactSupport hc).mono
  intro p hp
  change grushinTLaplacian G p ≠ 0
  intro hz
  exact hp (by simp [grushinWeightedT,hz])

#print axioms grushinWeightedT_contDiff
#print axioms grushinWeightedT_hasCompactSupport
end TheoremT.Continuum
