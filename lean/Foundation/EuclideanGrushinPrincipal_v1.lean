import CompactPartialIntegralDirectional_v1
import PartialSpectatorDirectional_v1
import EuclideanOscillatorCross_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def grushinYLaplacian (G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) : ℂ :=
  ∑ k : ι, partialYDirectional (partialYDirectional G (oscillatorBasis k)) (oscillatorBasis k) p

def grushinTLaplacian (G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) : ℂ :=
  ∑ k : κ, partialTDirectional (partialTDirectional G (oscillatorBasis k)) (oscillatorBasis k) p

def euclideanGrushin (c : ℝ) (G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) : ℂ :=
  -grushinYLaplacian G p - (c*‖p.1‖^2) • grushinTLaplacian G p

theorem grushinYLaplacian_contDiff {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (grushinYLaplacian G) :=
  ContDiff.sum (fun k _ => partialYDirectional_contDiff (partialYDirectional_contDiff hG _) _)

theorem grushinTLaplacian_contDiff {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (grushinTLaplacian G) :=
  ContDiff.sum (fun k _ => partialTDirectional_contDiff (partialTDirectional_contDiff hG _) _)

theorem grushinYLaplacian_hasCompactSupport {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hc : HasCompactSupport G) : HasCompactSupport (grushinYLaplacian G) := by
  have he : grushinYLaplacian G = ∑ k : ι,
      partialYDirectional (partialYDirectional G (oscillatorBasis k)) (oscillatorBasis k) := by
    funext p; simp [grushinYLaplacian]
  rw [he]
  exact HasCompactSupport.finset_sum (fun k _ =>
    partialYDirectional_hasCompactSupport (partialYDirectional_hasCompactSupport hc _) _)

theorem grushinTLaplacian_hasCompactSupport {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hc : HasCompactSupport G) : HasCompactSupport (grushinTLaplacian G) := by
  have he : grushinTLaplacian G = ∑ k : κ,
      partialTDirectional (partialTDirectional G (oscillatorBasis k)) (oscillatorBasis k) := by
    funext p; simp [grushinTLaplacian]
  rw [he]
  exact HasCompactSupport.finset_sum (fun k _ =>
    partialTDirectional_hasCompactSupport (partialTDirectional_hasCompactSupport hc _) _)

theorem euclideanGrushin_contDiff (c : ℝ) {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (euclideanGrushin c G) :=
  (grushinYLaplacian_contDiff hG).neg.sub
    ((contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_fst)).smul (grushinTLaplacian_contDiff hG))

theorem euclideanGrushin_hasCompactSupport (c : ℝ) {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hc : HasCompactSupport G) : HasCompactSupport (euclideanGrushin c G) := by
  have hw : HasCompactSupport (fun p => (c*‖p.1‖^2) • grushinTLaplacian G p) := by
    apply (grushinTLaplacian_hasCompactSupport hc).mono
    intro p hp
    change grushinTLaplacian G p ≠ 0
    intro hz
    exact hp (by simp [hz])
  exact (grushinYLaplacian_hasCompactSupport hc).neg.sub hw

#print axioms euclideanGrushin_contDiff
#print axioms euclideanGrushin_hasCompactSupport
end TheoremT.Continuum
