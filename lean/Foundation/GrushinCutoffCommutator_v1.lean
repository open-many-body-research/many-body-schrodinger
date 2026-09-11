import SecondDirectionalSmul_v1
import EuclideanGrushinPrincipal_v1

noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def grushinCutoffYError (η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ)
    (G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) : ℂ :=
  ∑ i : ι, ((partialYDirectional (partialYDirectional η (oscillatorBasis i)) (oscillatorBasis i) p) • G p +
    (2*partialYDirectional η (oscillatorBasis i) p) • partialYDirectional G (oscillatorBasis i) p)

def grushinCutoffTError (η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ)
    (G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) : ℂ :=
  ∑ j : κ, ((partialTDirectional (partialTDirectional η (oscillatorBasis j)) (oscillatorBasis j) p) • G p +
    (2*partialTDirectional η (oscillatorBasis j) p) • partialTDirectional G (oscillatorBasis j) p)

theorem grushinYLaplacian_cutoff {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hη : ContDiff ℝ ∞ η) (hG : ContDiff ℝ ∞ G) (p) :
    grushinYLaplacian (fun q => η q • G q) p =
      grushinCutoffYError η G p + η p • grushinYLaplacian G p := by
  unfold grushinYLaplacian grushinCutoffYError partialYDirectional
  simp only [second_same_directional_smul hη hG, Finset.sum_add_distrib, Finset.smul_sum]

theorem grushinTLaplacian_cutoff {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hη : ContDiff ℝ ∞ η) (hG : ContDiff ℝ ∞ G) (p) :
    grushinTLaplacian (fun q => η q • G q) p =
      grushinCutoffTError η G p + η p • grushinTLaplacian G p := by
  unfold grushinTLaplacian grushinCutoffTError partialTDirectional
  simp only [second_same_directional_smul hη hG, Finset.sum_add_distrib, Finset.smul_sum]

theorem euclideanGrushin_cutoff (c : ℝ)
    {η : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ}
    {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hη : ContDiff ℝ ∞ η) (hG : ContDiff ℝ ∞ G) (p) :
    euclideanGrushin c (fun q => η q • G q) p =
      η p • euclideanGrushin c G p - grushinCutoffYError η G p -
        (c*‖p.1‖^2) • grushinCutoffTError η G p := by
  simp only [euclideanGrushin,grushinYLaplacian_cutoff hη hG,grushinTLaplacian_cutoff hη hG]
  module

#print axioms grushinYLaplacian_cutoff
#print axioms grushinTLaplacian_cutoff
#print axioms euclideanGrushin_cutoff
end TheoremT.Continuum
