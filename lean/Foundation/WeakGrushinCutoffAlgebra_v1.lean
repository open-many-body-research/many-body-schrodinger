import WeakGrushinJetFields_v1
import GrushinCutoffCommutator_v1

/-! The cutoff commutator for genuine weak jet fields. The algebraic theorem
uses the explicit second-jet product formula, not an assumed operator identity.
The two error expressions are finite sums of actual cutoff derivatives and
actual L2 function/first-jet representatives. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def cutoffYError (χ : Space κ → ℝ) (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (p : Space κ) : ℂ :=
  ∑ i : Fin 4, (fderiv ℝ (fun q => fderiv ℝ χ q (yDir i)) p (yDir i) • f p +
    (2*fderiv ℝ χ p (yDir i)) • d (yDir i) p)

def cutoffTError (χ : Space κ → ℝ) (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (p : Space κ) : ℂ :=
  ∑ j : κ, (fderiv ℝ (fun q => fderiv ℝ χ q (tDir j)) p (tDir j) • f p +
    (2*fderiv ℝ χ p (tDir j)) • d (tDir j) p)

theorem principal_cutoff_of_second_jet_formula (c : ℝ)
    (χ : Space κ → ℝ) (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e b : Jet κ)
    (hb : ∀ v w, b v w =ᵐ[volume] (fun p =>
      (χ p • e v w p+fderiv ℝ χ p w • d v p)+
      (fderiv ℝ χ p v • d w p+
        fderiv ℝ (fun q => fderiv ℝ χ q v) p w • f p))) :
    principal c b =ᵐ[volume] (fun p => χ p • principal c e p -
      cutoffYError χ f d p - (c*‖p.1‖^2) • cutoffTError χ f d p) := by
  have hdiag (v : Space κ) : b v v =ᵐ[volume] (fun p => χ p • e v v p +
      (fderiv ℝ (fun q => fderiv ℝ χ q v) p v • f p +
        (2*fderiv ℝ χ p v) • d v p)) := by
    filter_upwards [hb v v] with p hp
    rw [hp]
    module
  have hy : ∀ᵐ p ∂volume, ∀ i : Fin 4,
      b (yDir i) (yDir i) p = χ p • e (yDir i) (yDir i) p +
        (fderiv ℝ (fun q => fderiv ℝ χ q (yDir i)) p (yDir i) • f p +
          (2*fderiv ℝ χ p (yDir i)) • d (yDir i) p) := by
    rw [ae_all_iff]
    exact fun i => hdiag (yDir i)
  have ht : ∀ᵐ p ∂volume, ∀ j : κ,
      b (tDir j) (tDir j) p = χ p • e (tDir j) (tDir j) p +
        (fderiv ℝ (fun q => fderiv ℝ χ q (tDir j)) p (tDir j) • f p +
          (2*fderiv ℝ χ p (tDir j)) • d (tDir j) p) := by
    rw [ae_all_iff]
    exact fun j => hdiag (tDir j)
  filter_upwards [hy,ht] with p hp hq
  simp only [principal,tWeighted,cutoffYError,cutoffTError,hp,hq,
    Finset.sum_add_distrib,← Finset.smul_sum]
  module

theorem cutoffYError_ae_smooth (χ : Space κ → ℝ)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))} {G : Space κ → ℂ}
    (hf : f =ᵐ[volume] G)
    (hd : ∀ v, d v =ᵐ[volume] (fun p => fderiv ℝ G p v)) :
    cutoffYError χ f d =ᵐ[volume] grushinCutoffYError χ G := by
  have hy : ∀ᵐ p ∂volume, ∀ i : Fin 4, d (yDir i) p = fderiv ℝ G p (yDir i) := by
    rw [ae_all_iff]
    exact fun i => hd (yDir i)
  filter_upwards [hf,hy] with p hp hq
  simp only [cutoffYError,grushinCutoffYError,hp,hq]
  rfl

theorem cutoffTError_ae_smooth (χ : Space κ → ℝ)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))} {G : Space κ → ℂ}
    (hf : f =ᵐ[volume] G)
    (hd : ∀ v, d v =ᵐ[volume] (fun p => fderiv ℝ G p v)) :
    cutoffTError χ f d =ᵐ[volume] grushinCutoffTError χ G := by
  have ht : ∀ᵐ p ∂volume, ∀ j : κ, d (tDir j) p = fderiv ℝ G p (tDir j) := by
    rw [ae_all_iff]
    exact fun j => hd (tDir j)
  filter_upwards [hf,ht] with p hp hq
  simp only [cutoffTError,grushinCutoffTError,hp,hq]
  rfl

#print axioms principal_cutoff_of_second_jet_formula
#print axioms cutoffYError_ae_smooth
#print axioms cutoffTError_ae_smooth
end TheoremT.Continuum.WeakGrushin
