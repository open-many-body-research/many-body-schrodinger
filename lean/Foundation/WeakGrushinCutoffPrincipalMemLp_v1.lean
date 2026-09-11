import WeakGrushinCutoffMemLp_v1

/-! A compact cutoff of an arbitrary global L2 second-jet field has an L2
Grushin principal expression. Consequently the exact weak cutoff jet formula
supplies a genuine L2 Hamiltonian principal output, even when the uncut weighted
principal expression is not globally L2. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem cutoff_principal_memLp (c : ℝ)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (e : Jet κ) : MemLp (fun p => χ p • principal c e p) 2 volume := by
  have hχm : MemLp χ ⊤ volume :=
    hχ.continuous.memLp_top_of_hasCompactSupport hc volume
  have ha : Continuous (fun p : Space κ => χ p*(c*‖p.1‖^2)) := by fun_prop
  have ham : MemLp (fun p : Space κ => χ p*(c*‖p.1‖^2)) ⊤ volume :=
    ha.memLp_top_of_hasCompactSupport hc.mul_right volume
  have hy : MemLp (fun p => ∑ i : Fin 4, χ p • e (yDir i) (yDir i) p) 2 volume := by
    apply memLp_finsetSum
    intro i hi
    exact (Lp.memLp (e (yDir i) (yDir i))).smul hχm
  have ht : MemLp (fun p => ∑ j : κ, (χ p*(c*‖p.1‖^2)) • e (tDir j) (tDir j) p) 2 volume := by
    apply memLp_finsetSum
    intro j hj
    exact (Lp.memLp (e (tDir j) (tDir j))).smul ham
  simpa only [principal,tWeighted,smul_sub,smul_neg,Finset.smul_sum,← mul_smul,
    Pi.sub_def,Pi.neg_def] using hy.neg.sub ht

theorem principal_cutoff_memLp_of_second_jet_formula (c : ℝ)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e b : Jet κ)
    (hb : ∀ v w, b v w =ᵐ[volume] (fun p =>
      (χ p • e v w p+fderiv ℝ χ p w • d v p)+
      (fderiv ℝ χ p v • d w p+
        fderiv ℝ (fun q => fderiv ℝ χ q v) p w • f p))) :
    MemLp (principal c b) 2 volume := by
  have hm : MemLp (fun p => χ p • principal c e p -
      cutoffYError χ f d p - (c*‖p.1‖^2) • cutoffTError χ f d p) 2 volume := by
    simpa only [Pi.sub_def] using
      ((cutoff_principal_memLp c hχ hc e).sub (cutoffYError_memLp hχ hc f d)).sub
        (weighted_cutoffTError_memLp c hχ hc f d)
  exact hm.ae_eq (principal_cutoff_of_second_jet_formula c χ f d e b hb).symm

#print axioms cutoff_principal_memLp
#print axioms principal_cutoff_memLp_of_second_jet_formula
end TheoremT.Continuum.WeakGrushin
