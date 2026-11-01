import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic

/-! Actual local invariance of a function with a convergent real power series
implies invariance of each diagonal multilinear coefficient. The coefficient
maps need not be symmetric; no equality of their off-diagonal values is claimed.
The proof uses the pinned diagonal uniqueness theorem for the zero series. -/
set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators
namespace TheoremT.Continuum

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem powerSeries_diagonal_eq_of_eventually
    {f g : E → F} {p q : FormalMultilinearSeries ℝ E F} {x : E}
    (hp : HasFPowerSeriesAt f p x) (hq : HasFPowerSeriesAt g q x)
    (heq : f =ᶠ[𝓝 x] g) (n : ℕ) (y : E) :
    p n (fun _ => y) = q n (fun _ => y) := by
  have hz : HasFPowerSeriesAt (0 : E → F) (p-q) x := by
    simpa only [sub_self] using (hp.congr heq).sub hq
  have hdiag := hz.apply_eq_zero n y
  simpa only [FormalMultilinearSeries.sub_apply,sub_apply,sub_eq_zero] using hdiag

theorem powerSeries_diagonal_invariant
    {f : E → F} {p : FormalMultilinearSeries ℝ E F}
    (hf : HasFPowerSeriesAt f p 0) (L : E →L[ℝ] E)
    (hInv : (f ∘ L) =ᶠ[𝓝 (0 : E)] f) (n : ℕ) (y : E) :
    p n (fun _ => L y) = p n (fun _ => y) := by
  have hcomp : HasFPowerSeriesAt (f ∘ L) (p.compContinuousLinearMap L) 0 :=
    (show HasFPowerSeriesAt f p (L 0) by simpa only [map_zero] using hf).compContinuousLinearMap
  simpa only [FormalMultilinearSeries.compContinuousLinearMap_apply,Function.comp_def] using
    powerSeries_diagonal_eq_of_eventually hcomp hf hInv n y

theorem powerSeries_odd_diagonal_eq_zero
    {f : E → F} {p : FormalMultilinearSeries ℝ E F}
    (hf : HasFPowerSeriesAt f p 0)
    (heven : (fun x => f (-x)) =ᶠ[𝓝 (0 : E)] f)
    {n : ℕ} (hn : Odd n) (y : E) : p n (fun _ => y) = 0 := by
  have hInv : (f ∘ (-ContinuousLinearMap.id ℝ E)) =ᶠ[𝓝 (0 : E)] f := by
    simpa only [Function.comp_def,neg_apply,ContinuousLinearMap.id_apply] using heven
  have hi : p n (fun _ => -y) = p n (fun _ => y) := by
    simpa only [neg_apply,ContinuousLinearMap.id_apply] using
      powerSeries_diagonal_invariant hf (-ContinuousLinearMap.id ℝ E) hInv n y
  have hm : p n (fun _ => -y) = -(p n (fun _ => y)) := by
    simpa only [neg_one_smul,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      hn.neg_one_pow,neg_one_smul] using
      (p n).map_smul_univ (fun _ : Fin n => (-1 : ℝ)) (fun _ => y)
  have heq : -(p n (fun _ => y)) = p n (fun _ => y) := hm.symm.trans hi
  have hz : (2 : ℝ) • p n (fun _ => y) = 0 := by
    calc
      _ = p n (fun _ => y) + p n (fun _ => y) := two_smul _ _
      _ = -(p n (fun _ => y)) + p n (fun _ => y) :=
        congrArg (fun z => z + p n (fun _ => y)) heq.symm
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

end TheoremT.Continuum
