import LocalizedSmoothCoulombCoefficient_v1
import WeakH1Algebra_v1
import WeakDerivativeEllipticGain_v1
import CompactCutoffLaplacian_v1
import CoulombTransformedEquation_v1

import ActualLocalWeakOrder_v1
import ActualWeakOrderSum_v1
import ActualWeakOrderEllipticGain_v1
import TestLaplacianSupport_v1

/-! One genuine local regularity gain for the actual Coulomb equation. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem scalar_coulomb_local_weakOrder_gain {N n : ℕ} {Z E : ℝ} {f : SpatialL2 N}
    (hgraph : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (hlocal : HasLocalWeakOrder f {x | collisionFree x} (n+1)) :
    HasLocalWeakOrder f {x | collisionFree x} (n+2) := by
  intro χ hχ hc hs
  obtain ⟨d,e,hd,he,hge⟩ := hgraph
  have hf1 : HasLocalWeakOrder f {x | collisionFree x} n := hlocal.mono (Nat.le_succ n)
  have hd1 (k : Coordinate N) : HasLocalWeakOrder (d k) {x | collisionFree x} n :=
    hlocal.weakPartial (collisionFree_isOpen N) (hd k)
  have hD (k : Coordinate N) : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (coordinateVector k)) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hL : ContDiff ℝ ∞ (realTestLaplacian χ) := by
    apply ContDiff.sum
    intro k hk
    exact ((hD k).fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  obtain ⟨g0,hg0,hg0a⟩ := hf1.compact_product_rep
    (localized_coulomb_coefficient_smooth Z E hχ hs) (localized_coulomb_coefficient_compact Z E hc) (tsupport_mul_subset_left.trans hs)
  have hgd (k : Coordinate N) := (hd1 k).compact_product_rep (hD k) (hc.fderiv_apply ℝ (coordinateVector k))
    ((tsupport_fderiv_apply_subset ℝ (coordinateVector k)).trans hs)
  choose g hg hga using hgd
  obtain ⟨g2,hg2,hg2a⟩ := hf1.compact_product_rep hL (realTestLaplacian_compact hc) ((realTestLaplacian_tsupport_subset χ).trans hs)
  let w : SpatialL2 N := g0+(2:ℂ) • (∑ k,g k)+g2
  have hw1 : HasWeakOrder w n := (hg0.add ((hasWeakOrder_finset_sum Finset.univ g (fun k _ => hg k)).smul 2)).add hg2
  obtain ⟨u,a,b,hua,hab,hu,ha,hb⟩ := compact_cutoff_weak_laplacian hχ hc hd he
  have hbw : (∑ k : Coordinate N,b k k : SpatialL2 N)=w := by
    apply Lp.ext
    filter_upwards [hb,hg0a,hg2a,ae_all_iff.mpr hga,hge,Lp.coeFn_smul (E:ℂ) f,
      Lp.coeFn_add (g0+(2:ℂ) • (∑ k,g k)) g2,
      Lp.coeFn_add g0 ((2:ℂ) • (∑ k,g k)),Lp.coeFn_smul (2:ℂ) (∑ k,g k),
      Lp.coeFn_fun_finsetSum Finset.univ g] with x hbx h0 h2 hx hge hsE hwadd hwa hws hgs
    have heq : (∑ k,e k k x)=2*((coulombPotential N Z x : ℂ)-(E:ℂ))*f x := by
      rw [hsE] at hge
      change (E:ℂ)*f x=_ at hge
      linear_combination 2*hge
    change (∑ k,b k k : SpatialL2 N) x=(g0+(2:ℂ) • (∑ k,g k)+g2) x
    simp only [Pi.add_apply,Pi.smul_apply] at hwadd hwa hws
    rw [hbx,hwadd,hwa,hws,hgs,h0,h2]
    simp only [hx,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_ofNat,smul_eq_mul]
    rw [heq]
    ring
  have hΔ := distribution_laplacian_eq_sum_of_weakPartial a (fun k => b k k) hua (fun k => hab k k)
  rw [hbw] at hΔ
  have huO := hasWeakOrder_add_two_of_laplacian hΔ hw1
  have hcut : cutoffMul χ hχ.continuous hc f=u :=
    Lp.ext ((cutoffMul_ae χ hχ.continuous hc f).trans hu.symm)
  rw [hcut]
  exact huO

#print axioms scalar_coulomb_local_weakOrder_gain
end TheoremT.Continuum
