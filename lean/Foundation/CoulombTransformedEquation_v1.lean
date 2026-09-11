import LocalizedCuspWeakJet_v1
import CoulombCuspHessianTrace_v1
import CoulombCuspGradientBound_v1
import FiniteCuspCancellation_v1

/-! Actual Coulomb eigenfunction equation after the physical cusp transform.
All weak derivatives and products are constructed, including collision strata.
The cutoff forcing is explicit in the original weak first derivatives. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem scalar_coulomb_localized_transformed_equation {N : ℕ} {Z E : ℝ}
    {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ d : Coordinate N → SpatialL2 N, ∃ g : SpatialL2 N,
      ∃ a : Coordinate N → SpatialL2 N, ∃ b : Coordinate N → Coordinate N → SpatialL2 N,
        (∀ k, WeakPartial f (d k) k) ∧ HasH2 g ∧
        (∀ k, WeakPartial g (a k) k) ∧ (∀ k l, WeakPartial (a k) (b k l) l) ∧
        g =ᵐ[volume] (fun x => (χ x*Real.exp (-coulombCusp N Z x)) • f x) ∧
        ∀ᵐ x, (∑ k, b k k x) =
          -2*(∑ k, (coulombCuspGradient N Z (coordinateVector k) x : ℂ)*a k x)-
          (((∑ k, (coulombCuspGradient N Z (coordinateVector k) x)^2)+2*E : ℝ) : ℂ)*g x+
          (Real.exp (-coulombCusp N Z x) : ℂ)*
            ((realTestLaplacian χ x : ℂ)*f x+
              2*(∑ k, (fderiv ℝ χ x (coordinateVector k) : ℂ)*d k x)) := by
  obtain ⟨d,e,hd,he,hgraph⟩ := hg
  obtain ⟨g,a,b,hga,hab,hv,ha,hb⟩ := localizedCusp_weak_jet N Z hχ hc hd he
  refine ⟨d,g,a,b,hd,⟨a,hga,fun k l => ⟨b k l,hab k l⟩⟩,hga,hab,hv,?_⟩
  filter_upwards [hgraph,Lp.coeFn_smul (E : ℂ) f,hv,ae_all_iff.mpr ha,
    ae_all_iff.mpr (fun k => hb k k)] with x hx hs hgv hax hbx
  have heq : (∑ k, e k k x)=2*((coulombPotential N Z x : ℂ)-(E : ℂ))*f x := by
    rw [hs] at hx
    change (E : ℂ)*f x = _ at hx
    linear_combination 2*hx
  have hh : (∑ k, (coulombCuspHessian N Z (coordinateVector k) (coordinateVector k) x : ℂ)) =
      2*(coulombPotential N Z x : ℂ) := by
    exact_mod_cast coulombCuspHessian_trace N Z x
  have hA (k : Coordinate N) : a k x =
      (Real.exp (-coulombCusp N Z x) : ℂ)*(χ x : ℂ)*d k x+
      (Real.exp (-coulombCusp N Z x) : ℂ)*
        ((fderiv ℝ χ x (coordinateVector k) : ℂ)-(χ x : ℂ)*
          (coulombCuspGradient N Z (coordinateVector k) x : ℂ))*f x := by
    rw [hax k]
    simp only [localizedCusp,localizedCuspGradient,Complex.real_smul,
      Complex.ofReal_mul,Complex.ofReal_sub]
    ring
  have hB (k : Coordinate N) : b k k x =
      ((Real.exp (-coulombCusp N Z x) : ℂ)*(χ x : ℂ)*e k k x+
      (Real.exp (-coulombCusp N Z x) : ℂ)*
        ((fderiv ℝ χ x (coordinateVector k) : ℂ)-(χ x : ℂ)*
          (coulombCuspGradient N Z (coordinateVector k) x : ℂ))*d k x)+
      ((Real.exp (-coulombCusp N Z x) : ℂ)*
        ((fderiv ℝ χ x (coordinateVector k) : ℂ)-(χ x : ℂ)*
          (coulombCuspGradient N Z (coordinateVector k) x : ℂ))*d k x+
      (Real.exp (-coulombCusp N Z x) : ℂ)*
        ((fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector k)) x (coordinateVector k) : ℂ)-
        (fderiv ℝ χ x (coordinateVector k) : ℂ)*(coulombCuspGradient N Z (coordinateVector k) x : ℂ)-
        (fderiv ℝ χ x (coordinateVector k) : ℂ)*(coulombCuspGradient N Z (coordinateVector k) x : ℂ)+
        (χ x : ℂ)*((coulombCuspGradient N Z (coordinateVector k) x : ℂ)*
          (coulombCuspGradient N Z (coordinateVector k) x : ℂ)-
          (coulombCuspHessian N Z (coordinateVector k) (coordinateVector k) x : ℂ)))*f x) := by
    rw [hbx k]
    simp only [localizedCusp,localizedCuspGradient,localizedCuspHessian,Complex.real_smul,
      Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add]
    ring
  have hcancel := finite_cusp_cancellation (χ x : ℂ) (Real.exp (-coulombCusp N Z x) : ℂ)
    (f x) (coulombPotential N Z x : ℂ) (E : ℂ)
    (fun k => (fderiv ℝ χ x (coordinateVector k) : ℂ))
    (fun k => (fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector k)) x (coordinateVector k) : ℂ))
    (fun k => (coulombCuspGradient N Z (coordinateVector k) x : ℂ))
    (fun k => (coulombCuspHessian N Z (coordinateVector k) (coordinateVector k) x : ℂ))
    (fun k => d k x) (fun k => e k k x) (fun k => a k x) (fun k => b k k x)
    heq hh hA hB
  rw [hgv]
  simp only [localizedCusp,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_add,
    Complex.ofReal_sum,Complex.ofReal_pow,Complex.ofReal_ofNat,realTestLaplacian]
  convert hcancel using 1 <;> ring

#print axioms scalar_coulomb_localized_transformed_equation
end TheoremT.Continuum
