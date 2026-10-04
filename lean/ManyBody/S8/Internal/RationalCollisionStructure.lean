import ManyBody.S8.Internal.RationalDistanceParity
import ManyBody.S8.Internal.CoordinateProductDerivativeBounds
/-! Rational approximants preserving the actual selected collision structure.

A literal rational reflection average makes the two coefficient polynomials
even without weakening their actual C2 errors. A genuine coordinate-product
derivative bound controls their ONE reconstruction PA+q_j PB. This same
reconstructing polynomial has a proved finite rational monomial dictionary.
The analytic, parity and approximation inputs here are discharged by the
physical public consumer from the original graph-derived profiles. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators ContDiff
namespace ManyBody.S8

def rationalDistanceMvPolynomial (s : Finset DistanceMultiIndex)
    (r : DistanceMultiIndex → ℚ) : MvPolynomial (Fin 3) ℚ :=
  ∑ α∈s, MvPolynomial.C (r α)*∏ j, (MvPolynomial.X j)^(α j)

theorem rationalDistanceMvPolynomial_eval (s : Finset DistanceMultiIndex)
    (r : DistanceMultiIndex → ℚ) (p : Fin 3 → ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) p (rationalDistanceMvPolynomial s r)=
      realDistancePolynomial s (fun α => (r α:ℝ)) p := by
  simp [rationalDistanceMvPolynomial,realDistancePolynomial,realDistanceMonomial,smul_eq_mul]

theorem rational_mvPolynomial_finite_distance_dictionary (P : MvPolynomial (Fin 3) ℚ) :
    ∃ s : Finset DistanceMultiIndex, ∃ r : DistanceMultiIndex → ℚ,
      ∀ p, MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) p P=
        realDistancePolynomial s (fun α => (r α:ℝ)) p := by
  classical
  let e : (Fin 3 →₀ ℕ) ≃ DistanceMultiIndex := Finsupp.equivFunOnFinite
  refine ⟨P.support.image e,fun α => P.coeff (e.symm α),?_⟩
  intro p
  rw [MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq']
  unfold realDistancePolynomial
  rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [e.symm_apply_apply,smul_eq_mul,realDistanceMonomial]
  rfl

theorem rational_collision_polynomial_finite_dictionary
    (j : Fin 3) (sA sB : Finset DistanceMultiIndex) (rA rB : DistanceMultiIndex → ℚ) :
    ∃ s : Finset DistanceMultiIndex, ∃ r : DistanceMultiIndex → ℚ,
      (fun p : Fin 3 → ℝ => realDistancePolynomial sA (fun α => (rA α:ℝ)) p+
        p j*realDistancePolynomial sB (fun α => (rB α:ℝ)) p)=
      realDistancePolynomial s (fun α => (r α:ℝ)) := by
  obtain ⟨s,r,hr⟩ := rational_mvPolynomial_finite_distance_dictionary
    (rationalDistanceMvPolynomial sA rA+MvPolynomial.X j*rationalDistanceMvPolynomial sB rB)
  refine ⟨s,r,funext fun p => ?_⟩
  rw [←hr p]
  simp only [map_add,map_mul,MvPolynomial.eval₂Hom_X',rationalDistanceMvPolynomial_eval]


def RationalCollisionStructureC2Data (A B H : (Fin 3 → ℝ) → ℝ) (j : Fin 3)
    (a : Fin 3 → ℝ) (b : ℝ) : Prop :=
  ∀ ζ : ℝ, 0<ζ →
    ∃ sA : Finset DistanceMultiIndex, ∃ rA : DistanceMultiIndex → ℚ,
    ∃ sB : Finset DistanceMultiIndex, ∃ rB : DistanceMultiIndex → ℚ,
      let PA := realDistancePolynomial sA (fun α => (rA α:ℝ))
      let PB := realDistancePolynomial sB (fun α => (rB α:ℝ))
      let PH := fun q : Fin 3 → ℝ => PA q+q j*PB q
      (∀ p, PA (realDistanceReflectCLM j p)=PA p) ∧
      (∀ p, PB (realDistanceReflectCLM j p)=PB p) ∧
      (∃ sH : Finset DistanceMultiIndex, ∃ rH : DistanceMultiIndex → ℚ,
        PH=realDistancePolynomial sH (fun α => (rH α:ℝ))) ∧
      ∀ p : Fin 3 → ℝ, ‖p-a‖≤b → ∀ k : Fin 3,
        ‖iteratedFDeriv ℝ (k:ℕ) A p-iteratedFDeriv ℝ (k:ℕ) PA p‖<ζ ∧
        ‖iteratedFDeriv ℝ (k:ℕ) B p-iteratedFDeriv ℝ (k:ℕ) PB p‖<ζ ∧
        ‖iteratedFDeriv ℝ (k:ℕ) H p-iteratedFDeriv ℝ (k:ℕ) PH p‖<ζ

theorem rational_collision_structure_C2
    {A B H : (Fin 3 → ℝ) → ℝ} (j : Fin 3) {a : Fin 3 → ℝ} {b : ℝ}
    (hb : 0≤b) (ha : a j=0)
    (hA : ∀ p : Fin 3 → ℝ, ‖p-a‖≤b → AnalyticAt ℝ A p)
    (hB : ∀ p : Fin 3 → ℝ, ‖p-a‖≤b → AnalyticAt ℝ B p)
    (heA : ∀ p, A (realDistanceReflectCLM j p)=A p)
    (heB : ∀ p, B (realDistanceReflectCLM j p)=B p)
    (hH : H=fun q => A q+q j*B q)
    (happroxA : ∀ η : ℝ, 0<η →
      ∃ s : Finset DistanceMultiIndex, ∃ r : DistanceMultiIndex → ℚ,
        ∀ p : Fin 3 → ℝ, ‖p-a‖≤b → ∀ k : Fin 3,
          ‖iteratedFDeriv ℝ (k:ℕ) A p-
            iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s (fun α => (r α:ℝ))) p‖<η)
    (happroxB : ∀ η : ℝ, 0<η →
      ∃ s : Finset DistanceMultiIndex, ∃ r : DistanceMultiIndex → ℚ,
        ∀ p : Fin 3 → ℝ, ‖p-a‖≤b → ∀ k : Fin 3,
          ‖iteratedFDeriv ℝ (k:ℕ) B p-
            iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s (fun α => (r α:ℝ))) p‖<η) :
    RationalCollisionStructureC2Data A B H j a b := by
  intro ζ hζ
  let η := ζ/(2*(5+4*b))
  have hη : 0<η := by dsimp [η]; positivity
  have hηζ : η<ζ := by
    dsimp [η]
    apply (div_lt_iff₀ (by positivity : 0<2*(5+4*b))).mpr
    nlinarith [mul_nonneg hb hζ.le]
  obtain ⟨sA,rA,hrA⟩ := happroxA η hη
  obtain ⟨sB,rB,hrB⟩ := happroxB η hη
  obtain ⟨hePA,hPA⟩ := rational_even_distance_polynomial_uniform_C2 j ha hA heA sA rA hrA
  obtain ⟨hePB,hPB⟩ := rational_even_distance_polynomial_uniform_C2 j ha hB heB sB rB hrB
  let cA := reflectedRationalDistanceCoefficients j rA
  let cB := reflectedRationalDistanceCoefficients j rB
  let PA := realDistancePolynomial sA (fun α => (cA α:ℝ))
  let PB := realDistancePolynomial sB (fun α => (cB α:ℝ))
  refine ⟨sA,cA,sB,cB,hePA,hePB,
    rational_collision_polynomial_finite_dictionary j sA sB cA cB,?_⟩
  intro p hp k
  have hPAp : ContDiffAt ℝ 2 PA p := (realDistancePolynomial_contDiff sA _).contDiffAt.of_le (by simp)
  have hPBp : ContDiffAt ℝ 2 PB p := (realDistancePolynomial_contDiff sB _).contDiffAt.of_le (by simp)
  have hAp : ContDiffAt ℝ 2 A p := (hA p hp).contDiffAt
  have hBp : ContDiffAt ℝ 2 B p := (hB p hp).contDiffAt
  have hcoord : ContDiffAt ℝ 2 (fun q : Fin 3 → ℝ => q j) p :=
    (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt
  have hk : (k:ℕ∞ω)≤2 := by exact_mod_cast (show (k:ℕ)≤2 by omega)
  have hV : ContDiffAt ℝ 2 (fun q => B q-PB q) p := hBp.sub hPBp
  have hVbound (i : ℕ) (hi : i≤2) :
      ‖iteratedFDeriv ℝ i (fun q => B q-PB q) p‖≤η := by
    change ‖iteratedFDeriv ℝ i (B-PB) p‖≤η
    rw [iteratedFDeriv_sub_apply (f:=B) (g:=PB) (hBp.of_le (by exact_mod_cast hi)) (hPBp.of_le (by exact_mod_cast hi))]
    exact (hPB p hp ⟨i,by omega⟩).le
  have hprod := real_coordinate_product_C2_bound j hη.le hV hVbound k
  have hpj : |p j|≤b := by
    calc _=‖(p-a) j‖ := by simp [Pi.sub_apply,ha,Real.norm_eq_abs]
         _≤‖p-a‖ := norm_le_pi_norm _ _
         _≤b := hp
  have hprod' : ‖iteratedFDeriv ℝ (k:ℕ) (fun q => q j*(B q-PB q)) p‖≤4*(1+b)*η :=
    hprod.trans (mul_le_mul_of_nonneg_right (by linarith : 4*(1+|p j|)≤4*(1+b)) hη.le)
  refine ⟨(hPA p hp k).trans hηζ,(hPB p hp k).trans hηζ,?_⟩
  rw [hH]
  have hdiff :
      iteratedFDeriv ℝ (k:ℕ) (fun q => A q+q j*B q) p-
        iteratedFDeriv ℝ (k:ℕ) (fun q => PA q+q j*PB q) p=
      iteratedFDeriv ℝ (k:ℕ) (fun q => (A q-PA q)+q j*(B q-PB q)) p := by
    rw [←iteratedFDeriv_sub_apply ((hAp.add (hcoord.mul hBp)).of_le hk)
      ((hPAp.add (hcoord.mul hPBp)).of_le hk)]
    congr 1
    funext q
    simp only [Pi.sub_apply]
    ring
  rw [hdiff]
  change ‖iteratedFDeriv ℝ (k:ℕ) ((A-PA)+(fun q => q j*(B q-PB q))) p‖<ζ
  rw [iteratedFDeriv_add_apply (f:=A-PA) (g:=fun q => q j*(B q-PB q))
      ((hAp.sub hPAp).of_le hk) ((hcoord.mul hV).of_le hk),
    iteratedFDeriv_sub_apply (f:=A) (g:=PA) (hAp.of_le hk) (hPAp.of_le hk)]
  calc
    _≤‖iteratedFDeriv ℝ (k:ℕ) A p-iteratedFDeriv ℝ (k:ℕ) PA p‖+
      ‖iteratedFDeriv ℝ (k:ℕ) (fun q => q j*(B q-PB q)) p‖ := norm_add_le _ _
    _<η+4*(1+b)*η := add_lt_add_of_lt_of_le (hPA p hp k) hprod'
    _=ζ/2 := by dsimp [η]; field_simp; ring
    _<ζ := by linarith

#print axioms rational_collision_polynomial_finite_dictionary
#print axioms rational_collision_structure_C2
end ManyBody.S8
