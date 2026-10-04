import ManyBody.S8.Internal.PhysicalCollisionDerivativeScaling
import ManyBody.S8.Internal.PhysicalAnnularAnalyticApplicability
import ManyBody.S8.CoulombSpinPhysicalOriginalNormAnalyticDerivative
/-! Genuine original unscaled physical mixed-coordinate derivative budgets.
The existing complex multiindex bounds are transported through the actual
physical Euclidean coordinate map, then through the proved inverse scale.
The public graph consumers discharge the data and original-value premises.
-/
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

def PhysicalOriginalCollisionDerivativeAtBudget
    (f : Space (Fin 3) → ℂ) (t0 : Position) (ε : ℝ) (u0 : ℂ)
    (m M A Csrc CH12 : ℝ) (ψ : SpinSpace 2) (p : Position × Position) : Prop :=
  ∀ α β : Fin 3 → ℕ,
    let n := ∑ i : Fin 3 ⊕ Fin 3, Sum.elim α β i
    ‖physicalMultiindexDeriv (physicalRescaledCollisionA ε u0 (physicalDescentAReal f t0))
      (Sum.elim α β) p‖ ≤
      ((if n=0 then m else 0)+ε*(ε⁻¹)^n*
        physicalKSDescentDerivativeBudget M A Csrc CH12 α β)*‖ψ‖ ∧
    ‖physicalMultiindexDeriv (physicalRescaledCollisionB ε (physicalDescentBReal f t0))
      (Sum.elim α β) p‖ ≤
      ((ε⁻¹)^n*(32*(7*physicalKSPointwiseRate M A)^2)*
        physicalKSDescentDerivativeBudget M A Csrc CH12 α β)*‖ψ‖

theorem physical_original_collision_derivative_at_budget
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ} {t0 : Position}
    {ε m M A Csrc CH12 : ℝ} {u0 : ℂ} {ψ : SpinSpace 2}
    (hε : 0<ε) (hA : 1≤A)
    (hdata : PhysicalKSBoxOriginalNormAnalyticDerivativeData f v t0 M A Csrc CH12 ψ)
    (hu0 : ‖u0‖ ≤ m*‖ψ‖) (p : Position × Position)
    (hX : (32*(7*physicalKSPointwiseRate M A)^2)*‖(ε⁻¹ • p).1‖ ≤ 1/4)
    (hT : (7*physicalKSPointwiseRate M A)*‖(ε⁻¹ • p).2-t0‖ ≤ 1/4) :
    PhysicalOriginalCollisionDerivativeAtBudget f t0 ε u0 m M A Csrc CH12 ψ p := by
  let q : Position × Position := ε⁻¹ • p
  let D : ℝ := 32*(7*physicalKSPointwiseRate M A)^2
  let S : ℝ := 7*physicalKSPointwiseRate M A
  have hS : 0<S := mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hD : 0<D := by dsimp [D]; positivity
  have hXc : D*‖fun i : Fin 3 => physicalComplexCoordinatesAt t0 q (.inl i)‖ ≤ 1/4 :=
    (mul_le_mul_of_nonneg_left (physicalComplexCoordinatesCLM_left_norm_le (q.1,q.2-t0)) hD.le).trans hX
  have hTc : S*‖fun i : Fin 3 => physicalComplexCoordinatesAt t0 q (.inr i)‖ ≤ 1/4 :=
    (mul_le_mul_of_nonneg_left (physicalComplexCoordinatesCLM_right_norm_le (q.1,q.2-t0)) hS.le).trans hT
  have hmem : D*‖fun i : Fin 3 => physicalComplexCoordinatesAt t0 q (.inl i)‖ < 1 ∧
      S*‖fun i : Fin 3 => physicalComplexCoordinatesAt t0 q (.inr i)‖ < 1 :=
    ⟨lt_of_le_of_lt hXc (by norm_num),lt_of_le_of_lt hTc (by norm_num)⟩
  have ha : AnalyticAt ℂ (physicalKSAnalyticDescentA f t0) (physicalComplexCoordinatesAt t0 q) :=
    hdata.1.1.2.1 _ hmem
  have hb : AnalyticAt ℂ (physicalKSAnalyticDescentB f t0) (physicalComplexCoordinatesAt t0 q) :=
    hdata.1.1.2.2.1 _ hmem
  have haReal : AnalyticAt ℝ (physicalDescentAReal f t0) q :=
    AnalyticAt.comp (f := physicalComplexCoordinatesAt t0) (g := physicalKSAnalyticDescentA f t0)
      (ha.restrictScalars (𝕜 := ℝ)) (physicalComplexCoordinatesAt_analytic t0 q)
  intro α β
  let n : ℕ := ∑ i : Fin 3 ⊕ Fin 3, Sum.elim α β i
  let B : ℝ := physicalKSDescentDerivativeBudget M A Csrc CH12 α β
  have hBA : ‖physicalMultiindexDeriv (physicalDescentAReal f t0) (Sum.elim α β) q‖ ≤ B*‖ψ‖ := by
    change ‖physicalMultiindexDeriv (physicalKSAnalyticDescentA f t0 ∘ physicalComplexCoordinatesAt t0)
      (Sum.elim α β) q‖ ≤ B*‖ψ‖
    rw [physical_multiindex_centered_complex_restriction t0 ha]
    exact (hdata.2.1 _ hXc hTc α β).1
  have hBB : ‖physicalMultiindexDeriv (physicalDescentBReal f t0) (Sum.elim α β) q‖ ≤ D*B*‖ψ‖ := by
    change ‖physicalMultiindexDeriv (physicalKSAnalyticDescentB f t0 ∘ physicalComplexCoordinatesAt t0)
      (Sum.elim α β) q‖ ≤ D*B*‖ψ‖
    rw [physical_multiindex_centered_complex_restriction t0 hb]
    exact (hdata.2.1 _ hXc hTc α β).2
  have hcoeff : 0≤ε*(ε⁻¹)^n := mul_nonneg hε.le (pow_nonneg (inv_nonneg.mpr hε.le) n)
  have hconst : ‖if n=0 then u0 else 0‖ ≤ (if n=0 then m else 0)*‖ψ‖ := by
    split_ifs
    · exact hu0
    · simp
  constructor
  · rw [physical_multiindex_rescaled_collision_A _ _ hε p _ haReal]
    calc
      _ ≤ ‖if n=0 then u0 else 0‖+
          ‖(ε*(ε⁻¹)^n) • physicalMultiindexDeriv (physicalDescentAReal f t0) (Sum.elim α β) q‖ :=
        norm_add_le _ _
      _ = ‖if n=0 then u0 else 0‖+
          (ε*(ε⁻¹)^n)*‖physicalMultiindexDeriv (physicalDescentAReal f t0) (Sum.elim α β) q‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hcoeff]
      _ ≤ (if n=0 then m else 0)*‖ψ‖+(ε*(ε⁻¹)^n)*(B*‖ψ‖) :=
        add_le_add hconst (mul_le_mul_of_nonneg_left hBA hcoeff)
      _ = ((if n=0 then m else 0)+ε*(ε⁻¹)^n*B)*‖ψ‖ := by ring
  · rw [physical_multiindex_rescaled_collision_B _ hε p _,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hε.le) n)]
    calc
      _ ≤ (ε⁻¹)^n*(D*B*‖ψ‖) :=
        mul_le_mul_of_nonneg_left hBB (pow_nonneg (inv_nonneg.mpr hε.le) n)
      _ = ((ε⁻¹)^n*D*B)*‖ψ‖ := by ring

theorem exists_annular_derivative_width {M A : ℝ} (hA : 1≤A) :
    ∃ η : ℝ, 0<η ∧ η<1/16 ∧
      Real.sqrt 2*η ≤ physicalDescentPositionRadius M A ∧
      Real.sqrt 2*η ≤ physicalDescentNeighborhoodRadius M A ∧
      (32*(7*physicalKSPointwiseRate M A)^2)*(Real.sqrt 2*η) ≤ 1/4 ∧
      (7*physicalKSPointwiseRate M A)*(Real.sqrt 2*η) ≤ 1/4 := by
  obtain ⟨η0,hη0,hsmall0,hX0,hT0⟩ := exists_annular_analytic_width hA
  obtain ⟨hR,hRX⟩ := physicalDescent_radii_pos hA
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let D : ℝ := 32*(7*physicalKSPointwiseRate M A)^2
  let S : ℝ := 7*physicalKSPointwiseRate M A
  have hS : 0<S := mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hD : 0<D := by dsimp [D]; positivity
  have hDX : D*physicalDescentPositionRadius M A ≤ 1 := by
    calc
      _ ≤ D*D⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) hD.le
      _ = 1 := mul_inv_cancel₀ hD.ne'
  have hST : S*physicalDescentNeighborhoodRadius M A ≤ 1 := by
    calc
      _ ≤ S*S⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) hS.le
      _ = 1 := mul_inv_cancel₀ hS.ne'
  let η : ℝ := η0/4
  have hη : 0<η := div_pos hη0 (by norm_num)
  have hηsmall : η<1/16 := by dsimp [η]; linarith
  have hXquarter : Real.sqrt 2*η ≤ physicalDescentPositionRadius M A/4 := by dsimp [η]; linarith
  have hTquarter : Real.sqrt 2*η ≤ physicalDescentNeighborhoodRadius M A/4 := by dsimp [η]; linarith
  have hX : Real.sqrt 2*η ≤ physicalDescentPositionRadius M A := by linarith
  have hT : Real.sqrt 2*η ≤ physicalDescentNeighborhoodRadius M A := by linarith
  have hXD : D*(Real.sqrt 2*η) ≤ 1/4 :=
    (mul_le_mul_of_nonneg_left hXquarter hD.le).trans (by nlinarith)
  have hTS : S*(Real.sqrt 2*η) ≤ 1/4 :=
    (mul_le_mul_of_nonneg_left hTquarter hS.le).trans (by nlinarith)
  exact ⟨η,hη,hηsmall,hX,hT,hXD,hTS⟩

#print axioms physical_original_collision_derivative_at_budget
#print axioms exists_annular_derivative_width

def AnnularNuclearOriginalDerivativeData (g : Configuration 2 → ℂ)
    (i : Fin 2) (ρ η : ℝ) (t0 : Position) (m M A Csrc CH12 : ℝ) (ψ : SpinSpace 2) : Prop :=
  AnnularNuclearAnalyticReconstruction g i ρ η t0 ∧
  ∀ x : Configuration 2, ρ⁻¹ • x ∈ annularNuclearNeighborhood i t0 η →
    PhysicalOriginalCollisionDerivativeAtBudget
      ((originScaledDifference g ρ ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      t0 ρ (g 0) m M A Csrc CH12 ψ (position x i,position x (1-i))

def AnnularPairOriginalDerivativeData (g : Configuration 2 → ℂ)
    (ρ η : ℝ) (t0 : Position) (m M A Csrc CH12 : ℝ) (ψ : SpinSpace 2) : Prop :=
  AnnularPairAnalyticReconstruction g ρ η t0 ∧
  ∀ x : Configuration 2, ρ⁻¹ • x ∈ annularPairNeighborhood t0 η →
    PhysicalOriginalCollisionDerivativeAtBudget
      ((originScaledDifference g (ρ / Real.sqrt 2) ∘ TheoremT.Continuum.pairKSLift) ∘
        (physicalSpectatorReindexAt (0 : Fin 2)).symm)
      t0 (ρ / Real.sqrt 2) (g 0) m M A Csrc CH12 ψ
      (position x 0-position x 1,annularPairCenter x)

theorem nuclear_annular_original_derivative_data
    (g : Configuration 2 → ℂ) (i : Fin 2) {ρ η m M A Csrc CH12 : ℝ}
    {t0 : Position} {ψ : SpinSpace 2} {v : Position → Position → ℂ}
    (hρ : 0<ρ) (hA : 1≤A) (hF0 : 0≤Csrc*‖ψ‖)
    (hηX : η≤physicalDescentPositionRadius M A)
    (hηT : η≤physicalDescentNeighborhoodRadius M A)
    (hηD : (32*(7*physicalKSPointwiseRate M A)^2)*η≤1/4)
    (hηS : (7*physicalKSPointwiseRate M A)*η≤1/4)
    (hdata : PhysicalKSBoxOriginalNormAnalyticDerivativeData
      ((originScaledDifference g ρ ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      v t0 M A Csrc CH12 ψ)
    (hu0 : ‖g 0‖≤m*‖ψ‖) :
    AnnularNuclearOriginalDerivativeData g i ρ η t0 m M A Csrc CH12 ψ := by
  refine ⟨nuclear_annular_analytic_reconstruction_of_pointwise g i hρ hA hF0
    hηX hηT hdata.1.1.1,?_⟩
  intro x hx
  have hS : 0≤7*physicalKSPointwiseRate M A :=
    (mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)).le
  have hD : 0≤32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hXq : ‖(ρ⁻¹ • (position x i,position x (1-i))).1‖ < η := by
    change ‖ρ⁻¹ • position x i‖ < η
    rw [← position_smul_annular]
    exact hx.1
  have hTq : ‖(ρ⁻¹ • (position x i,position x (1-i))).2-t0‖ < η := by
    change ‖ρ⁻¹ • position x (1-i)-t0‖ < η
    rw [← position_smul_annular]
    exact hx.2
  exact physical_original_collision_derivative_at_budget hρ hA hdata hu0
    (position x i,position x (1-i))
    ((mul_le_mul_of_nonneg_left hXq.le hD).trans hηD)
    ((mul_le_mul_of_nonneg_left hTq.le hS).trans hηS)

theorem pair_annular_original_derivative_data
    (g : Configuration 2 → ℂ) {ρ η m M A Csrc CH12 : ℝ}
    {t0 : Position} {ψ : SpinSpace 2} {v : Position → Position → ℂ}
    (hρ : 0<ρ) (hA : 1≤A) (hF0 : 0≤Csrc*‖ψ‖)
    (hηX : Real.sqrt 2*η≤physicalDescentPositionRadius M A)
    (hηT : Real.sqrt 2*η≤physicalDescentNeighborhoodRadius M A)
    (hηD : (32*(7*physicalKSPointwiseRate M A)^2)*(Real.sqrt 2*η)≤1/4)
    (hηS : (7*physicalKSPointwiseRate M A)*(Real.sqrt 2*η)≤1/4)
    (hdata : PhysicalKSBoxOriginalNormAnalyticDerivativeData
      ((originScaledDifference g (ρ / Real.sqrt 2) ∘ TheoremT.Continuum.pairKSLift) ∘
        (physicalSpectatorReindexAt (0 : Fin 2)).symm) v t0 M A Csrc CH12 ψ)
    (hu0 : ‖g 0‖≤m*‖ψ‖) :
    AnnularPairOriginalDerivativeData g ρ η t0 m M A Csrc CH12 ψ := by
  refine ⟨pair_annular_analytic_reconstruction_of_pointwise g hρ hA hF0
    hηX hηT hdata.1.1.1,?_⟩
  intro x hx
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hε : 0<ρ / Real.sqrt 2 := div_pos hρ hs
  have hS : 0≤7*physicalKSPointwiseRate M A :=
    (mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)).le
  have hD : 0≤32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hscalar : (ρ / Real.sqrt 2)⁻¹=Real.sqrt 2*ρ⁻¹ := by rw [inv_div,div_eq_mul_inv]
  have hfirst : (ρ / Real.sqrt 2)⁻¹ • (position x 0-position x 1) =
      Real.sqrt 2 • (position (ρ⁻¹ • x) 0-position (ρ⁻¹ • x) 1) := by
    rw [hscalar,position_smul_annular,position_smul_annular,smul_sub,smul_sub,smul_smul,smul_smul]
  have hsecond : (ρ / Real.sqrt 2)⁻¹ • annularPairCenter x-t0 =
      Real.sqrt 2 • (annularPairCenter (ρ⁻¹ • x)-(Real.sqrt 2)⁻¹ • t0) := by
    rw [hscalar,annularPairCenter_smul,smul_sub,smul_smul,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  have hXq : ‖((ρ / Real.sqrt 2)⁻¹ •
      (position x 0-position x 1,annularPairCenter x)).1‖ < Real.sqrt 2*η := by
    change ‖(ρ / Real.sqrt 2)⁻¹ • (position x 0-position x 1)‖ < _
    rw [hfirst,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact mul_lt_mul_of_pos_left hx.1 hs
  have hTq : ‖((ρ / Real.sqrt 2)⁻¹ •
      (position x 0-position x 1,annularPairCenter x)).2-t0‖ < Real.sqrt 2*η := by
    change ‖(ρ / Real.sqrt 2)⁻¹ • annularPairCenter x-t0‖ < _
    rw [hsecond,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact mul_lt_mul_of_pos_left hx.2 hs
  exact physical_original_collision_derivative_at_budget hε hA hdata hu0
    (position x 0-position x 1,annularPairCenter x)
    ((mul_le_mul_of_nonneg_left hXq.le hD).trans hηD)
    ((mul_le_mul_of_nonneg_left hTq.le hS).trans hηS)

#print axioms nuclear_annular_original_derivative_data
#print axioms pair_annular_original_derivative_data
end ManyBody.S8
