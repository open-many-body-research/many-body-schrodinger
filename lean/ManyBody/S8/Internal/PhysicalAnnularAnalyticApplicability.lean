import ManyBody.S8.PhysicalAnalyticDescentOriginalGerms
import ManyBody.S8.Internal.TwoElectronAnnularCollisionCover
import Mathlib.Tactic
/-! Actual physical analytic reconstruction throughout the annular product
neighborhoods. Geometry uses original electron positions and the restored
coefficient-1 half-sum pair coordinates. No PDE or analytic input is inserted
in the graph consumers; the generic helper explicitly consumes actual descent.
-/
noncomputable section
open Set Filter
open scoped Topology NNReal BigOperators
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

def physicalDescentPositionRadius (M A : ℝ) : ℝ :=
  min ((physicalDescentNeighborhoodRadius M A)^2)
    (32*(7*physicalKSPointwiseRate M A)^2)⁻¹

theorem physicalDescent_radii_pos {M A : ℝ} (hA : 1≤A) :
    0 < physicalDescentNeighborhoodRadius M A ∧
    0 < physicalDescentPositionRadius M A := by
  have hS : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hR : 0 < physicalDescentNeighborhoodRadius M A := by
    unfold physicalDescentNeighborhoodRadius
    positivity
  exact ⟨hR, by unfold physicalDescentPositionRadius; positivity⟩

theorem physical_descent_literal_physical_point
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ}
    {t0 : Position} {M A F0 W : ℝ} (p : Position × Position)
    (hdata : PhysicalKSBoxAnalyticDescentData f v t0 M A F0 W) (hA : 1≤A)
    (hX : ‖p.1‖ < physicalDescentPositionRadius M A)
    (hT : ‖p.2-t0‖ < physicalDescentNeighborhoodRadius M A) :
    AnalyticAt ℝ (physicalDescentAReal f t0) p ∧
    AnalyticAt ℝ (physicalDescentBReal f t0) p ∧
    physicalDescentAReal f t0 p+‖p.1‖ • physicalDescentBReal f t0 p = v p.1 p.2 := by
  have hS : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hD : 0 < 32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hXs : (32*(7*physicalKSPointwiseRate M A)^2)*‖p.1‖ < 1 := by
    have hh := mul_lt_mul_of_pos_left (hX.trans_le (min_le_right _ _)) hD
    simpa only [mul_inv_cancel₀ hD.ne'] using hh
  have hTs : (7*physicalKSPointwiseRate M A)*‖p.2-t0‖ < 1 := by
    have hh := mul_lt_mul_of_pos_left (hT.trans_le (min_le_right _ _)) hS
    simpa only [mul_inv_cancel₀ hS.ne'] using hh
  have hz : physicalComplexCoordinatesAt t0 p ∈
      {z : Fin 3 ⊕ Fin 3 → ℂ |
        (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖<1 ∧
        (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖<1} := by
    exact ⟨(mul_le_mul_of_nonneg_left
      (physicalComplexCoordinatesCLM_left_norm_le (p.1,p.2-t0)) hD.le).trans_lt hXs,
      (mul_le_mul_of_nonneg_left
      (physicalComplexCoordinatesCLM_right_norm_le (p.1,p.2-t0)) hS.le).trans_lt hTs⟩
  have ha : AnalyticAt ℝ (physicalDescentAReal f t0) p :=
    AnalyticAt.comp (f := physicalComplexCoordinatesAt t0) (g := physicalKSAnalyticDescentA f t0)
      ((hdata.2.1 _ hz).restrictScalars (𝕜 := ℝ)) (physicalComplexCoordinatesAt_analytic t0 p)
  have hb : AnalyticAt ℝ (physicalDescentBReal f t0) p :=
    AnalyticAt.comp (f := physicalComplexCoordinatesAt t0) (g := physicalKSAnalyticDescentB f t0)
      ((hdata.2.2.1 _ hz).restrictScalars (𝕜 := ℝ)) (physicalComplexCoordinatesAt_analytic t0 p)
  refine ⟨ha,hb,?_⟩
  obtain ⟨r,hr,he,hidentity⟩ := hdata.2.2.2
  have hXr : ‖p.1‖ < min ((r:ℝ)^2) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹ := by
    rw [he]
    exact hX
  have hTr : ‖p.2-t0‖ < (r:ℝ) := by rw [he]; exact hT
  have hh := hidentity p.1 (p.2-t0) hXr hTr
  rw [add_sub_cancel] at hh
  have hcoords : physicalComplexCoordinatesAt t0 p =
      Sum.elim (fun i => (p.1 i:ℂ)) (fun i => ((p.2-t0) i:ℂ)) := rfl
  rw [← hcoords] at hh
  simpa only [physicalDescentAReal,physicalDescentBReal,Complex.real_smul] using hh.symm

theorem physical_descent_unscaled_physical_point
    (g : Configuration 2 → ℂ) (C : (Position × Position) →L[ℝ] Configuration 2)
    {f : Space (Fin 3) → ℂ} {ε M A F0 W : ℝ} {t0 : Position}
    (p : Position × Position) (hε : 0<ε) (hA : 1≤A)
    (hdata : PhysicalKSBoxAnalyticDescentData f
      (fun X T => originScaledDifference g ε (C (X,T))) t0 M A F0 W)
    (hX : ‖(ε⁻¹ • p).1‖ < physicalDescentPositionRadius M A)
    (hT : ‖(ε⁻¹ • p).2-t0‖ < physicalDescentNeighborhoodRadius M A) :
    AnalyticAt ℝ (physicalRescaledCollisionA ε (g 0) (physicalDescentAReal f t0)) p ∧
    AnalyticAt ℝ (physicalRescaledCollisionB ε (physicalDescentBReal f t0)) p ∧
    physicalRescaledCollisionA ε (g 0) (physicalDescentAReal f t0) p+
      ‖p.1‖ • physicalRescaledCollisionB ε (physicalDescentBReal f t0) p = g (C p) := by
  obtain ⟨ha,hb,heq⟩ := physical_descent_literal_physical_point (ε⁻¹ • p) hdata hA hX hT
  have hs : AnalyticAt ℝ (fun q : Position × Position => ε⁻¹ • q) p :=
    by
      have hcst : AnalyticAt ℝ (fun _ : Position × Position => ε⁻¹) p := analyticAt_const
      exact hcst.smul analyticAt_id
  have ha' : AnalyticAt ℝ (fun q : Position × Position => physicalDescentAReal f t0 (ε⁻¹ • q)) p :=
    AnalyticAt.comp (f := fun q : Position × Position => ε⁻¹ • q)
      (g := physicalDescentAReal f t0) ha hs
  have hb' : AnalyticAt ℝ (fun q : Position × Position => physicalDescentBReal f t0 (ε⁻¹ • q)) p :=
    AnalyticAt.comp (f := fun q : Position × Position => ε⁻¹ • q)
      (g := physicalDescentBReal f t0) hb hs
  refine ⟨analyticAt_const.add (analyticAt_const.mul ha'),hb',?_⟩
  have hh := originScaledDifference_comp_physical_coordinates g C ε (ε⁻¹ • p)
  have hcancel : ε • (ε⁻¹ • p)=p := by simp [smul_smul,hε.ne']
  have hnorm : ‖(ε⁻¹ • p).1‖=ε⁻¹*‖p.1‖ := by
    change ‖ε⁻¹ • p.1‖=ε⁻¹*‖p.1‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hε)]
  change physicalDescentAReal f t0 (ε⁻¹ • p)+
    ‖(ε⁻¹ • p).1‖ • physicalDescentBReal f t0 (ε⁻¹ • p) =
    originScaledDifference g ε (C (ε⁻¹ • p)) at heq
  rw [hh,hcancel,map_zero,hnorm,Complex.real_smul] at heq
  have hc : (ε:ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  change g 0+(ε:ℂ)*physicalDescentAReal f t0 (ε⁻¹ • p)+
    (‖p.1‖:ℂ)*physicalDescentBReal f t0 (ε⁻¹ • p)=g (C p)
  have he := (eq_div_iff hc).mp heq
  push_cast at he
  field_simp [hc] at he
  simp only [one_div] at he
  linear_combination he

theorem position_smul_annular (a : ℝ) (x : Configuration 2) (i : Fin 2) :
    position (a • x) i = a • position x i := by
  ext k
  rfl

theorem originalNuclearPhysicalCoordinatesCLM_reconstruct (i : Fin 2) (x : Configuration 2) :
    originalNuclearPhysicalCoordinatesCLM i (position x i,position x (1-i)) = x := by
  rw [originalNuclearPhysicalCoordinatesCLM_apply]
  apply (configurationProductEquiv i).injective
  rw [(configurationProductEquiv i).apply_symm_apply]
  apply Prod.ext
  · rfl
  · ext k
    rw [twoElectronSpectatorPositionEquiv_symm_apply]
    rcases k with ⟨⟨j,l⟩,hj⟩
    change x (1-i,l) = x (j,l)
    fin_cases i <;> fin_cases j
    · exact False.elim (hj rfl)
    · rfl
    · rfl
    · exact False.elim (hj rfl)

theorem originalPairPhysicalCoordinatesCLM_reconstruct (x : Configuration 2) :
    originalPairPhysicalCoordinatesCLM (position x 0-position x 1,annularPairCenter x) = x := by
  have h0 : position (originalPairPhysicalCoordinatesCLM
      (position x 0-position x 1,annularPairCenter x)) 0 = position x 0 := by
    rw [originalPairPhysicalCoordinatesCLM_apply,TheoremT.Continuum.pairCoordinates_first,
      pairCenterEquiv.apply_symm_apply]
    dsimp [annularPairCenter]
    module
  have h1 : position (originalPairPhysicalCoordinatesCLM
      (position x 0-position x 1,annularPairCenter x)) 1 = position x 1 := by
    rw [originalPairPhysicalCoordinatesCLM_apply,TheoremT.Continuum.pairCoordinates_second,
      pairCenterEquiv.apply_symm_apply]
    dsimp [annularPairCenter]
    module
  ext ⟨i,k⟩
  fin_cases i
  · exact congrArg (fun z : Position => z k) h0
  · exact congrArg (fun z : Position => z k) h1

theorem annularPairCenter_smul (a : ℝ) (x : Configuration 2) :
    annularPairCenter (a • x) = a • annularPairCenter x := by
  simp only [annularPairCenter,position_smul_annular,smul_add,smul_smul]
  module

#print axioms physicalDescent_radii_pos
#print axioms physical_descent_literal_physical_point
#print axioms physical_descent_unscaled_physical_point
#print axioms originalNuclearPhysicalCoordinatesCLM_reconstruct
#print axioms originalPairPhysicalCoordinatesCLM_reconstruct

def AnnularNuclearAnalyticReconstruction (g : Configuration 2 → ℂ)
    (i : Fin 2) (ρ η : ℝ) (t0 : Position) : Prop :=
  ∀ x : Configuration 2, ρ⁻¹ • x ∈ annularNuclearNeighborhood i t0 η →
    let f := ((originScaledDifference g ρ ∘ nuclearKSLift i) ∘
      (physicalSpectatorReindexAt i).symm)
    let p := (position x i,position x (1-i))
    AnalyticAt ℝ (physicalRescaledCollisionA ρ (g 0) (physicalDescentAReal f t0)) p ∧
    AnalyticAt ℝ (physicalRescaledCollisionB ρ (physicalDescentBReal f t0)) p ∧
    physicalRescaledCollisionA ρ (g 0) (physicalDescentAReal f t0) p+
      ‖p.1‖ • physicalRescaledCollisionB ρ (physicalDescentBReal f t0) p = g x

def AnnularPairAnalyticReconstruction (g : Configuration 2 → ℂ)
    (ρ η : ℝ) (t0 : Position) : Prop :=
  ∀ x : Configuration 2, ρ⁻¹ • x ∈ annularPairNeighborhood t0 η →
    let ε := ρ / Real.sqrt 2
    let f := ((originScaledDifference g ε ∘ TheoremT.Continuum.pairKSLift) ∘
      (physicalSpectatorReindexAt (0 : Fin 2)).symm)
    let p := (position x 0-position x 1,annularPairCenter x)
    AnalyticAt ℝ (physicalRescaledCollisionA ε (g 0) (physicalDescentAReal f t0)) p ∧
    AnalyticAt ℝ (physicalRescaledCollisionB ε (physicalDescentBReal f t0)) p ∧
    physicalRescaledCollisionA ε (g 0) (physicalDescentAReal f t0) p+
      ‖p.1‖ • physicalRescaledCollisionB ε (physicalDescentBReal f t0) p = g x

theorem nuclear_annular_analytic_reconstruction_of_pointwise
    (g : Configuration 2 → ℂ) (i : Fin 2) {ρ η M A F0 W : ℝ} {t0 : Position}
    (hρ : 0<ρ) (hA : 1≤A) (hF0 : 0≤F0)
    (hηX : η ≤ physicalDescentPositionRadius M A)
    (hηT : η ≤ physicalDescentNeighborhoodRadius M A)
    (hdata : PhysicalKSBoxPointwiseData
      ((originScaledDifference g ρ ∘ nuclearKSLift i) ∘
        (physicalSpectatorReindexAt i).symm) t0 M A F0 W) :
    AnnularNuclearAnalyticReconstruction g i ρ η t0 := by
  intro x hx
  have hX : ‖(ρ⁻¹ • (position x i,position x (1-i))).1‖ < physicalDescentPositionRadius M A := by
    change ‖ρ⁻¹ • position x i‖ < physicalDescentPositionRadius M A
    rw [← position_smul_annular]
    exact hx.1.trans_le hηX
  have hT : ‖(ρ⁻¹ • (position x i,position x (1-i))).2-t0‖ < physicalDescentNeighborhoodRadius M A := by
    change ‖ρ⁻¹ • position x (1-i)-t0‖ < physicalDescentNeighborhoodRadius M A
    rw [← position_smul_annular]
    exact hx.2.trans_le hηT
  have hd := nuclearKSPhysicalAnalyticDescent_data (originScaledDifference g ρ) i hdata hA hF0
  have hh := physical_descent_unscaled_physical_point g (originalNuclearPhysicalCoordinatesCLM i)
    (position x i,position x (1-i)) hρ hA hd hX hT
  rw [originalNuclearPhysicalCoordinatesCLM_reconstruct] at hh
  exact hh

theorem pair_annular_analytic_reconstruction_of_pointwise
    (g : Configuration 2 → ℂ) {ρ η M A F0 W : ℝ} {t0 : Position}
    (hρ : 0<ρ) (hA : 1≤A) (hF0 : 0≤F0)
    (hηX : Real.sqrt 2*η ≤ physicalDescentPositionRadius M A)
    (hηT : Real.sqrt 2*η ≤ physicalDescentNeighborhoodRadius M A)
    (hdata : PhysicalKSBoxPointwiseData
      ((originScaledDifference g (ρ / Real.sqrt 2) ∘ TheoremT.Continuum.pairKSLift) ∘
        (physicalSpectatorReindexAt (0 : Fin 2)).symm) t0 M A F0 W) :
    AnnularPairAnalyticReconstruction g ρ η t0 := by
  intro x hx
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hε : 0<ρ / Real.sqrt 2 := div_pos hρ hs
  have hscalar : (ρ / Real.sqrt 2)⁻¹=Real.sqrt 2*ρ⁻¹ := by rw [inv_div,div_eq_mul_inv]
  have hfirst : (ρ / Real.sqrt 2)⁻¹ • (position x 0-position x 1) =
      Real.sqrt 2 • (position (ρ⁻¹ • x) 0-position (ρ⁻¹ • x) 1) := by
    rw [hscalar,position_smul_annular,position_smul_annular,smul_sub,smul_sub,
      smul_smul,smul_smul]
  have hsecond : (ρ / Real.sqrt 2)⁻¹ • annularPairCenter x-t0 =
      Real.sqrt 2 • (annularPairCenter (ρ⁻¹ • x)-(Real.sqrt 2)⁻¹ • t0) := by
    rw [hscalar,annularPairCenter_smul,smul_sub,smul_smul,smul_smul,
      mul_inv_cancel₀ hs.ne',one_smul]
  have hX : ‖((ρ / Real.sqrt 2)⁻¹ •
      (position x 0-position x 1,annularPairCenter x)).1‖ < physicalDescentPositionRadius M A := by
    change ‖(ρ / Real.sqrt 2)⁻¹ • (position x 0-position x 1)‖ < _
    rw [hfirst,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact (mul_lt_mul_of_pos_left hx.1 hs).trans_le hηX
  have hT : ‖((ρ / Real.sqrt 2)⁻¹ •
      (position x 0-position x 1,annularPairCenter x)).2-t0‖ < physicalDescentNeighborhoodRadius M A := by
    change ‖(ρ / Real.sqrt 2)⁻¹ • annularPairCenter x-t0‖ < _
    rw [hsecond,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact (mul_lt_mul_of_pos_left hx.2 hs).trans_le hηT
  have hd := pairKSPhysicalAnalyticDescent_data (originScaledDifference g (ρ / Real.sqrt 2)) hdata hA hF0
  have hh := physical_descent_unscaled_physical_point g originalPairPhysicalCoordinatesCLM
    (position x 0-position x 1,annularPairCenter x) hε hA hd hX hT
  rw [originalPairPhysicalCoordinatesCLM_reconstruct] at hh
  exact hh

theorem exists_annular_analytic_width {M A : ℝ} (hA : 1≤A) :
    ∃ η : ℝ, 0<η ∧ η<1/16 ∧
      Real.sqrt 2*η ≤ physicalDescentPositionRadius M A ∧
      Real.sqrt 2*η ≤ physicalDescentNeighborhoodRadius M A := by
  obtain ⟨hR,hX⟩ := physicalDescent_radii_pos hA
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let η : ℝ := min (1/32) (min (physicalDescentPositionRadius M A)
    (physicalDescentNeighborhoodRadius M A) / Real.sqrt 2)
  have hη : 0<η := by dsimp [η]; positivity
  have hsmall : η<1/16 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hscale : Real.sqrt 2*η ≤ min (physicalDescentPositionRadius M A)
      (physicalDescentNeighborhoodRadius M A) := by
    have hh := mul_le_mul_of_nonneg_left (show η ≤ _ from min_le_right _ _) hs.le
    calc
      _ ≤ Real.sqrt 2*(min (physicalDescentPositionRadius M A)
        (physicalDescentNeighborhoodRadius M A) / Real.sqrt 2) := hh
      _ = _ := by field_simp
  exact ⟨η,hη,hsmall,hscale.trans (min_le_left _ _),hscale.trans (min_le_right _ _)⟩

#print axioms nuclear_annular_analytic_reconstruction_of_pointwise
#print axioms pair_annular_analytic_reconstruction_of_pointwise
#print axioms exists_annular_analytic_width
end ManyBody.S8
