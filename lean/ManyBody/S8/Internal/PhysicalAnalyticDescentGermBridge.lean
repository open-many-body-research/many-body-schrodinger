import ManyBody.S8.Internal.AnalyticDistanceGermUniqueness
import ManyBody.S8.Internal.PhysicalComplexCoordinates
import PhysicalKSBoxAnalyticDescentData_v1
/-! The literal recovered complex descent has a true real physical germ.

The actual Euclidean coordinate embedding sends (X,T) to the selected
complex coordinate values (X,T-t0). Joint complex analyticity restricts to
real analyticity. The proved KS-surjective physical neighborhood identity
holds near every selected collision point inside the advertised spectator
radius. This supporting bridge supplies no physical data as a new axiom.
-/
noncomputable section
open Set Filter
open scoped Topology BigOperators NNReal
namespace ManyBody.S8
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

def physicalDescentNeighborhoodRadius (M A : ℝ) : ℝ :=
  min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹

def physicalDescentAReal (f : Space (Fin 3) → ℂ) (t0 : Position)
    (p : Position × Position) : ℂ :=
  physicalKSAnalyticDescentA f t0 (physicalComplexCoordinatesAt t0 p)

def physicalDescentBReal (f : Space (Fin 3) → ℂ) (t0 : Position)
    (p : Position × Position) : ℂ :=
  physicalKSAnalyticDescentB f t0 (physicalComplexCoordinatesAt t0 p)

theorem physical_descent_literal_collision_germ
    {f : Space (Fin 3) → ℂ} {v : Position → Position → ℂ}
    {t0 tStar : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxAnalyticDescentData f v t0 M A F0 W) (hA : 1≤A)
    (hT : ‖tStar-t0‖ < physicalDescentNeighborhoodRadius M A) :
    AnalyticAt ℝ (physicalDescentAReal f t0) (0,tStar) ∧
    AnalyticAt ℝ (physicalDescentBReal f t0) (0,tStar) ∧
    (fun p => physicalDescentAReal f t0 p+‖p.1‖ • physicalDescentBReal f t0 p)
      =ᶠ[𝓝 ((0:Position),tStar)] (fun p => v p.1 p.2) := by
  have hS : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hD : 0 < 32*(7*physicalKSPointwiseRate M A)^2 := by positivity
  have hTinv : ‖tStar-t0‖ < (7*physicalKSPointwiseRate M A)⁻¹ :=
    hT.trans_le (min_le_right _ _)
  have hTs : (7*physicalKSPointwiseRate M A)*‖tStar-t0‖ < 1 := by
    have hh := mul_lt_mul_of_pos_left hTinv hS
    simpa only [mul_inv_cancel₀ hS.ne'] using hh
  have hz : physicalComplexCoordinatesAt t0 ((0:Position),tStar) ∈
      {z : Fin 3 ⊕ Fin 3 → ℂ |
        (32*(7*physicalKSPointwiseRate M A)^2)*‖fun i : Fin 3 => z (.inl i)‖<1 ∧
        (7*physicalKSPointwiseRate M A)*‖fun i : Fin 3 => z (.inr i)‖<1} := by
    constructor
    · simp [physicalComplexCoordinatesAt]
    · exact (mul_le_mul_of_nonneg_left
        (physicalComplexCoordinatesCLM_right_norm_le ((0:Position),tStar-t0)) hS.le).trans_lt hTs
  have ha : AnalyticAt ℝ (physicalDescentAReal f t0) (0,tStar) :=
    AnalyticAt.comp (f := physicalComplexCoordinatesAt t0)
      (g := physicalKSAnalyticDescentA f t0)
      ((hdata.2.1 _ hz).restrictScalars (𝕜 := ℝ))
      (physicalComplexCoordinatesAt_analytic t0 _)
  have hb : AnalyticAt ℝ (physicalDescentBReal f t0) (0,tStar) :=
    AnalyticAt.comp (f := physicalComplexCoordinatesAt t0)
      (g := physicalKSAnalyticDescentB f t0)
      ((hdata.2.2.1 _ hz).restrictScalars (𝕜 := ℝ))
      (physicalComplexCoordinatesAt_analytic t0 _)
  refine ⟨ha,hb,?_⟩
  obtain ⟨r,hr,he,hidentity⟩ := hdata.2.2.2
  have hrR : (0:ℝ)<r := hr
  have hTr : ‖tStar-t0‖ < (r:ℝ) := by
    rw [he]
    exact hT
  let δ : ℝ := min ((r:ℝ)^2) (32*(7*physicalKSPointwiseRate M A)^2)⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hopen : IsOpen (collisionProductNeighborhood δ (r:ℝ) t0) :=
    (isOpen_lt continuous_fst.norm continuous_const).inter
      (isOpen_lt (continuous_snd.sub continuous_const).norm continuous_const)
  have hcenter : ((0:Position),tStar) ∈ collisionProductNeighborhood δ (r:ℝ) t0 :=
    ⟨by simpa only [norm_zero] using hδ,hTr⟩
  filter_upwards [hopen.mem_nhds hcenter] with p hp
  have hh := hidentity p.1 (p.2-t0) hp.1 hp.2
  rw [add_sub_cancel] at hh
  have hhh : v p.1 p.2 = physicalDescentAReal f t0 p+‖p.1‖ • physicalDescentBReal f t0 p := by
    have hcoords : physicalComplexCoordinatesAt t0 p =
        Sum.elim (fun i => (p.1 i:ℂ)) (fun i => ((p.2-t0) i:ℂ)) := rfl
    rw [← hcoords] at hh
    simpa only [physicalDescentAReal,physicalDescentBReal,Complex.real_smul] using hh
  exact hhh.symm


#print axioms physical_descent_literal_collision_germ
end ManyBody.S8
