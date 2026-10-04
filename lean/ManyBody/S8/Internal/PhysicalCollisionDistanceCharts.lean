import ManyBody.S8.NuclearIndexDyadicH2Approximation
import Mathlib.Tactic
/-! Actual nuclear-zero, nuclear-one and pair distance chart interfaces.
The two nuclear charts have selected and spectator radius semantics; the
index-one map is the true exchanged original configuration. Exact original
local dyadic data supplies actual weak43 error families for every chartkind.
The open inner patches are the literal preimages of actual distance balls. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators NNReal
namespace ManyBody.S8
open TheoremT.Continuum

def physicalCollisionChartDistances (j : Fin 3) : Configuration 2 → (Fin 3 → ℝ) :=
  fun x => if j=1 then physicalIndexOneDistanceTriple x else physicalDistanceTriple x

def physicalCollisionChartCenter (j : Fin 3) (ε : ℝ) : Fin 3 → ℝ :=
  if j=2 then physicalPairDistanceCenter ε else physicalNuclearDistanceCenter ε

def physicalCollisionChartRadius (j : Fin 3) (ε M A : ℝ) : ℝ :=
  ε*(if j=2 then pairAmbientDistanceRadius 1 M A else nuclearAmbientRetainedRadius M A)

def physicalCollisionChartProfile (u : Configuration 2 → ℂ) (j : Fin 3) (ε : ℝ) :
    (Fin 3 → ℂ) → ℂ :=
  if j=2 then pairOriginalAmbientFunction u ε else nuclearOriginalAmbientFunction u 0 ε

def physicalCollisionChartPatch (M A : ℝ) (j : Fin 3) (ε : ℝ) : Set (Configuration 2) :=
  {x | physicalCollisionChartDistances j x∈ball (physicalCollisionChartCenter j ε)
    (physicalCollisionChartRadius j ε M A/8)}

theorem physical_collision_chart_distances_continuous (j : Fin 3) :
    Continuous (physicalCollisionChartDistances j) := by
  by_cases hj : j=1
  · have hmap : physicalCollisionChartDistances j=physicalIndexOneDistanceTriple := by
      funext x
      simp [physicalCollisionChartDistances,hj]
    rw [hmap]
    apply continuous_pi
    intro k
    exact ((physicalDistanceLinearMaps k).comp
      (permuteSpace twoElectronSwap).toContinuousLinearEquiv.toContinuousLinearMap).continuous.norm
  · have hmap : physicalCollisionChartDistances j=physicalDistanceTriple := by
      funext x
      simp [physicalCollisionChartDistances,hj]
    rw [hmap]
    exact continuous_pi fun k => (physicalDistanceLinearMaps k).continuous.norm
theorem physical_collision_chart_patch_open (M A : ℝ) (j : Fin 3) (ε : ℝ) :
    IsOpen (physicalCollisionChartPatch M A j ε) :=
  isOpen_ball.preimage (physical_collision_chart_distances_continuous j)

def PhysicalChosenDistanceDyadicH2Data (u : Configuration 2 → ℂ)
    (χ : Configuration 2 → ℝ) (dMap : Configuration 2 → (Fin 3 → ℝ))
    (h : (Fin 3 → ℂ) → ℂ) (a : Fin 3 → ℝ) : Prop :=
  ∃C : ℝ,1≤C ∧ ∃m : ℕ,∀p : ℕ,
    (physicalDyadicDistanceSupport h a m p).card≤(physicalDyadicDistanceOrder m p)^3 ∧
    (∀α∈physicalDyadicDistanceSupport h a m p,(∑j : Fin 3,α j)<physicalDyadicDistanceOrder m p) ∧
    (∀α∈physicalDyadicDistanceSupport h a m p,∀j : Fin 3,α j<physicalDyadicDistanceOrder m p) ∧
    ∃F : SpatialL2 2,∃d : Coordinate 2 → SpatialL2 2,
    ∃e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
      (F : Configuration 2 → ℂ)=ᵐ[volume]
        (fun x => χ x • (u x-(physicalDyadicDistancePolynomial h a m p (dMap x):ℂ))) ∧
      (∀k,WeakPartial F (d k) k) ∧ (∀k l,WeakPartial (d k) (e k l) l) ∧ HasH2 F ∧
      ‖F‖≤(1/2:ℝ)^p*C ∧ (∀k,‖d k‖≤(1/2:ℝ)^p*C) ∧
      (∀k l,‖e k l‖≤(1/2:ℝ)^p*C) ∧ physicalH2ComponentNorm F d e≤(1/2:ℝ)^p*C

theorem physical_chosen_distance_data_of_raw
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {hc : HasCompactSupport χ}
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R : ℝ}
    (hdata : PhysicalDistanceDyadicH2Approximation u χ hc h a R) :
    PhysicalChosenDistanceDyadicH2Data u χ physicalDistanceTriple h a := by
  obtain ⟨C,hC,m,hm⟩ := hdata
  let B := ‖physicalDistanceCompactBudgetClass (tsupport χ) hc‖
  let C1 := max 1 (7*C*B)
  refine ⟨C1,le_max_left _ _,m,?_⟩
  intro p
  obtain ⟨hcard,hdegree,hcoord,_,herr,hid⟩ := hm p
  obtain ⟨F,d,e,hF,_,_,hw1,hw2,hH2,_,_,_,hnorm,_⟩ := herr
  have hfinal : physicalH2ComponentNorm F d e≤(1/2:ℝ)^p*C1 := by
    calc _≤7*(1/2:ℝ)^p*C*B := hnorm
         _=(1/2:ℝ)^p*(7*C*B) := by ring
         _≤(1/2:ℝ)^p*C1 := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  exact ⟨hcard,hdegree,hcoord,F,d,e,hF.trans (Eventually.of_forall hid),hw1,hw2,hH2,
    (physicalH2ComponentNorm_bounds _ _ _).1.trans hfinal,
    (fun k => (physicalH2ComponentNorm_first_le _ _ _ k).trans hfinal),
    (fun k l => (physicalH2ComponentNorm_bounds _ _ _).2.2 k l |>.trans hfinal),hfinal⟩

theorem physical_chosen_distance_data_of_index_one
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ}
    {h : (Fin 3 → ℂ) → ℂ} {a : Fin 3 → ℝ} {R : ℝ}
    (hdata : PhysicalIndexOneDistanceDyadicH2Approximation u χ h a R) :
    PhysicalChosenDistanceDyadicH2Data u χ physicalIndexOneDistanceTriple h a := by
  obtain ⟨C,hC,m,hm⟩ := hdata
  refine ⟨C,hC,m,?_⟩
  intro p
  obtain ⟨hcard,hdegree,hcoord,_,hweak⟩ := hm p
  exact ⟨hcard,hdegree,hcoord,hweak⟩

theorem actual_physical_collision_chart_dyadic_data
    {u : Configuration 2 → ℂ} {χ : Configuration 2 → ℝ} {ε M A : ℝ}
    (hPhys : PhysicalGroundDistanceDyadicH2Data u ε M A)
    (hOne : PhysicalGroundIndexOneDistanceDyadicH2Data u ε M A)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (j : Fin 3)
    (hs : ∀x∈tsupport χ,physicalCollisionChartDistances j x∈closedBall
      (physicalCollisionChartCenter j ε) (physicalCollisionChartRadius j ε M A/8)) :
    PhysicalChosenDistanceDyadicH2Data u χ (physicalCollisionChartDistances j)
      (physicalCollisionChartProfile u j ε) (physicalCollisionChartCenter j ε) := by
  fin_cases j
  · simp only [physicalCollisionChartProfile,physicalCollisionChartCenter] at ⊢
    simp only [physicalCollisionChartDistances,physicalCollisionChartCenter,
      physicalCollisionChartRadius] at hs
    simp at hs ⊢
    exact physical_chosen_distance_data_of_raw (hPhys.1 χ hχ hc hs)
  · simp only [physicalCollisionChartProfile,physicalCollisionChartCenter] at ⊢
    simp only [physicalCollisionChartDistances,physicalCollisionChartCenter,
      physicalCollisionChartRadius] at hs
    simp at hs ⊢
    exact physical_chosen_distance_data_of_index_one (hOne χ hχ hc hs)
  · simp only [physicalCollisionChartProfile,physicalCollisionChartCenter] at ⊢
    simp only [physicalCollisionChartDistances,physicalCollisionChartCenter,
      physicalCollisionChartRadius] at hs
    simp at hs ⊢
    exact physical_chosen_distance_data_of_raw (hPhys.2 χ hχ hc hs)
#print axioms physical_collision_chart_distances_continuous
#print axioms physical_collision_chart_patch_open
#print axioms physical_chosen_distance_data_of_raw
#print axioms physical_chosen_distance_data_of_index_one
#print axioms actual_physical_collision_chart_dyadic_data
end ManyBody.S8