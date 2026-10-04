import ManyBody.S8.Internal.PhysicalDistanceJetDomination
import ManyBody.S8.Internal.PhysicalDistanceProfileCompactBounds
import ManyBody.S8.Internal.PhysicalCompactL2Domination
import CollisionNull_v2
import WeakH2JetClosure_v1
import HardyWeakCore_v1
import Mathlib.Tactic
/-! Actual weak H2 physical distance pullbacks across all collision sets. Smooth regularized value/first/second jets converge strongly in true L2 by derived compact domination, and the original weak-jet closedness theorem gives the genuine unchanged domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def PhysicalDistanceWeakH2Data (χ : Configuration 2 → ℝ) (g : (Fin 3 → ℝ) → ℂ) : Prop :=
  ∃F : SpatialL2 2, ∃d : Coordinate 2 → SpatialL2 2,
    ∃e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
    F=ᵐ[volume] physicalCutoffDistanceValue χ g ∧
    (∀k,d k=ᵐ[volume] fun x => physicalCutoffDistanceFirst χ g x (coordinateVector k)) ∧
    (∀k j,e k j=ᵐ[volume] fun x => physicalCutoffDistanceSecond χ g x (coordinateVector k) (coordinateVector j)) ∧
    (∀k,WeakPartial F (d k) k) ∧ (∀k j,WeakPartial (d k) (e k j) j) ∧ HasH2 F

theorem actual_physical_distance_cutoff_weakH2 {χ : Configuration 2 → ℝ}
    {g : (Fin 3 → ℝ) → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : ContDiff ℝ ∞ g) : PhysicalDistanceWeakH2Data χ g := by
  let K := tsupport χ
  have hK : IsCompact K := hc
  obtain ⟨C,hC⟩ := actual_compact_cutoff_jet_bound hχ hc
  obtain ⟨D,hD,hDa,hDr⟩ := physical_distance_profile_compact_bounds K hK g hg
  let δ : ℕ→ℝ := fun n => 1/((n:ℝ)+1)
  have hp (n : ℕ) : 0<δ n := by dsimp [δ]; positivity
  have hδ1 (n : ℕ) : δ n≤1 := by
    dsimp [δ]
    rw [div_le_iff₀ (by positivity)]
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let Fn : ℕ→Configuration 2→ℂ := fun n => regularizedCutoffDistanceValue χ g (δ n)
  let Dn : ℕ→Coordinate 2→Configuration 2→ℂ := fun n k x => fderiv ℝ (Fn n) x (coordinateVector k)
  let En : ℕ→Coordinate 2→Coordinate 2→Configuration 2→ℂ := fun n k j x =>
    fderiv ℝ (Dn n k) x (coordinateVector j)
  have hs (n : ℕ) : ContDiff ℝ ∞ (Fn n) :=
    hχ.smul (hg.comp (regularized_physical_distance_contDiff (hp n)))
  have hsD (n : ℕ) (k : Coordinate 2) : ContDiff ℝ ∞ (Dn n k) :=
    ((hs n).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hsE (n : ℕ) (k j : Coordinate 2) : ContDiff ℝ ∞ (En n k j) :=
    ((hsD n k).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hv (k : Coordinate 2) : ‖coordinateVector k‖≤1 := by simp [coordinateVector]
  let b : Configuration 2→ℝ := fun x => 16*C*D*(1+physicalInverseDistanceBudget x)
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top (μ:=volume)⟩
  have hb : MemLp b 2 (volume.restrict K) :=
    ((memLp_const (1:ℝ)).add (physical_inverse_distance_budget_memLp_on_compact hK)).const_mul (16*C*D)
  have hB (n : ℕ) (k j : Coordinate 2) : ∀ᵐx∂volume,
      ‖Fn n x‖≤‖K.indicator b x‖ ∧ ‖Dn n k x‖≤‖K.indicator b x‖ ∧
      ‖En n k j x‖≤‖K.indicator b x‖ := by
    filter_upwards [ae_collisionFree 2] with x hx
    have hh := regularized_cutoff_distance_indicator_bounds (hp n) hχ hC hD
      (hDr (δ n) (hp n) (hδ1 n)) hx (hv k) (hv j)
    simpa only [Fn,Dn,En,regularized_cutoff_distance_first (hp n) hχ hg,
      regularized_cutoff_distance_second (hp n) hχ hg] using hh
  have hFbound (n : ℕ) : ∀ᵐx∂volume, ‖Fn n x‖≤‖K.indicator b x‖ := by
    filter_upwards [hB n (0,0) (0,0)] with x hx using hx.1
  have hFlim : ∀ᵐx∂volume,Tendsto (fun n => Fn n x) atTop
      (𝓝 (physicalCutoffDistanceValue χ g x)) :=
    Eventually.of_forall (regularized_cutoff_distance_value_tendsto hg.continuous hδ)
  obtain ⟨hFn,hF,hFt⟩ := physical_compact_dominated_L2_limit hK hb
    (fun n => (hs n).continuous.aestronglyMeasurable) hFbound hFlim
  have hDlimit (k : Coordinate 2) :
      ∃hDn : ∀n,MemLp (Dn n k) 2 volume,
      ∃hD0 : MemLp (fun x => physicalCutoffDistanceFirst χ g x (coordinateVector k)) 2 volume,
      Tendsto (fun n => (hDn n).toLp (Dn n k)) atTop
        (𝓝 (hD0.toLp (fun x => physicalCutoffDistanceFirst χ g x (coordinateVector k)))) := by
    apply physical_compact_dominated_L2_limit hK hb
    · exact fun n => (hsD n k).continuous.aestronglyMeasurable
    · intro n
      filter_upwards [hB n k (0,0)] with x hx using hx.2.1
    · filter_upwards [ae_collisionFree 2] with x hx
      have he : (fun n => Dn n k x)=
          (fun n => regularizedCutoffDistanceFirst χ g (δ n) x (coordinateVector k)) := by
        funext n
        exact regularized_cutoff_distance_first (hp n) hχ hg x _
      rw [he]
      exact regularized_cutoff_distance_first_tendsto hg hp hδ hx _
  choose hDn hD0 hDt using hDlimit
  have hElimit (k j : Coordinate 2) :
      ∃hEn : ∀n,MemLp (En n k j) 2 volume,
      ∃hE0 : MemLp (fun x => physicalCutoffDistanceSecond χ g x (coordinateVector k) (coordinateVector j)) 2 volume,
      Tendsto (fun n => (hEn n).toLp (En n k j)) atTop
        (𝓝 (hE0.toLp (fun x => physicalCutoffDistanceSecond χ g x (coordinateVector k) (coordinateVector j)))) := by
    apply physical_compact_dominated_L2_limit hK hb
    · exact fun n => (hsE n k j).continuous.aestronglyMeasurable
    · intro n
      filter_upwards [hB n k j] with x hx using hx.2.2
    · filter_upwards [ae_collisionFree 2] with x hx
      have he : (fun n => En n k j x)=
          (fun n => regularizedCutoffDistanceSecond χ g (δ n) x (coordinateVector k) (coordinateVector j)) := by
        funext n
        exact regularized_cutoff_distance_second (hp n) hχ hg x _ _
      rw [he]
      exact regularized_cutoff_distance_second_tendsto hg hp hδ hx _ _
  choose hEn hE0 hEt using hElimit
  have hweak1 (n : ℕ) (k : Coordinate 2) :=
    classicalDerivative_to_WeakPartial ((hs n).of_le (by simp)) k (hFn n) (hDn k n)
  have hweak2 (n : ℕ) (k j : Coordinate 2) :=
    classicalDerivative_to_WeakPartial ((hsD n k).of_le (by simp)) j (hDn k n) (hEn k j n)
  obtain ⟨hw1,hw2,hh2⟩ := weakH2_jet_of_tendsto hweak1 hweak2 hFt hDt hEt
  exact ⟨hF.toLp _,fun k => (hD0 k).toLp _,fun k j => (hE0 k j).toLp _,
    hF.coeFn_toLp,fun k => (hD0 k).coeFn_toLp,fun k j => (hE0 k j).coeFn_toLp,hw1,hw2,hh2⟩

#print axioms actual_physical_distance_cutoff_weakH2
end ManyBody.S8