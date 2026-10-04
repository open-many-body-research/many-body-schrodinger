import ManyBody.S8.Internal.PhysicalDistanceCompositionGeometry
import ManyBody.S8.NuclearAmbientDistanceDerivativeBudgets
import ManyBody.S8.Internal.AmbientRealSliceUniqueness
import Mathlib.Tactic
/-! Exact literal physical radii and the original nuclear-index-zero and coefficient-one pair distance reconstructions on the closed inner chart. The actual configuration is reconstructed and original representatives are retained. -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalNuclearDistanceCenter (ε : ℝ) : Fin 3 → ℝ := ![0,ε,ε]
def physicalPairDistanceCenter (ε : ℝ) : Fin 3 → ℝ := ![ε,ε,0]

theorem physical_distance_triple_eq_radii (x : Configuration 2) :
    physicalDistanceTriple x=![‖position x 0‖,‖position x 1‖,‖position x 0-position x 1‖] := by
  ext j
  fin_cases j <;> simp [physicalDistanceTriple,physicalDistanceLinearMaps,
    electronPositionCLM_apply,pairDifferenceCLM_apply]

theorem physical_distance_triple_eq_pair_distances (x : Configuration 2) :
    physicalDistanceTriple x=pairAmbientPhysicalDistances x := physical_distance_triple_eq_radii x

theorem nuclear_distance_center_real_cast (ε : ℝ) :
    ambientRealCast (physicalNuclearDistanceCenter ε)=nuclearOriginalDistanceCenter ε := by
  ext j
  fin_cases j <;> simp [physicalNuclearDistanceCenter,nuclearOriginalDistanceCenter]

theorem pair_distance_center_real_cast (ε : ℝ) :
    ambientRealCast (physicalPairDistanceCenter ε)=pairOriginalDistanceCenter ε := by
  ext j
  fin_cases j <;> simp [physicalPairDistanceCenter,pairOriginalDistanceCenter]

theorem nuclear_physical_coordinates_reconstruct_original (x : Configuration 2) :
    nuclearKSPhysicalCoordinates 0 (position x 0) (position x 1)=x := by
  ext ⟨j,k⟩
  change (position (nuclearKSPhysicalCoordinates 0 (position x 0) (position x 1)) j) k=(position x j) k
  rw [position_nuclearKSPhysicalCoordinates]
  fin_cases j <;> simp

theorem actual_nuclear_inner_distance_reconstruction
    {u : Configuration 2 → ℂ} {ε δ B : ℝ} (hε : 0<ε) (hδ : 0<δ) (hδsmall : δ≤1/4)
    (hrec : PhysicalNuclearAmbientReconstruction u 0 ε δ B)
    {x : Configuration 2}
    (hx : physicalDistanceTriple x∈closedBall (physicalNuclearDistanceCenter ε) (ε*δ/8)) :
    u x=nuclearOriginalAmbientFunction u 0 ε (ambientRealCast (physicalDistanceTriple x)) := by
  have hR : 0<ε*δ := mul_pos hε hδ
  have hb : ambientRealCast (physicalDistanceTriple x)∈ball (nuclearOriginalDistanceCenter ε) (ε*δ) := by
    rw [←nuclear_distance_center_real_cast,mem_ball,dist_eq_norm,←map_sub,ambientRealCast_norm]
    exact lt_of_le_of_lt (by simpa only [mem_closedBall,dist_eq_norm] using hx) (by linarith)
  obtain ⟨h0,h1,h2⟩ := (nuclear_original_distance_ball_iff hε hδ _).mp hb
  have hc : ambientRealCast (physicalDistanceTriple x)=
      ![(‖position x 0‖:ℂ),(‖position x 1‖:ℂ),(‖position x 0-position x 1‖:ℂ)] := by
    rw [physical_distance_triple_eq_radii]
    ext j
    fin_cases j <;> simp
  rw [hc] at h0 h1 h2
  have hr : ‖position x 0‖<ε*δ := by simpa using h0
  have hs : |‖position x 1‖-ε|<ε*δ := by simpa [←Complex.ofReal_sub,Complex.norm_real] using h1
  have ht : |‖position x 0-position x 1‖-ε|<ε*δ := by simpa [←Complex.ofReal_sub,Complex.norm_real] using h2
  have hTs : 0<‖position x 1‖ := by
    have hi := (abs_lt.mp hs).1
    have hm := mul_le_mul_of_nonneg_left hδsmall hε.le
    linarith
  simpa only [nuclear_physical_coordinates_reconstruct_original,hc] using
    hrec.2.2 (position x 0) (position x 1) hTs hr hs ht

theorem actual_pair_inner_distance_reconstruction
    {u : Configuration 2 → ℂ} {ε M A F0 W δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hrec : PhysicalPairAmbientReconstruction u ε M A F0 W δ)
    {x : Configuration 2}
    (hx : physicalDistanceTriple x∈closedBall (physicalPairDistanceCenter ε) (ε*δ/8)) :
    u x=pairOriginalAmbientFunction u ε (ambientRealCast (physicalDistanceTriple x)) := by
  have hR : 0<ε*δ := mul_pos hε hδ
  have hb : ambientRealCast (physicalDistanceTriple x)∈ball (pairOriginalDistanceCenter ε) (ε*δ) := by
    rw [←pair_distance_center_real_cast,mem_ball,dist_eq_norm,←map_sub,ambientRealCast_norm]
    exact lt_of_le_of_lt (by simpa only [mem_closedBall,dist_eq_norm] using hx) (by linarith)
  obtain ⟨h0,h1,h2⟩ := (pair_original_distance_ball_iff hε hδ _).mp hb
  have hc : ambientRealCast (physicalDistanceTriple x)=
      ![(‖position x 0‖:ℂ),(‖position x 1‖:ℂ),(‖position x 0-position x 1‖:ℂ)] := by
    rw [physical_distance_triple_eq_radii]
    ext j
    fin_cases j <;> simp
  rw [hc] at h0 h1 h2
  have hr : |‖position x 0‖-ε|<ε*δ := by simpa [←Complex.ofReal_sub,Complex.norm_real] using h0
  have hs : |‖position x 1‖-ε|<ε*δ := by simpa [←Complex.ofReal_sub,Complex.norm_real] using h1
  have ht : ‖position x 0-position x 1‖<ε*δ := by simpa using h2
  change u x=pairOriginalAmbientFunction u ε (fun i => (physicalDistanceTriple x i:ℂ))
  rw [physical_distance_triple_eq_pair_distances]
  exact hrec.2.2.2.2 x hr hs ht

#print axioms actual_nuclear_inner_distance_reconstruction
#print axioms actual_pair_inner_distance_reconstruction
end ManyBody.S8