import ManyBody.S8.Internal.AmbientProfileReality
import ManyBody.S8.AmbientDistanceTaylorTruncation
import Mathlib.Tactic
/-! Reality and real Taylor data of the actual original collision profiles.

A genuine feasible real triangle neighborhood supplies actual real physical
values of H. Real analytic continuation propagates these values through the
whole real slice, and actual selected-distance parity separates A/B, including
the collision axis. Every ordered real directional jet, canonical complex
diagonal coefficient and finite canonical polynomial then has real value.

The endpoint retains the same actual normalized scalar ground state from
S8-032, all its original graph, spectrum, weak H2 decay, descent,
reconstruction and complex/real budgets, and derives the genuine S8-033
Taylor sums/errors for those same profiles. The actual state reality and
physical reconstruction discharge every profile reality premise. These are
local distance statements; the real slice includes analytic extension values
outside the physical nonnegative triangle region.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology BigOperators NNReal
namespace ManyBody.S8
open TheoremT.Continuum

theorem ambient_profile_real_of_feasible
    {f : (Fin 3 → ℂ) → ℂ} {U : Set (Fin 3 → ℂ)}
    (hU : IsOpen U) (hconvex : Convex ℝ U) (hf : AnalyticOnNhd ℂ f U)
    (hvalues : ∀ p : Fin 3 → ℝ, p∈strictPhysicalDistanceTriangles →
      ambientRealCast p∈U → (f (ambientRealCast p)).im=0)
    (hbase : ∃ p : Fin 3 → ℝ, p∈strictPhysicalDistanceTriangles ∧ ambientRealCast p∈U) :
    ∀ p : Fin 3 → ℝ, ambientRealCast p∈U → (f (ambientRealCast p)).im=0 := by
  let V : Set (Fin 3 → ℝ) := ambientRealCast ⁻¹' U
  have hV : IsOpen V := hU.preimage ambientRealCast.continuous
  have hconn : IsPreconnected V := (hconvex.linear_preimage ambientRealCast.toLinearMap).isPreconnected
  have hAn : AnalyticOnNhd ℝ (f ∘ ambientRealCast) V :=
    fun p hp => ambient_real_profile_analytic (hf _ hp)
  obtain ⟨p₀,hpT,hpU⟩ := hbase
  have hnear : ∀ᶠ p in 𝓝 p₀, (f (ambientRealCast p)).im=0 := by
    filter_upwards [strictPhysicalDistanceTriangles_open.mem_nhds hpT,hV.mem_nhds hpU] with p hp hpV
    exact hvalues p hp hpV
  exact analytic_real_profile_real_of_germ hAn hconn hpU hnear

theorem nuclear_real_polydisc_feasible {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) :
    ∃ p : Fin 3 → ℝ, p∈strictPhysicalDistanceTriangles ∧
      ambientRealCast p∈nuclearOriginalDistancePolydisc ε δ := by
  let r : ℝ := min (ε*δ) ε/2
  have hr : 0<r := by dsimp [r]; positivity
  have hrδ : r<ε*δ := by have := min_le_left (ε*δ) ε; dsimp [r]; nlinarith
  have hrε : r<ε := by have := min_le_right (ε*δ) ε; dsimp [r]; nlinarith
  refine ⟨![r,ε,ε],⟨hr,hε,hε,?_,?_⟩,?_,?_,?_⟩
  · change |r-ε|<ε
    rw [abs_of_neg (sub_neg.mpr hrε)]
    linarith
  · change ε<r+ε; linarith
  · simpa [ambientRealCast_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hrδ
  · simpa [ambientRealCast_apply] using mul_pos hε hδ
  · simpa [ambientRealCast_apply] using mul_pos hε hδ

theorem pair_real_polydisc_feasible {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) :
    ∃ p : Fin 3 → ℝ, p∈strictPhysicalDistanceTriangles ∧
      ambientRealCast p∈pairOriginalDistancePolydisc ε δ := by
  let r : ℝ := min (ε*δ) ε/2
  have hr : 0<r := by dsimp [r]; positivity
  have hrδ : r<ε*δ := by have := min_le_left (ε*δ) ε; dsimp [r]; nlinarith
  have hrε : r<ε := by have := min_le_right (ε*δ) ε; dsimp [r]; nlinarith
  refine ⟨![ε,ε,r],⟨hε,hε,hr,?_,?_⟩,?_,?_,?_⟩
  · simpa using hr
  · change r<ε+ε; linarith
  · simpa [ambientRealCast_apply] using mul_pos hε hδ
  · simpa [ambientRealCast_apply] using mul_pos hε hδ
  · simpa [ambientRealCast_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hrδ

def NuclearAmbientProfileRealityData (u : Configuration 2 → ℂ) (i : Fin 2) (ε δ : ℝ) : Prop :=
  AmbientRealProfileRealityData (nuclearOriginalAmbientA u i ε) (nuclearOriginalDistancePolydisc ε δ) ∧
  AmbientRealProfileRealityData (nuclearOriginalAmbientB u i ε) (nuclearOriginalDistancePolydisc ε δ) ∧
  AmbientRealProfileRealityData (nuclearOriginalAmbientFunction u i ε) (nuclearOriginalDistancePolydisc ε δ)

def PairAmbientProfileRealityData (u : Configuration 2 → ℂ) (ε δ : ℝ) : Prop :=
  AmbientRealProfileRealityData (pairOriginalAmbientA u ε) (pairOriginalDistancePolydisc ε δ) ∧
  AmbientRealProfileRealityData (pairOriginalAmbientB u ε) (pairOriginalDistancePolydisc ε δ) ∧
  AmbientRealProfileRealityData (pairOriginalAmbientFunction u ε) (pairOriginalDistancePolydisc ε δ)

theorem nuclear_ambient_profile_reality
    (u : Configuration 2 → ℂ) (i : Fin 2) {ε M A F0 W : ℝ}
    (hε : 0<ε) (hA : 1≤A) (hreal : ∀ x, (u x).im=0)
    (haxis : PhysicalKSAxisAnalyticDescentData
      ((originScaledDifference u ε ∘ nuclearKSLift i) ∘ (physicalSpectatorReindexAt i).symm)
      (nuclearDistanceRealSpectator 1) M A F0 W (physicalKSAnalyticAxisRadius M A))
    (hrec : PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
      (nuclearAmbientNormalizedBound M A F0 W)) :
    NuclearAmbientProfileRealityData u i ε (nuclearAmbientRetainedRadius M A) := by
  let δ := nuclearAmbientRetainedRadius M A
  let U := nuclearOriginalDistancePolydisc ε δ
  have hδ : 0<δ := nuclearAmbientRetainedRadius_pos hA
  have hopen : IsOpen U := nuclearOriginalDistancePolydisc_open _ _
  have hconv : Convex ℝ U := nuclearOriginalDistancePolydisc_convex _ _
  have hbase := nuclear_real_polydisc_feasible hε hδ
  have hH : ∀ p : Fin 3 → ℝ, ambientRealCast p∈U →
      (nuclearOriginalAmbientFunction u i ε (ambientRealCast p)).im=0 := by
    apply ambient_profile_real_of_feasible hopen hconv hrec.1 _ hbase
    intro p hp hpU
    rw [nuclear_ambient_reconstruction_feasible hrec p hp hpU]
    exact hreal _
  obtain ⟨hAnA,hAnB⟩ := nuclearOriginalAmbient_profiles_analytic u i hε hA haxis
  let V : Set (Fin 3 → ℝ) := ambientRealCast ⁻¹' U
  have hV : IsOpen V := hopen.preimage ambientRealCast.continuous
  have hconn : IsPreconnected V := (hconv.linear_preimage ambientRealCast.toLinearMap).isPreconnected
  have hreflect : ∀ p∈V, ambientRealCoordinateReflect 0 p∈V := by
    intro p hp
    change ambientRealCast (ambientRealCoordinateReflect 0 p)∈U
    rw [ambientRealCast_reflect]
    simpa [V,U,nuclearOriginalDistancePolydisc,ambientCoordinateReflect] using hp
  have hnonzero : ∃ p∈V, p 0≠0 := by
    obtain ⟨p,hpT,hpU⟩ := hbase
    exact ⟨p,hpU,ne_of_gt hpT.1⟩
  obtain ⟨hAR,hBR⟩ := analytic_real_even_profiles_real 0 hV hconn
    (fun p hp => ambient_real_profile_analytic (hAnB _ hp)) hreflect
    (fun p _ => by simpa only [Function.comp_apply,ambientRealCast_reflect] using
      (nuclearOriginalAmbient_profiles_even u i ε (ambientRealCast p)).1)
    (fun p _ => by simpa only [Function.comp_apply,ambientRealCast_reflect] using
      (nuclearOriginalAmbient_profiles_even u i ε (ambientRealCast p)).2)
    (fun p _ => nuclearOriginalAmbient_profiles_recombine u i hε (ambientRealCast p))
    hH hnonzero
  exact ⟨ambient_profile_reality_data_of_real_values hopen hAnA hAR,
    ambient_profile_reality_data_of_real_values hopen hAnB hBR,
    ambient_profile_reality_data_of_real_values hopen hrec.1 hH⟩

theorem pair_ambient_profile_reality
    (u : Configuration 2 → ℂ) {ε M A F0 W δ : ℝ}
    (hε : 0<ε) (hδ : 0<δ) (hreal : ∀ x, (u x).im=0)
    (hrec : PhysicalPairAmbientReconstruction u ε M A F0 W δ) :
    PairAmbientProfileRealityData u ε δ := by
  let U := pairOriginalDistancePolydisc ε δ
  have hopen : IsOpen U := pairOriginalDistancePolydisc_open _ _
  have hconv : Convex ℝ U := pairOriginalDistancePolydisc_convex _ _
  have hbase := pair_real_polydisc_feasible hε hδ
  have hH : ∀ p : Fin 3 → ℝ, ambientRealCast p∈U →
      (pairOriginalAmbientFunction u ε (ambientRealCast p)).im=0 := by
    apply ambient_profile_real_of_feasible hopen hconv hrec.2.2.1 _ hbase
    intro p hp hpU
    rw [pair_ambient_reconstruction_feasible hrec p hp hpU]
    exact hreal _
  let V : Set (Fin 3 → ℝ) := ambientRealCast ⁻¹' U
  have hV : IsOpen V := hopen.preimage ambientRealCast.continuous
  have hconn : IsPreconnected V := (hconv.linear_preimage ambientRealCast.toLinearMap).isPreconnected
  have hreflect : ∀ p∈V, ambientRealCoordinateReflect 2 p∈V := by
    intro p hp
    change ambientRealCast (ambientRealCoordinateReflect 2 p)∈U
    rw [ambientRealCast_reflect]
    simpa [V,U,pairOriginalDistancePolydisc,ambientCoordinateReflect] using hp
  have hnonzero : ∃ p∈V, p 2≠0 := by
    obtain ⟨p,hpT,hpU⟩ := hbase
    exact ⟨p,hpU,ne_of_gt hpT.2.2.1⟩
  obtain ⟨hAR,hBR⟩ := analytic_real_even_profiles_real 2 hV hconn
    (fun p hp => ambient_real_profile_analytic (hrec.2.1 _ hp)) hreflect
    (fun p _ => by simpa only [Function.comp_apply,ambientRealCast_reflect] using
      (pairOriginalAmbient_profiles_even u ε (ambientRealCast p)).1)
    (fun p _ => by simpa only [Function.comp_apply,ambientRealCast_reflect] using
      (pairOriginalAmbient_profiles_even u ε (ambientRealCast p)).2)
    (fun _ _ => rfl) hH hnonzero
  exact ⟨ambient_profile_reality_data_of_real_values hopen hrec.1 hAR,
    ambient_profile_reality_data_of_real_values hopen hrec.2.1 hBR,
    ambient_profile_reality_data_of_real_values hopen hrec.2.2.1 hH⟩

#print axioms ambient_profile_real_of_feasible
#print axioms nuclear_real_polydisc_feasible
#print axioms pair_real_polydisc_feasible
#print axioms nuclear_ambient_profile_reality
#print axioms pair_ambient_profile_reality
theorem twoElectron_scalar_ground_ambient_real_profiles_and_taylor_data
    (Z : ℝ) (hZ : 2≤Z) :
    ∃ C_H M A : ℝ, 1 ≤ C_H ∧ 1 ≤ M ∧ 1 ≤ A ∧
      ∃ f : SpatialL2 2, ∃ u : Configuration 2 → ℂ,
      ∃ L : ℝ≥0, ∃ R : ℝ,
        ‖f‖ = 1 ∧ HasH2 f ∧
        scalarHamiltonianGraph 2 Z f
          (((variationalGroundEnergy 2 Z).toReal : ℂ) • f) ∧
        spectralGroundEnergy 2 Z = ((variationalGroundEnergy 2 Z).toReal : EReal) ∧
        (((variationalGroundEnergy 2 Z).toReal : ℂ) ∈
          TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z)) ∧
        (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z),
          (variationalGroundEnergy 2 Z).toReal ≤ z.re) ∧
        LocallyLipschitz u ∧ (f : Configuration 2 → ℂ) =ᵐ[volume] u ∧
        (∀ x, ‖u x‖ ≤
          coulombMoserBoundCoefficient 2 Z (variationalGroundEnergy 2 Z).toReal) ∧
        (∀ x, (u x).im = 0) ∧
        (∀ x, u (permuteSpace twoElectronSwap x) = u x) ∧
        (∀ Q : Position ≃ₗᵢ[ℝ] Position, ∀ x,
          u (configurationRotation 2 Q x) = u x) ∧
        0 < L ∧ 0 < R ∧ LipschitzOnWith L u (ball 0 R) ∧
        0 ≤ M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume ∧
        0 ≤ (((L : ℝ)^2+‖u 0‖^2)*C_H) ∧
        (∃ d : Coordinate 2 → SpatialL2 2,
          ∃ e : Coordinate 2 → Coordinate 2 → SpatialL2 2,
          (∀ k, WeakPartial f (d k) k) ∧
          (∀ k l, WeakPartial (d k) (e k l) l) ∧
          ∀ a : ℝ, 0 ≤ a → a^2 < Z^2/112 →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
              weakH2ExteriorNorm f d e r ≤ Real.exp (-a*r)*C) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ (i : Fin 2) (t0 : Position), ‖t0‖ = 1 →
            PhysicalKSBoxInvariantAnalyticDescentDerivativeData
              ((originScaledDifference u ε ∘ nuclearKSLift i) ∘
                (physicalSpectatorReindexAt i).symm)
              (fun X T => originScaledDifference u ε (nuclearKSPhysicalCoordinates i X T))
              t0 M A (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L : ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          ∀ t0 : Position, ‖t0‖ = 1 →
            PhysicalKSBoxEvenInvariantAnalyticDescentDerivativeData
              ((originScaledDifference u ε ∘ pairKSLift) ∘
                (physicalSpectatorReindexAt (0 : Fin 2)).symm)
              (fun X T => originScaledDifference u ε (pairKSPhysicalCoordinates X T))
              t0 M A (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L : ℝ)^2+‖u 0‖^2)*C_H)) ∧
        0 < physicalKSAnalyticAxisRadius M A ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) → ∀ i : Fin 2,
          PhysicalKSAxisAnalyticDescentData
            ((originScaledDifference u ε ∘ nuclearKSLift i) ∘
              (physicalSpectatorReindexAt i).symm)
            (WithLp.toLp 2 ![0,0,1]) M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L : ℝ)^2+‖u 0‖^2)*C_H) (physicalKSAnalyticAxisRadius M A)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ min 1 (R/4) →
          PhysicalKSAxisAnalyticDescentData
            ((originScaledDifference u ε ∘ pairKSLift) ∘
              (physicalSpectatorReindexAt (0 : Fin 2)).symm)
            (WithLp.toLp 2 ![0,0,1]) M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L : ℝ)^2+‖u 0‖^2)*C_H) (physicalKSAnalyticAxisRadius M A)) ∧
        0<pairAmbientDistanceRadius 1 M A ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientPhysicalAnalyticData (originScaledDifference u ε) 1 M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PhysicalPairAmbientReconstruction u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
        0<nuclearAmbientRetainedRadius M A ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          PhysicalNuclearAmbientReconstruction u i ε (nuclearAmbientRetainedRadius M A)
            (nuclearAmbientNormalizedBound M A
              (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
              (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
          NuclearAmbientDistanceDerivativeData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientDistanceDerivativeData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A) ∧
          PairRealAmbientDistanceDerivativeData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearRealAmbientDistanceDerivativeData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) → ∀ i : Fin 2,
          NuclearAmbientDistanceTaylorData u i ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) ∧
          NuclearAmbientProfileRealityData u i ε (nuclearAmbientRetainedRadius M A)) ∧
        (∀ ε : ℝ, 0<ε → ε≤min 1 (R/4) →
          PairAmbientDistanceTaylorData u ε M A
            (M*‖u 0‖*Real.sqrt physicalKSUniformSourceVolume)
            (((L:ℝ)^2+‖u 0‖^2)*C_H) (pairAmbientDistanceRadius 1 M A) ∧
          PairAmbientProfileRealityData u ε (pairAmbientDistanceRadius 1 M A)) := by
  obtain ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal⟩ :=
      twoElectron_scalar_ground_real_ambient_distance_derivative_budgets Z hZ
  refine ⟨C_H,M,A,hCH,hM,hA,f,u,L,R,hf,hH2,hgraph,hspectrum,hmem,hlower,
    hu,hAE,hbound,hreal,hexchange,hrotation,hL,hR,hLip,hF0,hW,htail,hN,hP,
    haxispos,hNA,hPA,hδP,hambient,hrec,hδN,hNrecData,hPairDeriv,hNuclearReal,?_,?_⟩
  · intro ε hε hlim i
    exact ⟨nuclear_ambient_distance_taylor_data u i hε hA (hNA ε hε hlim i)
        (hNrecData ε hε hlim i).1,
      nuclear_ambient_profile_reality u i hε hA hreal (hNA ε hε hlim i)
        (hNrecData ε hε hlim i).1⟩
  · intro ε hε hlim
    exact ⟨pair_ambient_distance_taylor_data u hε hδP (hrec ε hε hlim),
      pair_ambient_profile_reality u hε hδP hreal (hrec ε hε hlim)⟩

#print axioms twoElectron_scalar_ground_ambient_real_profiles_and_taylor_data

end ManyBody.S8
