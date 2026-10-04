import ManyBody.S8.Internal.PhysicalDistanceGraphErrorBudget
import CompactCutoffLaplacian_v1

/-! Actual cutoff H2 classes and true scalar Coulomb graph dictionary trials.
The cutoff product rule is applied to the original physical Sobolev class.
Subtracting a genuine weak H2 error produces the actual trial, together with
its genuine graph output and graph comparison to that same cutoff class. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_compact_cutoff_actual_H2_graph
    {f : SpatialL2 2} {u : Configuration 2 → ℂ} (hH2 : HasH2 f)
    (hAE : (f : Configuration 2 → ℂ)=ᵐ[volume] u)
    {χ : Configuration 2 → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (Z : ℝ) :
    ∃U : SpatialL2 2,∃a : Coordinate 2 → SpatialL2 2,
      ∃b : Coordinate 2 → Coordinate 2 → SpatialL2 2,∃H : SpatialL2 2,
      U=ᵐ[volume] (fun x => χ x • u x) ∧
      (∀k,WeakPartial U (a k) k) ∧ (∀k l,WeakPartial (a k) (b k l) l) ∧
      HasH2 U ∧ scalarHamiltonianGraph 2 Z U H := by
  classical
  obtain ⟨d,hd,he⟩ := hH2
  choose e he using he
  obtain ⟨U,a,b,ha,hb,hU,_hfirst,_hdiag⟩ := compact_cutoff_weak_laplacian hχ hc hd he
  have hU2 : HasH2 U := ⟨a,ha,fun k l => ⟨b k l,hb k l⟩⟩
  obtain ⟨H,hH⟩ := scalar_graph_exists_of_coulombProductL2 hU2
    (coulombProductL2_of_hasH2 Z hU2)
  refine ⟨U,a,b,H,?_,ha,hb,hU2,hH⟩
  filter_upwards [hU,hAE] with x hx hy
  rw [hx,hy]

theorem physical_actual_H2_graph_trial_of_error
    {U F HU : SpatialL2 2} {S D : Configuration 2 → ℂ}
    {a d : Coordinate 2 → SpatialL2 2}
    {b e : Coordinate 2 → Coordinate 2 → SpatialL2 2}
    {Z E τ : ℝ}
    (hU : U=ᵐ[volume] S) (hF : F=ᵐ[volume] (fun x => S x-D x))
    (ha : ∀k,WeakPartial U (a k) k) (hb : ∀k l,WeakPartial (a k) (b k l) l)
    (hd : ∀k,WeakPartial F (d k) k) (he : ∀k l,WeakPartial (d k) (e k l) l)
    (hHU : scalarHamiltonianGraph 2 Z U HU)
    (h0 : ‖F‖≤τ) (h1 : ∀k,‖d k‖≤τ) (h2 : ∀k l,‖e k l‖≤τ)
    (hN : physicalH2ComponentNorm F d e≤τ) :
    ∃T : SpatialL2 2,∃dt : Coordinate 2 → SpatialL2 2,
      ∃et : Coordinate 2 → Coordinate 2 → SpatialL2 2,∃HT : SpatialL2 2,
      T=ᵐ[volume] D ∧ (∀k,WeakPartial T (dt k) k) ∧
      (∀k l,WeakPartial (dt k) (et k l) l) ∧ HasH2 T ∧
      scalarHamiltonianGraph 2 Z T HT ∧
      ‖U-T‖≤τ ∧ (∀k,‖a k-dt k‖≤τ) ∧ (∀k l,‖b k l-et k l‖≤τ) ∧
      physicalH2ComponentNorm (U-T) (fun k => a k-dt k)
        (fun k l => b k l-et k l)≤τ ∧
      ‖HU-HT‖≤(3+2*(2*|Z|+1))*τ ∧
      ‖(HU-(E:ℂ) • U)-(HT-(E:ℂ) • T)‖≤physicalDistanceGraphCoefficient Z E*τ := by
  let T := U-F
  let dt := fun k => a k-d k
  let et := fun k l => b k l-e k l
  have hT1 (k) : WeakPartial T (dt k) k := weakPartial_sub_h1 (ha k) (hd k)
  have hT2 (k l) : WeakPartial (dt k) (et k l) l := weakPartial_sub_h1 (hb k l) (he k l)
  have hF2 : HasH2 F := ⟨d,hd,fun k l => ⟨e k l,he k l⟩⟩
  have hT2all : HasH2 T := ⟨dt,hT1,fun k l => ⟨et k l,hT2 k l⟩⟩
  obtain ⟨HF,hHF⟩ := scalar_graph_exists_of_coulombProductL2 hF2
    (coulombProductL2_of_hasH2 Z hF2)
  have hHT : scalarHamiltonianGraph 2 Z T (HU-HF) := by
    simpa only [T,neg_one_smul,sub_eq_add_neg] using
      scalar_graph_add hHU (scalar_graph_smul (-1:ℂ) hHF)
  have hTF : U-T=F := by dsimp [T]; abel
  have hdt (k) : a k-dt k=d k := by dsimp [dt]; abel
  have het (k l) : b k l-et k l=e k l := by dsimp [et]; abel
  refine ⟨T,dt,et,HU-HF,?_,hT1,hT2,hT2all,hHT,?_,?_,?_,?_,?_,?_⟩
  · filter_upwards [Lp.coeFn_sub U F,hU,hF] with x hx hy hz
    change (U-F) x=D x
    rw [hx]
    change U x-F x=D x
    rw [hy,hz]
    abel
  · simpa only [hTF] using h0
  · intro k
    simpa only [hdt] using h1 k
  · intro k l
    simpa only [het] using h2 k l
  · simpa only [hTF,hdt,het] using hN
  · have hid : HU-(HU-HF)=HF := by abel
    rw [hid]
    exact (scalar_graph_norm_le_physicalH2 Z hHF d e hd he).trans
      (mul_le_mul_of_nonneg_left hN (by positivity))
  · have hid : (HU-(E:ℂ) • U)-((HU-HF)-(E:ℂ) • T)=HF-(E:ℂ) • F := by
      simp only [T,smul_sub]
      abel
    rw [hid]
    exact (scalar_graph_shift_norm_le_physicalH2 Z E hHF d e hd he).trans
      (mul_le_mul_of_nonneg_left hN (by unfold physicalDistanceGraphCoefficient; positivity))

#print axioms physical_compact_cutoff_actual_H2_graph
#print axioms physical_actual_H2_graph_trial_of_error
end ManyBody.S8
