import SpectatorFiniteIteration_v1
import MixedYFiniteIteration_v1
import ProductCoordinateWeakHk_v1

/-! Finite actual coordinate weak regularity from the raw potential equation.
The geometric stages and finite source/coefficient data are explicit inputs;
no solution derivative or differentiated solution equation is assumed. The
result is per finite order, with no order-uniform or factorial rate claim.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem MixedTriangularState.lower_order
    {Ω : Set (Space κ)} {f : Space κ → ℂ} {r m r' m' : ℕ} {W : ℝ}
    (hf : MixedTriangularState Ω f r m W) (hr : r' ≤ r) (hm : m' ≤ m) :
    MixedTriangularState Ω f r' m' W := by
  obtain ⟨F,h0,hF,hY,hT⟩ := hf
  exact ⟨F,h0,fun a b ha hab => hF a b (ha.trans hr) (hab.trans hm),
    fun a b i ha hab => hY a b i (ha.trans_le hr) (hab.trans_le hm),
    fun a b j ha hab => hT a b j (ha.trans hr) (hab.trans_le hm)⟩

theorem ProductCoordinateWeakHk.restrict
    {Ω O : Set (Space κ)} {f : Space κ → ℂ} {m : ℕ} {W U : ℝ}
    (hf : ProductCoordinateWeakHk Ω f m W) (hO : O ⊆ Ω) (hWU : W ≤ U) :
    ProductCoordinateWeakHk O f m U := by
  obtain ⟨D,h0,hD,hChain⟩ := hf
  exact ⟨D,h0,fun w hw => (hD w hw).restrict hO hWU,
    fun w i hw => (hChain w i hw).mono hO⟩

set_option maxHeartbeats 1200000 in
theorem finite_weak_grushin_coordinate_regularity
    {c : ℝ} (hc : 0 < c) (m : ℕ)
    (ΩT VT ΩY VY : ℕ → Set (Space κ))
    (χT ηT χY ηY : ℕ → Space κ → ℝ)
    (MT AT LT DT QT MY AY LY DY QY : ℕ → ℝ)
    (hGeomT : ∀ k, k < m → SpectatorStepGeometry c (ΩT k) (ΩT (k+1)) (VT k)
      (χT k) (ηT k) (MT k) (AT k) (LT k) (DT k) (QT k))
    (hGeomY : ∀ k, k < m → SpectatorStepGeometry 0 (ΩY k) (ΩY (k+1)) (VY k)
      (χY k) (ηY k) (MY k) (AY k) (LY k) (DY k) (QY k))
    (hOpenY : ∀ k, k < m → IsOpen (ΩY (k+1)))
    (hJoin : ΩY 0 = ΩT m)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B (ΩT 0))
    (f : Space κ → ℂ) (S : List (Fin 4) → List κ → Space κ → ℂ)
    (K0 Q0 H0 W0 : ℝ) (hK0 : 0 ≤ K0) (hH0 : 0 ≤ H0) (hW0 : 0 ≤ W0)
    (hf : RegionL2Budget f (ΩT 0) W0)
    (hS : ∀ a b, a.length+b.length ≤ m → RegionL2Budget (S a b) (ΩT 0) H0)
    (hSY : ∀ a b i, a.length+b.length < m →
      ProductLocalWeakDirectional (ΩT 0) (S a b) (S (i :: a) b) (yDir i))
    (hST : ∀ b j, b.length < m →
      ProductLocalWeakDirectional (ΩT 0) (S [] b) (S [] (j :: b)) (tDir j))
    (hCoeff : ∀ a b, a.length+b.length ≤ m → ∀ p ∈ ΩT 0,
      |directionalWordDeriv yDir (spectatorWordDeriv B b) a p| ≤ K0)
    (hQuad : ∀ a, a.length ≤ m → ∀ p ∈ ΩT 0,
      |directionalWordDeriv yDir (fun p : Space κ => ‖p.1‖^2) a p| ≤ Q0)
    (hEq : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ΩT 0 →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p, φ p • S [] [] p) :
    ∃ W : ℝ, 0 ≤ W ∧ ProductCoordinateWeakHk (ΩY m) f m W := by
  have hDom : ∀ k, k ≤ m → ΩT k ⊆ ΩT 0 := by
    intro k
    induction k with
    | zero => intro _; exact Set.Subset.rfl
    | succ k ih =>
      intro hk
      exact (hGeomT k (by omega)).domain_subset.trans (ih (by omega))
  have hBase : ΩY 0 ⊆ ΩT 0 := hJoin ▸ hDom m le_rfl
  obtain ⟨hWT,hT⟩ := spectatorFiniteState_iterate hc m ΩT VT χT ηT MT AT LT DT QT
    hGeomT hB f (S []) K0 W0 H0 hK0 hW0 hH0 hf
    (fun b hb => hS [] b (by simp only [List.length_nil]; omega))
    (fun b j hb => (hST b j (by omega)).2.2)
    (fun b hb p hp => hCoeff [] b (by simp only [List.length_nil]; omega) p hp) hEq
  have hInitial := spectatorFiniteState_to_mixedTriangularState hT
  rw [← hJoin] at hInitial
  obtain ⟨hW,hFinal⟩ := mixedTriangularState_potential_iterate c m ΩY VY χY ηY MY AY LY DY QY
    hGeomY hOpenY (hB.mono hBase) (by norm_num : 1 ≤ 2) K0 Q0 H0 _ hWT f S hInitial
    (fun a b hab => (hS a b (by omega)).restrict hBase le_rfl)
    (fun a b i hab => (hSY a b i (by omega)).mono hBase)
    (fun b j hb => (hST b j (by omega)).mono hBase)
    (fun a b hab p hp => hCoeff a b (by omega) p (hBase hp))
    (fun a ha p hp => hQuad a (by omega) p (hBase hp))
    (fun φ hφ hcφ hs => hEq φ hφ hcφ (hs.trans hBase))
  exact ⟨_,hW,mixedTriangularState_coordinateWeakHk
    (hFinal.lower_order (by omega : m ≤ 2+2*m) le_rfl)⟩

#print axioms MixedTriangularState.lower_order
#print axioms ProductCoordinateWeakHk.restrict
#print axioms finite_weak_grushin_coordinate_regularity
end TheoremT.Continuum.WeakGrushin
