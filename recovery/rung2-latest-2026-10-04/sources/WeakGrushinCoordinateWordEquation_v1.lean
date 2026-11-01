import ProductCoordinateWordSpectatorTrace_v1
import ProductDirectionalWordCommutator_v1
import LocalWeakYLaplacianWordEquation_v1
import LocalWeakYToGrushinEquation_v1

/-! Exact finite differentiated weak Grushin equations along arbitrary
coordinate words. Every solution and source jet premise is a genuine local
weak identity. Only the zero-word PDE is assumed. The right side retains
all proper ordered splits, including repetitions, with the operator-fixed
plus quadratic and minus potential commutators. This finite calculus lemma
does not itself construct the input jet family or establish factorial bounds.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def coordinateWordYSource (c : ℝ) (B : Space κ → ℝ)
    (D S : List (Fin 4 ⊕ κ) → Space κ → ℂ) (w : List (Fin 4 ⊕ κ)) (p : Space κ) : ℂ :=
  S w p-directionalWordProduct productCoordinateDirection B D w p+
    c • directionalWordProduct productCoordinateDirection (fun q => ‖q.1‖^2)
      (coordinateWordSpectatorTrace D) w p

def coordinateWordGrushinSource (c : ℝ) (B : Space κ → ℝ)
    (D S : List (Fin 4 ⊕ κ) → Space κ → ℂ) (w : List (Fin 4 ⊕ κ)) (p : Space κ) : ℂ :=
  S w p-directionalWordCommutator productCoordinateDirection B D w p+
    c • directionalWordCommutator productCoordinateDirection (fun q => ‖q.1‖^2)
      (coordinateWordSpectatorTrace D) w p

theorem coordinateWordGrushinSource_eq (c : ℝ) (B : Space κ → ℝ)
    (D S : List (Fin 4 ⊕ κ) → Space κ → ℂ) (w : List (Fin 4 ⊕ κ)) (p : Space κ) :
    coordinateWordYSource c B D S w p-
      (c*‖p.1‖^2) • coordinateWordSpectatorTrace D w p+B p • D w p =
        coordinateWordGrushinSource c B D S w p := by
  simp only [coordinateWordYSource,coordinateWordGrushinSource,
    directionalWordProduct_eq_commutator_add,smul_add,smul_smul]
  abel

set_option maxHeartbeats 1600000 in
theorem weak_grushin_coordinate_word_equations
    (c : ℝ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ} {W : ℝ}
    (D S : List (Fin 4 ⊕ κ) → Space κ → ℂ)
    (hBudget : ∀ w, w.length ≤ m+2 → RegionL2Budget (D w) Ω W)
    (hChain : ∀ w i, w.length < m+2 →
      ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (productCoordinateDirection i))
    (hS : ∀ w, w.length ≤ m → ProductLocallyL2On (S w) Ω)
    (hSD : ∀ w i, w.length < m →
      ProductLocalWeakDirectional Ω (S w) (S (i :: w)) (productCoordinateDirection i))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • D [] p) = ∫ p, φ p • S [] p) :
    ∀ w, w.length ≤ m →
      ProductLocallyL2On (coordinateWordGrushinSource c B D S w) Ω ∧
      ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        Integrable (fun p => splitGrushin c oscillatorBasis B φ p • D w p) ∧
        Integrable (fun p => φ p • coordinateWordGrushinSource c B D S w p) ∧
        (∫ p, splitGrushin c oscillatorBasis B φ p • D w p) =
          ∫ p, φ p • coordinateWordGrushinSource c B D S w p := by
  have hD (w : List (Fin 4 ⊕ κ)) (hw : w.length ≤ m+2) :
      ProductLocallyL2On (D w) Ω := (hBudget w hw).local
  have hQ : ContDiffOn ℝ ∞ (fun p : Space κ => ‖p.1‖^2) Ω :=
    ((contDiff_norm_sq ℝ).comp contDiff_fst).contDiffOn
  have hTrace := coordinateWordSpectatorTrace_locallyL2 D hD
  have hHD (w : List (Fin 4 ⊕ κ)) (i : Fin 4 ⊕ κ) (hw : w.length < m) :
      ProductLocalWeakDirectional Ω (coordinateWordYSource c B D S w)
        (coordinateWordYSource c B D S (i :: w)) (productCoordinateDirection i) := by
    exact ((hSD w i hw).sub (directionalWordProduct_localD productCoordinateDirection
      hΩ hB D (fun v j hv => hChain v j (by omega)) w i hw)).add
      ((directionalWordProduct_localD productCoordinateDirection hΩ hQ
        (coordinateWordSpectatorTrace D) (coordinateWordSpectatorTrace_localD D hChain)
        w i hw).const_smul c)
  have hH (w : List (Fin 4 ⊕ κ)) (hw : w.length ≤ m) :
      ProductLocallyL2On (coordinateWordYSource c B D S w) Ω := by
    have hPot := directionalWordProduct_locallyL2 productCoordinateDirection hΩ hB D
      (fun v hv => hD v (by omega)) w hw
    have hQuad := directionalWordProduct_locallyL2 productCoordinateDirection hΩ hQ
      (coordinateWordSpectatorTrace D) hTrace w hw
    intro K hK hs
    exact ((hS w hw K hK hs).sub (hPot K hK hs)).add ((hQuad K hK hs).const_smul c)
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  have hRed := grushin_local_potential_reduction c (EuclideanSpace.basisFun κ ℝ)
    hB.continuousOn (D []) (S []) (hD [] (by simp)) (hS [] (by simp))
    (by simpa only [hBasis] using hP)
  rw [hBasis] at hRed
  have hBase := local_grushin_to_y_equation c (D [])
    (fun p => S [] p-B p • D [] p)
    (fun j => D [Sum.inr j]) (fun j => D [Sum.inr j,Sum.inr j])
    (hD [] (by simp)) hRed.1
    (fun j => hChain [] (Sum.inr j) (by simp))
    (fun j => hChain [Sum.inr j] (Sum.inr j) (by simp)) hRed.2
  have hP0 : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • D [] p) =
        ∫ p, φ p • coordinateWordYSource c B D S [] p := by
    intro φ hφ hc hs
    simpa only [coordinateWordYSource,directionalWordProduct_nil,
      coordinateWordSpectatorTrace,List.nil_append,smul_smul] using (hBase.2 φ hφ hc hs).2.2
  have hAll := local_weak_y_laplacian_word_equations productCoordinateDirection m D
    (coordinateWordYSource c B D S) (fun w hw => hD w (by omega)) hH
    (fun w i hw => hChain w i (by omega)) hHD hP0
  intro w hw
  have hFinal := local_y_to_grushin_potential_equation c hB.continuousOn
    (D w) (coordinateWordYSource c B D S w)
    (fun j => D (Sum.inr j :: w)) (fun j => D (w ++ [Sum.inr j,Sum.inr j]))
    (hD w (by omega)) (hH w hw)
    (fun j => hChain w (Sum.inr j) (by omega))
    (coordinate_word_appended_second_spectator hΩ D hBudget hChain w hw)
    (fun φ hφ hc hs => (hAll w hw φ hφ hc hs).2.2)
  have heq : (fun p => coordinateWordYSource c B D S w p-
      (c*‖p.1‖^2) • (∑ j, D (w ++ [Sum.inr j,Sum.inr j]) p)+B p • D w p) =
        coordinateWordGrushinSource c B D S w := by
    funext p
    exact coordinateWordGrushinSource_eq c B D S w p
  have hep (p : Space κ) := congrFun heq p
  simpa only [heq,hep] using hFinal

#print axioms coordinateWordYSource
#print axioms coordinateWordGrushinSource
#print axioms coordinateWordGrushinSource_eq
#print axioms weak_grushin_coordinate_word_equations
end TheoremT.Continuum.WeakGrushin
