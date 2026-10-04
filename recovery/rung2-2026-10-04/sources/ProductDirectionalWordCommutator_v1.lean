import ProductDirectionalWordLeibniz_v1

/-! Exact proper ordered Leibniz sum. The list retains every choice and
its multiplicity; only the unique undifferentiated coefficient term is removed.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

def directionalWordCommutator {ι : Type} (dirs : ι → Y × T) (B : Y × T → ℝ)
    (G : List ι → Y × T → ℂ) (w : List ι) (p : Y × T) : ℂ :=
  ((spectatorWordProperSplits w).map
    (fun ab => directionalWordDeriv dirs B ab.1 p • G ab.2 p)).sum

theorem directionalWordProduct_eq_commutator_add {ι : Type}
    (dirs : ι → Y × T) (B : Y × T → ℝ) (G : List ι → Y × T → ℂ)
    (w : List ι) (p : Y × T) :
    directionalWordProduct dirs B G w p =
      directionalWordCommutator dirs B G w p+B p • G w p := by
  simp only [directionalWordProduct,spectatorWordSplits_eq_proper_append,
    List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,directionalWordDeriv,directionalWordCommutator]

theorem directionalWordCommutator_nil {ι : Type}
    (dirs : ι → Y × T) (B : Y × T → ℝ) (G : List ι → Y × T → ℂ) :
    directionalWordCommutator dirs B G [] = 0 := by
  funext p
  simp [directionalWordCommutator,spectatorWordProperSplits]

theorem directionalWordCommutator_locallyL2 {ι : Type}
    (dirs : ι → Y × T) {Ω : Set (Y × T)} (hΩ : IsOpen Ω)
    {B : Y × T → ℝ} (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ}
    (G : List ι → Y × T → ℂ)
    (hG : ∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω)
    (w : List ι) (hw : w.length ≤ m) :
    ProductLocallyL2On (directionalWordCommutator dirs B G w) Ω := by
  have hEq : directionalWordCommutator dirs B G w =
      (fun p => directionalWordProduct dirs B G w p-B p • G w p) := by
    funext p
    rw [directionalWordProduct_eq_commutator_add,add_sub_cancel_right]
  rw [hEq]
  exact product_locallyL2On_sub
    (directionalWordProduct_locallyL2 dirs hΩ hB G hG w hw)
    (product_smooth_coefficient_locallyL2_raw hΩ hB (hG w hw))

#print axioms directionalWordProduct_eq_commutator_add
#print axioms directionalWordCommutator_nil
#print axioms directionalWordCommutator_locallyL2
end TheoremT.Continuum
