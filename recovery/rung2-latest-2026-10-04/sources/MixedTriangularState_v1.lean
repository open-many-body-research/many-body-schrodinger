import LocalMixedWordCompatibility_v1

/-! Finite mixed derivative reserve indexed by ordered words, with actual
region L2 budgets and local weak derivative chains. The initial two Y levels
are constructed from the existing spectator gain witnesses. Individual
component norms are bounded by the already proved aggregate norms, so this
conversion introduces no dimension factor or larger norm budget.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def MixedTriangularState (Ω : Set (Space κ)) (f : Space κ → ℂ)
    (r m : ℕ) (W : ℝ) : Prop :=
  ∃ F : List (Fin 4) → List κ → Space κ → ℂ,
    F [] [] = f ∧
    (∀ a b, a.length ≤ r → a.length + b.length ≤ m → RegionL2Budget (F a b) Ω W) ∧
    (∀ a b i, a.length < r → a.length + b.length < m →
      ProductLocalWeakDirectional Ω (F a b) (F (i :: a) b) (yDir i)) ∧
    ∀ a b j, a.length ≤ r → a.length + b.length < m →
      ProductLocalWeakDirectional Ω (F a b) (F a (j :: b)) (tDir j)

theorem MixedTriangularState.restrict
    {Ω O : Set (Space κ)} {f : Space κ → ℂ} {r m : ℕ} {W U : ℝ}
    (hf : MixedTriangularState Ω f r m W) (hO : O ⊆ Ω) (hWU : W ≤ U) :
    MixedTriangularState O f r m U := by
  obtain ⟨F,h0,hF,hY,hT⟩ := hf
  exact ⟨F,h0,fun a b ha hab => (hF a b ha hab).restrict hO hWU,
    fun a b i ha hab => (hY a b i ha hab).mono hO,
    fun a b j ha hab => (hT a b j ha hab).mono hO⟩

set_option maxHeartbeats 800000 in
theorem spectatorFiniteState_to_mixedTriangularState
    {Ω : Set (Space κ)} {f : Space κ → ℂ} {m : ℕ} {W : ℝ}
    (hf : SpectatorFiniteState Ω f m W) : MixedTriangularState Ω f 2 m W := by
  obtain ⟨G,gy,hyy,h0,hG,hGD,hRes⟩ := hf
  let F : List (Fin 4) → List κ → Space κ → ℂ := fun a b =>
    match a with
    | [] => G b
    | i :: [] => gy b i
    | j :: i :: _ => hyy b i j
  have hgy (b : List κ) (i : Fin 4) (hb : b.length < m) : RegionL2Budget (gy b i) Ω W := by
    apply regionL2Budget_of_global
    exact (Finset.single_le_sum (fun q _ => sq_nonneg ‖gy b q‖)
      (Finset.mem_univ i)).trans (hRes b hb).1
  have he (b : List κ) (i j : Fin 4) (hb : b.length < m) :
      RegionL2Budget (hyy b i j) Ω W := by
    apply regionL2Budget_of_global
    apply le_trans (Finset.single_le_sum (fun q _ => sq_nonneg ‖hyy b i q‖) (Finset.mem_univ j))
    apply le_trans (Finset.single_le_sum
      (fun q _ => Finset.sum_nonneg (fun s _ => sq_nonneg ‖hyy b q s‖)) (Finset.mem_univ i))
    exact (hRes b hb).2.1
  have hF (a : List (Fin 4)) (b : List κ) (ha : a.length ≤ 2)
      (hab : a.length + b.length ≤ m) : RegionL2Budget (F a b) Ω W := by
    cases a with
    | nil => exact hG b (by simpa using hab)
    | cons i a =>
      have hb : b.length < m := by simp only [List.length_cons] at hab; omega
      cases a with
      | nil => exact hgy b i hb
      | cons j a => exact he b j i hb
  have hY (a : List (Fin 4)) (b : List κ) (i : Fin 4) (ha : a.length < 2)
      (hab : a.length + b.length < m) :
      ProductLocalWeakDirectional Ω (F a b) (F (i :: a) b) (yDir i) := by
    cases a with
    | nil =>
      have hb : b.length < m := by simpa using hab
      exact ⟨(hG b (by omega)).local,(hgy b i hb).local,(hRes b hb).2.2.1 i⟩
    | cons j a =>
      have heq : a = [] := by
        have hn : a.length = 0 := by simp only [List.length_cons] at ha; omega
        exact List.length_eq_zero_iff.mp hn
      subst a
      have hb : b.length < m := by simp only [List.length_cons,List.length_nil] at hab; omega
      exact ProductLocalWeakDirectional.of_global ((hRes b hb).2.2.2 j i) Ω
  have hT (b : List κ) (j : κ) (hb : b.length < m) :
      ProductLocalWeakDirectional Ω (F [] b) (F [] (j :: b)) (tDir j) :=
    ⟨(hG b (by omega)).local,(hG (j :: b) (by simp only [List.length_cons]; omega)).local,
      hGD b j hb⟩
  exact ⟨F,h0,hF,hY,fun a b j ha hab =>
    mixed_word_spectator_compatibility F hY hT a b j ha hab⟩

#print axioms MixedTriangularState.restrict
#print axioms spectatorFiniteState_to_mixedTriangularState
end TheoremT.Continuum.WeakGrushin
