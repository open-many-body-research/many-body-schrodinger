import ProductDirectionalWordFDeriv_v1
import ProductCoordinateWeakHk_v1
import SpectatorWordFDeriv_v1

/-! Mixed ordered Y/T derivatives of a locally smooth real coefficient are
controlled by its actual iterated Frechet derivative of the total order.
The two words are concatenated in their existing outer-to-inner order; no
commutation of derivatives or factorial estimate is assumed. Coordinate
directions have norm one, so the comparison adds no dimension factor. -/
noncomputable section
open scoped Topology ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem productCoordinateDirection_norm (i : Fin 4 ⊕ κ) :
    ‖productCoordinateDirection i‖ = 1 := by
  cases i with
  | inl j => exact cutoff_yDir_norm j
  | inr j => exact cutoff_tDir_norm j

theorem coordinateWordDeriv_of_tWord (B : Space κ → ℝ) (tb : List κ) :
    directionalWordDeriv productCoordinateDirection B
      (tb.map (Sum.inr : κ → Fin 4 ⊕ κ)) = spectatorWordDeriv B tb := by
  induction tb with
  | nil => rfl
  | cons j tb ih =>
    simp only [List.map_cons, directionalWordDeriv, spectatorWordDeriv,
      productCoordinateDirection, ih]

theorem mixedWordDeriv_eq_coordinateWord (B : Space κ → ℝ)
    (ya : List (Fin 4)) (tb : List κ) :
    directionalWordDeriv yDir (spectatorWordDeriv B tb) ya =
      directionalWordDeriv productCoordinateDirection B
        (ya.map (Sum.inl : Fin 4 → Fin 4 ⊕ κ) ++
          tb.map (Sum.inr : κ → Fin 4 ⊕ κ)) := by
  induction ya with
  | nil =>
    simpa only [List.map_nil, List.nil_append, directionalWordDeriv] using
      (coordinateWordDeriv_of_tWord B tb).symm
  | cons i ya ih =>
    simp only [List.map_cons, List.cons_append, directionalWordDeriv,
      productCoordinateDirection, ih]

theorem mixedWordDeriv_abs_le_iteratedFDeriv {Ω : Set (Space κ)}
    (hΩ : IsOpen Ω) {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    (ya : List (Fin 4)) (tb : List κ) {p : Space κ} (hp : p ∈ Ω) :
    |directionalWordDeriv yDir (spectatorWordDeriv B tb) ya p| ≤
      ‖iteratedFDeriv ℝ (ya.length + tb.length) B p‖ := by
  rw [mixedWordDeriv_eq_coordinateWord]
  have hh := directionalWordDeriv_abs_le_iteratedFDeriv productCoordinateDirection
    (fun i => (productCoordinateDirection_norm i).le) hΩ hB
    (ya.map (Sum.inl : Fin 4 → Fin 4 ⊕ κ) ++
      tb.map (Sum.inr : κ → Fin 4 ⊕ κ)) hp
  have hlen : (ya.map (Sum.inl : Fin 4 → Fin 4 ⊕ κ) ++
      tb.map (Sum.inr : κ → Fin 4 ⊕ κ)).length = ya.length + tb.length := by simp
  rw [hlen] at hh
  exact hh

theorem mixedWordDeriv_finite_bound {Ω : Set (Space κ)}
    (hΩ : IsOpen Ω) {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {S : Set (Space κ)} (hS : S ⊆ Ω) {m : ℕ} {M : ℝ}
    (hM : ∀ k ≤ m, ∀ p ∈ S, ‖iteratedFDeriv ℝ k B p‖ ≤ M) :
    ∀ ya : List (Fin 4), ∀ tb : List κ, ya.length + tb.length ≤ m →
      ∀ p ∈ S, |directionalWordDeriv yDir (spectatorWordDeriv B tb) ya p| ≤ M := by
  intro ya tb hlen p hp
  exact (mixedWordDeriv_abs_le_iteratedFDeriv hΩ hB ya tb (hS hp)).trans
    (hM (ya.length + tb.length) hlen p hp)

#print axioms productCoordinateDirection_norm
#print axioms coordinateWordDeriv_of_tWord
#print axioms mixedWordDeriv_eq_coordinateWord
#print axioms mixedWordDeriv_abs_le_iteratedFDeriv
#print axioms mixedWordDeriv_finite_bound
end TheoremT.Continuum.WeakGrushin
