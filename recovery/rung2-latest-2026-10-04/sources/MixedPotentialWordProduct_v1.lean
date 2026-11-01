import ProductDirectionalWordLeibniz_v1
import MixedTriangularState_v1
import SpectatorWordProduct_v1

/-! Actual mixed ordered coefficient products. Spectator Leibniz choices
are followed by Y Leibniz choices, with multiplicity retained. Local weak Y
chains require only solution words inside the displayed triangular reserve.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def mixedPotentialWordProduct (B : Space κ → ℝ)
    (F : List (Fin 4) → List κ → Space κ → ℂ)
    (a : List (Fin 4)) (b : List κ) (p : Space κ) : ℂ :=
  ((spectatorWordSplits b).map (fun bc =>
    directionalWordProduct yDir (spectatorWordDeriv B bc.1) (fun a => F a bc.2) a p)).sum

theorem mixedPotentialWordProduct_nil
    (B : Space κ → ℝ) (F : List (Fin 4) → List κ → Space κ → ℂ)
    (b : List κ) (p : Space κ) :
    mixedPotentialWordProduct B F [] b p = spectatorWordProduct B (F []) b p := by
  simp only [mixedPotentialWordProduct,directionalWordProduct_nil,spectatorWordProduct]

theorem mixedPotentialWordProduct_locallyL2
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {r m : ℕ}
    (F : List (Fin 4) → List κ → Space κ → ℂ)
    (hF : ∀ a b, a.length ≤ r → a.length+b.length ≤ m → ProductLocallyL2On (F a b) Ω)
    (a : List (Fin 4)) (b : List κ) (ha : a.length ≤ r) (hab : a.length+b.length ≤ m) :
    ProductLocallyL2On (mixedPotentialWordProduct B F a b) Ω := by
  apply TheoremT.Continuum.productLocallyL2On_list_sum
  intro bc hbc
  have hn := spectatorWordSplits_length_sum hbc
  apply directionalWordProduct_locallyL2 yDir hΩ (spectatorWordDeriv_contDiffOn hΩ hB bc.1)
    (fun q => F q bc.2) (m := a.length)
  · intro q hq
    exact hF q bc.2 (by omega) (by omega)
  · exact le_rfl

theorem mixedPotentialWordProduct_localY
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {r m : ℕ}
    (F : List (Fin 4) → List κ → Space κ → ℂ)
    (hY : ∀ a b i, a.length < r → a.length+b.length < m →
      ProductLocalWeakDirectional Ω (F a b) (F (i :: a) b) (yDir i))
    (a : List (Fin 4)) (b : List κ) (i : Fin 4)
    (ha : a.length < r) (hab : a.length+b.length < m) :
    ProductLocalWeakDirectional Ω (mixedPotentialWordProduct B F a b)
      (mixedPotentialWordProduct B F (i :: a) b) (yDir i) := by
  apply ProductLocalWeakDirectional.list_sum
  intro bc hbc
  have hn := spectatorWordSplits_length_sum hbc
  apply directionalWordProduct_localD yDir hΩ (spectatorWordDeriv_contDiffOn hΩ hB bc.1)
    (fun q => F q bc.2) (m := a.length+1)
  · intro q j hq
    exact hY q bc.2 j (by omega) (by omega)
  · omega

#print axioms mixedPotentialWordProduct_nil
#print axioms mixedPotentialWordProduct_locallyL2
#print axioms mixedPotentialWordProduct_localY
end TheoremT.Continuum.WeakGrushin
