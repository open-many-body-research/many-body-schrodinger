import MixedPotentialWordProduct_v1

/-! The explicit right side for negative Y-Laplacian recovery. The
spectator-Laplacian term has a plus sign. Its actual weak Y derivatives use
only the existing triangular reserve, with two spectator orders accounted for.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def mixedYEquationSource (c : ℝ) (B : Space κ → ℝ)
    (F S : List (Fin 4) → List κ → Space κ → ℂ)
    (a : List (Fin 4)) (b : List κ) (p : Space κ) : ℂ :=
  S a b p - mixedPotentialWordProduct B F a b p +
    c • directionalWordProduct yDir (fun p : Space κ => ‖p.1‖^2)
      (fun q p => ∑ j : κ, F q (j :: j :: b) p) a p

theorem mixedYEquationSource_locallyL2
    (c : ℝ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {r m : ℕ}
    (F S : List (Fin 4) → List κ → Space κ → ℂ)
    (hF : ∀ a b, a.length ≤ r → a.length+b.length ≤ m → ProductLocallyL2On (F a b) Ω)
    (a : List (Fin 4)) (b : List κ) (ha : a.length ≤ r)
    (hab : a.length+b.length+2 ≤ m) (hS : ProductLocallyL2On (S a b) Ω) :
    ProductLocallyL2On (mixedYEquationSource c B F S a b) Ω := by
  have hQ := directionalWordProduct_locallyL2 yDir hΩ
    (((contDiff_norm_sq ℝ).comp contDiff_fst).contDiffOn)
    (fun q p => ∑ j : κ, F q (j :: j :: b) p) (m := a.length)
    (fun q hq K hK hs => memLp_finsetSum _ (fun j _ =>
      hF q (j :: j :: b) (by omega) (by simp only [List.length_cons]; omega) K hK hs))
    a le_rfl
  have hP := mixedPotentialWordProduct_locallyL2 hΩ hB F hF a b ha (by omega)
  intro K hK hs
  exact ((hS K hK hs).sub (hP K hK hs)).add ((hQ K hK hs).const_smul c)

theorem mixedYEquationSource_localY
    (c : ℝ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {B : Space κ → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {r m : ℕ}
    (F S : List (Fin 4) → List κ → Space κ → ℂ)
    (hY : ∀ a b i, a.length < r → a.length+b.length < m →
      ProductLocalWeakDirectional Ω (F a b) (F (i :: a) b) (yDir i))
    (a : List (Fin 4)) (b : List κ) (i : Fin 4)
    (ha : a.length < r) (hab : a.length+b.length+2 < m)
    (hS : ProductLocalWeakDirectional Ω (S a b) (S (i :: a) b) (yDir i)) :
    ProductLocalWeakDirectional Ω (mixedYEquationSource c B F S a b)
      (mixedYEquationSource c B F S (i :: a) b) (yDir i) := by
  have hQ := directionalWordProduct_localD yDir hΩ
    (((contDiff_norm_sq ℝ).comp contDiff_fst).contDiffOn)
    (fun q p => ∑ j : κ, F q (j :: j :: b) p) (m := a.length+1)
    (fun q k hq => ProductLocalWeakDirectional.finset_sum Finset.univ
      (fun j => F q (j :: j :: b)) (fun j => F (k :: q) (j :: j :: b))
      (fun j _ => hY q (j :: j :: b) k (by omega)
        (by simp only [List.length_cons]; omega))) a i (by omega)
  have hP := mixedPotentialWordProduct_localY hΩ hB F hY a b i ha (by omega)
  exact (hS.sub hP).add (hQ.const_smul c)

#print axioms mixedYEquationSource_locallyL2
#print axioms mixedYEquationSource_localY
end TheoremT.Continuum.WeakGrushin
