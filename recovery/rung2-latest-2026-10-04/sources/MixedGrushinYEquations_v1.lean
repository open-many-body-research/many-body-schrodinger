import MixedYEquationSource_v1
import LocalWeakYLaplacianWordEquation_v1
import LocalWeakGrushinYEquation_v1
import WeakGrushinFiniteSpectatorEquation_v1

/-! The actual mixed Y equations used by the triangular recovery. Only the
original potential PDE is assumed. Finite spectator differentiation, exact
potential reduction, two weak spectator integrations, and finite Y
Leibniz/differentiation derive every displayed right side. No differentiated
PDE, classical solution derivatives, or preliminary joint H2 are inputs.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 1200000 in
theorem mixed_grushin_y_equations
    (c : ℝ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω) {r m : ℕ}
    (F S : List (Fin 4) → List κ → Space κ → ℂ)
    (hF : ∀ a b, a.length ≤ r → a.length+b.length ≤ m → ProductLocallyL2On (F a b) Ω)
    (hY : ∀ a b i, a.length < r → a.length+b.length < m →
      ProductLocalWeakDirectional Ω (F a b) (F (i :: a) b) (yDir i))
    (hT : ∀ b j, b.length < m →
      ProductLocalWeakDirectional Ω (F [] b) (F [] (j :: b)) (tDir j))
    (hS : ∀ a b, a.length+b.length+2 ≤ m → ProductLocallyL2On (S a b) Ω)
    (hSY : ∀ a b i, a.length+b.length+2 < m →
      ProductLocalWeakDirectional Ω (S a b) (S (i :: a) b) (yDir i))
    (hST : ∀ b j, b.length+2 < m →
      ProductLocalWeakDirectional Ω (S [] b) (S [] (j :: b)) (tDir j))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • F [] [] p) = ∫ p, φ p • S [] [] p) :
    ∀ a b, a.length ≤ r → a.length+b.length+2 ≤ m →
      ProductLocallyL2On (mixedYEquationSource c B F S a b) Ω ∧
      ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        Integrable (fun p => splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • F a b p) ∧
        Integrable (fun p => φ p • mixedYEquationSource c B F S a b p) ∧
        (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • F a b p) =
          ∫ p, φ p • mixedYEquationSource c B F S a b p := by
  intro a b ha hab
  have hb : b.length+2 ≤ m := by omega
  have hBfun : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  have hGb (q : List κ) (hq : q.length ≤ b.length) : ProductLocallyL2On (F [] q) Ω :=
    hF [] q (by simp) (by simp only [List.length_nil,zero_add]; omega)
  have hSb (q : List κ) (hq : q.length ≤ b.length) : ProductLocallyL2On (S [] q) Ω :=
    hS [] q (by simp only [List.length_nil,zero_add]; omega)
  have hFinite := weak_grushin_finite_spectator_equations c hΩ hB b.length
    (F []) (S []) hGb hSb
    (fun q j hq => (hT q j (by omega)).2.2)
    (fun q j hq => (hST q j (by omega)).2.2) hP b le_rfl
  have hPrincipal : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • F [] b p) =
        ∫ p, φ p • (S [] b p-spectatorWordProduct B (F []) b p) := by
    intro φ hφ hc hs
    have he := grushin_local_potential_test_iff c (EuclideanSpace.basisFun κ ℝ)
      hB.continuousOn (F [] b) (fun p => S [] b p-spectatorWordCommutator B (F []) b p)
      (hGb b le_rfl) hFinite.1 hφ hc hs
    rw [hBfun] at he
    simpa only [spectatorWordProduct_eq_commutator_add,sub_add_eq_sub_sub] using
      he.mp (hFinite.2 φ hφ hc hs).2.2
  have hRawSource : ProductLocallyL2On
      (fun p => S [] b p-spectatorWordProduct B (F []) b p) Ω :=
    product_locallyL2On_sub (hSb b le_rfl)
      (spectatorWordProduct_locallyL2 hΩ hB (F []) hGb b le_rfl)
  have hYbase := local_grushin_to_y_equation c (F [] b)
    (fun p => S [] b p-spectatorWordProduct B (F []) b p)
    (fun j => F [] (j :: b)) (fun j => F [] (j :: j :: b))
    (hGb b le_rfl) hRawSource (fun j => hT b j (by omega))
    (fun j => hT (j :: b) j (by simp only [List.length_cons]; omega)) hPrincipal
  have hBase : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin 0 oscillatorBasis (fun _ => 0) φ p • F [] b p) =
        ∫ p, φ p • mixedYEquationSource c B F S [] b p := by
    intro φ hφ hc hs
    simpa only [mixedYEquationSource,mixedPotentialWordProduct_nil,
      directionalWordProduct_nil,smul_smul] using (hYbase.2 φ hφ hc hs).2.2
  have hSource (q : List (Fin 4)) (hq : q.length ≤ a.length) :
      ProductLocallyL2On (mixedYEquationSource c B F S q b) Ω :=
    mixedYEquationSource_locallyL2 c hΩ hB F S hF q b (by omega) (by omega) (hS q b (by omega))
  refine ⟨hSource a le_rfl,?_⟩
  exact local_weak_y_laplacian_word_equations yDir a.length (fun q => F q b)
    (fun q => mixedYEquationSource c B F S q b)
    (fun q hq => hF q b (by omega) (by omega)) hSource
    (fun q i hq => hY q b i (by omega) (by omega))
    (fun q i hq => mixedYEquationSource_localY c hΩ hB F S hY q b i
      (by omega) (by omega) (hSY q b i (by omega))) hBase a le_rfl

#print axioms mixed_grushin_y_equations
end TheoremT.Continuum.WeakGrushin
