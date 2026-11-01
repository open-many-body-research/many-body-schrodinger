import SpectatorWordWeakLeibniz_v1
import GrushinLocalPotentialReduction_v1

/-! Exact finite spectator differentiation of the weak potential equation.
The given families are genuine local weak derivative chains.  The resulting
right side is an explicit sum of strictly lower solution orders; no equation
for a positive-order solution derivative is an input. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 800000 in
theorem weak_grushin_finite_spectator_equations
    (c : ℝ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω) (m : ℕ)
    (G F : List κ → Space κ → ℂ)
    (hG : ∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω)
    (hF : ∀ w, w.length ≤ m → ProductLocallyL2On (F w) Ω)
    (hGD : ∀ w j, w.length < m → LocalSpectatorD Ω (G w) (G (j :: w)) j)
    (hFD : ∀ w j, w.length < m → LocalSpectatorD Ω (F w) (F (j :: w)) j)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • G [] p) = ∫ p, φ p • F [] p) :
    ∀ w, w.length ≤ m →
      ProductLocallyL2On (fun p => F w p - spectatorWordCommutator B G w p) Ω ∧
      ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        Integrable (fun p => splitGrushin c oscillatorBasis B φ p • G w p) ∧
        Integrable (fun p => φ p • (F w p - spectatorWordCommutator B G w p)) ∧
        (∫ p, splitGrushin c oscillatorBasis B φ p • G w p) =
          ∫ p, φ p • (F w p - spectatorWordCommutator B G w p) := by
  have hBasis : (EuclideanSpace.basisFun κ ℝ : κ → EuclideanSpace ℝ κ) = oscillatorBasis := by
    funext j
    exact EuclideanSpace.basisFun_apply κ ℝ j
  let H := fun w p => F w p - spectatorWordProduct B G w p
  have hProd (w : List κ) (hw : w.length ≤ m) :=
    spectatorWordProduct_locallyL2 hΩ hB G hG w hw
  have hH (w : List κ) (hw : w.length ≤ m) : ProductLocallyL2On (H w) Ω :=
    product_locallyL2On_sub (hF w hw) (hProd w hw)
  have hHD (w : List κ) (j : κ) (hw : w.length < m) :
      LocalSpectatorD Ω (H w) (H (j :: w)) j := by
    have hnext : (j :: w).length ≤ m := by simp only [List.length_cons]; omega
    have hn : ∀ q, q.length ≤ m → ProductLocallyL2On
        (fun p => -spectatorWordProduct B G q p) Ω := by
      intro q hq K hK hs
      exact (hProd q hq K hK hs).neg
    have he := LocalSpectatorD.add (hF w (by omega)) (hn w (by omega))
      (hF (j :: w) hnext) (hn (j :: w) hnext) (hFD w j hw)
      (spectatorWordProduct_localD hΩ hB G hG hGD w j hw).neg
    simpa only [H, sub_eq_add_neg] using he
  have hPrincipal : ∀ w, w.length ≤ m →
      ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • G w p) =
          ∫ p, φ p • H w p := by
    intro w
    induction w with
    | nil =>
      intro hw φ hφ hc hs
      have he := grushin_local_potential_test_iff c (EuclideanSpace.basisFun κ ℝ)
        hB.continuousOn (G []) (F []) (hG [] hw) (hF [] hw) hφ hc hs
      rw [hBasis] at he
      simpa only [H, spectatorWordProduct, spectatorWordSplits, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, spectatorWordDeriv, add_zero] using
        he.mp (hP φ hφ hc hs)
    | cons j w ih =>
      intro hw
      have hn : w.length < m := by simp only [List.length_cons] at hw; omega
      have hbase : w.length ≤ m := by omega
      have he := local_weak_grushin_spectator_differentiate c
        (G w) (G (j :: w)) (H w) (H (j :: w))
        (hG w hbase) (hG (j :: w) hw) (hH w hbase) (hH (j :: w) hw)
        (oscillatorBasis j) (hGD w j hn) (ih hbase) (hHD w j hn)
      exact fun φ hφ hc hs => (he φ hφ hc hs).2.2
  intro w hw
  have hR := product_locallyL2On_sub (hF w hw)
    (spectatorWordCommutator_locallyL2 hΩ hB G hG w hw)
  refine ⟨hR,?_⟩
  intro φ hφ hc hs
  obtain ⟨hleft,_,hright,_,_⟩ := grushin_local_potential_test_integrable c
    (EuclideanSpace.basisFun κ ℝ) hB.continuousOn (G w)
    (fun p => F w p - spectatorWordCommutator B G w p) (hG w hw) hR hφ hc hs
  rw [hBasis] at hleft
  refine ⟨hleft,hright,?_⟩
  have he := grushin_local_potential_test_iff c (EuclideanSpace.basisFun κ ℝ)
    hB.continuousOn (G w) (fun p => F w p - spectatorWordCommutator B G w p)
    (hG w hw) hR hφ hc hs
  rw [hBasis] at he
  apply he.mpr
  simpa only [H, spectatorWordProduct_eq_commutator_add, sub_add_eq_sub_sub] using
    hPrincipal w hw φ hφ hc hs

#print axioms weak_grushin_finite_spectator_equations
end TheoremT.Continuum.WeakGrushin
