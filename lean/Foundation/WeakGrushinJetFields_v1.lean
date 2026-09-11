import CompactFiniteWeightedL2_v1
import EuclideanGrushinPrincipal_v1
import GrushinWeightedSpectator_v1

/-! The actual Grushin principal expression formed from genuine second weak
L2 jets; no regularity or operator equation is included in these definitions. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]
abbrev Space (κ : Type) [Fintype κ] := EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ
abbrev Jet (κ : Type) [Fintype κ] := Space κ → Space κ → Lp ℂ 2 (volume : Measure (Space κ))

def yDir (i : Fin 4) : Space κ := (oscillatorBasis i,0)
def tDir (j : κ) : Space κ := (0,oscillatorBasis j)

def tWeighted (c : ℝ) (e : Jet κ) (p : Space κ) : ℂ :=
  (c*‖p.1‖^2) • (∑ j : κ, e (tDir j) (tDir j) p)

def principal (c : ℝ) (e : Jet κ) (p : Space κ) : ℂ :=
  -(∑ i : Fin 4, e (yDir i) (yDir i) p) - tWeighted c e p

def principalWeight (c : ℝ) : Fin 4 ⊕ κ → Space κ → ℝ
  | .inl _, _ => -1
  | .inr _, p => -(c*‖p.1‖^2)

def diagonalJet (e : Jet κ) : Fin 4 ⊕ κ → Lp ℂ 2 (volume : Measure (Space κ))
  | .inl i => e (yDir i) (yDir i)
  | .inr j => e (tDir j) (tDir j)

theorem principalWeight_continuous (c : ℝ) (i : Fin 4 ⊕ κ) :
    Continuous (principalWeight c i) := by
  cases i with
  | inl i => exact continuous_const
  | inr j =>
    change Continuous (fun p : Space κ => -(c*‖p.1‖^2))
    fun_prop

theorem principal_eq_finite_weighted (c : ℝ) (e : Jet κ) (p : Space κ) :
    principal c e p = ∑ i : Fin 4 ⊕ κ, principalWeight c i p • diagonalJet e i p := by
  simp only [Fintype.sum_sum_type,principalWeight,diagonalJet,neg_smul,one_smul,
    Finset.sum_neg_distrib, ← Finset.smul_sum, principal,tWeighted,sub_eq_add_neg]

theorem principal_ae_smooth (c : ℝ) {G : Space κ → ℂ} {e : Jet κ}
    (he : ∀ v w, (e v w : Space κ → ℂ) =ᵐ[volume]
      (fun p => fderiv ℝ (fun z => fderiv ℝ G z v) p w)) :
    principal c e =ᵐ[volume] euclideanGrushin c G := by
  have hy : ∀ᵐ p ∂volume, ∀ i : Fin 4,
      e (yDir i) (yDir i) p =
        partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis i) p := by
    rw [ae_all_iff]
    intro i
    exact he (yDir i) (yDir i)
  have ht : ∀ᵐ p ∂volume, ∀ j : κ,
      e (tDir j) (tDir j) p =
        partialTDirectional (partialTDirectional G (oscillatorBasis j)) (oscillatorBasis j) p := by
    rw [ae_all_iff]
    intro j
    exact he (tDir j) (tDir j)
  filter_upwards [hy,ht] with p hp hq
  simp only [principal,tWeighted,euclideanGrushin,grushinYLaplacian,grushinTLaplacian,hp,hq]

theorem tWeighted_ae_smooth (c : ℝ) {G : Space κ → ℂ} {e : Jet κ}
    (he : ∀ v w, (e v w : Space κ → ℂ) =ᵐ[volume]
      (fun p => fderiv ℝ (fun z => fderiv ℝ G z v) p w)) :
    tWeighted c e =ᵐ[volume] grushinWeightedT c G := by
  have ht : ∀ᵐ p ∂volume, ∀ j : κ,
      e (tDir j) (tDir j) p =
        partialTDirectional (partialTDirectional G (oscillatorBasis j)) (oscillatorBasis j) p := by
    rw [ae_all_iff]
    intro j
    exact he (tDir j) (tDir j)
  filter_upwards [ht] with p hp
  simp only [tWeighted,grushinWeightedT,grushinTLaplacian,hp]

end TheoremT.Continuum.WeakGrushin
