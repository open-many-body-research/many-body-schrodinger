import CompactCutoffWeakJet_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum

theorem compact_cutoff_weak_laplacian {N : ℕ}
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {f : SpatialL2 N} {d : Coordinate N → SpatialL2 N}
    {e : Coordinate N → Coordinate N → SpatialL2 N}
    (hd : ∀ k, WeakPartial f (d k) k) (he : ∀ k l, WeakPartial (d k) (e k l) l) :
    ∃ u : SpatialL2 N, ∃ a : Coordinate N → SpatialL2 N,
      ∃ b : Coordinate N → Coordinate N → SpatialL2 N,
        (∀ k, WeakPartial u (a k) k) ∧ (∀ k l, WeakPartial (a k) (b k l) l) ∧
        u =ᵐ[volume] (fun x => χ x • f x) ∧
        (∀ k, a k =ᵐ[volume] (fun x => χ x • d k x+fderiv ℝ χ x (coordinateVector k) • f x)) ∧
        (∑ k : Coordinate N, b k k : SpatialL2 N) =ᵐ[volume] (fun x =>
          (χ x : ℂ)*(∑ k, e k k x)+2*(∑ k, (fderiv ℝ χ x (coordinateVector k) : ℂ)*d k x)+
            (realTestLaplacian χ x : ℂ)*f x) := by
  obtain ⟨u,a,b,hua,hab,hu,ha,hb⟩ := compact_cutoff_weak_jet hχ hc hd he
  refine ⟨u,a,b,hua,hab,hu,ha,?_⟩
  have hdiag : ∀ᵐ x ∂volume, ∀ k, b k k x=
      (χ x • e k k x+fderiv ℝ χ x (coordinateVector k) • d k x)+
      (fderiv ℝ χ x (coordinateVector k) • d k x+
        fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector k)) x (coordinateVector k) • f x) := by
    rw [ae_all_iff]
    intro k
    exact hb k k
  filter_upwards [hdiag,Lp.coeFn_fun_finsetSum Finset.univ (fun k => b k k)] with x hx hsum
  rw [hsum]
  simp only [hx,Complex.real_smul,realTestLaplacian,Complex.ofReal_sum,
    Finset.sum_add_distrib]
  rw [← Finset.mul_sum,← Finset.sum_mul]
  ring

#print axioms compact_cutoff_weak_laplacian
end TheoremT.Continuum
