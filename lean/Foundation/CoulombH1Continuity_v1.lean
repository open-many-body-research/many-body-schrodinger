import CoulombH1Form_v1

/-! Continuity of the physical Coulomb form along genuine H¹ convergence.
No H² approximation or spectral assertion is assumed by these lemmas. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace TheoremT.Continuum

theorem weakPartial_sub_h1 {N : ℕ} {f g df dg : SpatialL2 N} {k : Coordinate N}
    (hf : WeakPartial f df k) (hg : WeakPartial g dg k) :
    WeakPartial (f - g) (df - dg) k := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    weakPartial_add hf (weakPartial_smul (-1 : ℂ) hg)

theorem spin_coulomb_product_sub {N : ℕ} {Z : ℝ} {ψ φ v w : SpinSpace N}
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x)
    (hw : ∀ σ, w σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * φ σ x) :
    ∀ σ, (v - w) σ =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ) * (ψ - φ) σ x := by
  intro σ
  change (v σ - w σ : SpatialL2 N) =ᵐ[volume]
    fun x => (coulombPotential N Z x : ℂ) * (ψ σ - φ σ : SpatialL2 N) x
  filter_upwards [hv σ, hw σ, Lp.coeFn_sub (v σ) (w σ),
    Lp.coeFn_sub (ψ σ) (φ σ)] with x hvx hwx hx hpx
  simp only [Pi.sub_apply] at hx hpx
  rw [hx, hpx, hvx, hwx, mul_sub]

theorem spin_coulomb_product_tendsto {N : ℕ} (Z : ℝ)
    (ψn : ℕ → SpinSpace N) (ψ : SpinSpace N)
    (dn : ℕ → Coordinate N → SpinSpace N) (d : Coordinate N → SpinSpace N)
    (vn : ℕ → SpinSpace N) (v : SpinSpace N)
    (hdn : ∀ n σ k, WeakPartial (ψn n σ) (dn n k σ) k)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (hvn : ∀ n σ, vn n σ =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ) * ψn n σ x)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x)
    (hdt : ∀ k, Tendsto (fun n => dn n k) atTop (𝓝 (d k))) :
    Tendsto vn atTop (𝓝 v) := by
  have hD : Tendsto (fun n => ∑ k : Coordinate N, ‖dn n k - d k‖^2)
      atTop (𝓝 0) := by
    have hh := tendsto_finset_sum Finset.univ (fun k _ =>
      (((hdt k).sub_const (d k)).norm.pow 2))
    simpa using hh
  have hs : Tendsto (fun n =>
      (2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ))) *
        Real.sqrt (∑ k : Coordinate N, ‖dn n k - d k‖^2)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hD).const_mul
      (2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)))
  have hsub : Tendsto (fun n => vn n - v) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hs
    exact coulomb_product_spin_norm_le Z (ψn n - ψ) (fun k => dn n k - d k)
      (fun σ k => weakPartial_sub_h1 (hdn n σ k) (hd σ k)) (vn n - v)
      (spin_coulomb_product_sub (hvn n) hv)
  simpa only [sub_add_cancel, zero_add] using hsub.add_const v

theorem coulombH1Energy_tendsto {N : ℕ} (Z : ℝ)
    (ψn : ℕ → SpinSpace N) (ψ : SpinSpace N)
    (dn : ℕ → Coordinate N → SpinSpace N) (d : Coordinate N → SpinSpace N)
    (vn : ℕ → SpinSpace N) (v : SpinSpace N)
    (hdn : ∀ n σ k, WeakPartial (ψn n σ) (dn n k σ) k)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (hvn : ∀ n σ, vn n σ =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ) * ψn n σ x)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x)
    (hψt : Tendsto ψn atTop (𝓝 ψ))
    (hdt : ∀ k, Tendsto (fun n => dn n k) atTop (𝓝 (d k))) :
    Tendsto (fun n => coulombH1Energy (ψn n) (dn n) (vn n))
      atTop (𝓝 (coulombH1Energy ψ d v)) := by
  have hD := tendsto_finset_sum Finset.univ (fun k _ => (hdt k).norm.pow 2)
  have hV := spin_coulomb_product_tendsto Z ψn ψ dn d vn v hdn hd hvn hv hdt
  exact (hD.const_mul (1 / 2 : ℝ)).add (hψt.inner hV)

#print axioms spin_coulomb_product_tendsto
#print axioms coulombH1Energy_tendsto

end TheoremT.Continuum
