import CoulombSemibounded_v2
import WeakDomainAlgebra_v2

/-! The genuine H¹ Coulomb quadratic form on the full simultaneous spatial/spin
fermionic space. Its graph uses actual weak derivative and multiplication
witnesses, whose uniqueness is proved. No spectral theorem is assumed. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace TheoremT.Continuum

def h1TargetDomain (N : ℕ) : Set (SpinSpace N) :=
  {ψ | ψ ∈ fermionicSubspace N ∧ ∀ σ, HasH1 (ψ σ)}

def coulombH1Energy {N : ℕ} (ψ : SpinSpace N)
    (d : Coordinate N → SpinSpace N) (v : SpinSpace N) : ℝ :=
  (1 / 2 : ℝ) * (∑ k, ‖d k‖^2) + inner ℝ ψ v

/-- The quadratic-form value on the actual H¹ fermionic domain. The potential
is the original untruncated continuum Coulomb potential, represented in L². -/
def coulombH1FormValue (N : ℕ) (Z : ℝ) (ψ : SpinSpace N) (q : ℝ) : Prop :=
  ψ ∈ fermionicSubspace N ∧
  ∃ d : Coordinate N → SpinSpace N, ∃ v : SpinSpace N,
    (∀ σ k, WeakPartial (ψ σ) (d k σ) k) ∧
    (∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) ∧
    q = coulombH1Energy ψ d v

theorem spin_weak_derivative_unique {N : ℕ} {ψ : SpinSpace N}
    {d d' : Coordinate N → SpinSpace N}
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (hd' : ∀ σ k, WeakPartial (ψ σ) (d' k σ) k) : d = d' := by
  funext k
  apply (WithLp.ext_iff 2).mpr
  funext σ
  exact weakPartial_unique (hd σ k) (hd' σ k)

theorem spin_coulomb_product_unique {N : ℕ} {Z : ℝ} {ψ v v' : SpinSpace N}
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x)
    (hv' : ∀ σ, v' σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) :
    v = v' := by
  apply (WithLp.ext_iff 2).mpr
  funext σ
  exact Lp.ext ((hv σ).trans (hv' σ).symm)

theorem coulombH1FormValue_unique {N : ℕ} {Z : ℝ} {ψ : SpinSpace N} {q q' : ℝ}
    (hq : coulombH1FormValue N Z ψ q) (hq' : coulombH1FormValue N Z ψ q') : q = q' := by
  obtain ⟨_, d, v, hd, hv, rfl⟩ := hq
  obtain ⟨_, d', v', hd', hv', rfl⟩ := hq'
  rw [spin_weak_derivative_unique hd hd', spin_coulomb_product_unique hv hv']

theorem spin_coulomb_product_exists_of_hasH1 {N : ℕ} (Z : ℝ) (ψ : SpinSpace N)
    (hψ : ∀ σ, HasH1 (ψ σ)) :
    ∃ v : SpinSpace N,
      ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x := by
  let hV := fun σ => coulombProductL2_of_hasH1 Z (hψ σ)
  refine ⟨WithLp.toLp 2 (fun σ => (hV σ).toLp _), ?_⟩
  intro σ
  exact (hV σ).coeFn_toLp

theorem coulombH1FormValue_exists_iff {N : ℕ} (Z : ℝ) (ψ : SpinSpace N) :
    (∃ q, coulombH1FormValue N Z ψ q) ↔ ψ ∈ h1TargetDomain N := by
  constructor
  · rintro ⟨q, hferm, d, v, hd, hv, hq⟩
    exact ⟨hferm, fun σ => ⟨fun k => d k σ, hd σ⟩⟩
  · rintro ⟨hferm, hψ⟩
    obtain ⟨v, hv⟩ := spin_coulomb_product_exists_of_hasH1 Z ψ hψ
    choose d hd using hψ
    let ds : Coordinate N → SpinSpace N := fun k => WithLp.toLp 2 (fun σ => d σ k)
    exact ⟨coulombH1Energy ψ ds v, hferm, ds, v, fun σ k => hd σ k, hv, rfl⟩

theorem coulombH1FormValue_existsUnique_iff {N : ℕ} (Z : ℝ) (ψ : SpinSpace N) :
    (∃! q, coulombH1FormValue N Z ψ q) ↔ ψ ∈ h1TargetDomain N := by
  constructor
  · intro h
    exact (coulombH1FormValue_exists_iff Z ψ).mp h.exists
  · intro h
    obtain ⟨q, hq⟩ := (coulombH1FormValue_exists_iff Z ψ).mpr h
    exact ⟨q, hq, fun q' hq' => coulombH1FormValue_unique hq' hq⟩

theorem coulombH1Energy_semibounded {N : ℕ} (Z : ℝ) (ψ : SpinSpace N)
    (d : Coordinate N → SpinSpace N) (v : SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) :
    -(2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)))^2 / 2 * ‖ψ‖^2 ≤
      coulombH1Energy ψ d v := by
  let D : ℝ := ∑ k : Coordinate N, ‖d k‖^2
  let C : ℝ := 2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ))
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ => sq_nonneg ‖d k‖)
  have hV : ‖v‖ ≤ C * Real.sqrt D := coulomb_product_spin_norm_le Z ψ d hd v hv
  have hinner : -(‖ψ‖ * ‖v‖) ≤ inner ℝ ψ v :=
    neg_le_of_abs_le (abs_real_inner_le_norm ψ v)
  have hnorm := mul_le_mul_of_nonneg_left hV (norm_nonneg ψ)
  have hquad := sq_nonneg (Real.sqrt D - C * ‖ψ‖)
  simp only [sub_sq, mul_pow, Real.sq_sqrt hD] at hquad
  change -C^2 / 2 * ‖ψ‖^2 ≤ 1 / 2 * D + inner ℝ ψ v
  nlinarith

/-- Infimum of normalized actual H¹ form values, with no attainment premise. -/
def formGroundEnergy (N : ℕ) (Z : ℝ) : EReal :=
  sInf {e | ∃ ψ : SpinSpace N, ∃ q : ℝ, ‖ψ‖ = 1 ∧
    coulombH1FormValue N Z ψ q ∧ e = (q : EReal)}

#print axioms coulombH1FormValue_existsUnique_iff
#print axioms coulombH1Energy_semibounded

end TheoremT.Continuum
