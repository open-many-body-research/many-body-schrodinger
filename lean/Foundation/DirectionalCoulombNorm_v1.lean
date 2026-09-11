import DirectionalHardy_v1
import ElectronGradientCauchy_v1
import StrictPairIncidence_v1

/-! The specified sqrt(N) Coulomb multiplication coefficient on actual weak H¹.
The proof counts each pair at both endpoints and applies electron Cauchy-Schwarz. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum

theorem coulomb_product_sum_directional_norm_le {N : ℕ} (Z : ℝ)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (v : SpatialL2 N)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    ‖v‖ ≤ (2*|Z| + (N : ℝ) - 1) *
      (∑ i : Fin N, Real.sqrt (∑ k : Fin 3, ‖d (i,k)‖^2)) := by
  let B : Fin N → ℝ := fun i => Real.sqrt (∑ k : Fin 3, ‖d (i,k)‖^2)
  let nu : Fin N → Configuration N → ℂ := fun i x => f x / (‖position x i‖ : ℂ)
  let pu : StrictElectronPair N → Configuration N → ℂ :=
    fun q x => f x / (‖position x q.val.1 - position x q.val.2‖ : ℂ)
  have hn i : MemLp (nu i) 2 volume := (directional_weak_nuclear_memLp_two_and_bound i f d hd).1
  have hp q : MemLp (pu q) 2 volume :=
    (directional_weak_pair_memLp_two_and_bound q.val.1 q.val.2 (ne_of_lt q.property) f d hd).1
  let ns : SpatialL2 N := ∑ i : Fin N, (hn i).toLp (nu i)
  let ps : SpatialL2 N := ∑ q : StrictElectronPair N, (hp q).toLp (pu q)
  have hnB : ‖ns‖ ≤ 2 * (∑ i : Fin N, B i) := by
    calc
      ‖ns‖ ≤ ∑ i : Fin N, ‖(hn i).toLp (nu i)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin N, 2 * B i := Finset.sum_le_sum
        (fun i _ => directional_nuclear_product_norm_le i f d hd)
      _ = 2 * (∑ i : Fin N, B i) := (Finset.mul_sum _ _ _).symm
  have hpB : ‖ps‖ ≤ ((N : ℝ) - 1) * (∑ i : Fin N, B i) := by
    calc
      ‖ps‖ ≤ ∑ q : StrictElectronPair N, ‖(hp q).toLp (pu q)‖ := norm_sum_le _ _
      _ ≤ ∑ q : StrictElectronPair N, (B q.val.1 + B q.val.2) := Finset.sum_le_sum
        (fun q _ => directional_pair_product_norm_le_add q.val.1 q.val.2 (ne_of_lt q.property) f d hd)
      _ = ((N : ℝ) - 1) * (∑ i : Fin N, B i) := strictElectronPair_incidence_sum N B
  have hvsum : v = (-Z : ℂ) • ns + ps := by
    apply Lp.ext
    filter_upwards [hv, Lp.coeFn_add ((-Z : ℂ) • ns) ps,
      Lp.coeFn_smul (-Z : ℂ) ns, finite_toLp_sum_ae nu hn,
      finite_toLp_sum_ae pu hp] with x hx hxa hxs hxn hxp
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxa hxs
    rw [hxa, hxs, hxn, hxp, hx, coulomb_product_eq_sums]
    dsimp only [nu, pu]
    rw [strictElectronPair_sum (fun i j => f x / (‖position x i - position x j‖ : ℂ))]
  rw [hvsum]
  calc
    ‖(-Z : ℂ) • ns + ps‖ ≤ ‖(-Z : ℂ) • ns‖ + ‖ps‖ := norm_add_le _ _
    _ = |Z| * ‖ns‖ + ‖ps‖ := by
      rw [_root_.norm_smul]
      simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |Z| * (2 * (∑ i : Fin N, B i)) + ((N : ℝ) - 1) * (∑ i : Fin N, B i) :=
      add_le_add (mul_le_mul_of_nonneg_left hnB (abs_nonneg Z)) hpB
    _ = (2*|Z| + (N : ℝ) - 1) * (∑ i : Fin N, B i) := by ring

theorem coulomb_product_directional_norm_le {N : ℕ} (Z : ℝ)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (v : SpatialL2 N)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    ‖v‖ ≤ (Real.sqrt (N : ℝ) * (2*|Z| + (N : ℝ) - 1)) *
      Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) :=
  (coulomb_product_sum_directional_norm_le Z f d hd v hv).trans
    (weighted_sum_electron_derivative_norm_le Z d)

theorem coulomb_toLp_directional_norm_le {N : ℕ} (Z : ℝ)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    ‖(coulombProductL2_of_hasH1 Z ⟨d, hd⟩).toLp
        (fun x => (coulombPotential N Z x : ℂ) * f x)‖ ≤
      (Real.sqrt (N : ℝ) * (2*|Z| + (N : ℝ) - 1)) *
        Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) :=
  coulomb_product_directional_norm_le Z f d hd _ (coulombProductL2_of_hasH1 Z ⟨d, hd⟩).coeFn_toLp

/-- The literal continuation-specification coefficient for nonnegative charge. -/
theorem coulomb_product_specification_norm_le {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (v : SpatialL2 N)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    ‖v‖ ≤ (Real.sqrt (N : ℝ) * (2*Z + (N : ℝ) - 1)) *
      Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) := by
  simpa only [abs_of_nonneg hZ] using coulomb_product_directional_norm_le Z f d hd v hv

#print axioms coulomb_product_sum_directional_norm_le
#print axioms coulomb_product_directional_norm_le
#print axioms coulomb_toLp_directional_norm_le
#print axioms coulomb_product_specification_norm_le
end TheoremT.Continuum
