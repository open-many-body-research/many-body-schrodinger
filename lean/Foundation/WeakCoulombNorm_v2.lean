import WeakCoulombL2_v2
import Mathlib.Data.Finset.Prod

/-! A quantitative actual-L² Coulomb multiplier bound with a deliberately coarse
full-gradient coefficient. The exact finite pair count is N.choose 2. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace TheoremT.Continuum

abbrev StrictElectronPair (N : ℕ) := {q : Fin N × Fin N // q.1 < q.2}

theorem strictElectronPair_card (N : ℕ) : Fintype.card (StrictElectronPair N) = N.choose 2 := by
  rw [Fintype.card_subtype]
  simpa only [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin N))))

theorem strictElectronPair_sum {N : ℕ} (a : Fin N → Fin N → ℂ) :
    (∑ q : StrictElectronPair N, a q.val.1 q.val.2) =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j), a i j := by
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun q : Fin N × Fin N => q.1 < q.2))
    (by simp) (fun q => a q.1 q.2)]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]

theorem finite_toLp_sum_ae {N : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → Configuration N → ℂ) (hu : ∀ a, MemLp (u a) 2 volume) :
    (∑ a : ι, (hu a).toLp (u a)) =ᵐ[volume] fun x => ∑ a : ι, u a x := by
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun a => (hu a).toLp (u a))
  have ha : ∀ᵐ x : Configuration N, ∀ a : ι, (hu a).toLp (u a) x = u a x := by
    rw [ae_all_iff]
    intro a
    exact (hu a).coeFn_toLp
  filter_upwards [hs, ha] with x hx hax
  rw [hx]
  exact Finset.sum_congr rfl (fun a _ => hax a)

theorem norm_toLp_le_two_sqrt_of_integral_sq_le {N : ℕ}
    {u : Configuration N → ℂ} (hu : MemLp u 2 volume) {D : ℝ} (hD : 0 ≤ D)
    (hb : (∫ x, ‖u x‖^2) ≤ 4 * D) :
    ‖hu.toLp u‖ ≤ 2 * Real.sqrt D := by
  have he : ‖hu.toLp u‖^2 = (∫ x, ‖u x‖^2) := by
    rw [spatialL2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with x hx
    rw [hx]
  rw [← he] at hb
  have hs := Real.sq_sqrt hD
  have hsn := Real.sqrt_nonneg D
  nlinarith [norm_nonneg (hu.toLp u)]

theorem nuclear_product_norm_le {N : ℕ} (i : Fin N)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    ‖(weak_nuclear_memLp_two_and_bound i f d hd).1.toLp
        (fun x => f x / (‖position x i‖ : ℂ))‖ ≤
      2 * Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) :=
  norm_toLp_le_two_sqrt_of_integral_sq_le _
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (weak_nuclear_memLp_two_and_bound i f d hd).2

theorem pair_product_norm_le {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    ‖(weak_pair_memLp_two_and_bound i j hij f d hd).1.toLp
        (fun x => f x / (‖position x i - position x j‖ : ℂ))‖ ≤
      2 * Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) :=
  norm_toLp_le_two_sqrt_of_integral_sq_le _
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (weak_pair_memLp_two_and_bound i j hij f d hd).2

/-- Actual L² norm bound; the full-gradient coefficient is
2*(|Z|*N+choose(N,2)). No sharper directional estimate is asserted here. -/
theorem coulomb_product_norm_le {N : ℕ} (Z : ℝ)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (v : SpatialL2 N)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    ‖v‖ ≤ 2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)) *
      Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) := by
  let B : ℝ := Real.sqrt (∑ k : Coordinate N, ‖d k‖^2)
  let nu : Fin N → Configuration N → ℂ := fun i x => f x / (‖position x i‖ : ℂ)
  let pu : StrictElectronPair N → Configuration N → ℂ :=
    fun q x => f x / (‖position x q.val.1 - position x q.val.2‖ : ℂ)
  have hn i : MemLp (nu i) 2 volume := (weak_nuclear_memLp_two_and_bound i f d hd).1
  have hp q : MemLp (pu q) 2 volume :=
    (weak_pair_memLp_two_and_bound q.val.1 q.val.2 (ne_of_lt q.property) f d hd).1
  let ns : SpatialL2 N := ∑ i : Fin N, (hn i).toLp (nu i)
  let ps : SpatialL2 N := ∑ q : StrictElectronPair N, (hp q).toLp (pu q)
  have hnB : ‖ns‖ ≤ (N : ℝ) * (2 * B) := by
    calc
      ‖ns‖ ≤ ∑ i : Fin N, ‖(hn i).toLp (nu i)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin N, 2 * B := Finset.sum_le_sum (fun i _ => nuclear_product_norm_le i f d hd)
      _ = (N : ℝ) * (2 * B) := by simp
  have hpB : ‖ps‖ ≤ (N.choose 2 : ℝ) * (2 * B) := by
    calc
      ‖ps‖ ≤ ∑ q : StrictElectronPair N, ‖(hp q).toLp (pu q)‖ := norm_sum_le _ _
      _ ≤ ∑ q : StrictElectronPair N, 2 * B := Finset.sum_le_sum
        (fun q _ => pair_product_norm_le q.val.1 q.val.2 (ne_of_lt q.property) f d hd)
      _ = (N.choose 2 : ℝ) * (2 * B) := by simp [strictElectronPair_card]
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
    _ ≤ |Z| * ((N : ℝ) * (2 * B)) + (N.choose 2 : ℝ) * (2 * B) :=
      add_le_add (mul_le_mul_of_nonneg_left hnB (abs_nonneg Z)) hpB
    _ = 2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)) * B := by ring

theorem coulomb_toLp_norm_le {N : ℕ} (Z : ℝ)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    ‖(coulombProductL2_of_hasH1 Z ⟨d, hd⟩).toLp
        (fun x => (coulombPotential N Z x : ℂ) * f x)‖ ≤
      2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)) *
        Real.sqrt (∑ k : Coordinate N, ‖d k‖^2) :=
  coulomb_product_norm_le Z f d hd _ (coulombProductL2_of_hasH1 Z ⟨d, hd⟩).coeFn_toLp

#print axioms strictElectronPair_card
#print axioms strictElectronPair_sum
#print axioms finite_toLp_sum_ae
#print axioms norm_toLp_le_two_sqrt_of_integral_sq_le
#print axioms nuclear_product_norm_le
#print axioms pair_product_norm_le
#print axioms coulomb_product_norm_le
#print axioms coulomb_toLp_norm_le

end TheoremT.Continuum
