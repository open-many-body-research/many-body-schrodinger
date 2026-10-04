import OpenSmoothCutoff_v1
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
/-! A genuine finite smooth partition on a covered compact physical set.
Actual bounded smooth bumps, compactness and a finite subcover produce
weights with values in [0,1], compact supports subordinate to the prescribed
open physical patches, and sum one on the actual compact set. The telescoping
product construction is literal and requires no assumed partition data. -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped Topology ContDiff BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_open_bounded_smooth_cutoff_at {Ω : Set (Configuration 2)}
    (hΩ : IsOpen Ω) {x : Configuration 2} (hx : x∈Ω) :
    ∃r : ℝ,0<r ∧ ∃χ : Configuration 2 → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ⊆Ω ∧
      (∀y,0≤χ y ∧ χ y≤1) ∧ ∀y∈ball x r,χ y=1 := by
  obtain ⟨ε,hε,hs⟩ := Metric.isOpen_iff.mp hΩ x hx
  let b : ContDiffBump x := ⟨ε/4,ε/2,by positivity,by linarith⟩
  refine ⟨ε/4,by positivity,b,b.contDiff,b.hasCompactSupport,?_,
    (fun _ => ⟨b.nonneg,b.le_one⟩),?_⟩
  · intro y hy
    apply hs
    have hy' : y∈closedBall x b.rOut := by simpa only [b.tsupport_eq] using hy
    change dist y x≤ε/2 at hy'
    exact lt_of_le_of_lt hy' (by linarith)
  · intro y hy
    exact b.one_of_mem_closedBall (ball_subset_closedBall hy)

def physicalFinitePartitionWeight {n : ℕ} (b : Fin n → Configuration 2 → ℝ)
    (i : Fin n) (x : Configuration 2) : ℝ :=
  b i x * ∏ j ∈ (Finset.univ.filter (fun j : Fin n => j < i)),(1-b j x)

theorem physical_finite_partition_sum {n : ℕ} (b : Fin n → Configuration 2 → ℝ)
    {x : Configuration 2} (hx : ∃i,b i x=1) :
    (∑i,physicalFinitePartitionWeight b i x)=1 := by
  obtain ⟨i,hi⟩ := hx
  have hp : (∏j : Fin n,(1-b j x))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi];ring)
  have ht := Finset.prod_one_add_ordered Finset.univ (fun j : Fin n => -b j x)
  simp only [←sub_eq_add_neg,neg_mul,Finset.sum_neg_distrib] at ht
  change (∏j : Fin n,(1-b j x))=1-(∑i,physicalFinitePartitionWeight b i x) at ht
  linarith

theorem physical_finite_smooth_partition_of_compact_cover
    {ι : Type*} {K : Set (Configuration 2)} (hK : IsCompact K)
    (Ω : ι → Set (Configuration 2)) (hΩ : ∀i,IsOpen (Ω i))
    (hcover : ∀x∈K,∃i,x∈Ω i) :
    ∃n : ℕ,∃idx : Fin n → ι,∃ρ : Fin n → Configuration 2 → ℝ,
      (∀i,ContDiff ℝ ∞ (ρ i)) ∧ (∀i,HasCompactSupport (ρ i)) ∧
      (∀i,tsupport (ρ i)⊆Ω (idx i)) ∧
      (∀i x,0≤ρ i x ∧ ρ i x≤1) ∧ (∀x∈K,(∑i,ρ i x)=1) := by
  classical
  choose idx hidx using (fun x : K => hcover x x.property)
  have hbump (x : K) := physical_open_bounded_smooth_cutoff_at (hΩ (idx x)) (hidx x)
  choose r hr b hb hc hs hbounds h1 using hbump
  obtain ⟨s,hsub⟩ := hK.elim_finite_subcover
    (fun x : K => ball (x:Configuration 2) (r x)) (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,by simpa using hr ⟨x,hx⟩⟩)
  let n := Fintype.card ↥s
  let e : ↥s ≃ Fin n := Fintype.equivFin ↥s
  let bs : Fin n → Configuration 2 → ℝ := fun i => b (e.symm i).val
  let js : Fin n → ι := fun i => idx (e.symm i).val
  let ρ := physicalFinitePartitionWeight bs
  have hsmooth (i : Fin n) : ContDiff ℝ ∞ (ρ i) :=
    (hb (e.symm i).val).mul (contDiff_prod (fun j _ => contDiff_const.sub (hb (e.symm j).val)))
  have hcompact (i : Fin n) : HasCompactSupport (ρ i) :=
    (hc (e.symm i).val).mul_right
  have hsupport (i : Fin n) : tsupport (ρ i)⊆Ω (js i) := by
    exact tsupport_mul_subset_left.trans (hs (e.symm i).val)
  have hbound (i : Fin n) (x : Configuration 2) : 0≤ρ i x ∧ ρ i x≤1 := by
    have hbi := hbounds (e.symm i).val x
    have hp0 : 0≤∏ j ∈ (Finset.univ.filter (fun j : Fin n => j < i)),(1-bs j x) :=
      Finset.prod_nonneg (fun j _ => by have := (hbounds (e.symm j).val x).2;dsimp [bs];linarith)
    have hp1 : (∏ j ∈ (Finset.univ.filter (fun j : Fin n => j < i)),(1-bs j x))≤1 := by
      apply Finset.prod_le_one₀
      · intro j _
        have := (hbounds (e.symm j).val x).2
        dsimp [bs]
        linarith
      · intro j _
        have := (hbounds (e.symm j).val x).1
        dsimp [bs]
        linarith
    change 0≤bs i x*∏ j ∈ (Finset.univ.filter (fun j : Fin n => j < i)),(1-bs j x) ∧
      bs i x*∏ j ∈ (Finset.univ.filter (fun j : Fin n => j < i)),(1-bs j x)≤1
    dsimp [bs] at hbi ⊢
    constructor
    · exact mul_nonneg hbi.1 hp0
    · nlinarith
  refine ⟨n,js,ρ,hsmooth,hcompact,hsupport,hbound,?_⟩
  intro x hx
  apply physical_finite_partition_sum
  obtain ⟨y,hys,hxy⟩ := mem_iUnion₂.mp (hsub hx)
  refine ⟨e ⟨y,hys⟩,?_⟩
  simpa only [bs,Equiv.symm_apply_apply] using h1 y x hxy

#print axioms physical_open_bounded_smooth_cutoff_at
#print axioms physical_finite_partition_sum
#print axioms physical_finite_smooth_partition_of_compact_cover
end ManyBody.S8