import ProductWeakFiniteFamilyUnique_v1
import ProductMixedMultiIndexWeakHk_v1

/-! A single genuine all-order weak jet family from finite-order existence.
Different finite choices are identified by local weak uniqueness. Classical
choice constructs mathematical representatives, not an executable algorithm.
No common-in-order norm bound or classical smooth representative is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem product_mixed_allOrder_weak_family
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {f : Space (Fin 3) → ℂ}
    (hreg : ∀ m : ℕ, ∃ W : ℝ, 0 ≤ W ∧ ProductMixedMultiIndexWeakHk Ω f m W) :
    ∃ F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ,
      F 0 0 = f ∧
      (∀ m : ℕ, ∃ W : ℝ, 0 ≤ W ∧ ∀ α β,
        (∑ i,α i)+(∑ j,β j) ≤ m → RegionL2Budget (F α β) Ω W) ∧
      (∀ α β i, ProductLocalWeakDirectional Ω
        (F α β) (F (α+Pi.single i 1) β) (yDir i)) ∧
      (∀ α β j, ProductLocalWeakDirectional Ω
        (F α β) (F α (β+Pi.single j 1)) (tDir j)) := by
  classical
  have hex : ∀ m : ℕ, ∃ (W : ℝ)
      (G : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ),
      0 ≤ W ∧ G 0 0 = f ∧
      (∀ α β, (∑ i,α i)+(∑ j,β j) ≤ m → RegionL2Budget (G α β) Ω W) ∧
      (∀ α β i, (∑ k,α k)+(∑ j,β j) < m →
        ProductLocalWeakDirectional Ω (G α β) (G (α+Pi.single i 1) β) (yDir i)) ∧
      (∀ α β j, (∑ i,α i)+(∑ k,β k) < m →
        ProductLocalWeakDirectional Ω (G α β) (G α (β+Pi.single j 1)) (tDir j)) := by
    intro m
    obtain ⟨W,hW,G,h0,hb,hy,ht⟩ := hreg m
    exact ⟨W,G,hW,h0,hb,hy,ht⟩
  choose W G hW h0 hb hy ht using hex
  let ord := fun (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) => (∑ i,α i)+(∑ j,β j)
  let F := fun α β => G (ord α β) α β
  have hmatch (m : ℕ) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hm : ord α β ≤ m) :
      ∀ᵐ p ∂volume, p ∈ Ω → G m α β p = F α β p := by
    apply product_mixed_multiIndex_weak_families_unique hΩ (G m) (G (ord α β))
      (m := ord α β)
      (Eventually.of_forall (fun p _ => by rw [h0 m,h0 (ord α β)]))
      (fun a b i hab => hy m a b i (lt_of_lt_of_le hab hm))
      (fun a b j hab => ht m a b j (lt_of_lt_of_le hab hm))
      (hy (ord α β)) (ht (ord α β)) α β le_rfl
  refine ⟨F,?_,?_,?_,?_⟩
  · simpa only [F,ord,Pi.zero_apply,Finset.sum_const_zero,Nat.zero_add] using h0 0
  · intro m
    refine ⟨W m,hW m,?_⟩
    intro α β hab
    apply (hb m α β hab).congr_ae
    exact (ae_restrict_iff' hΩ.measurableSet).2 (hmatch m α β hab)
  · intro α β i
    have hs : ord (α+Pi.single i 1) β = ord α β+1 := by
      simp only [ord,Pi.add_apply,Finset.sum_add_distrib,Finset.sum_pi_single',
        Finset.mem_univ,ite_true]
      omega
    exact (hy (ord α β+1) α β i (by dsimp [ord]; omega)).congr_ae_local
      (hmatch _ α β (by omega)) (hmatch _ _ _ (by rw [hs]))
  · intro α β j
    have hs : ord α (β+Pi.single j 1) = ord α β+1 := by
      simp only [ord,Pi.add_apply,Finset.sum_add_distrib,Finset.sum_pi_single',
        Finset.mem_univ,ite_true]
      omega
    exact (ht (ord α β+1) α β j (by dsimp [ord]; omega)).congr_ae_local
      (hmatch _ α β (by omega)) (hmatch _ _ _ (by rw [hs]))

theorem local_smooth_weak_grushin_allOrder_family
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    (a : Space (Fin 3)) {aY aT bY bT c : ℝ}
    (hby : 0 < bY) (hbt : 0 < bT) (hy : bY < aY) (ht : bT < aT)
    (hKΩ : rectangularClosedBox a aY aT ⊆ Ω) (hc : 0 < c)
    {B : Space (Fin 3) → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {s : Space (Fin 3) → ℂ} (hs : ContDiffOn ℝ ∞ s Ω)
    {f : Space (Fin 3) → ℂ} (hf : ProductLocallyL2On f Ω)
    (hEq : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p,φ p • s p) :
    ∃ F : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Space (Fin 3) → ℂ,
      F 0 0 = f ∧
      (∀ m : ℕ, ∃ W : ℝ, 0 ≤ W ∧ ∀ α β,
        (∑ i,α i)+(∑ j,β j) ≤ m →
          RegionL2Budget (F α β) (rectangularOpenBox a bY bT) W) ∧
      (∀ α β i, ProductLocalWeakDirectional (rectangularOpenBox a bY bT)
        (F α β) (F (α+Pi.single i 1) β) (yDir i)) ∧
      (∀ α β j, ProductLocalWeakDirectional (rectangularOpenBox a bY bT)
        (F α β) (F α (β+Pi.single j 1)) (tDir j)) :=
  product_mixed_allOrder_weak_family (rectangularOpenBox_isOpen a bY bT)
    (fun m => local_smooth_weak_grushin_mixed_multiIndex_regularity
      hΩ a hby hbt hy ht hKΩ hc hB hs hf hEq m)

end TheoremT.Continuum.WeakGrushin
