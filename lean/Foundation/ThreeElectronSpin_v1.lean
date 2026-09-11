import ContinuumFoundation_v1

/-!
The finite spin factor here is exactly the physical spin-1/2 factor of the
continuum Hilbert space, not a replacement Hamiltonian. This obstruction says
that the two-electron "symmetric spatial function times alternating spin
singlet" construction cannot be reused with three electrons.
-/
noncomputable section
namespace TheoremT.Continuum

theorem three_spins_repeat (σ : SpinConfiguration 3) :
    ∃ i j : Fin 3, i ≠ j ∧ σ i = σ j := by
  have h : ¬ Function.Injective σ := by
    intro hinj
    have hc := Fintype.card_le_of_injective σ hinj
    norm_num at hc
  rw [Function.Injective] at h
  push Not at h
  obtain ⟨i, j, heq, hne⟩ := h
  exact ⟨i, j, hne, heq⟩

theorem no_three_electron_alternating_spin
    (a : SpinConfiguration 3 → ℂ)
    (ha : ∀ π σ, a (permuteSpin π σ) = permutationSign π * a σ) :
    a = 0 := by
  funext σ
  obtain ⟨i, j, hne, heq⟩ := three_spins_repeat σ
  have hperm : permuteSpin (Equiv.swap i j) σ = σ := by
    funext k
    by_cases hki : k = i
    · subst k
      simpa [permuteSpin, Function.comp_def] using heq.symm
    · by_cases hkj : k = j
      · subst k
        simpa [permuteSpin, Function.comp_def] using heq
      · simp [permuteSpin, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hs := ha (Equiv.swap i j) σ
  rw [hperm] at hs
  have hsign : permutationSign (Equiv.swap i j) = -1 := by
    simp [permutationSign, Equiv.Perm.sign_swap hne]
  rw [hsign, neg_one_mul] at hs
  change a σ = 0
  linear_combination (1 / 2 : ℂ) * hs

#print axioms three_spins_repeat
#print axioms no_three_electron_alternating_spin

end TheoremT.Continuum
