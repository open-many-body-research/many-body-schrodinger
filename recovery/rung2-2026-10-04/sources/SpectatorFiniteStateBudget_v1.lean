import SpectatorIterationState_v1
import SpectatorIterationBudgetScale_v1

/-! Restriction and enlargement of a genuine finite derivative reserve keep
its actual weak witnesses. Joint input budget scaling then gives a common
reference-integral bound for the same witnessed state. -/
noncomputable section
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem SpectatorFiniteState.restrict {Ω O : Set (Space κ)} {f : Space κ → ℂ}
    {m k : ℕ} {W U : ℝ} (hf : SpectatorFiniteState Ω f m W)
    (hO : O ⊆ Ω) (hk : k ≤ m) (hWU : W ≤ U) : SpectatorFiniteState O f k U := by
  obtain ⟨G,gy,hyy,hG0,hG,hD,hY⟩ := hf
  refine ⟨G,gy,hyy,hG0,?_,?_,?_⟩
  · intro w hw
    exact (hG w (hw.trans hk)).restrict hO hWU
  · intro w j hw
    exact (hD w j (hw.trans_le hk)).mono hO
  · intro w hw
    obtain ⟨hy,hyyb,hyD,hyyD⟩ := hY w (hw.trans_le hk)
    exact ⟨hy.trans hWU,hyyb.trans hWU,fun i => (hyD i).mono hO,hyyD⟩

theorem SpectatorFiniteState.mono_budget {Ω : Set (Space κ)} {f : Space κ → ℂ}
    {m : ℕ} {W U : ℝ} (hf : SpectatorFiniteState Ω f m W) (hWU : W ≤ U) :
    SpectatorFiniteState Ω f m U := hf.restrict Set.Subset.rfl le_rfl hWU

theorem SpectatorFiniteState.common_reference_bound
    {Ω : Set (Space κ)} {f : Space κ → ℂ}
    (c : ℝ) (M A B D Q : ℕ → ℝ) (K : ℝ) {H W Hbase Wbase r : ℝ}
    (hc : 0 < c) (hH : H ≤ r*Hbase) (hW : W ≤ r*Wbase) (n : ℕ)
    (hB : ∀ k < n, 0 ≤ B k) (hD : ∀ k < n, 0 ≤ D k) (hQ : ∀ k < n, 0 ≤ Q k)
    (hf : SpectatorFiniteState Ω f n (spectatorIterationBudgetSeq c M A B D Q K H W n)) :
    SpectatorFiniteState Ω f n
      (r * spectatorIterationBudgetSeq c M A B D Q K Hbase Wbase n) :=
  hf.mono_budget (spectatorIterationBudgetSeq_common_bound c M A B D Q K hc hH hW n hB hD hQ)

#print axioms SpectatorFiniteState.restrict
#print axioms SpectatorFiniteState.mono_budget
#print axioms SpectatorFiniteState.common_reference_bound
end TheoremT.Continuum.WeakGrushin
