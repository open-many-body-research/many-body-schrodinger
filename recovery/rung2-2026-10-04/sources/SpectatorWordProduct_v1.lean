import SpectatorWordSplits_v1

/-! The actual ordered Leibniz sum, retaining repeated choices.  Its proper
part is the zeroth-order commutator in the differentiated Grushin equation. -/
noncomputable section
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def spectatorWordProduct (B : Space κ → ℝ)
    (G : List κ → Space κ → ℂ) (w : List κ) (p : Space κ) : ℂ :=
  ((spectatorWordSplits w).map
    (fun ab => spectatorWordDeriv B ab.1 p • G ab.2 p)).sum

def spectatorWordCommutator (B : Space κ → ℝ)
    (G : List κ → Space κ → ℂ) (w : List κ) (p : Space κ) : ℂ :=
  ((spectatorWordProperSplits w).map
    (fun ab => spectatorWordDeriv B ab.1 p • G ab.2 p)).sum

theorem spectatorWordProduct_eq_commutator_add
    (B : Space κ → ℝ) (G : List κ → Space κ → ℂ) (w : List κ) (p : Space κ) :
    spectatorWordProduct B G w p = spectatorWordCommutator B G w p + B p • G w p := by
  simp [spectatorWordProduct, spectatorWordCommutator,
    spectatorWordSplits_eq_proper_append, spectatorWordDeriv]

theorem spectatorWordProduct_cons
    (B : Space κ → ℝ) (G : List κ → Space κ → ℂ) (j : κ)
    (w : List κ) (p : Space κ) :
    spectatorWordProduct B G (j :: w) p =
      ((spectatorWordSplits w).map (fun ab =>
        fderiv ℝ (spectatorWordDeriv B ab.1) p (tDir j) • G ab.2 p +
        spectatorWordDeriv B ab.1 p • G (j :: ab.2) p)).sum := by
  simp only [spectatorWordProduct, spectatorWordSplits, List.map_append,
    List.sum_append, List.map_map, Function.comp_def, spectatorWordDeriv]
  rw [List.sum_map_add]

#print axioms spectatorWordProduct_eq_commutator_add
#print axioms spectatorWordProduct_cons
end TheoremT.Continuum.WeakGrushin
