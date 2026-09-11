import ContinuumFoundation_v1

/-!
Exact native dictionary as a subspace of functions on the actual R^6.
The factorial convention and single diagonal monomial agree with the frozen
RATE_DICTIONARY_DECISION.md. Dyadic normalization does not alter the span;
the canonical normalization algorithm and its bit cost are not proved here.
No claim of L2/H2 membership is made merely by defining these functions.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Dictionary
open TheoremT.Continuum

def radius1 (x : Configuration 2) : ℝ := ‖position x 0‖
def radius2 (x : Configuration 2) : ℝ := ‖position x 1‖
def separation (x : Configuration 2) : ℝ := ‖position x 0 - position x 1‖
def totalRadius (x : Configuration 2) : ℝ := radius1 x + radius2 x

def exchange (x : Configuration 2) : Configuration 2 :=
  permuteSpace (Equiv.swap (0 : Fin 2) 1) x

theorem position_exchange_zero (x : Configuration 2) :
    position (exchange x) 0 = position x 1 := by
  ext k
  simp [position, exchange, permuteSpace_apply]

theorem position_exchange_one (x : Configuration 2) :
    position (exchange x) 1 = position x 0 := by
  ext k
  simp [position, exchange, permuteSpace_apply]

theorem distances_exchange (x : Configuration 2) :
    radius1 (exchange x) = radius2 x ∧ radius2 (exchange x) = radius1 x ∧
      separation (exchange x) = separation x := by
  simp only [radius1, radius2, separation, position_exchange_zero, position_exchange_one]
  exact ⟨trivial, trivial, norm_sub_rev _ _⟩

def symmetricMonomial (i h k : ℕ) (x : Configuration 2) : ℝ :=
  (if i = h then radius1 x ^ i * radius2 x ^ h
    else radius1 x ^ i * radius2 x ^ h + radius1 x ^ h * radius2 x ^ i) *
      separation x ^ k / (Nat.factorial (i + h + k) : ℝ)

def generator (Z : ℝ) (j i h k : ℕ) (x : Configuration 2) : ℝ :=
  Real.exp (-Z * 2 ^ j * totalRadius x) * symmetricMonomial i h k x

def exactDictionary (Z : ℝ) (n : ℕ) : Submodule ℝ (Configuration 2 → ℝ) :=
  Submodule.span ℝ {f | ∃ j i h k : ℕ,
    h ≤ i ∧ 2 * j + i + h + k ≤ n ∧ f = generator Z j i h k}

theorem exact_dictionary_nested (Z : ℝ) {n m : ℕ} (hn : n ≤ m) :
    exactDictionary Z n ≤ exactDictionary Z m := by
  apply Submodule.span_mono
  rintro f ⟨j, i, h, k, hhi, hdegree, rfl⟩
  exact ⟨j, i, h, k, hhi, hdegree.trans hn, rfl⟩

theorem generator_exchange (Z : ℝ) (j i h k : ℕ) (x : Configuration 2) :
    generator Z j i h k (exchange x) = generator Z j i h k x := by
  obtain ⟨hr, hs, hu⟩ := distances_exchange x
  simp only [generator, totalRadius, symmetricMonomial, hr, hs, hu]
  rw [add_comm (radius2 x) (radius1 x)]
  congr 1
  by_cases hi : i = h
  · subst h
    simp only [ite_true]
    ring
  · simp only [ite_eq_right hi]
    ring

theorem dictionary_exchange {Z : ℝ} {n : ℕ} {f : Configuration 2 → ℝ}
    (hf : f ∈ exactDictionary Z n) (x : Configuration 2) :
    f (exchange x) = f x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, i, h, k, _, _, rfl⟩ := hf
    exact generator_exchange Z j i h k x
  | zero => rfl
  | add f g hf hg ihf ihg => exact congrArg₂ (· + ·) ihf ihg
  | smul a f hf ih => exact congrArg (a * ·) ih

/-- The unit spin-singlet formula in the usual up/down basis. -/
def singlet (σ : SpinConfiguration 2) : ℂ :=
  if σ 0 = 0 ∧ σ 1 = 1 then (Real.sqrt 2 : ℂ)⁻¹
  else if σ 0 = 1 ∧ σ 1 = 0 then -(Real.sqrt 2 : ℂ)⁻¹ else 0

/-- Honest lifting into the continuum L2 space: equality is almost everywhere.
This definition does not automatically assert the existence of such a lift. -/
def trialDictionary (Z : ℝ) (n : ℕ) : Set (SpinSpace 2) :=
  {ψ | ∃ f ∈ exactDictionary Z n, ∀ σ,
    (fun x => (ψ σ) x) =ᵐ[volume] (fun x => (f x : ℂ) * singlet σ)}

theorem trial_dictionary_nested (Z : ℝ) {n m : ℕ} (hn : n ≤ m) :
    trialDictionary Z n ⊆ trialDictionary Z m := by
  rintro ψ ⟨f, hf, hψ⟩
  exact ⟨f, exact_dictionary_nested Z hn hf, hψ⟩

#print axioms distances_exchange
#print axioms exact_dictionary_nested
#print axioms generator_exchange
#print axioms dictionary_exchange
#print axioms trial_dictionary_nested

end TheoremT.Dictionary
