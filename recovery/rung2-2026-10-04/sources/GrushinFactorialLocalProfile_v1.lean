import GrushinFactorialBaseIndices_v1
import GrushinFactorialIndexRowBudget_v1
import Mathlib.Data.Finset.Lattice.Fold

/-! The local profile is a finite maximum of actual restricted weighted
L2 norms. The finite-norm predicate is explicit: toReal is not treated as
an L2 norm when the underlying eLpNorm is infinite. Later applications
construct this predicate from genuine finite weak jets on bounded boxes. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

def factorialShiftedWeightedField (D : FactorialRawJetFamily)
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (m : FactorialOuterIndex) : Space (Fin 3) → ℂ :=
  fun p => factorialYMonomial m.2.2 p.1 • D (a+m.1) (b+m.2.1) p

def factorialLocalOuterNorm (D : FactorialRawJetFamily) (Ω : Set (Space (Fin 3)))
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) : ℝ :=
  ∑ m ∈ factorialOuterIndices,
    (eLpNorm (factorialShiftedWeightedField D a b m) 2 (volume.restrict Ω)).toReal

def FactorialLocalMemLp (D : FactorialRawJetFamily) (Ω : Set (Space (Fin 3))) (r : ℕ) : Prop :=
  ∀ a b, factorialMultiDerivativeCost a b ≤ r → ∀ m ∈ factorialOuterIndices,
    MemLp (factorialShiftedWeightedField D a b m) 2 (volume.restrict Ω)

def factorialLocalProfile (D : FactorialRawJetFamily) (Ω : Set (Space (Fin 3))) (r : ℕ) : ℝ :=
  (factorialBaseIndices r).sup' (factorialBaseIndices_nonempty r)
    (fun b => factorialLocalOuterNorm D Ω b.1 b.2)

theorem factorialLocalOuterNorm_nonneg (D : FactorialRawJetFamily) (Ω : Set (Space (Fin 3)))
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) : 0 ≤ factorialLocalOuterNorm D Ω a b :=
  Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)

theorem factorialLocalOuterNorm_le_profile (D : FactorialRawJetFamily) (Ω : Set (Space (Fin 3)))
    (r : ℕ) (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (hab : factorialMultiDerivativeCost a b ≤ r) :
    factorialLocalOuterNorm D Ω a b ≤ factorialLocalProfile D Ω r := by
  exact Finset.le_sup' (fun x : FactorialBaseIndex => factorialLocalOuterNorm D Ω x.1 x.2)
    ((factorialBaseIndices_mem r (a,b)).mpr hab)

theorem factorialLocalProfile_nonneg (D : FactorialRawJetFamily) (Ω : Set (Space (Fin 3))) (r : ℕ) :
    0 ≤ factorialLocalProfile D Ω r :=
  (factorialLocalOuterNorm_nonneg D Ω 0 0).trans
    (factorialLocalOuterNorm_le_profile D Ω r 0 0 (by simp [factorialMultiDerivativeCost,factorialDerivativeCost]))

theorem factorialLocalProfile_mono_order (D : FactorialRawJetFamily) (Ω : Set (Space (Fin 3)))
    {r q : ℕ} (hrq : r ≤ q) : factorialLocalProfile D Ω r ≤ factorialLocalProfile D Ω q := by
  apply Finset.sup'_le
  intro b hb
  exact factorialLocalOuterNorm_le_profile D Ω q b.1 b.2
    (((factorialBaseIndices_mem r b).mp hb).trans hrq)

theorem FactorialLocalMemLp.mono_order {D : FactorialRawJetFamily} {Ω : Set (Space (Fin 3))}
    {r q : ℕ} (h : FactorialLocalMemLp D Ω q) (hrq : r ≤ q) : FactorialLocalMemLp D Ω r :=
  fun a b hab m hm => h a b (hab.trans hrq) m hm

theorem FactorialLocalMemLp.restrict {D : FactorialRawJetFamily} {Ω O : Set (Space (Fin 3))}
    {r : ℕ} (h : FactorialLocalMemLp D Ω r) (hO : O ⊆ Ω) : FactorialLocalMemLp D O r :=
  fun a b hab m hm => (h a b hab m hm).mono_measure (Measure.restrict_mono hO le_rfl)

theorem factorialLocalOuterNorm_mono_domain {D : FactorialRawJetFamily} {Ω O : Set (Space (Fin 3))}
    {r : ℕ} (h : FactorialLocalMemLp D Ω r) (hO : O ⊆ Ω)
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (hab : factorialMultiDerivativeCost a b ≤ r) :
    factorialLocalOuterNorm D O a b ≤ factorialLocalOuterNorm D Ω a b := by
  apply Finset.sum_le_sum
  intro m hm
  exact ENNReal.toReal_mono (h a b hab m hm).2.ne
    (eLpNorm_mono_measure _ (Measure.restrict_mono hO le_rfl))

theorem factorialLocalProfile_mono_domain {D : FactorialRawJetFamily} {Ω O : Set (Space (Fin 3))}
    {r : ℕ} (h : FactorialLocalMemLp D Ω r) (hO : O ⊆ Ω) :
    factorialLocalProfile D O r ≤ factorialLocalProfile D Ω r := by
  apply Finset.sup'_le
  intro b hb
  have hc := (factorialBaseIndices_mem r b).mp hb
  exact (factorialLocalOuterNorm_mono_domain h hO b.1 b.2 hc).trans
    (factorialLocalOuterNorm_le_profile D Ω r b.1 b.2 hc)

end TheoremT.Continuum.WeakGrushin
