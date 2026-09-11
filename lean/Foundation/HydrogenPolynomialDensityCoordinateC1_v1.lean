import HydrogenPolynomialDensityCoordinateC0_v1
import HydrogenPolynomialDensityDifferenceFamily_v1

/-! Uniform convergence of the actual differentiated coordinate Bernstein
operator. The derivative polynomial is formed from genuine forward differences,
and no convergence or polynomial-density hypothesis is assumed. -/

noncomputable section
open scoped Polynomial BigOperators unitInterval
open Set
namespace TheoremT.HydrogenPolynomialDensityCoordinateC1
open TheoremT.HydrogenPolynomialDensity
open TheoremT.HydrogenPolynomialDensityCoordinateC0
open TheoremT.HydrogenPolynomialDensityDifference
open TheoremT.HydrogenPolynomialDensityDifferenceFamily

variable {ι : Type*} [DecidableEq ι]

def ownBernsteinDerivative (n : ℕ) (i : ι) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  (bernsteinCombination n
    (fun k => forwardGridDifference n k (fun t => f (Function.update x i t)))).eval (x i)

/-- The finite difference expression is the actual derivative of the degree
`n+1` coordinate Bernstein operator, even when the sampled input is arbitrary. -/
theorem ownBernsteinDerivative_hasDerivAt (n : ℕ) (i : ι) (f : (ι → ℝ) → ℝ)
    (x : ι → ℝ) :
    HasDerivAt (fun t => coordinateBernstein (n + 1) i f (Function.update x i t))
      (ownBernsteinDerivative n i f x) (x i) := by
  exact coordinateBernstein_own_hasDerivAt n i f x (x i)

/-- Actual slice derivatives within the cube and a continuous derivative field
imply uniform convergence of the differentiated coordinate Bernstein operator. -/
theorem ownBernsteinDerivative_uniform_within [Fintype ι]
    {f g : (ι → ℝ) → ℝ} (hg : Continuous g) (i : ι)
    (hf : ∀ y, inUnitCube y →
      HasDerivWithinAt (fun t => f (Function.update y i t)) (g y) (Icc 0 1) (y i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ x : ι → ℝ, inUnitCube x →
      |ownBernsteinDerivative n i f x - g x| < ε := by
  let F : (ι → I) → ℝ → ℝ := fun y t =>
    f (Function.update (fun j => (y j : ℝ)) i t)
  let G : (ι → I) → ℝ → ℝ := fun y t =>
    g (Function.update (fun j => (y j : ℝ)) i t)
  have hF : ∀ y ∈ (univ : Set (ι → I)), ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (F y) (G y t) (Icc 0 1) t := by
    intro y _ t ht
    have hy : inUnitCube (fun j => (y j : ℝ)) := fun j => (y j).property
    have hd := hf _ (inUnitCube_update hy i ht)
    simpa only [F, G, Function.update_self, Function.update_idem] using hd
  have hG : ContinuousOn (fun p : (ι → I) × ℝ => G p.1 p.2)
      ((univ : Set (ι → I)) ×ˢ Icc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    exact hg.comp (by fun_prop)
  obtain ⟨nd, hnd1, hnd⟩ := forwardSlope_compact_family_uniform
    isCompact_univ hF hG (half_pos hε)
  obtain ⟨nc, hnc⟩ := coordinateBernstein_uniform hg i (half_pos hε)
  refine ⟨max nd nc, hnd1.trans (le_max_left _ _), ?_⟩
  intro n hn x hx
  have hndn : nd ≤ n := (le_max_left _ _).trans hn
  have hncn : nc ≤ n := (le_max_right _ _).trans hn
  let y : ι → I := fun j => ⟨x j, hx j⟩
  have hcoeff (k : ℕ) (hk : k ≤ n) :
      |forwardGridDifference n k (fun t => f (Function.update x i t)) -
        g (Function.update x i ((k : ℝ) / n))| ≤ ε / 2 := by
    have h := hnd n hndn y (mem_univ y) k hk
    simpa only [forwardSlope, forwardGridDifference, F, G, y,
      Nat.cast_add, Nat.cast_one] using h.le
  have hstab := bernsteinCombination_sup_stability n
    (fun k => forwardGridDifference n k (fun t => f (Function.update x i t)))
    (fun k => g (Function.update x i ((k : ℝ) / n))) hcoeff (⟨x i, hx i⟩ : I)
  change |ownBernsteinDerivative n i f x - coordinateBernstein n i g x| ≤ ε / 2 at hstab
  calc
    |ownBernsteinDerivative n i f x - g x|
      ≤ |ownBernsteinDerivative n i f x - coordinateBernstein n i g x| +
          |coordinateBernstein n i g x - g x| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hstab (hnc n hncn x hx)
    _ = ε := by ring

/-- In particular, globally defined actual slice derivatives satisfy the
within-cube hypotheses of the uniform derivative theorem. -/
theorem ownBernsteinDerivative_uniform [Fintype ι]
    {f g : (ι → ℝ) → ℝ} (hg : Continuous g) (i : ι)
    (hf : ∀ y, HasDerivAt (fun t => f (Function.update y i t)) (g y) (y i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ x : ι → ℝ, inUnitCube x →
      |ownBernsteinDerivative n i f x - g x| < ε :=
  ownBernsteinDerivative_uniform_within hg i
    (fun y _ => (hf y).hasDerivWithinAt) hε

end TheoremT.HydrogenPolynomialDensityCoordinateC1

#print axioms TheoremT.HydrogenPolynomialDensityCoordinateC1.ownBernsteinDerivative_hasDerivAt
#print axioms TheoremT.HydrogenPolynomialDensityCoordinateC1.ownBernsteinDerivative_uniform_within
#print axioms TheoremT.HydrogenPolynomialDensityCoordinateC1.ownBernsteinDerivative_uniform
