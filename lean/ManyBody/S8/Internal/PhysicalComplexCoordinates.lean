import ContinuumFoundation_v1
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Tactic
/-! The literal physical coordinate embedding used by descended A/B series.

The input consists of two genuine real Euclidean three-vectors. The output
is the six complex coordinate values with their ordinary finite Pi norm.
The map is real continuous linear, has operator norm at most one, and sends
every physical coordinate unit direction to its literal complex Pi basis.
Spectator centering is the actual affine shift T-t0.
-/
noncomputable section
open scoped Topology
namespace ManyBody.S8
open TheoremT.Continuum

def physicalComplexCoordinatesLinear : (Position × Position) →ₗ[ℝ] (Fin 3 ⊕ Fin 3 → ℂ) where
  toFun p := Sum.elim (fun i => (p.1 i : ℂ)) (fun i => (p.2 i : ℂ))
  map_add' p q := by funext i; cases i <;> simp
  map_smul' a p := by funext i; cases i <;> simp [Complex.real_smul]

def physicalComplexCoordinatesCLM : (Position × Position) →L[ℝ] (Fin 3 ⊕ Fin 3 → ℂ) :=
  physicalComplexCoordinatesLinear.toContinuousLinearMap

@[simp] theorem physicalComplexCoordinatesCLM_inl (p : Position × Position) (i : Fin 3) :
    physicalComplexCoordinatesCLM p (.inl i) = (p.1 i : ℂ) := rfl
@[simp] theorem physicalComplexCoordinatesCLM_inr (p : Position × Position) (i : Fin 3) :
    physicalComplexCoordinatesCLM p (.inr i) = (p.2 i : ℂ) := rfl

theorem physicalComplexCoordinatesCLM_left_norm_le (p : Position × Position) :
    ‖fun i : Fin 3 => physicalComplexCoordinatesCLM p (.inl i)‖ ≤ ‖p.1‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa only [physicalComplexCoordinatesCLM_inl,Complex.norm_real] using PiLp.norm_apply_le p.1 i

theorem physicalComplexCoordinatesCLM_right_norm_le (p : Position × Position) :
    ‖fun i : Fin 3 => physicalComplexCoordinatesCLM p (.inr i)‖ ≤ ‖p.2‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa only [physicalComplexCoordinatesCLM_inr,Complex.norm_real] using PiLp.norm_apply_le p.2 i

theorem physicalComplexCoordinatesCLM_apply_norm_le (p : Position × Position) :
    ‖physicalComplexCoordinatesCLM p‖ ≤ ‖p‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  cases i with
  | inl j =>
    simp only [physicalComplexCoordinatesCLM_inl,Complex.norm_real,Prod.norm_def]
    exact (PiLp.norm_apply_le p.1 j).trans (le_max_left _ _)
  | inr j =>
    simp only [physicalComplexCoordinatesCLM_inr,Complex.norm_real,Prod.norm_def]
    exact (PiLp.norm_apply_le p.2 j).trans (le_max_right _ _)

theorem physicalComplexCoordinatesCLM_norm_le : ‖physicalComplexCoordinatesCLM‖ ≤ 1 := by
  apply physicalComplexCoordinatesCLM.opNorm_le_bound zero_le_one
  intro p
  simpa only [one_mul] using physicalComplexCoordinatesCLM_apply_norm_le p

def physicalComplexCoordinatesAt (t0 : Position) (p : Position × Position) : Fin 3 ⊕ Fin 3 → ℂ :=
  physicalComplexCoordinatesCLM (p.1,p.2-t0)

theorem physicalComplexCoordinatesAt_analytic (t0 : Position) (p : Position × Position) :
    AnalyticAt ℝ (physicalComplexCoordinatesAt t0) p := by
  have hh : AnalyticAt ℝ (fun q : Position × Position => (q.1,q.2-t0)) p :=
    analyticAt_fst.prod (analyticAt_snd.sub analyticAt_const)
  exact AnalyticAt.comp (f := fun q : Position × Position => (q.1,q.2-t0))
    (g := physicalComplexCoordinatesCLM)
    (physicalComplexCoordinatesCLM.analyticAt _) hh

theorem physicalComplexCoordinatesCLM_x_basis (i : Fin 3) :
    physicalComplexCoordinatesCLM (PiLp.single 2 i (1:ℝ),0) = Pi.single (.inl i) (1:ℂ) := by
  funext j
  cases j with
  | inl k => simp [PiLp.single_apply,Pi.single_apply]; split_ifs <;> simp
  | inr k => simp

theorem physicalComplexCoordinatesCLM_t_basis (i : Fin 3) :
    physicalComplexCoordinatesCLM (0,PiLp.single 2 i (1:ℝ)) = Pi.single (.inr i) (1:ℂ) := by
  funext j
  cases j with
  | inl k => simp
  | inr k => simp [PiLp.single_apply,Pi.single_apply]; split_ifs <;> simp

#print axioms physicalComplexCoordinatesCLM_norm_le
#print axioms physicalComplexCoordinatesAt_analytic
#print axioms physicalComplexCoordinatesCLM_x_basis
#print axioms physicalComplexCoordinatesCLM_t_basis
end ManyBody.S8