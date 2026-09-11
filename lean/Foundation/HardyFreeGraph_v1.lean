import HardyWeakLaplacian_v1
import WeakPermutation_v2

/-! The positive-shift free Schrödinger graph on the actual weak H² domain. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

def positiveFreeGraph {N : ℕ} (μ : ℝ) (u f : SpatialL2 N) : Prop :=
  ∃ d : Coordinate N → SpatialL2 N, ∃ e : Coordinate N → Coordinate N → SpatialL2 N,
    (∀ k, WeakPartial u (d k) k) ∧ (∀ k l, WeakPartial (d k) (e k l) l) ∧
      f = (-1/2 : ℝ) • (∑ k : Coordinate N, e k k) + μ • u

theorem positiveFreeGraph_hasH2 {N : ℕ} {μ : ℝ} {u f : SpatialL2 N}
    (h : positiveFreeGraph μ u f) : HasH2 u := by
  obtain ⟨d,e,hd,he,_⟩ := h
  exact ⟨d,hd,fun k l => ⟨e k l,he k l⟩⟩

theorem positiveFreeGraph_add {N : ℕ} {μ : ℝ} {u v f g : SpatialL2 N}
    (hu : positiveFreeGraph μ u f) (hv : positiveFreeGraph μ v g) :
    positiveFreeGraph μ (u+v) (f+g) := by
  obtain ⟨du,eu,hdu,heu,hu⟩ := hu
  obtain ⟨dv,ev,hdv,hev,hv⟩ := hv
  refine ⟨fun k => du k+dv k, fun k l => eu k l+ev k l,
    fun k => weakPartial_add (hdu k) (hdv k),
    fun k l => weakPartial_add (heu k l) (hev k l), ?_⟩
  rw [hu,hv,Finset.sum_add_distrib,smul_add,smul_add]
  abel

theorem positiveFreeGraph_smul {N : ℕ} {μ : ℝ} {u f : SpatialL2 N}
    (c : ℂ) (hu : positiveFreeGraph μ u f) : positiveFreeGraph μ (c•u) (c•f) := by
  obtain ⟨d,e,hd,he,hu⟩ := hu
  refine ⟨fun k => c•d k, fun k l => c•e k l,
    fun k => weakPartial_smul c (hd k), fun k l => weakPartial_smul c (he k l), ?_⟩
  rw [hu,smul_add,←Finset.smul_sum,smul_comm c (-1/2:ℝ),smul_comm c μ]

theorem positiveFreeGraph_sub {N : ℕ} {μ : ℝ} {u v f g : SpatialL2 N}
    (hu : positiveFreeGraph μ u f) (hv : positiveFreeGraph μ v g) :
    positiveFreeGraph μ (u-v) (f-g) := by
  simpa only [neg_one_smul,sub_eq_add_neg] using
    positiveFreeGraph_add hu (positiveFreeGraph_smul (-1) hv)

theorem positiveFreeGraph_coercive {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    {u f : SpatialL2 N} (h : positiveFreeGraph μ u f) : μ * ‖u‖ ≤ ‖f‖ := by
  obtain ⟨d,e,hd,he,hout⟩ := h
  have henergy := weak_laplacian_energy_identity d (fun k => e k k) hd (fun k => he k k)
  have hD : 0 ≤ ∑ k : Coordinate N, ‖d k‖^2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hpair : inner ℝ u f = (1/2:ℝ)*(∑ k : Coordinate N, ‖d k‖^2)+μ*‖u‖^2 := by
    rw [hout,inner_add_right,real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    linarith
  have hcs := real_inner_le_norm u f
  by_cases hu : u=0
  · simp [hu]
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  nlinarith

theorem positiveFreeGraph_input_unique {N : ℕ} {μ : ℝ} (hμ : 0 < μ)
    {u v f : SpatialL2 N} (hu : positiveFreeGraph μ u f) (hv : positiveFreeGraph μ v f) : u=v := by
  have hh := positiveFreeGraph_coercive hμ (positiveFreeGraph_sub hu hv)
  rw [sub_self,norm_zero] at hh
  have hn : ‖u-v‖=0 := by nlinarith [norm_nonneg (u-v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

#print axioms positiveFreeGraph_coercive
#print axioms positiveFreeGraph_input_unique
end TheoremT.Continuum
