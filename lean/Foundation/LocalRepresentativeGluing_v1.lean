import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Countable open gluing of locally Lipschitz representatives of one
almost-everywhere function. Pointwise compatibility is proved from open-set
positive measure and continuity. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace TheoremT.Continuum

theorem locally_lipschitz_representatives_glue {X Y : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MetricSpace Y] (μ : Measure X) [μ.IsOpenPosMeasure]
    {U : ℕ → Set X} (hU : ∀ n, IsOpen (U n)) (hcover : ∀ x, ∃ n, x ∈ U n)
    {f : X → Y} {v : ℕ → X → Y} (hv : ∀ n, LocallyLipschitz (v n))
    (hEq : ∀ n, f =ᵐ[μ.restrict (U n)] v n) :
    ∃ u : X → Y, LocallyLipschitz u ∧ f =ᵐ[μ] u := by
  classical
  choose index hindex using hcover
  let u : X → Y := fun x => v (index x) x
  have hcompat (n m : ℕ) : EqOn (v n) (v m) (U n ∩ U m) := by
    have hn : f =ᵐ[μ.restrict (U n ∩ U m)] v n :=
      (hEq n).filter_mono (ae_mono (Measure.restrict_mono_set μ inter_subset_left))
    have hm : f =ᵐ[μ.restrict (U n ∩ U m)] v m :=
      (hEq m).filter_mono (ae_mono (Measure.restrict_mono_set μ inter_subset_right))
    exact μ.eqOn_open_of_ae_eq (hn.symm.trans hm) ((hU n).inter (hU m))
      (hv n).continuous.continuousOn (hv m).continuous.continuousOn
  have huEq (n : ℕ) : EqOn u (v n) (U n) := by
    intro x hx
    exact hcompat (index x) n ⟨hindex x,hx⟩
  refine ⟨u,?_,?_⟩
  · intro x
    obtain ⟨K,T,hT,hLip⟩ := hv (index x) x
    refine ⟨K,T ∩ U (index x),inter_mem hT ((hU (index x)).mem_nhds (hindex x)),?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    rw [huEq (index x) hy.2,huEq (index x) hz.2]
    exact hLip.dist_le_mul y hy.1 z hz.1
  · have hlocal (n : ℕ) : ∀ᵐ x ∂μ, x ∈ U n → f x=v n x := ae_imp_of_ae_restrict (hEq n)
    have hall : ∀ᵐ x ∂μ, ∀ n, x ∈ U n → f x=v n x := ae_all_iff.mpr hlocal
    exact hall.mono (fun x hx => hx (index x) (hindex x))

#print axioms locally_lipschitz_representatives_glue
end TheoremT.Continuum
