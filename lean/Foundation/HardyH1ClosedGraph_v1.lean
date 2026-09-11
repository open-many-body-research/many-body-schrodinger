import WeakPartialDistribution_v1
import CoulombH1Form_v1
import FermionicClosed_v1

/-! Closedness of the genuine weak derivative graph and a complete Hilbert
realization of the actual fermionic H¹ space. Values and first derivatives
are recorded together; no second derivative is required. -/
noncomputable section
open MeasureTheory Filter LineDeriv
open scoped Topology SchwartzMap BigOperators
namespace TheoremT.Continuum

theorem weakPartial_graph_isClosed {N : ℕ} (k : Coordinate N) :
    IsClosed {p : SpatialL2 N × SpatialL2 N | WeakPartial p.1 p.2 k} := by
  simp_rw [weakPartial_iff_temperedDistribution_derivative]
  apply isClosed_eq
  · exact (continuous_lineDerivOp (coordinateVector k)).comp
      ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp continuous_fst)
  · exact (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp continuous_snd

theorem WeakPartial.of_tendsto {N : ℕ} {ι : Type*} {l : Filter ι} [NeBot l]
    {f g : ι → SpatialL2 N} {f₀ g₀ : SpatialL2 N} {k : Coordinate N}
    (h : ∀ i, WeakPartial (f i) (g i) k)
    (hf : Tendsto f l (nhds f₀)) (hg : Tendsto g l (nhds g₀)) :
    WeakPartial f₀ g₀ k := by
  exact (weakPartial_graph_isClosed k).mem_of_tendsto (hf.prodMk_nhds hg)
    (Eventually.of_forall h)

abbrev H1GraphAmbient (N : ℕ) :=
  PiLp 2 (fun _ : Option (Coordinate N) => SpinSpace N)

def fermionicH1Graph (N : ℕ) : Submodule ℂ (H1GraphAmbient N) where
  carrier := {a | a none ∈ fermionicSubspace N ∧
    ∀ σ k, WeakPartial (a none σ) (a (some k) σ) k}
  zero_mem' := ⟨(fermionicSubspace N).zero_mem, fun _ k => weakPartial_zero k⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨(fermionicSubspace N).add_mem ha.1 hb.1,
      fun σ k => weakPartial_add (ha.2 σ k) (hb.2 σ k)⟩
  smul_mem' := by
    intro c a ha
    exact ⟨(fermionicSubspace N).smul_mem c ha.1,
      fun σ k => weakPartial_smul c (ha.2 σ k)⟩

theorem fermionicH1Graph_isClosed (N : ℕ) :
    IsClosed (fermionicH1Graph N : Set (H1GraphAmbient N)) := by
  have he (i : Option (Coordinate N)) : Continuous (fun a : H1GraphAmbient N => a i) :=
    PiLp.continuous_apply 2 _ i
  have hes (i : Option (Coordinate N)) (σ : SpinConfiguration N) :
      Continuous (fun a : H1GraphAmbient N => a i σ) :=
    (PiLp.continuous_apply 2 _ σ).comp (he i)
  change IsClosed {a : H1GraphAmbient N | a none ∈ fermionicSubspace N ∧
    ∀ σ k, WeakPartial (a none σ) (a (some k) σ) k}
  rw [Set.setOf_and]
  apply IsClosed.inter ((fermionicSubspace_closed N).preimage (he none))
  simp_rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro σ
  apply isClosed_iInter
  intro k
  exact (weakPartial_graph_isClosed k).preimage
    ((hes none σ).prodMk (hes (some k) σ))

instance fermionicH1Graph_complete (N : ℕ) : CompleteSpace (fermionicH1Graph N) :=
  (fermionicH1Graph_isClosed N).completeSpace_coe

/-- The recorded Hilbert norm is exactly the actual L² value norm plus all
first weak derivative norms; no classical derivative representative is used. -/
theorem fermionicH1Graph_norm_sq {N : ℕ} (a : fermionicH1Graph N) :
    ‖a‖^2 = ‖a.val none‖^2 + ∑ k, ‖a.val (some k)‖^2 := by
  change ‖a.val‖^2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  exact Fintype.sum_option _

theorem fermionicH1Graph_value_mem {N : ℕ} (a : fermionicH1Graph N) :
    a.val none ∈ h1TargetDomain N :=
  ⟨a.property.1, fun σ => ⟨fun k => a.val (some k) σ, a.property.2 σ⟩⟩

theorem fermionicH1Graph_value_injective (N : ℕ) :
    Function.Injective (fun a : fermionicH1Graph N => a.val none) := by
  intro a b hab
  dsimp only at hab
  apply Subtype.ext
  apply (WithLp.ext_iff 2).mpr
  funext i
  cases i with
  | none => exact hab
  | some k =>
    apply (WithLp.ext_iff 2).mpr
    funext σ
    have h := a.property.2 σ k
    rw [hab] at h
    exact weakPartial_unique h (b.property.2 σ k)

theorem fermionicH1Graph_value_range (N : ℕ) :
    Set.range (fun a : fermionicH1Graph N => a.val none) = h1TargetDomain N := by
  ext ψ
  constructor
  · rintro ⟨a, rfl⟩
    exact fermionicH1Graph_value_mem a
  · rintro ⟨hψ, hd⟩
    choose d hd using hd
    let a : H1GraphAmbient N := WithLp.toLp 2
      (fun i => i.elim ψ (fun k => WithLp.toLp 2 (fun σ => d σ k)))
    have ha : a ∈ fermionicH1Graph N := ⟨hψ, hd⟩
    exact ⟨⟨a, ha⟩, rfl⟩

#print axioms weakPartial_graph_isClosed
#print axioms WeakPartial.of_tendsto
#print axioms fermionicH1Graph_isClosed
#print axioms fermionicH1Graph_norm_sq
#print axioms fermionicH1Graph_value_injective
#print axioms fermionicH1Graph_value_range
#synth InnerProductSpace ℂ (fermionicH1Graph 3)
#synth CompleteSpace (fermionicH1Graph 3)
end TheoremT.Continuum
