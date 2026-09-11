import ScalarCoulombOperator_v1
import CoulombH1PhysicalEnergy_v1
import CoulombH1GraphEnergy_v1
import CoulombSharpSemibounded_v1

/-! Actual scalar weak-H¹ Coulomb form. The witnesses are genuine weak
derivatives and multiplication by the untruncated continuum potential.
No permutation or spin restriction, eigenfunction, or spectral premise occurs. -/
noncomputable section
open MeasureTheory
open scoped BigOperators LinearPMap
namespace TheoremT.Continuum

def scalarCoulombH1Energy {N : ℕ} (f : SpatialL2 N)
    (d : Coordinate N → SpatialL2 N) (v : SpatialL2 N) : ℝ :=
  (1 / 2 : ℝ) * (∑ k, ‖d k‖^2) + (inner ℂ f v).re

def scalarCoulombH1FormValue (N : ℕ) (Z : ℝ) (f : SpatialL2 N) (q : ℝ) : Prop :=
  ∃ d : Coordinate N → SpatialL2 N, ∃ v : SpatialL2 N,
    (∀ k, WeakPartial f (d k) k) ∧
    (v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) ∧
    q = scalarCoulombH1Energy f d v

theorem scalarCoulombH1FormValue_unique {N : ℕ} {Z : ℝ} {f : SpatialL2 N} {q q' : ℝ}
    (hq : scalarCoulombH1FormValue N Z f q)
    (hq' : scalarCoulombH1FormValue N Z f q') : q = q' := by
  obtain ⟨d,v,hd,hv,rfl⟩ := hq
  obtain ⟨d',v',hd',hv',rfl⟩ := hq'
  have hdd : d = d' := funext (fun k => weakPartial_unique (hd k) (hd' k))
  have hvv : v = v' := Lp.ext (hv.trans hv'.symm)
  rw [hdd,hvv]

theorem scalarCoulombH1FormValue_exists_iff {N : ℕ} (Z : ℝ) (f : SpatialL2 N) :
    (∃ q, scalarCoulombH1FormValue N Z f q) ↔ HasH1 f := by
  constructor
  · rintro ⟨q,d,v,hd,hv,hq⟩
    exact ⟨d,hd⟩
  · intro hf
    have hV := coulombProductL2_of_hasH1 Z hf
    obtain ⟨d,hd⟩ := hf
    let v : SpatialL2 N := hV.toLp _
    exact ⟨scalarCoulombH1Energy f d v,d,v,hd,hV.coeFn_toLp,rfl⟩

theorem scalarCoulombH1FormValue_existsUnique_iff {N : ℕ} (Z : ℝ) (f : SpatialL2 N) :
    (∃! q, scalarCoulombH1FormValue N Z f q) ↔ HasH1 f := by
  constructor
  · intro h
    exact (scalarCoulombH1FormValue_exists_iff Z f).mp h.exists
  · intro hf
    obtain ⟨q,hq⟩ := (scalarCoulombH1FormValue_exists_iff Z f).mpr hf
    exact ⟨q,hq,fun q' hq' => scalarCoulombH1FormValue_unique hq' hq⟩

theorem scalarCoulombH1FormValue_iff_integral {N : ℕ} {Z : ℝ}
    {f : SpatialL2 N} {q : ℝ} :
    scalarCoulombH1FormValue N Z f q ↔
      ∃ d : Coordinate N → SpatialL2 N,
        (∀ k, WeakPartial f (d k) k) ∧
        q = (1 / 2 : ℝ) * (∑ k, ‖d k‖^2) +
          ∫ x, coulombPotential N Z x * ‖f x‖^2 := by
  constructor
  · rintro ⟨d,v,hd,hv,rfl⟩
    refine ⟨d,hd,?_⟩
    unfold scalarCoulombH1Energy
    rw [← spatialL2_real_inner_eq_re, coulomb_potential_energy_eq_integral hv]
  · rintro ⟨d,hd,rfl⟩
    have hV := coulombProductL2_of_hasH1 Z (⟨d,hd⟩ : HasH1 f)
    let v : SpatialL2 N := hV.toLp _
    refine ⟨d,v,hd,hV.coeFn_toLp,?_⟩
    unfold scalarCoulombH1Energy
    rw [← spatialL2_real_inner_eq_re, coulomb_potential_energy_eq_integral hV.coeFn_toLp]

theorem scalarCoulombH1FormValue_potential_integrable {N : ℕ} {Z : ℝ}
    {f : SpatialL2 N} {q : ℝ} (hq : scalarCoulombH1FormValue N Z f q) :
    Integrable (fun x => coulombPotential N Z x * ‖f x‖^2) := by
  obtain ⟨d,v,hd,hv,hq⟩ := hq
  exact coulomb_potential_energy_integrable hv

theorem scalarCoulombH1FormValue_eq_graph_energy {N : ℕ} {Z : ℝ}
    {f h : SpatialL2 N} {q : ℝ} (hq : scalarCoulombH1FormValue N Z f q)
    (hg : scalarHamiltonianGraph N Z f h) : q = (inner ℂ f h).re := by
  obtain ⟨d,v,hd,hv,rfl⟩ := hq
  unfold scalarCoulombH1Energy
  rw [← spatialL2_real_inner_eq_re, ← spatialL2_real_inner_eq_re]
  exact (scalar_graph_energy_identity hg d hd hv).symm

theorem scalarHamiltonianGraph_formValue {N : ℕ} {Z : ℝ}
    {f h : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f h) :
    scalarCoulombH1FormValue N Z f (inner ℂ f h).re := by
  obtain ⟨q,hq⟩ := (scalarCoulombH1FormValue_exists_iff Z f).mpr
    (h2_implies_h1 (scalar_graph_hasH2 hg))
  rw [← scalarCoulombH1FormValue_eq_graph_energy hq hg]
  exact hq

theorem scalarCoulombH1FormValue_sharp_lower_bound {N : ℕ} {Z : ℝ}
    {f : SpatialL2 N} {q : ℝ} (hq : scalarCoulombH1FormValue N Z f q) :
    -(N : ℝ) * (max Z 0)^2 / 2 * ‖f‖^2 ≤ q := by
  obtain ⟨d,v,hd,hv,rfl⟩ := hq
  unfold scalarCoulombH1Energy
  rw [← spatialL2_real_inner_eq_re]
  exact scalar_coulomb_h1_energy_sharp_bound Z f v d hd hv

def scalarFormGroundEnergy (N : ℕ) (Z : ℝ) : EReal :=
  sInf {e | ∃ f : SpatialL2 N, ∃ q : ℝ, ‖f‖ = 1 ∧
    scalarCoulombH1FormValue N Z f q ∧ e = (q : EReal)}

#print axioms scalarCoulombH1FormValue_existsUnique_iff
#print axioms scalarCoulombH1FormValue_iff_integral
#print axioms scalarCoulombH1FormValue_potential_integrable
#print axioms scalarCoulombH1FormValue_eq_graph_energy
#print axioms scalarHamiltonianGraph_formValue
#print axioms scalarCoulombH1FormValue_sharp_lower_bound
end TheoremT.Continuum
