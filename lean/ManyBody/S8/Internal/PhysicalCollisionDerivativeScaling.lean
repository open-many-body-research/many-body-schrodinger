import HomogeneousSpectatorMultiindexDerivative_v1
import ManyBody.S8.Internal.PhysicalCollisionGermRescaling
import ManyBody.S8.Internal.PhysicalComplexDerivativeTransport
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
/-! Exact positive-scale transport of genuine physical Euclidean mixed
coordinate derivatives. A retains its original constant at order zero and
has epsilon^(1-n); B has epsilon^(-n), with no additional epsilon factor.
-/
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

def physicalMultiindexDeriv (f : Position × Position → ℂ)
    (α : Fin 3 ⊕ Fin 3 → ℕ) (p : Position × Position) : ℂ :=
  iteratedFDeriv ℝ (∑ i,α i) f p
    (fun j => physicalCoordinateDirection (multiindexCoordinateWord α j))

def physicalUniformScalingEquiv (a : ℝ) (ha : a≠0) :
    (Position × Position) ≃L[ℝ] (Position × Position) :=
  ContinuousLinearEquiv.equivOfInverse
    (a • ContinuousLinearMap.id ℝ (Position × Position))
    (a⁻¹ • ContinuousLinearMap.id ℝ (Position × Position))
    (by intro p; simp [smul_smul,ha])
    (by intro p; simp [smul_smul,ha])

theorem physical_iteratedFDeriv_inverse_scale
    (f : Position × Position → ℂ) {ε : ℝ} (hε : 0<ε)
    (p : Position × Position) (n : ℕ) (v : Fin n → Position × Position) :
    iteratedFDeriv ℝ n (fun q => f (ε⁻¹ • q)) p v =
      (ε⁻¹)^n • iteratedFDeriv ℝ n f (ε⁻¹ • p) v := by
  let e := physicalUniformScalingEquiv ε⁻¹ (inv_ne_zero hε.ne')
  have he : iteratedFDeriv ℝ n (f ∘ e) p =
      (iteratedFDeriv ℝ n f (e p)).compContinuousLinearMap (fun _ => e.toContinuousLinearMap) := by
    simpa only [Set.preimage_univ,iteratedFDerivWithin_univ] using
      e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (e p)) n
  have hev := congrArg (fun c => c v) he
  change iteratedFDeriv ℝ n (fun q => f (ε⁻¹ • q)) p v =
    iteratedFDeriv ℝ n f (ε⁻¹ • p) (fun j => ε⁻¹ • v j) at hev
  rw [ContinuousMultilinearMap.map_smul_univ] at hev
  simpa using hev

theorem physical_multiindex_inverse_scale
    (f : Position × Position → ℂ) {ε : ℝ} (hε : 0<ε)
    (p : Position × Position) (α : Fin 3 ⊕ Fin 3 → ℕ) :
    physicalMultiindexDeriv (fun q => f (ε⁻¹ • q)) α p =
      (ε⁻¹)^(∑ i,α i) • physicalMultiindexDeriv f α (ε⁻¹ • p) := by
  exact physical_iteratedFDeriv_inverse_scale f hε p _ _

theorem physical_multiindex_rescaled_collision_B
    (b : Position × Position → ℂ) {ε : ℝ} (hε : 0<ε)
    (p : Position × Position) (α : Fin 3 ⊕ Fin 3 → ℕ) :
    physicalMultiindexDeriv (physicalRescaledCollisionB ε b) α p =
      (ε⁻¹)^(∑ i,α i) • physicalMultiindexDeriv b α (ε⁻¹ • p) := by
  exact physical_multiindex_inverse_scale b hε p α

theorem physical_multiindex_rescaled_collision_A
    (a : Position × Position → ℂ) (u0 : ℂ) {ε : ℝ} (hε : 0<ε)
    (p : Position × Position) (α : Fin 3 ⊕ Fin 3 → ℕ)
    (ha : AnalyticAt ℝ a (ε⁻¹ • p)) :
    physicalMultiindexDeriv (physicalRescaledCollisionA ε u0 a) α p =
      (if (∑ i,α i)=0 then u0 else 0)+
      (ε*(ε⁻¹)^(∑ i,α i)) • physicalMultiindexDeriv a α (ε⁻¹ • p) := by
  have hscale : AnalyticAt ℝ (fun q : Position × Position => ε⁻¹ • q) p := by
    have hcst : AnalyticAt ℝ (fun _ : Position × Position => ε⁻¹) p := analyticAt_const
    exact hcst.smul analyticAt_id
  have has : AnalyticAt ℝ (fun q : Position × Position => a (ε⁻¹ • q)) p :=
    AnalyticAt.comp ha hscale
  have hfun : physicalRescaledCollisionA ε u0 a =
      (fun _ : Position × Position => u0)+ε • (fun q => a (ε⁻¹ • q)) := by
    funext q
    simp [physicalRescaledCollisionA,Complex.real_smul]
  have hconst (n : ℕ) (v : Fin n → Position × Position) :
      iteratedFDeriv ℝ n (fun _ : Position × Position => u0) p v =
        if n=0 then u0 else 0 := by
    cases n
    · simp only [ite_true,iteratedFDeriv_zero_apply]
    · simp only [Nat.succ_ne_zero,ite_false,iteratedFDeriv_succ_const,Pi.zero_apply,zero_apply]
  unfold physicalMultiindexDeriv
  rw [hfun,iteratedFDeriv_add_apply (f := fun _ : Position × Position => u0)
    (g := ε • (fun q => a (ε⁻¹ • q))) contDiffAt_const (has.contDiffAt.const_smul ε)]
  rw [iteratedFDeriv_const_smul_apply (a := ε) (f := fun q => a (ε⁻¹ • q)) has.contDiffAt]
  simp only [add_apply,smul_apply]
  rw [physical_iteratedFDeriv_inverse_scale a hε p _ _,smul_smul]
  rw [hconst]

/-- The literal genuine Euclidean coordinate derivative equals the same
    canonical complex coordinate derivative through the actual embedding. -/
theorem physical_multiindex_centered_complex_restriction
    (t0 : Position) {f : (Fin 3 ⊕ Fin 3 → ℂ) → ℂ} {p : Position × Position}
    (hf : AnalyticAt ℂ f (physicalComplexCoordinatesAt t0 p))
    (α : Fin 3 ⊕ Fin 3 → ℕ) :
    physicalMultiindexDeriv (f ∘ physicalComplexCoordinatesAt t0) α p =
      complexMultiindexDeriv f α (physicalComplexCoordinatesAt t0 p) := by
  exact physical_centered_iteratedFDeriv_coordinate_word t0 hf _ (multiindexCoordinateWord α)

#print axioms physical_iteratedFDeriv_inverse_scale
#print axioms physical_multiindex_inverse_scale
#print axioms physical_multiindex_rescaled_collision_B
#print axioms physical_multiindex_rescaled_collision_A
#print axioms physical_multiindex_centered_complex_restriction
end ManyBody.S8
