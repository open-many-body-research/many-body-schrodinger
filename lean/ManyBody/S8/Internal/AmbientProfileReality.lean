import ManyBody.S8.RealAmbientDistanceDerivativeBudgets
import ManyBody.S8.Internal.ComplexTaylorTruncation
import ManyBody.S8.AmbientCollisionProfileCompatibility
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
/-! Reality of genuine ambient analytic profiles and their real Taylor data.

Real analytic continuation of the imaginary part propagates reality from a
genuine real open neighborhood.  Actual selected-distance parity separates
H=A+rB into real A/B; analyticity propagates B reality through r=0.
Local real values imply reality of every genuine real directional derivative.
The exact scalar-restriction transport then gives real values of the unchanged
canonical complex Taylor coefficients and finite polynomials on real inputs.
Physical consumers must supply the original feasible-configuration identity
and actual state reality, rather than assuming profile reality.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators ContDiff
namespace ManyBody.S8

theorem ambient_real_profile_analytic {f : (Fin 3 → ℂ) → ℂ} {p : Fin 3 → ℝ}
    (hf : AnalyticAt ℂ f (ambientRealCast p)) :
    AnalyticAt ℝ (f ∘ ambientRealCast) p :=
  hf.restrictScalars.comp (ambientRealCast.analyticAt p)

theorem analytic_real_profile_real_of_germ
    {f : (Fin 3 → ℝ) → ℂ} {U : Set (Fin 3 → ℝ)} {a : Fin 3 → ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hconn : IsPreconnected U) (ha : a∈U)
    (hreal : ∀ᶠ p in 𝓝 a, (f p).im=0) :
    ∀ p∈U, (f p).im=0 := by
  have him : AnalyticOnNhd ℝ (fun p => (f p).im) U := by
    intro p hp
    exact (Complex.imCLM.analyticAt (f p)).comp (hf p hp)
  exact him.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn ha hreal

theorem analytic_real_profile_derivative_real
    {f : (Fin 3 → ℝ) → ℂ} {p : Fin 3 → ℝ}
    (hf : AnalyticAt ℝ f p) (hreal : ∀ᶠ q in 𝓝 p, (f q).im=0)
    (n : ℕ) (v : Fin n → (Fin 3 → ℝ)) :
    (iteratedFDeriv ℝ n f p v).im=0 := by
  have heq : (Complex.imCLM ∘ f)=ᶠ[𝓝 p] (fun _ => (0:ℝ)) := hreal
  have hz := (heq.iteratedFDeriv ℝ n).eq_of_nhds
  have hc := Complex.imCLM.iteratedFDeriv_comp_left
    (hf.contDiffAt : ContDiffAt ℝ n f p) (le_refl (n:ℕ∞ω))
  rw [hc] at hz
  have hval := congrArg (fun D => D v) hz
  change (iteratedFDeriv ℝ n f p v).im=
    iteratedFDeriv ℝ n (fun _ : Fin 3 → ℝ => (0:ℝ)) p v at hval
  cases n with
  | zero => simpa using hval
  | succ n => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,zero_apply] using hval

def ambientRealCoordinateReflect (j : Fin 3) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => if k=j then -p k else p k

theorem ambientRealCast_reflect (j : Fin 3) (p : Fin 3 → ℝ) :
    ambientRealCast (ambientRealCoordinateReflect j p)=ambientCoordinateReflect j (ambientRealCast p) := by
  ext k
  by_cases hk : k=j <;> simp [ambientRealCoordinateReflect,ambientCoordinateReflect,hk]

theorem analytic_real_even_profiles_real
    {a b h : (Fin 3 → ℝ) → ℂ} {U : Set (Fin 3 → ℝ)}
    (j : Fin 3) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hb : AnalyticOnNhd ℝ b U)
    (hreflect : ∀ p∈U, ambientRealCoordinateReflect j p∈U)
    (hevenA : ∀ p∈U, a (ambientRealCoordinateReflect j p)=a p)
    (hevenB : ∀ p∈U, b (ambientRealCoordinateReflect j p)=b p)
    (hform : ∀ p∈U, h p=a p+(p j:ℂ)*b p)
    (hfull : ∀ p∈U, (h p).im=0) (hbase : ∃ p∈U, p j≠0) :
    (∀ p∈U, (a p).im=0) ∧ (∀ p∈U, (b p).im=0) := by
  have hplus (p : Fin 3 → ℝ) (hp : p∈U) : (a p).im+p j*(b p).im=0 := by
    have hh := hfull p hp
    simpa only [hform p hp,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,zero_add,add_zero] using hh
  have hminus (p : Fin 3 → ℝ) (hp : p∈U) : (a p).im-p j*(b p).im=0 := by
    have hh := hplus (ambientRealCoordinateReflect j p) (hreflect p hp)
    simpa only [hevenA p hp,hevenB p hp,ambientRealCoordinateReflect,
      ite_true,neg_mul,←sub_eq_add_neg] using hh
  have ha (p : Fin 3 → ℝ) (hp : p∈U) : (a p).im=0 := by
    linarith [hplus p hp,hminus p hp]
  have hbne (p : Fin 3 → ℝ) (hp : p∈U) (hne : p j≠0) : (b p).im=0 := by
    have hh : p j*(b p).im=0 := by linarith [ha p hp,hplus p hp]
    exact (mul_eq_zero.mp hh).resolve_left hne
  obtain ⟨p₀,hp₀,hne₀⟩ := hbase
  have hopen : IsOpen {p : Fin 3 → ℝ | p j≠0} :=
    isOpen_compl_singleton.preimage (continuous_apply j)
  have hnear : ∀ᶠ p in 𝓝 p₀, (b p).im=0 := by
    filter_upwards [hU.mem_nhds hp₀,hopen.mem_nhds hne₀] with p hp hne
    exact hbne p hp hne
  exact ⟨ha,analytic_real_profile_real_of_germ hb hconn hp₀ hnear⟩

#print axioms ambient_real_profile_analytic
#print axioms analytic_real_profile_real_of_germ
#print axioms analytic_real_profile_derivative_real
#print axioms analytic_real_even_profiles_real

theorem analytic_ambient_real_taylor_coefficient
    {f : (Fin 3 → ℂ) → ℂ} {p : Fin 3 → ℝ}
    (hf : AnalyticAt ℂ f (ambientRealCast p))
    (hreal : ∀ᶠ q in 𝓝 p, (f (ambientRealCast q)).im=0)
    (n : ℕ) (h : Fin 3 → ℝ) :
    (complexTaylorCoefficient f (ambientRealCast p) n (ambientRealCast h)).im=0 := by
  have hj := analytic_real_profile_derivative_real (ambient_real_profile_analytic hf) hreal n
    (fun _ => h)
  rw [ambient_real_iteratedFDeriv_complex_restriction hf n] at hj
  have he : ((n.factorial:ℂ)⁻¹)=(((n.factorial:ℝ)⁻¹:ℝ):ℂ) := by simp
  simp only [complexTaylorCoefficient,he,smul_eq_mul,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,hj,mul_zero,zero_mul,add_zero]

def AmbientRealProfileRealityData (f : (Fin 3 → ℂ) → ℂ)
    (U : Set (Fin 3 → ℂ)) : Prop :=
  ∀ p : Fin 3 → ℝ, ambientRealCast p∈U →
    AnalyticAt ℝ (f ∘ ambientRealCast) p ∧ (f (ambientRealCast p)).im=0 ∧
    (∀ n : ℕ, ∀ v : Fin n → (Fin 3 → ℝ),
      (iteratedFDeriv ℝ n (f ∘ ambientRealCast) p v).im=0) ∧
    (∀ n : ℕ, ∀ h : Fin 3 → ℝ,
      (complexTaylorCoefficient f (ambientRealCast p) n (ambientRealCast h)).im=0) ∧
    (∀ N : ℕ, ∀ q : Fin 3 → ℝ,
      (complexTaylorPolynomial f (ambientRealCast p) N (ambientRealCast q)).im=0)

theorem ambient_profile_reality_data_of_real_values
    {f : (Fin 3 → ℂ) → ℂ} {U : Set (Fin 3 → ℂ)}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hreal : ∀ p : Fin 3 → ℝ, ambientRealCast p∈U → (f (ambientRealCast p)).im=0) :
    AmbientRealProfileRealityData f U := by
  intro p hp
  have hnear : ∀ᶠ q in 𝓝 p, (f (ambientRealCast q)).im=0 := by
    filter_upwards [(hU.preimage ambientRealCast.continuous).mem_nhds hp] with q hq
    exact hreal q hq
  refine ⟨ambient_real_profile_analytic (hf _ hp),hreal p hp,
    fun n v => analytic_real_profile_derivative_real (ambient_real_profile_analytic (hf _ hp)) hnear n v,
    fun n h => analytic_ambient_real_taylor_coefficient (hf _ hp) hnear n h,?_⟩
  intro N q
  have he : ambientRealCast q-ambientRealCast p=ambientRealCast (q-p) := (map_sub _ q p).symm
  change Complex.imCLM (∑ n∈Finset.range N,
    complexTaylorCoefficient f (ambientRealCast p) n (ambientRealCast q-ambientRealCast p))=0
  rw [map_sum]
  simp only [he]
  exact Finset.sum_eq_zero fun n hn => analytic_ambient_real_taylor_coefficient (hf _ hp)
    hnear n (q-p)

#print axioms analytic_ambient_real_taylor_coefficient
#print axioms ambient_profile_reality_data_of_real_values

end ManyBody.S8
