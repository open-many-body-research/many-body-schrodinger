import ManyBody.S8.Internal.AmbientRealSliceUniqueness
/-! Separation of literal even holomorphic collision profiles.

If H=A+rB agrees on an open connected reflection-invariant complex domain,
and the actual A/B profiles are even in r, comparison at r and -r gives A
agreement and r times the B difference equal to zero. One nonzero-distance
point supplies a genuine open B agreement set; analytic continuation proves
B agreement on the entire domain, including r=0. Physical consumers must
prove actual profile evenness, analyticity, domain symmetry, and H equality.
-/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace ManyBody.S8

def ambientCoordinateReflect (j : Fin 3) (q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun k => if k=j then -q k else q k

@[simp] theorem ambientCoordinateReflect_same (j : Fin 3) (q : Fin 3 → ℂ) :
    ambientCoordinateReflect j q j=-q j := by simp [ambientCoordinateReflect]

theorem holomorphic_even_profiles_compatible
    {a₀ b₀ h₀ a₁ b₁ h₁ : (Fin 3 → ℂ) → ℂ} {U : Set (Fin 3 → ℂ)}
    (j : Fin 3) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hb₀ : AnalyticOnNhd ℂ b₀ U) (hb₁ : AnalyticOnNhd ℂ b₁ U)
    (hreflect : ∀ q∈U, ambientCoordinateReflect j q∈U)
    (hevenA₀ : ∀ q∈U, a₀ (ambientCoordinateReflect j q)=a₀ q)
    (hevenA₁ : ∀ q∈U, a₁ (ambientCoordinateReflect j q)=a₁ q)
    (hevenB₀ : ∀ q∈U, b₀ (ambientCoordinateReflect j q)=b₀ q)
    (hevenB₁ : ∀ q∈U, b₁ (ambientCoordinateReflect j q)=b₁ q)
    (hform₀ : ∀ q∈U, h₀ q=a₀ q+q j*b₀ q)
    (hform₁ : ∀ q∈U, h₁ q=a₁ q+q j*b₁ q)
    (hfull : EqOn h₀ h₁ U) (hbase : ∃ q∈U, q j≠0) :
    EqOn a₀ a₁ U ∧ EqOn b₀ b₁ U := by
  have hplus (q : Fin 3 → ℂ) (hq : q∈U) : a₀ q+q j*b₀ q=a₁ q+q j*b₁ q := by
    rw [←hform₀ q hq,←hform₁ q hq]; exact hfull hq
  have hminus (q : Fin 3 → ℂ) (hq : q∈U) : a₀ q-q j*b₀ q=a₁ q-q j*b₁ q := by
    have hh := hplus (ambientCoordinateReflect j q) (hreflect q hq)
    simpa only [hevenA₀ q hq,hevenA₁ q hq,hevenB₀ q hq,hevenB₁ q hq,
      ambientCoordinateReflect_same,neg_mul,←sub_eq_add_neg] using hh
  have ha (q : Fin 3 → ℂ) (hq : q∈U) : a₀ q=a₁ q := by
    have hp := hplus q hq
    have hm := hminus q hq
    linear_combination (1/2:ℂ)*hp+(1/2:ℂ)*hm
  have hbne (q : Fin 3 → ℂ) (hq : q∈U) (hne : q j≠0) : b₀ q=b₁ q := by
    have hp := hplus q hq
    have ha' := ha q hq
    have hh : q j*(b₀ q-b₁ q)=0 := by linear_combination hp-ha'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hne)
  obtain ⟨q₀,hq₀,hne₀⟩ := hbase
  have hopen : IsOpen {q : Fin 3 → ℂ | q j≠0} :=
    isOpen_compl_singleton.preimage (continuous_apply j)
  have hnear : b₀ =ᶠ[𝓝 q₀] b₁ := by
    filter_upwards [hU.mem_nhds hq₀,hopen.mem_nhds hne₀] with q hq hne
    exact hbne q hq hne
  exact ⟨ha,hb₀.eqOn_of_preconnected_of_eventuallyEq hb₁ hconn hq₀ hnear⟩

#print axioms holomorphic_even_profiles_compatible
end ManyBody.S8