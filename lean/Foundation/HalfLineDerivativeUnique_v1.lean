import HalfLineWeakGraph_v1

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace TheoremT.HalfLine

def Test.ofReal (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 0) : Test :=
  ⟨Complex.ofRealCLM ∘ φ, Complex.ofRealCLM.contDiff.comp hφ,
    hc.comp_left rfl, (tsupport_comp_subset rfl φ).trans hs⟩

theorem test_separation {u : E} (h : ∀ φ : Test, inner ℂ φ.value u = 0) : u = 0 := by
  have hz := (isOpen_Ioi : IsOpen (Ioi (0:ℝ))).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((Lp.memLp u).locallyIntegrable (by norm_num)).locallyIntegrableOn (Ioi 0)) (by
      intro φ hφ hc hs
      have hp := h (Test.ofReal φ hφ hc hs)
      rw [Test.inner_value] at hp
      simpa [Test.ofReal, Function.comp_apply, Complex.real_smul, mul_comm] using hp)
  apply Lp.ext
  filter_upwards [hz, ae_restrict_mem measurableSet_Ioi, Lp.coeFn_zero ℂ 2 μ] with x hx hxp hx0
  rw [hx hxp, hx0]
  rfl

theorem weak_unique {f d e : E} (hd : Weak f d) (he : Weak f e) : d = e := by
  apply sub_eq_zero.mp
  apply test_separation
  intro φ
  rw [inner_sub_right, hd φ, he φ, sub_self]

theorem J_injective : Function.Injective J := by
  intro u v huv
  apply Subtype.ext
  apply Prod.ext huv
  change dJ u = dJ v
  have h := domain_weak u
  rw [huv] at h
  exact weak_unique h (domain_weak v)

theorem domain_unique_derivative (f : E) :
    ∀ d e : E, (f,d) ∈ domain → (f,e) ∈ domain → d = e := by
  intro d e hd he
  exact weak_unique (domain_weak ⟨(f,d),hd⟩) (domain_weak ⟨(f,e),he⟩)

#print axioms test_separation
#print axioms weak_unique
#print axioms J_injective
#print axioms domain_unique_derivative
end TheoremT.HalfLine
