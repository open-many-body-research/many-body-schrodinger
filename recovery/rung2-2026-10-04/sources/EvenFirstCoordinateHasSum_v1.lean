import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-! Unconditional sums over a product index may discard the zero odd
first-coordinate terms. The retained even-index embedding is explicit;
no ordering of a conditionally convergent numerical series is assumed. -/
set_option autoImplicit false
namespace TheoremT.Continuum

theorem hasSum_even_first_coordinate_iff
    {κ E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {f : ℕ × κ → E} {a : E}
    (hodd : ∀ m γ, f (2*m+1,γ)=0) :
    HasSum (fun q : ℕ × κ => f (2*q.1,q.2)) a ↔ HasSum f a := by
  let e : ℕ × κ → ℕ × κ := fun q => (2*q.1,q.2)
  have hi : Function.Injective e := by
    intro q r h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Prod.ext
    · dsimp [e] at h1
      omega
    · exact h2
  apply hi.hasSum_iff
  rintro ⟨n,γ⟩ hn
  have hnodd : n%2=1 := by
    have hmod := Nat.mod_lt n (by decide : 0<2)
    by_contra h
    have he : 2*(n/2)=n := by omega
    apply hn
    exact ⟨(n/2,γ),Prod.ext he rfl⟩
  have he : 2*(n/2)+1=n := by omega
  rw [← he]
  exact hodd (n/2) γ

theorem hasSum_even_first_coordinate
    {κ E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {f : ℕ × κ → E} {a : E} (hf : HasSum f a)
    (hodd : ∀ m γ, f (2*m+1,γ)=0) :
    HasSum (fun q : ℕ × κ => f (2*q.1,q.2)) a :=
  (hasSum_even_first_coordinate_iff hodd).2 hf

end TheoremT.Continuum
