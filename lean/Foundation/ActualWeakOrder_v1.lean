import WeakH1Algebra_v1
import WeakDerivativeEllipticGain_v1

/-! Finite-order weak Sobolev regularity using actual L2 derivative witnesses.
This is an analytic predicate, not an executable method for finding derivatives. -/
noncomputable section
namespace TheoremT.Continuum

def HasWeakOrder {N : ℕ} (f : SpatialL2 N) : ℕ → Prop
  | 0 => True
  | n+1 => ∃ d : Coordinate N → SpatialL2 N,
      (∀ k, WeakPartial f (d k) k) ∧ ∀ k, HasWeakOrder (d k) n

theorem hasWeakOrder_one_iff {N : ℕ} (f : SpatialL2 N) : HasWeakOrder f 1 ↔ HasH1 f := by
  simp only [HasWeakOrder,HasH1]
  constructor
  · rintro ⟨d,hd,_⟩
    exact ⟨d,hd⟩
  · rintro ⟨d,hd⟩
    exact ⟨d,hd,fun _ => trivial⟩

theorem hasWeakOrder_two_iff {N : ℕ} (f : SpatialL2 N) : HasWeakOrder f 2 ↔ HasH2 f := by
  change (∃ d : Coordinate N → SpatialL2 N, (∀ k, WeakPartial f (d k) k) ∧ ∀ k, HasWeakOrder (d k) 1) ↔ _
  simp only [hasWeakOrder_one_iff,HasH1,HasH2]
  constructor
  · rintro ⟨d,hd,he⟩
    refine ⟨d,hd,fun k l => ?_⟩
    obtain ⟨e,he⟩ := he k
    exact ⟨e l,he l⟩
  · rintro ⟨d,hd,he⟩
    refine ⟨d,hd,fun k => ?_⟩
    choose e he using he k
    exact ⟨e,he⟩

theorem HasWeakOrder.pred {N : ℕ} {f : SpatialL2 N} {n : ℕ}
    (hf : HasWeakOrder f (n+1)) : HasWeakOrder f n := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    obtain ⟨d,hd,he⟩ := hf
    exact ⟨d,hd,fun k => ih (he k)⟩

theorem HasWeakOrder.mono {N : ℕ} {f : SpatialL2 N} {n m : ℕ}
    (hf : HasWeakOrder f n) (hmn : m ≤ n) : HasWeakOrder f m := by
  induction hmn with
  | refl => exact hf
  | step h ih => exact ih hf.pred

theorem HasWeakOrder.add {N : ℕ} {f g : SpatialL2 N} {n : ℕ}
    (hf : HasWeakOrder f n) (hg : HasWeakOrder g n) : HasWeakOrder (f+g) n := by
  induction n generalizing f g with
  | zero => trivial
  | succ n ih =>
    obtain ⟨d,hd,hdd⟩ := hf
    obtain ⟨e,he,hee⟩ := hg
    exact ⟨fun k => d k+e k,fun k => weakPartial_add (hd k) (he k),fun k => ih (hdd k) (hee k)⟩

theorem HasWeakOrder.smul {N : ℕ} {f : SpatialL2 N} {n : ℕ}
    (hf : HasWeakOrder f n) (c : ℂ) : HasWeakOrder (c • f) n := by
  induction n generalizing f with
  | zero => trivial
  | succ n ih =>
    obtain ⟨d,hd,he⟩ := hf
    exact ⟨fun k => c • d k,fun k => weakPartial_smul c (hd k),fun k => ih (he k)⟩

#print axioms hasWeakOrder_two_iff
#print axioms HasWeakOrder.mono
end TheoremT.Continuum
