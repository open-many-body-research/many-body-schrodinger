import WeakGrushinSpectatorDifferentiate_v1

/-! Finite algebra of genuine local weak spectator derivatives.  Each identity
is tested against all real smooth compact tests supported in the displayed
open region.  Local L2 membership is a separate hypothesis, not encoded by an
arbitrary value of the Bochner integral on nonintegrable functions. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def LocalSpectatorD (Ω : Set (Space κ)) (f g : Space κ → ℂ) (j : κ) : Prop :=
  ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ p, φ p • g p) = -(∫ p, fderiv ℝ φ p (tDir j) • f p)

theorem LocalSpectatorD.zero (Ω : Set (Space κ)) (j : κ) :
    LocalSpectatorD Ω (fun _ => 0) (fun _ => 0) j := by
  intro φ _ _ _
  simp

theorem LocalSpectatorD.add {Ω : Set (Space κ)} {f g a b : Space κ → ℂ} {j : κ}
    (hf : ProductLocallyL2On f Ω) (hg : ProductLocallyL2On g Ω)
    (ha : ProductLocallyL2On a Ω) (hb : ProductLocallyL2On b Ω)
    (hd : LocalSpectatorD Ω f a j) (he : LocalSpectatorD Ω g b j) :
    LocalSpectatorD Ω (fun p => f p + g p) (fun p => a p + b p) j := by
  intro φ hφ hc hs
  obtain ⟨hia,hif⟩ := local_spectator_test_integrable f a hf ha (oscillatorBasis j) hφ hc hs
  obtain ⟨hib,hig⟩ := local_spectator_test_integrable g b hg hb (oscillatorBasis j) hφ hc hs
  change Integrable (fun p => fderiv ℝ φ p (tDir j) • f p) at hif
  change Integrable (fun p => fderiv ℝ φ p (tDir j) • g p) at hig
  simp only [smul_add]
  rw [integral_add hia hib, integral_add hif hig, hd φ hφ hc hs, he φ hφ hc hs]
  abel

theorem LocalSpectatorD.neg {Ω : Set (Space κ)} {f a : Space κ → ℂ} {j : κ}
    (hd : LocalSpectatorD Ω f a j) :
    LocalSpectatorD Ω (fun p => -f p) (fun p => -a p) j := by
  intro φ hφ hc hs
  simpa only [smul_neg, integral_neg, neg_neg] using congrArg Neg.neg (hd φ hφ hc hs)

theorem productLocallyL2On_list_sum {ι : Type} {Ω : Set (Space κ)}
    (l : List ι) (f : ι → Space κ → ℂ)
    (hf : ∀ i ∈ l, ProductLocallyL2On (f i) Ω) :
    ProductLocallyL2On (fun p => (l.map (fun i => f i p)).sum) Ω := by
  induction l with
  | nil => intro K hK hs; simp
  | cons i l ih =>
    have hi := hf i (by simp)
    have hl := ih (fun a ha => hf a (by simp [ha]))
    intro K hK hs
    simp only [List.map_cons, List.sum_cons]
    exact (hi K hK hs).add (hl K hK hs)

theorem LocalSpectatorD.list_sum {ι : Type} {Ω : Set (Space κ)} {j : κ}
    (l : List ι) (f a : ι → Space κ → ℂ)
    (hf : ∀ i ∈ l, ProductLocallyL2On (f i) Ω)
    (ha : ∀ i ∈ l, ProductLocallyL2On (a i) Ω)
    (hd : ∀ i ∈ l, LocalSpectatorD Ω (f i) (a i) j) :
    LocalSpectatorD Ω (fun p => (l.map (fun i => f i p)).sum)
      (fun p => (l.map (fun i => a i p)).sum) j := by
  induction l with
  | nil => simpa using LocalSpectatorD.zero Ω j
  | cons i l ih =>
    have hfl : ∀ q ∈ l, ProductLocallyL2On (f q) Ω :=
      fun q hq => hf q (List.mem_cons_of_mem i hq)
    have hal : ∀ q ∈ l, ProductLocallyL2On (a q) Ω :=
      fun q hq => ha q (List.mem_cons_of_mem i hq)
    have hdl : ∀ q ∈ l, LocalSpectatorD Ω (f q) (a q) j :=
      fun q hq => hd q (List.mem_cons_of_mem i hq)
    have hi := LocalSpectatorD.add (hf i (by simp))
      (productLocallyL2On_list_sum l f hfl) (ha i (by simp))
      (productLocallyL2On_list_sum l a hal) (hd i (by simp)) (ih hfl hal hdl)
    simpa using hi

theorem LocalSpectatorD.mono {Ω V : Set (Space κ)} {f a : Space κ → ℂ} {j : κ}
    (hd : LocalSpectatorD Ω f a j) (hV : V ⊆ Ω) : LocalSpectatorD V f a j :=
  fun φ hφ hc hs => hd φ hφ hc (hs.trans hV)

#print axioms LocalSpectatorD.zero
#print axioms LocalSpectatorD.add
#print axioms LocalSpectatorD.neg
#print axioms productLocallyL2On_list_sum
#print axioms LocalSpectatorD.list_sum
#print axioms LocalSpectatorD.mono
end TheoremT.Continuum.WeakGrushin
