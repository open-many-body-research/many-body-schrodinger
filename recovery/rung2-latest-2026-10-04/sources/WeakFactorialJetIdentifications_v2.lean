import WeakFactorialJet_v1
import WeakFactorialJetSupport_v1

/-! Exact low-order coordinate identities for the canonical weak L2 jet.
Permutation symmetry is obtained by the proved compact H2 approximation,
ordinary smooth derivative symmetry, and uniqueness of strong L2 limits.
Original closed-support preservation is imported from the canonical support module.
Version 2 removes the duplicate support declaration from the preserved v1. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem mixedMultiIndexWord_zero_pi : mixedMultiIndexWord 0 0 = [] :=
  mixedMultiIndexWord_zero

theorem weakCoordinateJet_perm
    {f : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    {w z : List (Fin 4 ⊕ Fin 3)} (hwz : w.Perm z) (hw : w.length ≤ 2) :
    weakCoordinateJet f d e w = weakCoordinateJet f d e z := by
  obtain ⟨L,hL,hKL,u,g,dg,eg,hu,huc,hus,hgu,hdu,heu,hgconv,hdconv,heconv⟩ :=
    product_compact_weakH2_uniform_support_approximation d e hd he hK hs
  have hz : z.length ≤ 2 := hwz.length_eq ▸ hw
  have hn (n : ℕ) : weakCoordinateJet (g n) (dg n) (eg n) w =
      weakCoordinateJet (g n) (dg n) (eg n) z := by
    apply Lp.ext
    have hwAE := weakCoordinateJet_ae_smooth (g n) (dg n) (eg n)
      (hgu n) (hdu n) (heu n) w hw
    have hzAE := weakCoordinateJet_ae_smooth (g n) (dg n) (eg n)
      (hgu n) (hdu n) (heu n) z hz
    rw [complexDirectionalWordDeriv_perm productCoordinateDirection (hu n) hwz] at hwAE
    exact hwAE.trans hzAE.symm
  have hwlim := weakCoordinateJet_tendsto hgconv hdconv heconv w
  have hzlim := weakCoordinateJet_tendsto hgconv hdconv heconv z
  have hzlim' : Tendsto (fun n => weakCoordinateJet (g n) (dg n) (eg n) w) atTop
      (𝓝 (weakCoordinateJet f d e z)) := by simpa only [hn] using hzlim
  exact tendsto_nhds_unique hwlim hzlim'

theorem weakFactorialJet_single_y
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (i : Fin 4) : weakFactorialJet f d e (Pi.single i 1) 0 = d (yDir i) := by
  have hp : (mixedMultiIndexWord (Pi.single i 1) 0).Perm [Sum.inl i] := by
    simpa only [zero_add, mixedMultiIndexWord_zero_pi] using mixedMultiIndexWord_add_single_y_perm 0 0 i
  have hw : mixedMultiIndexWord (Pi.single i 1) 0 = [Sum.inl i] := List.perm_singleton.mp hp
  simp only [weakFactorialJet, hw, weakCoordinateJet, productCoordinateDirection]

theorem weakFactorialJet_single_t
    (f : Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (j : Fin 3) : weakFactorialJet f d e 0 (Pi.single j 1) = d (tDir j) := by
  have hp : (mixedMultiIndexWord 0 (Pi.single j 1)).Perm [Sum.inr j] := by
    simpa only [zero_add, mixedMultiIndexWord_zero_pi] using mixedMultiIndexWord_add_single_t_perm 0 0 j
  have hw : mixedMultiIndexWord 0 (Pi.single j 1) = [Sum.inr j] := List.perm_singleton.mp hp
  simp only [weakFactorialJet, hw, weakCoordinateJet, productCoordinateDirection]

theorem weakFactorialJet_double_y
    {f : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) (i j : Fin 4) :
    weakFactorialJet f d e (Pi.single i 1 + Pi.single j 1) 0 = e (yDir i) (yDir j) := by
  have hp : (mixedMultiIndexWord (Pi.single i 1) 0).Perm [Sum.inl i] := by
    simpa only [zero_add, mixedMultiIndexWord_zero_pi] using mixedMultiIndexWord_add_single_y_perm 0 0 i
  have hw := (mixedMultiIndexWord_add_single_y_perm (Pi.single i 1) 0 j).trans (hp.cons (Sum.inl j))
  exact weakCoordinateJet_perm d e hd he hK hs hw (by rw [hw.length_eq]; norm_num)

theorem weakFactorialJet_mixed
    {f : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) (i : Fin 4) (j : Fin 3) :
    weakFactorialJet f d e (Pi.single i 1) (Pi.single j 1) = e (yDir i) (tDir j) := by
  have hp : (mixedMultiIndexWord (Pi.single i 1) 0).Perm [Sum.inl i] := by
    simpa only [zero_add, mixedMultiIndexWord_zero_pi] using mixedMultiIndexWord_add_single_y_perm 0 0 i
  have hw : (mixedMultiIndexWord (Pi.single i 1) (Pi.single j 1)).Perm [Sum.inr j, Sum.inl i] := by
    simpa only [zero_add] using
      (mixedMultiIndexWord_add_single_t_perm (Pi.single i 1) 0 j).trans (hp.cons (Sum.inr j))
  exact weakCoordinateJet_perm d e hd he hK hs hw (by rw [hw.length_eq]; norm_num)

theorem weakFactorialJet_double_t
    {f : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) (i j : Fin 3) :
    weakFactorialJet f d e 0 (Pi.single i 1 + Pi.single j 1) = e (tDir i) (tDir j) := by
  have hp : (mixedMultiIndexWord 0 (Pi.single i 1)).Perm [Sum.inr i] := by
    simpa only [zero_add, mixedMultiIndexWord_zero_pi] using mixedMultiIndexWord_add_single_t_perm 0 0 i
  have hw := (mixedMultiIndexWord_add_single_t_perm 0 (Pi.single i 1) j).trans (hp.cons (Sum.inr j))
  exact weakCoordinateJet_perm d e hd he hK hs hw (by rw [hw.length_eq]; norm_num)

end TheoremT.Continuum.WeakGrushin
