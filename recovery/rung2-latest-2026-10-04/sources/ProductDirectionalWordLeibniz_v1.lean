import LocalProductDirectionalWeakLinear_v1
import SpectatorWordSplits_v1

/-! Finite ordered weak Leibniz calculus in supplied constant directions.
The list of splits retains every choice, including repetitions. Coefficients
are smooth only on the displayed open set, and solution derivatives are
supplied only through the finite order used by each identity. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem ProductLocalWeakDirectional.list_sum
    {ι : Type*} {Ω : Set (Y × T)} {v : Y × T}
    (l : List ι) (f d : ι → Y × T → ℂ)
    (hD : ∀ i ∈ l, ProductLocalWeakDirectional Ω (f i) (d i) v) :
    ProductLocalWeakDirectional Ω (fun p => (l.map (fun i => f i p)).sum)
      (fun p => (l.map (fun i => d i p)).sum) v := by
  induction l with
  | nil => simpa using ProductLocalWeakDirectional.zero Ω v
  | cons i l ih =>
    have hI := hD i (by simp)
    have hL := ih (fun j hj => hD j (List.mem_cons_of_mem i hj))
    simpa only [List.map_cons,List.sum_cons] using hI.add hL

theorem productLocallyL2On_list_sum
    {ι : Type*} {Ω : Set (Y × T)} (l : List ι) (f : ι → Y × T → ℂ)
    (hf : ∀ i ∈ l, ProductLocallyL2On (f i) Ω) :
    ProductLocallyL2On (fun p => (l.map (fun i => f i p)).sum) Ω := by
  induction l with
  | nil => intro K _ _; simp
  | cons i l ih =>
    have hI := hf i (by simp)
    have hL := ih (fun j hj => hf j (List.mem_cons_of_mem i hj))
    intro K hK hs
    simp only [List.map_cons,List.sum_cons]
    exact (hI K hK hs).add (hL K hK hs)

def directionalWordDeriv {ι : Type} (dirs : ι → Y × T) (B : Y × T → ℝ) :
    List ι → Y × T → ℝ
  | [] => B
  | j :: w => fun p => fderiv ℝ (directionalWordDeriv dirs B w) p (dirs j)

theorem directionalWordDeriv_contDiffOn {ι : Type} (dirs : ι → Y × T)
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) (w : List ι) :
    ContDiffOn ℝ ∞ (directionalWordDeriv dirs B w) Ω := by
  induction w with
  | nil => exact hB
  | cons j w ih =>
    intro p hp
    exact (local_contDiffAt_directional_derivative
      (ih.contDiffAt (hΩ.mem_nhds hp)) (dirs j)).contDiffWithinAt

def directionalWordProduct {ι : Type} (dirs : ι → Y × T) (B : Y × T → ℝ)
    (G : List ι → Y × T → ℂ) (w : List ι) (p : Y × T) : ℂ :=
  ((spectatorWordSplits w).map
    (fun ab => directionalWordDeriv dirs B ab.1 p • G ab.2 p)).sum

theorem directionalWordProduct_nil {ι : Type} (dirs : ι → Y × T) (B : Y × T → ℝ)
    (G : List ι → Y × T → ℂ) (p : Y × T) :
    directionalWordProduct dirs B G [] p = B p • G [] p := by
  simp [directionalWordProduct,spectatorWordSplits,directionalWordDeriv]

theorem directionalWordProduct_cons {ι : Type} (dirs : ι → Y × T) (B : Y × T → ℝ)
    (G : List ι → Y × T → ℂ) (j : ι) (w : List ι) (p : Y × T) :
    directionalWordProduct dirs B G (j :: w) p =
      ((spectatorWordSplits w).map (fun ab =>
        fderiv ℝ (directionalWordDeriv dirs B ab.1) p (dirs j) • G ab.2 p +
        directionalWordDeriv dirs B ab.1 p • G (j :: ab.2) p)).sum := by
  simp only [directionalWordProduct,spectatorWordSplits,List.map_append,
    List.sum_append,List.map_map,Function.comp_def,directionalWordDeriv]
  rw [List.sum_map_add]

theorem directionalWordProduct_locallyL2 {ι : Type} (dirs : ι → Y × T)
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ} (G : List ι → Y × T → ℂ)
    (hG : ∀ w, w.length ≤ m → ProductLocallyL2On (G w) Ω)
    (w : List ι) (hw : w.length ≤ m) :
    ProductLocallyL2On (directionalWordProduct dirs B G w) Ω := by
  apply productLocallyL2On_list_sum
  intro ab hab
  have hn := spectatorWordSplits_length_sum hab
  exact product_smooth_coefficient_locallyL2_raw hΩ
    (directionalWordDeriv_contDiffOn dirs hΩ hB ab.1) (hG ab.2 (by omega))

theorem directionalWordProduct_localD {ι : Type} (dirs : ι → Y × T)
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {B : Y × T → ℝ}
    (hB : ContDiffOn ℝ ∞ B Ω) {m : ℕ} (G : List ι → Y × T → ℂ)
    (hD : ∀ w j, w.length < m →
      ProductLocalWeakDirectional Ω (G w) (G (j :: w)) (dirs j))
    (w : List ι) (j : ι) (hw : w.length < m) :
    ProductLocalWeakDirectional Ω (directionalWordProduct dirs B G w)
      (directionalWordProduct dirs B G (j :: w)) (dirs j) := by
  let f := fun ab : List ι × List ι => fun p : Y × T =>
    directionalWordDeriv dirs B ab.1 p • G ab.2 p
  let a := fun ab : List ι × List ι => fun p : Y × T =>
    directionalWordDeriv dirs B ab.1 p • G (j :: ab.2) p +
      fderiv ℝ (directionalWordDeriv dirs B ab.1) p (dirs j) • G ab.2 p
  have hL (ab : List ι × List ι) (hab : ab ∈ spectatorWordSplits w) :
      ProductLocalWeakDirectional Ω (f ab) (a ab) (dirs j) := by
    have hn := spectatorWordSplits_length_sum hab
    have hb : ab.2.length < m := by omega
    exact (hD ab.2 j hb).smooth_smul hΩ (directionalWordDeriv_contDiffOn dirs hΩ hB ab.1)
  have hs := ProductLocalWeakDirectional.list_sum (spectatorWordSplits w) f a hL
  have he : (fun p => ((spectatorWordSplits w).map (fun ab => a ab p)).sum) =
      directionalWordProduct dirs B G (j :: w) := by
    funext p
    rw [directionalWordProduct_cons]
    simp only [a,add_comm]
  rw [he] at hs
  exact hs

end TheoremT.Continuum
