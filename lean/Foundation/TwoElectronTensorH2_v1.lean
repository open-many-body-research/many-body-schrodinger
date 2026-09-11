import TwoElectronTensorWeak_v1

/-! Products of actual weak Sobolev functions, including all mixed second derivatives. -/
noncomputable section
namespace TheoremT.Continuum

def twoElectronTensorGradient (f g : SpatialL2 1)
    (df dg : Coordinate 1 → SpatialL2 1) (k : Coordinate 2) : SpatialL2 2 :=
  if k.1 = 0 then twoElectronTensor (df (0,k.2)) g
    else twoElectronTensor f (dg (0,k.2))

theorem twoElectronTensorGradient_weak (f g : SpatialL2 1)
    (df dg : Coordinate 1 → SpatialL2 1)
    (hf : ∀ k, WeakPartial f (df k) k) (hg : ∀ k, WeakPartial g (dg k) k)
    (k : Coordinate 2) :
    WeakPartial (twoElectronTensor f g) (twoElectronTensorGradient f g df dg k) k := by
  rcases k with ⟨i,k⟩
  fin_cases i
  · simpa [twoElectronTensorGradient] using twoElectronTensor_weakPartial_first g k (hf (0,k))
  · simpa [twoElectronTensorGradient] using twoElectronTensor_weakPartial_second f k (hg (0,k))

theorem twoElectronTensor_hasH1 {f g : SpatialL2 1} (hf : HasH1 f) (hg : HasH1 g) :
    HasH1 (twoElectronTensor f g) := by
  obtain ⟨df,hf⟩ := hf
  obtain ⟨dg,hg⟩ := hg
  exact ⟨twoElectronTensorGradient f g df dg,twoElectronTensorGradient_weak f g df dg hf hg⟩

theorem twoElectronTensor_hasH2 {f g : SpatialL2 1} (hf : HasH2 f) (hg : HasH2 g) :
    HasH2 (twoElectronTensor f g) := by
  obtain ⟨df,hf,hef⟩ := hf
  obtain ⟨dg,hg,heg⟩ := hg
  refine ⟨twoElectronTensorGradient f g df dg,
    twoElectronTensorGradient_weak f g df dg hf hg,?_⟩
  rintro ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j
  · obtain ⟨e,he⟩ := hef (0,k) (0,l)
    exact ⟨twoElectronTensor e g,by
      simpa [twoElectronTensorGradient] using twoElectronTensor_weakPartial_first g l he⟩
  · exact ⟨twoElectronTensor (df (0,k)) (dg (0,l)),by
      simpa [twoElectronTensorGradient] using
        twoElectronTensor_weakPartial_second (df (0,k)) l (hg (0,l))⟩
  · exact ⟨twoElectronTensor (df (0,l)) (dg (0,k)),by
      simpa [twoElectronTensorGradient] using
        twoElectronTensor_weakPartial_first (dg (0,k)) l (hf (0,l))⟩
  · obtain ⟨e,he⟩ := heg (0,k) (0,l)
    exact ⟨twoElectronTensor f e,by
      simpa [twoElectronTensorGradient] using twoElectronTensor_weakPartial_second f l he⟩

#print axioms twoElectronTensorGradient_weak
#print axioms twoElectronTensor_hasH1
#print axioms twoElectronTensor_hasH2
end TheoremT.Continuum
