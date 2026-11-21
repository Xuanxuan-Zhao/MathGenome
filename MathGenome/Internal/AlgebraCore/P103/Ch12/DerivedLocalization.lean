import MathGenome.Internal.AlgebraCore.Specs.P103.Ch12.DerivedLocalization
import MathGenome.Internal.AlgebraCore.P103.Ch12.ExtBaseChange
import MathGenome.Internal.AlgebraCore.P103.Ch04.ModuleLocalization
import MathGenome.Internal.AlgebraCore.P103.Ch04.LocalDetection

import MathGenome.Internal.AlgebraCore.P103.Ch12.TorBaseChange
namespace P103.Ch12.DerivedLocalization
noncomputable section
universe u v w
open CategoryTheory TensorProduct
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch12.TorBaseChange P103.Specs.Ch12.ExtBaseChange
open P103.Specs.Ch12.DerivedLocalization
set_option maxHeartbeats 1600000

section Coefficients
variable {R : Type u} [CommRing R] {K L : ChainComplex (ModuleCat.{max u v} R) ℕ}
  {B D : Type w} [AddCommGroup B] [AddCommGroup D] [Module R B] [Module R D]

/-- Change the coefficient by its specified linear isomorphism. -/
def coefficientIso (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (e : B ≃ₗ[R] D) :
    coefficientComplex (S := R) K B ≅ coefficientComplex (S := R) K D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (TensorProduct.AlgebraTensorModule.congr e
      (LinearEquiv.refl R (K.X n))).toModuleIso)
    (by intro i j h; exact (coefficientMap (𝟙 K) e.toLinearMap).comm i j)

/-- Postcomposition by a specified coefficient isomorphism. -/
def linearHomIso (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (e : B ≃ₗ[R] D) :
    linearHomComplex K B ≅ linearHomComplex K D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((LinearEquiv.refl R (K.X n)).arrowCongr e).toModuleIso)
    (by intro i j h; exact (linearHomMap (𝟙 K) e.toLinearMap).comm i j)

end Coefficients

section Tor
variable {R : Type u} [CommRing R] (T : Submonoid R)
  (F : FlatTorBaseChange.{u,v,w} R (Localization T))

/-- Replacing the tensor coefficient by its fraction module. -/
def torComparison {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :
    LocalizedModule T (commutativeTor P B n) ≃ₗ[Localization T] localizedTor T P B n :=
  (localizationEquiv T (commutativeTor P B n)).symm.trans
    ((F.second P B n).trans
      (((quotientHomology (ComplexShape.down ℕ) n).mapIso
        (coefficientIso (extendComplex (Localization T) P.complex)
          (localizationEquiv T B))).toLinearEquiv))

@[simp] theorem torComparison_apply {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] n x :
    torComparison T F P B n x = homologyMap
      (coefficientMap (R := Localization T) (S := Localization T)
        (𝟙 (extendComplex (Localization T) P.complex))
        (localizationEquiv T B).toLinearMap) n
      (F.second P B n ((localizationEquiv T (commutativeTor P B n)).symm x)) := rfl

/-- Exact extension and the localization augmentation retain projectivity. -/
theorem localized_projective {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (hP : P.IsProjective) :
    (localizedResolution T P).IsProjective := by
  intro n
  letI := hP n
  change Module.Projective (Localization T) (Localization T ⊗[R] P.complex.X n)
  infer_instance

end Tor

section TorNaturality
variable {R : Type u} [CommRing R] (T : Submonoid R)
  (F : FlatTorBaseChange.{u,v,w} R (Localization T))

/-- The fraction comparison commutes with the simultaneous coefficient map. -/
theorem torCoefficient_natural {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A')
    {B D : Type w} [AddCommGroup B] [AddCommGroup D] [Module R B] [Module R D]
    (l : P.complex ⟶ Q.complex) (g : B →ₗ[R] D) n y :
    homologyMap (coefficientMap (R := Localization T) (S := Localization T)
        (𝟙 (extendComplex (Localization T) Q.complex)) (localizationEquiv T D).toLinearMap) n
      (homologyMap (coefficientMap (R := Localization T) (S := Localization T)
        (extensionMap (S := Localization T) l) (g.baseChange (Localization T))) n y) =
    homologyMap (coefficientMap (R := Localization T) (S := Localization T)
        (extensionMap (S := Localization T) l) (LocalizedModule.map T g)) n
      (homologyMap (coefficientMap (R := Localization T) (S := Localization T)
        (𝟙 (extendComplex (Localization T) P.complex)) (localizationEquiv T B).toLinearMap) n y) := by
  have hc : coefficientMap (R := Localization T) (S := Localization T)
        (extensionMap (S := Localization T) l) (g.baseChange (Localization T)) ≫
      coefficientMap (R := Localization T) (S := Localization T)
        (𝟙 (extendComplex (Localization T) Q.complex)) (localizationEquiv T D).toLinearMap =
      coefficientMap (R := Localization T) (S := Localization T)
        (𝟙 (extendComplex (Localization T) P.complex)) (localizationEquiv T B).toLinearMap ≫
      coefficientMap (R := Localization T) (S := Localization T)
        (extensionMap (S := Localization T) l) (LocalizedModule.map T g) := by
    ext k : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro b p
    change localizationEquiv T D (g.baseChange (Localization T) b) ⊗ₜ[Localization T]
        (l.f k).hom.baseChange (Localization T) p =
      LocalizedModule.map T g (localizationEquiv T B b) ⊗ₜ[Localization T]
        (l.f k).hom.baseChange (Localization T) p
    rw [show localizationEquiv T D (g.baseChange (Localization T) b) =
      LocalizedModule.map T g (localizationEquiv T B b) from
        P103.Ch04.ModuleLocalization.tensorNaturality R T B D g b]
  simpa only [P103.Ch10.Complexes.homologyMap_comp, LinearMap.comp_apply] using
    congrArg (fun f => homologyMap f n y) hc

theorem torComparison_natural {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A')
    {B D : Type w} [AddCommGroup B] [AddCommGroup D] [Module R B] [Module R D]
    (l : P.complex ⟶ Q.complex) (g : B →ₗ[R] D) n x :
    torComparison T F Q D n
        (LocalizedModule.map T (homologyMap (coefficientMap (S := R) l g) n) x) =
      homologyMap (coefficientMap (R := Localization T) (S := Localization T)
        (extensionMap (S := Localization T) l) (LocalizedModule.map T g)) n
        (torComparison T F P B n x) := by
  obtain ⟨y, rfl⟩ := (localizationEquiv T (commutativeTor P B n)).surjective x
  rw [← P103.Ch04.ModuleLocalization.tensorNaturality R T _ _
    (homologyMap (coefficientMap (S := R) l g) n) y]
  simp only [torComparison_apply, LinearEquiv.symm_apply_apply]
  have hb : TensorProduct.map LinearMap.id (homologyMap (coefficientMap (S := R) l g) n) y =
      (homologyMap (coefficientMap (S := R) l g) n).baseChange (Localization T) y := rfl
  have hn := F.second_natural P Q l g n y
  rw [hb, hn]
  exact torCoefficient_natural T P Q l g n _

def torLocalization : TorLocalization.{u,v,w} R T where
  baseChange := F
  projective := localized_projective T
  equiv := torComparison T F
  induced := torComparison_apply T F
  natural := torComparison_natural T F

end TorNaturality

section Ext
variable {R : Type u} [CommRing R] (T : Submonoid R)
  {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
  (hP : P.IsFree) (hf : ∀ n, Module.Finite R (P.complex.X n))
  (B : Type w) [AddCommGroup B] [Module R B]

/-- Flat cohomology, the finite-free Hom comparison, and the fraction comparison. -/
def extComparison (n : ℕ) :
    LocalizedModule T (linearExt P B n) ≃ₗ[Localization T] localizedExt T P B n :=
  (localizationEquiv T (linearExt P B n)).symm.trans
    ((P103.Ch12.ExtBaseChange.flatCohomology (Localization T)
        (linearHomComplex P.complex B) n).trans
      ((((quotientHomology (ComplexShape.up ℕ) n).mapIso
        (P103.Ch12.ExtBaseChange.hom_cochain_isomorphism R (Localization T)
          P.complex B hP hf).choose).toLinearEquiv).trans
        (((quotientHomology (ComplexShape.up ℕ) n).mapIso
          (linearHomIso (baseChangeComplex (Localization T) P.complex)
            (localizationEquiv T B))).toLinearEquiv)))

theorem extComparison_formula n (s : Localization T)
    (z : cycles (linearHomComplex P.complex B) n) :
    ∃ z' : cycles (linearHomComplex (localizedResolution T P).complex (LocalizedModule T B)) n,
      (∀ (t : Localization T) (p : P.complex.X n),
        (show Localization T ⊗[R] P.complex.X n →ₗ[Localization T] LocalizedModule T B from z'.val)
          (t ⊗ₜ[R] p) = s • localizationEquiv T B
            (t ⊗ₜ[R] (show P.complex.X n →ₗ[R] B from z.val) p)) ∧
      extComparison T P hP hf B n (localizationEquiv T (linearExt P B n)
        (s ⊗ₜ[R] homologyClass _ n z)) = homologyClass _ n z' := by
  let hc := P103.Ch12.ExtBaseChange.hom_cochain_isomorphism R (Localization T) P.complex B hP hf
  let z0 := baseChangeCycle (Localization T) (linearHomComplex P.complex B) n s z
  let z1 := cyclesMap hc.choose.hom n z0
  let z2 := cyclesMap (linearHomIso (baseChangeComplex (Localization T) P.complex)
    (localizationEquiv T B)).hom n z1
  refine ⟨z2, ?_, ?_⟩
  · intro t p
    change localizationEquiv T B ((show Localization T ⊗[R] P.complex.X n →ₗ[Localization T] Localization T ⊗[R] B
      from (hc.choose.hom.f n).hom (s ⊗ₜ[R] z.val)) (t ⊗ₜ[R] p)) = _
    rw [hc.choose_spec n]
    change localizationEquiv T B (s • (t ⊗ₜ[R] (show P.complex.X n →ₗ[R] B from z.val) p)) = _
    exact map_smul _ _ _
  · change _ = homologyClass _ n z2
    change homologyMap (linearHomIso (baseChangeComplex (Localization T) P.complex)
      (localizationEquiv T B)).hom n
      (homologyMap hc.choose.hom n
        (P103.Ch12.ExtBaseChange.flatCohomology (Localization T)
          (linearHomComplex P.complex B) n
          ((localizationEquiv T (linearExt P B n)).symm
            (localizationEquiv T (linearExt P B n) (s ⊗ₜ[R] homologyClass _ n z))))) = _
    rw [LinearEquiv.symm_apply_apply, P103.Ch12.ExtBaseChange.flatCohomology_class]
    rfl

end Ext

section ExtNaturality
variable {R : Type u} [CommRing R] (T : Submonoid R)

theorem extComparison_natural {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A')
    (hP : P.IsFree) (hPf : ∀ n, Module.Finite R (P.complex.X n))
    (hQ : Q.IsFree) (hQf : ∀ n, Module.Finite R (Q.complex.X n))
    {B D : Type w} [AddCommGroup B] [AddCommGroup D] [Module R B] [Module R D]
    (l : Q.complex ⟶ P.complex) (g : B →ₗ[R] D) n x :
    extComparison T Q hQ hQf D n
        (LocalizedModule.map T (homologyMap (linearHomMap l g) n) x) =
      homologyMap (linearHomMap (extensionMap (S := Localization T) l)
        (LocalizedModule.map T g)) n (extComparison T P hP hPf B n x) := by
  obtain ⟨y, rfl⟩ := (localizationEquiv T (linearExt P B n)).surjective x
  rw [← P103.Ch04.ModuleLocalization.tensorNaturality R T _ _
    (homologyMap (linearHomMap l g) n) y]
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' =>
    simp only [map_add, hy, hy']
    exact (map_add _ _ _).symm
  | tmul s x =>
    refine Quotient.inductionOn' x ?_
    intro z
    let z0 := cyclesMap (linearHomMap l g) n z
    obtain ⟨zP, hzP, heP⟩ := extComparison_formula T P hP hPf B n s z
    obtain ⟨zQ, hzQ, heQ⟩ := extComparison_formula T Q hQ hQf D n s z0
    change extComparison T Q hQ hQf D n
      (localizationEquiv T (linearExt Q D n) (s ⊗ₜ[R] homologyClass _ n z0)) = _
    erw [heQ, heP, P103.Ch10.Complexes.homologyMap_apply]
    apply congrArg (homologyClass _ n)
    apply Subtype.ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro t p
    change (show Localization T ⊗[R] Q.complex.X n →ₗ[Localization T]
      LocalizedModule T D from zQ.val) (t ⊗ₜ[R] p) =
      LocalizedModule.map T g ((show Localization T ⊗[R] P.complex.X n →ₗ[Localization T]
        LocalizedModule T B from zP.val) (t ⊗ₜ[R] (l.f n).hom p))
    rw [hzQ, hzP, map_smul]
    change s • localizationEquiv T D
      (t ⊗ₜ[R] g ((show P.complex.X n →ₗ[R] B from z.val) ((l.f n).hom p))) = _
    rw [← P103.Ch04.ModuleLocalization.tensorNaturality R T B D g]
    rfl

theorem extScalarBridge : ExtScalarBridge.{u,v,w} R := by
  intro n E A P B
  exact ⟨P103.Ch12.ExtBaseChange.linearExtEquiv E P B, fun _ => rfl⟩

/-- Compatibility with the actual Chapter 11 two-variable Ext map. -/
theorem computedExtMap {n : ℕ} (E : P103.Specs.Ch11.ExtTorDefinitions.ExtMaps.{u,v,w} R n)
    {A A' : ModuleCat.{v} R} (P : ProjectiveChoice R A) (Q : ProjectiveChoice R A')
    {B B' : ModuleCat.{w} R} (f : A' ⟶ A) (g : B ⟶ B')
    (l : Q.val.complex ⟶ P.val.complex) (hl : ChainLift Q.val P.val f.hom l) x :
    E.map P Q f g x = homologyMap (linearHomMap l g.hom) n x := by
  rw [E.formula P Q f g l hl]
  rfl

/-- Homotopic choices of comparison lifts give exactly the same quotient map. -/
theorem extLiftIndependent {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A')
    (hP : P.IsProjective) (hQ : Q.IsProjective) (f : A →ₗ[R] A')
    (l l' : P.complex ⟶ Q.complex) (hl : ChainLift P Q f l) (hl' : ChainLift P Q f l')
    (B : Type w) [AddCommGroup B] [Module R B] n :
    homologyMap (linearHomMap l (LinearMap.id : B →ₗ[R] B)) n =
      homologyMap (linearHomMap l' (LinearMap.id : B →ₗ[R] B)) n := by
  let E := P103.Ch11.ExtTorDefinitions.extMaps.{u,v,w} (R := R) n
  apply LinearMap.ext
  intro x
  exact (computedExtMap E (⟨Q, hQ⟩ : ProjectiveChoice R (ModuleCat.of R A'))
    (⟨P, hP⟩ : ProjectiveChoice R (ModuleCat.of R A))
    (ModuleCat.ofHom f) (𝟙 (ModuleCat.of R B)) l hl x).symm.trans
      (computedExtMap E (⟨Q, hQ⟩ : ProjectiveChoice R (ModuleCat.of R A'))
        (⟨P, hP⟩ : ProjectiveChoice R (ModuleCat.of R A))
        (ModuleCat.ofHom f) (𝟙 (ModuleCat.of R B)) l' hl' x)

def extLocalization : ExtLocalization.{u,v,w} R T where
  bridgeR := extScalarBridge
  bridgeL := extScalarBridge
  lift_independent := extLiftIndependent
  finite_resolution h A _ _ _ := by
    letI := h
    exact P103.Ch12.ExtBaseChange.exists_finite_free_resolution R A
  equiv := extComparison T
  formula := extComparison_formula T
  natural := extComparison_natural T

end ExtNaturality

/-- Arbitrary modules, including unital modules over the zero ring. -/
theorem zeroDetection : zero_detectionType.{u,v} := by
  intro R _ E _ _
  have hm := P103.Ch04.LocalDetection.zeroDetection R E
  refine ⟨?_, hm⟩
  constructor
  · intro h p _
    letI := h
    infer_instance
  · intro h
    apply hm.mpr
    intro m _
    exact h m

section Vanishing

theorem torVanishing (H : flat_base_changeType.{u,v,w}) : tor_vanishingType.{u,v,w} := by
  intro R _ A _ _ P B _ _ n
  have h := zeroDetection R (commutativeTor P B n)
  have e (T : Submonoid R) := (torLocalization T (H R (Localization T)).some).equiv P B n
  constructor
  · constructor
    · intro hz p _
      exact (e p.primeCompl).toEquiv.subsingleton_congr.mp ((h.1.mp hz) p)
    · intro hz
      apply h.1.mpr
      intro p _
      exact (e p.primeCompl).toEquiv.subsingleton_congr.mpr (hz p)
  · constructor
    · intro hz p _
      exact (e p.primeCompl).toEquiv.subsingleton_congr.mp ((h.2.mp hz) p)
    · intro hz
      apply h.2.mpr
      intro p _
      exact (e p.primeCompl).toEquiv.subsingleton_congr.mpr (hz p)

end Vanishing

theorem extVanishing : ext_vanishingType.{u,v,w} := by
  intro R _ _ A _ _ _
  obtain ⟨P, hP, hf⟩ := P103.Ch12.ExtBaseChange.exists_finite_free_resolution R A
  refine ⟨P, hP, hf, ?_⟩
  intro B _ _ n
  have h := zeroDetection R (linearExt P B n)
  have e (T : Submonoid R) := extComparison T P hP hf B n
  constructor
  · constructor
    · intro hz p _
      exact (e p.primeCompl).toEquiv.subsingleton_congr.mp ((h.1.mp hz) p)
    · intro hz
      apply h.1.mpr
      intro p _
      exact (e p.primeCompl).toEquiv.subsingleton_congr.mpr (hz p)
  · constructor
    · intro hz p _
      exact (e p.primeCompl).toEquiv.subsingleton_congr.mp ((h.2.mp hz) p)
    · intro hz
      apply h.2.mpr
      intro p _
      exact (e p.primeCompl).toEquiv.subsingleton_congr.mpr (hz p)

/-- Conditional draft: the only premise is the complete frozen flat Tor
base-change statement, with its three original universe parameters. -/
theorem derived_localization_conditional
    (H : P103.Specs.Ch12.TorBaseChange.flat_base_changeType.{u,v,w}) :
    derived_localizationType.{u,v,w} := by
  refine ⟨?_, ?_, zeroDetection, torVanishing H, extVanishing⟩
  · intro R _ T
    exact ⟨torLocalization T (H R (Localization T)).some⟩
  · intro R _ T
    exact ⟨extLocalization T⟩

end
end P103.Ch12.DerivedLocalization

universe v8_closure_22ffc361937c4957_u0 v8_closure_22ffc361937c4957_u1 v8_closure_22ffc361937c4957_u2
theorem _root_.«P103».«Ch12».«DerivedLocalization».«derived_localization» : _root_.«P103».«Specs».«Ch12».«DerivedLocalization».«derived_localizationType».{v8_closure_22ffc361937c4957_u0, v8_closure_22ffc361937c4957_u1, v8_closure_22ffc361937c4957_u2} :=
  @_root_.«P103».«Ch12».«DerivedLocalization».«derived_localization_conditional».{v8_closure_22ffc361937c4957_u0, v8_closure_22ffc361937c4957_u1, v8_closure_22ffc361937c4957_u2} (@_root_.«P103».«Ch12».«TorBaseChange».«flat_base_change».{v8_closure_22ffc361937c4957_u0, v8_closure_22ffc361937c4957_u1, v8_closure_22ffc361937c4957_u2})
