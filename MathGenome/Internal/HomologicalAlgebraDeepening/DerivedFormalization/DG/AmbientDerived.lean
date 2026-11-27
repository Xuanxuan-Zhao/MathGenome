import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CoefficientLiftComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.AmbientDerived
import Mathlib.CategoryTheory.Localization.LocalizerMorphism

open CategoryTheory

universe u v w t

namespace DerivedFormalization.DG.AmbientDerived

open RightDGModule (K D Q instCategoryK homotopyClass)
open CoefficientLift
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)
open Specs.DerivedFormalization.DG.AmbientDerived
  (IsLocalization InputCoefficients InputLocalization)

noncomputable section

variable {k : Type u} [CommRing k]

/-- The base dg category with its arrows lifted to the adequate coefficient level. -/
abbrev category (A : DGCategory.{u,v,w} k) : DGCategory.{u,max v w t,w} k :=
  liftCategory.{u,v,w,max w t} A

/-- The homotopy category of all right dg modules at the adequate level. -/
abbrev homotopyCategory (A : DGCategory.{u,v,w} k) := K (category.{u,v,w,t} A)

/-- The common derived category at the adequate coefficient level. -/
abbrev derivedCategory (A : DGCategory.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A) := ⟨instCategoryK _, rfl⟩) :=
  D (category.{u,v,w,t} A) h

/-- The localization functor on the entire adequate homotopy category. -/
abbrev quotient (A : DGCategory.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A) := ⟨instCategoryK _, rfl⟩) :
    homotopyCategory.{u,v,w,t} A ⥤ derivedCategory.{u,v,w,t} A h :=
  Q (category.{u,v,w,t} A) h

theorem isLocalization : IsLocalization.{u,v,w,t} := by
  intro k _ A h
  exact RightDGModule.Q_isLocalization (category.{u,v,w,t} A) h

/-- The canonical input on original strict modules. -/
abbrev strictInput (A : DGCategory.{u,v,w} k) :=
  liftFunctor.{u,v,w,max w t} A

/-- The canonical input on homotopy classes of original modules. -/
abbrev homotopyInput (A : DGCategory.{u,v,w} k) :=
  homotopyLift.{u,v,w,max w t} A

/-- The input on the native localization obtained by inverting quasi-isomorphisms. -/
abbrev derivedInput (A : DGCategory.{u,v,w} k) :=
  derivedLift.{u,v,w,max w t} A

/-- The comparison square on the native homotopy category. -/
abbrev inputSquare (A : DGCategory.{u,v,w} k) :
    Q A ⋙ derivedInput.{u,v,w,t} A ≅ homotopyInput.{u,v,w,t} A ⋙ quotient.{u,v,w,t} A :=
  derivedLiftComparison.{u,v,w,max w t} A

theorem inputCoefficients : InputCoefficients.{u,v,w,t} :=
  ⟨componentComparison, mapProperties, homologyComparison⟩

theorem inputLocalization : InputLocalization.{u,v,w,t} :=
  homotopyAndDerivedComparison.{u,v,w,max w t}

section AdequateNative

open Specs.DerivedFormalization.DG.AmbientDerived (NativeStrictComparison)

variable {A : DGCategory.{u,max v w t,w} k}

abbrev transportToAmbient (A : DGCategory.{u,max v w t,w} k) :=
  Specs.DerivedFormalization.DG.AmbientDerived.transportToAmbient.{u,v,w,t} A

abbrev transportToNative (A : DGCategory.{u,max v w t,w} k) :=
  Specs.DerivedFormalization.DG.AmbientDerived.transportToNative.{u,v,w,t} A

/-- At an unchanged coefficient level, transport only the arrow action in both directions. -/
def strictEquivalence (A : DGCategory.{u,max v w t,w} k) :
    RightDGModule A ≌ RightDGModule (category.{u,max v w t,w,t} A) where
  functor := transportToAmbient.{u,v,w,t} A
  inverse := transportToNative.{u,v,w,t} A
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp; rfl)

/-- Compare the pointwise coefficient lift with transport that fixes the term complexes. -/
def strictComparison (A : DGCategory.{u,max v w t,w} k) :
    strictInput.{u,max v w t,w,t} A ≅ transportToAmbient.{u,v,w,t} A :=
  NatIso.ofComponents (downModule.{u,v,w,max w t}) (by
    intro M N f
    apply RightDGModuleModel.hom_ext
    intro a
    apply HomologicalComplex.hom_ext
    intro i
    rfl)

theorem nativeStrictComparison : NativeStrictComparison.{u,v,w,t} :=
  fun A => ⟨strictEquivalence A, rfl, rfl, strictComparison A, fun _ _ _ _ => rfl⟩

open RightDGModule (GradedHom homotopyCriterion IsQuasiIso)
open Specs.DerivedFormalization.DG.AmbientDerived (NativeGradedComparison NativeHomotopyAndQuasiIso)

variable {M N : RightDGModule A}

/-- The homogeneous maps keep their component maps when only the arrows are transported. -/
def gradedEquivalence (M N : RightDGModule A) (r : ℤ) :
    GradedHom M N r ≃ₗ[k]
      GradedHom ((transportToAmbient.{u,v,w,t} A).obj M) ((transportToAmbient.{u,v,w,t} A).obj N) r where
  toFun f := ⟨f.val, by
    intro a b i j n ir nr h hi hn x z
    exact f.comm_act i j n ir nr h hi hn x z.down⟩
  invFun f := ⟨f.val, by
    intro a b i j n ir nr h hi hn x z
    exact f.comm_act i j n ir nr h hi hn x (ULift.up z)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem nativeGradedComparison : NativeGradedComparison.{u,v,w,t} :=
  fun _ => ⟨gradedEquivalence.{u,v,w,t}, fun _ _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => Subtype.ext rfl, fun _ _ _ _ _ _ _ _ _ => Subtype.ext rfl,
    fun _ => Subtype.ext rfl⟩

/-- Homotopy of strict maps is unchanged by transport of the arrow action. -/
theorem transport_homotopy_iff (f g : M ⟶ N) :
    homotopyClass ((transportToAmbient.{u,v,w,t} A).map f) =
      homotopyClass ((transportToAmbient.{u,v,w,t} A).map g) ↔
    homotopyClass f = homotopyClass g := by
  rw [homotopyCriterion, homotopyCriterion]
  constructor
  · rintro ⟨h, eqn⟩
    exact ⟨(gradedEquivalence.{u,v,w,t} M N (-1)).symm h, eqn⟩
  · rintro ⟨h, eqn⟩
    exact ⟨gradedEquivalence.{u,v,w,t} M N (-1) h, eqn⟩

theorem nativeHomotopyAndQuasiIso : NativeHomotopyAndQuasiIso.{u,v,w,t} :=
  fun _ => ⟨transport_homotopy_iff, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

open RightDGModule (toHomotopyCategory quasiIsomorphisms quasiIsomorphisms_homotopyClass
  homotopyClass_surjective)
open Specs.DerivedFormalization.DG.AmbientDerived (NativeLocalizationComparison)

private def homotopyComparisonAt (A : DGCategory.{u,max v w t,w} k) (M : K A) :
    (homotopyInput.{u,max v w t,w,t} A).obj M ≅
      (transportToAmbient.{u,v,w,t} A).obj (show RightDGModule A from M) :=
  (toHomotopyCategory (category.{u,max v w t,w,t} A)).mapIso ((strictComparison.{u,v,w,t} A).app M)

/-- The homotopy category functor that only transports arrow actions. -/
def homotopyTransport (A : DGCategory.{u,max v w t,w} k) :
    K A ⥤ homotopyCategory.{u,max v w t,w,t} A :=
  (homotopyInput.{u,max v w t,w,t} A).copyObj
    (fun M => (transportToAmbient.{u,v,w,t} A).obj (show RightDGModule A from M))
    (homotopyComparisonAt.{u,v,w,t} A)

/-- The degreewise down isomorphism also identifies the homotopy category functors. -/
def homotopyTransportComparison (A : DGCategory.{u,max v w t,w} k) :
    homotopyInput.{u,max v w t,w,t} A ≅ homotopyTransport.{u,v,w,t} A :=
  (homotopyInput.{u,max v w t,w,t} A).isoCopyObj _ (homotopyComparisonAt.{u,v,w,t} A)

@[simp] theorem homotopyTransport_map_class (f : M ⟶ N) :
    (homotopyTransport.{u,v,w,t} A).map (homotopyClass f) =
      homotopyClass ((transportToAmbient.{u,v,w,t} A).map f) := by
  let J := toHomotopyCategory (category.{u,max v w t,w,t} A)
  let alpha := strictComparison.{u,v,w,t} A
  change J.map (alpha.inv.app M) ≫
      (homotopyInput.{u,max v w t,w,t} A).map (homotopyClass f) ≫
        J.map (alpha.hom.app N) = J.map ((transportToAmbient.{u,v,w,t} A).map f)
  rw [homotopyLift_map_class]
  change J.map (alpha.inv.app M) ≫ J.map ((strictInput.{u,max v w t,w,t} A).map f) ≫
      J.map (alpha.hom.app N) = J.map ((transportToAmbient.{u,v,w,t} A).map f)
  rw [← J.map_comp, ← J.map_comp, alpha.hom.naturality f,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

instance homotopyTransport_isEquivalence (A : DGCategory.{u,max v w t,w} k) :
    (homotopyTransport.{u,v,w,t} A).IsEquivalence := by
  let ff := (homotopyLiftFullyFaithful.{u,max v w t,w,max w t} A).ofIso
    (homotopyTransportComparison.{u,v,w,t} A)
  refine { full := ff.full, faithful := ff.faithful, essSurj := ⟨?_⟩ }
  intro M
  exact ⟨(transportToNative.{u,v,w,t} A).obj (show RightDGModule _ from M),
    ⟨(toHomotopyCategory _).mapIso ((strictEquivalence.{u,v,w,t} A).counitIso.app M)⟩⟩

def homotopyEquivalence (A : DGCategory.{u,max v w t,w} k) :
    K A ≌ homotopyCategory.{u,max v w t,w,t} A :=
  (homotopyTransport.{u,v,w,t} A).asEquivalence

theorem homotopyTransport_quasiIsomorphisms_iff {M N : K A} (f : M ⟶ N) :
    quasiIsomorphisms (category.{u,max v w t,w,t} A) ((homotopyTransport.{u,v,w,t} A).map f) ↔
      quasiIsomorphisms A f := by
  obtain ⟨g, rfl⟩ := homotopyClass_surjective f
  rw [homotopyTransport_map_class]
  exact (quasiIsomorphisms_homotopyClass ((transportToAmbient.{u,v,w,t} A).map g)).trans
    (quasiIsomorphisms_homotopyClass g).symm

private def transportLocalizer (A : DGCategory.{u,max v w t,w} k) :
    LocalizerMorphism (quasiIsomorphisms A) (quasiIsomorphisms (category.{u,max v w t,w,t} A)) where
  functor := homotopyTransport.{u,v,w,t} A
  map _ _ f hf := (homotopyTransport_quasiIsomorphisms_iff.{u,v,w,t} f).mpr hf

/-- The quotient square for the native transport uses the same derived input functor. -/
def transportSquare (A : DGCategory.{u,max v w t,w} k) :
    Q A ⋙ derivedInput.{u,max v w t,w,t} A ≅
      homotopyTransport.{u,v,w,t} A ⋙ quotient.{u,max v w t,w,t} A :=
  inputSquare.{u,max v w t,w,t} A ≪≫
    Functor.isoWhiskerRight (homotopyTransportComparison.{u,v,w,t} A) _

private theorem transport_quasiIsomorphisms_surjective (A : DGCategory.{u,max v w t,w} k) :
    quasiIsomorphisms (category.{u,max v w t,w,t} A) ≤
      (quasiIsomorphisms A).map (homotopyTransport.{u,v,w,t} A) := by
  intro M N f hf
  obtain ⟨g, rfl⟩ := homotopyClass_surjective f
  let g₀ := (transportToNative.{u,v,w,t} A).map g
  have hg₀ : quasiIsomorphisms A (homotopyClass g₀) :=
    (quasiIsomorphisms_homotopyClass g₀).mpr ((quasiIsomorphisms_homotopyClass g).mp hf)
  have e : (homotopyTransport.{u,v,w,t} A).map (homotopyClass g₀) = homotopyClass g :=
    homotopyTransport_map_class.{u,v,w,t} g₀
  exact e ▸ (quasiIsomorphisms A).map_mem_map (homotopyTransport.{u,v,w,t} A) _ hg₀

instance derivedInput_isEquivalence (A : DGCategory.{u,max v w t,w} k) :
    (derivedInput.{u,max v w t,w,t} A).IsEquivalence := by
  let F := transportLocalizer.{u,v,w,t} A
  have : F.functor.IsEquivalence := homotopyTransport_isEquivalence.{u,v,w,t} A
  have : F.IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.of_equivalence F
      (transport_quasiIsomorphisms_surjective.{u,v,w,t} A)
  let Q₀ := Q A ⟨instCategoryK A, rfl⟩
  let Q₁ := quotient.{u,max v w t,w,t} A
  have : CatCommSq F.functor Q₀ Q₁ (derivedInput.{u,max v w t,w,t} A) :=
    ⟨(transportSquare.{u,v,w,t} A).symm⟩
  exact F.isEquivalence Q₀ Q₁ (derivedInput.{u,max v w t,w,t} A)

/-- At an adequate native level the canonical derived input is an equivalence. -/
def derivedEquivalence (A : DGCategory.{u,max v w t,w} k) :
    D A ≌ derivedCategory.{u,max v w t,w,t} A :=
  letI := derivedInput_isEquivalence.{u,v,w,t} A
  (derivedInput.{u,max v w t,w,t} A).asEquivalence

theorem nativeLocalizationComparison : NativeLocalizationComparison.{u,v,w,t} := by
  intro k _ A h h'
  exact ⟨homotopyEquivalence.{u,v,w,t} A, fun _ => rfl,
    fun f => heq_of_eq (homotopyTransport_map_class.{u,v,w,t} f),
    homotopyTransport_quasiIsomorphisms_iff.{u,v,w,t},
    derivedEquivalence.{u,v,w,t} A, ⟨transportSquare.{u,v,w,t} A⟩⟩

end AdequateNative

end

end DerivedFormalization.DG.AmbientDerived
