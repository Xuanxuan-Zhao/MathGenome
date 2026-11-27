import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedAffineBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentComplex
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.Flat.Basic

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Specs.DerivedFormalization.Affine.CotangentBaseChange

open _root_.DerivedFormalization.Affine
open _root_.DerivedFormalization.Affine.Kahler (DifferentialModel value)
open Tensor (ModuleTensor act regular restrict restrictFunctor)
open TensorResolutionComparison (CoproductModel)
open CotangentComplex (Model ComparisonSystem oneObject)
open DG.Derived (HomotopyCategoryLaws)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B P C Q D : NonpositiveCDGA.{u,v} k}

abbrev Differential (f : A ⟶ P) :=
  DifferentialModel (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)

abbrev extend (T : ModuleTensor.{u,v} k) (g : P ⟶ Q) :=
  T.baseChange (g : P.toCommDGAlgebra ⟶ Q.toCommDGAlgebra)

abbrev symbol {f : A ⟶ P} (O : Differential f) (i : ℤ) (x : P.complex.X i) :=
  value O.symbol i i (add_zero i) x

abbrev symbolTensor (T : ModuleTensor.{u,v} k) {f : A ⟶ P} (O : Differential f)
    (g : P ⟶ Q) (i j n : ℤ) (h : i+j=n) (x : P.complex.X i) (y : Q.complex.X j) :=
  T.tmul (g : P.toCommDGAlgebra ⟶ Q.toCommDGAlgebra) (N := regular Q.toCommDGAlgebra)
    i j n h (symbol O i x) y

/-- Base change preserves the very same variables and stages of the
given presentation. The differential on each of the new generators is
the image of the old differential, since the algebra inclusion is a chain map. -/
def PresentationBaseChange {f : A ⟶ P} {a : A ⟶ C} {p : P ⟶ Q} {q : C ⟶ Q} : Prop :=
  IsPushout f a p q →
    ∀ (V : Semifree.Variables.{v}) (E : Semifree.StagedPresentation A V f),
    ∃ E' : Semifree.StagedPresentation C V q, E'.stages = E.stages ∧
      ∀ x : V.Index,
        E'.component (V.degree x) (Semifree.variableTerm C V x) =
          p.chainMap.f (V.degree x)
            (E.component (V.degree x) (Semifree.variableTerm A V x))

/-- The comparison of relative differential modules on the base-changed
algebra carries the original symbols to the symbols of their images. -/
def IsDifferentialComparison (T : ModuleTensor.{u,v} k)
    {f : A ⟶ P} {g : C ⟶ Q} (O : Differential f) (O' : Differential g) (p : P ⟶ Q)
    (m : (extend T p).obj O.module ⟶ O'.module) : Prop :=
  ∀ (i j n : ℤ) (h : i+j=n) (x : P.complex.X i) (y : Q.complex.X j),
    (m.app ()).f n (symbolTensor T O p i j n h x y) =
      act O'.module i j n h (symbol O' i (p.chainMap.f i x)) y

/-- The scalar-extension associator in the order of the right-module model. -/
def IsAssociator (T : ModuleTensor.{u,v} k) (p : P ⟶ Q) (q : Q ⟶ D) (M : P.Module)
    (e : (extend T q).obj ((extend T p).obj M) ≅ (extend T (p ≫ q)).obj M) : Prop :=
  ∀ (i j l m n : ℤ) (hm : i+j=m) (hn : m+l=n)
    (x : Tensor.term M i) (b : Q.complex.X j) (c : D.complex.X l),
    (e.hom.app ()).f n (T.tmul (q : Q.toCommDGAlgebra ⟶ D.toCommDGAlgebra)
      (N := regular D.toCommDGAlgebra) m l n hn
      (T.tmul (p : P.toCommDGAlgebra ⟶ Q.toCommDGAlgebra)
        (N := regular Q.toCommDGAlgebra) i j m hm x b) c) =
      T.tmul (p ≫ q : P.toCommDGAlgebra ⟶ D.toCommDGAlgebra)
        (N := regular D.toCommDGAlgebra) i (j+l) n (by omega) x
          (D.mul j l (j+l) rfl (q.chainMap.f j b) c)

variable (T : ModuleTensor.{u,v} k)
variable (O : ∀ {A P : NonpositiveCDGA.{u,v} k} (f : A ⟶ P), Differential f)

/-- Strict differential comparison on the pushout of a semifree map.
The identity resolution of the pushout gives the cotangent model via
scalar extension along the identity. -/
def DifferentialComparisons : Prop :=
  ∀ {A P C Q : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} {a : A ⟶ C}
    {p : P ⟶ Q} {q : C ⟶ Q},
    IsPushout f a p q → Semifree.IsSemifree A f →
    ∃! e : (extend T p).obj (O f).module ≅ (O q).module,
      IsDifferentialComparison T (O f) (O q) p e.hom

/-- For two successive pushouts, the composite is the comparison for the
outer rectangle, using the associator. Pasting identifies that rectangle
with any chosen tensor model for the composite base change. -/
def IteratedComparisons : Prop :=
  ∀ {A P C Q D R : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} {a : A ⟶ C}
    {p : P ⟶ Q} {q : C ⟶ Q} {b : C ⟶ D} {r : Q ⟶ R} {s : D ⟶ R},
    IsPushout f a p q → IsPushout q b r s →
    ∀ (e : (extend T p).obj (O f).module ≅ (O q).module)
      (e' : (extend T r).obj (O q).module ≅ (O s).module)
      (e'' : (extend T (p ≫ r)).obj (O f).module ≅ (O s).module)
      (assoc : (extend T r).obj ((extend T p).obj (O f).module) ≅
        (extend T (p ≫ r)).obj (O f).module),
      IsDifferentialComparison T (O f) (O q) p e.hom →
      IsDifferentialComparison T (O q) (O s) r e'.hom →
      IsDifferentialComparison T (O f) (O s) (p ≫ r) e''.hom →
      IsAssociator T p r (O f).module assoc →
      (extend T r).map e.hom ≫ e'.hom = assoc.hom ≫ e''.hom

/-- Flatness of an ordinary base change uses the action of the specified
ordinary ring map. It makes no flatness assumption on the algebra being resolved. -/
def OrdinaryFlat (a : A ⟶ C) : Prop :=
  ∃ (A₀ C₀ : CommAlgCat.{v} k) (a₀ : A₀ ⟶ C₀)
    (eA : A ≅ NonpositiveCDGA.ordinary A₀)
    (eC : C ≅ NonpositiveCDGA.ordinary C₀),
    a ≫ eC.hom = eA.hom ≫ NonpositiveCDGA.ordinaryMap a₀ ∧
    letI : Algebra A₀ C₀ := a₀.hom.toRingHom.toAlgebra
    Module.Flat A₀ C₀

/-- The flat pushout resolution and its comparison before localization. -/
structure FlatComparison {f : A ⟶ P} {g : A ⟶ B} {a : A ⟶ C}
    (π : P ⟶ B) (X : PushoutCocone f a) (Y : PushoutCocone g a) where
  augmentation : X.pt ⟶ Y.pt
  left : X.inl ≫ augmentation = π ≫ Y.inl
  right : X.inr ≫ augmentation = Y.inr
  semifree : Semifree.IsSemifree C X.inr
  surjective : NonpositiveCDGA.DegreewiseSurjective augmentation
  quasiIso : NonpositiveCDGA.IsQuasiIso augmentation
  iso : (extend T Y.inl).obj ((extend T π).obj (O f).module) ≅
    (extend T augmentation).obj (O X.inr).module
  onSymbols :
    ∀ (i j l m n : ℤ) (hm : i+j=m) (hn : m+l=n)
      (x : P.complex.X i) (b : B.complex.X j) (z : Y.pt.complex.X l),
      (iso.hom.app ()).f n
        (T.tmul (Y.inl : B.toCommDGAlgebra ⟶ Y.pt.toCommDGAlgebra)
          (N := regular Y.pt.toCommDGAlgebra) m l n hn (symbolTensor T (O f) π i j m hm x b) z) =
      symbolTensor T (O X.inr) augmentation i (j+l) n (by omega)
        (X.inl.chainMap.f i x) (Y.pt.mul j l (j+l) rfl (Y.inl.chainMap.f j b) z)

/-- A semilinear map on strict cotangent representatives that takes the
extended differential of every element to the extended differential of its
image and applies the given map to the scalar. -/
def IsSymbolMap {A' P' D' : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} {f' : A' ⟶ P'}
    (O₁ : Differential f) (O₂ : Differential f') (g : P ⟶ D) (g' : P' ⟶ D')
    (p : P ⟶ P') (d : D ⟶ D')
    (m : (extend T g).obj O₁.module ⟶
      restrict (d : D.toCommDGAlgebra ⟶ D'.toCommDGAlgebra) ((extend T g').obj O₂.module)) : Prop :=
  ∀ (i j n : ℤ) (h : i+j=n) (x : P.complex.X i) (z : D.complex.X j),
    (m.app ()).f n (symbolTensor T O₁ g i j n h x z) =
      symbolTensor T O₂ g' i j n h (p.chainMap.f i x) (d.chainMap.f j z)

/-- Strict maps of resolved diagrams act on both the differential and the
scalar. Uniqueness gives the identity and composition laws, since the
symbol formula for a composite is the composite of the two formulas. -/
def SymbolMaps : Prop :=
  ∀ {A P D A' P' D' : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} {f' : A' ⟶ P'}
    (a : A ⟶ A') (p : P ⟶ P') (g : P ⟶ D) (g' : P' ⟶ D') (d : D ⟶ D'),
    f ≫ p = a ≫ f' → g ≫ d = p ≫ g' →
    ∃! m, IsSymbolMap T (O f) (O f') g g' p d m

/-- Naturality in compatible maps of pushout squares, with scalar
restriction on the target differential module. -/
def DifferentialNaturality : Prop :=
  ∀ {A P C Q A' P' C' Q' : NonpositiveCDGA.{u,v} k}
    {f : A ⟶ P} {a : A ⟶ C} {p : P ⟶ Q} {q : C ⟶ Q}
    {f' : A' ⟶ P'} {a' : A' ⟶ C'} {p' : P' ⟶ Q'} {q' : C' ⟶ Q'},
    IsPushout f a p q → IsPushout f' a' p' q' →
    ∀ (α : A ⟶ A') (β : P ⟶ P') (γ : C ⟶ C') (d : Q ⟶ Q'),
    f ≫ β = α ≫ f' → a ≫ γ = α ≫ a' →
    p ≫ d = β ≫ p' → q ≫ d = γ ≫ q' →
    ∀ (e : (extend T p).obj (O f).module ≅ (O q).module)
      (e' : (extend T p').obj (O f').module ≅ (O q').module),
    IsDifferentialComparison T (O f) (O q) p e.hom →
    IsDifferentialComparison T (O f') (O q') p' e'.hom →
    ∀ l, IsSymbolMap T (O f) (O f') p p' β d l →
    ∃ r : (O q).module ⟶ restrict (d : Q.toCommDGAlgebra ⟶ Q'.toCommDGAlgebra) (O q').module,
      (∀ i (x : Q.complex.X i), (r.app ()).f i (symbol (O q) i x) =
        symbol (O q') i (d.chainMap.f i x)) ∧
      e.hom ≫ r =
        l ≫ (restrictFunctor (d : Q.toCommDGAlgebra ⟶ Q'.toCommDGAlgebra)).map e'.hom

def FlatComparisons : Prop :=
  ∀ {A P B C : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} {g : A ⟶ B}
    {a : A ⟶ C} (π : P ⟶ B),
    f ≫ π = g → Semifree.IsSemifree A f →
    NonpositiveCDGA.DegreewiseSurjective π → NonpositiveCDGA.IsQuasiIso π →
    OrdinaryFlat a → ∀ (X : PushoutCocone f a) (Y : PushoutCocone g a),
    Nonempty (IsColimit X) → Nonempty (IsColimit Y) →
    Nonempty (FlatComparison T O π X Y)

/-- A map of flat scalar extensions of the fixed resolution induces the
strict comparison square used in the Amitsur diagram. The left column,
normalized by the associator, extends the same symbols of the original P. -/
def FlatNaturality : Prop :=
  ∀ {A P B C C' : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} {g : A ⟶ B}
    {a : A ⟶ C} {a' : A ⟶ C'} {π : P ⟶ B}
    {X : PushoutCocone f a} {Y : PushoutCocone g a}
    {X' : PushoutCocone f a'} {Y' : PushoutCocone g a'}
    (F : FlatComparison T O π X Y) (F' : FlatComparison T O π X' Y')
    (c : C ⟶ C') (p : X.pt ⟶ X'.pt) (d : Y.pt ⟶ Y'.pt),
    X.inl ≫ p = X'.inl → X.inr ≫ p = c ≫ X'.inr →
    Y.inl ≫ d = Y'.inl → Y.inr ≫ d = c ≫ Y'.inr →
    F.augmentation ≫ d = p ≫ F'.augmentation →
    ∀ (e : (extend T Y.inl).obj ((extend T π).obj (O f).module) ≅
          (extend T (π ≫ Y.inl)).obj (O f).module)
      (e' : (extend T Y'.inl).obj ((extend T π).obj (O f).module) ≅
          (extend T (π ≫ Y'.inl)).obj (O f).module),
    IsAssociator T π Y.inl (O f).module e →
    IsAssociator T π Y'.inl (O f).module e' →
    ∃ l r, IsSymbolMap T (O f) (O f) (π ≫ Y.inl) (π ≫ Y'.inl) (𝟙 P) d l ∧
      IsSymbolMap T (O X.inr) (O X'.inr) F.augmentation F'.augmentation p d r ∧
      e.hom ≫ l ≫ (restrictFunctor (d : Y.pt.toCommDGAlgebra ⟶ Y'.pt.toCommDGAlgebra)).map
        (e'.inv ≫ F'.iso.hom) = F.iso.hom ≫ r

/-- The identity augmentation of a semifree algebra over its base. -/
def identityModel (q : C ⟶ Q) (hs : Semifree.IsSemifree C q) : Model q where
  algebra := Q
  base := q
  augmentation := 𝟙 Q
  triangle := Category.comp_id q
  semifree := hs
  surjective := by
    intro i x
    refine ⟨x, ?_⟩
    change ((𝟙 Q.complex : Q.complex ⟶ Q.complex).f i) x = x
    rfl
  quasiIso := by
    change QuasiIso (𝟙 Q.complex)
    infer_instance
  differentials := O q

/-- The pushed-out augmentation is a resolution of the flat base-changed
algebra. Its representative is the target of the strict comparison. -/
def FlatComparison.model {f : A ⟶ P} {g : A ⟶ B} {a : A ⟶ C}
    {π : P ⟶ B} {X : PushoutCocone f a} {Y : PushoutCocone g a}
    (F : FlatComparison T O π X Y) : Model Y.inr where
  algebra := X.pt
  base := X.inr
  augmentation := F.augmentation
  triangle := F.right
  semifree := F.semifree
  surjective := F.surjective
  quasiIso := F.quasiIso
  differentials := O X.inr

/-- The relative differential module itself represents the cotangent
complex of a semifree extension via the tensor unit isomorphism. -/
def IdentityCotangentModels : Prop :=
  ∀ {C Q : NonpositiveCDGA.{u,v} k} (q : C ⟶ Q) (hs : Semifree.IsSemifree C q),
    ∃ e : (identityModel O q hs).module T ≅ (O q).module,
      IsDifferentialComparison T (O q) (O q) (𝟙 Q) e.hom

/-- The comparison uses the pushouts of the semifree resolution and, in the
ordinary flat case, its augmentation. All its maps are on the strict models
that represent the cotangent complexes by the resolution comparison theorem.
The tensor formulas also give scalar extension on maps from other strict
representatives, such as the finite projective representative in descent. -/
def BaseChange : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∃ (T : ModuleTensor.{u,v} k) (S : CoproductModel T)
      (O : ∀ {A P : NonpositiveCDGA.{u,v} k} (f : A ⟶ P), Differential f),
      T.Comparisons ∧
      (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module), T.Formulas f N) ∧
      (∀ {A P C : NonpositiveCDGA.{u,v} k} (f : A ⟶ P) (a : A ⟶ C),
        IsPushout f a (S.inl f a) (S.inr f a)) ∧
      (∀ {A B : NonpositiveCDGA.{u,v} k} (b : A ⟶ B),
        Nonempty (Model b) ∧
        ∀ h : HomotopyCategoryLaws (oneObject B), Nonempty (ComparisonSystem T b h)) ∧
      (∀ {A P C Q : NonpositiveCDGA.{u,v} k} (f : A ⟶ P) (a : A ⟶ C)
        (p : P ⟶ Q) (q : C ⟶ Q), PresentationBaseChange (f := f) (a := a) (p := p) (q := q)) ∧
      DifferentialComparisons T O ∧ IdentityCotangentModels T O ∧
      IteratedComparisons T O ∧ SymbolMaps T O ∧ DifferentialNaturality T O ∧
      FlatComparisons T O ∧ FlatNaturality T O

end

end Specs.DerivedFormalization.Affine.CotangentBaseChange
