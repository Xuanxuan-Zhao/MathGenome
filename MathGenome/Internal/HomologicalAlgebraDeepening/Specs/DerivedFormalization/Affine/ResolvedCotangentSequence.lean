import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedTensor

open CategoryTheory

universe u v

namespace Specs.DerivedFormalization.Affine.ResolvedCotangentSequence

open _root_.DerivedFormalization.Affine
open _root_.DerivedFormalization.Affine.Kahler (DifferentialModel value)
open Tensor (ModuleTensor act regular term)
open CotangentComplex (Model oneObject localizedModel moduleClass)
open FlatFiltration (GradedSplit)
open Specs.DerivedFormalization.DG
open DG.Derived (HomotopyCategoryLaws quotient)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B C P Q : NonpositiveCDGA.{u,v} k}

/-- The underlying commutative dg algebra map of a map of nonpositive algebras. -/
abbrev underlying (f : A ⟶ B) : A.toCommDGAlgebra ⟶ B.toCommDGAlgebra := f

/-- Relative differentials for a map of nonpositive algebras. -/
abbrev Differentials (f : A ⟶ B) := DifferentialModel (underlying f)

abbrev symbol {f : A ⟶ B} (O : Differentials f) (n : ℤ) (x : B.complex.X n) :
    term O.module n :=
  value O.symbol n n (add_zero n) x

/-- Extension of a module along a map of nonpositive algebras. -/
abbrev extend (T : ModuleTensor.{u,v} k) (f : A ⟶ B) : A.Module ⥤ B.Module :=
  T.baseChange (underlying f)

abbrev extendedSymbol (T : ModuleTensor.{u,v} k) {f : A ⟶ P} (O : Differentials f)
    (g : P ⟶ Q) (i j n : ℤ) (h : i + j = n) (x : P.complex.X i) (a : Q.complex.X j) :
    term ((extend T g).obj O.module) n :=
  T.tmul (underlying g) (N := regular Q.toCommDGAlgebra) i j n h (symbol O i x) a

/-- All the strict tensor operations in the sequence use the signed balanced tensor. -/
abbrev TensorFormulas (T : ModuleTensor.{u,v} k) : Prop :=
  ∀ {U V : CommDGAlgebra.{u,v} k} (g : U ⟶ V) (N : V.Module), T.Formulas g N

/-- The unaugmented transitivity sequence over Q, with its maps specified on
the symbols of the two absolute modules of differentials. -/
structure DifferentialSequence (T : ModuleTensor.{u,v} k)
    (f : A ⟶ P) (g : P ⟶ Q)
    (O : Differentials f) (U : Differentials (f ≫ g)) (V : Differentials g) where
  incl : (extend T g).obj O.module ⟶ U.module
  proj : U.module ⟶ V.module
  incl_symbol (i j n : ℤ) (h : i + j = n) (x : P.complex.X i) (a : Q.complex.X j) :
    (incl.app ()).f n (extendedSymbol T O g i j n h x a) =
      act U.module i j n h (symbol U i (g.chainMap.f i x)) a
  proj_symbol (i : ℤ) (x : Q.complex.X i) :
    (proj.app ()).f i (symbol U i x) = symbol V i x
  split : GradedSplit incl proj

def DifferentialSequence.extendedSplit {T : ModuleTensor.{u,v} k}
    {f : A ⟶ P} {g : P ⟶ Q} {O : Differentials f} {U : Differentials (f ≫ g)}
    {V : Differentials g} (D : DifferentialSequence T f g O U V)
    {E : CommDGAlgebra.{u,v} k} (t : Q.toCommDGAlgebra ⟶ E) : Prop :=
  Nonempty (GradedSplit ((T.baseChange t).map D.incl) ((T.baseChange t).map D.proj))

/-- Concatenation uses all the semifree stages allowed by the original definition. -/
def Concatenation : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A P Q : NonpositiveCDGA.{u,v} k}
    (f : A ⟶ P) (g : P ⟶ Q),
    Semifree.IsSemifree A f → Semifree.IsSemifree P g → Semifree.IsSemifree A (f ≫ g)

/-- The two canonical maps form a graded-split short exact sequence before
augmentation and after extension to any target dg algebra. -/
def ExactDifferentialSequence : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k),
    TensorFormulas T →
    ∀ {A P Q : NonpositiveCDGA.{u,v} k} (f : A ⟶ P) (g : P ⟶ Q)
      (O : Differentials f) (U : Differentials (f ≫ g)) (V : Differentials g),
      Semifree.IsSemifree A f → Semifree.IsSemifree P g →
      ∃ D : DifferentialSequence T f g O U V,
        ∀ {E : CommDGAlgebra.{u,v} k} (t : Q.toCommDGAlgebra ⟶ E), D.extendedSplit t

/-- The nonpositive algebra of the signed coproduct, with Q as the first factor. -/
abbrev pushout {T : ModuleTensor.{u,v} k} {g : P ⟶ Q} {p : P ⟶ B}
    (X : T.AlgebraCoproduct (underlying g) (underlying p)) (hX : X.Formulas) :
    NonpositiveCDGA.{u,v} k where
  toCommDGAlgebra := X.obj
  nonpositive := hX.nonpositive Q.nonpositive B.nonpositive

/-- The Q inclusion into the nonpositive coproduct. -/
abbrev pushoutInl {T : ModuleTensor.{u,v} k} {g : P ⟶ Q} {p : P ⟶ B}
    (X : T.AlgebraCoproduct (underlying g) (underlying p)) (hX : X.Formulas) :
    Q ⟶ pushout X hX := by
  change Q.toCommDGAlgebra ⟶ X.obj
  exact X.inl

/-- The B inclusion into the nonpositive coproduct. -/
abbrev pushoutInr {T : ModuleTensor.{u,v} k} {g : P ⟶ Q} {p : P ⟶ B}
    (X : T.AlgebraCoproduct (underlying g) (underlying p)) (hX : X.Formulas) :
    B ⟶ pushout X hX := by
  change B.toCommDGAlgebra ⟶ X.obj
  exact X.inr

/-- The base change B → B ⊗ₚ Q with its specified augmentation to C. -/
structure PushoutResolution {T : ModuleTensor.{u,v} k} {g : P ⟶ Q} {p : P ⟶ B}
    (c : B ⟶ C) (q : Q ⟶ C) (X : T.AlgebraCoproduct (underlying g) (underlying p))
    (hX : X.Formulas) where
  augmentation : pushout X hX ⟶ C
  ofQ_comp : (pushoutInl X hX) ≫ augmentation = q
  ofB_comp : (pushoutInr X hX) ≫ augmentation = c
  semifree : Semifree.IsSemifree B (pushoutInr X hX)
  ofQ_quasiIso : NonpositiveCDGA.IsQuasiIso (pushoutInl X hX)
  surjective : NonpositiveCDGA.DegreewiseSurjective augmentation
  quasiIso : NonpositiveCDGA.IsQuasiIso augmentation

abbrev PushoutResolution.model {T : ModuleTensor.{u,v} k} {g : P ⟶ Q} {p : P ⟶ B}
    {c : B ⟶ C} {q : Q ⟶ C} {X : T.AlgebraCoproduct (underlying g) (underlying p)}
    {hX : X.Formulas} (D : PushoutResolution c q X hX)
    (O : Differentials (pushoutInr X hX)) : Model c where
  algebra := pushout X hX
  base := pushoutInr X hX
  augmentation := D.augmentation
  triangle := D.ofB_comp
  semifree := D.semifree
  surjective := D.surjective
  quasiIso := D.quasiIso
  differentials := O

/-- No flatness assumption is imposed on B → C (or on P → B). -/
def PushoutResolves : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k),
    TensorFormulas T → T.Comparisons →
    ∀ {P Q B C : NonpositiveCDGA.{u,v} k}
      (g : P ⟶ Q) (p : P ⟶ B) (c : B ⟶ C) (q : Q ⟶ C)
      (X : T.AlgebraCoproduct (underlying g) (underlying p)) (hX : X.Formulas),
      g ≫ q = p ≫ c → Semifree.IsSemifree P g → NonpositiveCDGA.IsQuasiIso p →
      NonpositiveCDGA.DegreewiseSurjective q → NonpositiveCDGA.IsQuasiIso q →
      Nonempty (PushoutResolution c q X hX)

/-- Any maps A → B → C admit the two successive resolutions, with
relative differential models for P/A, Q/P and Q/A. -/
def ResolutionsExist : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B C : NonpositiveCDGA.{u,v} k}
    (b : A ⟶ B) (c : B ⟶ C),
    ∃ (R : Model b) (S : Model (R.augmentation ≫ c)),
      Semifree.IsSemifree A (R.base ≫ S.base) ∧ Nonempty (Differentials (R.base ≫ S.base))

/-- The cell presentation and the good-model properties are properties of
the actual module, in the original one-object category. -/
def GoodTerm (T : ModuleTensor.{u,v} k) {E : NonpositiveCDGA.{u,v} k} (M : E.Module) : Prop :=
  IndexedSemiFree.semiFree M ∧ KProjective.isKProjective M ∧ T.KFlat M

variable {b : A ⟶ B} {c : B ⟶ C}
variable (T : ModuleTensor.{u,v} k) (R : Model b) (S : Model (R.augmentation ≫ c))
variable (U : Differentials (R.base ≫ S.base))

/-- The same Q resolves C over A by the composite semifree map. -/
abbrev compositeModel (h : Semifree.IsSemifree A (R.base ≫ S.base)) : Model (b ≫ c) where
  algebra := S.algebra
  base := R.base ≫ S.base
  augmentation := S.augmentation
  triangle := by rw [Category.assoc, S.triangle, ← Category.assoc, R.triangle]
  semifree := h
  surjective := S.surjective
  quasiIso := S.quasiIso
  differentials := U

/-- The first term of the strict sequence after tensoring over Q with C. -/
abbrev leftTerm : C.Module :=
  (extend T S.augmentation).obj ((extend T S.base).obj R.differentials.module)

/-- The first term expressed using the cotangent model over B. -/
abbrev leftModel : C.Module := (extend T c).obj (R.module T)

/-- The middle term of the strict sequence after tensoring over Q with C. -/
abbrev middleTerm : C.Module := (extend T S.augmentation).obj U.module

/-- The quotient term of the strict sequence after tensoring over Q with C. -/
abbrev rightTerm : C.Module := S.module T

variable {T R S U}
variable {X : T.AlgebraCoproduct (underlying S.base) (underlying R.augmentation)}
variable {hX : X.Formulas}

/-- Identifications of the three strict terms. Formulas on the generating
symbols pin down both isomorphisms and thus also the transported arrows. -/
structure TermIdentifications (D : PushoutResolution c S.augmentation X hX)
    (W : Differentials (pushoutInr X hX)) where
  left : leftTerm T R S ≅ leftModel T R (c := c)
  right : rightTerm T R S ≅ (D.model W).module T
  left_symbol (i j n : ℤ) (h : i+j=n) (x : R.algebra.complex.X i) (a : C.complex.X j) :
    (left.hom.app ()).f n
      (T.tmul (underlying S.augmentation) (N := regular C.toCommDGAlgebra) i j n h
        (extendedSymbol T R.differentials S.base i 0 i (add_zero i) x S.algebra.one) a) =
      T.tmul (underlying c) (N := regular C.toCommDGAlgebra) i j n h
        (extendedSymbol T R.differentials R.augmentation i 0 i (add_zero i) x B.one) a
  right_symbol (i j n : ℤ) (h : i+j=n) (x : S.algebra.complex.X i) (a : C.complex.X j) :
    (right.hom.app ()).f n (extendedSymbol T S.differentials S.augmentation i j n h x a) =
      extendedSymbol T W D.augmentation i j n h (X.inl.chainMap.f i x) a

/-- The inclusion expressed on the iterated scalar extension of the
B-cotangent model. -/
abbrev TermIdentifications.inclusion {D : PushoutResolution c S.augmentation X hX}
    {W : Differentials (pushoutInr X hX)} (I : TermIdentifications D W)
    (F : DifferentialSequence T R.base S.base R.differentials U S.differentials) :
    leftModel T R (c := c) ⟶ middleTerm T R S U :=
  I.left.inv ≫ (extend T S.augmentation).map F.incl

/-- The projection expressed on the B-relative cotangent model over C. -/
abbrev TermIdentifications.projection {D : PushoutResolution c S.augmentation X hX}
    {W : Differentials (pushoutInr X hX)} (I : TermIdentifications D W)
    (F : DifferentialSequence T R.base S.base R.differentials U S.differentials) :
    middleTerm T R S U ⟶ (D.model W).module T :=
  (extend T S.augmentation).map F.proj ≫ I.right.hom

/-- For any given resolutions, the scalar-extended sequence is exact on the
specified maps, identifies with the cotangent models and consists of good
models over C. The left cotangent model over B may be used unchanged. -/
def ResolvedTerms : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k),
    TensorFormulas T → T.Comparisons →
    ∀ {A B C : NonpositiveCDGA.{u,v} k} {b : A ⟶ B} {c : B ⟶ C}
      (R : Model b) (S : Model (R.augmentation ≫ c))
      (U : Differentials (R.base ≫ S.base))
      (F : DifferentialSequence T R.base S.base R.differentials U S.differentials)
      (X : T.AlgebraCoproduct (underlying S.base) (underlying R.augmentation))
      (hX : X.Formulas) (D : PushoutResolution c S.augmentation X hX)
      (W : Differentials (pushoutInr X hX)),
      KProjective.isKProjective (R.module T) ∧ T.KFlat (R.module T) ∧
      Nonempty (TermIdentifications D W) ∧ F.extendedSplit (underlying S.augmentation) ∧
      GoodTerm T (leftTerm T R S) ∧ GoodTerm T (middleTerm T R S U) ∧
      GoodTerm T (rightTerm T R S)

/-- The exact derived extension of the B-cotangent model identifies with
the localized first term. The middle and last terms use the A → Q → C
and B → B ⊗ₚ Q → C cotangent models, respectively. -/
def LocalizedTerms : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {T : ModuleTensor.{u,v} k}
    {A B C : NonpositiveCDGA.{u,v} k} {b : A ⟶ B} {c : B ⟶ C}
    {R : Model b} {S : Model (R.augmentation ≫ c)}
    (U : Differentials (R.base ≫ S.base))
    (hs : Semifree.IsSemifree A (R.base ≫ S.base))
    {X : T.AlgebraCoproduct (underlying S.base) (underlying R.augmentation)}
    {hX : X.Formulas} {D : PushoutResolution c S.augmentation X hX}
    {W : Differentials (pushoutInr X hX)}
    (I : TermIdentifications D W)
    (F : DifferentialSequence T R.base S.base R.differentials U S.differentials)
    (hB : HomotopyCategoryLaws (oneObject B)) (hC : HomotopyCategoryLaws (oneObject C))
    (E : DerivedTensor.ScalarExtension T (underlying c) hB hC)
    (hp : KProjective.isKProjective (R.module T)),
    letI := Derived.homotopyCategory (oneObject B) hB
    letI := Derived.homotopyCategory (oneObject C) hC
    letI := DerivedKProjective.derivedCategoryInstance (oneObject B) hB
    letI := DerivedKProjective.derivedCategoryInstance (oneObject C) hC
    let QC := quotient (oneObject C) hC
    let L := E.onProjective (R.module T) hp
    ∃ (l : E.functor.obj (localizedModel hB R T) ≅ QC.obj (leftTerm T R S))
      (m : QC.obj (middleTerm T R S U) ≅ localizedModel hC (compositeModel R S U hs) T)
      (r : QC.obj (rightTerm T R S) ≅ localizedModel hC (D.model W) T),
      l.hom = L.hom ≫ QC.map (moduleClass hC I.left.inv) ∧
      m.hom = 𝟙 _ ∧
      r.hom = QC.map (moduleClass hC I.right.hom) ∧
      l.hom ≫ QC.map (moduleClass hC ((extend T S.augmentation).map F.incl)) ≫ m.hom =
        L.hom ≫ QC.map (moduleClass hC (I.inclusion F)) ∧
      QC.map (moduleClass hC ((extend T S.augmentation).map F.proj)) ≫ r.hom =
        m.hom ≫ QC.map (moduleClass hC (I.projection F))

end
end Specs.DerivedFormalization.Affine.ResolvedCotangentSequence
