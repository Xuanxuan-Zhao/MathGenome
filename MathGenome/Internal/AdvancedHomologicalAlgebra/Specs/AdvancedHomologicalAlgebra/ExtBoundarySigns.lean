import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
HA-R13 (boundary assertions), source lines 2114–2146 and 2174–2177.
Shifts and the derived category are the ones in HA-K01 and HA-D03.
The triangle closing map is the negative of the positive cone projection.
Ordinary Hom boundaries are to be compared using unsigned lift-and-differential
in injective Hom coordinates; the first-variable comparison has a degree sign.
-/
set_option linter.checkUnivs false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Pretriangulated.Opposite
open CochainComplex HomComplex
open Specs.AdvancedHomologicalAlgebra.StandardHeart
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

namespace Specs.AdvancedHomologicalAlgebra.ExtBoundarySigns

/-- Second-variable boundary in the representable triangle long exact sequence. -/
def triangleSecondType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex A) (hS : S.ShortExact)
  (X : A) (n : ℤ) (x : Ext X S.X₃ n),
  (preadditiveCoyoneda.obj (Opposite.op ((stalk A).obj X))).homologySequenceδ
    hS.singleTriangle n (n+1) rfl x =
    x ≫ hS.singleδ⟦n⟧' ≫
      (CategoryTheory.shiftFunctorAdd' (DerivedCategory A) 1 n (n+1) (add_comm 1 n)).inv.app _

/-- First-variable triangle boundary; this is distinct from the ordinary boundary. -/
def triangleFirstType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex A) (hS : S.ShortExact)
  (Y : A) (n : ℤ) (x : Ext S.X₁ Y n),
  (preadditiveYoneda.obj ((stalk A).obj Y)).homologySequenceδ
    ((triangleOpEquivalence _).functor.obj (Opposite.op hS.singleTriangle))
      n (n+1) rfl x =
    hS.singleδ ≫ x⟦(1 : ℤ)⟧' ≫
      (CategoryTheory.shiftFunctorAdd' (DerivedCategory A) n 1 (n+1) rfl).inv.app _

/-- The roof with the positive projection is the negative of the triangle boundary.
This statement applies to all short exact sequences of complexes, including stalks. -/
def positiveProjectionType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex (CochainComplex A ℤ))
  (hS : S.ShortExact),
  letI := mappingCone.quasiIso_descShortComplex hS
  inv (_root_.DerivedCategory.Q.map (mappingCone.descShortComplex S)) ≫
    _root_.DerivedCategory.Q.map
      (Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift S.f) ≫
    (_root_.DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ =
      -_root_.DerivedCategory.triangleOfSESδ hS

/-- Unsigned lift-and-differential boundary in the contravariant Hom complex.
The hypotheses say that w extends u and dw descends to v. They do not
assume any identity between the resulting derived classes. -/
def ordinaryFirstComplexType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex (CochainComplex A ℤ))
  (hS : S.ShortExact) (I : CochainComplex A ℤ) (n : ℤ)
  (u : Cocycle S.X₁ I n) (v : Cocycle S.X₃ I (n+1)) (w : Cochain S.X₂ I n),
  (Cochain.ofHom S.f).comp w (zero_add n) = u.1 →
  δ n (n+1) w = (v.precomp S.g).1 →
  classToDerived _ _ (n+1) (CohomologyClass.mk v) =
    (n+1).negOnePow • ShiftedHom.comp (_root_.DerivedCategory.triangleOfSESδ hS)
      (classToDerived _ _ n (CohomologyClass.mk u)) rfl

/-- Unsigned lift-and-differential boundary in the covariant Hom complex:
b lifts z and db is the image of a. This applies in particular to
any degreewise split injective horseshoe model. -/
def ordinarySecondComplexType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex (CochainComplex A ℤ))
  (hS : S.ShortExact) (K : CochainComplex A ℤ) (n : ℤ)
  (z : Cocycle K S.X₃ n) (a : Cocycle K S.X₁ (n+1)) (b : Cochain K S.X₂ n),
  b.comp (Cochain.ofHom S.g) (add_zero n) = z.1 →
  δ n (n+1) b = (a.postcomp S.f).1 →
  classToDerived _ _ (n+1) (CohomologyClass.mk a) =
    ShiftedHom.comp (classToDerived _ _ n (CohomologyClass.mk z))
      (_root_.DerivedCategory.triangleOfSESδ hS) (add_comm 1 n)

/-- The ordinary first-variable boundary under the canonical injective Hom
comparison. The two cochain equations are the usual unsigned extension w
of u and descent of dw to the quotient. Any quasi-isomorphic target model
is allowed, hence in particular every bounded-below injective resolution. -/
def ordinaryFirstType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex A) (hS : S.ShortExact)
  (Y : A) (I : CochainComplex A ℤ)
  (ι : (CochainComplex.singleFunctor A 0).obj Y ⟶ I) (hι : QuasiIso ι)
  (n : ℤ) (u : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₁) I n)
  (v : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₃) I (n+1))
  (w : Cochain ((CochainComplex.singleFunctor A 0).obj S.X₂) I n),
  (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.f)).comp w (zero_add n) = u.1 →
  δ n (n+1) w = (v.precomp ((CochainComplex.singleFunctor A 0).map S.g)).1 →
  injectiveClassMap S.X₃ Y I ι hι (n+1) (CohomologyClass.mk v) =
    (n+1).negOnePow • ShiftedHom.comp hS.singleδ
      (injectiveClassMap S.X₁ Y I ι hι n (CohomologyClass.mk u)) rfl

/-- The ordinary second-variable boundary for every compatible horseshoe model.
`ρ` is the augmentation of the short exact sequence of stalks into the
short exact sequence of resolving complexes. We allow arbitrary resolving
complexes, which is stronger than requiring bounded-below injective ones.
All unsigned lifts b and their differentials a have the asserted class.
There is no assumed identity involving a connecting morphism. -/
def ordinarySecondType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex A) (hS : S.ShortExact)
  (T : ShortComplex (CochainComplex A ℤ)) (_hT : T.ShortExact)
  (ρ : S.map (CochainComplex.singleFunctor A 0) ⟶ T)
  (hρ₁ : QuasiIso ρ.τ₁) (_hρ₂ : QuasiIso ρ.τ₂) (hρ₃ : QuasiIso ρ.τ₃)
  (X : A) (n : ℤ) (z : Cocycle ((CochainComplex.singleFunctor A 0).obj X) T.X₃ n)
  (a : Cocycle ((CochainComplex.singleFunctor A 0).obj X) T.X₁ (n+1))
  (b : Cochain ((CochainComplex.singleFunctor A 0).obj X) T.X₂ n),
  b.comp (Cochain.ofHom T.g) (add_zero n) = z.1 →
  δ n (n+1) b = (a.postcomp T.f).1 →
  injectiveClassMap X S.X₁ T.X₁ ρ.τ₁ hρ₁ (n+1) (CohomologyClass.mk a) =
    ShiftedHom.comp (injectiveClassMap X S.X₃ T.X₃ ρ.τ₃ hρ₃ n (CohomologyClass.mk z))
      hS.singleδ (add_comm 1 n)

/-- Every cocycle has the ordinary first-variable lift and descended
cocycle when the terms of the target are injective. -/
def firstLiftsType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (S : ShortComplex A) (_hS : S.ShortExact) (I : CochainComplex A ℤ)
  (_hinj : ∀ i, Injective (I.X i)) (n : ℤ)
  (u : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₁) I n),
  ∃ (w : Cochain ((CochainComplex.singleFunctor A 0).obj S.X₂) I n)
    (v : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₃) I (n+1)),
    (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.f)).comp w (zero_add n) = u.1 ∧
    δ n (n+1) w = (v.precomp ((CochainComplex.singleFunctor A 0).map S.g)).1

/-- Every cocycle has the usual second-variable lift and differential
in a degreewise split short exact sequence (in particular an injective
horseshoe sequence). No projectivity of X is required. -/
def secondLiftsType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (S : ShortComplex (CochainComplex A ℤ)) (_hS : S.ShortExact)
  (_hsplit : ∀ i : ℤ, Nonempty (S.map (HomologicalComplex.eval A (.up ℤ) i)).Splitting)
  (X : A) (n : ℤ) (z : Cocycle ((CochainComplex.singleFunctor A 0).obj X) S.X₃ n),
  ∃ (b : Cochain ((CochainComplex.singleFunctor A 0).obj X) S.X₂ n)
    (a : Cocycle ((CochainComplex.singleFunctor A 0).obj X) S.X₁ (n+1)),
    b.comp (Cochain.ofHom S.g) (add_zero n) = z.1 ∧
    δ n (n+1) b = (a.postcomp S.f).1

/-- In an injective horseshoe the splitting needed for ordinary
second-variable lifts follows from injectivity; it is not an additional
assumption on the short exact sequence. -/
def secondInjectiveLiftsType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (S : ShortComplex (CochainComplex A ℤ)) (_hS : S.ShortExact)
  (_hinj : ∀ i : ℤ, Injective (S.X₁.X i))
  (X : A) (n : ℤ) (z : Cocycle ((CochainComplex.singleFunctor A 0).obj X) S.X₃ n),
  ∃ (b : Cochain ((CochainComplex.singleFunctor A 0).obj X) S.X₂ n)
    (a : Cocycle ((CochainComplex.singleFunctor A 0).obj X) S.X₁ (n+1)),
    b.comp (Cochain.ofHom S.g) (add_zero n) = z.1 ∧
    δ n (n+1) b = (a.postcomp S.f).1

end Specs.AdvancedHomologicalAlgebra.ExtBoundarySigns
