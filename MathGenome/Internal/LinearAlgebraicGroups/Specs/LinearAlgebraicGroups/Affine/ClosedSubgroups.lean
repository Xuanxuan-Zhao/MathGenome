import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.HopfAlgebras
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open Coalgebra HopfAlgebra WithConv
open scoped TensorProduct CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups

noncomputable section

variable {k : Type u} [Field k]

abbrev specGroup (A : HopfAlgebraCategory k) : Specs.GroupScheme k :=
  (hopfSpec (CommRingCat.of k)).obj (op A)

abbrev specGroupMap {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    specGroup B ⟶ specGroup A :=
  (hopfSpec (CommRingCat.of k)).map f.op

abbrev hopfQuotient (A : HopfAlgebraCategory k) (I : Ideal A) [I.IsHopfIdeal k] :
    HopfAlgebraCategory k :=
  CommHopfAlgCat.of k (A ⧸ I)

abbrev hopfQuotientMap (A : HopfAlgebraCategory k) (I : Ideal A) [I.IsHopfIdeal k] :
    A ⟶ hopfQuotient A I :=
  CommHopfAlgCat.ofHom (Bialgebra.Quotient.mkBialgHom I)

namespace Specs

/-- The conjugation morphism is evaluated on the two universal projections. -/
def subgroupConjugation {G H : Specs.GroupScheme k} (i : H ⟶ G) :
    CategoryTheory.MonoidalCategory.tensorObj G.X H.X ⟶ G.X :=
  (fst G.X H.X * (snd G.X H.X ≫ i.hom.hom)) * (fst G.X H.X)⁻¹

/-- Normality asks for factorization of the whole conjugation morphism. -/
def IsNormalSubgroup {G H : Specs.GroupScheme k} (i : H ⟶ G) : Prop :=
  ∃ c : CategoryTheory.MonoidalCategory.tensorObj G.X H.X ⟶ H.X, c ≫ i.hom.hom = subgroupConjugation i

def augmentationIdeal (B : HopfAlgebraCategory k) : Ideal B :=
  RingHom.ker (Bialgebra.counitAlgHom k B)

def kernelIdeal {A B : HopfAlgebraCategory k} (a : B ⟶ A) : Ideal A :=
  (augmentationIdeal B).map a.hom.toAlgHom

structure ClosedSubgroup (G : GroupScheme k) where
  group : GroupScheme k
  inclusion : group ⟶ G
  isClosedImmersion : IsClosedImmersion inclusion.hom.hom.left

def ClosedSubgroupType := ∀ {k : Type u} [Field k], GroupScheme k → Type (u + 1)
def ClosedSubgroupValue : ClosedSubgroupType.{u} := @ClosedSubgroup
def NormalSubgroupType := ∀ {k : Type u} [Field k] {G H : GroupScheme k}, (H ⟶ G) → Prop
def AugmentationIdealType := ∀ {k : Type u} [Field k] (B : HopfAlgebraCategory k), Ideal B
def KernelIdealType := ∀ {k : Type u} [Field k] {A B : HopfAlgebraCategory k}, (B ⟶ A) → Ideal A

end Specs

abbrev hopfCounit (B : HopfAlgebraCategory k) : B ⟶ CommHopfAlgCat.of k k :=
  CommHopfAlgCat.ofHom (Bialgebra.counitBialgHom k B)

abbrev hopfUnit (B : HopfAlgebraCategory k) : CommHopfAlgCat.of k k ⟶ B :=
  CommHopfAlgCat.ofHom (Bialgebra.unitBialgHom k B)

abbrev extendedHopf (K : Type u) [Field K] [Algebra k K] (A : HopfAlgebraCategory k) :
    HopfAlgebraCategory K :=
  CommHopfAlgCat.of K (K ⊗[k] A)

abbrev extendedHopfMap (K : Type u) [Field K] [Algebra k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B) : extendedHopf K A ⟶ extendedHopf K B :=
  CommHopfAlgCat.ofHom (Bialgebra.TensorProduct.map (BialgHom.id K K) f.hom)

namespace Specs

def extendedIdeal (K : Type u) [Field K] [Algebra k K]
    {A : HopfAlgebraCategory k} (I : Ideal A) : Ideal (extendedHopf K A) :=
  I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)

def ExtendedIdealType :=
  ∀ {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {A : HopfAlgebraCategory k}, Ideal A → Ideal (extendedHopf K A)

def TextbookHopfIdeal : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k) (I : Ideal A),
    I.IsHopfIdeal k ↔
      (∀ x ∈ I, comul (R := k) x ∈
        LinearMap.range (LinearMap.rTensor A (I.restrictScalars k).subtype) ⊔
        LinearMap.range (LinearMap.lTensor A (I.restrictScalars k).subtype)) ∧
      (∀ x ∈ I, counit (R := k) x = 0) ∧
      (∀ x ∈ I, antipode k x ∈ I)

def HopfMapClosedImmersion : Prop :=
  ∀ (k : Type u) [Field k] {A B : HopfAlgebraCategory k} (a : A ⟶ B),
    IsClosedImmersion (specGroupMap a).hom.hom.left ↔ Function.Surjective a.hom

/-- Classification of subgroup inclusions of the spectrum up to isomorphism over it. -/
def ClosedSubgroupClassification : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k)
    (H : GroupScheme k) (i : H ⟶ specGroup A),
    IsClosedImmersion i.hom.hom.left ↔
      ∃! I : Ideal A, ∃ (_ : I.IsHopfIdeal k), ∃ e : H ≅ specGroup (hopfQuotient A I),
        e.hom ≫ specGroupMap (hopfQuotientMap A I) = i

def HopfKernelIdeal : Prop :=
  ∀ (k : Type u) [Field k] {A B : HopfAlgebraCategory k} (a : B ⟶ A),
    (kernelIdeal a).IsHopfIdeal k

def HopfIdealSup : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k)
    (I J : Ideal A) [I.IsHopfIdeal k] [J.IsHopfIdeal k], (I ⊔ J).IsHopfIdeal k

/-- The sum of an arbitrary family of Hopf ideals is a Hopf ideal. -/
def HopfIdeal_iSup : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k) {Index : Sort v}
    (I : Index → Ideal A) [∀ i, (I i).IsHopfIdeal k], (⨆ i, I i).IsHopfIdeal k

/-- The ideal generated by the pulled-back augmentation ideal cuts out the
scheme-theoretic kernel, and its inclusion is normal. -/
def SchemeKernel : Prop :=
  ∀ (k : Type u) [Field k] {A B : HopfAlgebraCategory k} (a : B ⟶ A)
    [(kernelIdeal a).IsHopfIdeal k],
    let Q := hopfQuotient A (kernelIdeal a)
    let i := specGroupMap (hopfQuotientMap A (kernelIdeal a))
    IsPullback i (specGroupMap (hopfUnit Q)) (specGroupMap a)
        (specGroupMap (hopfCounit B)) ∧ IsNormalSubgroup i

/-- The sum cuts out the intersection as a pullback of group schemes. -/
def SubgroupIntersection : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k)
    (I J : Ideal A) [I.IsHopfIdeal k] [J.IsHopfIdeal k] [(I ⊔ J).IsHopfIdeal k],
    ∃ (p : specGroup (hopfQuotient A (I ⊔ J)) ⟶ specGroup (hopfQuotient A I))
      (q : specGroup (hopfQuotient A (I ⊔ J)) ⟶ specGroup (hopfQuotient A J)),
      IsPullback p q (specGroupMap (hopfQuotientMap A I))
          (specGroupMap (hopfQuotientMap A J)) ∧
        p ≫ specGroupMap (hopfQuotientMap A I) = specGroupMap (hopfQuotientMap A (I ⊔ J))

/-- The quotient by the sum is the intersection in group schemes and on underlying schemes. -/
def SubgroupFamilyIntersection : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k) {Index : Type v}
    (I : Index → Ideal A) [∀ i, (I i).IsHopfIdeal k],
    ∃ h : (⨆ i, I i).IsHopfIdeal k,
      letI := h
      let q := specGroupMap (hopfQuotientMap A (⨆ i, I i))
      let inc (i : Index) := specGroupMap (hopfQuotientMap A (I i))
      ∃ (p : ∀ i, specGroup (hopfQuotient A (⨆ i, I i)) ⟶ specGroup (hopfQuotient A (I i)))
        (hp : ∀ i, p i ≫ inc i = q),
        let c := WidePullbackCone.mk q p hp
        Nonempty (IsLimit c) ∧ Nonempty (IsLimit ((Grp.forget (SchemeOver k)).mapCone c))

def ExtendedHopfIdeal : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (I : Ideal A) [I.IsHopfIdeal k],
      (extendedIdeal K I).IsHopfIdeal K

/-- Scalar extension of the quotient commutes with the quotient map. -/
def ExtendedHopfQuotient : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (I : Ideal A) [I.IsHopfIdeal k]
    [(extendedIdeal K I).IsHopfIdeal K],
    ∃ e : hopfQuotient (extendedHopf K A) (extendedIdeal K I) ≅
      extendedHopf K (hopfQuotient A I),
      hopfQuotientMap (extendedHopf K A) (extendedIdeal K I) ≫ e.hom =
        extendedHopfMap K (hopfQuotientMap A I)

def ExtendedKernelIdeal : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {A B : HopfAlgebraCategory k} (a : B ⟶ A),
    extendedIdeal K (kernelIdeal a) = kernelIdeal (extendedHopfMap K a)

def ExtendedIdealSup : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (I J : Ideal A),
    extendedIdeal K (I ⊔ J) = extendedIdeal K I ⊔ extendedIdeal K J

def ExtendedIdeal_iSup : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) {Index : Sort v} (I : Index → Ideal A),
    extendedIdeal K (⨆ i, I i) = ⨆ i, extendedIdeal K (I i)

/-- Base change preserves the cartesian squares that define kernels and intersections. -/
def BaseChangeSubgroupPullback : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G H L P : GroupScheme k} {i : P ⟶ G} {j : P ⟶ H} {f : G ⟶ L} {g : H ⟶ L},
    IsPullback i j f g →
      IsPullback ((groupBaseChange k K).map i) ((groupBaseChange k K).map j)
        ((groupBaseChange k K).map f) ((groupBaseChange k K).map g)

/-- Field extension preserves intersections indexed by any type. -/
def BaseChangeSubgroupFamilyIntersection : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] {Index : Type v}
    {F : WidePullbackShape Index ⥤ GroupScheme k} {c : Cone F},
    Nonempty (IsLimit ((Grp.forget (SchemeOver k)).mapCone c)) →
      let cK := (groupBaseChange k K).mapCone c
      Nonempty (IsLimit cK) ∧ Nonempty (IsLimit ((Grp.forget (SchemeOver K)).mapCone cK))

def BaseChangeClosedSubgroup : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme k} (i : H ⟶ G),
    IsClosedImmersion i.hom.hom.left →
      IsClosedImmersion ((groupBaseChange k K).map i).hom.hom.left

def BaseChangeNormalSubgroup : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme k} (i : H ⟶ G),
    IsNormalSubgroup i → IsNormalSubgroup ((groupBaseChange k K).map i)

/-- For a closed subgroup, normality can be checked after any field extension. -/
def BaseChangeNormalSubgroupIff : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme k} (i : H ⟶ G),
    IsClosedImmersion i.hom.hom.left →
      (IsNormalSubgroup ((groupBaseChange k K).map i) ↔ IsNormalSubgroup i)

/-- The base-changed inclusion is the spectrum of the quotient by the extended ideal. -/
def BaseChangeQuotientInclusion : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (I : Ideal A) [I.IsHopfIdeal k]
    [(extendedIdeal K I).IsHopfIdeal K],
    let J := extendedIdeal K I
    let E := extendedHopf K A
    ∃ (eG : specGroup E ≅ (groupBaseChange k K).obj (specGroup A))
      (eH : specGroup (hopfQuotient E J) ≅
        (groupBaseChange k K).obj (specGroup (hopfQuotient A I))),
      specGroupMap (hopfQuotientMap E J) ≫ eG.hom =
        eH.hom ≫ (groupBaseChange k K).map (specGroupMap (hopfQuotientMap A I))

end Specs
end
end LinearAlgebraicGroups
