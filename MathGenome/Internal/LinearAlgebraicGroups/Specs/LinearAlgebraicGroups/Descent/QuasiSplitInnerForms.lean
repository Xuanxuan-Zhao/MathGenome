import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeFormComparison

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u v w

namespace LinearAlgebraicGroups.Specs.QuasiSplitInnerForms

open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology

section Cohomology

variable {Γ : Type u} {M : Type v} {D : Type w}
  [Group Γ] [TopologicalSpace Γ] [Group M] [TopologicalSpace M]
  [Group D] [TopologicalSpace D]

/-- Compatibility of a coefficient homomorphism with the two actions. -/
def Equivariant {ρ : Γ →* MulAut M} {ρD : Γ →* MulAut D} (p : M →* D) : Prop :=
  ∀ σ x, p (ρ σ x) = ρD σ (p x)

/-- Pushforward of continuous cocycles along an equivariant homomorphism. -/
def mapCocycle {ρ : Γ →* MulAut M} {ρD : Γ →* MulAut D}
    (p : M →* D) (hp : Continuous p) (he : Equivariant (ρ := ρ) (ρD := ρD) p)
    (a : Cocycle ρ) : Cocycle ρD :=
  ⟨fun σ => p (a σ), hp.comp a.property.1, fun σ τ => by
    change p (a (σ * τ)) = p (a σ) * ρD σ (p (a τ))
    rw [a.property.2, map_mul, he]⟩

/-- The resulting map on pointed sets. -/
def mapH1 {ρ : Γ →* MulAut M} {ρD : Γ →* MulAut D}
    (p : M →* D) (hp : Continuous p) (he : Equivariant (ρ := ρ) (ρD := ρD) p) :
    H1 ρ → H1 ρD :=
  Quotient.map (mapCocycle p hp he) (by
    intro a b
    rintro ⟨t, ht⟩
    refine ⟨p t, fun σ => ?_⟩
    change p (b σ) = (p t)⁻¹ * p (a σ) * ρD σ (p t)
    rw [ht σ, map_mul, map_mul, map_inv, he])

/-- The conjugate action belonging to a cocycle, expressed on the ambient group.
For the exact automorphism sequence this restricts to the twisted adjoint action. -/
def twistedAction {ρ : Γ →* MulAut M} (a : Cocycle ρ) : Γ →* MulAut M where
  toFun σ := MulAut.conj (a σ) * ρ σ
  map_one' := by
    have h : a 1 = a 1 * a 1 := by simpa using a.property.2 1 1
    have h₁ : a 1 = 1 := by
      apply mul_left_cancel (a := a 1)
      simpa only [mul_one] using h.symm
    simp [h₁]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    change a (σ * τ) * ρ (σ * τ) x * (a (σ * τ))⁻¹ =
      a σ * ρ σ (a τ * ρ τ x * (a τ)⁻¹) * (a σ)⁻¹
    rw [a.property.2, map_mul ρ, mul_inv_rev]
    simp only [MulAut.mul_apply, map_mul, map_inv, mul_assoc]

/-- Being obtainable from a by a cocycle for the twisted action in the
inner kernel. The kernel-valued cocycle is written in the ambient group
using the injective kernel map. -/
def IsInnerTwist {ρ : Γ →* MulAut M} (p : M →* D)
    (a : Cocycle ρ) (y : H1 ρ) : Prop :=
  ∃ (b : Cocycle ρ) (d : Cocycle (twistedAction a)),
    classOf b = y ∧ ∀ σ, p (d σ) = 1 ∧ b σ = d σ * a σ

/-- Every element of the fiber is an inner twist, and every such twist lies in
the fiber. -/
def OuterFiberCriterion : Prop :=
  ∀ {Γ : Type u} {M : Type v} {D : Type w}
    [Group Γ] [TopologicalSpace Γ]
    [Group M] [TopologicalSpace M] [DiscreteTopology M] [Group D] [TopologicalSpace D]
    {ρ : Γ →* MulAut M} {ρD : Γ →* MulAut D} (p : M →* D)
    (hp : Continuous p) (he : Equivariant (ρ := ρ) (ρD := ρD) p),
    Function.Surjective p → Continuous (fun x : Γ × M => ρ x.1 x.2) →
    ∀ (a : Cocycle ρ) (y : H1 ρ),
      mapH1 p hp he y = mapH1 p hp he (classOf a) ↔ IsInnerTwist p a y

/-- An equivariant section gives a preferred class in every outer fiber. -/
def OuterFiberSection : Prop :=
  ∀ {Γ : Type u} {M : Type v} {D : Type w}
    [Group Γ] [TopologicalSpace Γ] [Group M] [TopologicalSpace M]
    [Group D] [TopologicalSpace D] {ρ : Γ →* MulAut M} {ρD : Γ →* MulAut D}
    (p : M →* D) (hp : Continuous p) (he : Equivariant (ρ := ρ) (ρD := ρD) p)
    (s : D →* M) (hs : Continuous s) (se : Equivariant (ρ := ρD) (ρD := ρ) s),
    (∀ x, p (s x) = x) →
    Function.RightInverse (mapH1 s hs se) (mapH1 p hp he)

end Cohomology

section FieldPoints

open AutomorphismSequence
open RootGroups (AdditiveLine)
open Pinning (AttachedDatum PinnedGroup)
open _root_.LinearAlgebraicGroups.Descent.Forms (SchemeModels SchemeFormClasses)

noncomputable section

variable (k S : Type u) [Field k] [Field S] [Algebra k S]

open RelativeFormComparison
  (fieldTest fieldMap relativeAction automorphismAction transportedAut RelativeClassification)

/-- Evaluation on the one-point spectrum identifies the constant outer group
with the group of based datum automorphisms. -/
def constantEvaluation (D : Type u) [Group D] :
    ((constantGroup (k := k) D).obj (op (fieldTest k S))) ≃* D where
  toFun x := x.down (IsLocalRing.closedPoint S)
  invFun d := ⟨LocallyConstant.const _ d⟩
  left_inv x := by
    apply ULift.ext
    apply LocallyConstant.ext
    intro t
    exact congrArg x.down (Subsingleton.elim (IsLocalRing.closedPoint S) t)
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {k S} {A : AdditiveLine k} {P : PinnedGroup A}
  {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
  {Q : AdjointQuotient P.pair.G}

/-- The actual outer homomorphism on separable-closure points of the fppf sequence. -/
def outerHom (E : SplitSequence P D l Q) :
    RelativeAut P.pair.G.val (fieldTest k S) →* Aut D.toBased :=
  (constantEvaluation k S _).toMonoidHom.comp
    (E.toExactSequence.outer.app (op (fieldTest k S))).hom

/-- The pinned section evaluated on points, with constants identified with their labels. -/
def pinnedSection (E : SplitSequence P D l Q) :
    Aut D.toBased →* RelativeAut P.pair.G.val (fieldTest k S) :=
  (E.sectionMap.app (op (fieldTest k S))).hom.comp (constantEvaluation k S _).symm.toMonoidHom

local instance relativeAutTopology (G : GroupScheme k) :
    TopologicalSpace (RelativeAut G (fieldTest k S)) := ⊥

local instance basedAutTopology (D : Pinning.BasedRootDatum.{u}) :
    TopologicalSpace (Aut D) := ⊥

local instance relativeAutDiscrete (G : GroupScheme k) :
    DiscreteTopology (RelativeAut G (fieldTest k S)) := ⟨rfl⟩

local instance basedAutDiscrete (D : Pinning.BasedRootDatum.{u}) :
    DiscreteTopology (Aut D) := ⟨rfl⟩

local instance fieldGalTopology : TopologicalSpace (Gal(S/k)) := krullTopology k S

/-- The based datum of the split group has trivial Galois action. -/
abbrev trivialOuterAction (D : Pinning.BasedRootDatum.{u}) : Gal(S/k) →* MulAut (Aut D) := 1

/-- Compatibility of the projection and pinning with Galois restriction. -/
def CoefficientMaps (E : SplitSequence P D l Q) : Prop :=
  Equivariant (ρ := automorphismAction k S P.pair.G.val)
      (ρD := trivialOuterAction (k := k) (S := S) D.toBased) (outerHom (S := S) E) ∧
  Equivariant (ρ := trivialOuterAction (k := k) (S := S) D.toBased)
      (ρD := automorphismAction k S P.pair.G.val) (pinnedSection (S := S) E) ∧
  Function.RightInverse (pinnedSection (S := S) E) (outerHom (S := S) E)

def SplitCoefficientMaps : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] {A : AdditiveLine k}
    {P : PinnedGroup A} {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {Q : AdjointQuotient P.pair.G} (E : SplitSequence P D l Q), CoefficientMaps (S := S) E

variable (k S)

/-- Cohomology of the actual automorphism group on the chosen separable closure. -/
abbrev AutomorphismClasses (G : GroupScheme k) := H1 (automorphismAction k S G)

variable {k S}

open GeometricBorelConjugacy (IsKBorel IsQuasiSplit)
open GeometricRadicals (IsReductive IsTorus)
open RankOneFlag (IsGeometricallyMaximal)
open AdjointBorelCohomology (PinnedTwist)

/-- A continuous homomorphism to the discrete outer group factors through
some finite Galois restriction, even when the outer group is infinite. -/
def FiniteOuterLevel : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (D : Pinning.BasedRootDatum.{u})
    (ω : Cocycle (trivialOuterAction (k := k) (S := S) D)),
    ∃ (L : FiniteGaloisIntermediateField k S) (ωL : Gal(L/k) →* Aut D),
      ∀ σ, ωL (restriction L σ) = ω σ

/-- The standard model for a fiber, with the chosen outer cocycle descended
from a finite layer, and with its actual descended Borel and torus. -/
structure PinnedRepresentative (E : SplitSequence P D l Q)
    (ω : Cocycle (trivialOuterAction (k := k) (S := S) D.toBased)) where
  model : SchemeModels S P.pair.G
  reductive : IsReductive model.val
  B : ClosedSubgroup model.val.val
  T : ClosedSubgroup model.val.val
  borel : IsKBorel B
  torus : IsTorus T.group
  maximal : IsGeometricallyMaximal T
  j : T.group ⟶ B.group
  j_comm : j ≫ B.inclusion = T.inclusion
  layer : FiniteGaloisIntermediateField k S
  data : PinnedTwist (P := P) layer D l B T
  outer_eq : ∀ σ, data.outer (restriction layer σ) = ω σ
  trivialization : relativePoints P.pair.G.val (fieldTest k S) ≅
    relativePoints model.val.val (fieldTest k S)
  transport_eq : ∀ σ, transportedAut k S trivialization σ = pinnedSection E (ω σ)

/-- Construction of the descended pinned pair for every outer cocycle. -/
def PinnedRepresentatives : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q)
    (ω : Cocycle (trivialOuterAction (k := k) (S := S) D.toBased)),
    Nonempty (PinnedRepresentative (S := S) E ω)

open AdjointBorelCohomology (ImageBorel)
open AdjointCocharacters (IsAdjointQuotient)

/-- An inner-valued automorphism cocycle uniquely lifts to an actual
adjoint cocycle on the given ground-field form. -/
def LiftInnerCocycle : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    (G Q : GroupScheme k) (inn : groupSections Q ⟶ automorphisms G),
    Function.Injective (inn.app (op (fieldTest k S))) →
    ∀ a : Cocycle (automorphismAction k S G),
      (∀ σ, a σ ∈ (inn.app (op (fieldTest k S))).hom.range) →
      ∃! d : @Cocycle (Gal(S/k)) (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points k S Q.X)
          _ (krullTopology k S) _ ⊥ (pointAction k S Q.X),
        ∀ σ, inn.app (op (fieldTest k S)) ⟨d σ⟩ = a σ

/-- The inner displacement on the split model lies in the range of its
adjoint kernel map exactly when its outer image is the identity. -/
def SplitKernel : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] {A : AdditiveLine k}
    {P : PinnedGroup A} {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {Q : AdjointQuotient P.pair.G} (E : SplitSequence P D l Q)
    (f : RelativeAut P.pair.G.val (fieldTest k S)),
    outerHom (S := S) E f = 1 ↔
      f ∈ (E.toExactSequence.inner.app (op (fieldTest k S))).hom.range

/-- The displacement of an isomorphism of two forms is the difference of
their two transported cocycles, conjugated by the first trivialization. -/
def DifferenceOfTrivializations : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] {G H J : GroupScheme k}
    (i : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S))
    (j : relativePoints G (fieldTest k S) ≅ relativePoints J (fieldTest k S))
    (σ : Gal(S/k)),
    transportedAut k S (i.symm ≪≫ j) σ =
      Aut.autMulEquivOfIso i (transportedAut k S j σ * (transportedAut k S i σ)⁻¹)

/-- A coboundary adjustment is realized by composing the trivialization
with the adjusting automorphism of the split model. -/
def ChangeOfTrivialization : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] {G H : GroupScheme k}
    (i : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S))
    (b : RelativeAut G (fieldTest k S)) (σ : Gal(S/k)),
    transportedAut k S (b.asIso ≪≫ i) σ =
      b⁻¹ * transportedAut k S i σ * automorphismAction k S G σ b

/-- Two forms are inner forms of each other if some isomorphism over the
separable closure has Galois displacement in the actual adjoint image. -/
def AreInnerForms (G H : AffineAlgebraicGroup k) : Prop :=
  ∃ (V : AdjointQuotient G) (inn : groupSections V.quotient.val ⟶ automorphisms G.val),
    (∀ (U : SchemeOver k) (g : U ⟶ G.val.X),
      inn.app (op U) ⟨g ≫ V.projection.hom.hom⟩ = innerAut g) ∧
    (∀ U, Function.Injective (inn.app U)) ∧
    ∃ i : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val (fieldTest k S),
      ∀ σ, transportedAut k S i σ ∈ (inn.app (op (fieldTest k S))).hom.range

/-- The full assertion on forms, using the same fppf sequence and pinning as
the sequence theorem. The unique quasi-split class is the image of the
given outer class under the pinned section. -/
def FormStatement (E : SplitSequence P D l Q)
    (C : RelativeClassification k S P.pair.G) : Prop :=
  ∃ h : CoefficientMaps (S := S) E,
    let p := mapH1 (outerHom (S := S) E) continuous_of_discreteTopology h.1
    let s := mapH1 (pinnedSection (S := S) E) continuous_of_discreteTopology h.2.1
    (∀ (a : Cocycle (automorphismAction k S P.pair.G.val))
      (y : AutomorphismClasses k S P.pair.G.val),
      p y = p (classOf a) ↔ IsInnerTwist (outerHom (S := S) E) a y) ∧
    (∀ H J : SchemeModels S P.pair.G,
      p (C.equiv (Quotient.mk _ J)) = p (C.equiv (Quotient.mk _ H)) ↔
        AreInnerForms (S := S) H.val J.val) ∧
    (∀ ω, Nonempty (PinnedRepresentative (S := S) E ω)) ∧
    ∀ x (y : SchemeFormClasses S P.pair.G),
      (p (C.equiv y) = x ∧
        ∃ H : SchemeModels S P.pair.G, Quotient.mk _ H = y ∧ IsQuasiSplit H.val) ↔
      C.equiv y = s x

/-- Source result F06 for an arbitrary base field and chosen separable closure. -/
def Statement : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {A : AdditiveLine k} (P : PinnedGroup A),
    ∃ (D : AttachedDatum P.pair) (l : Aut D.toBased ≃* Aut P)
      (Q : AdjointQuotient P.pair.G) (E : SplitSequence P D l Q),
      Twists E.toExactSequence ∧
      ∃ C : RelativeClassification k S P.pair.G, FormStatement (S := S) E C

end
end FieldPoints

end LinearAlgebraicGroups.Specs.QuasiSplitInnerForms
