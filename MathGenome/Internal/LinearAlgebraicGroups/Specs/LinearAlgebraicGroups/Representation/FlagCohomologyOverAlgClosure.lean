import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.FlagCohomologyOverAlgClosure

noncomputable section
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false

open CharacterDescent (Character)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open FlagLineBundle (OppositeBorelPair BorelProjection)
open FlagCohomology
open GeometricRadicals
open GeometricBorelConjugacy (IsKBorel)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open QuotientEmbedding (Presentation IsQuasiProjective)

variable {k : Type u} [Field k]

/-- A closed subgroup with its original inclusion after extension to the algebraic closure. -/
abbrev geometricSubgroup {G : GroupScheme k} (H : ClosedSubgroup G) :
    ClosedSubgroup ((groupBaseChange k (AlgebraicClosure k)).obj G) := by
  let K := AlgebraicClosure k
  let f := fieldSpecMap k K
  let i := H.inclusion.hom.hom
  let j := ((baseChange k K).map i).left
  have hH : IsPullback (pullback.fst H.group.X.hom f) (pullback.snd H.group.X.hom f)
      (i.left ≫ G.X.hom) f := by
    rw [Over.w i]
    exact IsPullback.of_hasPullback _ _
  have h₁ : j ≫ pullback.fst G.X.hom f = pullback.fst H.group.X.hom f ≫ i.left :=
    pullback.lift_fst _ _ _
  have h₂ : j ≫ pullback.snd G.X.hom f = pullback.snd H.group.X.hom f :=
    pullback.lift_snd _ _ _
  exact baseChangedSubgroup K H (MorphismProperty.of_isPullback
    (IsPullback.of_bot (h₂.symm ▸ hH) h₁.symm (IsPullback.of_hasPullback G.X.hom f))
      H.isClosedImmersion)

/-- The properties of the scalar extensions of the three marked subgroups. -/
structure GeometricBorelPair {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G) : Prop where
  reductive : IsReductive (GeometricGroup G)
  split : IsSplitTorus (geometricSubgroup P.torus).group
  maximal : IsGeometricallyMaximal (geometricSubgroup P.torus)
  positiveBorel : IsKBorel (geometricSubgroup P.positive)
  negativeBorel : IsKBorel (geometricSubgroup P.negative)
  inPositive : IsSubgroupOf (geometricSubgroup P.torus) (geometricSubgroup P.positive)
  inNegative : IsSubgroupOf (geometricSubgroup P.torus) (geometricSubgroup P.negative)
  opposite : OpenCell.AreOpposite (geometricSubgroup P.torus) (geometricSubgroup P.positive)
    (geometricSubgroup P.negative)

/-- The pair used to form the flag over the algebraic closure has the actual
scalar extensions as its marked subgroups. -/
abbrev GeometricBorelPair.pair {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (E : GeometricBorelPair P) : OppositeBorelPair (GeometricGroup G) where
  torus := geometricSubgroup P.torus
  positive := geometricSubgroup P.positive
  negative := geometricSubgroup P.negative
  reductive := E.reductive
  split := E.split
  maximal := E.maximal
  positiveBorel := E.positiveBorel
  negativeBorel := E.negativeBorel
  inPositive := E.inPositive
  inNegative := E.inNegative
  opposite := E.opposite

abbrev multiplicativeGroup (k : Type u) [Field k] : GroupScheme k :=
  specGroup (groupAlgebra k IntegerCharacters)

/-- The scalar-extension isomorphism of the multiplicative group preserves
the unit represented by each point on every algebra over the new field. -/
structure MultiplicativeComparison (k K : Type u) [Field k] [Field K] [Algebra k K] where
  iso : multiplicativeGroup K ≅ (groupBaseChange k K).obj (multiplicativeGroup k)
  units (R : TestAlgebra K) (s : Rˣ) :
    baseChangePoint k K (multiplicativeGroup k).X R (unitPoint R s ≫ iso.hom.hom.hom) =
      unitPoint ((restrictTestAlgebra k K).obj R) s

/-- Scalar extension of a character through the standard multiplicative group. -/
def MultiplicativeComparison.character {K : Type u} [Field K] [Algebra k K]
    (e : MultiplicativeComparison k K) {T : GroupScheme k} (χ : Character T) :
    Character ((groupBaseChange k K).obj T) :=
  (groupBaseChange k K).map χ ≫ e.iso.inv

abbrev closureAlgebra (k : Type u) [Field k] : TestAlgebra k :=
  CommAlgCat.of k (AlgebraicClosure k)

/-- A presentation of the extended quotient on the actual scalar extension
of the original flag scheme, with the actual scalar extension of its projection. -/
structure GeometricQuotient {G : AffineAlgebraicGroup k} {B : ClosedSubgroup G.val}
    (Q : Presentation B) where
  quasiProjective : IsQuasiProjective ((baseChange k (AlgebraicClosure k)).obj Q.scheme)
  flat : Flat ((baseChange k (AlgebraicClosure k)).map Q.projection).left
  surjective : Surjective ((baseChange k (AlgebraicClosure k)).map Q.projection).left
  finitePresentation :
    LocallyOfFinitePresentation ((baseChange k (AlgebraicClosure k)).map Q.projection).left
  quotientIso : rightQuotientSheaf (geometricSubgroup B) ≅
    schemeFppfSheaf ((baseChange k (AlgebraicClosure k)).obj Q.scheme)
  quotientProjection : rightQuotientProjection (geometricSubgroup B) ≫ quotientIso.hom =
    (fppfOver (AlgebraicClosure k)).uliftYoneda.map
      ((baseChange k (AlgebraicClosure k)).map Q.projection)

abbrev GeometricQuotient.presentation {G : AffineAlgebraicGroup k} {B : ClosedSubgroup G.val}
    {Q : Presentation B} (E : GeometricQuotient Q) : Presentation (geometricSubgroup B) where
  scheme := (baseChange k (AlgebraicClosure k)).obj Q.scheme
  projection := (baseChange k (AlgebraicClosure k)).map Q.projection
  quasiProjective := E.quasiProjective
  flat := E.flat
  surjective := E.surjective
  finitePresentation := E.finitePresentation
  quotientIso := E.quotientIso
  quotientProjection := E.quotientProjection

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}

abbrev overlapComparison (P : OppositeBorelPair G) :=
  (PreservesLimitPair.iso (baseChange k (AlgebraicClosure k))
    G.val.X P.negative.group.X).symm

/-- The cohomology comparison uses the extension of both maps of the
torsor kernel pair and of the inverse-character transition function.
The coefficient isomorphism preserves the inclusion into regular functions. -/
structure Comparison (Q : Presentation P.negative) (b : BorelProjection P)
    (χ : Character P.torus.group) (h : FlagKernelPair Q) where
  borels : GeometricBorelPair P
  multiplicative : MultiplicativeComparison k (AlgebraicClosure k)
  quotient : GeometricQuotient Q
  projection : BorelProjection borels.pair
  projection_eq : projection.projection = (groupBaseChange k (AlgebraicClosure k)).map b.projection
  kernelPair : FlagKernelPair (P := borels.pair) quotient.presentation
  first_eq : (overlapComparison P).hom ≫ ((flagLineData Q b χ h).extend (closureAlgebra k)).first =
    (flagLineData quotient.presentation projection (multiplicative.character χ) kernelPair).first
  second_eq : (overlapComparison P).hom ≫ ((flagLineData Q b χ h).extend (closureAlgebra k)).second =
    (flagLineData quotient.presentation projection (multiplicative.character χ) kernelPair).second
  multiplier_eq : (overlapComparison P).hom.left.appTop
      ((flagLineData Q b χ h).extend (closureAlgebra k)).multiplier =
    (flagLineData quotient.presentation projection (multiplicative.character χ) kernelPair).multiplier
  coefficients : ((flagLineData Q b χ h).extend (closureAlgebra k)).sheaf ≅
    flagLineSheaf quotient.presentation projection (multiplicative.character χ) kernelPair
  coefficients_inclusion : coefficients.hom ≫
    (flagLineData (P := borels.pair) quotient.presentation projection (multiplicative.character χ) kernelPair).inclusion =
    ((flagLineData Q b χ h).extend (closureAlgebra k)).inclusion
  scalarExtension : (flagLineData Q b χ h).ScalarExtension (closureAlgebra k)

def Comparison.cohomologyIso {Q : Presentation P.negative} {b : BorelProjection P}
    {χ : Character P.torus.group} {h : FlagKernelPair Q} (E : Comparison Q b χ h) (n : ℕ) :
    (extendToAlgebra (k := k) (K := AlgebraicClosure k)).obj (flagCohomology Q b χ h n) ≅
      flagCohomology E.quotient.presentation E.projection
        (E.multiplicative.character χ) E.kernelPair n :=
  E.scalarExtension.iso n ≪≫ (cohomology _ n).mapIso E.coefficients

def OppositeBorelBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G),
    GeometricBorelPair P

def Statement : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (b : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q), Nonempty (Comparison Q b χ h)

end

end LinearAlgebraicGroups.Specs.FlagCohomologyOverAlgClosure
