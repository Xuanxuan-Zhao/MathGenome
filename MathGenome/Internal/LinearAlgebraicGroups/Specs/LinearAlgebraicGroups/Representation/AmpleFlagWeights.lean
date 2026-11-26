import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagLineBundle
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.ParabolicLineWeights

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj TensorProduct BigOperators

universe u

namespace LinearAlgebraicGroups.Specs.AmpleFlagWeights

open AbstractPairing (Datum)
open CharacterDescent (Character)
open CharacterPairing (characterValue)
open FlagLineBundle (OppositeBorelPair BorelProjection)
open GeometricRadicals (IsSemisimple IsSplitTorus)
open ParabolicLineWeights (LineWeightData ParabolicLine)
open ProjectiveSpaces (LineRepresentation projectiveSpace)
open QuotientEmbedding (Presentation)
open RootWeightAction (SimpleRoot act extendVector)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- Strict dominance uses the simple roots of the fixed positive Borel. -/
def IsStrictlyDominant {T B : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) (χ : Character T.group) : Prop :=
  ∀ i : SimpleRoot T B, 0 < D.rootDatum.coroot' i.val (Additive.ofMul χ)

/-- Integral exponents giving a common power of the inverse character from the
opposite maximal-parabolic lines. Each simple root occurs with positive multiplicity. -/
def CharacterPowerDecomposition : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {T B Bneg : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (pos : LineWeightData T B) (neg : LineWeightData T Bneg)
    (e : pos.base.support ≃ neg.base.support),
    (∀ i, neg.fundamentalWeight (e i) = -pos.fundamentalWeight i) →
    ∀ (χ : Character T.group),
      (∀ i : pos.base.support, 0 < pos.datum.rootDatum.coroot' i.val (Additive.ofMul χ)) →
      ∃ (m : ℕ) (r : neg.base.support → ℕ),
        0 < m ∧ (∀ i, 0 < r i) ∧
          (∏ i, (neg.line i).weight ^ r i) = (χ ^ m)⁻¹

/-- Scalar extension of a vector in the given finite coordinate system. -/
def vectorCoordinates {I : Type u} [Fintype I] [DecidableEq I] (R : TestAlgebra k) :
    (R ⊗[k] (I → k)) ≃ₗ[R] (I → R) :=
  ((Pi.basisFun k I).baseChange R).equivFun

/-- The vector generating the line over a point of the group. -/
def orbitVector {T B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    {H : ClosedSubgroup G.val} (L : ParabolicLine (T := T) U H)
    (R : TestAlgebra k) (g : Points G.val.X R) : R ⊗[k] (L.index → k) :=
  letI := L.finite
  letI := L.decidable
  (vectorCoordinates R).symm (act L.representation R g (extendVector R L.vector))

/-- A projective orbit constructed from the specified nonzero vector, with its
pointwise orbit formula over every commutative test algebra. -/
def IsLineOrbit {T B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    {H : ClosedSubgroup G.val} (L : ParabolicLine (T := T) U H) (Q : Presentation H) :
    letI := L.finite
    (Q.scheme ⟶ projectiveSpace k (L.index → k)) → LineRepresentation k (L.index → k) → Prop := by
  letI := L.finite
  letI := L.decidable
  intro j ρ
  exact ∀ (R : TestAlgebra k) (g : Points G.val.X R),
    ((ρ.points _ j).line R (g ≫ Q.projection)).submodule =
      Submodule.span R {orbitVector L R g}

/-- A parabolic line with its full scheme stabilizer induces a closed immersion
of the represented parabolic quotient into the projective space of that line's
representation. -/
def ParabolicOrbitEmbeddings : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom →
    ∀ {T B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
      (H : ClosedSubgroup G.val), BorelProper.IsParabolic G H →
      ∀ (L : ParabolicLine (T := T) U H) (Q : Presentation H),
        letI := L.finite
        ∀ (ρ : LineRepresentation k (L.index → k)),
          ∃ (j : Q.scheme ⟶ projectiveSpace k (L.index → k)),
          IsClosedImmersion j.left ∧ IsLineOrbit L Q j ρ

/-- The joint stabilizer of the specified opposite maximal-parabolic lines
is the opposite Borel as a subgroup scheme. Membership is tested on all
schemes over the ground field. -/
def OppositeParabolicIntersection : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G)
    [IsCommMonObj P.torus.group.X] (neg : LineWeightData P.torus P.negative)
    (S : SchemeOver k) (g : S ⟶ G.val.X),
    (∀ i, g ∈ SubgroupSections (neg.parabolic i).limitGroups.parabolic S) ↔
      g ∈ SubgroupSections P.negative S

/-- Change of coefficients of a vector in the constant bundle on affine tests. -/
def changeVector {V : Type u} [AddCommGroup V] [Module k V] {R S : TestAlgebra k}
    (a : R ⟶ S) : R ⊗[k] V →ₗ[k] S ⊗[k] V :=
  TensorProduct.map a.hom.toLinearMap (LinearMap.id : V →ₗ[k] V)

/-- Descent description of the identification with the hyperplane pullback.
A basis of the tautological line over the quotient torsor transforms by the
inverse of the bundle character. Its dual thus descends by the same
transition as the associated bundle of the displayed character. -/
def IsHyperplanePullback {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (p : BorelProjection P) (χ : Character P.torus.group)
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (j : Q.scheme ⟶ projectiveSpace k V) (ρ : LineRepresentation k V) : Prop :=
  ∃ frame : ∀ (R : TestAlgebra k), Points G.val.X R → R ⊗[k] V,
    (∀ (R : TestAlgebra k) (g : Points G.val.X R),
      ((ρ.points _ j).line R (g ≫ Q.projection)).submodule =
        Submodule.span R {frame R g} ∧
      Function.Injective (fun r : R ↦ r • frame R g)) ∧
    (∀ {R S : TestAlgebra k} (a : R ⟶ S) (g : Points G.val.X R),
      frame S (mapPoints a g) = changeVector a (frame R g)) ∧
    ∀ (R : TestAlgebra k) (g : Points G.val.X R) (b : Points P.negative.group.X R),
      frame R (g * (b ≫ P.negative.inclusion.hom.hom)) =
        characterValue (p.projection ≫ χ) R (b⁻¹) • frame R g

/-- Ampleness on the proper flag scheme, expressed by a positive power
becoming a hyperplane pullback along a closed projective embedding.
The power uses the character power, which gives the tensor power by the
descent transition of the associated line bundle. -/
def IsAmple {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (p : BorelProjection P) (χ : Character P.torus.group) : Prop :=
  ∃ (m : ℕ), 0 < m ∧
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module.Finite k V)
      (ρ : LineRepresentation k V) (j : Q.scheme ⟶ projectiveSpace k V),
      IsClosedImmersion j.left ∧ IsHyperplanePullback Q p (χ ^ m) j ρ

/-- The ampleness claim holds for split semisimple groups, in particular the
simply connected groups used for vanishing. -/
def StrictDominanceImpliesAmple : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G),
    IsSemisimple G →
    ∀ [IsCommMonObj P.torus.group.X] (D : Datum P.torus) (χ : Character P.torus.group),
      IsStrictlyDominant (B := P.positive) D χ →
      ∀ (Q : Presentation P.negative) (p : BorelProjection P), IsAmple Q p χ

/-- A split torus has point flag scheme and every associated character bundle
on that scheme is ample. -/
def SplitTorusPointCase : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G),
    IsSplitTorus G.val →
    ∀ (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group),
      IsIso Q.scheme.hom ∧ IsAmple Q p χ

end

end LinearAlgebraicGroups.Specs.AmpleFlagWeights
