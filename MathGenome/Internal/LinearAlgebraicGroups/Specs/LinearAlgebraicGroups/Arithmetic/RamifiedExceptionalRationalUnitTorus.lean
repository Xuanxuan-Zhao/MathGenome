import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

/-! Rationality and residue coordinates of the marked unit torus at one ramified level. -/

namespace LinearAlgebraicGroups.Specs.RamifiedExceptionalRationalUnitTorus

open CategoryTheory ValuativeRel
open scoped CategoryTheory.MonObj
open AdjointRepresentation (GroupPoints)
open ExceptionalAffineBruhat (DiagramCompositum FieldPoints FoldedApartment FoldedLevel
  RamifiedReference residue)
open ExceptionalIwahoriCongruence (changeRingHom integralRing)
open ExceptionalIwahoriImageComparison (integralUnitTorus)
open ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open IntegralSemisimpleModel (IntegralAlgebra IntegralPoints Model TorusValues integerAlgebra torusPoint)
open Pinning (BasedIso BasedRootDatum)

universe u

attribute [local instance] integerAlgebra

noncomputable section

local notation "Oᵥ[" K "]" => Valuation.valuationSubring (valuation K)

/-- The point of the marked group obtained by evaluating its split torus. -/
abbrev markedTorusPoint {D : BasedRootDatum.{u}} (M : Model D)
    {S : IntegralAlgebra.{u}} (q : TorusValues D S) : IntegralPoints M.group S :=
  torusPoint D S q ≫ M.torus.hom.hom

/-- Character values of an integral tuple in the splitting field. -/
abbrev genericTorusValues {D : BasedRootDatum.{u}} {K : Type u} [Field K] [ValuativeRel K]
    (q : TorusValues D (integralRing Oᵥ[K])) : TorusValues D (integralRing K) :=
  (Units.map (valuationRingInclusion K).hom.toRingHom).comp q

/-- Reduce the unit value of every character in the actual valuation ring. -/
abbrev reduceTorusValues {D : BasedRootDatum.{u}} {K : Type u} [Field K] [ValuativeRel K]
    (q : TorusValues D (integralRing Oᵥ[K])) : TorusValues D (integralRing (residue K)) :=
  (Units.map (IsLocalRing.residue Oᵥ[K])).comp q

/-- Invariance under the permutation of characters, expressed on the full lattice. -/
def IsInvariant {D : BasedRootDatum.{u}} (τ : BasedIso D D) {S : IntegralAlgebra.{u}}
    (t : TorusValues D S) : Prop :=
  ∀ χ : D.X, t (Multiplicative.ofAdd (τ.val.weightEquiv χ)) = t (Multiplicative.ofAdd χ)

/-- The generic points of integral torus tuples give exactly the actual unit torus. -/
def IntegralUnitTorusCoordinates : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] {D : BasedRootDatum.{u}} (M : Model D),
    (∀ q : TorusValues D (integralRing Oᵥ[K]),
      changeRingHom M.group (valuationRingInclusion K) (markedTorusPoint M q) =
        markedTorusPoint M (genericTorusValues q)) ∧
    (∀ p : FieldPoints M K, p ∈ integralUnitTorus M ↔
      ∃ q : TorusValues D (integralRing Oᵥ[K]),
        p = markedTorusPoint M (genericTorusValues q))

/-- Torus rationality, chart membership, and integral reduction for the given comparison. -/
structure UnitTorusAtLevel
    {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
    {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
    (T : DiagramCompositum F L k σ)
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A) : Prop where
  rational (q : TorusValues D (integralRing T.field)) :
    markedTorusPoint M q ∈ X.points.range ↔
      ∀ χ : D.X, q (Multiplicative.ofAdd ((R.diagram σ).val.weightEquiv χ)) =
        Units.map T.diagram.toRingHom (q (Multiplicative.ofAdd χ))
  chart (q : TorusValues D (integralRing T.field)) :
    q ∈ X.comparison.chart.chart.torus ↔ markedTorusPoint M q ∈ X.points.range
  integral (g : GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    g ∈ X.comparison.T₀ ↔
      ∃ q : TorusValues D (integralRing Oᵥ[T.field]),
        X.points g = markedTorusPoint M (genericTorusValues q)
  reduction (q : TorusValues D (integralRing Oᵥ[T.field])) :
    markedTorusPoint M (genericTorusValues q) ∈ X.points.range →
      IsInvariant (R.diagram σ) (reduceTorusValues q)
  lift :
    D.datum.rootSpan ℤ = ⊤ →
    ∀ t : TorusValues D (integralRing (residue T.field)), IsInvariant (R.diagram σ) t →
      ∃ q : TorusValues D (integralRing Oᵥ[T.field]),
        reduceTorusValues q = t ∧
          markedTorusPoint M (genericTorusValues q) ∈ X.points.range

/-- The marked unit torus comparison applies over every given finite coefficient level. -/
def RationalUnitTorusComparison : Prop :=
  ∀ {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
    {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
    (T : DiagramCompositum F L k σ)
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A),
    UnitTorusAtLevel T X

end
end LinearAlgebraicGroups.Specs.RamifiedExceptionalRationalUnitTorus
