import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolics
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.PrimitiveLine

open CategoryTheory
open scoped CategoryTheory.MonoidalCategory TensorProduct
open TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.ParabolicLineWeights

open AbstractPairing (Datum Root)
open BorelProper (IsParabolic)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open CharacterDescent (Character Cocharacter)
open CyclicHighestWeight (orbitSpan)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSemisimple IsSplitTorus IsUnipotentRadical)
open OpenCell (AreOpposite)
open OrderedRootProducts (RootSubgroupFamily)
open RankOneFlag (IsGeometricallyMaximal)
open RootWeightAction (Representation IsPrimitive IsDominant act extendVector weightSpace)
open SchemeDerivedGroup (IsSubgroupOf)
open SimpleRoots (IsBaseFor evaluate)
open StandardParabolicLevi (StandardParabolic parabolicWeylGroup)
open StandardParabolics (HasWeylIndices)
open Unipotent (closedSubgroupAlgebraicGroup)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
variable {T B : ClosedSubgroup G.val}

abbrev RationalCharacters (T : ClosedSubgroup G.val) :=
  ℚ ⊗[ℤ] Additive (Character T.group)

def rationalCharacter (χ : Character T.group) : RationalCharacters T :=
  (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul χ

variable [IsCommMonObj T.group.X] {D : Datum T}

/-- Evaluation on a coroot, extended from the character lattice to its rationalization. -/
def rationalCorootPairing (D : Datum T) (α : Root T) : RationalCharacters T →ₗ[ℚ] ℚ :=
  (AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.comp
    ((D.rootDatum.toLinearMap.flip (D.rootDatum.coroot α)).baseChange ℚ)

/-- The scheme stabilizer of a nonzero vector's line, tested over every test algebra. -/
def HasLineStabilizer {I : Type u} [Fintype I] [DecidableEq I]
    (ρ : Representation G.val I) (v : I → k) (P : ClosedSubgroup G.val) : Prop :=
  ∀ (R : TestAlgebra k) (g : Points G.val.X R),
    (∃ a : Rˣ, act ρ R g (extendVector R v) = (a : R) • extendVector R v) ↔
      ∃ p : Points P.group.X R, p ≫ P.inclusion.hom.hom = g

/-- The maximal standard parabolic obtained by omitting a single simple root. -/
def omittedSimpleRoot (b : D.rootDatum.Base) (i : b.support) : Set (Root T) :=
  (b.support : Set (Root T)) \ {i.val}

/-- A proper parabolic maximal among proper parabolic subgroup schemes. -/
def IsMaximalProperParabolic (P : ClosedSubgroup G.val) : Prop :=
  IsParabolic G P ∧ ¬ IsIso P.inclusion ∧
    ∀ H : ClosedSubgroup G.val, IsParabolic G H → IsSubgroupOf P H →
      IsIso H.inclusion ∨ IsSubgroupOf H P

/-- A cyclic representation with the required primitive line and its scheme stabilizer. -/
structure ParabolicLine (U : ClosedSubgroup B.group) (P : ClosedSubgroup G.val) where
  index : Type u
  finite : Fintype index
  decidable : DecidableEq index
  representation : @Representation _ _ G.val index finite decidable
  vector : index → k
  weight : Character T.group
  primitive : IsPrimitive representation T B U weight vector
  cyclic : orbitSpan representation (𝟙 G.val.X) vector = ⊤
  highestLine : weightSpace representation T weight = Submodule.span k {vector}
  stabilizer : HasLineStabilizer representation vector P

open scoped Classical in
/-- The maximal parabolic lines and primitive weights for one Borel through the split torus. -/
structure LineWeightData (T B : ClosedSubgroup G.val) [IsCommMonObj T.group.X] where
  datum : Datum T
  weyl : Identification datum
  rootGroups : RootSubgroupFamily T
  cocharacter : Cocharacter T.group
  base : datum.rootDatum.Base
  radical : ClosedSubgroup B.group
  regular : IsRegular T cocharacter
  positive : positiveRoots T cocharacter = subgroupRoots T B
  isBase : IsBaseFor datum.rootDatum (evaluate datum cocharacter) base
  isRadical : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) radical
  parabolic : (i : base.support) → StandardParabolic B datum base rootGroups (omittedSimpleRoot base i)
  line : (i : base.support) → ParabolicLine (T := T) radical (parabolic i).limitGroups.parabolic
  degree : base.support → ℕ
  fundamentalWeight : base.support → RationalCharacters T
  maximal : ∀ i, IsMaximalProperParabolic (parabolic i).limitGroups.parabolic
  weylIndices : ∀ i, HasWeylIndices weyl (parabolic i).limitGroups.parabolic
    (parabolicWeylGroup datum (omittedSimpleRoot base i))
  separates : ∀ x, (∀ j : base.support, rationalCorootPairing datum j.val x = 0) → x = 0
  fundamentalPairing : ∀ i j, rationalCorootPairing datum j.val (fundamentalWeight i) =
    if i = j then 1 else 0
  lineWeight : ∀ i, 0 < degree i ∧ rationalCharacter (line i).weight =
    (degree i : ℚ) • fundamentalWeight i
  dominantMultiple : ∀ (η : Character T.group), IsDominant datum B η →
    ∀ m : ℕ, (∀ i, degree i ∣ m) →
      ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
        (ρ : Representation G.val I) (v : I → k), IsPrimitive ρ T B radical (η ^ m) v

/-- The omitted-root lines have weights that are positive integral multiples
of the fundamental weights, with opposite signs in the fixed character space
for the lines attached to the opposite Borel. -/
def LineWeights : Prop := by
  exact ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G → IsSemisimple G →
  ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    IsKBorel B → IsSubgroupOf T B →
    ∃ comm : IsCommMonObj T.group.X, letI := comm
      ∃ positive : LineWeightData T B,
        ∀ Bneg : ClosedSubgroup G.val, IsKBorel Bneg → IsSubgroupOf T Bneg →
          AreOpposite T B Bneg → ∃ negative : LineWeightData T Bneg,
            ∃ e : positive.base.support ≃ negative.base.support,
              ∀ i, (e i).val.val = i.val.val⁻¹ ∧
                negative.fundamentalWeight (e i) = -positive.fundamentalWeight i ∧
                rationalCharacter (negative.line (e i)).weight =
                  -((negative.degree (e i) : ℚ) • positive.fundamentalWeight i)

end

end LinearAlgebraicGroups.Specs.ParabolicLineWeights
