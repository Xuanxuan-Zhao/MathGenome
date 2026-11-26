import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.NormalizerComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleClassification
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.DominantOrder
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Trace

open CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

universe u

namespace LinearAlgebraicGroups.Specs.SteinbergFundamentalTraces

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open GeometricRadicals (IsSemisimple IsUnipotentRadical)
open NormalizerComparison (SimpleRepresentative)
open Pinning (AttachedDatum PinnedGroup SimpleRoot)
open RootGroups (AdditiveLine rootPoint)
open RootWeightAction (Representation IsPrimitive)
open PrimitiveLine (IsSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup)
open BorelsAndChambers (subgroupRoots)

noncomputable section

variable {k : Type u} [Field k] {A : AdditiveLine k}
variable {P : PinnedGroup A} {r : ℕ}

/-- The dual coordinates to the simple coroots in the actual character lattice. -/
def IsFundamental (D : AttachedDatum P.pair) (e : Fin r ≃ SimpleRoot P.pair)
    (ω : Fin r → Character P.pair.T.group) : Prop :=
  letI := D.comm
  ∀ i j, D.datum.rootDatum.toLinearMap (Additive.ofMul (ω j))
    (D.datum.rootDatum.coroot (e i).val) = if i = j then 1 else 0

/-- Integral height given by the positive coroots of the pinned Borel. -/
def height (D : AttachedDatum P.pair) (χ : Character P.pair.T.group) : ℤ :=
  letI := D.comm
  letI := D.datum.finiteRoots
  D.datum.rootDatum.toLinearMap (Additive.ofMul χ)
    (DominantOrder.twoRhoCoroot D.datum.rootDatum (subgroupRoots P.pair.T P.pair.B))

/-- The ordered pinned section, evaluated with the chosen linked representatives. -/
def sectionWord (D : AttachedDatum P.pair) (e : Fin r ≃ SimpleRoot P.pair)
    (n : ∀ i, SimpleRepresentative P D i) (R : TestAlgebra k) (t : Fin r → R) :
    GroupPoints P.pair.G.val R :=
  let factor (i : Fin r) : GroupPoints P.pair.G.val R :=
    let representative : GroupPoints P.pair.G.val R := toUnit _ ≫ (n (e i)).reflection.representative
    rootPoint ((P.pin (e i)).val.hom ≫ (P.roots (e i).val).val.inclusion) R (t i) * representative
  ((List.finRange r).map factor).prod

/-- A basis presentation of a rational simple module of the indicated highest weight. -/
structure HighestWeightModule (U : ClosedSubgroup P.pair.B.group)
    (χ : Character P.pair.T.group) where
  I : Type u
  [finiteI : Fintype I]
  [decI : DecidableEq I]
  action : Representation P.pair.G.val I
  simple : IsSimple action
  primitive : ∃ v, IsPrimitive action P.pair.T P.pair.B U χ v

attribute [instance] HighestWeightModule.finiteI HighestWeightModule.decI

/-- The fundamental trace of each simple highest-weight module, on every
test algebra. This applies to every split semisimple simply connected root
datum and hence to the three split exceptional types. -/
def TracePolynomial : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ∀ (D : AttachedDatum P.pair) {r : ℕ} (e : Fin r ≃ SimpleRoot P.pair)
      (n : ∀ i, SimpleRepresentative P D i)
      (ω : Fin r → Character P.pair.T.group), IsFundamental D e ω →
    ∀ (U : ClosedSubgroup P.pair.B.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U →
    ∀ (j : Fin r) (V : HighestWeightModule U (ω j)),
    ∃ (d : k) (p : MvPolynomial (Fin r) k), d ≠ 0 ∧
      (∀ m ∈ p.support, ∀ i ∈ m.support, height D (ω i) < height D (ω j)) ∧
      ∀ (R : TestAlgebra k) (t : Fin r → R),
        Matrix.trace (V.action.app R (sectionWord D e n R t)).val =
          MvPolynomial.aeval t (MvPolynomial.C d * MvPolynomial.X j + p)

/-- Every fundamental weight and its simple module are available on the
actual split torus, for any chosen unipotent radical of the pinned Borel. -/
def FundamentalModulesExist : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ∀ (D : AttachedDatum P.pair) {r : ℕ} (e : Fin r ≃ SimpleRoot P.pair)
      (U : ClosedSubgroup P.pair.B.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U →
    ∃ ω : Fin r → Character P.pair.T.group, IsFundamental D e ω ∧
      ∀ (ω' : Fin r → Character P.pair.T.group), IsFundamental D e ω' →
        ∀ j, Nonempty (HighestWeightModule U (ω' j))

end

end LinearAlgebraicGroups.Specs.SteinbergFundamentalTraces
