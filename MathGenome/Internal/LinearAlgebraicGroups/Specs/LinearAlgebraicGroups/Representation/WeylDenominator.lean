import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.DominantOrder
import Mathlib.Algebra.MonoidAlgebra.MapDomain

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.WeylDenominator

open AbstractPairing (Datum Root)
open BorelsAndChambers (IsPositiveSystem)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)

/-- A half-weight is stored by its double in the character lattice. In the rationalization
of the free lattice, the coordinate `x` denotes `x / 2`, so an integral weight `x`
has coordinate `2 • x`. Addition and the Weyl action commute with this identification. -/
abbrev HalfWeight (X : Type*) := X

abbrev GroupRing (X : Type*) [AddCommGroup X] := AddMonoidAlgebra ℤ (HalfWeight X)

noncomputable abbrev monomial {X : Type*} [AddCommGroup X] (x : HalfWeight X) : GroupRing X :=
  AddMonoidAlgebra.single x 1

noncomputable section

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : RootPairing I ℤ X Y)

/-- A word in the reflections in the given simple roots, multiplied in list order. -/
def wordProduct (b : P.Base) (word : List b.support) : P.weylGroup :=
  (word.map (fun i ↦ RootPairing.weylGroup.ofIdx P i.val)).prod

/-- Coxeter length for the chosen simple roots. -/
def weylLength (b : P.Base) (w : P.weylGroup) : ℕ :=
  sInf {n | ∃ word : List b.support, wordProduct P b word = w ∧ word.length = n}

def weylSign (b : P.Base) (w : P.weylGroup) : ℤ :=
  (-1) ^ weylLength P b w

/-- The action on the integral group ring of the half-character lattice. -/
def onGroupRing (w : P.weylGroup) : GroupRing X ≃+* GroupRing X :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ w.val.weightEquiv.toAddEquiv

variable [Finite I]

def positiveRoots (S : Set I) : Finset I := by
  classical
  let := Fintype.ofFinite I
  exact Finset.univ.filter (· ∈ S)

/-- The exponent `ρ` in doubled coordinates. -/
def rho (S : Set I) : HalfWeight X :=
  ∑ i ∈ positiveRoots S, P.root i

/-- The unshifted Weyl denominator. The integral root in its exponent is doubled. -/
def denominator (S : Set I) : GroupRing X :=
  ∏ i ∈ positiveRoots S, (1 - monomial (-(2 • P.root i)))

variable [Finite P.weylGroup]

/-- The alternant of the formal exponential of a half-weight. -/
def alternant (b : P.Base) (x : HalfWeight X) : GroupRing X := by
  classical
  let := Fintype.ofFinite P.weylGroup
  exact ∑ w : P.weylGroup, weylSign P b w • monomial (w.val.weightEquiv x)

/-- Denominator formula and the associated Weyl sign identities. -/
structure Laws (S : Set I) (b : P.Base) : Prop where
  sign_one : weylSign P b 1 = 1
  sign_mul : ∀ w v, weylSign P b (w * v) = weylSign P b w * weylSign P b v
  sign_simple : ∀ i ∈ b.support, weylSign P b (RootPairing.weylGroup.ofIdx P i) = -1
  denominatorAction : ∀ w, onGroupRing P w (denominator P S) =
    weylSign P b w •
      (monomial (rho P S - w.val.weightEquiv (rho P S)) * denominator P S)
  shiftedDenominatorAction : ∀ w,
    onGroupRing P w (monomial (rho P S) * denominator P S) =
      weylSign P b w • (monomial (rho P S) * denominator P S)
  alternantAction : ∀ w x, onGroupRing P w (alternant P b x) =
    weylSign P b w • alternant P b x
  identity : alternant P b (rho P S) = monomial (rho P S) * denominator P S
  leadingCoefficient : (alternant P b (rho P S)).coeff (rho P S) = 1
  rootless : IsEmpty I → alternant P b (rho P S) = 1 ∧ denominator P S = 1

/-- The Weyl denominator formula for a split maximal torus in a connected reductive
group, on its actual character lattice and with its scheme Weyl group. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ D : Datum T, Nonempty (DatumAndWeyl.Identification D) ∧
          letI := D.finiteRoots
          ∃ hW : Finite D.rootDatum.weylGroup, letI := hW
            ∀ S : Set (Root T), IsPositiveSystem T S →
              (∃ b : D.rootDatum.Base, DominantOrder.IsBaseFor D.rootDatum S b) ∧
              ∀ b : D.rootDatum.Base, DominantOrder.IsBaseFor D.rootDatum S b →
                Laws D.rootDatum S b

end

end LinearAlgebraicGroups.Specs.WeylDenominator
