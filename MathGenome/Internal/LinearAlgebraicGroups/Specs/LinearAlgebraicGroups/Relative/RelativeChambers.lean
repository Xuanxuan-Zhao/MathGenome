import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori
import Mathlib.Topology.Connected.Basic

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Relative.RelativeChambers

open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots pairing)
open GeometricRadicals (IsReductive IsTorus IsSplitTorus baseChangedSubgroup)
open RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open BorelProper (IsParabolic)
open MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition unitPoint)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)

noncomputable section

variable {k : Type u} [Field k] {G : GroupScheme k}

/-- Nontrivial actual characters of the split torus occurring on the adjoint Lie algebra. -/
def relativeRoots (S : ClosedSubgroup G) : Set (Character S.group) :=
  absoluteRoots S

abbrev RelativeRootsType :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (S : ClosedSubgroup G), Set (Character S.group)

/-- Integral cocharacters off all relative root hyperplanes. -/
def IsRegular (S : ClosedSubgroup G) (c : Cocharacter S.group) : Prop :=
  ∀ a : relativeRoots S, pairing S.group a.val c ≠ 0

def nonnegativeRoots (S : ClosedSubgroup G) (c : Cocharacter S.group) : Set (relativeRoots S) :=
  {a | 0 ≤ pairing S.group a.val c}

/-- The real cocharacter space in its realization as the real-valued dual
of the character lattice. -/
abbrev RealCocharacterSpace (S : ClosedSubgroup G) :=
  Additive (Character S.group) →ₗ[ℤ] ℝ

/-- Evaluation on the character lattice gives the usual topology on the
real cocharacter space. -/
abbrev realCocharacterTopology (S : ClosedSubgroup G) :
    TopologicalSpace (RealCocharacterSpace S) :=
  TopologicalSpace.induced (fun f : RealCocharacterSpace S ↦
    (f : Additive (Character S.group) → ℝ)) inferInstance

/-- The complement of all relative root hyperplanes. -/
def regularRealCocharacters (S : ClosedSubgroup G) : Set (RealCocharacterSpace S) :=
  {f | ∀ a : relativeRoots S, f (Additive.ofMul a.val) ≠ 0}

/-- The region where precisely the roots in `A` are positive and all
remaining roots are negative. -/
def chamberRegion (S : ClosedSubgroup G) (A : Set (relativeRoots S)) :
    Set (RealCocharacterSpace S) :=
  {f | (∀ a ∈ A, 0 < f (Additive.ofMul a.val)) ∧ ∀ a ∉ A, f (Additive.ofMul a.val) < 0}

/-- A chamber is encoded by its realized set of positive roots. -/
def IsChamber (S : ClosedSubgroup G) (A : Set (relativeRoots S)) : Prop :=
  ∃ f ∈ regularRealCocharacters S, A = {a | 0 < f (Additive.ofMul a.val)}

/-- The sign pattern of a regular real cocharacter determines its whole
connected component in the root hyperplane complement. -/
def ChamberComponents : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (S : ClosedSubgroup G),
    letI := realCocharacterTopology S
    ∀ f ∈ regularRealCocharacters S, ∀ A : Set (relativeRoots S),
      A = {a | 0 < f (Additive.ofMul a.val)} ↔
        chamberRegion S A = connectedComponentIn (regularRealCocharacters S) f

def RelativeRootsFinite : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (S : ClosedSubgroup G.val),
    IsSplitTorus S.group → (relativeRoots S).Finite

def MaximalTorusOverSplitTorus : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      ∃ T : ClosedSubgroup G.val, IsTorus T.group ∧ IsGeometricallyMaximal T ∧ IsSubgroupOf S T

private abbrev multiplicativeGroup (F : Type u) [Field F] := specGroup (groupAlgebra F IntegerCharacters)

/-- Restricting the absolute roots over any splitting field gives exactly the
nontrivial split-torus weights, with repetitions removed by the set image. -/
def RelativeRootsByRestriction : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (S T : ClosedSubgroup G.val)
    (i : S.group ⟶ T.group), i ≫ T.inclusion = S.inclusion →
    IsSplitTorus S.group →
    ∀ (hT : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left),
      IsSplitTorus ((groupBaseChange k K).obj T.group) →
      ∃ e : (multiplicativeGroup K) ≅ (groupBaseChange k K).obj (multiplicativeGroup k),
        (∀ (R : TestAlgebra K) (t : Rˣ),
          baseChangePoint k K (multiplicativeGroup k).X R (unitPoint R t ≫ e.hom.hom.hom) =
            unitPoint ((restrictTestAlgebra k K).obj R) t) ∧
        Function.Injective (fun a : Character S.group ↦ (groupBaseChange k K).map a ≫ e.inv) ∧
        (fun a : Character S.group ↦ (groupBaseChange k K).map a ≫ e.inv) '' relativeRoots S =
          ((fun a : Character ((groupBaseChange k K).obj T.group) ↦
            (groupBaseChange k K).map i ≫ a) '' absoluteRoots (baseChangedSubgroup K T hT)) \ {1}

def ParabolicThroughSplitTorus : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (S : ClosedSubgroup G.val),
    IsMaximalSplitTorus S →
    ∀ P : ClosedSubgroup G.val, IsParabolic G P → IsSubgroupOf S P →
      ∃ (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion)),
        SameSubgroup P D.parabolic

def LimitParabolicThroughSplitTorus : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (S : ClosedSubgroup G.val), IsSplitTorus S.group →
      ∀ (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion)),
        IsParabolic G D.parabolic ∧ IsSubgroupOf S D.parabolic

/-- The comparison is of closed subgroups in G, hence scheme-theoretic. -/
def LimitParabolicsEqual : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S : ClosedSubgroup G.val, IsSplitTorus S.group →
      ∀ (c d : Cocharacter S.group)
        (C : LimitDecomposition (c ≫ S.inclusion)) (D : LimitDecomposition (d ≫ S.inclusion)),
        SameSubgroup C.parabolic D.parabolic ↔ nonnegativeRoots S c = nonnegativeRoots S d

def ChamberCocharacters : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (S : ClosedSubgroup G.val),
    IsSplitTorus S.group →
      ∀ A : Set (relativeRoots S), IsChamber S A ↔
        ∃ c : Cocharacter S.group, IsRegular S c ∧ nonnegativeRoots S c = A

def RegularLevi : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S : ClosedSubgroup G.val, IsSplitTorus S.group →
      ∀ (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion)), IsRegular S c →
        RepresentsSubgroup D.centralizer (fun _ x ↦ Centralizes S.inclusion x)

def MinimalLimitParabolic : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      ∀ (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion)),
        IsMinimalParabolic G D.parabolic ↔ IsRegular S c

/-- The chamber determines a unique minimal parabolic through S up to
equality as a closed subgroup. Each minimal parabolic comes from a
unique chamber. -/
def ChamberCorrespondence : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
    let Associated := fun (A : Set (relativeRoots S)) (P : ClosedSubgroup G.val) ↦
      ∃ (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion)),
        IsRegular S c ∧ nonnegativeRoots S c = A ∧ SameSubgroup P D.parabolic
    (∀ A, IsChamber S A →
      ∃ P, IsMinimalParabolic G P ∧ IsSubgroupOf S P ∧ Associated A P ∧
        ∀ Q, Associated A Q → SameSubgroup P Q) ∧
    (∀ P, IsMinimalParabolic G P → IsSubgroupOf S P →
      ∃! A, IsChamber S A ∧ Associated A P)

/-- For an empty relative root set the chamber is unique, the only parabolic
through S is the full group, and S is central in it. -/
def EmptyRelativeRoots : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S → relativeRoots S = ∅ →
      (∃! A : Set (relativeRoots S), IsChamber S A) ∧
      (∀ P : ClosedSubgroup G.val, IsParabolic G P → IsSubgroupOf S P → IsIso P.inclusion) ∧
      ∀ (X : SchemeOver k) (x : X ⟶ G.val.X), Centralizes S.inclusion x

end

end LinearAlgebraicGroups.Specs.Relative.RelativeChambers
