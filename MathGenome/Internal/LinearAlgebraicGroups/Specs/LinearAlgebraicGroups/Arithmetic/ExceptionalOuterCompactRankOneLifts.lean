import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedWeyl
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterTorus
import Mathlib.LinearAlgebra.UnitaryGroup

noncomputable section

set_option autoImplicit false

namespace LinearAlgebraicGroups.Specs.ExceptionalOuterCompactRankOneLifts

open AlgebraicGeometry CategoryTheory Topology
open Arithmetic.AdelicGroups (PointsIn)
open IntegralModels (MatrixRealization)
open ExceptionalCompactInner (HasExceptionalType fixedSubgroup)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open AbsoluteDynkinTypes (E6Reflection IsAbsolutelyAlmostSimple PreservesCartan)
open Pinning (PinnedIso)
open RootGroups (AdditiveLine)
open ExceptionalOuterTorus (MarkedPair OuterInvolutions IsMaximalCompactTorus
  fixedCompact identityComponent)
open ExceptionalFoldedWeyl (E6Space e6Diagram e6Inner e6Roots foldedSpace foldedRoots
  e6Lattice foldedCoroot reflection OnWall diagramCentralizingWeyl)

variable {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}

/-- Data and properties of a single witness of `OuterTorusComparison`.
All point actions use the same marked pair and matrix realization. -/
structure MarkedTorus (ω θ : MulAut (PointsIn i ℂ)) (S : Subgroup (PointsIn i ℂ)) where
  T : Subgroup (PointsIn i ℂ)
  A : AdditiveLine ℂ
  M : MarkedPair G A
  d : PinnedIso M.P M.P
  δ : MulAut (PointsIn i ℂ)
  centralizer : T = fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _)
  centralizerComponent : (T : Set (PointsIn i ℂ)) =
    identityComponent (fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _))
  maximal : IsMaximalCompactTorus (fixedSubgroup ω : Set _) T
  stablePair : M.IsStable (i := i) θ
  compactPinning : M.IsCompactCompatible (i := i) ω
  tori : (T : Set (PointsIn i ℂ)) = (fixedSubgroup ω : Set _) ∩
    Set.range (M.onPoints (i := i) M.P.pair.T.inclusion)
  cartan :
    letI := M.datum.comm
    PreservesCartan (RootData.integralCartan M.datum.datum.rootDatum M.datum.base)
      (CartanMatrix.E 6) M.numbering
  corootBasis :
    letI := M.datum.comm
    ∃ b : Module.Basis (Fin 6) ℤ
      (Additive (CharacterDescent.Cocharacter M.P.pair.T.group)),
      ∀ j, b j = Additive.ofMul (M.coroot j)
  rootCoordinates :
    Set.range M.rootValues = (fun α j => e6Inner (Pi.single j 1) α) '' e6Roots
  rootEvaluation : ∀ (α : AbstractPairing.Root M.P.pair.T) x,
    CharacterPairing.characterValue α.val ExceptionalOuterTorus.complexTest (M.torusPoint x) =
      (Circle.exp (2 * Real.pi * ∑ j, M.rootValues α j * x j) : ℂ)
  regularChamber : ∃ z ∈ foldedSpace, M.IsRegularChamber z
  continuousExp : Continuous (M.exp (i := i))
  expAdd : ∀ y z, M.exp (i := i) (y + z) = M.exp y * M.exp z
  expRange : (T : Set (PointsIn i ℂ)) = Set.range (M.exp (i := i))
  expKernel : ∀ y, M.exp (i := i) y = 1 ↔ y ∈ e6Lattice
  diagramPin : ∀ j, M.simpleCoordinate j ≫ d.group.hom = M.simpleCoordinate (E6Reflection j)
  diagramCoroot : ∀ j, M.coroot j ≫ d.torus.hom = M.coroot (E6Reflection j)
  diagramAction : ExceptionalCompactInner.ActsOnComplexPoints (i := i)
    (Aut.of (M.comparison.symm ≪≫ d.group ≪≫ M.comparison)) δ
  diagramInvolutive : Function.Involutive δ
  continuousDiagram : Continuous δ
  diagramCommutes : Function.Commute δ ω
  diagramExp : ∀ y, δ (M.exp (i := i) y) = M.exp (e6Diagram y)
  twist : ∃ t₀ : T, θ = MulAut.conj t₀.val * δ
  fixedTorus : S = T ⊓ fixedSubgroup δ
  fixedExp : (S : Set (PointsIn i ℂ)) = M.exp (i := i) '' foldedSpace

variable {ω θ : MulAut (PointsIn i ℂ)} {S : Subgroup (PointsIn i ℂ)}

abbrev MarkedTorus.exp (D : MarkedTorus ω θ S) :=
  D.M.exp (i := i)

def MarkedTorus.twisted (D : MarkedTorus ω θ S) (x : E6Space) :
    MulAut (PointsIn i ℂ) := MulAut.conj (D.exp x) * D.δ

def MarkedTorus.fixedAt (D : MarkedTorus ω θ S) (x : E6Space) :
    Subgroup (PointsIn i ℂ) := fixedCompact ω (D.twisted x)

/-- Conjugation on the entire compact torus, in the marked real coordinates. -/
def MarkedTorus.RepresentsWeyl (D : MarkedTorus ω θ S) (n : PointsIn i ℂ)
    (w : Function.End E6Space) : Prop :=
  ∀ y, n * D.exp y * n⁻¹ = D.exp (w y)

/-- A compact root SU(2) with the folded coroot circle and the prescribed Weyl action. -/
def MarkedTorus.RealizesFoldedRoot (D : MarkedTorus ω θ S) (x β : E6Space) : Prop :=
  let SU := Matrix.specialUnitaryGroup (Fin 2) ℂ
  ∃ f : SU →* PointsIn i ℂ, Continuous f ∧
    Set.range f ⊆ identityComponent (D.fixedAt x) ∧
    (∀ s : ℝ, ∃ a : SU, a.val = Matrix.diagonal
        (![↑(Circle.exp (2 * Real.pi * s)), ↑((Circle.exp (2 * Real.pi * s))⁻¹)] :
          Fin 2 → ℂ) ∧ f a = D.exp (s • foldedCoroot β)) ∧
    ∃ a : SU, a.val = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∧
      f a ∈ Subgroup.normalizer (S : Set _) ∧
      ∀ y ∈ foldedSpace, f a * D.exp y * (f a)⁻¹ = D.exp (reflection β y)

/-- Every absolute Weyl label centralizing the diagram is represented by a
compact, diagram-fixed normalizer of the given torus. -/
def DiagramFixedNormalizerLifts : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)), OuterInvolutions (i := i) ω θ →
      ∀ S : Subgroup (PointsIn i ℂ),
        IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) S →
        ∀ D : MarkedTorus ω θ S, ∀ w ∈ diagramCentralizingWeyl,
          ∃ n ∈ fixedCompact ω D.δ, n ∈ Subgroup.normalizer (S : Set _) ∧ D.RepresentsWeyl n w

/-- Each folded wall through an involutive twist in the marked fixed space
has a compact rank-one map in the connected fixed group of that twist. -/
def CompactRankOneWallLifts : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)), OuterInvolutions (i := i) ω θ →
      ∀ S : Subgroup (PointsIn i ℂ),
        IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) S →
        ∀ (D : MarkedTorus ω θ S) (x : E6Space), x ∈ foldedSpace →
          Function.Involutive (D.twisted x) →
          ∀ β ∈ foldedRoots, OnWall β x → D.RealizesFoldedRoot x β

end LinearAlgebraicGroups.Specs.ExceptionalOuterCompactRankOneLifts
