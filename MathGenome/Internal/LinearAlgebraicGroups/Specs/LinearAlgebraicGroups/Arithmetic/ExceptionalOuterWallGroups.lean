import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactRankOneLifts

noncomputable section

set_option autoImplicit false

namespace LinearAlgebraicGroups.Specs.ExceptionalOuterWallGroups

open Arithmetic.AdelicGroups (PointsIn)
open AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open ExceptionalCompactInner (HasExceptionalType)
open ExceptionalFoldedWeyl (E6Space e6Lattice foldedSpace foldedRoots projectedLattice
  OnWall diagramCentralizingWeyl wallReflections)
open ExceptionalOuterCompactRankOneLifts (MarkedTorus)
open ExceptionalOuterTorus (OuterInvolutions IsMaximalCompactTorus fixedCompact identityComponent)
open IntegralModels (MatrixRealization)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- The outer compact calculation with one marked torus and exponential for the
quotient, normalizer, and rank-one maps. The element `a` conjugates the original
involution to the toral twist at the fixed logarithm `x`. -/
def OuterWallCalculation : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)), OuterInvolutions (i := i) ω θ →
      ∀ S : Subgroup (PointsIn i ℂ),
        IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) S →
        ConnectedSpace (fixedCompact ω θ) ∧
        ∃ (D : MarkedTorus ω θ S) (t₀ a : D.T) (x : E6Space),
          x ∈ foldedSpace ∧ (2 : ℝ) • x ∈ e6Lattice ∧
          θ = MulAut.conj t₀.val * D.δ ∧
          D.exp x = a.val * t₀.val * (D.δ a.val)⁻¹ ∧
          D.twisted x * MulAut.conj a.val = MulAut.conj a.val * θ ∧
          (∀ t : D.T, ∃ y ∈ foldedSpace, ∃ b : D.T,
            D.exp y = t.val * (b.val * (D.δ b.val)⁻¹)) ∧
          (∀ y ∈ foldedSpace, ∀ z ∈ foldedSpace,
            (∃ b : D.T, D.exp y = D.exp z * (b.val * (D.δ b.val)⁻¹)) ↔
              y - z ∈ projectedLattice) ∧
          D.T ⊓ D.fixedAt x = S ∧
          (∀ n ∈ D.fixedAt x, D.RepresentsWeyl n 1 ↔ n ∈ S) ∧
          (∀ g ∈ D.fixedAt x, ∃ n ∈ D.fixedAt x,
            n ∈ Subgroup.normalizer (S : Set _) ∧
              g * n⁻¹ ∈ identityComponent (D.fixedAt x)) ∧
          (∀ n ∈ D.fixedAt x, n ∈ Subgroup.normalizer (S : Set _) →
            ∃! w, w ∈ diagramCentralizingWeyl ∧ D.RepresentsWeyl n w) ∧
          (∀ w ∈ diagramCentralizingWeyl,
            (∃ n ∈ D.fixedAt x, n ∈ Subgroup.normalizer (S : Set _) ∧ D.RepresentsWeyl n w) ↔
              w x - x ∈ projectedLattice) ∧
          (∀ w ∈ diagramCentralizingWeyl,
            (w x - x ∈ projectedLattice) ↔
              ∃ r ∈ wallReflections x, Set.EqOn w r foldedSpace) ∧
          (∀ β ∈ foldedRoots, OnWall β x ↔ D.RealizesFoldedRoot x β)

end LinearAlgebraicGroups.Specs.ExceptionalOuterWallGroups
