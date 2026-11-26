import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedWeyl
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterTorus

noncomputable section

set_option autoImplicit false

namespace LinearAlgebraicGroups.Specs.ExceptionalOuterCompactWeylLabels

open CategoryTheory
open Arithmetic.AdelicGroups (PointsIn)
open AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple PreservesCartan)
open CharacterDescent (Cocharacter)
open ExceptionalCompactInner (HasExceptionalType fixedSubgroup)
open ExceptionalFoldedWeyl (E6Space e6Diagram e6Lattice e6Weyl foldedSpace
  diagramCentralizingWeyl)
open ExceptionalOuterTorus (MarkedPair OuterInvolutions IsMaximalCompactTorus
  fixedCompact identityComponent)
open IntegralModels (MatrixRealization)
open RootGroups (AdditiveLine)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- A compact normalizer of the fixed torus acts by an absolute Weyl element
in the given marked coordinates. If it is fixed by the normalized twist,
its Weyl element commutes with the diagram reflection. -/
def CompactWeylLabels : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)), OuterInvolutions (i := i) ω θ →
      ∀ S : Subgroup (PointsIn i ℂ),
        IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) S →
        ∀ (T : Subgroup (PointsIn i ℂ)) (A : AdditiveLine ℂ) (M : MarkedPair G A)
          (δ : MulAut (PointsIn i ℂ)),
          T = fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _) →
          (T : Set (PointsIn i ℂ)) = (fixedSubgroup ω : Set _) ∩
            Set.range (M.onPoints (i := i) M.P.pair.T.inclusion) →
          (letI := M.datum.comm
           PreservesCartan (RootData.integralCartan M.datum.datum.rootDatum M.datum.base)
             (CartanMatrix.E 6) M.numbering) →
          (letI := M.datum.comm
           ∃ b : Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)),
             ∀ j, b j = Additive.ofMul (M.coroot j)) →
          (∀ y z, M.exp (i := i) (y + z) = M.exp y * M.exp z) →
          (T : Set (PointsIn i ℂ)) = Set.range (M.exp (i := i)) →
          (∀ y, M.exp (i := i) y = 1 ↔ y ∈ e6Lattice) →
          (∀ y, δ (M.exp (i := i) y) = M.exp (e6Diagram y)) →
          ∀ n ∈ fixedSubgroup ω, n ∈ Subgroup.normalizer (S : Set _) →
            ∃ w ∈ e6Weyl,
              (∀ y, n * M.exp (i := i) y * n⁻¹ = M.exp (w y)) ∧
              ∀ x ∈ foldedSpace,
                let θx := MulAut.conj (M.exp (i := i) x) * δ
                Function.Involutive θx → n ∈ fixedCompact ω θx →
                  w ∈ diagramCentralizingWeyl

end LinearAlgebraicGroups.Specs.ExceptionalOuterCompactWeylLabels
