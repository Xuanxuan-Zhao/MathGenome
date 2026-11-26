import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
import Mathlib.Analysis.Complex.Circle

open Topology

namespace LinearAlgebraicGroups.Specs.ExceptionalOuterCompactCentralizer

open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open ExceptionalCompactInner (fixedSubgroup HasExceptionalType)
open IntegralModels (MatrixRealization)
open SimplyConnectedLattice (GeometricallySimplyConnected)

variable {P : Type*} [Group P] [TopologicalSpace P]

/-- The identity component of a subgroup, using its induced topology and
viewed as a subset of the ambient group. -/
def identityComponent (J : Subgroup P) : Set P :=
  Subtype.val '' connectedComponent (1 : J)

/-- A compact torus with its subgroup topology, including the trivial torus. -/
def IsCompactTorus (T : Subgroup P) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → Circle) ≃* T), Continuous e ∧ Continuous e.symm

/-- Maximality is among compact tori contained in the given subset. -/
def IsMaximalCompactTorus (J : Set P) (T : Subgroup P) : Prop :=
  IsCompactTorus T ∧ (T : Set P) ⊆ J ∧
    ∀ V : Subgroup P, IsCompactTorus V → (V : Set P) ⊆ J → T ≤ V → V = T

/-- The identity component of the full centralizer of a maximal torus of
the connected fixed group is an invariant maximal torus of the compact group. -/
def CompactCentralizer : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)),
      Continuous ω → Continuous θ → Function.Involutive ω → Function.Involutive θ →
      Function.Commute θ ω →
      CompactSpace (fixedSubgroup ω) → ConnectedSpace (fixedSubgroup ω) →
      ∀ S : Subgroup (PointsIn i ℂ),
        IsMaximalCompactTorus (identityComponent (fixedSubgroup ω ⊓ fixedSubgroup θ)) S →
        ∃ T : Subgroup (PointsIn i ℂ),
          (T : Set (PointsIn i ℂ)) =
            identityComponent (fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _)) ∧
          S ≤ T ∧ T.map θ.toMonoidHom = T ∧ IsMaximalCompactTorus (fixedSubgroup ω : Set _) T

end LinearAlgebraicGroups.Specs.ExceptionalOuterCompactCentralizer
