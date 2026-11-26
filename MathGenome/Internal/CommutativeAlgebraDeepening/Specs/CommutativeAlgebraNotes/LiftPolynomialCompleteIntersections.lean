import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace

/-! Unobstructedness for marked deformations of polynomial complete intersections. -/

namespace Specs.CommutativeAlgebraNotes.LiftPolynomialCompleteIntersections

open _root_.CommutativeAlgebraNotes
open Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace

universe u v z

/-- Every marked flat deformation lifts along a surjection of local Artin
algebras with the specified residue field. -/
def Lifting : Prop :=
  ∀ {k : Type u} [Field k] {n s : ℕ} (f : Fin s → P k n),
    RingTheory.Sequence.IsRegular (P k n) (List.ofFn f) →
    ∀ {A' A : LocalArtinAlgebra.{u,v} k} (π : LocalArtinAlgebra.Hom A' A),
      Function.Surjective π →
      ∀ D : MarkedDeformation.{u,v,u,z} A (B f),
        ∃ D' : MarkedDeformation.{u,v,u,z} A' (B f),
          MarkedDeformation.Isomorphic (MarkedDeformation.baseChangeModel π D') D

/-- The lifting property and the pointed identification of the tangent space
with the Jacobian cokernel for the same polynomial complete intersections. -/
def Unobstructed : Prop := Lifting.{u,v,z} ∧ TangentSpace.{u,z}

end Specs.CommutativeAlgebraNotes.LiftPolynomialCompleteIntersections
