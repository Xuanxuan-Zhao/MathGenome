import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.SquareZeroLifts
import Mathlib.Algebra.Group.Action.Defs

/-! Independent statements for paper.tex, FL-03 (The set of lifts).
The module structure is induced by the map to the quotient, independently
of a reference lift. Zero rings and empty fibers are allowed. -/
namespace Specs.AdvCommAlg.FormalLifting

open Specs.AdvCommAlg.Differentials.SquareZero
universe u v w
noncomputable section

/-- The additive group acting on the fiber. -/
abbrev LiftCoordinates {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (N : Ideal C) (hN : N ^ 2 = ⊥) (u : B →ₐ[A] C ⧸ N) :=
  letI := idealModule N hN u
  KaehlerDifferential A B →ₗ[B] N

/-- Composition with d followed by addition to any chosen lift is bijective. -/
def liftParametrization : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (N : Ideal C) (hN : N ^ 2 = ⊥) (u : B →ₐ[A] C ⧸ N),
    ∀ v : Lifts N u, ∃ e : LiftCoordinates N hN u ≃ Lifts N u,
      ∀ (h : LiftCoordinates N hN u) (b : B),
        (e h).1 b = v.1 b + (h (KaehlerDifferential.D A B b) : C)

/-- Moving the reference by h₀ changes the coordinate h to h - h₀.
This holds for any two parametrizations with the specified pointwise formula. -/
def referenceChange : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (N : Ideal C) (hN : N ^ 2 = ⊥) (u : B →ₐ[A] C ⧸ N),
    ∀ (v : Lifts N u) (e : LiftCoordinates N hN u ≃ Lifts N u),
      (∀ (h : LiftCoordinates N hN u) (b : B),
        (e h).1 b = v.1 b + (h (KaehlerDifferential.D A B b) : C)) →
    ∀ (h₀ : LiftCoordinates N hN u)
      (e' : LiftCoordinates N hN u ≃ Lifts N u),
      (∀ (h : LiftCoordinates N hN u) (b : B),
        (e' h).1 b = (e h₀).1 b + (h (KaehlerDifferential.D A B b) : C)) →
    ∀ h : LiftCoordinates N hN u,
      e' (h - h₀) = e h ∧ e'.symm (e h) = h - h₀

/-- Addition of h d is an additive group action. On any nonempty fiber,
each ordered pair of lifts is joined by a unique group element. Freeness is
also stated explicitly, without asserting that an arbitrary fiber has a lift. -/
def liftsAction : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (N : Ideal C) (hN : N ^ 2 = ⊥) (u : B →ₐ[A] C ⧸ N),
    ∃ action : AddAction (LiftCoordinates N hN u) (Lifts N u),
      letI := action
      (∀ (h : LiftCoordinates N hN u) (v : Lifts N u) (b : B),
        (h +ᵥ v).1 b = v.1 b + (h (KaehlerDifferential.D A B b) : C)) ∧
      (∀ (h k : LiftCoordinates N hN u) (v : Lifts N u),
        h +ᵥ v = k +ᵥ v → h = k) ∧
      (∀ v w : Lifts N u, ∃! h : LiftCoordinates N hN u, h +ᵥ v = w)

end
end Specs.AdvCommAlg.FormalLifting
