import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftGraph
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.Algebra.Torsor.Defs

noncomputable section

namespace Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor

open CommutativeAlgebraNotes.SquareZeroLift

universe u v w t n l m

variable {A' : Type u} {A : Type v} {B : Type w} {σ : Type t}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B] {e : BaseExtension A' A}
  (p : Presentation e B σ)

/-- Precomposition with the reduced conormal differential. The tensor in Mathlib's
cotangent space puts the factor B on the left. -/
def conormalRestriction (N : Type n) [AddCommGroup N] [Module B N] :
    (p.barExtension.CotangentSpace →ₗ[B] N) →ₗ[B] (p.BarConormal →ₗ[B] N) :=
  LinearMap.lcomp B N p.barExtension.cotangentComplex

/-- The cokernel of the restriction along the reduced conormal differential. -/
abbrev T1 (N : Type n) [AddCommGroup N] [Module B N] :=
  (p.BarConormal →ₗ[B] N) ⧸ (conormalRestriction p N).range

set_option linter.checkUnivs false in
def conormalRestrictionType := type_of% @conormalRestriction
set_option linter.checkUnivs false in
def T1Type := type_of% @T1

variable {N : Type n} [AddCommGroup N] [Module B N] {c : e.CoefficientMap (B := B) N}

/-- The marked isomorphism class of a lift in its own universe. -/
abbrev liftClass (L : Lift.{u,v,w,n,l} e c) :
    Lift.Classes.{u,v,w,n,l} c :=
  Quotient.mk (Lift.isoSetoid (c := c)) L

/-- Translation by a cokernel element represented by g adds the pullback of g
to the evaluated relation map. -/
def ActsByReduction
    (action : VAdd (T1 p N) (Lift.Classes.{u,v,w,n,max u t n} c)) : Prop :=
  ∀ (g : p.BarConormal →ₗ[B] N)
    (L M : p.ChosenLift.{u,v,w,t,n,max u t n} c) (ρ τ : p.RelationMaps c),
    L.Realizes ρ → M.Realizes τ →
    τ.val = ρ.val + g.comp p.conormalReduction →
    action.vadd ((conormalRestriction p N).range.mkQ g) (liftClass L.lift) =
      liftClass M.lift

def torsorType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    (p : Presentation e B σ) (c : e.CoefficientMap (B := B) N),
    Nonempty (Lift.{u,v,w,n,l} e c) →
      ∃ a : AddTorsor (T1 p N) (Lift.Classes.{u,v,w,n,max u t n} c),
        ActsByReduction p a.toAddAction.toVAdd

/-- The reduced conormal differences account for precisely the marked isomorphisms,
including when representatives use different universes. -/
def liftIsoType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    {p : Presentation e B σ} {c : e.CoefficientMap (B := B) N}
    (L : p.ChosenLift.{u,v,w,t,n,l} c) (M : p.ChosenLift.{u,v,w,t,n,m} c)
    (ρ τ : p.RelationMaps c), L.Realizes ρ → M.Realizes τ →
    (Nonempty (L.lift.Iso M.lift) ↔
      ∃ h : p.barExtension.CotangentSpace →ₗ[B] N,
        τ.val - ρ.val = (conormalRestriction p N h).comp p.conormalReduction)

/-- Classes in the graph universe represent lifts from any universe, with precisely the
prescribed notion of isomorphism. -/
def classRepresentativeType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    (_p : Presentation e B σ) {c : e.CoefficientMap (B := B) N}
    (L : Lift.{u,v,w,n,l} e c),
    ∃ X : Lift.Classes.{u,v,w,n,max u t n} c,
      ∀ M : Lift.{u,v,w,n,max u t n} e c,
        X = liftClass M ↔ Nonempty (L.Iso M)

end Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor
