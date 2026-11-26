import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.FieldTheory.Perfect

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.RadicalBaseChange

open GeometricRadicals
open Unipotent (baseChangedAlgebraicGroup)

def UnipotentRadicalBaseChange : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
    (G : AffineAlgebraicGroup k), Smooth G.val.X.hom → GeometricallyConnected G.val.X.hom →
    ∀ N : ClosedSubgroup G.val, IsUnipotentRadical G N →
      ∃ h : IsClosedImmersion ((groupBaseChange k K).map N.inclusion).hom.hom.left,
        IsUnipotentRadical (baseChangedAlgebraicGroup K G) (baseChangedSubgroup K N h)

def SolvableRadicalBaseChange : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
    (G : AffineAlgebraicGroup k), Smooth G.val.X.hom → GeometricallyConnected G.val.X.hom →
    ∀ N : ClosedSubgroup G.val, IsSolvableRadical G N →
      ∃ h : IsClosedImmersion ((groupBaseChange k K).map N.inclusion).hom.hom.left,
        IsSolvableRadical (baseChangedAlgebraicGroup K G) (baseChangedSubgroup K N h)

def ReductiveFieldExtension : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → GeometricallyConnected G.val.X.hom →
      (IsReductive (baseChangedAlgebraicGroup K G) ↔ IsReductive G)

def SemisimpleFieldExtension : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → GeometricallyConnected G.val.X.hom →
      (IsSemisimple (baseChangedAlgebraicGroup K G) ↔ IsSemisimple G)

def UnipotentRadicalPerfectDescent : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → GeometricallyConnected G.val.X.hom →
    ∃ N : ClosedSubgroup G.val, IsUnipotentRadical G N ∧
      ∃ e : (groupBaseChange k (AlgebraicClosure k)).obj N.group ≅
          (geometricUnipotentRadical G).group,
        e.hom ≫ (geometricUnipotentRadical G).inclusion =
          (groupBaseChange k (AlgebraicClosure k)).map N.inclusion

def SolvableRadicalPerfectDescent : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → GeometricallyConnected G.val.X.hom →
    ∃ N : ClosedSubgroup G.val, IsSolvableRadical G N ∧
      ∃ e : (groupBaseChange k (AlgebraicClosure k)).obj N.group ≅
          (geometricSolvableRadical G).group,
        e.hom ≫ (geometricSolvableRadical G).inclusion =
          (groupBaseChange k (AlgebraicClosure k)).map N.inclusion

end LinearAlgebraicGroups.Specs.RadicalBaseChange
