import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RepresentationModules
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent statements for paper.tex 1364–1381 (Schur's lemma).
The representation and nonzero irreducibility convention are the shared
Chapter 8 objects. Neither the group nor the representations need be finite
for the first two assertions. Multiplication on intertwining endomorphisms
is composition. Only the scalar assertion assumes finite dimension and an
algebraically closed base field.
-/

universe u v w x
namespace P103.Ch08.Specs.Schur

/-- The isomorphism is equivariant and has the specified original map. -/
def nonzeroIntertwinerType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} {W : Type x}
    [Field k] [Group G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    Irreducible k G V ρ → Irreducible k G W σ →
    ∀ f : ρ.IntertwiningMap σ, f ≠ 0 →
      ∃ e : ρ.Equiv σ, e.toIntertwiningMap = f

/-- A division ring structure on the original endomorphism algebra, retaining
its existing addition, composition, zero and identity. The scalar action is
the original one on intertwining maps. -/
def endomorphismDivisionRingType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w}
    [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V), Irreducible k G V ρ →
      ∃ D : DivisionRing (ρ.IntertwiningMap ρ),
        D.toSemiring = (inferInstance : Semiring (ρ.IntertwiningMap ρ))

/-- Every intertwining endomorphism is a unique scalar multiple of identity. -/
def uniqueScalarType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w}
    [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [IsAlgClosed k]
    (ρ : Representation k G V), Irreducible k G V ρ →
    ∀ f : ρ.IntertwiningMap ρ,
      ∃! c : k, f = c • Representation.IntertwiningMap.id ρ

end P103.Ch08.Specs.Schur
