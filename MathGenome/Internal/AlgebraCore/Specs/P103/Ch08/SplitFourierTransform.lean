import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RepresentationModules
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Split-field part of paper.tex, the split-field Fourier theorem, lines 1547–1549 and
1573–1577. Splitting means that the Schur rings of the simple regular
constituents are the base field *as algebras*, via their scalar maps.
Completeness is tested on simple left ideals: over a semisimple algebra
every simple module is isomorphic to one of these. No finite dimensionality
or finiteness of the representative family is assumed. -/
noncomputable section
universe u v x w
namespace P103.Ch08.SplitFourierTransform
open scoped MonoidAlgebra

variable (k : Type u) (G : Type v) [Field k] [Group G]

/-- The Schur-ring formulation of a split semisimple group algebra. -/
def Splits : Prop :=
  ∀ S : Ideal k[G], IsSimpleModule k[G] S →
    Function.Bijective (algebraMap k (Module.End k[G] S))

variable {k G} {ι : Type x} {V : ι → Type w}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  (ρ : ∀ i, Representation k G (V i))

/-- Every simple regular constituent is represented. -/
def Complete : Prop :=
  ∀ S : Ideal k[G], IsSimpleModule k[G] S →
    ∃ i, Nonempty (S ≃ₗ[k[G]] (ρ i).asModule)

/-- Representatives of different indices are not isomorphic. -/
def Nonrepeating : Prop :=
  ∀ i j, Nonempty ((ρ i).asModule ≃ₗ[k[G]] (ρ j).asModule) → i = j

/-- The actual unital action map, with the prescribed scalar structure. -/
def actionMap : k[G] →ₐ[k] Π i, Module.End k (V i) :=
  AlgHom.pi fun i => (ρ i).asAlgebraHom

namespace Specs

def finiteDimensionalType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V),
    Irreducible k G V ρ → FiniteDimensional k V

def finiteFamilyType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
    {ι : Type x} {V : ι → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (ρ : ∀ i, Representation k G (V i)),
    (Nat.card G : k) ≠ 0 →
    (∀ i, Irreducible k G (V i) (ρ i)) → Nonrepeating ρ → Finite ι

def fourierType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
    {ι : Type x} {V : ι → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (ρ : ∀ i, Representation k G (V i)),
    (Nat.card G : k) ≠ 0 → Splits k G →
    (∀ i, Irreducible k G (V i) (ρ i)) → Complete ρ → Nonrepeating ρ →
    ∃ E : k[G] ≃ₐ[k] Π i, Module.End k (V i),
      ∀ a i, E a i = (ρ i).asAlgebraHom a

end Specs
end P103.Ch08.SplitFourierTransform
