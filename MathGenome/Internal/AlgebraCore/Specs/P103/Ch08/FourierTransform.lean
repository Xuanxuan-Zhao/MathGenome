import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RegularMultiplicity
import Mathlib.LinearAlgebra.Trace

/-! The complex action-map and inverse in paper.tex 1538–1547, 1561–1571.
The spaces in this family are arbitrary complex vector spaces, not left ideals.
Completeness is ordinary exhaustiveness among nonzero irreducibles. Testing
spaces in the group universe suffices in every universe, since every irreducible
is isomorphic to a simple regular ideal, without any dimension assumption. -/
noncomputable section
universe u v
namespace P103.Ch08.FourierSpecs
open scoped MonoidAlgebra

structure Family (G : Type u) [Group G] where
  n : ℕ
  space : Fin n → Type v
  add : ∀ i, AddCommGroup (space i)
  module : ∀ i, Module ℂ (space i)
  representation : ∀ i, letI := add i; letI := module i; Representation ℂ G (space i)

attribute [instance] Family.add Family.module

variable {G : Type u} [Group G]

def Valid (C : Family.{u,v} G) : Prop :=
  (∀ i, Irreducible ℂ G (C.space i) (C.representation i)) ∧
  ∀ i j, Nonempty ((C.representation i).Equiv (C.representation j)) → i = j

/-- Every irreducible representation occurs. The implementation also proves
that this condition covers representation spaces in any other universe. -/
def Complete (C : Family.{u,v} G) : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W),
    Irreducible ℂ G W σ → ∃ i, Nonempty ((C.representation i).Equiv σ)

/-- This is the actual action map, using the given group actions. -/
def action (C : Family.{u,v} G) :
    ℂ[G] →ₐ[ℂ] (∀ i, Module.End ℂ (C.space i)) :=
  AlgHom.pi fun i => (C.representation i).asAlgebraHom

/-- The displayed inverse formula, including the inverse group element. -/
def inverseCoefficient [Fintype G] (C : Family.{u,v} G)
    (B : ∀ i, Module.End ℂ (C.space i)) (g : G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ i : Fin C.n,
    (Module.finrank ℂ (C.space i) : ℂ) *
      LinearMap.trace ℂ (C.space i) (C.representation i g⁻¹ * B i)

/-- An algebra equivalence equal to the specified finite-support action, its
inverse coefficients on every tuple of endomorphisms, and coefficient recovery. -/
def fourierType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C →
    ∃ E : ℂ[G] ≃ₐ[ℂ] (∀ i, Module.End ℂ (C.space i)),
      (∀ a i, E a i = (C.representation i).asAlgebraHom a) ∧
      (∀ a i (x : C.space i), E a i x =
        a.coeff.sum (fun g c => c • C.representation i g x)) ∧
      (∀ B g, (E.symm B).coeff g = inverseCoefficient C B g) ∧
      (∀ a g, inverseCoefficient C (action C a) g = a.coeff g)

end P103.Ch08.FourierSpecs
