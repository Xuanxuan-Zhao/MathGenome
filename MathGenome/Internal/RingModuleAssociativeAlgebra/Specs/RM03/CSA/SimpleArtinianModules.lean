import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Basic

universe u v w x

namespace RM03.Specs.CSA.SimpleArtinianModules

open scoped Matrix.Module

/-- The column module with its left action transported through the given presentation. -/
abbrev columnModule {k T E : Type*} [Field k] [Ring T] [DivisionRing E]
    [Algebra k T] [Algebra k E] {s : ℕ}
    (e : T ≃ₐ[k] Matrix (Fin s) (Fin s) E) : Module T (Fin s → E) :=
  Module.compHom (Fin s → E) e.toRingEquiv.toRingHom

/-- The transported column action is compatible with the coordinatewise field action. -/
theorem columnScalarTower {k T E : Type*} [Field k] [Ring T] [DivisionRing E]
    [Algebra k T] [Algebra k E] {s : ℕ}
    (e : T ≃ₐ[k] Matrix (Fin s) (Fin s) E) :
    letI := columnModule e
    IsScalarTower k T (Fin s → E) := by
  let := columnModule e
  constructor
  intro r t v
  change e (r • t) • v = r • (e t • v)
  rw [map_smul, smul_assoc]

/-- A finite-dimensional simple algebra has a positive-size matrix presentation as a k-algebra. -/
def matrixPresentationType : Prop :=
  ∀ (k : Type u) (T : Type v) [Field k] [Ring T] [Algebra k T]
    [Module.Finite k T] [IsSimpleRing T],
    ∃ (s : ℕ) (E : Type v) (_ : DivisionRing E) (_ : Algebra k E) (_ : Module.Finite k E),
      0 < s ∧ Nonempty (T ≃ₐ[k] Matrix (Fin s) (Fin s) E)

def columnSimpleType : Prop :=
  ∀ (k : Type u) (T : Type v) (E : Type w) [Field k] [Ring T] [DivisionRing E]
    [Algebra k T] [Algebra k E] (s : ℕ) (e : T ≃ₐ[k] Matrix (Fin s) (Fin s) E),
    0 < s →
    letI := columnModule e
    IsSimpleModule T (Fin s → E)

/-- Composition of right multiplications uses the opposite ring of the coefficient division ring. -/
def columnEndType : Prop :=
  ∀ (k : Type u) (T : Type v) (E : Type w) [Field k] [Ring T] [DivisionRing E]
    [Algebra k T] [Algebra k E] (s : ℕ) (e : T ≃ₐ[k] Matrix (Fin s) (Fin s) E),
    0 < s →
    letI := columnModule e
    letI := columnScalarTower e
    ∃ f : Eᵐᵒᵖ ≃ₐ[k] Module.End T (Fin s → E),
      ∀ (a : E) (z : Fin s → E) (i : Fin s), f (MulOpposite.op a) z i = z i * a

def simpleModuleEquivColumnType : Prop :=
  ∀ (k : Type u) (T : Type v) (E : Type w) [Field k] [Ring T] [DivisionRing E]
    [Algebra k T] [Algebra k E] [Module.Finite k T] [IsSimpleRing T]
    (s : ℕ) (e : T ≃ₐ[k] Matrix (Fin s) (Fin s) E), 0 < s →
    ∀ (S : Type x) [AddCommGroup S] [Module T S] [IsSimpleModule T S],
    letI := columnModule e
    Nonempty (S ≃ₗ[T] (Fin s → E))

/-- For finite index sets the function module is the finite direct sum of the columns. -/
def moduleDecompositionType : Prop :=
  ∀ (k : Type u) (T : Type v) (E : Type w) [Field k] [Ring T] [DivisionRing E]
    [Algebra k T] [Algebra k E] [Module.Finite k T] [IsSimpleRing T] [Module.Finite k E]
    (s : ℕ) (e : T ≃ₐ[k] Matrix (Fin s) (Fin s) E), 0 < s →
    ∀ (V : Type x) [AddCommGroup V] [Module k V] [Module T V] [IsScalarTower k T V]
      [Module.Finite k V] [Nontrivial V],
    letI := columnModule e
    ∃ m : ℕ, 0 < m ∧ Nonempty (V ≃ₗ[T] (Fin m → Fin s → E)) ∧
      Module.finrank k V = s * m * Module.finrank k E ∧
      (∀ n : ℕ, Module.finrank k V = s * n * Module.finrank k E → n = m) ∧
      Nonempty (Module.End T V ≃ₐ[k] Matrix (Fin m) (Fin m) Eᵐᵒᵖ) ∧
      Module.finrank k T = s ^ 2 * Module.finrank k E ∧
      Module.finrank k (Module.End T V) = m ^ 2 * Module.finrank k E

def endSimpleAndDimensionType : Prop :=
  ∀ (k : Type u) (T : Type v) [Field k] [Ring T] [Algebra k T]
    [Module.Finite k T] [IsSimpleRing T]
    (V : Type w) [AddCommGroup V] [Module k V] [Module T V] [IsScalarTower k T V]
    [Module.Finite k V] [Nontrivial V],
    Module.Finite k (Module.End T V) ∧ IsSimpleRing (Module.End T V) ∧
      Module.finrank k T * Module.finrank k (Module.End T V) = (Module.finrank k V) ^ 2

def equivOfFinrankEqType : Prop :=
  ∀ (k : Type u) (T : Type v) [Field k] [Ring T] [Algebra k T]
    [Module.Finite k T] [IsSimpleRing T]
    (V : Type w) [AddCommGroup V] [Module k V] [Module T V] [IsScalarTower k T V]
    [Module.Finite k V] [Nontrivial V]
    (W : Type x) [AddCommGroup W] [Module k W] [Module T W] [IsScalarTower k T W]
    [Module.Finite k W] [Nontrivial W],
    Module.finrank k V = Module.finrank k W → Nonempty (V ≃ₗ[T] W)

end RM03.Specs.CSA.SimpleArtinianModules
