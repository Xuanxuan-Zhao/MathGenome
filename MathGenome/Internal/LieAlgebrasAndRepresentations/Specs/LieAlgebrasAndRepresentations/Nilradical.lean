import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CharacteristicRadical
import Mathlib.Algebra.Lie.Engel

/-! LA-B08, source lines 1001–1097. The nilradical is the sum of ideals
which are nilpotent as Lie algebras in their own right. This is distinct
from nilpotence as a module for the full ambient Lie algebra. -/

universe u v
namespace Specs.LieAlgebrasAndRepresentations.Nilradical

def nilradical_value (k : Type u) (L : Type v) [Field k]
    [LieRing L] [LieAlgebra k L] : LieIdeal k L :=
  sSup {I : LieIdeal k L | LieRing.IsNilpotent I}

def nilradical_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L], LieIdeal k L

def nilradical_nilpotent_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    LieRing.IsNilpotent (nilradical_value k L)

def nilpotent_ideal_le_nilradical_type : Prop :=
  ∀ {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
    (I : LieIdeal k L), LieRing.IsNilpotent I → I ≤ nilradical_value k L

def mem_nilradical_iff_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] (x : L),
    x ∈ nilradical_value k L ↔
      x ∈ SolvableRadical.radical_value k L ∧ IsNilpotent (LieAlgebra.ad k L x)

def derivation_radical_mem_nilradical_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (D : LieDerivation k L L) (x : L),
    x ∈ SolvableRadical.radical_value k L → D x ∈ nilradical_value k L

def derivation_nilradical_mem_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (D : LieDerivation k L L) (x : L),
    x ∈ nilradical_value k L → D x ∈ nilradical_value k L

def bracket_radical_le_nilradical_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    ⁅(⊤ : LieIdeal k L), SolvableRadical.radical_value k L⁆ ≤ nilradical_value k L

end Specs.LieAlgebrasAndRepresentations.Nilradical
