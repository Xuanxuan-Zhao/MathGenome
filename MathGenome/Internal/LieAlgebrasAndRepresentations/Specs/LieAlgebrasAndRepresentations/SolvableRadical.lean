import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Independent specification of the radical part of LA-B05, source lines
865–883. The chapter convention imposes finite dimension. No characteristic
restriction is needed for this part. The Killing criterion is allocated to
LA-B05. Semisimplicity here means vanishing radical, including the zero algebra.
The supremum in `LieIdeal` is the sum of ideals, not their set-theoretic union. -/

universe u v
namespace Specs.LieAlgebrasAndRepresentations.SolvableRadical

/-- The sum of all solvable ideals, with no finiteness needed for the definition. -/
def radical_value (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L] :
    LieIdeal k L := LieAlgebra.radical k L

def radical_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L], LieIdeal k L

/-- The source's definition, valid in every characteristic. -/
def IsSemisimple_value (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L] :
    Prop := radical_value k L = ⊥

def IsSemisimple_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L], Prop

def radical_eq_sum_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L],
    radical_value k L = sSup {I : LieIdeal k L | LieAlgebra.IsSolvable I}

def radical_solvable_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L], LieAlgebra.IsSolvable (radical_value k L)

def solvable_ideal_le_radical_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]
    (I : LieIdeal k L), LieAlgebra.IsSolvable I → I ≤ radical_value k L

def quotient_no_solvable_ideal_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] (J : LieIdeal k (L ⧸ radical_value k L)),
    LieAlgebra.IsSolvable J → J = ⊥

def semisimple_iff_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L],
    IsSemisimple_value k L ↔ radical_value k L = ⊥

def semisimple_iff_no_solvable_ideals_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L],
    IsSemisimple_value k L ↔ ∀ I : LieIdeal k L, LieAlgebra.IsSolvable I → I = ⊥

def semisimple_of_subsingleton_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    [Subsingleton L], IsSemisimple_value k L

def quotient_semisimple_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L], IsSemisimple_value k (L ⧸ radical_value k L)

end Specs.LieAlgebrasAndRepresentations.SolvableRadical
