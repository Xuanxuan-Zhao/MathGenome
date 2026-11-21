import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Quotients
import Mathlib.Algebra.Lie.Nilpotent

/-!
Independent specification for LA-A02, source lines 205–252.
No dimension or characteristic assumptions. Ideals are `LieIdeal k L`;
`bracket_span_type` explicitly identifies their bracket with the linear span.
The positive-indexed lower central series is extended at 0 by the top ideal.
LA-A02-Upper owns the upper central series; LA-U02 owns the following boundary example.
-/

universe u v
namespace Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries

variable (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]

def derivedSeries_value (n : ℕ) : LieIdeal k L :=
  LieAlgebra.derivedSeries k L n

def lowerCentralSeries_value (n : ℕ) : LieIdeal k L :=
  LieModule.lowerCentralSeries k L L (n - 1)

def derivedSeries_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L],
    ℕ → LieIdeal k L

def lowerCentralSeries_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L],
    ℕ → LieIdeal k L

def bracket_span_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (I J : LieIdeal k L),
    (⁅I, J⁆ : LieIdeal k L).toSubmodule =
      Submodule.span k { ⁅x, y⁆ | (x ∈ I) (y ∈ J) }

def derivedSeries_zero_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L],
    derivedSeries_value k L 0 = ⊤

def derivedSeries_succ_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (n : ℕ),
    derivedSeries_value k L (n + 1) = ⁅derivedSeries_value k L n, derivedSeries_value k L n⁆

def lowerCentralSeries_one_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L],
    lowerCentralSeries_value k L 1 = ⊤

def lowerCentralSeries_succ_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (n : ℕ) (hn : 0 < n),
    lowerCentralSeries_value k L (n + 1) = ⁅(⊤ : LieIdeal k L), lowerCentralSeries_value k L n⁆

def series_are_ideals_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (n : ℕ) (x y : L),
    (y ∈ derivedSeries_value k L n → ⁅x, y⁆ ∈ derivedSeries_value k L n) ∧
    (y ∈ lowerCentralSeries_value k L n → ⁅x, y⁆ ∈ lowerCentralSeries_value k L n)

def solvable_iff_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L],
    LieAlgebra.IsSolvable L ↔ ∃ n, derivedSeries_value k L n = ⊥

def nilpotent_iff_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L],
    LieRing.IsNilpotent L ↔
    ∃ n, 0 < n ∧ lowerCentralSeries_value k L n = ⊥

def solvable_subalgebra_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (S : LieSubalgebra k L) (h : LieAlgebra.IsSolvable L),
    LieAlgebra.IsSolvable S

def nilpotent_subalgebra_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (S : LieSubalgebra k L) (h : LieRing.IsNilpotent L),
    LieRing.IsNilpotent S

def solvable_quotient_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (I : LieIdeal k L) (h : LieAlgebra.IsSolvable L),
    LieAlgebra.IsSolvable (L ⧸ I)

def nilpotent_quotient_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (I : LieIdeal k L) (h : LieRing.IsNilpotent L),
    LieRing.IsNilpotent (L ⧸ I)

def solvable_extension_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (I : LieIdeal k L) (hI : LieAlgebra.IsSolvable I)
    (hQ : LieAlgebra.IsSolvable (L ⧸ I)),
    LieAlgebra.IsSolvable L

def lowerCentralSeries_bracket_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (i j : ℕ) (hi : 0 < i) (hj : 0 < j),
    ⁅lowerCentralSeries_value k L i, lowerCentralSeries_value k L j⁆ ≤
      lowerCentralSeries_value k L (i + j)

end Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries
