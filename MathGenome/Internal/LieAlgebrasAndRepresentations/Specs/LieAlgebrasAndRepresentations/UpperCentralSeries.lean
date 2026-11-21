import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries

/-!
LA-A02-Upper, source res:A02, lines 221–225 and 245–251.
All fields and all Lie algebras, including the zero algebra, are allowed.
The successor membership statement identifies the series with the inverse image
of the center under the canonical quotient map. Lower central series indices
are those of the accepted positive-indexed interface (extended by γ₀ = ⊤).
The two comparison inclusions are stated for every natural r, so they also
cover the usual range 0 ≤ r ≤ c and its boundary cases.
-/

universe u v
namespace Specs.LieAlgebrasAndRepresentations.UpperCentralSeries

variable (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]

def upperCentralSeries_value (n : ℕ) : LieIdeal k L :=
  (⊥ : LieIdeal k L).ucs n

def upperCentralSeries_type :=
  ∀ (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L],
    ℕ → LieIdeal k L

def upperCentralSeries_zero_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L],
    upperCentralSeries_value k L 0 = ⊥

def upperCentralSeries_succ_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]
    (n : ℕ) (x : L),
    x ∈ upperCentralSeries_value k L (n + 1) ↔
      (LieSubmodule.Quotient.mk x : L ⧸ upperCentralSeries_value k L n) ∈
        LieAlgebra.center k (L ⧸ upperCentralSeries_value k L n)

def upperCentralSeries_mono_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L],
    Monotone (upperCentralSeries_value k L)

def upperCentralSeries_eq_top_iff_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L] (c : ℕ),
    upperCentralSeries_value k L c = ⊤ ↔
      DerivedLowerSeries.lowerCentralSeries_value k L (c + 1) = ⊥

def upperCentralSeries_reaches_iff_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L],
    (∃ c, upperCentralSeries_value k L c = ⊤) ↔
      ∃ c, DerivedLowerSeries.lowerCentralSeries_value k L (c + 1) = ⊥

def upperCentralSeries_nilpotent_iff_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L],
    (∃ c, upperCentralSeries_value k L c = ⊤) ↔ LieRing.IsNilpotent L

def lower_le_upper_of_lower_eq_bot_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]
    (c r : ℕ) (h : DerivedLowerSeries.lowerCentralSeries_value k L (c + 1) = ⊥),
    DerivedLowerSeries.lowerCentralSeries_value k L (c + 1 - r) ≤
      upperCentralSeries_value k L r

def lower_le_upper_of_upper_eq_top_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]
    (c r : ℕ) (h : upperCentralSeries_value k L c = ⊤),
    DerivedLowerSeries.lowerCentralSeries_value k L (r + 1) ≤
      upperCentralSeries_value k L (c - r)

end Specs.LieAlgebrasAndRepresentations.UpperCentralSeries
