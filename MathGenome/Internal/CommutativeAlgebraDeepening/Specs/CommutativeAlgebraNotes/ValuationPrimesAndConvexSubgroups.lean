import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.OrderedValuationGroups
import Mathlib.RingTheory.KrullDimension.Basic

noncomputable section

namespace Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups

open OrderedValuationGroups (valueGroup value)
open Additive (ofMul)

universe u

/-- An additive subgroup containing every order interval between two of its elements.
The subtype inherits the subgroup inclusion order. -/
abbrev convexAddSubgroup (Γ : Type u) [AddGroup Γ] [Preorder Γ] :=
  { H : AddSubgroup Γ // ∀ ⦃a b c : Γ⦄, a ∈ H → c ∈ H → a ≤ b → b ≤ c → b ∈ H }

abbrev ringValue {K : Type u} [Field K] (V : ValuationSubring K) (x : V) (hx : x ≠ 0) :
    valueGroup V :=
  value V (ofMul (Units.mk0 (x : K) (by
    intro h
    exact hx (Subtype.ext h))))

/-- The values of the nonzero elements of the valuation ring outside a prime. -/
def PrimeValues {K : Type u} [Field K] (V : ValuationSubring K) (P : PrimeSpectrum V)
    (g : valueGroup V) : Prop :=
  ∃ (x : V) (hx : x ≠ 0), x ∉ P.asIdeal ∧ ringValue V x hx = g

abbrev valuationRank {K : Type u} [Field K] (V : ValuationSubring K) : WithBot ℕ∞ :=
  ringKrullDim V

def ConvexAddSubgroupType :=
  ∀ (Γ : Type u) [AddGroup Γ] [Preorder Γ], Type u

def ValuationRankType :=
  ∀ {K : Type u} [Field K], ValuationSubring K → WithBot ℕ∞

def Correspondence : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K),
    ∃ e : (PrimeSpectrum V)ᵒᵈ ≃o convexAddSubgroup (valueGroup V),
      (∀ (P : PrimeSpectrum V) (g : valueGroup V),
        (0 ≤ g ∧ g ∈ (e (OrderDual.toDual P)).1) ↔ PrimeValues V P g) ∧
      (∀ (H : convexAddSubgroup (valueGroup V)) (x : V),
        x ∈ (OrderDual.ofDual (e.symm H)).asIdeal ↔
          x = 0 ∨ ∃ hx : x ≠ 0, 0 ≤ ringValue V x hx ∧ ringValue V x hx ∉ H.1) ∧
      (e (OrderDual.toDual (⊥ : PrimeSpectrum V))).1 = ⊤ ∧
      (e (OrderDual.toDual (⟨IsLocalRing.maximalIdeal V, inferInstance⟩ : PrimeSpectrum V))).1 = ⊥

def RankAsChainLength : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K),
    valuationRank V = ⨆ c : LTSeries (convexAddSubgroup (valueGroup V)), (c.length : WithBot ℕ∞)

end Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups
