import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoarseningAndResidueValuations
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.RingTheory.LaurentSeries

noncomputable section

namespace Specs.CommutativeAlgebraNotes.LexicographicLaurentValuation

open OrderedValuationGroups (valueGroup value AddValuationInequality)
open ValuationPrimesAndConvexSubgroups (convexAddSubgroup PrimeValues)
open CoarseningAndResidueValuations (residueMap)
open Additive (ofMul)
open scoped WithZero

universe u

abbrev IteratedLaurent (k : Type u) [Zero k] := LaurentSeries (LaurentSeries k)
abbrev LexIntegers := ℤ ×ₗ ℤ

/-- On nonzero series these are the two orders in the source's valuation. -/
def seriesValue {k : Type u} [Field k] (f : IteratedLaurent k) : LexIntegers :=
  toLex (f.order, f.leadingCoeff.order)

/-- The subgroup consisting of the second coordinate. -/
def vertical : convexAddSubgroup LexIntegers :=
  ⟨{ carrier := {g | (ofLex g).1 = 0}
     zero_mem' := rfl
     add_mem' := fun {a b} ha hb ↦ show (ofLex a).1 + (ofLex b).1 = 0 by rw [ha, hb, add_zero]
     neg_mem' := fun {a} ha ↦ show -(ofLex a).1 = 0 by rw [ha, neg_zero] },
   by
     intro a b c ha hc hab hbc
     change (ofLex a).1 = 0 at ha
     change (ofLex c).1 = 0 at hc
     change (ofLex b).1 = 0
     exact le_antisymm (hc ▸ Prod.Lex.monotone_fst _ _ hbc)
       (ha ▸ Prod.Lex.monotone_fst _ _ hab)⟩

abbrev adicSubring (k : Type u) [Field k] : ValuationSubring (LaurentSeries k) :=
  (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring

def VerticalType := convexAddSubgroup LexIntegers

def ConvexSubgroups : Prop :=
  vertical.1 ≠ ⊥ ∧ vertical.1 ≠ ⊤ ∧
    ∀ H : convexAddSubgroup LexIntegers, H.1 = ⊥ ∨ H = vertical ∨ H.1 = ⊤

variable (k : Type u) [Field k]

def IsSeriesValuation (f : Additive (IteratedLaurent k)ˣ →+ LexIntegers) : Prop :=
  (∀ a : (IteratedLaurent k)ˣ, f (ofMul a) = seriesValue (a : IteratedLaurent k)) ∧
  AddValuationInequality f ∧ Function.Surjective f

def SeriesValuation : Prop :=
  ∀ (k : Type u) [Field k], ∃ f, IsSeriesValuation k f

def IsLocalizationAndResidue (V : ValuationSubring (IteratedLaurent k)) (P : PrimeSpectrum V) :
    Prop :=
  V.ofPrime P.asIdeal = adicSubring (LaurentSeries k) ∧
  (∀ x : IteratedLaurent k, x ∈ V ↔
    x ∈ adicSubring (LaurentSeries k) ∧ x.coeff 0 ∈ adicSubring k) ∧
  (∃ e : valueGroup (V.ofPrime P.asIdeal) ≃+o ℤ,
    ∀ a : (IteratedLaurent k)ˣ, e (value (V.ofPrime P.asIdeal) (ofMul a)) =
      (a : IteratedLaurent k).order) ∧
  ∃ r : P.asIdeal.ResidueField ≃+* LaurentSeries k,
    (∀ a : V, r (residueMap V P a) = (a : IteratedLaurent k).coeff 0) ∧
    (∀ z : P.asIdeal.ResidueField, z ∈ (residueMap V P).range ↔
      r z ∈ adicSubring k) ∧
    (∀ a : V, a ∉ P.asIdeal →
      (r (residueMap V P a)).order = (ofLex (seriesValue (a : IteratedLaurent k))).2) ∧
    ∃ W : ValuationSubring P.asIdeal.ResidueField,
      (∀ z, z ∈ W ↔ z ∈ (residueMap V P).range) ∧
      ∃ e : valueGroup W ≃+o ℤ,
        ∀ a : P.asIdeal.ResidueFieldˣ, e (value W (ofMul a)) =
          (r (a : P.asIdeal.ResidueField)).order

/-- The coarsening and the residue use the same prime of the specified valuation ring. -/
def LaurentExample : Prop :=
  ∀ (k : Type u) [Field k], ∃ (f : Additive (IteratedLaurent k)ˣ →+ LexIntegers)
    (V : ValuationSubring (IteratedLaurent k)) (P : PrimeSpectrum V),
      IsSeriesValuation k f ∧
      (∀ x : IteratedLaurent k, x ∈ V ↔ x = 0 ∨ 0 ≤ seriesValue x) ∧
      (∃ e : valueGroup V ≃+o LexIntegers,
        (∀ a : Additive (IteratedLaurent k)ˣ, e (value V a) = f a) ∧
        ∀ g : valueGroup V, 0 ≤ g → (e g ∈ vertical.1 ↔ PrimeValues V P g)) ∧
      IsLocalizationAndResidue k V P ∧
      ringKrullDim V = 2 ∧ ¬ IsNoetherianRing V

end Specs.CommutativeAlgebraNotes.LexicographicLaurentValuation
