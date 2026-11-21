import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DarbouxFubini
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.ExceptionalSets

/-! Independent statements for d04:06:exceptional-slices and d04:06:bad-slice.
Nullity means countable box covers; content zero means finite box covers.
All slice functions retain their original pointwise values. -/
noncomputable section
open Set
namespace Specs.D04.C06.ExceptionalSlices.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.DarbouxFubini.Model

def sliceGap {p q : ℕ} (f : E (p + q) → ℝ) (B : Box q) (x : E p) : ℝ :=
  upperSlice f B x - lowerSlice f B x

def sliceGapReverse {p q : ℕ} (f : E (p + q) → ℝ) (A : Box p) (y : E q) : ℝ :=
  upperSliceReverse f A y - lowerSliceReverse f A y

def exceptionalSet {p q : ℕ} (A : Box p) (B : Box q)
    (f : E (p + q) → ℝ) : Set (E p) :=
  {x | x ∈ carrier A ∧ ¬ Integrable (fun y => f (productPoint x y)) B}

def exceptionalSetReverse {p q : ℕ} (A : Box p) (B : Box q)
    (f : E (p + q) → ℝ) : Set (E q) :=
  {y | y ∈ carrier B ∧ ¬ Integrable (fun x => f (productPoint x y)) A}

/-- The exact product of the singleton indicator and the rational indicator. -/
def badSlice (z : E (1 + 1)) : ℝ := by
  classical
  exact (if z 0 = 0 then 1 else 0) *
    (if z 1 ∈ Set.range (fun r : ℚ => (r : ℝ)) then 1 else 0)
end Specs.D04.C06.ExceptionalSlices.Model

namespace Specs.D04.C06.ExceptionalSlices
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.DarbouxFubini.Model
open Specs.D04.C06.NullCovers.Model
open Specs.D04.C06.ExceptionalSets.Model Model

abbrev sliceGapType := {p q : ℕ} → (E (p + q) → ℝ) → Box q → E p → ℝ
def sliceGapValue : sliceGapType := @Model.sliceGap
abbrev sliceGapReverseType := {p q : ℕ} → (E (p + q) → ℝ) → Box p → E q → ℝ
def sliceGapReverseValue : sliceGapReverseType := @Model.sliceGapReverse
abbrev exceptionalSetType := {p q : ℕ} → Box p → Box q → (E (p + q) → ℝ) → Set (E p)
def exceptionalSetValue : exceptionalSetType := @Model.exceptionalSet
abbrev exceptionalSetReverseType := {p q : ℕ} → Box p → Box q → (E (p + q) → ℝ) → Set (E q)
def exceptionalSetReverseValue : exceptionalSetReverseType := @Model.exceptionalSetReverse
abbrev badSliceType := E (1 + 1) → ℝ
def badSliceValue : badSliceType := Model.badSlice

/-- The finite-cover statement used for the gap, independently reusable. -/
def zero_integral_level_contentZeroType : Prop := ∀ {n : ℕ} (Q : Box n)
  (w : E n → ℝ) (hw : Integrable w Q),
  (∀ x ∈ carrier Q, 0 ≤ w x) → integral w Q hw = 0 →
  ∀ η > 0, ContentZero {x | x ∈ carrier Q ∧ η ≤ w x}

def exceptional_slicesType : Prop := ∀ {p q : ℕ}, 0 < p → 0 < q →
  ∀ (A : Box p) (B : Box q) (f : E (p + q) → ℝ)
    (hf : Integrable f (productBox A B)),
  ∃ hw : Integrable (sliceGap f B) A,
    (∀ x ∈ carrier A, 0 ≤ sliceGap f B x) ∧ integral (sliceGap f B) A hw = 0 ∧
    (∀ η > 0, ContentZero {x | x ∈ carrier A ∧ η ≤ sliceGap f B x}) ∧
    {x | x ∈ carrier A ∧ 0 < sliceGap f B x} = exceptionalSet A B f ∧
    Null (exceptionalSet A B f)

def exceptional_slices_reverseType : Prop := ∀ {p q : ℕ}, 0 < p → 0 < q →
  ∀ (A : Box p) (B : Box q) (f : E (p + q) → ℝ)
    (hf : Integrable f (productBox A B)),
  ∃ hw : Integrable (sliceGapReverse f A) B,
    (∀ y ∈ carrier B, 0 ≤ sliceGapReverse f A y) ∧ integral (sliceGapReverse f A) B hw = 0 ∧
    (∀ η > 0, ContentZero {y | y ∈ carrier B ∧ η ≤ sliceGapReverse f A y}) ∧
    {y | y ∈ carrier B ∧ 0 < sliceGapReverse f A y} = exceptionalSetReverse A B f ∧
    Null (exceptionalSetReverse A B f)

/-- All claims about the separately stated counterexample, including both outer values. -/
def bad_slice_exampleType : Prop :=
  (∃ hf : Integrable badSlice (productBox unitBox unitBox),
    integral badSlice (productBox unitBox unitBox) hf = 0) ∧
  ¬ Integrable (fun y => badSlice (productPoint (0 : E 1) y)) unitBox ∧
  (∀ x : E 1, lowerSlice badSlice unitBox x = 0 ∧
    upperSlice badSlice unitBox x = if x 0 = 0 then 1 else 0) ∧
  (∃ (hl : Integrable (lowerSlice badSlice unitBox) unitBox)
     (hu : Integrable (upperSlice badSlice unitBox) unitBox),
    integral (lowerSlice badSlice unitBox) unitBox hl = 0 ∧
    integral (upperSlice badSlice unitBox) unitBox hu = 0)
end Specs.D04.C06.ExceptionalSlices
