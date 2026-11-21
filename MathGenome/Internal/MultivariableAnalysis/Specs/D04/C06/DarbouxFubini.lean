import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DarbouxIntegral
import Mathlib.Logic.Equiv.Fin.Basic

/-! Pointwise Darboux Fubini (paper.tex, d04:06:fubini).
The inner lower/upper integrals use the original values at every parameter.
No slice integrability or exceptional-set replacement enters the main theorem.
All dimensions are allowed; in particular positive dimensions and degenerate
closed boxes are included. -/
noncomputable section
open Set
namespace Specs.D04.C06.DarbouxFubini.Model
open Specs.D04.C06.DarbouxIntegral.Model

abbrev blockPoint {p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (x : E p) (y : E q) : E n :=
  WithLp.toLp 2 (fun i => Sum.rec (fun j => x j) (fun j => y j) (e.symm i))

abbrev blockBox {p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Box p) (B : Box q) : Box n where
  lower := blockPoint e A.lower B.lower
  upper := blockPoint e A.upper B.upper
  ordered i := by
    dsimp only [blockPoint, WithLp.toLp_ofLp]
    cases e.symm i with
    | inl j => exact A.ordered j
    | inr j => exact B.ordered j

def productPoint {p q : ℕ} (x : E p) (y : E q) : E (p + q) :=
  blockPoint finSumFinEquiv x y

def productBox {p q : ℕ} (A : Box p) (B : Box q) : Box (p + q) :=
  blockBox finSumFinEquiv A B

def lowerSlice {p q : ℕ} (f : E (p + q) → ℝ) (B : Box q) (x : E p) : ℝ :=
  lowerIntegral (fun y => f (productPoint x y)) B

def upperSlice {p q : ℕ} (f : E (p + q) → ℝ) (B : Box q) (x : E p) : ℝ :=
  upperIntegral (fun y => f (productPoint x y)) B

def lowerSliceReverse {p q : ℕ} (f : E (p + q) → ℝ) (A : Box p) (y : E q) : ℝ :=
  lowerIntegral (fun x => f (productPoint x y)) A

def upperSliceReverse {p q : ℕ} (f : E (p + q) → ℝ) (A : Box p) (y : E q) : ℝ :=
  upperIntegral (fun x => f (productPoint x y)) A
end Specs.D04.C06.DarbouxFubini.Model

namespace Specs.D04.C06.DarbouxFubini
open Specs.D04.C06.DarbouxIntegral.Model Model
abbrev productPointType := {p q : ℕ} → E p → E q → E (p + q)
def productPointValue : productPointType := @Model.productPoint
abbrev productBoxType := {p q : ℕ} → Box p → Box q → Box (p + q)
def productBoxValue : productBoxType := @Model.productBox
abbrev lowerSliceType := {p q : ℕ} → (E (p + q) → ℝ) → Box q → E p → ℝ
def lowerSliceValue : lowerSliceType := @Model.lowerSlice
abbrev upperSliceType := lowerSliceType
def upperSliceValue : upperSliceType := @Model.upperSlice
abbrev lowerSliceReverseType := {p q : ℕ} → (E (p + q) → ℝ) → Box p → E q → ℝ
def lowerSliceReverseValue : lowerSliceReverseType := @Model.lowerSliceReverse
abbrev upperSliceReverseType := lowerSliceReverseType
def upperSliceReverseValue : upperSliceReverseType := @Model.upperSliceReverse

def fubini_lower_upperType : Prop := ∀ {p q} (A : Box p) (B : Box q)
  (f : E (p + q) → ℝ) (hf : Integrable f (productBox A B)),
  ∃ (hl : Integrable (lowerSlice f B) A) (hu : Integrable (upperSlice f B) A),
    integral (lowerSlice f B) A hl = integral f (productBox A B) hf ∧
    integral (upperSlice f B) A hu = integral f (productBox A B) hf

def fubini_reverseType : Prop := ∀ {p q} (A : Box p) (B : Box q)
  (f : E (p + q) → ℝ) (hf : Integrable f (productBox A B)),
  ∃ (hl : Integrable (lowerSliceReverse f A) B) (hu : Integrable (upperSliceReverse f A) B),
    integral (lowerSliceReverse f A) B hl = integral f (productBox A B) hf ∧
    integral (upperSliceReverse f A) B hu = integral f (productBox A B) hf

/-- Any outer function equal to the actual ordinary slice integrals on A. -/
def fubini_slicesType : Prop := ∀ {p q} (A : Box p) (B : Box q)
  (f : E (p + q) → ℝ) (hf : Integrable f (productBox A B))
  (hs : ∀ x ∈ carrier A, Integrable (fun y => f (productPoint x y)) B)
  (g : E p → ℝ)
  (_hg : ∀ x (hx : x ∈ carrier A), g x = integral _ B (hs x hx)),
  ∃ hi : Integrable g A, integral g A hi = integral f (productBox A B) hf

def fubini_slices_reverseType : Prop := ∀ {p q} (A : Box p) (B : Box q)
  (f : E (p + q) → ℝ) (hf : Integrable f (productBox A B))
  (hs : ∀ y ∈ carrier B, Integrable (fun x => f (productPoint x y)) A)
  (g : E q → ℝ)
  (_hg : ∀ y (hy : y ∈ carrier B), g y = integral _ A (hs y hy)),
  ∃ hi : Integrable g B, integral g B hi = integral f (productBox A B) hf
/-- Concrete product content, including zero side lengths. -/
def productBox_contentType : Prop := ∀ {p q} (A : Box p) (B : Box q),
  content (productBox A B) = content A * content B

def productBox_degenerate_iffType : Prop := ∀ {p q} (A : Box p) (B : Box q),
  Degenerate (productBox A B) ↔ Degenerate A ∨ Degenerate B

/-- All five integrals vanish if either factor box is degenerate. -/
def fubini_degenerateType : Prop := ∀ {p q} (A : Box p) (B : Box q)
  (f : E (p + q) → ℝ) (hb : Bounded f (productBox A B)),
  Degenerate A ∨ Degenerate B →
  ∃ hf : Integrable f (productBox A B), integral f (productBox A B) hf = 0 ∧
    (∃ (hl : Integrable (lowerSlice f B) A) (hu : Integrable (upperSlice f B) A),
      integral (lowerSlice f B) A hl = 0 ∧ integral (upperSlice f B) A hu = 0) ∧
    (∃ (hl : Integrable (lowerSliceReverse f A) B) (hu : Integrable (upperSliceReverse f A) B),
      integral (lowerSliceReverse f A) B hl = 0 ∧ integral (upperSliceReverse f A) B hu = 0)

end Specs.D04.C06.DarbouxFubini
