import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DarbouxIntegral
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Chapter 6, d04:06:null and d04:06:cover-facts. Covers are indexed
families, so repetitions are counted. Arbitrary countable (respectively finite)
index types allow an empty cover, including in dimension zero. ENNReal sums
encode sums of nonnegative contents without an implicit summability assumption.
No measure or integration definition occurs in these predicates. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C06.NullCovers.Model
open Specs.D04.C06.DarbouxIntegral.Model

/-- The open box with the same endpoints and content as `Q`. -/
def openCarrier {n : ℕ} (Q : Box n) : Set (E n) :=
  {x | ∀ i, Q.lower i < x i ∧ x i < Q.upper i}

/-- Countable closed box covers with arbitrarily small total content. -/
def Null {n : ℕ} (S : Set (E n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (ι : Type) (_ : Countable ι) (Q : ι → Box n),
    S ⊆ ⋃ i, carrier (Q i) ∧ (∑' i, ENNReal.ofReal (content (Q i))) < ENNReal.ofReal ε

def OpenNull {n : ℕ} (S : Set (E n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (ι : Type) (_ : Countable ι) (Q : ι → Box n),
    S ⊆ ⋃ i, openCarrier (Q i) ∧ (∑' i, ENNReal.ofReal (content (Q i))) < ENNReal.ofReal ε

/-- Finite closed box covers with arbitrarily small total content. -/
def ContentZero {n : ℕ} (S : Set (E n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (ι : Type) (_ : Finite ι) (Q : ι → Box n),
    S ⊆ ⋃ i, carrier (Q i) ∧ (∑' i, ENNReal.ofReal (content (Q i))) < ENNReal.ofReal ε

def OpenContentZero {n : ℕ} (S : Set (E n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (ι : Type) (_ : Finite ι) (Q : ι → Box n),
    S ⊆ ⋃ i, openCarrier (Q i) ∧ (∑' i, ENNReal.ofReal (content (Q i))) < ENNReal.ofReal ε

/-- Relative oscillation; used for bounded `f` and `x ∈ carrier Q`. -/
def localOscillation {n : ℕ} (f : E n → ℝ) (Q : Box n) (x : E n) (r : ℝ) : ℝ :=
  sSup {v | ∃ y ∈ carrier Q ∩ Metric.ball x r,
    ∃ z ∈ carrier Q ∩ Metric.ball x r, v = |f y - f z|}
def oscillation {n : ℕ} (f : E n → ℝ) (Q : Box n) (x : E n) : ℝ :=
  sInf {v | ∃ r > 0, v = localOscillation f Q x r}

/-- A bounded coordinate face, including an internal coordinate slice. -/
def coordinateFace {n : ℕ} (Q : Box n) (i : Fin n) (c : ℝ) : Set (E n) :=
  carrier Q ∩ {x | x i = c}

def rationalUnit : Set (E 1) :=
  {x | x 0 ∈ Set.range (fun q : ℚ => (q : ℝ)) ∧ x 0 ∈ Icc (0 : ℝ) 1}
end Specs.D04.C06.NullCovers.Model

namespace Specs.D04.C06.NullCovers
open Specs.D04.C06.DarbouxIntegral.Model Model
abbrev openCarrierType := {n : ℕ} → Box n → Set (E n)
def openCarrierValue : openCarrierType := @Model.openCarrier
abbrev NullType := {n : ℕ} → Set (E n) → Prop
def NullValue : NullType := @Model.Null
abbrev OpenNullType := NullType
def OpenNullValue : OpenNullType := @Model.OpenNull
abbrev ContentZeroType := NullType
def ContentZeroValue : ContentZeroType := @Model.ContentZero
abbrev OpenContentZeroType := NullType
def OpenContentZeroValue : OpenContentZeroType := @Model.OpenContentZero
abbrev localOscillationType := {n : ℕ} → (E n → ℝ) → Box n → E n → ℝ → ℝ
def localOscillationValue : localOscillationType := @Model.localOscillation
abbrev oscillationType := {n : ℕ} → (E n → ℝ) → Box n → E n → ℝ
def oscillationValue : oscillationType := @Model.oscillation
abbrev coordinateFaceType := {n : ℕ} → Box n → Fin n → ℝ → Set (E n)
def coordinateFaceValue : coordinateFaceType := @Model.coordinateFace
abbrev rationalUnitType := Set (E 1)
def rationalUnitValue : rationalUnitType := Model.rationalUnit

def null_iff_openNullType : Prop := ∀ {n} (S : Set (E n)), Null S ↔ OpenNull S
def contentZero_iff_openContentZeroType : Prop :=
  ∀ {n} (S : Set (E n)), ContentZero S ↔ OpenContentZero S
def null_iUnionType : Prop := ∀ {n} (S : ℕ → Set (E n)),
  (∀ i, Null (S i)) → Null (⋃ i, S i)
def compact_null_contentZeroType : Prop := ∀ {n} (S : Set (E n)),
  IsCompact S → Null S → ContentZero S
def finite_faces_contentZeroType : Prop := ∀ {n} (Q : Box n)
  (F : Finset (Fin n × ℝ)), ContentZero (⋃ p ∈ F, coordinateFace Q p.1 p.2)
def box_not_nullType : Prop := ∀ {n} (Q : Box n), Nondegenerate Q → ¬ Null (carrier Q)
def closure_contentZeroType : Prop := ∀ {n} (S : Set (E n)),
  ContentZero S → ContentZero (closure S)
def finite_box_cover_contentType : Prop := ∀ {n} (Q : Box n) {ι : Type}
  [Fintype ι] (R : ι → Box n), (carrier Q ⊆ ⋃ i, carrier (R i)) →
  content Q ≤ ∑ i, content (R i)
def rationalUnit_boundedType : Prop := Bornology.IsBounded rationalUnit
def rationalUnit_nullType : Prop := Null rationalUnit
def rationalUnit_finite_coverType : Prop := ∀ {ι : Type} [Fintype ι] (R : ι → Box 1),
  rationalUnit ⊆ ⋃ i, carrier (R i) → (1 : ℝ) ≤ ∑ i, content (R i)
def rationalUnit_not_contentZeroType : Prop := ¬ ContentZero rationalUnit
def zero_dim_point_not_nullType : Prop := ¬ Null ({0} : Set (E 0))
end Specs.D04.C06.NullCovers
