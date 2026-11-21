import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent objects for paper.tex, Chapter 6, labels d04:06:boxes and d04:06:criteria, boxes and integral criteria.
Coordinate partitions are exactly the admitted D03 strict endpoint lists. Thus a
singleton coordinate interval has no cells. The product of no coordinate lists
has one cell; this is the dimension-zero evaluation convention. Functions are
ambient functions, used only on their indicated box (so extensions outside the
box have no mathematical role). No integrability or refinement fact is assumed.
The statements at the end specify the full construction and equivalence criteria.
-/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C06.DarbouxIntegral.Model
abbrev E := Specs.D04.C01.EuclideanInterfaces.Model.E
abbrev IntervalPartition := _root_.SingleVariableAnalysis.Riemann.PartitionData

structure Box (n : ℕ) where
  lower : E n
  upper : E n
  ordered : ∀ i, lower i ≤ upper i

def carrier {n : ℕ} (Q : Box n) : Set (E n) :=
  {x | ∀ i, x i ∈ Icc (Q.lower i) (Q.upper i)}
def content {n : ℕ} (Q : Box n) : ℝ := ∏ i, (Q.upper i - Q.lower i)
def Degenerate {n : ℕ} (Q : Box n) : Prop := ∃ i, Q.lower i = Q.upper i
def Nondegenerate {n : ℕ} (Q : Box n) : Prop := ∀ i, Q.lower i < Q.upper i
abbrev Grid {n : ℕ} (Q : Box n) := ∀ i, IntervalPartition (Q.lower i) (Q.upper i)
abbrev CellIndex {n : ℕ} {Q : Box n} (P : Grid Q) := ∀ i, Fin (P i).n

def cellBox {n : ℕ} {Q : Box n} (P : Grid Q) (c : CellIndex P) : Box n where
  lower := WithLp.toLp 2 (fun i => (P i).point (c i).castSucc)
  upper := WithLp.toLp 2 (fun i => (P i).point (c i).succ)
  ordered i := ((P i).strictMono (Fin.castSucc_lt_succ (i := c i))).le

def cell {n : ℕ} {Q : Box n} (P : Grid Q) (c : CellIndex P) : Set (E n) :=
  carrier (cellBox P c)
def cellContent {n : ℕ} {Q : Box n} (P : Grid Q) (c : CellIndex P) : ℝ :=
  content (cellBox P c)
def mesh {n : ℕ} {Q : Box n} (P : Grid Q) : ℝ :=
  (insert 0 (Finset.univ.image (fun c => Metric.diam (cell P c)))).sup'
    (Finset.insert_nonempty _ _) id
abbrev Tagging {n : ℕ} {Q : Box n} (P : Grid Q) := ∀ c, {x // x ∈ cell P c}
def taggedSum {n : ℕ} (f : E n → ℝ) {Q : Box n} (P : Grid Q) (ξ : Tagging P) : ℝ :=
  ∑ c, f (ξ c) * cellContent P c

def Bounded {n : ℕ} (f : E n → ℝ) (Q : Box n) : Prop :=
  BddBelow (f '' carrier Q) ∧ BddAbove (f '' carrier Q)
def cellInfimum {n : ℕ} (f : E n → ℝ) {Q : Box n} (P : Grid Q) (c : CellIndex P) : ℝ :=
  sInf (f '' cell P c)
def cellSupremum {n : ℕ} (f : E n → ℝ) {Q : Box n} (P : Grid Q) (c : CellIndex P) : ℝ :=
  sSup (f '' cell P c)
def lowerSum {n : ℕ} (f : E n → ℝ) {Q : Box n} (P : Grid Q) : ℝ :=
  ∑ c, cellInfimum f P c * cellContent P c
def upperSum {n : ℕ} (f : E n → ℝ) {Q : Box n} (P : Grid Q) : ℝ :=
  ∑ c, cellSupremum f P c * cellContent P c

def lowerIntegral {n : ℕ} (f : E n → ℝ) (Q : Box n) : ℝ :=
  sSup (Set.range (lowerSum f (Q := Q)))
def upperIntegral {n : ℕ} (f : E n → ℝ) (Q : Box n) : ℝ :=
  sInf (Set.range (upperSum f (Q := Q)))
def Integrable {n : ℕ} (f : E n → ℝ) (Q : Box n) : Prop :=
  Bounded f Q ∧ lowerIntegral f Q = upperIntegral f Q
def integral {n : ℕ} (f : E n → ℝ) (Q : Box n) (_h : Integrable f Q) : ℝ :=
  lowerIntegral f Q

def Refines {n : ℕ} {Q : Box n} (R P : Grid Q) : Prop :=
  ∀ i, Specs.SingleVariableAnalysis.Ch08.Partitions.refinesValue (R i) (P i)
def GapCriterion {n : ℕ} (f : E n → ℝ) (Q : Box n) : Prop :=
  ∀ ε > 0, ∃ P : Grid Q, upperSum f P - lowerSum f P < ε
def HasTaggedIntegral {n : ℕ} (f : E n → ℝ) (Q : Box n) (I : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (P : Grid Q) (ξ : Tagging P),
    mesh P < δ → |taggedSum f P ξ - I| < ε

/-- The concrete coordinate identification in dimension one. -/
def scalarPoint (t : ℝ) : E 1 := WithLp.toLp 2 (fun _ => t)
def intervalBox (a b : ℝ) (hab : a ≤ b) : Box 1 :=
  ⟨scalarPoint a, scalarPoint b, fun _ => hab⟩
def intervalGrid {a b : ℝ} {hab : a ≤ b} (P : IntervalPartition a b) :
    Grid (intervalBox a b hab) := fun _ => P
/-- Scalar tags become vector tags by the concrete coordinate map. -/
def intervalTags {a b : ℝ} {hab : a ≤ b} (P : IntervalPartition a b)
    (ζ : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P) :
    Tagging (intervalGrid (hab := hab) P) := fun c =>
  ⟨scalarPoint (ζ (c 0)), fun i => by fin_cases i; exact (ζ (c 0)).property⟩
end Specs.D04.C06.DarbouxIntegral.Model

namespace Specs.D04.C06.DarbouxIntegral
open Model

abbrev BoxType := ℕ → Type
def BoxValue : BoxType := Model.Box
abbrev carrierType := {n : ℕ} → Box n → Set (E n)
abbrev contentType := {n : ℕ} → Box n → ℝ
abbrev DegenerateType := {n : ℕ} → Box n → Prop
abbrev NondegenerateType := {n : ℕ} → Box n → Prop
abbrev GridType := {n : ℕ} → Box n → Type
abbrev CellIndexType := {n : ℕ} → {Q : Box n} → Grid Q → Type
abbrev cellBoxType := {n : ℕ} → {Q : Box n} → (P : Grid Q) → CellIndex P → Box n
abbrev cellType := {n : ℕ} → {Q : Box n} → (P : Grid Q) → CellIndex P → Set (E n)
abbrev cellContentType := {n : ℕ} → {Q : Box n} → (P : Grid Q) → CellIndex P → ℝ
abbrev meshType := {n : ℕ} → {Q : Box n} → Grid Q → ℝ
abbrev TaggingType := {n : ℕ} → {Q : Box n} → Grid Q → Type
abbrev taggedSumType := {n : ℕ} → (E n → ℝ) → {Q : Box n} → (P : Grid Q) → Tagging P → ℝ
abbrev BoundedType := {n : ℕ} → (E n → ℝ) → Box n → Prop
abbrev cellInfimumType := {n : ℕ} → (E n → ℝ) → {Q : Box n} → (P : Grid Q) → CellIndex P → ℝ
abbrev cellSupremumType := {n : ℕ} → (E n → ℝ) → {Q : Box n} → (P : Grid Q) → CellIndex P → ℝ
abbrev lowerSumType := {n : ℕ} → (E n → ℝ) → {Q : Box n} → Grid Q → ℝ
abbrev upperSumType := {n : ℕ} → (E n → ℝ) → {Q : Box n} → Grid Q → ℝ
abbrev lowerIntegralType := {n : ℕ} → (E n → ℝ) → Box n → ℝ
abbrev upperIntegralType := {n : ℕ} → (E n → ℝ) → Box n → ℝ
abbrev IntegrableType := {n : ℕ} → (E n → ℝ) → Box n → Prop
abbrev integralType := {n : ℕ} → (f : E n → ℝ) → (Q : Box n) → Integrable f Q → ℝ
abbrev RefinesType := {n : ℕ} → {Q : Box n} → Grid Q → Grid Q → Prop
abbrev GapCriterionType := {n : ℕ} → (E n → ℝ) → Box n → Prop
abbrev HasTaggedIntegralType := {n : ℕ} → (E n → ℝ) → Box n → ℝ → Prop
abbrev scalarPointType := ℝ → E 1
abbrev intervalBoxType := (a b : ℝ) → a ≤ b → Box 1
abbrev intervalGridType := {a b : ℝ} → {hab : a ≤ b} → IntervalPartition a b → Grid (intervalBox a b hab)
abbrev intervalTagsType := {a b : ℝ} → {hab : a ≤ b} → (P : IntervalPartition a b) → Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P → Tagging (intervalGrid (hab := hab) P)

-- Full statements, independent of the candidate implementation.
def content_nonnegType : Prop := ∀ {n} (Q : Box n), 0 ≤ content Q
def content_degenerateType : Prop := ∀ {n} (Q : Box n), Degenerate Q → content Q = 0
def grid_existsType : Prop := ∀ {n} (Q : Box n), Nonempty (Grid Q)
def cell_subsetType : Prop := ∀ {n} {Q : Box n} (P : Grid Q) c, cell P c ⊆ carrier Q
def cells_coverType : Prop := ∀ {n} (Q : Box n), Nondegenerate Q →
  ∀ P : Grid Q, carrier Q = ⋃ c, cell P c
def content_partitionType : Prop := ∀ {n} {Q : Box n} (P : Grid Q),
  ∑ c, cellContent P c = content Q
def tags_existType : Prop := ∀ {n} {Q : Box n} (P : Grid Q), Nonempty (Tagging P)
def tagged_boundsType : Prop := ∀ {n} (f : E n → ℝ) {Q : Box n}, Bounded f Q →
  ∀ (P : Grid Q) (ξ : Tagging P), lowerSum f P ≤ taggedSum f P ξ ∧
    taggedSum f P ξ ≤ upperSum f P

def common_refinementType : Prop := ∀ {n} {Q : Box n} (P R : Grid Q),
  ∃ T : Grid Q, Refines T P ∧ Refines T R
def lower_refinementType : Prop := ∀ {n} (f : E n → ℝ) {Q : Box n}, Bounded f Q →
  ∀ P R : Grid Q, Refines R P → lowerSum f P ≤ lowerSum f R
def upper_refinementType : Prop := ∀ {n} (f : E n → ℝ) {Q : Box n}, Bounded f Q →
  ∀ P R : Grid Q, Refines R P → upperSum f R ≤ upperSum f P
def lower_le_upperType : Prop := ∀ {n} (f : E n → ℝ) {Q : Box n}, Bounded f Q →
  ∀ P R : Grid Q, lowerSum f P ≤ upperSum f R
def integral_boundsType : Prop := ∀ {n} (f : E n → ℝ) (Q : Box n)
  (h : Integrable f Q) (P : Grid Q), lowerSum f P ≤ integral f Q h ∧
    integral f Q h ≤ upperSum f P

def degenerate_sumsType : Prop := ∀ {n} (f : E n → ℝ) {Q : Box n}, Degenerate Q →
  ∀ (P : Grid Q) (ξ : Tagging P),
    taggedSum f P ξ = 0 ∧ lowerSum f P = 0 ∧ upperSum f P = 0
def degenerate_integralsType : Prop := ∀ {n} (f : E n → ℝ) (Q : Box n),
  Degenerate Q → lowerIntegral f Q = 0 ∧ upperIntegral f Q = 0
/-- All functions on R^0 are bounded; there are no extra hypotheses here. -/
def zero_dimensionType : Prop := ∀ (Q : Box 0) (f : E 0 → ℝ),
  content Q = 1 ∧ Integrable f Q ∧ lowerIntegral f Q = f 0 ∧ upperIntegral f Q = f 0 ∧
    ∀ (P : Grid Q) (ξ : Tagging P), taggedSum f P ξ = f 0 ∧
      lowerSum f P = f 0 ∧ upperSum f P = f 0

def arbitrarily_fineType : Prop := ∀ {n} (Q : Box n), Nondegenerate Q →
  ∀ δ > 0, ∃ P : Grid Q, mesh P < δ

def integrable_iff_gapType : Prop := ∀ {n} (f : E n → ℝ) (Q : Box n), Bounded f Q →
  (Integrable f Q ↔ GapCriterion f Q)
def equivalent_criteriaType : Prop := ∀ {n} (f : E n → ℝ) (Q : Box n),
  Bounded f Q → Nondegenerate Q →
  (Integrable f Q ↔ GapCriterion f Q) ∧
  (Integrable f Q ↔ ∃ I, HasTaggedIntegral f Q I) ∧
  ∀ I, HasTaggedIntegral f Q I → ∃ h : Integrable f Q, I = integral f Q h

/-- The scalar bridge includes every grid, not just the image of a chosen list. -/
def scalar_grid_surjectiveType : Prop := ∀ a b (hab : a ≤ b)
  (P : Grid (intervalBox a b hab)), P = intervalGrid (P 0)
def scalar_sumsType : Prop := ∀ (f : E 1 → ℝ) a b (hab : a ≤ b)
  (hf : Bounded f (intervalBox a b hab)) (P : IntervalPartition a b),
  ∃ hb : Specs.SingleVariableAnalysis.Ch08.DarbouxSums.boundedOnIntervalValue
    (fun t => f (scalarPoint t)) a b,
  lowerSum f (intervalGrid (hab := hab) P) =
    Specs.SingleVariableAnalysis.Ch08.DarbouxSums.lowerSumValue (fun t => f (scalarPoint t)) P hb ∧
  upperSum f (intervalGrid (hab := hab) P) =
    Specs.SingleVariableAnalysis.Ch08.DarbouxSums.upperSumValue (fun t => f (scalarPoint t)) P hb

def scalar_integralType : Prop := ∀ (f : E 1 → ℝ) a b (hab : a ≤ b),
  (Integrable f (intervalBox a b hab) ↔
    Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue (fun t => f (scalarPoint t)) a b) ∧
  ∀ h : Integrable f (intervalBox a b hab),
    ∃ hs : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue
      (fun t => f (scalarPoint t)) a b,
    integral f (intervalBox a b hab) h =
      Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue (fun t => f (scalarPoint t)) hs

def scalar_tags_surjectiveType : Prop := ∀ {a b : ℝ} {hab : a ≤ b}
  (P : IntervalPartition a b) (ξ : Tagging (intervalGrid (hab := hab) P)),
  ∃ ζ : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P,
    ξ = intervalTags (hab := hab) P ζ

def scalar_taggedSumType : Prop := ∀ (f : E 1 → ℝ) {a b : ℝ} {hab : a ≤ b}
  (P : IntervalPartition a b) (ζ : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P),
  taggedSum f (intervalGrid (hab := hab) P) (intervalTags P ζ) =
    Specs.SingleVariableAnalysis.Ch08.Partitions.sumValue P ζ (fun t => f (scalarPoint t))

def scalar_meshType : Prop := ∀ {a b : ℝ} {hab : a ≤ b} (P : IntervalPartition a b),
  mesh (intervalGrid (hab := hab) P) = Specs.SingleVariableAnalysis.Ch08.Partitions.meshValue P

def zero_box_uniqueType : Prop := Subsingleton (Box 0)
def scalar_box_representationType : Prop := ∀ Q : Box 1,
  Q = intervalBox (Q.lower 0) (Q.upper 0) (Q.ordered 0)

end Specs.D04.C06.DarbouxIntegral
