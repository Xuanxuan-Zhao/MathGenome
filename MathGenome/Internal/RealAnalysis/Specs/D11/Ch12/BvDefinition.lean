import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Normed.Group.Basic

/-! Classical partition variation, paper.tex, Chapter 12, Definition `bv_definition`.
All values are extended nonnegative reals, so infinite variation is retained.
The expected values use an ambient function only through its closed-interval restriction;
`restriction_type` below records the bridge to interval-domain functions.
The normed additive group generality includes both real and complex scalars.
-/
open scoped ENNReal NNReal

namespace D11.Ch12

/-- A finite strictly increasing partition with both endpoints included.
Length zero is allowed, representing a degenerate interval. Values of `point`
after `length` are unused. -/
structure IntervalPartition (a b : ℝ) where
  length : ℕ
  point : ℕ → ℝ
  strictMono : StrictMonoOn point (Set.Iic length)
  start : point 0 = a
  finish : point length = b

variable {E : Type*} [NormedAddCommGroup E]

/-- The sum of the absolute scalar increments along a partition. -/
noncomputable def partitionSum (F : ℝ → E) {a b : ℝ}
    (p : IntervalPartition a b) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range p.length, ‖F (p.point (i + 1)) - F (p.point i)‖ₑ

end D11.Ch12

namespace Specs.D11.Ch12
open _root_.D11.Ch12

abbrev variation_type := {E : Type*} → [NormedAddCommGroup E] → (ℝ → E) → ℝ → ℝ → ℝ≥0∞
noncomputable def variation_value : variation_type :=
  fun F a b => ⨆ p : IntervalPartition a b, partitionSum F p

abbrev variationFunction_type := {E : Type*} → [NormedAddCommGroup E] →
  (ℝ → E) → ℝ → ℝ → ℝ≥0∞
noncomputable def variationFunction_value : variationFunction_type :=
  fun F a x => variation_value F a x

abbrev BV_type := {E : Type*} → [NormedAddCommGroup E] → (ℝ → E) → ℝ → ℝ → Prop
def BV_value : BV_type := fun F a b => variation_value F a b < ⊤

/-- Identifies the literal strict-partition definition with the library's
supremum over nondecreasing chains whose points lie in the interval. -/
def library_bridge_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (a b : ℝ),
    variation_value F a b = eVariationOn F (Set.Icc a b)

def self_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (a : ℝ), variation_value F a a = 0

def additivity_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {a c b : ℝ},
    a ≤ c → c ≤ b → variation_value F a b = variation_value F a c + variation_value F c b

def triangle_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F G : ℝ → E) (a b : ℝ),
    variation_value (fun x => F x + G x) a b ≤ variation_value F a b + variation_value G a b

def sub_triangle_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F G : ℝ → E) (a b : ℝ),
    variation_value (fun x => F x - G x) a b ≤ variation_value F a b + variation_value G a b

def increment_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {x y : ℝ}, x ≤ y →
    ‖F y - F x‖ₑ ≤ variation_value F x y

/-- The ordinary real norm version is used only when variation is finite. -/
def finite_increment_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {x y : ℝ}, x ≤ y → BV_value F x y →
    ‖F y - F x‖ ≤ (variation_value F x y).toReal

def bv_library_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (a b : ℝ),
    BV_value F a b ↔ BoundedVariationOn F (Set.Icc a b)

def congr_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] {F G : ℝ → E} {a b : ℝ},
    Set.EqOn F G (Set.Icc a b) → variation_value F a b = variation_value G a b

def restriction_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (a b : ℝ),
    eVariationOn (fun x : Set.Icc a b => F x) Set.univ = variation_value F a b

/-- Every original interval-domain function is represented, not just a
preselected class of functions admitting an ambient presentation. -/
def interval_domain_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (a b : ℝ) (F : Set.Icc a b → E),
    ∃ G : ℝ → E, (∀ x : Set.Icc a b, G x = F x) ∧
      variation_value G a b = eVariationOn F Set.univ

end Specs.D11.Ch12
