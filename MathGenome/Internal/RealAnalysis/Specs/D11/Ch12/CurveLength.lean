import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDefinition
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Euclidean (L², not supremum-norm) polygonal length. All suprema retain
infinite values. Ambient presentations are bridged to arbitrary interval-domain
functions by `interval_domain_type`. The estimates hold without continuity;
the continuous rectifiable case additionally has a continuous real length function.
The AC length and integral formulas are allocated to RectifiableCurveBridge. -/
open scoped ENNReal

namespace Specs.D11.Ch12
open _root_.D11.Ch12

abbrev curveLength_type := {d : ℕ} → (ℝ → EuclideanSpace ℝ (Fin d)) → ℝ → ℝ → ℝ≥0∞
noncomputable def curveLength_value : curveLength_type :=
  fun γ a b => ⨆ p : IntervalPartition a b, partitionSum γ p

abbrev Rectifiable_type := {d : ℕ} → (ℝ → EuclideanSpace ℝ (Fin d)) → ℝ → ℝ → Prop
def Rectifiable_value : Rectifiable_type := fun γ a b => curveLength_value γ a b < ⊤

abbrev lengthFunction_type := {d : ℕ} → (ℝ → EuclideanSpace ℝ (Fin d)) → ℝ → ℝ → ℝ≥0∞
noncomputable def lengthFunction_value : lengthFunction_type :=
  fun γ a t => curveLength_value γ a t

abbrev realLengthFunction_type := {d : ℕ} → (ℝ → EuclideanSpace ℝ (Fin d)) → ℝ → ℝ → ℝ
noncomputable def realLengthFunction_value : realLengthFunction_type :=
  fun γ a t => (curveLength_value γ a t).toReal

def curve_variation_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) (a b : ℝ),
    curveLength_value γ a b = variation_value γ a b

def coordinate_bound_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) (a b : ℝ) (i : Fin d),
    variation_value (fun t => γ t i) a b ≤ curveLength_value γ a b

def sum_bound_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) (a b : ℝ),
    curveLength_value γ a b ≤ ∑ i : Fin d, variation_value (fun t => γ t i) a b

def rectifiable_iff_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) (a b : ℝ),
    Rectifiable_value γ a b ↔ ∀ i : Fin d, BV_value (fun t => γ t i) a b

def length_self_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) (a : ℝ), curveLength_value γ a a = 0

def length_additivity_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a c b : ℝ}, a ≤ c → c ≤ b →
    curveLength_value γ a b = curveLength_value γ a c + curveLength_value γ c b

def length_monotone_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) (a : ℝ),
    MonotoneOn (lengthFunction_value γ a) (Set.Ici a)

def length_nonnegative_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) (a t : ℝ),
    0 ≤ lengthFunction_value γ a t ∧ 0 ≤ realLengthFunction_value γ a t

def length_subinterval_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a x y b : ℝ},
    Rectifiable_value γ a b → a ≤ x → x ≤ y → y ≤ b →
    realLengthFunction_value γ a y - realLengthFunction_value γ a x =
      (curveLength_value γ x y).toReal

def real_length_monotone_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ},
    Rectifiable_value γ a b → MonotoneOn (realLengthFunction_value γ a) (Set.Icc a b)

def length_variation_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a x y b : ℝ},
    Rectifiable_value γ a b → a ≤ x → x ≤ y → y ≤ b →
    variation_value (realLengthFunction_value γ a) x y = curveLength_value γ x y

def length_continuous_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ},
    a ≤ b → ContinuousOn γ (Set.Icc a b) → Rectifiable_value γ a b →
    ContinuousOn (realLengthFunction_value γ a) (Set.Icc a b)

def curve_congr_type : Prop :=
  ∀ {d : ℕ} {γ δ : ℝ → EuclideanSpace ℝ (Fin d)} {a b : ℝ},
    Set.EqOn γ δ (Set.Icc a b) → curveLength_value γ a b = curveLength_value δ a b

def curve_restriction_type : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) (a b : ℝ),
    eVariationOn (fun t : Set.Icc a b => γ t) Set.univ = curveLength_value γ a b

def curve_interval_domain_type : Prop :=
  ∀ {d : ℕ} (a b : ℝ) (γ : Set.Icc a b → EuclideanSpace ℝ (Fin d)),
    ∃ G : ℝ → EuclideanSpace ℝ (Fin d), (∀ t : Set.Icc a b, G t = γ t) ∧
      curveLength_value G a b = eVariationOn γ Set.univ

end Specs.D11.Ch12
