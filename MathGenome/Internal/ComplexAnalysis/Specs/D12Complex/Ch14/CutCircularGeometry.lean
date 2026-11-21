import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularCornerRounding
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! Independent statements for the fixed-cut geometry in paper.tex:2660–2678.
The full obligation is `cut_circular_geometry_type`; the other propositions
record useful proper parts. No Green identity or regularity certificate is a
hypothesis of the full obligation. -/

noncomputable section
open Set Metric MeasureTheory
open scoped Topology Interval

namespace D12Complex.CircularCutGeometry

/-- The literal finite closed-disk deletion, with no geometric certificates. -/
def circularCut (D : Set ℂ) (centers : Finset ℂ) (q : ℂ → ℝ) : Set ℂ :=
  D \ (⋃ c ∈ centers, closedBall c (q c))

/-- A signed, labeled, disjoint display of the actual frontier. Labels refer
to the original finite arrays, so radii and centers cannot be substituted.
The final conjunct is exact angular integration on each deleting circle. -/
def SignedCircularDisplay (D K : Set ℂ) (s : Finset ℂ) (r : ℂ → ℝ)
    (centers : Finset ℂ) (q : ℂ → ℝ) : Prop :=
  ∃ (n : ℕ) (center : Fin n → ℂ) (radius start stop sign : Fin n → ℝ)
    (label : Fin n → (↥s ⊕ ↥centers)),
    (∀ i, 0 < radius i ∧ 0 ≤ start i ∧ start i < stop i ∧ stop i ≤ 2 * Real.pi) ∧
    (∀ i, match label i with
      | Sum.inl c => center i = c ∧ radius i = r c ∧ sign i = 1 ∧
          CircularExhaustion.arcParam (center i) (radius i) ''
            Icc (start i) (stop i) ⊆ frontier D
      | Sum.inr c => center i = c ∧ radius i = q c ∧ sign i = -1 ∧
          CircularExhaustion.arcParam (center i) (radius i) ''
            Ioo (start i) (stop i) ⊆ D) ∧
    frontier K = ⋃ i, CircularExhaustion.arcParam (center i) (radius i) ''
      Icc (start i) (stop i) ∧
    (∀ i j, i ≠ j → Disjoint
      (CircularExhaustion.arcParam (center i) (radius i) '' Ioo (start i) (stop i))
      (CircularExhaustion.arcParam (center j) (radius j) '' Ioo (start j) (stop j))) ∧
    (∀ i, InjOn (CircularExhaustion.arcParam (center i) (radius i))
      (Ioo (start i) (stop i))) ∧
    (∀ i, ∀ t ∈ Ioo (start i) (stop i), ∃ W : Set ℂ,
      IsOpen W ∧ CircularExhaustion.arcParam (center i) (radius i) t ∈ W ∧
      ∀ z ∈ W, z ∈ K ↔ sign i * (‖z - center i‖ ^ 2 - radius i ^ 2) < 0) ∧
    ∀ c : ↥centers,
      MeasurableSet {t : ℝ | CircularExhaustion.arcParam c (q c) t ∈ D} ∧
      ∃ E : Finset ℝ,
        (∀ i, label i = Sum.inr c → start i ∈ E ∧ stop i ∈ E) ∧
        (∀ t ∈ Ioo (0 : ℝ) (2 * Real.pi), t ∉ E →
          (CircularExhaustion.arcParam c (q c) t ∈ D ↔
            ∃ i, label i = Sum.inr c ∧ t ∈ Ioo (start i) (stop i))) ∧
        (∀ i j, label i = Sum.inr c → label j = Sum.inr c → i ≠ j →
          Disjoint (Ioo (start i) (stop i)) (Ioo (start j) (stop j))) ∧
        ∀ f : ℝ → ℝ, Function.Periodic f (2 * Real.pi) →
          IntervalIntegrable f volume 0 (2 * Real.pi) →
          (∀ i, label i = Sum.inr c →
            IntervalIntegrable f volume (start i) (stop i)) →
          (∑ i ∈ Finset.univ.filter (fun i => label i = Sum.inr c),
            ∫ t in start i..stop i, f t) =
          ∫ t in (0 : ℝ)..(2 * Real.pi),
            ({t : ℝ | CircularExhaustion.arcParam c (q c) t ∈ D}).indicator f t

end D12Complex.CircularCutGeometry

namespace Specs.D12Complex.Ch14.CutCircularGeometry
open _root_.D12Complex.CircularCutGeometry _root_.D12Complex.CircularExhaustion

def circularCut_type := Set ℂ → Finset ℂ → (ℂ → ℝ) → Set ℂ
def circularCut_value : circularCut_type := fun D centers q =>
  D \ (⋃ c ∈ centers, closedBall c (q c))

/-- The shared canonical definition has exactly the required literal value.
The implementation proves this equality; the shared definition itself is
reserved in this independent Spec and is not an implementation target. -/
def circularCut_eq_setDiff_type : Prop := circularCut = circularCut_value

/-- Full unchanged obligation. The scale works for every positive radius
function below it, including empty families and artificial smooth corners. -/
def cut_circular_geometry_type : Prop :=
  ∀ (s : Finset ℂ) (r : ℂ → ℝ), GeneralPosition s r →
    ∀ (corners poles : Finset ℂ),
      (↑corners : Set ℂ) ⊆ frontier (diskUnion s r) →
      (∀ p ∈ frontier (diskUnion s r), p ∉ corners →
        SectorChart (diskUnion s r) p Real.pi) →
      (∀ p ∈ corners, ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧
        SectorChart (diskUnion s r) p θ) →
      (↑poles : Set ℂ) ⊆ diskUnion s r →
      ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℂ → ℝ,
        (∀ c ∈ poles ∪ corners, 0 < q c ∧ q c < δ) →
        (∀ c ∈ poles, closedBall c (q c) ⊆ diskUnion s r) ∧
        (∀ c ∈ poles ∪ corners, ∀ d ∈ poles ∪ corners, c ≠ d →
          Disjoint (closedBall c (q c)) (closedBall d (q d))) ∧
        ∃ J : Finset ℂ,
          _root_.D12Complex.CircularCornerRounding.RoundingGeometry
            (circularCut (diskUnion s r) (poles ∪ corners) q) J ∧
          SignedCircularDisplay (diskUnion s r)
            (circularCut (diskUnion s r) (poles ∪ corners) q) s r (poles ∪ corners) q

/-- Generic endpoint-null finite angular additivity, independent of geometry. -/
def finite_angular_interval_additivity_type : Prop :=
  ∀ {ι : Type*} (pieces : Finset ι) (start stop : ι → ℝ) (A B : ℝ), A ≤ B →
    ∀ inside E : Set ℝ, MeasurableSet inside → E.Finite →
      (∀ i ∈ pieces, A ≤ start i ∧ start i < stop i ∧ stop i ≤ B) →
      Set.Pairwise (↑pieces : Set ι)
        (fun i j => Disjoint (Ioo (start i) (stop i)) (Ioo (start j) (stop j))) →
      (∀ t ∈ Ioo A B, t ∉ E →
        (t ∈ inside ↔ ∃ i ∈ pieces, t ∈ Ioo (start i) (stop i))) →
      ∀ f : ℝ → ℝ,
        (∀ i ∈ pieces, IntervalIntegrable f volume (start i) (stop i)) →
        (∑ i ∈ pieces, ∫ t in start i..stop i, f t) =
          ∫ t in A..B, inside.indicator f t

end Specs.D12Complex.Ch14.CutCircularGeometry
