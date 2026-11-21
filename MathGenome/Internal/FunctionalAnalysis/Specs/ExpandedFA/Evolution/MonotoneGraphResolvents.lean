import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.Definitions

/-! Independent specifications for the resolvent portion of
`paper.tex:15926–15956`, `fa2:p3:nonlinear-monotone`.
Graphs in Hilbert coordinates use the canonical real Riesz transport into
H × H′. Monotonicity and maximality are the shared graph predicates.
The resolvent is chosen from surjectivity, without assuming uniqueness;
uniqueness is a theorem. Fixed-parameter results only require surjectivity
at that positive parameter, and therefore apply under the manuscript's
surjectivity hypothesis for every positive parameter. -/
noncomputable section
namespace ExpandedFA.Evolution.MonotoneGraphResolvents.Spec
universe u

def ShiftOntoType := ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
  Set (H × H) → ℝ → Prop

def ShiftOntoValue : ShiftOntoType.{u} :=
  fun H _ _ A t => ∀ x : H, ∃ u a : H, (u, a) ∈ A ∧ x = u + t • a

def ResolventType := ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (A : Set (H × H)) (t : ℝ), ShiftOntoValue H A t → H → H

def ResolventValue : ResolventType.{u} :=
  fun _ _ _ _ _ h x => (h x).choose

def YosidaType := ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (A : Set (H × H)) (t : ℝ), ShiftOntoValue H A t → H → H

def YosidaValue : YosidaType.{u} :=
  fun H _ _ A t h x => t⁻¹ • (x - ResolventValue H A t h x)

/-- The chosen value really is a preimage under I + tA. -/
def ResolventPreimage : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)) (t : ℝ) (honto : ShiftOntoValue H A t) (x : H),
    ∃ a : H, (ResolventValue H A t honto x, a) ∈ A ∧
      x = ResolventValue H A t honto x + t • a

/-- The inverse relation is single valued, including multivalued A. -/
def ResolventSingleValued : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (t : ℝ), 0 < t → ∀ (x u v a b : H),
      (u, a) ∈ A → (v, b) ∈ A → x = u + t • a → x = v + t • b → u = v

/-- Exact identification with (I + tA)⁻¹. -/
def ResolventCharacterization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (t : ℝ), 0 < t → ∀ (honto : ShiftOntoValue H A t) (x u : H),
      ResolventValue H A t honto x = u ↔ ∃ a, (u, a) ∈ A ∧ x = u + t • a

/-- The Yosida value together with its resolvent value belongs to the graph. -/
def YosidaGraph : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)) (t : ℝ), 0 < t →
    ∀ (honto : ShiftOntoValue H A t) (x : H),
      (ResolventValue H A t honto x, YosidaValue H A t honto x) ∈ A

def ResolventIdentity : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)) (t : ℝ), 0 < t →
    ∀ (honto : ShiftOntoValue H A t) (x : H),
      x = ResolventValue H A t honto x + t • YosidaValue H A t honto x

def ResolventFirm : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (t : ℝ), 0 < t → ∀ (honto : ShiftOntoValue H A t) (x y : H),
      ‖ResolventValue H A t honto x - ResolventValue H A t honto y‖ ^ 2 ≤
        inner ℝ (ResolventValue H A t honto x - ResolventValue H A t honto y) (x - y)

def ResolventNonexpansive : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (t : ℝ), 0 < t → ∀ (honto : ShiftOntoValue H A t),
      LipschitzWith 1 (ResolventValue H A t honto)

/-- The sharp bound, valid everywhere, with t⁻¹ a nonnegative real constant. -/
def YosidaLipschitz : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (t : ℝ) (ht : 0 < t) (honto : ShiftOntoValue H A t),
      LipschitzWith ⟨t⁻¹, inv_nonneg.mpr ht.le⟩ (YosidaValue H A t honto)

/-- Monotonicity uses precisely the same Riesz-transported graph predicate. -/
def YosidaMonotone : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (t : ℝ), 0 < t → ∀ (honto : ShiftOntoValue H A t),
      ExpandedFA.Monotone.Spec.MonotoneValue H
        (ExpandedFA.Monotone.Spec.HilbertGraphValue H
          {p : H × H | p.2 = YosidaValue H A t honto p.1})

/-- Maximality among all dual-valued graphs, using actual real Riesz.
Completeness is needed here to test every possible dual-valued extension. -/
def GraphMaximality : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    (∀ t : ℝ, 0 < t → ShiftOntoValue H A t) →
      ExpandedFA.Monotone.Spec.MaximalMonotoneValue H
        (ExpandedFA.Monotone.Spec.HilbertGraphValue H A)

end ExpandedFA.Evolution.MonotoneGraphResolvents.Spec
