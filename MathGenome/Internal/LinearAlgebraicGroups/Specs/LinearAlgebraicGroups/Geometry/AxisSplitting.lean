import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Geometry.Projection

/-! Specification of axes, flat strips and the equivariant minimum-set splitting. -/

open Set unitInterval
open scoped Topology

namespace LinearAlgebraicGroups.Geometry.AxisSplittingSpec

open CAT0SpacesSpec ProjectionSpec

variable {X : Type*} [MetricSpace X]

def isAxisType := ∀ {X : Type*} [MetricSpace X], (X ≃ᵢ X) → ℝ → (ℝ → X) → Prop

def isAxisValue (a : X ≃ᵢ X) (L : ℝ) (c : ℝ → X) : Prop :=
  Isometry c ∧ ∀ t : ℝ, a (c t) = c (t + L)

def axesAlignedType := ∀ {X : Type*} [MetricSpace X], (ℝ → X) → (ℝ → X) → Prop

def axesAlignedValue (c d : ℝ → X) : Prop :=
  isNearestPointValue (range d) (c 0) (d 0)

def axisBusemannType := ∀ {X : Type*} [MetricSpace X], (ℝ → X) → X → ℝ

noncomputable def axisBusemannValue (c : ℝ → X) (x : X) : ℝ :=
  ⨅ t : ℝ, dist x (c t) - t

def axisCrossSectionType := ∀ {X : Type*} [MetricSpace X], (X ≃ᵢ X) → (ℝ → X) → Set X

def axisCrossSectionValue (a : X ≃ᵢ X) (c : ℝ → X) : Set X :=
  {x | x ∈ minsetValue a ∧ axisBusemannValue c x = 0}

def translationLengthEqType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {a : X ≃ᵢ X} {L : ℝ} {c : ℝ → X},
    isAxisValue a L c → 0 < L → translationLengthValue a = L

def axisMemMinsetType :=
  ∀ {X : Type*} [MetricSpace X] {a : X ≃ᵢ X} {c : ℝ → X},
    isAxisValue a (translationLengthValue a) c → 0 < translationLengthValue a →
      ∀ t : ℝ, c t ∈ minsetValue a

def existsAxisType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X →
    ∀ {a : X ≃ᵢ X}, 0 < translationLengthValue a →
      ∀ {x : X}, x ∈ minsetValue a →
        ∃ c : ℝ → X, isAxisValue a (translationLengthValue a) c ∧ c 0 = x

def axisDistOffsetType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {a : X ≃ᵢ X} {L : ℝ}, 0 < L →
    ∀ {c d : ℝ → X}, isAxisValue a L c → isAxisValue a L d →
      ∀ r s t : ℝ, dist (c s) (d (s + r)) = dist (c t) (d (t + r))

def axisNearestPointsType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {a : X ≃ᵢ X} {L : ℝ}, 0 < L →
    ∀ {c d : ℝ → X}, isAxisValue a L c → isAxisValue a L d → axesAlignedValue c d →
      ∀ t : ℝ,
        isNearestPointValue (range d) (c t) (d t) ∧ isNearestPointValue (range c) (d t) (c t)

def alignedAxisDistSqType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {a : X ≃ᵢ X} {L : ℝ}, 0 < L →
    ∀ {c d : ℝ → X}, isAxisValue a L c → isAxisValue a L d → axesAlignedValue c d →
      ∀ s t : ℝ, dist (c s) (d t) ^ 2 = dist (c 0) (d 0) ^ 2 + (s - t) ^ 2

def alignedAxisStripDistSqType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {a : X ≃ᵢ X} {L : ℝ}, 0 < L →
    ∀ {c d : ℝ → X}, isAxisValue a L c → isAxisValue a L d → axesAlignedValue c d →
      ∀ (p : ∀ t, geodesicSegmentValue (c t) (d t)) (s t : ℝ) (u v : I),
        dist ((p s).val u) ((p t).val v) ^ 2 =
          ((u : ℝ) - (v : ℝ)) ^ 2 * dist (c 0) (d 0) ^ 2 + (s - t) ^ 2

def existsAxisFlatStripType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {a : X ≃ᵢ X} {L : ℝ}, 0 < L →
    ∀ {c d : ℝ → X}, isAxisValue a L c → isAxisValue a L d → axesAlignedValue c d →
      let D := dist (c 0) (d 0)
      ∃ F : euclideanProductValue ℝ (Set.Icc 0 D) → X,
        Isometry F ∧
        (∀ t : ℝ, F (WithLp.toLp 2 (t, ⟨0, le_rfl, dist_nonneg⟩)) = c t ∧
          F (WithLp.toLp 2 (t, ⟨D, dist_nonneg, le_rfl⟩)) = d t) ∧
        ∀ p, a (F p) = F (WithLp.toLp 2 (p.fst + L, p.snd))

def axisBusemannSelfType :=
  ∀ {X : Type*} [MetricSpace X] {c : ℝ → X}, Isometry c →
    ∀ s : ℝ, axisBusemannValue c (c s) = -s

def tendstoAxisBusemannType :=
  ∀ {X : Type*} [MetricSpace X] {c : ℝ → X}, Isometry c →
    ∀ x : X, Filter.Tendsto (fun t : ℝ => dist x (c t) - t) Filter.atTop (𝓝 (axisBusemannValue c x))

def lipschitzWithAxisBusemannType :=
  ∀ {X : Type*} [MetricSpace X] {c : ℝ → X}, Isometry c →
    LipschitzWith 1 (axisBusemannValue c)

def axisBusemannEqOfAlignedType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {a : X ≃ᵢ X} {L : ℝ}, 0 < L →
    ∀ {c d : ℝ → X}, isAxisValue a L c → isAxisValue a L d → axesAlignedValue c d →
      axisBusemannValue c = axisBusemannValue d

def axisBusemannEqAddType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {a : X ≃ᵢ X} {L : ℝ}, 0 < L →
    ∀ {c d : ℝ → X}, isAxisValue a L c → isAxisValue a L d → ∀ x : X,
      axisBusemannValue c x = axisBusemannValue d x + axisBusemannValue c (d 0)

def axesAlignedIffAxisBusemannEqType :=
  ∀ {X : Type*} [MetricSpace X], cat0Value X → ∀ {a : X ≃ᵢ X} {L : ℝ}, 0 < L →
    ∀ {c d : ℝ → X}, isAxisValue a L c → isAxisValue a L d →
      (axesAlignedValue c d ↔ axisBusemannValue c = axisBusemannValue d)

def axisMinsetSplittingType :=
  ∀ {X : Type*} [MetricSpace X] [CompleteSpace X], cat0Value X →
    ∀ a : X ≃ᵢ X, isSemisimpleValue a → 0 < translationLengthValue a →
      ∃ c : ℝ → X, isAxisValue a (translationLengthValue a) c ∧
        IsClosed (axisCrossSectionValue a c) ∧ geodesicConvexValue (axisCrossSectionValue a c) ∧
        cat0Value (axisCrossSectionValue a c) ∧ CompleteSpace (axisCrossSectionValue a c) ∧
        ∃ e : euclideanProductValue (axisCrossSectionValue a c) ℝ ≃ᵢ minsetValue a,
          (∀ z : axisCrossSectionValue a c, (e (WithLp.toLp 2 (z, 0)) : X) = z) ∧
          (∀ p, axisBusemannValue c (e p) = -p.snd) ∧
          (∀ z : axisCrossSectionValue a c,
            isAxisValue a (translationLengthValue a) (fun t => (e (WithLp.toLp 2 (z, t)) : X))) ∧
          (∀ p, a (e p) = (e (WithLp.toLp 2 (p.fst, p.snd + translationLengthValue a)) : X)) ∧
          ∀ b : X ≃ᵢ X, Function.Commute a b →
            ∃ (f : axisCrossSectionValue a c ≃ᵢ axisCrossSectionValue a c) (τ : ℝ),
              ∀ p, b (e p) = (e (WithLp.toLp 2 (f p.fst, p.snd + τ)) : X)

end LinearAlgebraicGroups.Geometry.AxisSplittingSpec
