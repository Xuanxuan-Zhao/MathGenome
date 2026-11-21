import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact

/-!
Independent specification of paper.tex, d10:17:projection (lines 2836–2870).
`EuclideanSpace ℝ (Fin m)` has the Euclidean inner-product norm, including m = 0.
The chosen map has codomain K with its subspace topology. Its construction uses
compact minimization, and its nearest-point and retraction properties below are
obligations, not assumed certificates. No interior or dimension condition on K
is imposed.
-/

namespace D10Topology.Ch17.MetricProjectionData

/-- A nearest point is a member of K minimizing the actual Euclidean distance. -/
def NearestPoint {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (x p : EuclideanSpace ℝ (Fin m)) : Prop :=
  p ∈ K ∧ ∀ q ∈ K, ‖x - p‖ ≤ ‖x - q‖

/-- Choose a distance minimizer on a nonempty compact set. Convexity will
ensure uniqueness and nonexpansiveness, but is not needed to make this choice. -/
noncomputable def projection {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (hK : IsCompact K) (hne : K.Nonempty) (x : EuclideanSpace ℝ (Fin m)) : K :=
  let h := hK.exists_isMinOn hne
    (f := fun p => ‖x - p‖) (continuous_const.sub continuous_id).norm.continuousOn
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

end D10Topology.Ch17.MetricProjectionData

namespace Specs.D10Topology.Ch17.MetricProjection
open _root_.D10Topology.Ch17.MetricProjectionData

def nearestPointType := {m : ℕ} → Set (EuclideanSpace ℝ (Fin m)) →
  EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → Prop
def nearestPointValue : nearestPointType := @NearestPoint

def projectionType := {m : ℕ} → (K : Set (EuclideanSpace ℝ (Fin m))) →
  IsCompact K → K.Nonempty → EuclideanSpace ℝ (Fin m) → K
noncomputable def projectionValue : projectionType := @projection

def projection_nearest : Prop :=
  ∀ {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (x : EuclideanSpace ℝ (Fin m)), NearestPoint K x (projection K hK hne x)

def nearest_unique : Prop :=
  ∀ {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))),
    IsCompact K → K.Nonempty → Convex ℝ K →
    ∀ x : EuclideanSpace ℝ (Fin m), ∃! p, NearestPoint K x p

def nearest_iff_eq_projection : Prop :=
  ∀ {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (hK : IsCompact K) (hne : K.Nonempty), Convex ℝ K →
    ∀ x p : EuclideanSpace ℝ (Fin m),
      NearestPoint K x p ↔ p = (projection K hK hne x : EuclideanSpace ℝ (Fin m))

def projection_fixes : Prop :=
  ∀ {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (hK : IsCompact K) (hne : K.Nonempty), Convex ℝ K →
    ∀ x : K, projection K hK hne x = x

def projection_nonexpansive : Prop :=
  ∀ {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (hK : IsCompact K) (hne : K.Nonempty), Convex ℝ K →
    ∀ x y : EuclideanSpace ℝ (Fin m),
      ‖(projection K hK hne x : EuclideanSpace ℝ (Fin m)) - projection K hK hne y‖ ≤
        ‖x - y‖

def projection_continuous_retraction : Prop :=
  ∀ {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (hK : IsCompact K) (hne : K.Nonempty), Convex ℝ K →
    Continuous (projection K hK hne) ∧
      Function.LeftInverse (projection K hK hne) (Subtype.val : K → EuclideanSpace ℝ (Fin m))

end Specs.D10Topology.Ch17.MetricProjection
