import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LeviCivita
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Independent statements for paper.tex 3299–3357. All velocities lie in the
canonical intrinsic tangent fibers. One-sided derivatives are used at endpoints
and corners; no rank or endpoint-fixing assumption is imposed on a variation.
No first-variation or differential identity is assumed in the data. -/
set_option autoImplicit false

namespace P202.FirstVariationData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

/-- Coordinate smoothness on a closed segment: actual ambient smooth extensions
are required only for coordinate values, on a germ of the parameter strip.
The total map outside the strip is irrelevant. -/
def SmoothVariationOn (S : SmoothManifold n kind M) (F : ℝ × ℝ → M)
    (ε a b : ℝ) : Prop :=
  let D := Ioo (-ε) ε ×ˢ Icc a b
  ContinuousOn F D ∧ ∀ z ∈ D,
    ∃ e ∈ S.smoothStructure.val, F z ∈ e.source ∧
      ∃ x : ℝ × ℝ → Euclidean n,
        ContDiffAt ℝ (⊤ : ℕ∞) x z ∧ x z = (e (F z)).val ∧
          (fun w => (e (F w)).val) =ᶠ[𝓝[D] z] x

/-- The endpoint velocity is the intrinsic one-sided derivative of the slice.
On singleton intervals the choice has no effect on any asserted formula. -/
noncomputable def segmentVelocity (S : SmoothManifold n kind M)
    (F : ℝ × ℝ → M) (a b : ℝ) (t : ℝ) : TangentSpace S (F (0,t)) := by
  classical
  exact if h : ∃ v, HasVelocityWithinAt S (fun r => F (0,r)) (Icc a b) t v then
    Classical.choose h else 0

noncomputable def variationField (S : SmoothManifold n kind M)
    (F : ℝ × ℝ → M) (t : ℝ) : TangentSpace S (F (0,t)) :=
  velocity S (fun s => F (s,t)) 0

noncomputable def unitVelocity (g : RiemannianMetric S) (F : ℝ × ℝ → M)
    (a b t : ℝ) : TangentSpace S (F (0,t)) :=
  (tangentNorm g (F (0,t)) (segmentVelocity S F a b t))⁻¹ • segmentVelocity S F a b t

/-- These are precisely the existing speed integrands for length and energy,
now applied to the slices of a variation. -/
noncomputable def variedEnergy (g : RiemannianMetric S) (F : ℝ × ℝ → M)
    (a b s : ℝ) : ℝ := (1/2 : ℝ) * ∫ t in a..b, speed g (fun r => F (s,r)) t ^ 2

noncomputable def variedLength (g : RiemannianMetric S) (F : ℝ × ℝ → M)
    (a b s : ℝ) : ℝ := ∫ t in a..b, speed g (fun r => F (s,r)) t

/-- Pair any field along the base curve with the actual variation field. -/
noncomputable def variationPairing (g : RiemannianMetric S) (F : ℝ × ℝ → M)
    (W : (t : ℝ) → TangentSpace S (F (0,t))) (t : ℝ) : ℝ :=
  pairing g (F (0,t)) (variationField S F t) (W t)

noncomputable def energyFirstVariation (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : ℝ × ℝ → M) (a b : ℝ) : ℝ :=
  variationPairing g F (segmentVelocity S F a b) b -
  variationPairing g F (segmentVelocity S F a b) a -
  ∫ t in a..b, variationPairing g F
    (covariantDerivativeWithin C (fun r => F (0,r))
      (segmentVelocity S F a b) (Icc a b)) t

noncomputable def lengthFirstVariation (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : ℝ × ℝ → M) (a b : ℝ) : ℝ :=
  variationPairing g F (unitVelocity g F a b) b -
  variationPairing g F (unitVelocity g F a b) a -
  ∫ t in a..b, variationPairing g F
    (covariantDerivativeWithin C (fun r => F (0,r))
      (unitVelocity g F a b) (Icc a b)) t

/-- Energy corner term with the full left-minus-right velocities. -/
noncomputable def energyCorner (g : RiemannianMetric S) (F : ℝ × ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (j : Fin k) : ℝ :=
  let t := node j.succ.castSucc
  variationPairing g F (fun r =>
    segmentVelocity S F (node j.castSucc.castSucc) (node j.castSucc.succ) r -
    segmentVelocity S F (node j.succ.castSucc) (node j.succ.succ) r) t

/-- Length corner term with the left-minus-right unit velocities. -/
noncomputable def lengthCorner (g : RiemannianMetric S) (F : ℝ × ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (j : Fin k) : ℝ :=
  let t := node j.succ.castSucc
  variationPairing g F (fun r =>
    unitVelocity g F (node j.castSucc.castSucc) (node j.castSucc.succ) r -
    unitVelocity g F (node j.succ.castSucc) (node j.succ.succ) r) t

end P202.FirstVariationData

namespace P202Specs.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  P202.MetricData P202.CurveData P202.ConnectionData P202.LeviCivitaData
  P202.FirstVariationData
open Set
universe u

def length_sq_le_energyType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    {a b : ℝ} (c : PiecewiseC1Curve S a b),
    length g c ^ 2 ≤ 2 * (b - a) * energy g c

/-- Constancy almost everywhere includes the one-sided constant-speed pieces
whose total-function velocities may be undefined at the finitely many joins. -/
def constant_speed_equalityType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) (v : ℝ),
    (∀ᵐ t ∂MeasureTheory.volume.restrict (Ioc a b), speed g c t = v) →
    length g c ^ 2 = 2 * (b - a) * energy g c

def equality_iff_constant_speedType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    {a b : ℝ} (c : PiecewiseC1Curve S a b), a < b →
    ContinuousOn (speed g c) (Icc a b) →
    (length g c ^ 2 = 2 * (b - a) * energy g c ↔
      ∃ v : ℝ, ∀ t ∈ Icc a b, speed g c t = v)

def degenerateType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (a : ℝ) (c : PiecewiseC1Curve S a a), length g c = 0 ∧ energy g c = 0


/-- Energy first variation on any smooth segment, with moving endpoints.
There is no speed, immersion, nonconstancy, or fixed-endpoint hypothesis. -/
def first_variation_energyType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : ℝ × ℝ → M) (ε a b : ℝ), 0 < ε → a ≤ b →
    SmoothVariationOn S F ε a b →
    HasDerivAt (variedEnergy g F a b) (energyFirstVariation g C F a b) 0

/-- Length first variation requires positive one-sided speed on the whole
compact base segment; the nearby curves need no assumed speed bound. -/
def first_variation_lengthType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : ℝ × ℝ → M) (ε a b : ℝ), 0 < ε → a ≤ b →
    SmoothVariationOn S F ε a b →
    (∀ t ∈ Icc a b, 0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) →
    HasDerivAt (variedLength g F a b) (lengthFirstVariation g C F a b) 0

/-- Segmentwise energy formula, including the explicit full-velocity jumps.
A common map F ensures that the variation values at a join agree. -/
def piecewise_energyType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : ℝ × ℝ → M) (ε : ℝ), 0 < ε →
    ∀ {k : ℕ} (node : Fin (k+2) → ℝ), StrictMono node →
    (∀ i : Fin (k+1), SmoothVariationOn S F ε (node i.castSucc) (node i.succ)) →
    HasDerivAt (variedEnergy g F (node 0) (node (Fin.last (k+1))))
      (variationPairing g F
          (segmentVelocity S F (node (Fin.last k).castSucc) (node (Fin.last k).succ))
          (node (Fin.last (k+1))) -
       variationPairing g F (segmentVelocity S F (node 0) (node (Fin.succ 0))) (node 0) +
       (∑ j : Fin k, energyCorner g F node j) -
       (∑ i : Fin (k+1), ∫ t in node i.castSucc..node i.succ,
          variationPairing g F
            (P202.CurveConnectionData.covariantDerivativeWithin C (fun r => F (0,r))
              (segmentVelocity S F (node i.castSucc) (node i.succ))
              (Icc (node i.castSucc) (node i.succ))) t)) 0

/-- Segmentwise length formula, including the unit-velocity jumps. -/
def piecewise_lengthType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : ℝ × ℝ → M) (ε : ℝ), 0 < ε →
    ∀ {k : ℕ} (node : Fin (k+2) → ℝ), StrictMono node →
    (∀ i : Fin (k+1), SmoothVariationOn S F ε (node i.castSucc) (node i.succ)) →
    (∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      0 < tangentNorm g (F (0,t)) (segmentVelocity S F (node i.castSucc) (node i.succ) t)) →
    HasDerivAt (variedLength g F (node 0) (node (Fin.last (k+1))))
      (variationPairing g F
          (unitVelocity g F (node (Fin.last k).castSucc) (node (Fin.last k).succ))
          (node (Fin.last (k+1))) -
       variationPairing g F (unitVelocity g F (node 0) (node (Fin.succ 0))) (node 0) +
       (∑ j : Fin k, lengthCorner g F node j) -
       (∑ i : Fin (k+1), ∫ t in node i.castSucc..node i.succ,
          variationPairing g F
            (P202.CurveConnectionData.covariantDerivativeWithin C (fun r => F (0,r))
              (unitVelocity g F (node i.castSucc) (node i.succ))
              (Icc (node i.castSucc) (node i.succ))) t)) 0

end P202Specs.Geometry.FirstVariation
