import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Singularities
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Logic.Equiv.PartialEquiv

/-!
The canonical sphere and infinity-coordinate definitions for paper.tex:1773–1781.
OnePoint supplies the topology; the implementation proves its concrete neighborhood
formulas. Chart homeomorphisms and the compactness/classification propositions
belong to later goals. A scalar germ on an exterior has no prescribed value at
infinity: holomorphy means existence of a holomorphic extension. For a function
already defined on the sphere, HolomorphicAtInfinityWithValue tests its actual value.
No analyticity certificate or classification theorem is assumed.
-/

open scoped Topology
noncomputable section
namespace D12Complex

/-- The complex plane with one added point, carrying the one-point compactification topology. -/
abbrev RiemannSphere : Type :=
  OnePoint ℂ

/-- The added point at infinity. -/
def sphereInfty : RiemannSphere :=
  OnePoint.infty

/-- The canonical inclusion of the finite plane. -/
def sphereFinite : ℂ → RiemannSphere :=
  fun z => (z : OnePoint ℂ)

/-- The coordinate z, used only away from infinity; the filler at infinity is zero. -/
def finiteCoordinate : RiemannSphere → ℂ :=
  fun p => OnePoint.elim p 0 id

/-- The coordinate w = 1/z, with value zero at infinity; used away from finite zero. -/
def infinityCoordinate : RiemannSphere → ℂ :=
  fun p => OnePoint.elim p 0 (fun z => z⁻¹)

/-- The inverse infinity coordinate: zero maps to infinity and nonzero w maps to 1/w. -/
def infinityParametrization : ℂ → RiemannSphere :=
  fun w => if w = 0 then sphereInfty else sphereFinite w⁻¹

/-- The finite chart, with source the sphere minus infinity and image the whole plane. -/
def finiteChart : PartialEquiv RiemannSphere ℂ :=
  {
  toFun := finiteCoordinate
  invFun := sphereFinite
  source := {sphereInfty}ᶜ
  target := Set.univ
  map_source' := by intro p hp; trivial
  map_target' := by intro z hz; exact OnePoint.coe_ne_infty z
  left_inv' := by
    intro p hp
    induction p using OnePoint.rec with
    | infty => exact False.elim (hp rfl)
    | coe z => rfl
  right_inv' := by intro z hz; rfl
}

/-- The infinity chart, with source the sphere minus finite zero and image the whole plane. -/
def infinityChart : PartialEquiv RiemannSphere ℂ :=
  {
  toFun := infinityCoordinate
  invFun := infinityParametrization
  source := {sphereFinite 0}ᶜ
  target := Set.univ
  map_source' := by intro p hp; trivial
  map_target' := by
    intro w hw
    by_cases h : w = 0
    · simp [infinityParametrization, h, sphereInfty, sphereFinite]
    · simp [infinityParametrization, h, sphereFinite, inv_ne_zero h]
  left_inv' := by
    intro p hp
    induction p using OnePoint.rec with
    | infty => simp [infinityCoordinate, infinityParametrization, sphereInfty]
    | coe z =>
      have hz : z ≠ 0 := by
        intro h; apply hp; exact congrArg sphereFinite h
      simp [infinityCoordinate, infinityParametrization, inv_ne_zero hz, sphereFinite]
  right_inv' := by
    intro w hw
    by_cases h : w = 0
    · simp [infinityParametrization, h, infinityCoordinate, sphereInfty]
    · simp [infinityParametrization, h, infinityCoordinate, sphereFinite]
}

/-- A whole exterior of a disk, with no directional or boundary restriction. -/
def exterior : ℝ → Set ℂ :=
  fun R => {z | R < ‖z‖}

/-- The basic infinity neighborhood consisting of infinity and all finite points with norm > R. -/
def infinityNeighborhood : ℝ → Set RiemannSphere :=
  fun R => {sphereInfty} ∪ sphereFinite '' exterior R

/-- The expression f(1/w). Its filler at w = 0 is ignored by singularity predicates. -/
def reciprocalPullback : (ℂ → ℂ) → ℂ → ℂ :=
  fun f w => f w⁻¹

/-- The expression in the infinity source chart, retaining the specified value at infinity. -/
def infinityPullback : (RiemannSphere → ℂ) → ℂ → ℂ :=
  fun f w => f (infinityParametrization w)

/-- An isolated singularity at infinity, measured at zero in the reciprocal coordinate. -/
def IsolatedSingularityAtInfinity : (ℂ → ℂ) → Prop :=
  fun f => IsolatedSingularityAt (reciprocalPullback f) 0

/-- A holomorphically extendible scalar germ at infinity. -/
def RemovableSingularityAtInfinity : (ℂ → ℂ) → Prop :=
  fun f => RemovableSingularityAt (reciprocalPullback f) 0

/-- A pole of exact positive order m at infinity. -/
def PoleOfOrderAtInfinity : (ℂ → ℂ) → ℕ → Prop :=
  fun f m => PoleOfOrderAt (reciprocalPullback f) 0 m

/-- A pole of some finite positive order at infinity. -/
def PoleAtInfinity : (ℂ → ℂ) → Prop :=
  fun f => PoleAt (reciprocalPullback f) 0

/-- An isolated singularity at infinity that is neither removable nor a pole. -/
def EssentialSingularityAtInfinity : (ℂ → ℂ) → Prop :=
  fun f => EssentialSingularityAt (reciprocalPullback f) 0

/-- Holomorphy of a scalar germ at infinity means that f(1/w) admits a holomorphic extension at zero. -/
def HolomorphicAtInfinity : (ℂ → ℂ) → Prop :=
  fun f => RemovableSingularityAt (reciprocalPullback f) 0

/-- Scalar meromorphy at infinity: the reciprocal expression is removable or has a finite-order pole at zero. -/
def MeromorphicAtInfinity : (ℂ → ℂ) → Prop :=
  fun f => RemovableSingularityAt (reciprocalPullback f) 0 ∨ PoleAt (reciprocalPullback f) 0

/-- Holomorphy for a sphere scalar function with an already specified infinity value, using that value at w = 0. -/
def HolomorphicAtInfinityWithValue : (RiemannSphere → ℂ) → Prop :=
  fun f => ∃ r : ℝ, 0 < r ∧ HolomorphicOn (Metric.ball 0 r) (infinityPullback f)

end D12Complex

namespace Specs.D12Complex.Ch07.Sphere
open _root_.D12Complex

def RiemannSphere_type := Type

def RiemannSphere_value : RiemannSphere_type :=
  OnePoint ℂ

def sphereInfty_type := RiemannSphere

def sphereInfty_value : sphereInfty_type :=
  OnePoint.infty

def sphereFinite_type := ℂ → RiemannSphere

def sphereFinite_value : sphereFinite_type :=
  fun z => (z : OnePoint ℂ)

def finiteCoordinate_type := RiemannSphere → ℂ

def finiteCoordinate_value : finiteCoordinate_type :=
  fun p => OnePoint.elim p 0 id

def infinityCoordinate_type := RiemannSphere → ℂ

def infinityCoordinate_value : infinityCoordinate_type :=
  fun p => OnePoint.elim p 0 (fun z => z⁻¹)

def infinityParametrization_type := ℂ → RiemannSphere

def infinityParametrization_value : infinityParametrization_type :=
  fun w => if w = 0 then sphereInfty else sphereFinite w⁻¹

def finiteChart_type := PartialEquiv RiemannSphere ℂ

def finiteChart_value : finiteChart_type :=
  {
  toFun := finiteCoordinate
  invFun := sphereFinite
  source := {sphereInfty}ᶜ
  target := Set.univ
  map_source' := by intro p hp; trivial
  map_target' := by intro z hz; exact OnePoint.coe_ne_infty z
  left_inv' := by
    intro p hp
    induction p using OnePoint.rec with
    | infty => exact False.elim (hp rfl)
    | coe z => rfl
  right_inv' := by intro z hz; rfl
}

def infinityChart_type := PartialEquiv RiemannSphere ℂ

def infinityChart_value : infinityChart_type :=
  {
  toFun := infinityCoordinate
  invFun := infinityParametrization
  source := {sphereFinite 0}ᶜ
  target := Set.univ
  map_source' := by intro p hp; trivial
  map_target' := by
    intro w hw
    by_cases h : w = 0
    · simp [infinityParametrization, h, sphereInfty, sphereFinite]
    · simp [infinityParametrization, h, sphereFinite, inv_ne_zero h]
  left_inv' := by
    intro p hp
    induction p using OnePoint.rec with
    | infty => simp [infinityCoordinate, infinityParametrization, sphereInfty]
    | coe z =>
      have hz : z ≠ 0 := by
        intro h; apply hp; exact congrArg sphereFinite h
      simp [infinityCoordinate, infinityParametrization, inv_ne_zero hz, sphereFinite]
  right_inv' := by
    intro w hw
    by_cases h : w = 0
    · simp [infinityParametrization, h, infinityCoordinate, sphereInfty]
    · simp [infinityParametrization, h, infinityCoordinate, sphereFinite]
}

def exterior_type := ℝ → Set ℂ

def exterior_value : exterior_type :=
  fun R => {z | R < ‖z‖}

def infinityNeighborhood_type := ℝ → Set RiemannSphere

def infinityNeighborhood_value : infinityNeighborhood_type :=
  fun R => {sphereInfty} ∪ sphereFinite '' exterior R

def reciprocalPullback_type := (ℂ → ℂ) → ℂ → ℂ

def reciprocalPullback_value : reciprocalPullback_type :=
  fun f w => f w⁻¹

def infinityPullback_type := (RiemannSphere → ℂ) → ℂ → ℂ

def infinityPullback_value : infinityPullback_type :=
  fun f w => f (infinityParametrization w)

def IsolatedSingularityAtInfinity_type := (ℂ → ℂ) → Prop

def IsolatedSingularityAtInfinity_value : IsolatedSingularityAtInfinity_type :=
  fun f => IsolatedSingularityAt (reciprocalPullback f) 0

def RemovableSingularityAtInfinity_type := (ℂ → ℂ) → Prop

def RemovableSingularityAtInfinity_value : RemovableSingularityAtInfinity_type :=
  fun f => RemovableSingularityAt (reciprocalPullback f) 0

def PoleOfOrderAtInfinity_type := (ℂ → ℂ) → ℕ → Prop

def PoleOfOrderAtInfinity_value : PoleOfOrderAtInfinity_type :=
  fun f m => PoleOfOrderAt (reciprocalPullback f) 0 m

def PoleAtInfinity_type := (ℂ → ℂ) → Prop

def PoleAtInfinity_value : PoleAtInfinity_type :=
  fun f => PoleAt (reciprocalPullback f) 0

def EssentialSingularityAtInfinity_type := (ℂ → ℂ) → Prop

def EssentialSingularityAtInfinity_value : EssentialSingularityAtInfinity_type :=
  fun f => EssentialSingularityAt (reciprocalPullback f) 0

def HolomorphicAtInfinity_type := (ℂ → ℂ) → Prop

def HolomorphicAtInfinity_value : HolomorphicAtInfinity_type :=
  fun f => RemovableSingularityAt (reciprocalPullback f) 0

def MeromorphicAtInfinity_type := (ℂ → ℂ) → Prop

def MeromorphicAtInfinity_value : MeromorphicAtInfinity_type :=
  fun f => RemovableSingularityAt (reciprocalPullback f) 0 ∨ PoleAt (reciprocalPullback f) 0

def HolomorphicAtInfinityWithValue_type := (RiemannSphere → ℂ) → Prop

def HolomorphicAtInfinityWithValue_value : HolomorphicAtInfinityWithValue_type :=
  fun f => ∃ r : ℝ, 0 < r ∧ HolomorphicOn (Metric.ball 0 r) (infinityPullback f)

def sphereFinite_injective_type : Prop :=
  Function.Injective sphereFinite

def sphere_eq_infty_or_finite_type : Prop :=
  ∀ p : RiemannSphere, p = sphereInfty ∨ ∃ z : ℂ, p = sphereFinite z

def nhds_sphereFinite_type : Prop :=
  ∀ z : ℂ, 𝓝 (sphereFinite z) = Filter.map sphereFinite (𝓝 z)

def mem_nhds_sphereInfty_iff_type : Prop :=
  ∀ U : Set RiemannSphere, U ∈ 𝓝 sphereInfty ↔
  ∃ R : ℝ, 0 < R ∧ infinityNeighborhood R ⊆ U

def finiteCoordinate_sphereFinite_type : Prop :=
  ∀ z : ℂ, finiteCoordinate (sphereFinite z) = z

def infinityCoordinate_sphereFinite_type : Prop :=
  ∀ z : ℂ, infinityCoordinate (sphereFinite z) = z⁻¹

def infinityCoordinate_sphereInfty_type : Prop :=
  infinityCoordinate sphereInfty = 0

def infinityParametrization_zero_type : Prop :=
  infinityParametrization 0 = sphereInfty

def infinityParametrization_ne_zero_type : Prop :=
  ∀ w : ℂ, w ≠ 0 → infinityParametrization w = sphereFinite w⁻¹

def infinityChart_finiteChart_transition_type : Prop :=
  ∀ z : ℂ, z ≠ 0 → infinityChart (finiteChart.symm z) = z⁻¹

def isolatedSingularityAtInfinity_iff_exterior_type : Prop :=
  ∀ f : ℂ → ℂ, IsolatedSingularityAtInfinity f ↔
  ∃ R : ℝ, 0 < R ∧ HolomorphicOn (exterior R) f

def removableSingularityAtInfinity_isolated_type : Prop :=
  ∀ f : ℂ → ℂ, RemovableSingularityAtInfinity f → IsolatedSingularityAtInfinity f

def poleOfOrderAtInfinity_positive_type : Prop :=
  ∀ (f : ℂ → ℂ) (m : ℕ), PoleOfOrderAtInfinity f m → 1 ≤ m

def poleOfOrderAtInfinity_isolated_type : Prop :=
  ∀ (f : ℂ → ℂ) (m : ℕ), PoleOfOrderAtInfinity f m → IsolatedSingularityAtInfinity f

def essentialSingularityAtInfinity_iff_type : Prop :=
  ∀ f : ℂ → ℂ, EssentialSingularityAtInfinity f ↔
  IsolatedSingularityAtInfinity f ∧ ¬ RemovableSingularityAtInfinity f ∧ ¬ PoleAtInfinity f

def holomorphicAtInfinity_iff_removable_type : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicAtInfinity f ↔ RemovableSingularityAtInfinity f

def meromorphicAtInfinity_iff_type : Prop :=
  ∀ f : ℂ → ℂ, MeromorphicAtInfinity f ↔
  RemovableSingularityAtInfinity f ∨ PoleAtInfinity f

end Specs.D12Complex.Ch07.Sphere
