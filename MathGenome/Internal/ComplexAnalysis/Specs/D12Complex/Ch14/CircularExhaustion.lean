import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.GeometricBarriers
import Mathlib.Topology.Connected.Basic

/-! Independent statements for the exhaustion and boundary geometry in
paper.tex:2660–2669. Corner estimates and Green identities are allocated elsewhere.
The geometric conclusions below are properties of actual subsets of the plane.
No regularity or existence certificate is included in general position. -/
noncomputable section
open Set Metric
open scoped Topology

namespace D12Complex.CircularExhaustion

/-- The actual finite union of open disks, indexed by their distinct centers. -/
def diskUnion (s : Finset ℂ) (r : ℂ → ℝ) : Set ℂ :=
  ⋃ c ∈ s, ball c (r c)

/-- Positive radii; no external or internal tangencies; no triple circle points.
Distinct centers follow from the finite-set indexing. -/
def GeneralPosition (s : Finset ℂ) (r : ℂ → ℝ) : Prop :=
  (∀ c ∈ s, 0 < r c) ∧
  (∀ c ∈ s, ∀ d ∈ s, c ≠ d →
    dist c d ≠ r c + r d ∧ dist c d ≠ |r c - r d|) ∧
  ∀ c ∈ s, ∀ d ∈ s, ∀ e ∈ s, c ≠ d → c ≠ e → d ≠ e →
    sphere c (r c) ∩ sphere d (r d) ∩ sphere e (r e) = ∅

/-- A genuine circular parametrization, analytic with nonzero velocity for R>0. -/
def arcParam (c : ℂ) (R t : ℝ) : ℂ := c + (R : ℂ) * Complex.exp (t * Complex.I)

/-- A finite covering by closed circular arcs of positive length at most 2π.
The open parts of these parametrizations are injective; a complete circle is
allowed, with its two parametrization endpoints identified. -/
def FiniteCircularArcs (D : Set ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (R a b : Fin n → ℝ),
    (∀ i, 0 < R i ∧ a i < b i ∧ b i - a i ≤ 2 * Real.pi) ∧
    frontier D = ⋃ i, arcParam (c i) (R i) '' Icc (a i) (b i) ∧
    (∀ i, AnalyticOnNhd ℝ (arcParam (c i) (R i)) (Icc (a i) (b i))) ∧
    (∀ i, ∀ t ∈ Icc (a i) (b i), deriv (arcParam (c i) (R i)) t ≠ 0) ∧
    (∀ i, InjOn (arcParam (c i) (R i)) (Ioo (a i) (b i)))

/-- The open angular sector with counterclockwise angle θ, with vertex excluded. -/
def sector (θ : ℝ) : Set ℂ :=
  {w | ∃ (ρ t : ℝ), 0 < ρ ∧ 0 < t ∧ t < θ ∧
    w = (ρ : ℂ) * Complex.exp (t * Complex.I)}

/-- A conformal local sector chart at a boundary point. Its derivative is
explicitly nonzero, so θ is the actual interior angle at the point. -/
def SectorChart (D : Set ℂ) (ξ : ℂ) (θ : ℝ) : Prop :=
  ∃ (U V : Set ℂ) (f g : ℂ → ℂ),
    ξ ∈ U ∧ BiholomorphicPair U V f g ∧ f ξ = 0 ∧ deriv f ξ ≠ 0 ∧
    ∀ z ∈ U, z ∈ D ↔ f z ∈ sector θ

/-- Only finitely many exceptional corners; away from them the angle is π.
At every corner the actual conformal sector angle is strictly between 0 and 2π. -/
def BoundarySectors (D : Set ℂ) : Prop :=
  ∃ corners : Finset ℂ, (↑corners : Set ℂ) ⊆ frontier D ∧
    (∀ ξ ∈ frontier D, ξ ∉ corners → SectorChart D ξ Real.pi) ∧
    ∀ ξ ∈ corners, ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧ SectorChart D ξ θ

/-- The topological and compact-containment properties of one disk stage. -/
def DiskStage (Ω : Set ℂ) (s : Finset ℂ) (r : ℂ → ℝ) : Prop :=
  (∀ c ∈ s, 0 < r c) ∧ IsDomain (diskUnion s r) ∧
    IsCompact (closure (diskUnion s r)) ∧ closure (diskUnion s r) ⊆ Ω

/-- Exhaustion, before the transverse-circle and boundary-geometry requirements. -/
def TopologicalExhaustion (Ω : Set ℂ) (s : ℕ → Finset ℂ)
    (r : ℕ → ℂ → ℝ) : Prop :=
  (∀ j, DiskStage Ω (s j) (r j) ∧
    closure (diskUnion (s j) (r j)) ⊆ diskUnion (s (j + 1)) (r (j + 1))) ∧
  (⋃ j, diskUnion (s j) (r j)) = Ω ∧
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ j, K ⊆ diskUnion (s j) (r j)

/-- All parts of the original exhaustion conclusion, including compact cofinality,
transverse circles, analytic arcs, actual corner charts, cones and regularity. -/
def IsCircularExhaustion (Ω : Set ℂ) (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ) : Prop :=
  (∀ j, GeneralPosition (s j) (r j) ∧ IsDomain (diskUnion (s j) (r j)) ∧
    IsCompact (closure (diskUnion (s j) (r j))) ∧
    closure (diskUnion (s j) (r j)) ⊆ Ω ∧
    closure (diskUnion (s j) (r j)) ⊆ diskUnion (s (j + 1)) (r (j + 1)) ∧
    FiniteCircularArcs (diskUnion (s j) (r j)) ∧
    BoundarySectors (diskUnion (s j) (r j)) ∧
    (∀ ξ ∈ frontier (diskUnion (s j) (r j)),
      LocalExteriorCone (diskUnion (s j) (r j)) ξ) ∧
    (∀ ξ ∈ frontier (diskUnion (s j) (r j)),
      Specs.D12Complex.Ch14.BarrierSqueeze.RegularBoundaryPoint_value
        (diskUnion (s j) (r j)) ξ)) ∧
  (⋃ j, diskUnion (s j) (r j)) = Ω ∧
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ j, K ⊆ diskUnion (s j) (r j)

end D12Complex.CircularExhaustion

namespace Specs.D12Complex.Ch14.CircularExhaustion
open _root_.D12Complex _root_.D12Complex.CircularExhaustion

/-- Full assigned obligation, with the original domain hypothesis. -/
def circular_exhaustion_type : Prop :=
  ∀ Ω : Set ℂ, IsDomain Ω →
    ∃ (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ), IsCircularExhaustion Ω s r

/-- A reusable topological step; general position is a separate obligation. -/
def connected_finite_disk_thickening_type : Prop :=
  ∀ (Ω K : Set ℂ), IsDomain Ω → IsCompact K → K ⊆ Ω →
    ∃ (s : Finset ℂ) (r : ℂ → ℝ),
      (∀ c ∈ s, 0 < r c) ∧ K ⊆ diskUnion s r ∧ IsDomain (diskUnion s r) ∧
      IsCompact (closure (diskUnion s r)) ∧ closure (diskUnion s r) ⊆ Ω

/-- A complete topological exhaustion, a proper part of the assigned result. -/
def finite_disk_exhaustion_type : Prop :=
  ∀ Ω : Set ℂ, IsDomain Ω →
    ∃ (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ), TopologicalExhaustion Ω s r

/-- Recursion preserves an additional property P when compact disk thickenings
can be chosen with P. In particular, this can later carry general position. -/
def exhaustion_of_thickening_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω → ∀ P : Finset ℂ → (ℂ → ℝ) → Prop,
    (∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ (s : Finset ℂ) (r : ℂ → ℝ),
        DiskStage Ω s r ∧ K ⊆ diskUnion s r ∧ P s r) →
    ∃ (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ),
      TopologicalExhaustion Ω s r ∧ ∀ j, P (s j) (r j)

/-- Compact thickening with the full finite-circle general-position conditions. -/
def connected_finite_disk_thickening_generalPosition_type : Prop :=
  ∀ (Ω K : Set ℂ), IsDomain Ω → IsCompact K → K ⊆ Ω →
    ∃ (s : Finset ℂ) (r : ℂ → ℝ),
      DiskStage Ω s r ∧ K ⊆ diskUnion s r ∧ GeneralPosition s r

/-- All exhaustion and arrangement conditions; boundary geometry is separate. -/
def generalPosition_exhaustion_type : Prop :=
  ∀ Ω : Set ℂ, IsDomain Ω →
    ∃ (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ),
      TopologicalExhaustion Ω s r ∧ ∀ j, GeneralPosition (s j) (r j)

/-- The actual local set is the union of its one or two active disks; inactive
disks disappear in a neighborhood. This does not yet assert a sector chart. -/
def local_boundary_disk_model_type : Prop :=
  ∀ (s : Finset ℂ) (r : ℂ → ℝ), GeneralPosition s r →
    ∀ ξ ∈ frontier (diskUnion s r),
      ∃ (t : Finset ℂ) (δ : ℝ), t ⊆ s ∧ t.Nonempty ∧ t.card ≤ 2 ∧ 0 < δ ∧
        (∀ c ∈ t, ξ ∈ sphere c (r c)) ∧
        ∀ z ∈ ball ξ δ, z ∈ diskUnion s r ↔ z ∈ diskUnion t r

/-- The boundary-arrangement obligation, stated independently of the
exhaustion construction. It contains geometric conclusions, not certificates. -/
def boundary_geometry_type : Prop :=
  ∀ (s : Finset ℂ) (r : ℂ → ℝ), GeneralPosition s r →
    FiniteCircularArcs (diskUnion s r) ∧ BoundarySectors (diskUnion s r) ∧
      ∀ ξ ∈ frontier (diskUnion s r), LocalExteriorCone (diskUnion s r) ξ

/-- The exhaustion construction and cone barriers assemble the original
obligation from the arrangement geometry theorem. -/
def circular_exhaustion_of_boundary_geometry_type : Prop :=
  boundary_geometry_type → circular_exhaustion_type

end Specs.D12Complex.Ch14.CircularExhaustion
