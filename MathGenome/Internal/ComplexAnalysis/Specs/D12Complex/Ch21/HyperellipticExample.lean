import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.MapsMultiplicity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Squarefree.Basic

/-!
Independent contracts for the square-free example, paper.tex:3720–3755.
The literal smooth affine curve and its compact connected completion are
constructed from the original hypotheses. The completion conclusions include
actual infinity charts, exact infinity fibers and projection orders.
-/
noncomputable section
open Set Polynomial Filter
open scoped Topology
set_option linter.unusedVariables false

namespace D12Complex.HyperellipticExample.FiniteGeometry
/-- The literal affine zero set, with the topology induced from ℂ². -/
abbrev AffineCurve (P : Polynomial ℂ) := {q : ℂ × ℂ // q.2 ^ 2 = P.eval q.1}

/-- A genuine coordinate projection chart with holomorphic inverse coordinates. -/
def GoodCoordinateChart {P : Polynomial ℂ} (e : OpenPartialHomeomorph (AffineCurve P) ℂ) : Prop :=
  ((∀ x, e x = x.val.1) ∨ (∀ x, e x = x.val.2)) ∧
    HolomorphicOn e.target (fun z => (e.symm z).val.1) ∧
    HolomorphicOn e.target (fun z => (e.symm z).val.2)

end D12Complex.HyperellipticExample.FiniteGeometry

namespace Specs.D12Complex.Ch21.HyperellipticExample
open _root_.D12Complex _root_.D12Complex.HyperellipticExample.FiniteGeometry

def AffineCurve_type := Polynomial ℂ → Type

def AffineCurve_value : AffineCurve_type :=
  fun P => {q : ℂ × ℂ // q.2 ^ 2 = P.eval q.1}

def GoodCoordinateChart_type := {P : Polynomial ℂ} →
  OpenPartialHomeomorph (AffineCurve P) ℂ → Prop

def GoodCoordinateChart_value : GoodCoordinateChart_type := fun e =>
  ((∀ x, e x = x.val.1) ∨ (∀ x, e x = x.val.2)) ∧
    HolomorphicOn e.target (fun z => (e.symm z).val.1) ∧
    HolomorphicOn e.target (fun z => (e.symm z).val.2)

def squarefree_derivative_ne_zero_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P)
    (a : ℂ) (ha : P.eval a = 0),
  P.derivative.eval a ≠ 0

def polynomial_holomorphic_type : Prop :=
  ∀ (P : Polynomial ℂ),
  HolomorphicOn Set.univ P.eval

def affine_graph_at_nonzero_type : Prop :=
  ∀ (P : Polynomial ℂ) (a b : ℂ)
    (h : b ^ 2 = P.eval a) (hb : b ≠ 0),
  ∃ (U V : Set ℂ) (f : ℂ → ℂ),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ b ∈ V ∧
      HolomorphicOn U f ∧ f a = b ∧ MapsTo f U V ∧
      ∀ z ∈ U, ∀ w ∈ V, w ^ 2 = P.eval z ↔ w = f z

def polynomial_inverse_at_root_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P)
    (a : ℂ) (ha : P.eval a = 0),
  ∃ (U V : Set ℂ) (h : ℂ → ℂ),
      a ∈ U ∧ 0 ∈ V ∧ BiholomorphicPair U V P.eval h ∧ h 0 = a ∧
      HasDerivAt h (1 / P.derivative.eval a) 0

def affine_graph_at_root_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P)
    (a : ℂ) (ha : P.eval a = 0),
  ∃ (U W : Set ℂ) (f : ℂ → ℂ),
      IsOpen U ∧ IsOpen W ∧ a ∈ U ∧ 0 ∈ W ∧
      HolomorphicOn W f ∧ f 0 = a ∧ MapsTo f W U ∧
      (∀ w ∈ W, ∀ z ∈ U, w ^ 2 = P.eval z ↔ z = f w) ∧
      analyticOrderAt (fun w => f w - a) 0 = (2 : ℕ∞)

def FiniteGeometry_local_parameter_z_type : Prop :=
  ∀ (P : Polynomial ℂ) (x : AffineCurve P) (hx : x.val.2 ≠ 0),
  ∃ e : OpenPartialHomeomorph (AffineCurve P) ℂ,
      x ∈ e.source ∧ (∀ y, e y = y.val.1) ∧
      HolomorphicOn e.target (fun z => (e.symm z).val.2)

def FiniteGeometry_local_parameter_w_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P)
    (a : ℂ) (ha : P.eval a = 0),
  ∃ e : OpenPartialHomeomorph (AffineCurve P) ℂ,
      (⟨(a, 0), by simpa using ha.symm⟩ : AffineCurve P) ∈ e.source ∧
      (∀ y, e y = y.val.2) ∧
      HolomorphicOn e.target (fun w => (e.symm w).val.1) ∧
      analyticOrderAt (fun w => (e.symm w).val.1 - a) 0 = (2 : ℕ∞)

def FiniteGeometry_coordinate_charts_compatible_type : Prop :=
  ∀ {P : Polynomial ℂ}
    (e f : Surfaces.ComplexChart (AffineCurve P))
    (he : GoodCoordinateChart e.val) (hf : GoodCoordinateChart f.val),
  Surfaces.CompatibleCharts e f

def FiniteGeometry_exists_good_chart_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P) (x : AffineCurve P),
  ∃ e : OpenPartialHomeomorph (AffineCurve P) ℂ,
      x ∈ e.source ∧ IsDomain e.target ∧ GoodCoordinateChart e

def FiniteGeometry_affine_complex_atlas_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P),
  T2Space (AffineCurve P) ∧ SecondCountableTopology (AffineCurve P) ∧
      ∃ A : Set (Surfaces.ComplexChart (AffineCurve P)), Surfaces.IsAtlas A ∧
        ∀ e ∈ A, GoodCoordinateChart e.val

def FiniteGeometry_good_chart_immersion_type : Prop :=
  ∀ {P : Polynomial ℂ}
    (e : OpenPartialHomeomorph (AffineCurve P) ℂ) (he : GoodCoordinateChart e),
  ∀ t ∈ e.target, ∃ v : ℂ × ℂ, v ≠ 0 ∧
      HasDerivAt (fun t => (e.symm t).val) v t

def FiniteGeometry_smooth_affine_curve_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P),
  T2Space (AffineCurve P) ∧ SecondCountableTopology (AffineCurve P) ∧
      ∃ A : Set (Surfaces.ComplexChart (AffineCurve P)), Surfaces.IsAtlas A ∧
        ∀ e ∈ A, GoodCoordinateChart e.val ∧
          ∀ t ∈ e.val.target, ∃ v : ℂ × ℂ, v ≠ 0 ∧
            HasDerivAt (fun t => (e.val.symm t).val) v t

def FiniteGeometry_finite_root_chart_order_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P)
    (a : ℂ) (ha : P.eval a = 0)
    (S : Surfaces.RiemannSurface (AffineCurve P))
    (hS : ∀ e ∈ S.atlas, GoodCoordinateChart e.val),
  let x : AffineCurve P := ⟨(a, 0), by simpa using ha.symm⟩
    ∃ e : Surfaces.ComplexChart (AffineCurve P),
      e ∈ Surfaces.maximalAtlas S.atlas ∧ x ∈ e.val.source ∧ e.val x = 0 ∧
      (∀ y, e.val y = y.val.2) ∧
      analyticOrderAt (fun w => (e.val.symm w).val.1 - a) 0 = (2 : ℕ∞)

def InfinityCharts_reverse_eval_eq_type : Prop :=
  ∀ (p : Polynomial ℂ) (t : ℂ) (ht : t ≠ 0),
  p.reverse.eval t = t ^ p.natDegree * p.eval t⁻¹

def InfinityCharts_reverse_eval_zero_type : Prop :=
  ∀ (p : Polynomial ℂ),
  p.reverse.eval 0 = p.leadingCoeff

def InfinityCharts_exists_local_nonzero_sqrt_type : Prop :=
  ∀ (p : Polynomial ℂ) (hp : p ≠ 0)
    (c : ℂ) (hc : c ^ 2 = p.leadingCoeff),
  ∃ r : ℝ, ∃ h : ℂ → ℂ, 0 < r ∧ HolomorphicOn (Metric.ball 0 r) h ∧
      h 0 = c ∧ ∀ t ∈ Metric.ball 0 r, h t ≠ 0 ∧ (h t)^2 = p.reverse.eval t

def InfinityCharts_exists_even_local_sqrt_type : Prop :=
  ∀ (p : Polynomial ℂ) (hp : p ≠ 0),
  ∃ r : ℝ, ∃ u : ℂ → ℂ, 0 < r ∧ HolomorphicOn (Metric.ball 0 r) u ∧
      (∀ t : ℂ, u (-t) = u t) ∧
      (u 0)^2 = p.leadingCoeff ∧
      ∀ t ∈ Metric.ball 0 r, u t ≠ 0 ∧ (u t)^2 = p.reverse.eval (t^2)

def InfinityCharts_even_substitution_type : Prop :=
  ∀ (p : Polynomial ℂ) (g : ℕ) (hd : p.natDegree = 2*g+2)
    (t v : ℂ) (ht : t ≠ 0),
  v^2 = p.reverse.eval t ↔ (v / t^(g+1))^2 = p.eval t⁻¹

def InfinityCharts_odd_substitution_type : Prop :=
  ∀ (p : Polynomial ℂ) (g : ℕ) (hd : p.natDegree = 2*g+1)
    (t u : ℂ) (ht : t ≠ 0),
  u^2 = p.reverse.eval (t^2) ↔ (u / t^(2*g+1))^2 = p.eval (t^2)⁻¹

def InfinityCharts_even_sheet_values_type : Prop :=
  ∀ (p : Polynomial ℂ) (g : ℕ) (hd : p.natDegree = 2*g+2)
    (t h : ℂ) (ht : t ≠ 0) (hh : h^2 = p.reverse.eval t) (w : ℂ),
  w^2 = p.eval t⁻¹ ↔ w = h / t^(g+1) ∨ w = -(h / t^(g+1))

def InfinityCharts_odd_opposite_parameter_type : Prop :=
  ∀ (g : ℕ) (u : ℂ → ℂ) (hu : ∀ t, u (-t) = u t) (t : ℂ),
  u (-t) / (-t)^(2*g+1) = -(u t / t^(2*g+1))

def InfinityCharts_odd_parameter_injective_type : Prop :=
  ∀ (g : ℕ) (u : ℂ → ℂ) (U : Set ℂ)
    (hu : ∀ t, u (-t) = u t) (hne : ∀ t ∈ U, u t ≠ 0),
  Set.InjOn (fun t : ℂ => ((t^2)⁻¹, u t / t^(2*g+1))) (U \ {0})

def InfinityCharts_odd_recover_parameter_type : Prop :=
  ∀ (g : ℕ) (t a : ℂ) (ht : t ≠ 0) (ha : a ≠ 0),
  a * ((t^2)⁻¹)^g / (a / t^(2*g+1)) = t

def InfinityCharts_odd_sheet_values_type : Prop :=
  ∀ (p : Polynomial ℂ) (g : ℕ) (hd : p.natDegree = 2*g+1)
    (u : ℂ → ℂ) (hu : ∀ t, u (-t) = u t) (t : ℂ) (ht : t ≠ 0)
    (hroot : (u t)^2 = p.reverse.eval (t^2)) (w : ℂ),
  w^2 = p.eval (t^2)⁻¹ ↔
      w = u t / t^(2*g+1) ∨ w = u (-t) / (-t)^(2*g+1)

def InfinityCharts_odd_parameter_covers_type : Prop :=
  ∀ (p : Polynomial ℂ) (g : ℕ) (hd : p.natDegree = 2*g+1)
    (r : ℝ) (hr : 0 < r) (u : ℂ → ℂ) (hu : ∀ t, u (-t) = u t)
    (hroot : ∀ t ∈ Metric.ball 0 r, (u t)^2 = p.reverse.eval (t^2))
    (z w : ℂ) (hz : z ≠ 0) (hnorm : ‖z⁻¹‖ < r^2) (hw : w^2 = p.eval z),
  ∃ t ∈ Metric.ball 0 r, t ≠ 0 ∧
      ((t^2)⁻¹,u t / t^(2*g+1)) = (z,w)

def InfinityCharts_even_parameter_injective_type : Prop :=
  ∀ (g : ℕ) (h : ℂ → ℂ),
  Function.Injective (fun t : ℂ => (t⁻¹,h t / t^(g+1)))

def InfinityCharts_opposite_sheet_values_ne_type : Prop :=
  ∀ (g : ℕ) (t a : ℂ) (ht : t ≠ 0) (ha : a ≠ 0),
  a / t^(g+1) ≠ -(a / t^(g+1))

def InfinityCharts_parameter_coordinate_holomorphic_type : Prop :=
  ∀ (r : ℝ) (u : ℂ → ℂ)
    (hu : HolomorphicOn (Metric.ball 0 r) u) (n : ℕ),
  HolomorphicOn (Metric.ball 0 r \ {0}) (fun t => u t / t^n)

def InfinityCharts_inverse_power_holomorphic_type : Prop :=
  ∀ (r : ℝ) (n : ℕ),
  HolomorphicOn (Metric.ball 0 r \ {0}) (fun t : ℂ => (t^n)⁻¹)

def quadraticPolynomial_irreducible_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P)
    (hd : 1 ≤ P.natDegree),
  Irreducible ((X : Polynomial (Polynomial ℂ)) ^ 2 - C P)

def isCompact_affine_core_type : Prop :=
  ∀ (P : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K),
  IsCompact {q : ℂ × ℂ | q.1 ∈ K ∧ q.2 ^ 2 = P.eval q.1}

def FiniteGeometry_affine_connected_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P) (hd : 1 ≤ P.natDegree),
  ConnectedSpace (AffineCurve P)

def FiniteGeometry_exists_affine_surface_type : Prop :=
  ∀ (P : Polynomial ℂ) (hP : Squarefree P) (hd : 1 ≤ P.natDegree),
  ∃ S : Surfaces.RiemannSurface (AffineCurve P),
      (∀ e ∈ S.atlas, GoodCoordinateChart e.val) ∧
      Surfaces.ScalarHolomorphic S (fun x => x.val.1) ∧
      Surfaces.ScalarHolomorphic S (fun x => x.val.2)

end Specs.D12Complex.Ch21.HyperellipticExample

namespace D12Complex.HyperellipticExample
open FiniteGeometry Surfaces

/-- A compact complex completion of the literal affine zero set. All topology,
regularity and multiplicity assertions are output fields of the construction. -/
structure Compactification (P : Polynomial ℂ) (J : Type)
    [TopologicalSpace (AffineCurve P ⊕ J)] where
  affineSurface : RiemannSurface (AffineCurve P)
  good_affine : ∀ e ∈ affineSurface.atlas, GoodCoordinateChart e.val
  surface : RiemannSurface (AffineCurve P ⊕ J)
  compact : CompactSpace (AffineCurve P ⊕ J)
  old_open : Topology.IsOpenEmbedding (Sum.inl : AffineCurve P → AffineCurve P ⊕ J)
  old_dense : DenseRange (Sum.inl : AffineCurve P → AffineCurve P ⊕ J)
  old_holomorphic : HolomorphicMap affineSurface surface Sum.inl
  old_locallyBiholomorphic : ∀ x, LocallyBiholomorphicAt affineSurface surface Sum.inl x
  Z : AffineCurve P ⊕ J → RiemannSphere
  W : AffineCurve P ⊕ J → RiemannSphere
  z_old : ∀ x, Z (Sum.inl x) = sphereFinite x.val.1
  w_old : ∀ x, W (Sum.inl x) = sphereFinite x.val.2
  z_infinity : ∀ j, Z (Sum.inr j) = sphereInfty
  w_infinity : ∀ j, W (Sum.inr j) = sphereInfty
  z_meromorphic : ScalarMeromorphic surface Z
  w_meromorphic : ScalarMeromorphic surface W
  z_holomorphic : SphereValuedHolomorphic surface Z
  infinity_fiber : Z ⁻¹' {sphereInfty} = range (Sum.inr : J → AffineCurve P ⊕ J)
  finite_root_order : ∀ (a : ℂ) (ha : P.eval a = 0),
    let x : AffineCurve P := ⟨(a, 0), by simpa using ha.symm⟩
    ∃ e : ComplexChart (AffineCurve P ⊕ J),
      e ∈ maximalAtlas surface.atlas ∧ Sum.inl x ∈ e.val.source ∧
      e.val (Sum.inl x) = 0 ∧
      analyticOrderAt (fun t => finiteCoordinate (Z (e.val.symm t)) - a) 0 = 2

end D12Complex.HyperellipticExample

namespace Specs.D12Complex.Ch21.HyperellipticExample
open _root_.D12Complex _root_.D12Complex.HyperellipticExample
open _root_.D12Complex.HyperellipticExample.FiniteGeometry _root_.D12Complex.Surfaces

/-- The two actual infinity centers, with full disk coordinates and orders in
all compatible source charts. The displayed root retains degree two (g=0). -/
def even_compact_completion_type : Prop :=
  ∀ (P : Polynomial ℂ) (g : ℕ), Squarefree P → P.natDegree = 2*g+2 →
    ∃ top : TopologicalSpace (AffineCurve P ⊕ Bool),
      letI := top
      ∃ c : Compactification P Bool, ∃ (r : ℝ) (h : ℂ → ℂ)
        (chart : Bool → ComplexChart (AffineCurve P ⊕ Bool)),
        0 < r ∧ HolomorphicOn (Metric.ball 0 r) h ∧
        (∀ t ∈ Metric.ball 0 r, h t ≠ 0 ∧ h t ^ 2 = P.reverse.eval t) ∧
        h 0 ^ 2 = P.leadingCoeff ∧
        Disjoint (chart false).val.source (chart true).val.source ∧
        ∀ b : Bool,
          chart b ∈ c.surface.atlas ∧ Sum.inr b ∈ (chart b).val.source ∧
          (chart b).val.target = Metric.ball 0 r ∧
          (chart b).val (Sum.inr b) = 0 ∧
          (∀ t ∈ Metric.ball 0 r,
            c.Z ((chart b).val.symm t) = infinityParametrization t ∧
            c.W ((chart b).val.symm t) =
              if t = 0 then sphereInfty else
                sphereFinite ((if b then -h t else h t) / t^(g+1))) ∧
          (∀ e ∈ maximalAtlas c.surface.atlas, Sum.inr b ∈ e.val.source →
            analyticOrderAt (fun t => infinityCoordinate (c.Z (e.val.symm t)))
              (e.val (Sum.inr b)) = 1)

/-- The single odd-degree infinity center, with the even nonvanishing root,
full disk parameter and order two. This includes degree one (g=0). -/
def odd_compact_completion_type : Prop :=
  ∀ (P : Polynomial ℂ) (g : ℕ), Squarefree P → P.natDegree = 2*g+1 →
    ∃ top : TopologicalSpace (AffineCurve P ⊕ Unit),
      letI := top
      ∃ c : Compactification P Unit, ∃ (r : ℝ) (u : ℂ → ℂ)
        (chart : ComplexChart (AffineCurve P ⊕ Unit)),
        0 < r ∧ HolomorphicOn (Metric.ball 0 r) u ∧
        (∀ t : ℂ, u (-t) = u t) ∧
        (∀ t ∈ Metric.ball 0 r, u t ≠ 0 ∧ u t ^ 2 = P.reverse.eval (t^2)) ∧
        u 0 ^ 2 = P.leadingCoeff ∧
        chart ∈ c.surface.atlas ∧ Sum.inr () ∈ chart.val.source ∧
        chart.val.target = Metric.ball 0 r ∧ chart.val (Sum.inr ()) = 0 ∧
        (∀ t ∈ Metric.ball 0 r,
          c.Z (chart.val.symm t) = infinityParametrization (t^2) ∧
          c.W (chart.val.symm t) =
            if t = 0 then sphereInfty else sphereFinite (u t / t^(2*g+1))) ∧
        (∀ e ∈ maximalAtlas c.surface.atlas, Sum.inr () ∈ e.val.source →
          analyticOrderAt (fun t => infinityCoordinate (c.Z (e.val.symm t)))
            (e.val (Sum.inr ())) = 2)

end Specs.D12Complex.Ch21.HyperellipticExample

namespace Specs.D12Complex.Ch21.HyperellipticExample
open _root_.D12Complex.HyperellipticExample _root_.D12Complex.HyperellipticExample.FiniteGeometry

/-- Every positive degree is covered by the parity constructions above. -/
def compact_completion_type : Prop :=
  ∀ (P : Polynomial ℂ), Squarefree P → 1 ≤ P.natDegree →
    ∃ J : Type, Finite J ∧ ∃ top : TopologicalSpace (AffineCurve P ⊕ J),
      letI := top
      Nonempty (Compactification P J)

end Specs.D12Complex.Ch21.HyperellipticExample
