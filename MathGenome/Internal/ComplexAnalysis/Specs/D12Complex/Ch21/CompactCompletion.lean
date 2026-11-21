import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.CyclicParameters
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.AlgebraicGrowth
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.MapsMultiplicity
import Mathlib.Topology.Compactness.Compact

/-! Independent contracts for the finite-branch completion in
paper.tex:3689–3718.  The carrier adds exactly one point per actual connected
component of each punctured algebraic restriction.  The preceding cyclic
parameter theorem identifies these components with the monodromy cycles.
No topology, extension, compactness, or regularity at a missing center is an
input to the main theorem.
-/

noncomputable section
open Set
open scoped Topology

namespace D12Complex.CompactCompletion
open D12Complex.AlgebraicCovering D12Complex.CyclicParameters
open D12Complex.Ch20.PuncturedDiskLoops D12Complex.Ch20.PunctureCompletion
open D12Complex.Surfaces

/-- All finite exceptional values and the separate value at infinity. -/
abbrev Puncture (P : Polynomial (Polynomial ℂ)) := exceptionalSet P ⊕ Unit

/-- The original base variable expressed in a local punctured base disk. -/
def baseMap (P : Polynomial (Polynomial ℂ)) : Puncture P → ℂ → ℂ
  | Sum.inl c => fun u => (c : ℂ) + u
  | Sum.inr _ => fun u => u⁻¹

/-- Radii are chosen as part of the construction.  Admissibility excludes
every other exceptional value on the actual punctured base disks. -/
structure Radii (P : Polynomial (Polynomial ℂ)) where
  radius : Puncture P → ℝ
  positive : ∀ a, 0 < radius a
  admissible : ∀ a, ∀ u : Disk (radius a), baseMap P a u ∈ baseSet P

/-- The local covering is the canonical pullback of the literal old curve. -/
abbrev LocalCover (P : Polynomial (Polynomial ℂ)) (R : Radii P) (a : Puncture P) :=
  CurveOver P (baseMap P a) (R.radius a)

/-- The labels are actual local components, including cycles of length one. -/
abbrev End (P : Polynomial (Polynomial ℂ)) (R : Radii P) :=
  (a : Puncture P) × ConnectedComponents (LocalCover P R a)

abbrev LocalComponent (P : Polynomial (Polynomial ℂ)) (R : Radii P) (j : End P R) :=
  {x : LocalCover P R j.1 // ConnectedComponents.mk x = j.2}

/-- Retain the original algebraic point rather than an abstract equivalent sheet. -/
def localPoint (P : Polynomial (Polynomial ℂ)) (R : Radii P) (j : End P R)
    (x : LocalComponent P R j) : Curve P := x.val.val.2

/-- Each model is an output with its actual fiber cardinal and power projection.
The values of `root` at zero are irrelevant here: holomorphy is asserted only
on the punctured parameter disk. -/
structure LocalModel (P : Polynomial (Polynomial ℂ)) (R : Radii P) (j : End P R) where
  anchor : Disk (R.radius j.1)
  degree : ℕ
  positive : 0 < degree
  degree_eq_card : degree = Nat.card
    {x : diskProjection P (baseMap P j.1) (R.radius j.1) ⁻¹' {anchor} //
      ConnectedComponents.mk (x : LocalCover P R j.1) = j.2}
  parameter : Disk (rootRadius (R.radius j.1) degree) ≃ₜ LocalComponent P R j
  componentSurface : RiemannSurface (LocalComponent P R j)
  parameterSurface : RiemannSurface (Disk (rootRadius (R.radius j.1) degree))
  component_coordinates : ∀ e ∈ componentSurface.atlas, ∀ x ∈ e.val.source,
    e.val x = (diskProjection P (baseMap P j.1) (R.radius j.1) x : ℂ)
  parameter_coordinates : ∀ e ∈ parameterSurface.atlas, ∀ t ∈ e.val.source,
    e.val t = (t : ℂ)
  parameter_holomorphic : HolomorphicMap parameterSurface componentSurface parameter
  inverse_holomorphic : HolomorphicMap componentSurface parameterSurface parameter.symm
  projection_eq : ∀ t,
    diskProjection P (baseMap P j.1) (R.radius j.1) (parameter t) =
      powerMap (R.positive j.1) positive t
  root : ℂ → ℂ
  holomorphic : HolomorphicOn
    (puncturedDisk 0 (rootRadius (R.radius j.1) degree)) root
  root_eq : ∀ t : Disk (rootRadius (R.radius j.1) degree),
    root t = (localPoint P R j (parameter t)).val.2

/-- The underlying set fixes all old points and exactly the required centers. -/
abbrev Carrier (P : Polynomial (Polynomial ℂ)) (R : Radii P) := Curve P ⊕ End P R

/-- The extended first coordinate has its forced value at every new center. -/
def baseCoordinate (P : Polynomial (Polynomial ℂ)) (R : Radii P) :
    Carrier P R → RiemannSphere
  | Sum.inl x => sphereFinite x.val.1
  | Sum.inr ⟨Sum.inl c, _⟩ => sphereFinite c
  | Sum.inr ⟨Sum.inr _, _⟩ => sphereInfty

/-- The full completed component that must be the source of its added chart. -/
def endChartSource (P : Polynomial (Polynomial ℂ)) (R : Radii P) (j : End P R) :
    Set (Carrier P R) :=
  Sum.inl '' Set.range (localPoint P R j) ∪ {Sum.inr j}

end D12Complex.CompactCompletion

namespace Specs.D12Complex.Ch21.CompactCompletion
open _root_.D12Complex _root_.D12Complex.AlgebraicCovering
open _root_.D12Complex.CompactCompletion _root_.D12Complex.Surfaces
open _root_.D12Complex.Ch20.PuncturedDiskLoops
open _root_.D12Complex.Ch20.PunctureCompletion

def continuous_fiber_eval_type : Prop :=
  ∀ P : Polynomial (Polynomial ℂ),
    Continuous (fun x : ℂ × ℂ => (fiber P x.1).eval x.2)

def exists_uniform_root_bound_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) {K : Set ℂ}, IsCompact K →
    (∀ z ∈ K, P.leadingCoeff.eval z ≠ 0) →
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ w : ℂ, (fiber P z).eval w = 0 → ‖w‖ ≤ R

def isCompact_affine_preimage_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) {K : Set ℂ}, IsCompact K →
    (∀ z ∈ K, P.leadingCoeff.eval z ≠ 0) →
    IsCompact {x : ℂ × ℂ | x.1 ∈ K ∧ (fiber P x.1).eval x.2 = 0}

def isCompact_curve_preimage_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) {K : Set ℂ}, IsCompact K →
    K ⊆ baseSet P → IsCompact {x : Curve P | x.val.1 ∈ K}

def isCompact_projection_preimage_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) {K : Set (Base P)}, IsCompact K →
    IsCompact (projection P ⁻¹' K)

def finite_fiber_roots_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) {a : ℂ}, P.leadingCoeff.eval a ≠ 0 →
    Set.Finite {w : ℂ | (fiber P a).eval w = 0}

def exists_scalarMeromorphic_disk_extension_type : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ {W : ℂ → ℂ},
    HolomorphicOn (puncturedDisk 0 r) W → MeromorphicAt W 0 →
    ∃ F : ℂ → RiemannSphere,
      ScalarMeromorphicOn (Metric.ball 0 r) F ∧
      ∀ t ∈ puncturedDisk 0 r, F t = sphereFinite (W t)

def exists_admissible_radii_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d → Nonempty (Radii P)

def holomorphic_baseMap_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (R : Radii P) (a : Puncture P),
    HolomorphicOn {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ < R.radius a} (baseMap P a)

def finite_ends_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d → ∀ R : Radii P, Finite (End P R)

def exists_local_model_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    ∀ (R : Radii P) (j : End P R), Nonempty (LocalModel P R j)

def exists_local_models_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    ∃ (R : Radii P) (M : ∀ j : End P R, LocalModel P R j), Finite (End P R)

def local_model_meromorphic_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)), P ≠ 0 →
    ∀ (R : Radii P) (j : End P R) (M : LocalModel P R j), MeromorphicAt M.root 0

def local_model_equation_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (R : Radii P) (j : End P R)
    (M : LocalModel P R j) (t : Disk (rootRadius (R.radius j.1) M.degree)),
    (fiber P (baseMap P j.1 ((t : ℂ) ^ M.degree))).eval (M.root t) = 0

def local_model_extension_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)), P ≠ 0 →
    ∀ (R : Radii P) (j : End P R) (M : LocalModel P R j),
    ∃ F : ℂ → RiemannSphere,
      ScalarMeromorphicOn (Metric.ball 0 (rootRadius (R.radius j.1) M.degree)) F ∧
      ∀ t ∈ puncturedDisk 0 (rootRadius (R.radius j.1) M.degree),
        F t = sphereFinite (M.root t)

def scalarMeromorphic_of_local_charts_type : Prop :=
  ∀ {X : Type*} [TopologicalSpace X] (S : RiemannSurface X) (F : X → RiemannSphere),
    (∀ x : X, ∃ e ∈ maximalAtlas S.atlas,
      x ∈ e.val.source ∧ ScalarMeromorphicOn e.val.target (F ∘ e.val.symm)) →
    ScalarMeromorphic S F

/-- Full original completion conclusion.  The topology, models, meromorphic
extension and compact cover are conclusions, never assumed certificates.
The old surface uses its base-coordinate atlas.  Its inclusion preserves that
complex structure, and the added charts identify the actual punctured models.
The final finite compact cover makes the source's compact-core argument explicit.
-/
def compact_completion_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    ∃ (R : Radii P) (M : ∀ j : End P R, LocalModel P R j),
      Finite (End P R) ∧
      ∃ top : TopologicalSpace (Carrier P R),
        letI := top
        ∃ (S : RiemannSurface (Carrier P R)) (S₀ : RiemannSurface (Curve P))
          (W : Carrier P R → RiemannSphere)
          (chart : End P R → ComplexChart (Carrier P R)),
          CompactSpace (Carrier P R) ∧
          Topology.IsOpenEmbedding (Sum.inl : Curve P → Carrier P R) ∧
          DenseRange (Sum.inl : Curve P → Carrier P R) ∧
          (∀ e ∈ S₀.atlas, ∀ x ∈ e.val.source, e.val x = x.val.1) ∧
          HolomorphicMap S₀ S Sum.inl ∧
          (∀ x : Curve P, LocallyBiholomorphicAt S₀ S Sum.inl x) ∧
          ScalarMeromorphic S (baseCoordinate P R) ∧ ScalarMeromorphic S W ∧
          (∀ x : Curve P, W (Sum.inl x) = sphereFinite x.val.2) ∧
          (∀ j : End P R,
            chart j ∈ S.atlas ∧
            (chart j).val.source = endChartSource P R j ∧
            (chart j).val.target = Metric.ball 0 (rootRadius (R.radius j.1) (M j).degree) ∧
            (chart j).val (Sum.inr j) = 0 ∧
            (∀ t : Disk (rootRadius (R.radius j.1) (M j).degree),
              (chart j).val.symm t = Sum.inl (localPoint P R j ((M j).parameter t))) ∧
            ∀ t ∈ (chart j).val.target,
              baseCoordinate P R ((chart j).val.symm t) =
                match j.1 with
                | Sum.inl c => sphereFinite ((c : ℂ) + t ^ (M j).degree)
                | Sum.inr _ => infinityParametrization (t ^ (M j).degree)) ∧
          ∃ (K : Set ℂ) (s : End P R → ℝ),
            IsCompact K ∧ K ⊆ baseSet P ∧
            (∀ j, 0 < s j ∧ s j < rootRadius (R.radius j.1) (M j).degree) ∧
            IsCompact (Sum.inl '' {x : Curve P | x.val.1 ∈ K} : Set (Carrier P R)) ∧
            (∀ j, IsCompact ((chart j).val.symm '' Metric.closedBall 0 (s j))) ∧
            (Set.univ : Set (Carrier P R)) =
              (Sum.inl '' {x : Curve P | x.val.1 ∈ K}) ∪
                ⋃ j, (chart j).val.symm '' Metric.closedBall 0 (s j)

end Specs.D12Complex.Ch21.CompactCompletion
