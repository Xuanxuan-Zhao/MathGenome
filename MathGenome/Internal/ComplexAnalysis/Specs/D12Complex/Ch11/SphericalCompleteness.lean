import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.CompactExhaustion
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.SphericalLimits
import Mathlib.Topology.MetricSpace.Cauchy

/-! The space consists of maps on Ω, not arbitrary total representatives.
The extension below fills values outside Ω only to use the canonical local
holomorphy and scalar-meromorphy predicates. It imposes no boundary condition. -/
noncomputable section
open Set Filter
open scoped Topology Classical
namespace D12Complex.SphericalCompleteness

/-- A total representative of a map defined on Ω. -/
def extend (Ω : Set ℂ) (F : Ω → RiemannSphere) : ℂ → RiemannSphere :=
  fun z => if h : z ∈ Ω then F ⟨z, h⟩ else sphereInfty

/-- Holomorphic sphere maps, equivalently scalar meromorphic maps plus infinity
on a domain. The equivalence is a theorem, not a field in this definition. -/
abbrev Map (Ω : Set ℂ) :=
  {F : Ω → RiemannSphere // PlaneSphereHolomorphicOn Ω (extend Ω F)}

/-- Empty suprema are zero, using the real conditional supremum convention. -/
def compactSup (Ω K : Set ℂ) (F G : Ω → RiemannSphere) : ℝ :=
  ⨆ z : {z : Ω // (z : ℂ) ∈ K}, Chordal.chordal (F z.val) (G z.val)

/-- Exactly the source sum, indexed by j = n+1 ≥ 1. -/
def compactDistance (Ω : Set ℂ) (F G : Ω → RiemannSphere) : ℝ :=
  ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
    min 1 (compactSup Ω (Ch11.compactExhaustionStage Ω (n + 1)) F G)

/-- Sequential spherical normality with the full scalar/infinity alternative. -/
def SphericallyNormal (Ω : Set ℂ) (𝓕 : Set (ℂ → RiemannSphere)) : Prop :=
  (∀ F ∈ 𝓕, ScalarMeromorphicOn Ω F ∨ EqOn F (fun _ => sphereInfty) Ω) ∧
  ∀ f : ℕ → ℂ → RiemannSphere, (∀ n, f n ∈ 𝓕) →
    ∃ (φ : ℕ → ℕ) (F : ℂ → RiemannSphere), StrictMono φ ∧
      (ScalarMeromorphicOn Ω F ∨ EqOn F (fun _ => sphereInfty) Ω) ∧
      SphericalLimits.SphericalLocallyUniformOn (f ∘ φ) F Ω

/-- The finite constants used in the source example. -/
def naturalConstantFamily : Set (ℂ → RiemannSphere) :=
  Set.range (fun n : ℕ => fun _ : ℂ => sphereFinite (n : ℂ))

end D12Complex.SphericalCompleteness

namespace Specs.D12Complex.Ch11.SphericalCompleteness
open _root_.D12Complex _root_.D12Complex.SphericalCompleteness

def extend_type := (Ω : Set ℂ) → (Ω → RiemannSphere) → ℂ → RiemannSphere
def extend_value : extend_type := fun Ω F z =>
  if h : z ∈ Ω then F ⟨z, h⟩ else sphereInfty

def Map_type := Set ℂ → Type
def Map_value : Map_type := fun Ω =>
  {F : Ω → RiemannSphere // PlaneSphereHolomorphicOn Ω (extend Ω F)}

def compactSup_type := (Ω K : Set ℂ) → (Ω → RiemannSphere) → (Ω → RiemannSphere) → ℝ
def compactSup_value : compactSup_type := fun Ω K F G =>
  ⨆ z : {z : Ω // (z : ℂ) ∈ K}, Chordal.chordal (F z.val) (G z.val)

def compactDistance_type := (Ω : Set ℂ) → (Ω → RiemannSphere) → (Ω → RiemannSphere) → ℝ
def compactDistance_value : compactDistance_type := fun Ω F G =>
  ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
    min 1 (compactSup Ω (_root_.D12Complex.Ch11.compactExhaustionStage Ω (n + 1)) F G)

def SphericallyNormal_type := Set ℂ → Set (ℂ → RiemannSphere) → Prop
def SphericallyNormal_value : SphericallyNormal_type := fun Ω 𝓕 =>
  (∀ F ∈ 𝓕, ScalarMeromorphicOn Ω F ∨ EqOn F (fun _ => sphereInfty) Ω) ∧
  ∀ f : ℕ → ℂ → RiemannSphere, (∀ n, f n ∈ 𝓕) →
    ∃ (φ : ℕ → ℕ) (F : ℂ → RiemannSphere), StrictMono φ ∧
      (ScalarMeromorphicOn Ω F ∨ EqOn F (fun _ => sphereInfty) Ω) ∧
      SphericalLimits.SphericalLocallyUniformOn (f ∘ φ) F Ω

def naturalConstantFamily_type := Set (ℂ → RiemannSphere)
def naturalConstantFamily_value : naturalConstantFamily_type :=
  Set.range (fun n : ℕ => fun _ : ℂ => sphereFinite (n : ℂ))

/-- Exact identification with the original scalar objects on every domain. -/
def map_classification_type : Prop := ∀ (Ω : Set ℂ), IsDomain Ω →
  ∀ F : Ω → RiemannSphere,
    PlaneSphereHolomorphicOn Ω (extend Ω F) ↔
      ScalarMeromorphicOn Ω (extend Ω F) ∨ EqOn (extend Ω F) (fun _ => sphereInfty) Ω

/-- Any original total representative induces a member of Map Ω. -/
def map_representation_type : Prop := ∀ (Ω : Set ℂ), IsDomain Ω →
  ∀ F : ℂ → RiemannSphere,
    (ScalarMeromorphicOn Ω F ∨ EqOn F (fun _ => sphereInfty) Ω) →
      ∃ G : Map Ω, ∀ z : Ω, G.val z = F z

/-- Existence of the specified complete metric, with its precise convergence. -/
def complete_metric_type : Prop := ∀ (Ω : Set ℂ), IsDomain Ω →
  ∃ m : MetricSpace (Map Ω),
    (∀ F G : Map Ω, @dist (Map Ω) m.toDist F G = compactDistance Ω F.val G.val) ∧
    @CompleteSpace (Map Ω) m.toUniformSpace ∧
    ∀ (f : ℕ → Map Ω) (F : Map Ω),
      @Tendsto _ _ (fun n => f n) atTop (@nhds _ m.toUniformSpace.toTopologicalSpace F) ↔
        SphericalLimits.SphericalLocallyUniformOn
          (fun n => extend Ω (f n).val) (extend Ω F.val) Ω

def constants_uniform_infty_type : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ _z : ℂ,
    Chordal.chordal sphereInfty (sphereFinite (n : ℂ)) < ε

def constants_normal_type : Prop := ∀ (Ω : Set ℂ), IsDomain Ω →
  SphericallyNormal Ω naturalConstantFamily

/-- Unbounded on every nonempty compact subset, with a single family member
exceeding any specified real bound at all its points. -/
def constants_unbounded_type : Prop := ∀ (Ω K : Set ℂ), IsDomain Ω →
  IsCompact K → K ⊆ Ω → K.Nonempty → ∀ M : ℝ,
    ∃ n : ℕ, ∀ z ∈ K, M < ‖(n : ℂ)‖

/-- The approximants in the example are genuine finite scalar meromorphic maps. -/
def constants_finite_meromorphic_type : Prop := ∀ (Ω : Set ℂ), IsDomain Ω →
  ∀ n : ℕ, ScalarMeromorphicOn Ω (fun _ => sphereFinite (n : ℂ))

/-- Explicit failure of local ordinary boundedness, in its compact-set form. -/
def constants_counterexample_type : Prop := ∀ (Ω : Set ℂ), IsDomain Ω →
  SphericallyNormal Ω naturalConstantFamily ∧
  SphericalLimits.SphericalLocallyUniformOn
    (fun n _ => sphereFinite (n : ℂ)) (fun _ => sphereInfty) Ω ∧
  ¬ (∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ M : ℝ,
    ∀ (n : ℕ) (z : ℂ), z ∈ K → ‖(n : ℂ)‖ ≤ M)

end Specs.D12Complex.Ch11.SphericalCompleteness
