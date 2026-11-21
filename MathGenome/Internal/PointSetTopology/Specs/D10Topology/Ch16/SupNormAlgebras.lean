import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-! Independent interfaces for paper.tex, chapter 16, opening paragraphs.
`C(X, 𝕜)` always means the canonical continuous maps. Compactness here has
no separation hypothesis. `RCLike` specializes to both ℝ and ℂ with their
usual norms and algebra operations. A function algebra need not contain 1.
The uniform closure explicitly uses chapter 13's uniform topology.
No approximation or Stone--Weierstrass result is imported. -/
noncomputable section
open Set Filter
open scoped Topology
universe u v w
namespace Specs.D10Topology.Ch16.SupNormAlgebras

def supNorm {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X]
    [RCLike 𝕜] (f : C(X, 𝕜)) : ℝ := ‖f‖

def supNormType := {X : Type u} → {𝕜 : Type v} → [TopologicalSpace X] → [CompactSpace X] →
    [RCLike 𝕜] → C(X, 𝕜) → ℝ

def supNormTopology {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X]
    [RCLike 𝕜] : TopologicalSpace C(X, 𝕜) :=
  (inferInstance : MetricSpace C(X, 𝕜)).toUniformSpace.toTopologicalSpace

def supNormTopologyType := {X : Type u} → {𝕜 : Type v} → [TopologicalSpace X] → [CompactSpace X] →
    [RCLike 𝕜] → TopologicalSpace C(X, 𝕜)

abbrev FunctionSubalgebra (X : Type u) (𝕜 : Type v) [TopologicalSpace X] [RCLike 𝕜] :=
  NonUnitalSubalgebra 𝕜 C(X, 𝕜)

def FunctionSubalgebraType := (X : Type u) → (𝕜 : Type v) → [TopologicalSpace X] → [RCLike 𝕜] → Type (max u v)

abbrev RealFunctionAlgebra (X : Type u) [TopologicalSpace X] := FunctionSubalgebra X ℝ

def RealFunctionAlgebraType := (X : Type u) → [TopologicalSpace X] → Type u

abbrev ComplexFunctionAlgebra (X : Type u) [TopologicalSpace X] := FunctionSubalgebra X ℂ

def ComplexFunctionAlgebraType := (X : Type u) → [TopologicalSpace X] → Type u

def IsUnital {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜]
    (A : FunctionSubalgebra X 𝕜) : Prop := (1 : C(X, 𝕜)) ∈ A

def IsUnitalType := {X : Type u} → {𝕜 : Type v} → [TopologicalSpace X] → [RCLike 𝕜] →
    FunctionSubalgebra X 𝕜 → Prop

def SeparatesPoints {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜]
    (A : Set C(X, 𝕜)) : Prop :=
  ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y

def SeparatesPointsType := {X : Type u} → {𝕜 : Type v} → [TopologicalSpace X] → [RCLike 𝕜] →
    Set C(X, 𝕜) → Prop

def ConjugationInvariant {X : Type u} [TopologicalSpace X] (A : Set C(X, ℂ)) : Prop :=
  ∀ f ∈ A, star f ∈ A

def ConjugationInvariantType := {X : Type u} → [TopologicalSpace X] → Set C(X, ℂ) → Prop

def uniformClosure {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜]
    (A : Set C(X, 𝕜)) : Set C(X, 𝕜) :=
  @closure _ (Specs.D10Topology.Ch13.FunctionTopologies.uniformContinuousTopology) A

def uniformClosureType := {X : Type u} → {𝕜 : Type v} → [TopologicalSpace X] → [RCLike 𝕜] →
    Set C(X, 𝕜) → Set C(X, 𝕜)

def supNorm_eq_iSup : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ f : C(X, 𝕜), supNorm f = ⨆ x : X, ‖f x‖

def realSupNorm_eq_iSup_abs : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] (f : C(X, ℝ)),
    supNorm f = ⨆ x : X, |f x|

def complexSupNorm_eq_iSup : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] (f : C(X, ℂ)),
    supNorm f = ⨆ x : X, ‖f x‖

def supNorm_bounded : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ f : C(X, 𝕜), ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M

def supNorm_nonneg : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ f : C(X, 𝕜), 0 ≤ supNorm f

def supNorm_eq_zero : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ f : C(X, 𝕜), supNorm f = 0 ↔ f = 0

def supNorm_add_le : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ f g : C(X, 𝕜), supNorm (f + g) ≤ supNorm f + supNorm g

def supNorm_smul : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ (c : 𝕜) (f : C(X, 𝕜)), supNorm (c • f) = ‖c‖ * supNorm f

def supNorm_mul_le : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ f g : C(X, 𝕜), supNorm (f * g) ≤ supNorm f * supNorm g

def supNorm_empty : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ [IsEmpty X] (f : C(X, 𝕜)), supNorm f = 0

def supNorm_const : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ [Nonempty X] (c : 𝕜), supNorm (ContinuousMap.const X c) = ‖c‖

def supNorm_dist : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ f g : C(X, 𝕜), dist f g = supNorm (f - g)

def supNorm_lt_iff : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ (f : C(X, 𝕜)) (ε : ℝ), 0 < ε →
    (supNorm f < ε ↔ ∀ x, ‖f x‖ < ε)

def supNormTopology_eq_uniform : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  supNormTopology (X := X) (𝕜 := 𝕜) =
    Specs.D10Topology.Ch13.FunctionTopologies.uniformContinuousTopology

def tendsto_iff_uniform : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ {ι : Type w} (F : ι → C(X, 𝕜)) (f : C(X, 𝕜)) (l : Filter ι),
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i => (F i : X → 𝕜)) f l

def functionSubalgebra_iff : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜],
  ∀ S : Set C(X, 𝕜),
    (∃ A : FunctionSubalgebra X 𝕜, (A : Set C(X, 𝕜)) = S) ↔
    (0 ∈ S ∧ (∀ f ∈ S, ∀ g ∈ S, f + g ∈ S) ∧
      (∀ f ∈ S, ∀ g ∈ S, f * g ∈ S) ∧ ∀ c : 𝕜, ∀ f ∈ S, c • f ∈ S)

def unital_iff_contains_constants : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜],
  ∀ A : FunctionSubalgebra X 𝕜,
    IsUnital A ↔ ∀ c : 𝕜, ContinuousMap.const X c ∈ A

def empty_domain_collapse : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜],
  ∀ [IsEmpty X] (f g : C(X, 𝕜)), f = g ∧ (1 : C(X, 𝕜)) = 0

def empty_domain_algebra : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜],
  ∀ [IsEmpty X] (A : FunctionSubalgebra X 𝕜),
    IsUnital A ∧ (A : Set C(X, 𝕜)) = Set.univ

def conjugate_apply : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (f : C(X, ℂ)) (x : X),
    (star f) x = starRingEnd ℂ (f x)

def conjugationInvariant_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set C(X, ℂ)),
    ConjugationInvariant A ↔ ∀ f ∈ A, ∃ g ∈ A, ∀ x, g x = starRingEnd ℂ (f x)

def uniformClosure_eq_norm_closure : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ A : Set C(X, 𝕜), uniformClosure A = closure A

def mem_uniformClosure_iff : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ (A : Set C(X, 𝕜)) (f : C(X, 𝕜)),
    f ∈ uniformClosure A ↔ ∀ ε : ℝ, 0 < ε → ∃ g ∈ A, supNorm (f - g) < ε

def mem_uniformClosure_iff_pointwise_error : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜],
  ∀ (A : Set C(X, 𝕜)) (f : C(X, 𝕜)),
    f ∈ uniformClosure A ↔ ∀ ε : ℝ, 0 < ε → ∃ g ∈ A, ∀ x, ‖f x - g x‖ < ε

end Specs.D10Topology.Ch16.SupNormAlgebras
