import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Bases

/-! Shared chart models and the local ambient-extension convention.

Coordinates are indexed by `Fin n`, so the manuscript's coordinate x_n is
`Fin.last (n-1)`. In dimension zero there is exactly one coordinate tuple.
The topology on every model is the subspace topology. No smooth compatibility,
boundary invariance, or subsequent manifold theorem is part of the data here.
-/
namespace SmoothManifolds

universe u v w

/-- Either of the two permitted uniform models for ordinary manifolds. -/
inductive ModelKind where
  | halfSpace
  | euclidean
  deriving DecidableEq

/- Canonical data shared by independent specifications and the implementation.
The implementation exports transparent aliases under `SmoothManifolds`. -/
namespace ModelData

/-- A fixed finite-dimensional real coordinate space. -/
abbrev Euclidean (n : ℕ) := Fin n → ℝ

/-- The last-coordinate half-space; the zero-dimensional model is a point. -/
def halfSpaceSet : (n : ℕ) → Set (Euclidean n)
  | 0 => Set.univ
  | n + 1 => {x | 0 ≤ x (Fin.last n)}

/-- The model face, with the separate empty-boundary convention in dimension zero.
This is not an ambient frontier or an assertion of chart invariance. -/
def halfSpaceFace : (n : ℕ) → Set (Euclidean n)
  | 0 => ∅
  | n + 1 => {x | x (Fin.last n) = 0}

abbrev HalfSpace (n : ℕ) := ↥(halfSpaceSet n)

/-- The first k coordinates are nonnegative; `k : Fin (n+1)` enforces 0 ≤ k ≤ n. -/
def orthantSet (n : ℕ) (k : Fin (n + 1)) : Set (Euclidean n) :=
  {x | ∀ i : Fin n, i.val < k.val → 0 ≤ x i}

abbrev Orthant (n : ℕ) (k : Fin (n + 1)) := ↥(orthantSet n k)

def modelSet (n : ℕ) : ModelKind → Set (Euclidean n)
  | .halfSpace => halfSpaceSet n
  | .euclidean => Set.univ

abbrev ModelSpace (n : ℕ) (kind : ModelKind) := ↥(modelSet n kind)

/-- Open source and relatively open target, with mutually inverse continuous maps.
`OpenPartialHomeomorph`, rather than `PartialHomeomorph`, supplies openness. -/
abbrev ModelChart (n : ℕ) (kind : ModelKind) (M : Type u) [TopologicalSpace M] :=
  OpenPartialHomeomorph M (ModelSpace n kind)

/-- Chart-based topological manifold data. There is no nonemptiness requirement.
The separation/countability fields refer to the given topology on M. -/
structure TopologicalManifold (n : ℕ) (kind : ModelKind)
    (M : Type u) [TopologicalSpace M] where
  hausdorff : T2Space M
  secondCountable : SecondCountableTopology M
  atlas : Set (ModelChart n kind M)
  covers : ∀ p : M, ∃ c ∈ atlas, p ∈ c.source

section Extensions
variable {n : ℕ} {D : Type u} {F : Type v}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A local C^r ambient extension at one point of an embedded domain.
The extension takes values in the ambient vector space F, even when the original
map has constrained values. `r = ⊤ : ℕ∞` means smooth, not analytic. -/
def HasLocalContDiffExtensionAt (r : ℕ∞) (ι : D → Euclidean n)
    (f : D → F) (x : D) : Prop :=
  ∃ U : Set (Euclidean n), IsOpen U ∧ ι x ∈ U ∧
    ∃ g : Euclidean n → F, ContDiffOn ℝ r g U ∧
      ∀ y : D, ι y ∈ U → g (ι y) = f y

/-- Local extension at every domain point; no openness of an arbitrary subset is
imposed. This is intentionally stronger than merely differentiating within a set. -/
def LocallyContDiffAlong (r : ℕ∞) (ι : D → Euclidean n) (f : D → F) : Prop :=
  ∀ x : D, HasLocalContDiffExtensionAt r ι f x

/-- C^r on any Euclidean subset, using the local-extension convention. -/
def LocallyContDiffOn (r : ℕ∞) (s : Set (Euclidean n)) (f : s → F) : Prop :=
  LocallyContDiffAlong r Subtype.val f

def LocallySmoothOn (s : Set (Euclidean n)) (f : s → F) : Prop :=
  LocallyContDiffOn (⊤ : ℕ∞) s f

/-- The same convention on a subset of a half-space or Euclidean model.
Relatively open chart domains are the special case `IsOpen s`. -/
def ModelContDiffOn (r : ℕ∞) {kind : ModelKind}
    (s : Set (ModelSpace n kind)) (f : s → F) : Prop :=
  LocallyContDiffAlong r (fun x => x.val.val) f

def ModelSmoothOn {kind : ModelKind}
    (s : Set (ModelSpace n kind)) (f : s → F) : Prop :=
  ModelContDiffOn (⊤ : ℕ∞) s f

/-- Maps into a model are tested after inclusion into its ambient Euclidean space;
the local extension is explicitly not required to stay inside the target model. -/
def ModelMapContDiffOn (r : ℕ∞) {kind : ModelKind} {m : ℕ} {targetKind : ModelKind}
    (s : Set (ModelSpace n kind)) (f : s → ModelSpace m targetKind) : Prop :=
  ModelContDiffOn r s (fun x => (f x).val)

/-- Local extension on elementary orthant domains, including k=0 and n=0. -/
def OrthantContDiffOn (r : ℕ∞) {k : Fin (n + 1)}
    (s : Set (Orthant n k)) (f : s → F) : Prop :=
  LocallyContDiffAlong r (fun x => x.val.val) f

def OrthantSmoothOn {k : Fin (n + 1)}
    (s : Set (Orthant n k)) (f : s → F) : Prop :=
  OrthantContDiffOn (⊤ : ℕ∞) s f

/-- Orthant-valued maps are likewise extended in the ambient target, without
requiring a local extension to preserve its inequalities. -/
def OrthantMapContDiffOn (r : ℕ∞) {k : Fin (n + 1)} {m : ℕ} {l : Fin (m + 1)}
    (s : Set (Orthant n k)) (f : s → Orthant m l) : Prop :=
  OrthantContDiffOn r s (fun x => (f x).val)

end Extensions

/-- Support of a dependent section, closed in the base, not in the total space. -/
def sectionSupport {B : Type u} [TopologicalSpace B] {E : B → Type v}
    [∀ x, Zero (E x)] (s : ∀ x, E x) : Set B :=
  closure {x | s x ≠ 0}

end ModelData

end SmoothManifolds

/-! Independent full types and values for the public definitions are added below.
The shared objects above are available to future Specs without any proof import. -/

namespace Specs.SmoothManifolds.Foundations.Models

open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
universe u v

def EuclideanType :=
  ℕ → Type

def EuclideanValue : EuclideanType :=
  fun n => Fin n → ℝ

def halfSpaceSetType :=
  (n : ℕ) → Set (Euclidean n)

def halfSpaceSetValue : halfSpaceSetType :=
  fun n => match n with
    | 0 => Set.univ
    | n + 1 => {x | 0 ≤ x (Fin.last n)}

def halfSpaceFaceType :=
  (n : ℕ) → Set (Euclidean n)

def halfSpaceFaceValue : halfSpaceFaceType :=
  fun n => match n with
    | 0 => ∅
    | n + 1 => {x | x (Fin.last n) = 0}

def HalfSpaceType :=
  ℕ → Type

def HalfSpaceValue : HalfSpaceType :=
  fun n => ↥(halfSpaceSet n)

def orthantSetType :=
  (n : ℕ) → Fin (n + 1) → Set (Euclidean n)

def orthantSetValue : orthantSetType :=
  fun n k => {x | ∀ i : Fin n, i.val < k.val → 0 ≤ x i}

def OrthantType :=
  (n : ℕ) → Fin (n + 1) → Type

def OrthantValue : OrthantType :=
  fun n k => ↥(orthantSet n k)

def modelSetType :=
  (n : ℕ) → ModelKind → Set (Euclidean n)

def modelSetValue : modelSetType :=
  fun n kind => match kind with
    | .halfSpace => halfSpaceSet n
    | .euclidean => Set.univ

def ModelSpaceType :=
  ℕ → ModelKind → Type

def ModelSpaceValue : ModelSpaceType :=
  fun n kind => ↥(modelSet n kind)

def ModelChartType :=
  ℕ → ModelKind → (M : Type u) → [TopologicalSpace M] → Type u

def ModelChartValue : ModelChartType :=
  @fun n kind M _ => OpenPartialHomeomorph M (ModelSpace n kind)

def TopologicalManifoldType :=
  ℕ → ModelKind → (M : Type u) → [TopologicalSpace M] → Type u

def TopologicalManifoldValue : TopologicalManifoldType :=
  @ModelData.TopologicalManifold

def HasLocalContDiffExtensionAtType :=
  {n : ℕ} → {D : Type u} → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → ℕ∞ → (D → Euclidean n) → (D → F) → D → Prop

def HasLocalContDiffExtensionAtValue : HasLocalContDiffExtensionAtType :=
  fun {n} {D} {F} _ _ r ι f x =>
    ∃ U : Set (Euclidean n), IsOpen U ∧ ι x ∈ U ∧
      ∃ g : Euclidean n → F, ContDiffOn ℝ r g U ∧
        ∀ y : D, ι y ∈ U → g (ι y) = f y

def LocallyContDiffAlongType :=
  {n : ℕ} → {D : Type u} → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → ℕ∞ → (D → Euclidean n) → (D → F) → Prop

def LocallyContDiffAlongValue : LocallyContDiffAlongType :=
  @fun _ _ _ _ _ r ι f => ∀ x, HasLocalContDiffExtensionAt r ι f x

def LocallyContDiffOnType :=
  {n : ℕ} → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → ℕ∞ → (s : Set (Euclidean n)) → (s → F) → Prop

def LocallyContDiffOnValue : LocallyContDiffOnType :=
  @fun _ _ _ _ r s f => LocallyContDiffAlong r Subtype.val f

def LocallySmoothOnType :=
  {n : ℕ} → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (s : Set (Euclidean n)) → (s → F) → Prop

def LocallySmoothOnValue : LocallySmoothOnType :=
  @fun _ _ _ _ s f => LocallyContDiffOn (⊤ : ℕ∞) s f

def ModelContDiffOnType :=
  {n : ℕ} → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → ℕ∞ → {kind : ModelKind} → (s : Set (ModelSpace n kind)) → (s → F) → Prop

def ModelContDiffOnValue : ModelContDiffOnType :=
  @fun _ _ _ _ r _ s f => LocallyContDiffAlong r (fun x => x.val.val) f

def ModelSmoothOnType :=
  {n : ℕ} → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → {kind : ModelKind} → (s : Set (ModelSpace n kind)) → (s → F) → Prop

def ModelSmoothOnValue : ModelSmoothOnType :=
  @fun _ _ _ _ _ s f => ModelContDiffOn (⊤ : ℕ∞) s f

def ModelMapContDiffOnType :=
  {n : ℕ} → ℕ∞ → {kind : ModelKind} → {m : ℕ} → {targetKind : ModelKind} → (s : Set (ModelSpace n kind)) → (s → ModelSpace m targetKind) → Prop

def ModelMapContDiffOnValue : ModelMapContDiffOnType :=
  @fun _ r _ _ _ s f => ModelContDiffOn r s (fun x => (f x).val)

def OrthantContDiffOnType :=
  {n : ℕ} → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → ℕ∞ → {k : Fin (n + 1)} → (s : Set (Orthant n k)) → (s → F) → Prop

def OrthantContDiffOnValue : OrthantContDiffOnType :=
  @fun _ _ _ _ r _ s f => LocallyContDiffAlong r (fun x => x.val.val) f

def OrthantSmoothOnType :=
  {n : ℕ} → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → {k : Fin (n + 1)} → (s : Set (Orthant n k)) → (s → F) → Prop

def OrthantSmoothOnValue : OrthantSmoothOnType :=
  @fun _ _ _ _ _ s f => OrthantContDiffOn (⊤ : ℕ∞) s f

def OrthantMapContDiffOnType :=
  {n : ℕ} → ℕ∞ → {k : Fin (n + 1)} → {m : ℕ} → {l : Fin (m + 1)} → (s : Set (Orthant n k)) → (s → Orthant m l) → Prop

def OrthantMapContDiffOnValue : OrthantMapContDiffOnType :=
  @fun _ r _ _ _ s f => OrthantContDiffOn r s (fun x => (f x).val)

def sectionSupportType :=
  {B : Type u} → [TopologicalSpace B] → {E : B → Type v} → [∀ x, Zero (E x)] → (∀ x, E x) → Set B

def sectionSupportValue : sectionSupportType :=
  @fun _ _ _ _ s => closure {x | s x ≠ 0}

def halfSpaceZeroEquivType :=
  HalfSpace 0 ≃ PUnit

def halfSpaceZeroEquivValue : halfSpaceZeroEquivType :=
  {
    toFun := fun _ => PUnit.unit
    invFun := fun _ => ⟨fun i => Fin.elim0 i, Set.mem_univ _⟩
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ }

def emptyManifoldType :=
  (n : ℕ) → (kind : ModelKind) → TopologicalManifold n kind Empty

def emptyManifoldValue : emptyManifoldType :=
  fun n kind => {
    hausdorff := inferInstance
    secondCountable := inferInstance
    atlas := ∅
    covers := fun p => Empty.elim p }

def chartAtType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} → [TopologicalSpace M] → TopologicalManifold n kind M → M → ModelChart n kind M

noncomputable def chartAtValue : chartAtType :=
  @fun _ _ _ _ A p => Classical.choose (A.covers p)

def halfSpaceSet_zeroType :=
  halfSpaceSet 0 = Set.univ

def mem_halfSpaceSet_succType :=
  ∀ (n : ℕ) (x : Euclidean (n + 1)), x ∈ halfSpaceSet (n + 1) ↔ 0 ≤ x (Fin.last n)

def halfSpaceFace_zeroType :=
  halfSpaceFace 0 = ∅

def mem_halfSpaceFace_succType :=
  ∀ (n : ℕ) (x : Euclidean (n + 1)), x ∈ halfSpaceFace (n + 1) ↔ x (Fin.last n) = 0

def orthantSet_zeroType :=
  ∀ n : ℕ, orthantSet n 0 = Set.univ

def mem_orthantSetType :=
  ∀ (n : ℕ) (k : Fin (n + 1)) (x : Euclidean n), x ∈ orthantSet n k ↔ ∀ i : Fin n, i.val < k.val → 0 ≤ x i

def nonempty_topologicalManifold_iffType :=
  ∀ (n : ℕ) (kind : ModelKind) (M : Type u) [TopologicalSpace M],
    Nonempty (TopologicalManifold n kind M) ↔
      T2Space M ∧ SecondCountableTopology M ∧
        ∃ atlas : Set (ModelChart n kind M), ∀ p : M, ∃ c ∈ atlas, p ∈ c.source

def chartAt_memType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (A : TopologicalManifold n kind M) (p : M), chartAtValue A p ∈ A.atlas

def mem_chartAt_sourceType :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (A : TopologicalManifold n kind M) (p : M), p ∈ (chartAtValue A p).source

def locallyContDiffOn_iffType :=
  ∀ {n : ℕ} {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℕ∞) (s : Set (Euclidean n)) (f : s → F),
    LocallyContDiffOn r s f ↔
      ∀ x : s, ∃ U : Set (Euclidean n), IsOpen U ∧ x.val ∈ U ∧
        ∃ g : Euclidean n → F, ContDiffOn ℝ r g U ∧
          ∀ y : s, y.val ∈ U → g y.val = f y

def sectionSupport_eqType :=
  ∀ {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ x, Zero (E x)]
    (s : ∀ x, E x), sectionSupport s = closure {x | s x ≠ 0}

end Specs.SmoothManifolds.Foundations.Models
