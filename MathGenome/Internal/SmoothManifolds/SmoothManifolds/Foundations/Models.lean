import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Models

namespace SmoothManifolds

universe u v

/-! Public names for the canonical chart and extension data. These transparent
aliases keep implementation targets in this module while allowing independent
Specs to refer to precisely the same underlying objects. -/

abbrev Euclidean := @ModelData.Euclidean

abbrev halfSpaceSet := @ModelData.halfSpaceSet

abbrev halfSpaceFace := @ModelData.halfSpaceFace

abbrev HalfSpace := @ModelData.HalfSpace

abbrev orthantSet := @ModelData.orthantSet

abbrev Orthant := @ModelData.Orthant

abbrev modelSet := @ModelData.modelSet

abbrev ModelSpace := @ModelData.ModelSpace

abbrev ModelChart := @ModelData.ModelChart

abbrev TopologicalManifold := @ModelData.TopologicalManifold

abbrev HasLocalContDiffExtensionAt := @ModelData.HasLocalContDiffExtensionAt

abbrev LocallyContDiffAlong := @ModelData.LocallyContDiffAlong

abbrev LocallyContDiffOn := @ModelData.LocallyContDiffOn

abbrev LocallySmoothOn := @ModelData.LocallySmoothOn

abbrev ModelContDiffOn := @ModelData.ModelContDiffOn

abbrev ModelSmoothOn := @ModelData.ModelSmoothOn

abbrev ModelMapContDiffOn := @ModelData.ModelMapContDiffOn

abbrev OrthantContDiffOn := @ModelData.OrthantContDiffOn

abbrev OrthantSmoothOn := @ModelData.OrthantSmoothOn

abbrev OrthantMapContDiffOn := @ModelData.OrthantMapContDiffOn

abbrev sectionSupport := @ModelData.sectionSupport

@[simp] theorem halfSpaceSet_zero : halfSpaceSet 0 = Set.univ := rfl

@[simp] theorem mem_halfSpaceSet_succ (n : ℕ) (x : Euclidean (n + 1)) :
    x ∈ halfSpaceSet (n + 1) ↔ 0 ≤ x (Fin.last n) := Iff.rfl

@[simp] theorem halfSpaceFace_zero : halfSpaceFace 0 = ∅ := rfl

@[simp] theorem mem_halfSpaceFace_succ (n : ℕ) (x : Euclidean (n + 1)) :
    x ∈ halfSpaceFace (n + 1) ↔ x (Fin.last n) = 0 := Iff.rfl

/-- Dimension zero really is a one-point space, not an empty model. -/
def halfSpaceZeroEquiv : HalfSpace 0 ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := ⟨fun i => Fin.elim0 i, Set.mem_univ _⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

@[simp] theorem orthantSet_zero (n : ℕ) : orthantSet n 0 = Set.univ := by
  ext x
  simp [orthantSet, ModelData.orthantSet]

@[simp] theorem mem_orthantSet (n : ℕ) (k : Fin (n + 1)) (x : Euclidean n) :
    x ∈ orthantSet n k ↔ ∀ i : Fin n, i.val < k.val → 0 ≤ x i := Iff.rfl

/-- An empty base is a manifold in every dimension and either permitted model. -/
def emptyManifold (n : ℕ) (kind : ModelKind) : TopologicalManifold n kind Empty where
  hausdorff := inferInstance
  secondCountable := inferInstance
  atlas := ∅
  covers p := Empty.elim p

/-- Exactly the source's topological axioms and chart cover, with no additional
proof certificate hidden in the manifold data. -/
theorem nonempty_topologicalManifold_iff (n : ℕ) (kind : ModelKind)
    (M : Type u) [TopologicalSpace M] :
    Nonempty (TopologicalManifold n kind M) ↔
      T2Space M ∧ SecondCountableTopology M ∧
        ∃ atlas : Set (ModelChart n kind M), ∀ p : M, ∃ c ∈ atlas, p ∈ c.source := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.hausdorff, A.secondCountable, A.atlas, A.covers⟩
  · rintro ⟨hT, hC, atlas, hcover⟩
    exact ⟨⟨hT, hC, atlas, hcover⟩⟩

namespace TopologicalManifold

/-- Choosing a chart requires no extra structure or theorem hypothesis. -/
noncomputable def chartAt {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : TopologicalManifold n kind M) (p : M) :
    ModelChart n kind M := Classical.choose (A.covers p)

theorem chartAt_mem {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : TopologicalManifold n kind M) (p : M) :
    A.chartAt p ∈ A.atlas := (Classical.choose_spec (A.covers p)).1

theorem mem_chartAt_source {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : TopologicalManifold n kind M) (p : M) :
    p ∈ (A.chartAt p).source := (Classical.choose_spec (A.covers p)).2

end TopologicalManifold

/-- This exposes the full extension quantifiers for arbitrary subsets. -/
theorem locallyContDiffOn_iff {n : ℕ} {F : Type v}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℕ∞) (s : Set (Euclidean n)) (f : s → F) :
    LocallyContDiffOn r s f ↔
      ∀ x : s, ∃ U : Set (Euclidean n), IsOpen U ∧ x.val ∈ U ∧
        ∃ g : Euclidean n → F, ContDiffOn ℝ r g U ∧
          ∀ y : s, y.val ∈ U → g y.val = f y := Iff.rfl

@[simp] theorem sectionSupport_eq {B : Type u} [TopologicalSpace B]
    {E : B → Type v} [∀ x, Zero (E x)] (s : ∀ x, E x) :
    sectionSupport s = closure {x | s x ≠ 0} := rfl

end SmoothManifolds
