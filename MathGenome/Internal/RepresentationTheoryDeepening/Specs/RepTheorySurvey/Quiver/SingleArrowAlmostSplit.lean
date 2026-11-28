import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.SingleArrowObjects
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! The almost split sequence for the quiver `1 → 2`. -/

open CategoryTheory
open scoped RM03.OneArrowSpec

namespace RepTheorySurvey.Quiver.SingleArrowAlmostSplitSpec

open SingleArrowObjectsSpec (Rep FiniteRep Vertex S₁ S₂ P₁)
open RM03.QuiverRepresentation (vertex arrow component homMk)
open RM03.OneArrowSpec (edge)

set_option linter.checkUnivs false

universe w d

variable (k : Type w) [Field k]

/-- The common copy of the field at vertex 2. -/
theorem targetVertex :
    vertex (S₂.{w, d} k) true = vertex (P₁.{w, d} k) true := by
  calc
    _ = ModuleCat.of k (ULift.{d} k) := by simp [S₂, FormsSpec.vertexSimple]
    _ = _ := rfl

/-- The common copy of the field at vertex 1. -/
theorem sourceVertex :
    vertex (P₁.{w, d} k) false = vertex (S₁.{w, d} k) false := by
  calc
    _ = ModuleCat.of k (ULift.{d} k) := rfl
    _ = _ := by simp [S₁, FormsSpec.vertexSimple]

abbrev InclusionType := ∀ (k : Type w) [Field k], S₂.{w, d} k ⟶ P₁.{w, d} k

abbrev ProjectionType := ∀ (k : Type w) [Field k], P₁.{w, d} k ⟶ S₁.{w, d} k

/-- Zero at vertex 1 and the identity of the field at vertex 2. -/
noncomputable def inclusion : InclusionType.{w, d} := fun k [_] =>
  homMk (fun i => match i with
    | false => 0
    | true => (eqToHom (targetVertex k)).hom) (by
      intro i j a
      rcases a with ⟨⟨⟩, rfl, rfl⟩
      change (eqToHom (targetVertex.{w, d} k)).hom.comp (arrow (S₂.{w, d} k) edge) =
        (arrow (P₁.{w, d} k) edge).comp 0
      rw [show arrow (S₂.{w, d} k) edge = 0 from
        RM03.QuiverRepresentation.arrow_ofArrows _ _ edge]
      simp)

/-- The identity of the field at vertex 1 and zero at vertex 2. -/
noncomputable def projection : ProjectionType.{w, d} := fun k [_] =>
  homMk (fun i => match i with
    | false => (eqToHom (sourceVertex k)).hom
    | true => 0) (by
      intro i j a
      rcases a with ⟨⟨⟩, rfl, rfl⟩
      change (0 : _ →ₗ[k] _).comp (arrow (P₁.{w, d} k) edge) =
        (arrow (S₁.{w, d} k) edge).comp (eqToHom (sourceVertex.{w, d} k)).hom
      rw [show arrow (S₁.{w, d} k) edge = 0 from
        RM03.QuiverRepresentation.arrow_ofArrows _ _ edge]
      simp)

abbrev SequenceType := ∀ (k : Type w) [Field k], ShortComplex (Rep.{w, d} k)

/-- The sequence with the given inclusion and projection. -/
noncomputable def sequence : SequenceType.{w, d} := fun k [_] =>
  ShortComplex.mk (inclusion k) (projection k) (by
    apply RM03.QuiverRepresentation.hom_ext
    intro i
    cases i
    · change (component (projection k) false).comp 0 = 0
      simp
    · change (0 : _ →ₗ[k] _).comp (component (inclusion k) true) = 0
      simp)

abbrev ShortExact : Prop :=
  ∀ (k : Type w) [Field k], (sequence.{w, d} k).ShortExact

abbrev Nonsplit : Prop :=
  ∀ (k : Type w) [Field k],
    ¬ IsSplitMono (inclusion.{w, d} k) ∧ ¬ IsSplitEpi (projection.{w, d} k)

abbrev RightFactorization : Prop :=
  ∀ (k : Type w) [Field k] (V : FiniteRep.{w, d} k) (f : V.obj ⟶ S₁.{w, d} k),
    ¬ IsSplitEpi f → ∃ g : V.obj ⟶ P₁.{w, d} k, g ≫ projection k = f

abbrev LeftFactorization : Prop :=
  ∀ (k : Type w) [Field k] (V : FiniteRep.{w, d} k) (f : S₂.{w, d} k ⟶ V.obj),
    ¬ IsSplitMono f → ∃ g : P₁.{w, d} k ⟶ V.obj, inclusion k ≫ g = f

/-- The displayed sequence is almost split in the full subcategory of
finite-dimensional representations. -/
abbrev AlmostSplit : Prop :=
  ∀ (k : Type w) [Field k],
    ∃ S : ShortComplex (FiniteRep.{w, d} k),
      S.map (RM03.QuiverModuleEquivalenceSpec.finiteRepresentations
        (k := k) (Q := Vertex)).ι = sequence.{w, d} k ∧
      S.ShortExact ∧ ¬ IsSplitMono S.f ∧ ¬ IsSplitEpi S.g ∧
      (∀ (V : FiniteRep.{w, d} k) (f : V ⟶ S.X₃),
        ¬ IsSplitEpi f → ∃ g : V ⟶ S.X₂, g ≫ S.g = f) ∧
      (∀ (V : FiniteRep.{w, d} k) (f : S.X₁ ⟶ V),
        ¬ IsSplitMono f → ∃ g : S.X₂ ⟶ V, S.f ≫ g = f)

end RepTheorySurvey.Quiver.SingleArrowAlmostSplitSpec
