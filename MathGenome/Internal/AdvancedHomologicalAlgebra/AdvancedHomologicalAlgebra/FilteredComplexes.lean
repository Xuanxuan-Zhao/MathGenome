import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FilteredComplexes

/-! HA-F01: decreasing filtered cochain complexes in any abelian category.

`Filtration`, `FilteredComplex`, and `FilteredMap` are the shared canonical
interfaces. Their conditions are subobject containments, expressed by
factorization. `Filtration.ofSuccessive` accepts exactly the consecutive-degree
preservation hypothesis in the source.

The definitions below expose the canonical restriction and degreewise quotient
constructions. The lemmas establish their functoriality and the quotient
universal property in the category of cochain complexes.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra

/-- The cochain complex `F^p K`. -/
def filtrationStep : F01Specs.StepType.{v,u} := F01Specs.StepValue
/-- The associated graded cochain complex `F^p K / F^(p+1) K`. -/
def associatedGraded : F01Specs.GradedType.{v,u} := F01Specs.GradedValue
/-- Inclusion `F^p K ⟶ K`. -/
def filtrationInclusion : F01Specs.InclusionType.{v,u} := F01Specs.InclusionValue
/-- Inclusion `F^(p+1) K ⟶ F^p K`. -/
def filtrationTransition : F01Specs.TransitionType.{v,u} := F01Specs.TransitionValue
/-- Quotient map `F^p K ⟶ gr^p K`. -/
def gradedProjection : F01Specs.ProjectionType.{v,u} := F01Specs.ProjectionValue
/-- Restriction of a filtered map to a filtration step. -/
def filtrationStepMap : F01Specs.StepMapType.{v,u} := F01Specs.StepMapValue
/-- The map on associated graded complexes. -/
def associatedGradedMap : F01Specs.GradedMapType.{v,u} := F01Specs.GradedMapValue
/-- Descend a cochain map to the quotient complex. -/
def gradedDesc : F01Specs.QuotientDescType.{v,u} := F01Specs.QuotientDescValue

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace FilteredMap
variable {X Y Z : FilteredComplex A}

@[ext]
theorem ext {f g : FilteredMap X Y} (h : f.hom = g.hom) : f = g := by
  cases f; cases g; cases h; rfl

@[simp]
theorem id_comp (f : FilteredMap X Y) : (id X).comp f = f := by
  apply ext
  exact Category.id_comp _

@[simp]
theorem comp_id (f : FilteredMap X Y) : f.comp (id Y) = f := by
  apply ext
  exact Category.comp_id _

theorem comp_assoc {W : FilteredComplex A}
    (f : FilteredMap W X) (g : FilteredMap X Y) (h : FilteredMap Y Z) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply ext
  exact Category.assoc _ _ _

@[simp]
theorem stepMap_id (X : FilteredComplex A) (p : ℤ) :
    (id X).stepMap p = 𝟙 (X.filtration.step p) := by
  ext n
  apply (cancel_mono (X.filtration.piece p n).arrow).1
  change (id X).component p n ≫ _ = 𝟙 _ ≫ _
  rw [component_arrow]
  simp [id]

@[simp]
theorem stepMap_comp (f : FilteredMap X Y) (g : FilteredMap Y Z) (p : ℤ) :
    (f.comp g).stepMap p = f.stepMap p ≫ g.stepMap p := by
  ext n
  apply (cancel_mono (Z.filtration.piece p n).arrow).1
  change (f.comp g).component p n ≫ _ = (f.component p n ≫ g.component p n) ≫ _
  rw [component_arrow, Category.assoc, component_arrow, ← Category.assoc, component_arrow]
  change (X.filtration.piece p n).arrow ≫ (f.hom.f n ≫ g.hom.f n) =
    ((X.filtration.piece p n).arrow ≫ f.hom.f n) ≫ g.hom.f n
  rw [Category.assoc]

@[reassoc (attr := simp)]
theorem inclusion_naturality (f : FilteredMap X Y) (p : ℤ) :
    f.stepMap p ≫ Y.filtration.inclusion p = X.filtration.inclusion p ≫ f.hom := by
  ext n
  exact f.component_arrow p n

@[reassoc (attr := simp)]
theorem projection_naturality (f : FilteredMap X Y) (p : ℤ) :
    X.filtration.projection p ≫ f.gradedMap p = f.stepMap p ≫ Y.filtration.projection p := by
  ext n
  dsimp only [HomologicalComplex.comp_f, Filtration.projection, gradedMap]
  exact cokernel.π_desc _ _ _

@[simp]
theorem gradedMap_id (X : FilteredComplex A) (p : ℤ) :
    (id X).gradedMap p = 𝟙 (X.filtration.graded p) := by
  have : Epi (X.filtration.projection p) :=
    HomologicalComplex.epi_of_epi_f _ (fun _ => inferInstanceAs (Epi (cokernel.π _)))
  apply (cancel_epi (X.filtration.projection p)).1
  rw [projection_naturality, stepMap_id, Category.id_comp, Category.comp_id]

@[simp]
theorem gradedMap_comp (f : FilteredMap X Y) (g : FilteredMap Y Z) (p : ℤ) :
    (f.comp g).gradedMap p = f.gradedMap p ≫ g.gradedMap p := by
  have : Epi (X.filtration.projection p) :=
    HomologicalComplex.epi_of_epi_f _ (fun _ => inferInstanceAs (Epi (cokernel.π _)))
  apply (cancel_epi (X.filtration.projection p)).1
  calc
    X.filtration.projection p ≫ (f.comp g).gradedMap p =
        (f.stepMap p ≫ g.stepMap p) ≫ Z.filtration.projection p := by
      rw [projection_naturality, stepMap_comp]
    _ = (X.filtration.projection p ≫ f.gradedMap p) ≫ g.gradedMap p := by
      rw [Category.assoc, ← g.projection_naturality, ← Category.assoc,
        ← f.projection_naturality]
    _ = X.filtration.projection p ≫ (f.gradedMap p ≫ g.gradedMap p) := Category.assoc _ _ _

end FilteredMap

namespace Filtration
variable {K : CochainComplex A ℤ}

instance inclusion_mono (F : Filtration K) (p : ℤ) : Mono (F.inclusion p) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstanceAs (Mono (Subobject.arrow _)))

instance transition_mono (F : Filtration K) (p : ℤ) : Mono (F.transition p) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstanceAs (Mono (Subobject.ofLE _ _ _)))

instance projection_epi (F : Filtration K) (p : ℤ) : Epi (F.projection p) :=
  HomologicalComplex.epi_of_epi_f _ (fun _ => inferInstanceAs (Epi (cokernel.π _)))

@[reassoc (attr := simp)]
theorem transition_inclusion (F : Filtration K) (p : ℤ) :
    F.transition p ≫ F.inclusion p = F.inclusion (p + 1) := by
  ext n
  exact Subobject.ofLE_arrow _

@[reassoc (attr := simp)]
theorem transition_projection (F : Filtration K) (p : ℤ) :
    F.transition p ≫ F.projection p = 0 := by
  ext n
  exact cokernel.condition _

@[reassoc (attr := simp)]
theorem projection_quotientDesc (F : Filtration K) (p : ℤ) {L : CochainComplex A ℤ}
    (g : F.step p ⟶ L) (h : F.transition p ≫ g = 0) :
    F.projection p ≫ F.quotientDesc p g h = g := by
  ext n
  exact cokernel.π_desc _ _ _

theorem quotientDesc_unique (F : Filtration K) (p : ℤ) {L : CochainComplex A ℤ}
    (g : F.step p ⟶ L) (h : F.transition p ≫ g = 0)
    (q : F.graded p ⟶ L) (hq : F.projection p ≫ q = g) :
    q = F.quotientDesc p g h := by
  apply (cancel_epi (F.projection p)).1
  rw [hq, projection_quotientDesc]

/-- In particular the degreewise quotient is the cokernel as a cochain complex. -/
def projectionIsCokernel (F : Filtration K) (p : ℤ) :
    IsColimit (CokernelCofork.ofπ (F.projection p) (F.transition_projection p)) :=
  CokernelCofork.IsColimit.ofπ _ _ (F.quotientDesc p)
    (F.projection_quotientDesc p) (F.quotientDesc_unique p)
end Filtration

/-- Full functoriality of both constructions. -/
theorem filtered_constructions_functorial : F01Specs.Functoriality.{v,u} := by
  intro A _ _
  exact ⟨FilteredMap.stepMap_id, FilteredMap.stepMap_comp,
    FilteredMap.gradedMap_id, FilteredMap.gradedMap_comp⟩

/-- The structure maps are natural with respect to every filtered map. -/
theorem filtered_constructions_natural : F01Specs.Naturality.{v,u} := by
  intro A _ _ X Y f p
  exact ⟨f.inclusion_naturality p, f.transition_naturality p, f.projection_naturality p⟩

/-- Subcomplex inclusions and the quotient's existence and uniqueness property. -/
theorem filtered_subcomplex_and_quotient : F01Specs.SubcomplexAndQuotient.{v,u} := by
  intro A _ _ K F p
  refine ⟨inferInstance, inferInstance, inferInstance, F.transition_projection p, ?_⟩
  intro L g h
  exact ⟨F.quotientDesc p g h, F.projection_quotientDesc p g h,
    fun q hq => F.quotientDesc_unique p g h q hq⟩

/-- The restriction and quotient differentials are induced by the original one. -/
theorem filtered_differential_formulas : F01Specs.DifferentialFormulas.{v,u} := by
  intro A _ _ K F p i j k
  exact ⟨F.differential_arrow p i j, (F.step p).d_comp_d i j k,
    F.π_gradedDifferential p i j, (F.graded p).d_comp_d i j k⟩
end AdvancedHomologicalAlgebra
