import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.Category
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Central character and root-lattice components of the finite category O. -/

noncomputable section

open CategoryTheory UniversalEnvelopingAlgebra
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)
open scoped Classical ModuleCat.Algebra

namespace Specs.RepTheorySurvey.CategoryO.ComponentProjectors

universe u v
set_option linter.checkUnivs false

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g]

abbrev Center (g : Type u) [LieRing g] [LieAlgebra ℂ g] := Subalgebra.center ℂ (U g)

abbrev CentralCharacter (g : Type u) [LieRing g] [LieAlgebra ℂ g] :=
  Center g →ₐ[ℂ] ℂ

variable [FiniteDimensional ℂ g] (D : Setup g)

/-- The additive quotient by the integral root lattice. -/
abbrev Coset := D.Weight ⧸ rootLattice_value D

def coset (μ : D.Weight) : Coset D := (rootLattice_value D).mkQ μ

abbrev Index := CentralCharacter g × Coset D

variable (X : ModuleCat.{v} (U g))

/-- Multiplication by a central element is linear over the enveloping algebra. -/
def centerAction (z : Center g) : X →ₗ[U g] X where
  toFun x := z.val • x
  map_add' := smul_add _
  map_smul' a x := by
    change z.val • (a • x) = a • (z.val • x)
    rw [← mul_smul, ← mul_smul, Subalgebra.mem_center_iff.mp z.property a]

def difference (χ : CentralCharacter g) (z : Center g) : Center g :=
  z - algebraMap ℂ (Center g) (χ z)

/-- The character condition is local nilpotence of each central difference. -/
def centralPart (χ : CentralCharacter g) : Submodule (U g) X :=
  ⨅ z : Center g, ⨆ n : ℕ, (centerAction X (difference χ z ^ n)).ker

/-- The span of the weight spaces in the indicated root-lattice coset.
The root-shift property identifies this with their complex sum. -/
def cosetPart (ξ : Coset D) : Submodule (U g) X :=
  Submodule.span (U g) { x | ∃ μ, coset D μ = ξ ∧ x ∈ weightSpace_value D.cartan X μ }

def component (k : Index D) : Submodule (U g) X :=
  centralPart X k.1 ⊓ cosetPart D X k.2

def CosetPartType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : ModuleCat.{v} (U g)) (ξ : Coset D),
    (cosetPart D X ξ).restrictScalars ℂ =
      ⨆ μ : D.Weight, ⨆ (_ : coset D μ = ξ), weightSpace_value D.cartan X μ

def CentralPartType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g]
    (X : ModuleCat.{v} (U g)) (χ : CentralCharacter g) (x : X),
    x ∈ centralPart X χ ↔ ∀ z : Center g, ∃ n : ℕ, ((difference χ z ^ n).val : U g) • x = 0

/-- The sum of the actual joint components is internal, and only finitely many are nonzero. -/
def DecompositionType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : category_value.{u, v} D),
    DirectSum.IsInternal (component D X.obj) ∧
      { k : Index D | component D X.obj k ≠ ⊥ }.Finite


omit [FiniteDimensional ℂ g] in
theorem centerPart_mem {χ : CentralCharacter g} {x : X} :
    x ∈ centralPart X χ ↔ ∀ z : Center g, ∃ n : ℕ, ((difference χ z ^ n).val : U g) • x = 0 := by
  rw [centralPart, Submodule.mem_iInf]
  apply forall_congr'
  intro z
  have hs : Monotone (fun n : ℕ => (centerAction X (difference χ z ^ n)).ker) := by
    intro m n hmn y hy
    change ((difference χ z ^ n).val : U g) • y = 0
    change ((difference χ z ^ m).val : U g) • y = 0 at hy
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [add_comm, pow_add]
    change ((difference χ z ^ l).val * (difference χ z ^ m).val) • y = 0
    rw [mul_smul, hy, smul_zero]
  rw [Submodule.mem_iSup_of_directed _ hs.directed_le]
  rfl

private lemma weight_mem {μ : D.Weight} {x : X} :
    x ∈ weightSpace_value D.cartan X μ ↔
      ∀ h : D.cartan, (ι ℂ (h : g)) • x = μ h • x := by
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  change x ∈ LieModule.weightSpace X (μ : D.cartan → ℂ) ↔
    ∀ h : D.cartan, ⁅(h : g), x⁆ = μ h • x
  simpa only [LieSubalgebra.coe_bracket_of_module] using
    LieModule.mem_weightSpace (μ : D.cartan → ℂ) x

variable {D X} {Y : ModuleCat.{v} (U g)}

theorem component_map_mem (f : X →ₗ[U g] Y) (k : Index D) {x : X}
    (hx : x ∈ component D X k) : f x ∈ component D Y k := by
  refine ⟨(centerPart_mem Y).2 fun z => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := (centerPart_mem X).1 hx.1 z
    exact ⟨n, by rw [← f.map_smul, hn, map_zero]⟩
  · have h : cosetPart D X k.2 ≤ (cosetPart D Y k.2).comap f := by
      apply Submodule.span_le.mpr
      rintro y ⟨μ, hμ, hy⟩
      apply Submodule.subset_span
      refine ⟨μ, hμ, (weight_mem D Y).mpr fun t => ?_⟩
      rw [← f.map_smul, (weight_mem D X).mp hy t, f.map_smul_of_tower]
    exact h hx.2

/-- Restriction of an enveloping-linear map to the indicated joint component. -/
def componentMap (f : X →ₗ[U g] Y) (k : Index D) :
    component D X k →ₗ[U g] component D Y k :=
  (f.domRestrict (component D X k)).codRestrict _ fun x => component_map_mem f k x.property

variable (D)

/-- The component functor with values in left enveloping modules. -/
def ambientFunctor (k : Index D) : category_value.{u, v} D ⥤ ModuleCat.{v} (U g) where
  obj X := ModuleCat.of (U g) (component D X.obj k)
  map f := ModuleCat.ofHom (componentMap f.hom.hom k)
  map_id X := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f h := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Every component is again an object of category O. -/
def ComponentInOType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (k : Index D) (X : category_value.{u, v} D),
    objects_value D ((ambientFunctor D k).obj X)

/-- The component projector as an endofunctor of category O. -/
def componentFunctor (k : Index D)
    (h : ∀ X : category_value.{u, v} D, objects_value D ((ambientFunctor D k).obj X)) :
    category_value.{u, v} D ⥤ category_value.{u, v} D :=
  (objects_value D).lift (ambientFunctor D k) h

/-- The canonical projection to a summand of the internal decomposition. -/
def projection (h : DirectSum.IsInternal (component D X)) (k : Index D) :
    X →ₗ[U g] component D X k :=
  (DirectSum.component (U g) (Index D) (fun j => component D X j) k).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (component D X)) h).symm.toLinearMap

def ProjectionNaturalityType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) {X Y : category_value.{u, v} D}
    (hX : DirectSum.IsInternal (component D X.obj))
    (hY : DirectSum.IsInternal (component D Y.obj))
    (f : X ⟶ Y) (k : Index D),
    (projection D hY k).comp f.hom.hom =
      (componentMap f.hom.hom k).comp (projection D hX k)

def ProjectionOnSummandsType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : category_value.{u, v} D)
    (hX : DirectSum.IsInternal (component D X.obj)) (k : Index D),
    (projection D hX k).comp (component D X.obj k).subtype = LinearMap.id ∧
    ∀ j : Index D, j ≠ k →
      (projection D hX k).comp (component D X.obj j).subtype = 0

/-- No morphisms between summands with different joint indices. -/
def CrossComponentVanishingType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X Y : category_value.{u, v} D) (k j : Index D), k ≠ j →
    ∀ f : component D X.obj k →ₗ[U g] component D Y.obj j, f = 0

/-- Exactness on short exact sequences in the inherited enveloping-module structure. -/
def ProjectorExactType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (k : Index D) {X Y Z : category_value.{u, v} D}
    (f : X ⟶ Y) (q : Y ⟶ Z),
    Function.Injective f.hom.hom →
    Function.Exact f.hom.hom q.hom.hom →
    Function.Surjective q.hom.hom →
    Function.Injective (componentMap f.hom.hom k) ∧
    Function.Exact (componentMap f.hom.hom k) (componentMap q.hom.hom k) ∧
    Function.Surjective (componentMap q.hom.hom k)


def CosetMapType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g), D.Weight → Coset D

def CentralSubmoduleType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] (X : ModuleCat.{v} (U g)),
    CentralCharacter g → Submodule (U g) X

def CosetSubmoduleType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : ModuleCat.{v} (U g)), Coset D → Submodule (U g) X

def ComponentSubmoduleType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : ModuleCat.{v} (U g)), Index D → Submodule (U g) X

def ComponentMapType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    {D : Setup g} {X Y : ModuleCat.{v} (U g)} (_ : X →ₗ[U g] Y) (k : Index D),
    component D X k →ₗ[U g] component D Y k

def AmbientFunctorType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (_ : Index D), category_value.{u, v} D ⥤ ModuleCat.{v} (U g)

def ComponentFunctorType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (k : Index D)
    (_ : ∀ X : category_value.{u, v} D, objects_value D ((ambientFunctor D k).obj X)),
    category_value.{u, v} D ⥤ category_value.{u, v} D

def ProjectionType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) {X : ModuleCat.{v} (U g)}
    (_ : DirectSum.IsInternal (component D X)) (k : Index D),
    X →ₗ[U g] component D X k

end Specs.RepTheorySurvey.CategoryO.ComponentProjectors
