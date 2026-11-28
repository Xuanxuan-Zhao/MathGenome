import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-! Finite Category O and its highest-weight conventions (LO01). -/

noncomputable section

open CategoryTheory UniversalEnvelopingAlgebra Module
open Specs.LieAlgebrasAndRepresentations
open VermaModules (Direction Regular U envelopingMap)
open scoped Classical ModuleCat.Algebra

namespace Specs.RepTheorySurvey.CategoryO
attribute [local instance 100] LieRing.ofAssociativeRing

universe u v
-- The Lie algebra and module carriers vary independently.
set_option linter.checkUnivs false

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g]

/-- A choice of opposite root vectors with the usual coroot normalization. -/
structure RootTriple [FiniteDimensional ℂ g] (H : LieSubalgebra ℂ g)
    (α : Module.Dual ℂ H) where
  e : g
  f : g
  e_mem : e ∈ RootDecomposition.rootSpace_value H α
  f_mem : f ∈ RootDecomposition.rootSpace_value H (-α)
  e_ne_zero : e ≠ 0
  f_ne_zero : f ≠ 0
  lie_e_f : ⁅e, f⁆ = (RootForm.coroot_value H α : g)
  lie_h_e : ⁅(RootForm.coroot_value H α : g), e⁆ = (2 : ℂ) • e
  lie_h_f : ⁅(RootForm.coroot_value H α : g), f⁆ = (-2 : ℂ) • f

/-- The simple roots are indexed by the full subtype of indecomposable positive roots. -/
structure Setup (g : Type u) [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g] where
  semisimple : SolvableRadical.IsSemisimple_value ℂ g
  cartan : LieSubalgebra ℂ g
  [isCartan : cartan.IsCartanSubalgebra]
  direction : Direction cartan
  regular : Regular cartan direction
  triple : ∀ i : SerreRelations.simple cartan direction, RootTriple cartan i.val

attribute [instance] Setup.isCartan

abbrev Setup.Weight [FiniteDimensional ℂ g] (D : Setup g) := Module.Dual ℂ D.cartan

abbrev Setup.Simple [FiniteDimensional ℂ g] (D : Setup g) :=
  SerreRelations.simple D.cartan D.direction

abbrev Setup.alpha [FiniteDimensional ℂ g] (D : Setup g) (i : D.Simple) : D.Weight := i.val

abbrev Setup.h [FiniteDimensional ℂ g] (D : Setup g) (i : D.Simple) : D.cartan :=
  RootForm.coroot_value D.cartan (D.alpha i)

abbrev Setup.e [FiniteDimensional ℂ g] (D : Setup g) (i : D.Simple) : g := (D.triple i).e
abbrev Setup.f [FiniteDimensional ℂ g] (D : Setup g) (i : D.Simple) : g := (D.triple i).f

abbrev Setup.nPlus [FiniteDimensional ℂ g] (D : Setup g) :=
  VermaModules.positive_value D.cartan D.direction
abbrev Setup.nMinus [FiniteDimensional ℂ g] (D : Setup g) :=
  VermaModules.negative_value D.cartan D.direction
abbrev Setup.borel [FiniteDimensional ℂ g] (D : Setup g) :=
  VermaModules.borel_value D.cartan D.direction

/-- The Lie action obtained by restricting a compatible enveloping action along ι. -/
abbrev restrictedRepresentation (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V]
    [IsScalarTower ℂ (U g) V] : _root_.Shared.Lie.Representation ℂ g V :=
  ((Algebra.lsmul ℂ ℂ V : U g →ₐ[ℂ] Module.End ℂ V) :
    U g →ₗ⁅ℂ⁆ Module.End ℂ V).comp (ι ℂ)

abbrev restrictedLieRingModule (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V]
    [IsScalarTower ℂ (U g) V] : LieRingModule g V :=
  _root_.Shared.Lie.representationLieRingModule ℂ g V (restrictedRepresentation V)

abbrev restrictedLieModule (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V]
    [IsScalarTower ℂ (U g) V] :
    @LieModule ℂ g V _ _ _ _ _ (restrictedLieRingModule V) :=
  _root_.Shared.Lie.representationLieModule ℂ g V (restrictedRepresentation V)

def weightSpace_value (H : LieSubalgebra ℂ g) (V : Type v) [AddCommGroup V] [Module ℂ V]
    [Module (U g) V] [IsScalarTower ℂ (U g) V] (μ : Module.Dual ℂ H) : Submodule ℂ V :=
  letI := restrictedLieRingModule V (g := g)
  letI := restrictedLieModule V (g := g)
  HighestWeightData.weightSpace_value V H μ

/-- The complex image of the enveloping algebra of N acting on one vector. -/
def orbit_value (N : LieSubalgebra ℂ g) (V : Type v) [AddCommGroup V] [Module ℂ V]
    [Module (U g) V] [IsScalarTower ℂ (U g) V] (x : V) : Submodule ℂ V :=
  LinearMap.range
    { toFun := fun a : U N => envelopingMap N.incl a • x
      map_add' := fun a b => by rw [map_add, add_smul]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, Algebra.smul_def, map_mul, AlgHom.commutes, mul_smul,
          algebraMap_smul] }

variable [FiniteDimensional ℂ g]

def rootLattice_value (D : Setup g) : Submodule ℤ D.Weight :=
  HighestWeightData.integralRootLattice_value D.alpha

def positiveRootCone_value (D : Setup g) : Submodule ℕ D.Weight :=
  HighestWeightData.positiveRootCone_value D.alpha

def weightLE_value (D : Setup g) (μ lam : D.Weight) : Prop :=
  HighestWeightData.weightLE_value D.alpha μ lam

def objects_value (D : Setup g) : ObjectProperty (ModuleCat.{v} (U g)) :=
  fun X => Module.Finite (U g) X ∧
    DirectSum.IsInternal (weightSpace_value D.cartan X) ∧
    ∀ x : X, FiniteDimensional ℂ (orbit_value D.nPlus X x)

abbrev category_value (D : Setup g) : Type (max u (v + 1)) :=
  (objects_value.{u, v} D).FullSubcategory

/-- The character with the prescribed evaluations on the Cartan and positive part.
The accompanying existence and uniqueness theorem justifies the choice for every weight. -/
def character_value (D : Setup g) (lam : D.Weight) : U D.borel →ₐ[ℂ] ℂ :=
  letI : Nonempty (U D.borel →ₐ[ℂ] ℂ) := ⟨_root_.Shared.Lie.augmentation ℂ D.borel⟩
  Classical.epsilon (VermaModules.IsWeightCharacter D.cartan D.direction lam)

def verma_value (D : Setup g) (lam : D.Weight) : ModuleCat.{u} (U g) :=
  ModuleCat.of (U g) (VermaModules.induced_value D.cartan D.direction (character_value D lam))

section

open VermaWeightsUniversal (inducedLieRingModule inducedLieModule)

local instance {H : LieSubalgebra ℂ g} {φ : Direction H} {χ : U (VermaModules.borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule g (VermaModules.induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {H : LieSubalgebra ℂ g} {φ : Direction H} {χ : U (VermaModules.borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ g (VermaModules.induced_value H φ χ) := inducedLieModule H φ χ

/-- On the pinned simple quotient use the enveloping action extending its quotient Lie action. -/
def simpleQuotient_value (D : Setup g) (lam : D.Weight) : ModuleCat.{u} (U g) :=
  letI : Module (U g) (SimpleHighestWeightQuotient.simpleQuotient_value
      D.cartan D.direction (character_value D lam)) :=
    _root_.Shared.Lie.actionModule ℂ g _
      (UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ g _))
  ModuleCat.of (U g)
    (SimpleHighestWeightQuotient.simpleQuotient_value D.cartan D.direction (character_value D lam))

end

/-- Positive integral coordinates with at least one strictly positive coefficient. -/
def positiveCoordinates_value {E : Type u} [AddCommGroup E] [Module ℝ E] {I : Type v}
    [Fintype I] (b : Basis I ℝ E) (x : E) : Prop :=
  ∃ n : I → ℕ, (∃ i, 0 < n i) ∧ x = ∑ i, (n i : ℝ) • b i

/-- The root-space-generated Lie subalgebra for a set of Cartan roots. -/
def rootLieSpan_value (H : LieSubalgebra ℂ g) (P : Set (Module.Dual ℂ H)) :
    LieSubalgebra ℂ g :=
  LieSubalgebra.lieSpan ℂ g {x | ∃ α ∈ P, x ∈ RootDecomposition.rootSpace_value H α}

/-- A regular direction preserving the sign partition, simple roots, and triangular data. -/
def MatchesPositiveSystem (H : LieSubalgebra ℂ g) (P : Set (Module.Dual ℂ H))
    (φ : Direction H) : Prop :=
  Regular H φ ∧
    SerreRelations.positive H φ = P ∧
    SerreRelations.simple H φ = {α | α ∈ P ∧ ∀ β ∈ P, ∀ γ ∈ P, α ≠ β + γ} ∧
    VermaModules.positive_value H φ = rootLieSpan_value H P ∧
    VermaModules.negative_value H φ =
      rootLieSpan_value H (RootDecomposition.rootSet_value H \ P) ∧
    VermaModules.borel_value H φ = H ⊔ rootLieSpan_value H P

def direction_for_positive_system_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (H : LieSubalgebra ℂ g) (P : Set (Module.Dual ℂ H)) {I : Type v}
    [Fintype I] (b : Basis I ℝ (RealRootSpace.E H)),
    P ⊆ RootDecomposition.rootSet_value H →
    (∀ α ∈ RootDecomposition.rootSet_value H,
      (α ∈ P → positiveCoordinates_value b (RealRootSpace.rootRestriction H α)) ∧
      (α ∉ P → positiveCoordinates_value b (-RealRootSpace.rootRestriction H α))) →
    ∃ φ : Direction H, MatchesPositiveSystem H P φ

open _root_.LieAlgebrasAndRepresentations (RootRegular positiveRoots)

/-- The sign system of any regular chamber of the actual real Cartan root system. -/
def direction_for_real_positive_system_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (H : LieSubalgebra ℂ g) (d : RealRootSpace.Realization H),
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    ∀ w : RealRootSpace.E H, RootRegular (RealRootSpace.realRoots H) w →
    ∃ φ : Direction H, MatchesPositiveSystem H
      {α | α ∈ RootDecomposition.rootSet_value H ∧
        RealRootSpace.rootRestriction H α ∈ positiveRoots (RealRootSpace.realRoots H) w} φ

def root_parts_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g] (D : Setup g),
    D.nPlus.toSubmodule =
      ⨆ α : {α : D.Weight // 0 < D.direction α}, RootDecomposition.rootSpace_value D.cartan α.val
    ∧ D.nMinus.toSubmodule =
      ⨆ α : {α : D.Weight // D.direction α < 0}, RootDecomposition.rootSpace_value D.cartan α.val

def finite_simple_roots_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g] (D : Setup g),
    Finite D.Simple

def cartan_borel_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g] (D : Setup g),
    D.borel.toSubmodule = D.cartan.toSubmodule ⊔ D.nPlus.toSubmodule ∧
    Disjoint D.cartan.toSubmodule D.nPlus.toSubmodule ∧
    IsCompl D.nMinus.toSubmodule D.borel.toSubmodule

def exists_triples_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g],
    SolvableRadical.IsSemisimple_value ℂ g →
    ∀ (H : LieSubalgebra ℂ g) [H.IsCartanSubalgebra] (φ : Direction H),
      Nonempty (∀ i : SerreRelations.simple H φ, RootTriple H i.val)

def mem_weightSpace_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] (H : LieSubalgebra ℂ g)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V] [IsScalarTower ℂ (U g) V]
    (μ : Module.Dual ℂ H) (x : V),
    x ∈ weightSpace_value H V μ ↔ ∀ h : H, (ι ℂ (h : g)) • x = μ h • x

def mem_orbit_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] (N : LieSubalgebra ℂ g)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V] [IsScalarTower ℂ (U g) V]
    (x y : V), y ∈ orbit_value N V x ↔ ∃ a : U N, envelopingMap N.incl a • x = y

def character_unique_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (lam : D.Weight),
    VermaModules.IsWeightCharacter D.cartan D.direction lam (character_value D lam) ∧
    ∀ χ, VermaModules.IsWeightCharacter D.cartan D.direction lam χ → χ = character_value D lam

def submoduleOrderIso_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g]
    (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V] [IsScalarTower ℂ (U g) V],
    letI := restrictedLieRingModule V (g := g)
    letI := restrictedLieModule V (g := g)
    Submodule (U g) V ≃o LieSubmodule ℂ g V

def submodule_correspondence_type : Prop :=
  ∃ F : submoduleOrderIso_type.{u, v},
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g]
    (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V] [IsScalarTower ℂ (U g) V]
    (S : Submodule (U g) V) (x : V),
    x ∈ F V S ↔ x ∈ S

def quotientMap_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (lam : D.Weight), verma_value D lam →ₗ[U g] simpleQuotient_value D lam

def quotient_map_type : Prop :=
  ∃ q : quotientMap_type.{u},
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (lam : D.Weight),
    Function.Surjective (q D lam) ∧
    ∀ x : verma_value D lam,
      q D lam x = SimpleHighestWeightQuotient.quotientMap D.cartan D.direction (character_value D lam) x

def simpleQuotient_simple_type : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (lam : D.Weight), IsSimpleModule (U g) (simpleQuotient_value D lam)

def category_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g],
    Setup g → Type (max u (v + 1))

def objects_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g],
    Setup g → ObjectProperty (ModuleCat.{v} (U g))

def rootLattice_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g), Submodule ℤ D.Weight

def positiveRootCone_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g), Submodule ℕ D.Weight

def weightLE_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g), D.Weight → D.Weight → Prop

def weightSpace_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] (H : LieSubalgebra ℂ g)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V] [IsScalarTower ℂ (U g) V],
    Module.Dual ℂ H → Submodule ℂ V

def orbit_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g], LieSubalgebra ℂ g →
    ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V] [IsScalarTower ℂ (U g) V],
    V → Submodule ℂ V

def character_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g), D.Weight → (U D.borel →ₐ[ℂ] ℂ)

def verma_type :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g), D.Weight → ModuleCat.{u} (U g)

def simpleQuotient_type := verma_type.{u}

end Specs.RepTheorySurvey.CategoryO
