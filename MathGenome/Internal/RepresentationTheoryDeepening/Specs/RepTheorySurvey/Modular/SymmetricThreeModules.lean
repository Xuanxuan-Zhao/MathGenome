import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.StableLattices
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible

/-! The trivial, sign and standard representations and the integral standard lattice for (S_3). -/

namespace RepTheorySurvey.Modular.SymmetricThree
namespace Spec

universe u v

abbrev GroupValue := Equiv.Perm (Fin 3)

def transpositionValue : GroupValue := Equiv.swap 0 1

def threeCycleValue : GroupValue := Equiv.swap 0 1 * Equiv.swap 1 2

abbrev trivialType (R : Type u) [CommRing R] := Representation R GroupValue R

def trivialValue (R : Type u) [CommRing R] : trivialType R :=
  Representation.trivial R GroupValue R

abbrev signType (R : Type u) [CommRing R] := Representation R GroupValue R

def signValue (R : Type u) [CommRing R] : signType R where
  toFun g := ((Equiv.Perm.sign g : ℤ) : R) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp [mul_assoc, mul_left_comm]

abbrev permutationType (R : Type u) [CommRing R] :=
  Representation R GroupValue (Fin 3 → R)

def permutationValue (R : Type u) [CommRing R] : permutationType R where
  toFun g :=
    { toFun := fun x i => x (g⁻¹ i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext x i; rfl
  map_mul' g h := by ext x i; rfl

abbrev planeSubmoduleType (R : Type u) [CommRing R] := Submodule R (Fin 3 → R)

def planeSubmoduleValue (R : Type u) [CommRing R] : planeSubmoduleType R where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by intros; simp_all [Finset.sum_add_distrib]
  smul_mem' := by
    intro a x hx
    change ∑ i, a * x i = 0
    rw [← Finset.mul_sum, hx, mul_zero]

abbrev PlaneValue (R : Type u) [CommRing R] := ↥(planeSubmoduleValue R)

abbrev standardType (R : Type u) [CommRing R] := Representation R GroupValue (PlaneValue R)

def standardValue (R : Type u) [CommRing R] : standardType R :=
  (permutationValue R).subrepresentation (planeSubmoduleValue R) fun g x hx => by
    change ∑ i, x (g⁻¹ i) = 0
    rw [Equiv.sum_comp g⁻¹]
    exact hx

abbrev ordinaryFamilyType (F : Type u) [Field F] :=
  Fin 3 → ModuleCat.{u} (MonoidAlgebra F GroupValue)

noncomputable def ordinaryFamilyValue (F : Type u) [Field F] : ordinaryFamilyType F :=
  ![MR01Spec.representationModuleValue (trivialValue F),
    MR01Spec.representationModuleValue (signValue F),
    MR01Spec.representationModuleValue (standardValue F)]

def classData : Prop :=
  (∀ g : GroupValue, IsConj g 1 ∨ IsConj g transpositionValue ∨ IsConj g threeCycleValue) ∧
  Nat.card {g : GroupValue // IsConj g 1} = 1 ∧
  Nat.card {g : GroupValue // IsConj g transpositionValue} = 3 ∧
  Nat.card {g : GroupValue // IsConj g threeCycleValue} = 2

def representativeOrders : Prop :=
  orderOf (1 : GroupValue) = 1 ∧ orderOf transpositionValue = 2 ∧ orderOf threeCycleValue = 3

def standardDimension : Prop :=
  ∀ (F : Type u) [Field F], Module.finrank F (PlaneValue F) = 2

def ordinaryDimensions : Prop :=
  ∀ (F : Type u) [Field F], ∀ i : Fin 3,
    Module.finrank F (RestrictScalars F (MonoidAlgebra F GroupValue)
      (ordinaryFamilyValue F i)) = (![1, 1, 2] : Fin 3 → ℕ) i

def trivialCharacter : Prop :=
  ∀ (F : Type u) [Field F] (g : GroupValue), (trivialValue F).character g = 1

def signCharacter : Prop :=
  ∀ (F : Type u) [Field F] (g : GroupValue),
    (signValue F).character g = ((Equiv.Perm.sign g : ℤ) : F)

def signRepresentatives : Prop :=
  Equiv.Perm.sign transpositionValue = -1 ∧ Equiv.Perm.sign threeCycleValue = 1

def standardCharacter : Prop :=
  ∀ (F : Type u) [Field F],
    (standardValue F).character 1 = 2 ∧
    (standardValue F).character transpositionValue = 0 ∧
    (standardValue F).character threeCycleValue = -1

/-- The argument with coordinate differences works in every characteristic other than three. -/
def standardSimple : Prop :=
  ∀ (F : Type u) [Field F], (3 : F) ≠ 0 → Representation.IsIrreducible (standardValue F)

def ordinarySimpleFamily : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K] {p : ℕ},
    MR01Spec.SplittingSystemData GroupValue p O K →
      MR01Spec.SimpleRepresentativeFamily (ordinaryFamilyValue K)

section Lattice

variable (O : Type u) [CommRing O] (K : Type v) [Field K] [Algebra O K]

local instance : Module O (PlaneValue K) := Module.restrictScalars O K _

abbrev integralEmbeddingType := PlaneValue O →ₗ[O] PlaneValue K

/-- Coordinatewise inclusion of the integral zero-sum plane into the fraction-field plane. -/
def integralEmbeddingValue : integralEmbeddingType O K where
  toFun x := ⟨fun i => algebraMap O K (x.val i), by
    change ∑ i, algebraMap O K (x.val i) = 0
    rw [← map_sum, show ∑ i, x.val i = 0 from x.property, map_zero]⟩
  map_add' x y := Subtype.ext (funext fun i => map_add (algebraMap O K) (x.val i) (y.val i))
  map_smul' a x := Subtype.ext (funext fun i => map_mul (algebraMap O K) a (x.val i))

end Lattice

abbrev coordinateReductionType (O : Type u) [CommRing O] [IsLocalRing O] :=
  letI := Module.restrictScalars O (IsLocalRing.ResidueField O) (PlaneValue (IsLocalRing.ResidueField O))
  PlaneValue O →ₗ[O] PlaneValue (IsLocalRing.ResidueField O)

noncomputable def coordinateReductionValue (O : Type u) [CommRing O] [IsLocalRing O] :
    coordinateReductionType O :=
  integralEmbeddingValue O (IsLocalRing.ResidueField O)

def standardLatticeReduction : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K] {p : ℕ},
    MR01Spec.SplittingSystemData GroupValue p O K →
    letI := Module.restrictScalars O K (PlaneValue K)
    letI := IsScalarTower.restrictScalars O K (PlaneValue K)
    ∃ (L : MR04LatticeSpec.LatticeData O (standardValue K))
      (j : PlaneValue O ≃ₗ[O] L.carrier)
      (e : (MR04LatticeSpec.residueAction (MR04LatticeSpec.integralAction O L)).Equiv
        (standardValue (IsLocalRing.ResidueField O))),
      (∀ x, (j x : PlaneValue K) = integralEmbeddingValue O K x) ∧
        ∀ x, e (MR04LatticeSpec.reduce (O := O) (j x)) = coordinateReductionValue O x

abbrev groupType := type_of% (@GroupValue)
abbrev elementType := GroupValue
abbrev trivialRepresentationType := type_of% (@trivialValue)
abbrev signRepresentationType := type_of% (@signValue)
abbrev permutationRepresentationType := type_of% (@permutationValue)
abbrev planeType := type_of% (@PlaneValue)
abbrev zeroSumSubmoduleType := type_of% (@planeSubmoduleValue)
abbrev standardRepresentationType := type_of% (@standardValue)
abbrev familyType := type_of% (@ordinaryFamilyValue)
abbrev integralInclusionType := type_of% (@integralEmbeddingValue)
abbrev residueMapType := type_of% (@coordinateReductionValue)

def standardAction : Prop :=
  ∀ {R : Type u} [CommRing R] (g : GroupValue) (x : PlaneValue R) (i : Fin 3),
    (standardValue R g x).val i = x.val (g⁻¹ i)

end Spec
end RepTheorySurvey.Modular.SymmetricThree
