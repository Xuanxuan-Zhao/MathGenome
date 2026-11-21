import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RegularMultiplicity
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin

/-! The three representations in Example A, paper.tex 1669–1676.
Coordinates are indexed by `Fin 3`, and permutations act by inverse pullback.
The standard space is the actual zero-sum subspace of the permutation space. -/
noncomputable section
universe u
namespace P103.Ch08.S3CharacterTableSpecs

abbrev S3 := Equiv.Perm (Fin 3)
abbrev Coordinates := Fin 3 → ℂ

def transposition : S3 := Equiv.swap 0 1
def threeCycle : S3 := Equiv.swap 0 1 * Equiv.swap 1 2

def trivialValue : Representation ℂ S3 ℂ := Representation.trivial ℂ S3 ℂ

def signValue : Representation ℂ S3 ℂ where
  toFun g := ((Equiv.Perm.sign g : ℤ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp [mul_smul]
    ring

def permutationValue : Representation ℂ S3 Coordinates where
  toFun g :=
    { toFun := fun x i => x (g⁻¹ i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext x i; rfl
  map_mul' g h := by ext x i; rfl

def zeroSum : Submodule ℂ Coordinates where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by intros; simp_all [Finset.sum_add_distrib]
  smul_mem' := by
    intro c x hx
    change ∑ i, c * x i = 0
    rw [← Finset.mul_sum, hx, mul_zero]

abbrev Plane := zeroSum

def planeSubrepresentation : Subrepresentation permutationValue where
  toSubmodule := zeroSum
  apply_mem_toSubmodule g x hx := by
    change ∑ i, x (g⁻¹ i) = 0
    rw [Equiv.sum_comp g⁻¹]
    exact hx

def standardValue : Representation ℂ S3 Plane := planeSubrepresentation.toRepresentation

/-- Construction interfaces; the expected values below fix the actual actions. -/
def trivialRepresentationType := Representation ℂ S3 ℂ
def signRepresentationType := Representation ℂ S3 ℂ
def permutationRepresentationType := Representation ℂ S3 Coordinates
def standardRepresentationType := Representation ℂ S3 Plane

def classDataType : Prop :=
  (∀ g : S3, IsConj g 1 ∨ IsConj g transposition ∨ IsConj g threeCycle) ∧
  Nat.card {g : S3 // IsConj g 1} = 1 ∧
  Nat.card {g : S3 // IsConj g transposition} = 3 ∧
  Nat.card {g : S3 // IsConj g threeCycle} = 2

def fixedPointTraceType : Prop :=
  ∀ g : S3, CharacterSpecs.characterValue permutationValue g = (Fintype.card {i : Fin 3 // g i = i} : ℂ)

def decompositionType : Prop :=
  ∃ e : (trivialValue.prod standardValue).Equiv permutationValue,
    ∀ (c : ℂ) (x : Plane) (i : Fin 3), e (c, x) i = c + x.val i

def dimensionsType : Prop := Module.finrank ℂ Plane = 2

def trivialRowType : Prop :=
  CharacterSpecs.characterValue trivialValue 1 = 1 ∧ CharacterSpecs.characterValue trivialValue transposition = 1 ∧
    CharacterSpecs.characterValue trivialValue threeCycle = 1

def signRowType : Prop :=
  CharacterSpecs.characterValue signValue 1 = 1 ∧ CharacterSpecs.characterValue signValue transposition = -1 ∧
    CharacterSpecs.characterValue signValue threeCycle = 1

def standardRowType : Prop :=
  CharacterSpecs.characterValue standardValue 1 = 2 ∧ CharacterSpecs.characterValue standardValue transposition = 0 ∧
    CharacterSpecs.characterValue standardValue threeCycle = -1

def normType : Prop :=
  UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue standardValue) (CharacterSpecs.characterValue standardValue) =
    ((4 + 3 * 0 + 2 * 1 : ℂ) / 6) ∧ (4 + 3 * 0 + 2 * 1 : ℂ) / 6 = 1

def irreducibilityType : Prop :=
  Irreducible ℂ S3 ℂ trivialValue ∧ Irreducible ℂ S3 ℂ signValue ∧
    Irreducible ℂ S3 Plane standardValue

def distinctType : Prop :=
  ¬ Nonempty (trivialValue.Equiv signValue) ∧
  ¬ Nonempty (trivialValue.Equiv standardValue) ∧
  ¬ Nonempty (signValue.Equiv standardValue)

def squareSumType : Prop :=
  (Module.finrank ℂ ℂ)^2 + (Module.finrank ℂ ℂ)^2 +
    (Module.finrank ℂ Plane)^2 = Fintype.card S3

def exhaustiveType : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ S3 V),
    Irreducible ℂ S3 V ρ →
      Nonempty (trivialValue.Equiv ρ) ∨ Nonempty (signValue.Equiv ρ) ∨
        Nonempty (standardValue.Equiv ρ)

end P103.Ch08.S3CharacterTableSpecs
