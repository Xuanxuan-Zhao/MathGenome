import MathGenome.Internal.Specs.D07.Ch21.CharacterCompleteness
import MathGenome.Internal.D07.Ch21.CharacterCompletenessGroupAlgebraProduct
import MathGenome.Internal.D07.Ch21.CharacterCompletenessCenterClassSumBasis
import MathGenome.Internal.D07.Ch17.Characters
import Mathlib.LinearAlgebra.FreeModule.Basic

namespace D07.Ch21.CharacterCompleteness

universe u r v w
noncomputable section
open scoped Classical
open Specs.D07.Ch21.CharacterCompleteness
open Specs.D07.Ch21.RegularDecomposition
open Specs.D07.Ch21.HomPairing

/-- Pull a function on the conjugacy quotient back to the group. -/
def quotientToClassFunctions (G : Type u) [Group G] :
    (ConjClasses G → ℂ) →ₗ[ℂ] classFunctions G where
  toFun f := ⟨fun g => f (ConjClasses.mk g), fun _ _ h =>
    congrArg f (ConjClasses.mk_eq_mk_iff_isConj.mpr h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every class function descends uniquely to the quotient. -/
def classFunctionsEquiv (G : Type u) [Group G] :
    (ConjClasses G → ℂ) ≃ₗ[ℂ] classFunctions G :=
  LinearEquiv.ofBijective (quotientToClassFunctions G) (by
    constructor
    · intro f k h
      funext c
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      exact congrArg (fun z : classFunctions G => z.val g) h
    · intro f
      exact ⟨Quotient.lift f.val (fun x y h => f.property x y h), Subtype.ext rfl⟩)

theorem class_function_dimension : ClassFunctionDimension.{u} := by
  classical
  intro G _ _
  let e := classFunctionsEquiv G
  exact ⟨Module.Finite.equiv e, e.finrank_eq.symm.trans (by simp [Nat.card_eq_fintype_card])⟩

/-- An algebra isomorphism transports its center linearly. -/
def centerEquiv {A : Type*} {B : Type*} [Ring A] [Ring B]
    [Algebra ℂ A] [Algebra ℂ B] (e : A ≃ₐ[ℂ] B) :
    Subalgebra.center ℂ A ≃ₗ[ℂ] Subalgebra.center ℂ B where
  toFun a := ⟨e a, (Subalgebra.mem_center_iff).mpr (by
    intro b
    obtain ⟨x, rfl⟩ := e.surjective b
    simpa only [← map_mul] using congrArg e ((Subalgebra.mem_center_iff).mp a.property x))⟩
  invFun b := ⟨e.symm b, (Subalgebra.mem_center_iff).mpr (by
    intro a
    obtain ⟨x, rfl⟩ := e.symm.surjective a
    simpa only [← map_mul] using congrArg e.symm
      ((Subalgebra.mem_center_iff).mp b.property x))⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)
  map_add' a b := Subtype.ext (map_add e (a : A) (b : A))
  map_smul' c a := Subtype.ext (map_smul e c (a : A))

section ProductCenter
variable {I : Type r} {V : I → Type v}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Independent scalar multiples of the identity give central product elements. -/
def scalarsToProductCenter : (I → ℂ) →ₗ[ℂ]
    Subalgebra.center ℂ (∀ i, Module.End ℂ (V i)) where
  toFun c := ⟨fun i => c i • 1, (Subalgebra.mem_center_iff).mpr (by
    intro T
    funext i
    simp)⟩
  map_add' a b := by apply Subtype.ext; funext i; exact add_smul _ _ _
  map_smul' a b := by apply Subtype.ext; funext i; exact mul_smul _ _ _

/-- The center of an endomorphism algebra consists of scalars; the free-module
lemma also handles one-dimensional spaces. Nonzero carriers give uniqueness. -/
lemma scalarsToProductCenter_bijective [∀ i, Module.Free ℂ (V i)]
    [∀ i, Nontrivial (V i)] : Function.Bijective (scalarsToProductCenter (V := V)) := by
  classical
  constructor
  · intro c d h
    funext i
    have he : c i • (1 : Module.End ℂ (V i)) = d i • 1 :=
      congrArg (fun z : Subalgebra.center ℂ (∀ i, Module.End ℂ (V i)) => z.val i) h
    exact (algebraMap ℂ (Module.End ℂ (V i))).injective he
  · intro z
    have hs (i : I) : ∃ c : ℂ, z.val i = c • 1 := by
      have hz : z.val i ∈ Set.center (Module.End ℂ (V i)) := by
        apply Semigroup.mem_center_iff.mpr
        intro T
        have h := congrFun ((Subalgebra.mem_center_iff).mp z.property (Pi.single i T)) i
        simpa only [Pi.mul_apply, Pi.single_eq_same] using h
      obtain ⟨c, hc, he⟩ := Module.End.mem_center_iff.mp hz
      exact ⟨c, he.trans (by ext x; rfl)⟩
    choose c hc using hs
    exact ⟨c, Subtype.ext (funext fun i => (hc i).symm)⟩

end ProductCenter

/-- The two center dimensions count irreducible factors and conjugacy classes. -/
theorem class_count : ClassCount.{u,r,v} := by
  intro G _ _ I _ V _ _ ρ hi hne hc
  have : ∀ i, FiniteDimensional ℂ (V i) := fun i =>
    (RegularDecomposition.irreducible_finite G (V i) (ρ i) (hi i)).1
  have : ∀ i, Nontrivial (V i) := fun i =>
    D07.Ch17.IrreducibleDefinition.irreducible_nontrivial (hi i)
  obtain ⟨e, _⟩ := CharacterCompletenessGroupAlgebraProduct.group_algebra_product
    G I V ρ hi hne hc
  let se := LinearEquiv.ofBijective (scalarsToProductCenter (V := V))
    (scalarsToProductCenter_bijective (V := V))
  calc
    Fintype.card I = Module.finrank ℂ (I → ℂ) := by simp
    _ = Module.finrank ℂ (Subalgebra.center ℂ (∀ i, Module.End ℂ (V i))) := se.finrank_eq
    _ = Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :=
      (centerEquiv e).finrank_eq.symm
    _ = Nat.card (ConjClasses G) :=
      (CharacterCompletenessCenterClassSumBasis.center_dimension G).2

/-- A character is a vector of the full class-function space. -/
def characterAsClassFunction {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : classFunctions G :=
  ⟨Specs.D07.Ch17.Characters.characterValue ℂ G V ρ, by
    intro x y h
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    exact (D07.Ch17.Characters.character_conjugate ℂ G V ρ x g).symm⟩

section Characters
variable {G : Type u} [Group G] [Fintype G] {I : Type r} [Fintype I]
  {V : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
  (hi : ∀ i, Representation.IsIrreducible (ρ i))
  (hne : ∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j)))

include hi hne

omit [Fintype I] in
lemma character_family_orthonormal (i j : I) :
    pairingValue G (characterAsClassFunction (ρ i)) (characterAsClassFunction (ρ j)) =
      if i = j then 1 else 0 := by
  classical
  change pairingValue G (Specs.D07.Ch17.Characters.characterValue ℂ G (V i) (ρ i))
    (Specs.D07.Ch17.Characters.characterValue ℂ G (V j) (ρ j)) = _
  rw [MatrixOrthogonality.character_orthogonality G (V i) (V j) (ρ i) (ρ j) (hi i) (hi j)]
  by_cases h : i = j
  · subst j
    simp [show Nonempty ((ρ i).Equiv (ρ i)) from ⟨.refl _⟩]
  · simp [h, hne i j h]

/-- Pairing a vanishing linear combination with each character extracts its
coefficient, since the pairing is linear in the first argument. -/
lemma characters_independent : LinearIndependent ℂ (fun i => characterAsClassFunction (ρ i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  let L : classFunctions G →ₗ[ℂ] ℂ := {
    toFun := fun f => pairingValue G f (characterAsClassFunction (ρ j))
    map_add' := by intros; simp [pairingValue, add_mul, Finset.sum_add_distrib, mul_add]
    map_smul' := by intros; simp [pairingValue, mul_assoc, Finset.mul_sum, mul_left_comm]
  }
  have h := congrArg L hc
  simp only [map_sum, map_smul, map_zero] at h
  change ∑ i, c i • pairingValue G (characterAsClassFunction (ρ i))
    (characterAsClassFunction (ρ j)) = 0 at h
  simpa only [character_family_orthonormal ρ hi hne, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

end Characters

theorem character_basis : CharacterBasis.{u,r,v} := by
  intro G _ _ I _ V _ _ ρ hi hne hc
  have : ∀ i, FiniteDimensional ℂ (V i) := fun i =>
    (RegularDecomposition.irreducible_finite G (V i) (ρ i) (hi i)).1
  classical
  let f (i : I) := characterAsClassFunction (ρ i)
  let B := basisOfLinearIndependentOfCardEqFinrank' f (characters_independent ρ hi hne)
    ((class_count G I V ρ hi hne hc).trans (class_function_dimension G).2.symm)
  have hB (i : I) : B i = f i := congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank' f _ _) i
  refine ⟨inferInstance, B, ?_, ?_⟩
  · intro i g
    rw [hB]
    rfl
  · intro i j
    rw [hB, hB]
    exact character_family_orthonormal ρ hi hne i j

theorem completeness_theorem : CompletenessTheorem.{u,w} := by
  intro G _ _
  classical
  obtain ⟨s, hs, hi, hne, hc, hu, _, _⟩ := RegularDecomposition.regular_theorem.{u,w} G
  let ρ (i : s) := i.val.toRepresentation
  have hirr : ∀ i, Representation.IsIrreducible (ρ i) := fun i => hi i.val i.property
  have hneq : ∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j)) := by
    intro i j hij
    exact hne i.property j.property (fun h => hij (Subtype.ext h))
  refine ⟨s, hs, hi, hne, hu,
    class_count G s (fun i : s => i.val.toSubmodule) ρ hirr hneq hc,
    ?_⟩
  obtain ⟨B, hB, hO⟩ :=
    (character_basis G s (fun i : s => i.val.toSubmodule) ρ hirr hneq hc).2
  refine ⟨B, hB, fun i j => ?_⟩
  by_cases h : i = j
  · simpa only [if_pos h] using hO i j
  · simpa only [if_neg h] using hO i j

end
end D07.Ch21.CharacterCompleteness
