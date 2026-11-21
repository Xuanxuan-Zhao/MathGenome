import MathGenome.Internal.Specs.D07.Ch21.CharacterCompletenessGroupAlgebraProduct
import MathGenome.Internal.Specs.D07.Ch21.CharacterCompletenessCenterClassSumBasis
import Mathlib.Algebra.Group.ConjFinite

/-!
K07.21.character_completeness, paper.tex:6383–6421.
Class functions are actual functions constant on conjugacy classes. A complete
family is nonrepeating and exhaustive among irreducibles, with the upstream
universe-independent completeness bridge. Finite dimension is a conclusion.
The Hermitian pairing is the normalized sum, linear in its first argument.
-/
namespace Specs.D07.Ch21.CharacterCompleteness

universe u r v w
noncomputable section

/-- The full space of complex class functions, including the zero function. -/
def classFunctions (G : Type u) [Group G] : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ x y, IsConj x y → f x = f y}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by intro f k hf hk x y h; exact congrArg₂ (· + ·) (hf x y h) (hk x y h)
  smul_mem' := by intro a f hf x y h; exact congrArg (a • ·) (hf x y h)

/-- Dimension of the entire space, independently of any representation family. -/
def ClassFunctionDimension : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    Module.Finite ℂ (classFunctions G) ∧
      Module.finrank ℂ (classFunctions G) = Nat.card (ConjClasses G)

/-- Every choice of one representative of each irreducible type has this size. -/
def ClassCount : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) →
    RegularDecomposition.IsComplete ρ → Fintype.card I = Nat.card (ConjClasses G)

/-- Basis vectors are exactly the original trace characters. This states both
spanning and orthonormality, and proves finite dimension of all its carriers. -/
def CharacterBasis : Prop := by
  classical
  exact ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) →
    RegularDecomposition.IsComplete ρ →
      (∀ i, Module.Finite ℂ (V i)) ∧
      ∃ B : Module.Basis I ℂ (classFunctions G),
        (∀ i g, (B i : G → ℂ) g = LinearMap.trace ℂ (V i) (ρ i g)) ∧
        ∀ i j, HomPairing.pairingValue G (B i) (B j) = if i = j then 1 else 0

/-- A finite list of actual irreducible representatives exists, exhausts all
irreducibles (in any carrier universe), has one member per conjugacy class,
and its characters form the stated orthonormal basis. -/
def CompletenessTheorem : Prop := by
  classical
  exact ∀ (G : Type u) [Group G] [Fintype G],
    ∃ s : Finset (Subrepresentation (Representation.leftRegular ℂ G)),
      s.Nonempty ∧
      (∀ U ∈ s, Representation.IsIrreducible U.toRepresentation) ∧
      (s : Set (Subrepresentation (Representation.leftRegular ℂ G))).Pairwise
        (fun U W => ¬ Nonempty (U.toRepresentation.Equiv W.toRepresentation)) ∧
      (∀ (W : Type w) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W),
        Representation.IsIrreducible σ →
          Module.Finite ℂ W ∧ ∃ i : s, Nonempty (i.val.toRepresentation.Equiv σ)) ∧
      Fintype.card s = Nat.card (ConjClasses G) ∧
      ∃ B : Module.Basis s ℂ (classFunctions G),
        (∀ i g, (B i : G → ℂ) g =
          LinearMap.trace ℂ i.val.toSubmodule (i.val.toRepresentation g)) ∧
        ∀ i j, HomPairing.pairingValue G (B i) (B j) = if i = j then 1 else 0

end
end Specs.D07.Ch21.CharacterCompleteness
