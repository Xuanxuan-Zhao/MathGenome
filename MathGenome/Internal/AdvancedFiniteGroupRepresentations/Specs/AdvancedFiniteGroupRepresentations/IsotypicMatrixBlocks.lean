import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorEvaluation
import Mathlib.Algebra.Algebra.Pi

/-! FR-D04, the block argument in lines 1428–1459.  The blocks below are
specified by their action on the canonical evaluation vectors f(v).  Only
nonzero multiplicity spaces index the products.  No centralizer assertion,
semisimplicity assertion, or matrix decomposition is a hypothesis. -/
noncomputable section
open scoped TensorProduct DirectSum BigOperators
open Classical
universe u v
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Linear extension of the actual family of inherited Specht actions. -/
def spechtFamilyAlgebraMap {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)) :
    GroupAlgebra n →ₐ[ℂ] ∀ p : Partition n, Module.End ℂ (SpechtModule p) :=
  AlgHom.pi (fun p => (σ p).asAlgebraHom)

def spechtFamilyAlgebraMapType := ∀ {n : ℕ}
  (_σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)),
  GroupAlgebra n →ₐ[ℂ] ∀ p : Partition n, Module.End ℂ (SpechtModule p)

def spechtFamilyAlgebraMap_bijectiveType : Prop := ∀ {n : ℕ}
  (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)),
  (∀ p, InheritedSpechtAction p (σ p)) → Function.Bijective (spechtFamilyAlgebraMap σ)

def spechtFamilyAlgebra_isomorphismType : Prop := ∀ {n : ℕ}
  (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)),
  (∀ p, InheritedSpechtAction p (σ p)) →
  ∃ e : GroupAlgebra n ≃ₐ[ℂ] ∀ p : Partition n, Module.End ℂ (SpechtModule p),
    e.toAlgHom = spechtFamilyAlgebraMap σ

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- The zero summands are omitted from the indexing set, including when X=0. -/
abbrev ActivePartition (n : ℕ) := {p : Partition n // Nontrivial (TensorMultiplicity V p)}

/-- An independent first-factor family, specified on evaluation vectors. -/
def ActsOnFirstFactors {n : ℕ}
    (F : ∀ p : ActivePartition V n, Module.End ℂ (SpechtModule p.val))
    (T : Module.End ℂ (TensorPower V n)) : Prop :=
  ∀ (p : Partition n) (v : SpechtModule p) (f : TensorMultiplicity V p),
    T (f.val v) = if h : Nontrivial (TensorMultiplicity V p) then
      f.val (F ⟨p, h⟩ v) else 0

/-- An independent second-factor family, specified on evaluation vectors. -/
def ActsOnSecondFactors {n : ℕ}
    (F : ∀ p : ActivePartition V n, Module.End ℂ (TensorMultiplicity V p.val))
    (T : Module.End ℂ (TensorPower V n)) : Prop :=
  ∀ (p : Partition n) (v : SpechtModule p) (f : TensorMultiplicity V p),
    T (f.val v) = if h : Nontrivial (TensorMultiplicity V p) then
      (F ⟨p, h⟩ f).val v else 0

private theorem inactive_evaluation {n : ℕ} (p : Partition n)
    (h : ¬ Nontrivial (TensorMultiplicity V p)) (f : TensorMultiplicity V p)
    (v : SpechtModule p) : f.val v = 0 := by
  have : Subsingleton (TensorMultiplicity V p) := not_nontrivial_iff_subsingleton.mp h
  have hf : f = 0 := Subsingleton.elim _ _
  rw [hf]
  rfl

/-- Concrete first-factor block algebra, transported by evaluation. -/
def firstFactorBlocks (n : ℕ) : Subalgebra ℂ (Module.End ℂ (TensorPower V n)) where
  carrier := {T | ∃ F, ActsOnFirstFactors V F T}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro p v f
    dsimp
    split <;> simp
  one_mem' := by
    refine ⟨1, ?_⟩
    intro p v f
    dsimp
    split
    · rfl
    · next h => exact inactive_evaluation V p h f v
  add_mem' := by
    rintro T U ⟨F, hF⟩ ⟨G, hG⟩
    refine ⟨F + G, ?_⟩
    intro p v f
    change T (f.val v) + U (f.val v) = _
    rw [hF, hG]
    dsimp
    split <;> simp
  mul_mem' := by
    rintro T U ⟨F, hF⟩ ⟨G, hG⟩
    refine ⟨F * G, ?_⟩
    intro p v f
    change T (U (f.val v)) = _
    rw [hG]
    dsimp
    split
    · next h => simpa [h, Pi.mul_apply, Module.End.mul_apply] using hF p (G ⟨p, h⟩ v) f
    · exact map_zero T
  algebraMap_mem' := by
    intro c
    refine ⟨algebraMap ℂ _ c, ?_⟩
    intro p v f
    change c • f.val v = _
    dsimp
    split
    · simp
    · next h => simp [inactive_evaluation V p h f v]

/-- Concrete second-factor block algebra, with the same omitted zero summands. -/
def secondFactorBlocks (n : ℕ) : Subalgebra ℂ (Module.End ℂ (TensorPower V n)) where
  carrier := {T | ∃ F, ActsOnSecondFactors V F T}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro p v f
    dsimp
    split <;> rfl
  one_mem' := by
    refine ⟨1, ?_⟩
    intro p v f
    dsimp
    split
    · rfl
    · next h => exact inactive_evaluation V p h f v
  add_mem' := by
    rintro T U ⟨F, hF⟩ ⟨G, hG⟩
    refine ⟨F + G, ?_⟩
    intro p v f
    change T (f.val v) + U (f.val v) = _
    rw [hF, hG]
    dsimp
    split <;> simp
  mul_mem' := by
    rintro T U ⟨F, hF⟩ ⟨G, hG⟩
    refine ⟨F * G, ?_⟩
    intro p v f
    change T (U (f.val v)) = _
    rw [hG]
    dsimp
    split
    · next h => simpa [h, Pi.mul_apply, Module.End.mul_apply] using hF p v (G ⟨p, h⟩ f)
    · exact map_zero T
  algebraMap_mem' := by
    intro c
    refine ⟨algebraMap ℂ _ c, ?_⟩
    intro p v f
    change c • f.val v = _
    dsimp
    split
    · rfl
    · next h => simp [inactive_evaluation V p h f v]

def ActivePartitionType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V], ℕ → Type
def ActsOnFirstFactorsType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] {n : ℕ},
  (∀ p : ActivePartition V n, Module.End ℂ (SpechtModule p.val)) →
    Module.End ℂ (TensorPower V n) → Prop
def ActsOnSecondFactorsType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] {n : ℕ},
  (∀ p : ActivePartition V n, Module.End ℂ (TensorMultiplicity V p.val)) →
    Module.End ℂ (TensorPower V n) → Prop
def firstFactorBlocksType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
  Subalgebra ℂ (Module.End ℂ (TensorPower V n))
def secondFactorBlocksType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
  Subalgebra ℂ (Module.End ℂ (TensorPower V n))

/-- Realizability asserts the independence of all blocks, not just containment. -/
def firstFactorBlocks_realizeType : Prop := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (n : ℕ)
  (F : ∀ p : ActivePartition V n, Module.End ℂ (SpechtModule p.val)),
  ∃! T : Module.End ℂ (TensorPower V n), ActsOnFirstFactors V F T

def secondFactorBlocks_realizeType : Prop := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (n : ℕ)
  (F : ∀ p : ActivePartition V n, Module.End ℂ (TensorMultiplicity V p.val)),
  ∃! T : Module.End ℂ (TensorPower V n), ActsOnSecondFactors V F T

def tensorA_eq_firstFactorBlocksType : Prop := ∀ (V : Type u)
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
  tensorA V n = firstFactorBlocks V n

def firstFactorBlocks_centralizerType : Prop := ∀ (V : Type u)
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
  Subalgebra.centralizer ℂ (firstFactorBlocks V n : Set _) = secondFactorBlocks V n

def secondFactorBlocks_centralizerType : Prop := ∀ (V : Type u)
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
  Subalgebra.centralizer ℂ (secondFactorBlocks V n : Set _) = tensorA V n

/-- Rank-one/matrix-unit form of the tensor centralizer bridge. -/
def tensor_firstFactor_centralizerType : Prop :=
  ∀ (X : Type u) (Y : Type v) [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    [AddCommGroup Y] [Module ℂ Y] (T : Module.End ℂ (X ⊗[ℂ] Y)),
    (∀ a : Module.End ℂ X, Commute (TensorProduct.map a (1 : Module.End ℂ Y)) T) →
    ∃ b : Module.End ℂ Y, T = TensorProduct.map (1 : Module.End ℂ X) b

def tensor_secondFactor_centralizerType : Prop :=
  ∀ (X : Type u) (Y : Type v) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [Nontrivial Y] (T : Module.End ℂ (X ⊗[ℂ] Y)),
    (∀ b : Module.End ℂ Y, Commute (TensorProduct.map (1 : Module.End ℂ X) b) T) →
    ∃ a : Module.End ℂ X, T = TensorProduct.map a (1 : Module.End ℂ Y)

/-- Orthogonal block projectors, including the zero projectors on omitted summands. -/
def isotypicProjectorsType : Prop := ∀ (V : Type u)
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
  ∃ P : Partition n → Module.End ℂ (TensorPower V n),
    (∀ p, P p ∈ firstFactorBlocks V n ∧ P p ∈ secondFactorBlocks V n) ∧
    (∀ (p q : Partition n) (v : SpechtModule q) (f : TensorMultiplicity V q),
      P p (f.val v) = if q = p then f.val v else 0) ∧
    (∀ p q, P p * P q = if p = q then P p else 0) ∧
    (∑ p, P p) = 1 ∧
    (∀ p, ¬ Nontrivial (TensorMultiplicity V p) → P p = 0)

end Specs.AdvancedFiniteGroupRepresentations
