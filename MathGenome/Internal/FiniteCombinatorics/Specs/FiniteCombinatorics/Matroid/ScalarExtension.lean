import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.VectorRepresentation
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! Scalar extension in paper.tex W71. The algebra structure records the chosen
field embedding. There is no finiteness assumption on the ambient vector space.
The tensor family has the very same indices, including zero or repeated columns.
-/
namespace FiniteCombinatorics.Matroid.Expected
open Set Submodule
open scoped TensorProduct
universe u v w z

/-- Independence is preserved and reflected, even for arbitrary index families. -/
def scalarExtensionLinearIndepOn : Prop :=
  ∀ {α : Type u} (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L]
    {V : Type z} [AddCommGroup V] [Module K V] (v : α → V) (I : Set α),
    LinearIndepOn L (fun e => (1 : L) ⊗ₜ[K] v e) I ↔ LinearIndepOn K v I

def scalarExtensionMatroid : Prop :=
  ∀ {α : Type u} (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L]
    {V : Type z} [AddCommGroup V] [Module K V]
    (E : Set α) (hE : E.Finite) (v : α → V),
    vectorMatroid L E hE (fun e => (1 : L) ⊗ₜ[K] v e) = vectorMatroid K E hE v

def scalarExtensionRank : Prop :=
  ∀ {α : Type u} (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L]
    {V : Type z} [AddCommGroup V] [Module K V]
    (E : Set α) (hE : E.Finite) (v : α → V) (A : Set α), A ⊆ E →
    rank (vectorMatroid L E hE (fun e => (1 : L) ⊗ₜ[K] v e)) A =
      rank (vectorMatroid K E hE v) A

/-- The dimensions here are those of finite spans, not of the ambient spaces. -/
def scalarExtensionSpanDimension : Prop :=
  ∀ {α : Type u} (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L]
    {V : Type z} [AddCommGroup V] [Module K V]
    (E : Set α) (hE : E.Finite) (v : α → V) (A : Set α), A ⊆ E →
    Module.finrank L (span L ((fun e => (1 : L) ⊗ₜ[K] v e) '' A)) =
      Module.finrank K (span K (v '' A))

def scalarExtensionRepresents : Prop :=
  ∀ {α : Type u} (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L]
    {V : Type z} [AddCommGroup V] [Module K V]
    (M : _root_.Matroid α) (v : α → V), Represents K M v →
    Represents L M (fun e => (1 : L) ⊗ₜ[K] v e)

/-- Every unital homomorphism of fields is injective; its own algebra structure
is used in the tensor product, so this statement covers every chosen embedding. -/
def scalarExtensionAlong : Prop :=
  ∀ {α : Type u} (K : Type v) (L : Type w) [Field K] [Field L] (ι : K →+* L)
    {V : Type z} [AddCommGroup V] [Module K V]
    (E : Set α) (hE : E.Finite) (v : α → V),
    letI : Algebra K L := ι.toAlgebra
    algebraMap K L = ι ∧
    vectorMatroid L E hE (fun e => (1 : L) ⊗ₜ[K] v e) = vectorMatroid K E hE v ∧
    ∀ A, A ⊆ E →
      rank (vectorMatroid L E hE (fun e => (1 : L) ⊗ₜ[K] v e)) A =
        rank (vectorMatroid K E hE v) A

end FiniteCombinatorics.Matroid.Expected
