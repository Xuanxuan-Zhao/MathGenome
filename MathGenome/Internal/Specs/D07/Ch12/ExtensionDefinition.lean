import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Basic.Complex.Basic

/-!
Independent specification for K07.12.extension_definition, paper.tex:3542–3552.
Fields are commutative and nontrivial. An extension retains its chosen unital
structure map; no surjectivity, algebraicity, finite degree, or algebraic
closedness is assumed. The canonical Algebra/Module structures below use exactly
that map. Base embeddings use the two specified Algebra structures, whose maps
can in particular be any two chosen field homomorphisms via `toAlgebra`.
Degree, adjoining elements, and tower degree formulas are separate entries.
-/

universe u v w

namespace Specs.D07.Ch12.ExtensionDefinition

def FieldExtensionType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L], Type (max u v)

def fieldExtensionValue : FieldExtensionType.{u, v} :=
  fun K L _ _ => K →+* L

def ExtensionAlgebraType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L],
    (K →+* L) → Algebra K L

def extensionAlgebraValue : ExtensionAlgebraType.{u, v} :=
  fun _ _ _ _ ι => ι.toAlgebra

/-- Over a field a module is precisely a vector space. The expected value fixes
its scalar action, rather than merely asserting existence of some module. -/
def ExtensionModuleType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L],
    (K →+* L) → Module K L

def extensionModuleValue : ExtensionModuleType.{u, v} :=
  fun _ _ _ _ ι => letI := ι.toAlgebra; Algebra.toModule

def FieldEmbeddingType : Type (max u v w + 1) :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L], Type (max v w)

def fieldEmbeddingValue : FieldEmbeddingType.{u, v, w} :=
  fun K E L _ _ _ _ _ => E →ₐ[K] L

def StructureMapInjective : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    (ι : K →+* L), Function.Injective ι

/-- Both the recovered structure map and scalar multiplication are the specified
ones. The accompanying module definition above supplies all vector-space laws. -/
def InducedScalars : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] (ι : K →+* L),
    letI := ι.toAlgebra
    algebraMap K L = ι ∧ ∀ (a : K) (x : L), a • x = ι a * x

/-- Conversely, no extra extension data are hidden in the Algebra encoding. -/
def RecoverAlgebra : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] (A : Algebra K L),
    letI := A
    (algebraMap K L).toAlgebra = A

/-- The identification with the image is a field isomorphism compatible with
inclusion into L, not an equality between unrelated types. -/
def IdentifyWithImage : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] (ι : K →+* L),
    ∃ e : K ≃+* ι.fieldRange, ∀ a : K, (e a : L) = ι a

/-- This iff checks the exact source definition of a base embedding, including
injectivity and compatibility with both chosen structure maps. -/
def EmbeddingIff : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    (f : E →+* L),
    (∃ σ : E →ₐ[K] L, σ.toRingHom = f) ↔
      Function.Injective f ∧ ∀ a : K, f (algebraMap K E a) = algebraMap K L a

def EmbeddingLaws : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    (σ : E →ₐ[K] L),
    Function.Injective σ ∧
      (∀ a : K, σ (algebraMap K E a) = algebraMap K L a) ∧
      ∀ (a : K) (x : E), σ (a • x) = a • σ x

/-- The scalar action remembers the selected embedding, even with fixed
underlying fields. Testing it on 1 recovers the entire map. -/
def EmbeddingsDetermineScalars : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] (ι κ : K →+* L),
    (ι = κ ↔ ι.toAlgebra = κ.toAlgebra) ∧
    (ι = κ ↔ ∀ (a : K) (x : L), ι a * x = κ a * x)

/-- Identity and conjugation realize different extension data on the same two
abstract fields. This uses only complex arithmetic, not algebraic closedness. -/
def DifferentExtensions : Prop :=
  ∃ ι κ : ℂ →+* ℂ, ι ≠ κ ∧ ι.toAlgebra ≠ κ.toAlgebra

end Specs.D07.Ch12.ExtensionDefinition
