import MathGenome.Internal.Specs.D05.M02.Subspace
import MathGenome.Internal.Specs.D05.M12.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
Independent statements for K05.12.orthogonal_complement, paper.tex:2002–2012.
The paper's complement is Mathlib's `Submodule.orthogonal`: its defining
`inner F u v` is exactly `D05.firstInner v u`. All subspaces are arbitrary;
neither finite dimension, closedness, nor completeness is assumed.
-/

namespace Specs.D05.M12.OrthogonalComplement

universe u v

/-- The complement is a subspace of the same ambient inner-product space. -/
def orthogonalComplement_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → Submodule F V → Submodule F V

/-- Reuse the canonical submodule rather than introducing a second complement. -/
def orthogonalComplement_value : orthogonalComplement_type.{u, v} :=
  fun U => U.orthogonal

/-- The first-slot-linear set formula, including its quantification over all of U. -/
def mem_orthogonalComplement : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) (v : V),
    v ∈ U.orthogonal ↔ ∀ u ∈ U, _root_.D05.firstInner (F := F) v u = 0

/-- The displayed set is a subspace, with the ambient inherited operations. -/
def orthogonal_is_subspace : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V),
    ∃ P : Submodule F V,
      (P : Set V) = {v | ∀ u ∈ U, _root_.D05.firstInner (F := F) v u = 0}

/-- Positive definiteness makes the intersection exactly the zero subspace. -/
def inf_orthogonal_eq_bot : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V),
    U ⊓ U.orthogonal = ⊥

/-- Only the inclusion is asserted for an arbitrary subspace. -/
def le_double_orthogonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V),
    U ≤ U.orthogonal.orthogonal

end Specs.D05.M12.OrthogonalComplement
