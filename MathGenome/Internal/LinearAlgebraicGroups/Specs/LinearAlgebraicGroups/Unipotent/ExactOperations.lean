import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Criteria
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Flat

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.Unipotent

noncomputable section

variable {k : Type u} [Field k]

/-- A closed subgroup of an affine algebraic group inherits affineness and finite type. -/
def closedSubgroupAlgebraicGroup {G : AffineAlgebraicGroup k} (N : ClosedSubgroup G.val) :
    AffineAlgebraicGroup k := by
  have := N.isClosedImmersion
  have := G.property.1
  have := G.property.2.1
  have := G.property.2.2
  have h := N.inclusion.hom.hom.w
  refine ⟨N.group, isAffine_of_isAffineHom N.inclusion.hom.hom.left, ?_, ?_⟩
  · rw [← h]
    infer_instance
  · rw [← h]
    infer_instance

def ClosedSubgroupsUnipotent : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (N : ClosedSubgroup G.val),
    IsUnipotent G → IsUnipotent (closedSubgroupAlgebraicGroup N)

def FaithfullyFlatQuotientsUnipotent : Prop :=
  ∀ {k : Type u} [Field k] (G Q : AffineAlgebraicGroup k) (p : G.val ⟶ Q.val),
    Flat p.hom.hom.left → Surjective p.hom.hom.left → IsUnipotent G → IsUnipotent Q

def ExtensionsUnipotent : Prop :=
  ∀ {k : Type u} [Field k] (G Q : AffineAlgebraicGroup k) (p : G.val ⟶ Q.val)
    (N : ClosedSubgroup G.val),
    IsSchemeKernel p N → Flat p.hom.hom.left → Surjective p.hom.hom.left →
    IsUnipotent (closedSubgroupAlgebraicGroup N) → IsUnipotent Q → IsUnipotent G

/-- The invariant subspace after restricting a coaction to the scheme kernel of
`Spec B → Spec A`. -/
def kernelInvariants {A B : HopfAlgebraCategory k} (a : A ⟶ B)
    [(kernelIdeal a).IsHopfIdeal k] {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : RightComodule k B V) : Submodule k V :=
  let C := hopfQuotient B (kernelIdeal a)
  let q := (hopfQuotientMap B (kernelIdeal a)).hom.toLinearMap
  LinearMap.ker ((q.lTensor V).comp ρ.coaction - RationalRepresentations.trivialLinearMap C)

/-- For a faithfully flat quotient the kernel invariants carry a quotient coaction.
Its pullback along the quotient map, composed with inclusion, is the ambient coaction
on these vectors. -/
def QuotientActionOnKernelInvariants : Prop :=
  ∀ {k : Type u} [Field k] {A B : HopfAlgebraCategory k} (a : A ⟶ B)
    [(kernelIdeal a).IsHopfIdeal k], a.hom.toAlgHom.toRingHom.FaithfullyFlat →
    ∀ {V : Type u} [AddCommGroup V] [Module k V] (ρ : RightComodule k B V),
      let W := kernelInvariants a ρ
      ∃ σ : RightComodule k A W,
        ((W.subtype.rTensor B).comp (a.hom.toLinearMap.lTensor W)).comp σ.coaction =
          ρ.coaction.comp W.subtype

/-- The base-changed group with its inherited affineness and finite type. -/
def baseChangedAlgebraicGroup (K : Type u) [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) : AffineAlgebraicGroup K := by
  let g := fieldSpecMap k K
  let H := (groupBaseChange k K).obj G.val
  have : IsAffine G.val.X.left := G.property.1
  have : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  have : QuasiCompact G.val.X.hom := G.property.2.2
  exact ⟨H, inferInstanceAs (IsAffine (Limits.pullback G.val.X.hom g)),
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.val.X.hom g)),
    inferInstanceAs (QuasiCompact (Limits.pullback.snd G.val.X.hom g))⟩

def UnipotenceFieldExtension : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] (G : AffineAlgebraicGroup k),
    IsUnipotent (baseChangedAlgebraicGroup K G) ↔ IsUnipotent G

end

end LinearAlgebraicGroups.Specs.Unipotent
