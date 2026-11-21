import Mathlib.GroupTheory.IsPerfect
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.HopfFormula

namespace ALG02GroupTheory.Extensions.CentralPresentation.Spec

open _root_.ALG02GroupTheory.HopfFormula (denominator numerator PresentationQuotient
  toKernelQuotient)
open _root_.ALG02GroupTheory.IntegralBar (homology)
open _root_.ALG02GroupTheory.BarProjectionKernel (KernelQuotient)

universe u v w

variable {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]

/-- The group `[F,F]/[F,R]` attached to the specified presentation. -/
abbrev PresentationGroup (S : GroupExtension R F G) :=
  commutator F ⧸ (denominator S.inl.range).subgroupOf (commutator F)

set_option linter.checkUnivs false in
def PresentationGroupType :=
  ∀ {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G],
    GroupExtension R F G → Type v

/-- The map on the quotient induced by the restriction of the presentation projection. -/
def projection (S : GroupExtension R F G) : PresentationGroup S →* G :=
  QuotientGroup.lift _ (S.rightHom.comp (commutator F).subtype) (by
    intro x hx
    change (x : F) ∈ S.rightHom.ker
    rw [← S.range_inl_eq_ker_rightHom]
    exact Subgroup.commutator_le_right (⊤ : Subgroup F) S.inl.range hx)

set_option linter.checkUnivs false in
def ProjectionType :=
  ∀ {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]
    (S : GroupExtension R F G), PresentationGroup S →* G

/-- The inclusion induced by the inclusion of `R ∩ [F,F]` into `[F,F]`. -/
def kernelInclusion (S : GroupExtension R F G) :
    PresentationQuotient S.inl.range →* PresentationGroup S :=
  QuotientGroup.quotientMapSubgroupOfOfLe
    (le_rfl : denominator S.inl.range ≤ denominator S.inl.range)
    (inf_le_right : numerator S.inl.range ≤ commutator F)

set_option linter.checkUnivs false in
def KernelInclusionType :=
  ∀ {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]
    (S : GroupExtension R F G), PresentationQuotient S.inl.range →* PresentationGroup S

def ProjectionSurjective : Prop :=
  ∀ {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]
    [Group.IsPerfect G] (S : GroupExtension R F G), Function.Surjective (projection S)

def ProjectionCentral : Prop :=
  ∀ {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]
    (S : GroupExtension R F G), (projection S).ker ≤ Subgroup.center (PresentationGroup S)

def PresentationPerfect : Prop :=
  ∀ {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]
    [Group.IsPerfect G] (S : GroupExtension R F G), Group.IsPerfect (PresentationGroup S)

/-- The equivalence with the actual kernel is induced by relator representatives. -/
def KernelIdentification : Prop :=
  ∀ {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]
    (S : GroupExtension R F G),
    ∃ e : PresentationQuotient S.inl.range ≃* (projection S).ker,
      ∀ x, (e x).val = kernelInclusion S x

/-- On second integral homology the same identification is composed with
the Hopf isomorphism, with the sign specified by the five-term sequence. -/
def HomologyKernelIdentification : Prop :=
  ∀ {R F G : Type u} [Group R] [Group F] [Group G] [IsFreeGroup F]
    (S : GroupExtension R F G),
    ∃ (e : Multiplicative (homology G 2) ≃* (projection S).ker)
      (hopf : Multiplicative (homology G 2) ≃* PresentationQuotient S.inl.range)
      (d : Multiplicative (homology G 2) →* KernelQuotient S),
      _root_.ALG02GroupTheory.FiveTerm.Spec.IsSignedTransgression S d ∧
      ∀ x, toKernelQuotient S (hopf x) = d x ∧ (e x).val = kernelInclusion S (hopf x)

end ALG02GroupTheory.Extensions.CentralPresentation.Spec
