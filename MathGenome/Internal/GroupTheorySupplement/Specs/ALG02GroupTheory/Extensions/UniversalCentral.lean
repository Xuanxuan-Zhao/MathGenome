import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.Central
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.CentralPresentation

/-! Independent statements for the universal central extension theorem. -/

namespace ALG02GroupTheory.Extensions.UniversalCentral.Spec

open _root_.Specs.ALG02GroupTheory.Extensions
open CentralPresentation.Spec (PresentationGroup projection kernelInclusion)
open HopfFormula (PresentationQuotient toKernelQuotient)
open BarProjectionKernel (KernelQuotient)
open IntegralBar (homology)

universe u v w t u' v' t'

/-- The presentation quotient has the unique map over the base to each central extension. -/
def PresentationUniqueHom : Prop :=
  ∀ {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]
    [IsFreeGroup F] [Group.IsPerfect G] (S : GroupExtension R F G)
    {K : Type u'} {D : Type v'} [Group K] [Group D] (T : GroupExtension K D G),
    isCentralExtensionValue T →
      ∃! f : PresentationGroup S →* D, T.rightHom.comp f = projection S

/-- The middle group and the base of any universal central extension are perfect. -/
def PerfectOfUniversal : Prop :=
  ∀ {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]
    {S : GroupExtension N E G}, isUniversalCentralExtensionValue.{u, v, w, t} S →
      Group.IsPerfect E ∧ Group.IsPerfect G

/-- The comparison of two universal central extensions is an isomorphism over the fixed base. -/
def UniversalComparison : Prop :=
  ∀ {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]
    {S : GroupExtension N E G} {K : Type u'} {D : Type v'} [Group K] [Group D]
    {T : GroupExtension K D G}, isUniversalCentralExtensionValue.{u, v, w, t} S →
      isUniversalCentralExtensionValue.{u', v', w, t'} T →
      ∃! e : E ≃* D, T.rightHom.comp e.toMonoidHom = S.rightHom

/-- A universal central extension exists precisely for a perfect group. -/
def ExistsUniversalIffPerfect : Prop :=
  ∀ (G : Type w) [Group G],
    (∃ (N E : Type w) (_ : Group N) (_ : Group E) (S : GroupExtension N E G),
      isUniversalCentralExtensionValue.{w, w, w, t} S) ↔ Group.IsPerfect G

/-- The free presentation on the elements of the base group. -/
def freePresentation (G : Type w) [Group G] :
    GroupExtension (FreeGroup.lift (id : G → G)).ker (FreeGroup G) G where
  inl := (FreeGroup.lift (id : G → G)).ker.subtype
  rightHom := FreeGroup.lift id
  inl_injective := Subtype.val_injective
  range_inl_eq_ker_rightHom := Subgroup.range_subtype _
  rightHom_surjective := FreeGroup.lift_surjective_of_surjective Function.surjective_id

/-- Identify the actual kernel by the signed Hopf map for the free presentation
on the base, followed by the comparison over the base. -/
def KernelIdentifiedByHopf {N : Type u} {E : Type v} {G : Type w}
    [Group N] [Group E] [Group G] (S : GroupExtension N E G) : Prop :=
  let P := freePresentation G
  ∃ (e : Multiplicative (homology G 2) ≃* S.rightHom.ker)
    (comparison : PresentationGroup P ≃* E)
    (hopf : Multiplicative (homology G 2) ≃* PresentationQuotient P.inl.range)
    (d : Multiplicative (homology G 2) →* KernelQuotient P),
    S.rightHom.comp comparison.toMonoidHom = projection P ∧
    FiveTerm.Spec.IsSignedTransgression P d ∧
    ∀ x, toKernelQuotient P (hopf x) = d x ∧
      (e x).val = comparison (kernelInclusion P (hopf x))

/-- The kernel of any universal central extension is canonically second integral homology. -/
def UniversalKernelHomology : Prop :=
  ∀ {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]
    {S : GroupExtension N E G}, isUniversalCentralExtensionValue.{u, v, w, t} S →
      KernelIdentifiedByHopf S

/-- The exact extension uses the specified inclusion and projection on the presentation
quotient. Its homology kernel identification comes from Hopf's formula. -/
def UniversalPresentation : Prop :=
  ∀ {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]
    [IsFreeGroup F] [Group.IsPerfect G] (S : GroupExtension R F G),
    ∃ U : GroupExtension (PresentationQuotient S.inl.range) (PresentationGroup S) G,
      U.inl = kernelInclusion S ∧ U.rightHom = projection S ∧
      isUniversalCentralExtensionValue.{v, v, w, t} U ∧
      Group.IsPerfect (PresentationGroup S) ∧
      KernelIdentifiedByHopf U

end ALG02GroupTheory.Extensions.UniversalCentral.Spec
