import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
Independent specification for the extension conventions and splitting criterion in
paper.tex:313–321, the section normalization in 325–327, and the fixed-end maps in 382–386.
The end maps are the prescribed maps of a short exact sequence.
-/

namespace Specs.ALG02GroupTheory.Extensions

universe u v w v'

-- The independent expected types quantify over groups in separate universes.
set_option linter.checkUnivs false

def NormalizedSectionType :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q],
    GroupExtension N E Q → Type (max v w)

def normalizedSectionValue : NormalizedSectionType.{u, v, w} :=
  fun S => {s : S.Section // s 1 = 1}

def IsComplementType :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q],
    GroupExtension N E Q → Subgroup E → Prop

open scoped Pointwise

def isComplementValue : IsComplementType.{u, v, w} :=
  fun {_ E _} _ _ _ S H => (S.inl.range : Set E) * (H : Set E) = Set.univ ∧ S.inl.range ⊓ H = ⊥

def IsExtensionMapType :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    {E' : Type v'} [Group E'],
    GroupExtension N E Q → GroupExtension N E' Q → (E →* E') → Prop

def isExtensionMapValue : IsExtensionMapType.{u, v, w, v'} :=
  fun S T f => f.comp S.inl = T.inl ∧ T.rightHom.comp f = S.rightHom

def AbelianKernelExtensionType :=
  ∀ (A : Type u) (E : Type v) (Q : Type w) [AddCommGroup A] [Group E] [Group Q],
    Type (max u v w)

def abelianKernelExtensionValue : AbelianKernelExtensionType.{u, v, w} :=
  fun A E Q _ _ _ => GroupExtension (Multiplicative A) E Q

def NormalizedSectionExists : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q), Nonempty (normalizedSectionValue S)

def ComplementProjectionBijective : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) {H : Subgroup E},
    isComplementValue S H → Function.Bijective (S.rightHom.domRestrict H)

/-- Both maps of the correspondence are specified by their values. -/
def SplittingsCorrespondToComplements : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q),
    ∃ e : S.Splitting ≃ {H : Subgroup E // isComplementValue S H},
      (∀ s : S.Splitting, (e s).val = s.toMonoidHom.range) ∧
      (∀ H : {H : Subgroup E // isComplementValue S H},
        (∀ q : Q, e.symm H q ∈ H.val) ∧
        (∀ h : H.val, e.symm H (S.rightHom h) = (h : E)))

/-- The isomorphism has the given middle homomorphism as its underlying map. -/
def FixedEndMapIsEquivalence : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    {E' : Type v'} [Group E']
    {S : GroupExtension N E Q} {T : GroupExtension N E' Q} (f : E →* E'),
    isExtensionMapValue S T f → ∃ e : S.Equiv T, e.toMulEquiv.toMonoidHom = f

end Specs.ALG02GroupTheory.Extensions
