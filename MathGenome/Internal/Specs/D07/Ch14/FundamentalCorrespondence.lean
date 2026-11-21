import MathGenome.Internal.Specs.D07.Ch14.FixedField

/-!
Independent specification of K07.14.fundamental_correspondence
(paper.tex:4165–4174; chapters/M07.14.tex:83–92).

The chosen `Algebra K L` is the specified embedding. Finite degree is
`FiniteDimensional K L`; `IsGalois K L` means normal and algebraically
separable, as in the source and the upstream interfaces. All intermediate
fields and all subgroups occur, including the endpoints and trivial group.
The maps below are the canonical upstream constructions, whose carriers are
the pointwise fixing predicates. The order dual expresses inclusion reversal.
No normality of a subgroup or of an intermediate extension over K is required.
-/

universe u v

namespace Specs.D07.Ch14.FundamentalCorrespondence

/-- Taking the fixed field of the pointwise fixing subgroup recovers E. -/
def FixedFieldFixingSubgroup : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (E : IntermediateField K L),
    FixedField.fixedFieldValue K L (FixedField.fixingSubgroupValue K L E) = E

/-- Taking the fixing subgroup of the fixed field recovers every H. -/
def FixingSubgroupFixedField : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)),
    FixedField.fixingSubgroupValue K L (FixedField.fixedFieldValue K L H) = H

/-- Both specified assignments are bijections and reverse inclusion. -/
def AntitoneBijections : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    Function.Bijective (FixedField.fixingSubgroupValue K L) ∧
      Function.Bijective (FixedField.fixedFieldValue K L) ∧
      Antitone (FixedField.fixingSubgroupValue K L) ∧
      Antitone (FixedField.fixedFieldValue K L)

/-- The inverse inclusion-reversing correspondence uses exactly the two
source assignments in both directions, rather than an unrelated bijection. -/
def OrderCorrespondence : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    ∃ e : IntermediateField K L ≃o (Subgroup (L ≃ₐ[K] L))ᵒᵈ,
      (∀ E, OrderDual.ofDual (e E) = FixedField.fixingSubgroupValue K L E) ∧
      ∀ H, e.symm (OrderDual.toDual H) = FixedField.fixedFieldValue K L H

end Specs.D07.Ch14.FundamentalCorrespondence
