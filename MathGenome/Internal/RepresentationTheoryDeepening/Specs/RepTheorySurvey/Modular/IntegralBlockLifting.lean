import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.GroupAlgebraReduction
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.ModularBlocks

/-! Independent specifications for central reduction and integral block lifting. -/

namespace RepTheorySurvey.Modular.MR08IntegralSpec

universe uO uG uK uI

set_option linter.checkUnivs false

local notation "Z[" R "," G "]" => Subalgebra.center R (MonoidAlgebra R G)

def centerReductionType :=
  (O : Type uO) → [CommRing O] → (G : Type uG) → [Group G] → [IsLocalRing O] →
    Z[O,G] →+* Z[IsLocalRing.ResidueField O,G]

/-- Coefficient reduction restricted to the centers. -/
noncomputable def centerReductionValue : centerReductionType.{uO, uG} :=
  fun O _ G _ _ =>
    ((MR01Spec.reductionValue O G).comp (Subalgebra.center O (MonoidAlgebra O G)).val.toRingHom).codRestrict
      (Subalgebra.center (IsLocalRing.ResidueField O) (MonoidAlgebra (IsLocalRing.ResidueField O) G))
      fun z => z.property.map (f := MR01Spec.reductionValue O G)
        (MonoidAlgebra.map_surjective _ IsLocalRing.residue_surjective)

def centerUniformizerIdealType :=
  (O : Type uO) → [CommRing O] → (G : Type uG) → [Group G] → O → Ideal Z[O,G]

/-- The scalar principal ideal in the integral center. -/
noncomputable def centerUniformizerIdealValue : centerUniformizerIdealType.{uO, uG} :=
  fun O _ G _ t => Ideal.span {algebraMap O Z[O,G] t}

def reductionSurjectiveType : Prop :=
  ∀ (O : Type uO) [CommRing O] (G : Type uG) [Group G] [Finite G] [IsLocalRing O],
    Function.Surjective (centerReductionValue O G)

def memUniformizerIdealPowType : Prop :=
  ∀ (O : Type uO) [CommRing O] (G : Type uG) [Group G] [Finite G]
    (t : O) (n : ℕ) (z : Z[O,G]),
    z ∈ centerUniformizerIdealValue O G t ^ n ↔
      z.val ∈ MRGroupAlgebraReductionSpec.uniformizerIdealValue O G t ^ n

def reductionKernelType : Prop :=
  ∀ (O : Type uO) [CommRing O] (G : Type uG) [Group G] [Finite G]
    {p : ℕ} {K : Type uK} [Field K] [Algebra O K] [IsDomain O] [IsDiscreteValuationRing O]
    (S : MR01Spec.SplittingSystemData G p O K),
    RingHom.ker (centerReductionValue O G) = centerUniformizerIdealValue O G S.uniformizer

def completeSeparatedType : Prop :=
  ∀ (O : Type uO) [CommRing O] (G : Type uG) [Group G] [Finite G]
    {p : ℕ} {K : Type uK} [Field K] [Algebra O K] [IsDomain O] [IsDiscreteValuationRing O]
    (S : MR01Spec.SplittingSystemData G p O K),
    IsAdicCompleteSeparated (centerUniformizerIdealValue O G S.uniformizer)

def reductionQuotientType : Prop :=
  ∀ (O : Type uO) [CommRing O] (G : Type uG) [Group G] [Finite G]
    {p : ℕ} {K : Type uK} [Field K] [Algebra O K] [IsDomain O] [IsDiscreteValuationRing O]
    (S : MR01Spec.SplittingSystemData G p O K),
    ∃ e : (Z[O,G] ⧸ centerUniformizerIdealValue O G S.uniformizer) ≃+*
        Z[IsLocalRing.ResidueField O,G],
      ∀ z, e (Ideal.Quotient.mk (centerUniformizerIdealValue O G S.uniformizer) z) =
        centerReductionValue O G z

def centralIdempotentLiftType : Prop :=
  ∀ (O : Type uO) [CommRing O] (G : Type uG) [Group G] [Finite G]
    {p : ℕ} {K : Type uK} [Field K] [Algebra O K] [IsDomain O] [IsDiscreteValuationRing O]
    (_S : MR01Spec.SplittingSystemData G p O K)
    (e : Z[IsLocalRing.ResidueField O,G]), IsIdempotentElem e →
    ∃! b : Z[O,G], IsIdempotentElem b ∧ centerReductionValue O G b = e

def orthogonalityType : Prop :=
  ∀ (O : Type uO) [CommRing O] (G : Type uG) [Group G] [Finite G]
    {p : ℕ} {K : Type uK} [Field K] [Algebra O K] [IsDomain O] [IsDiscreteValuationRing O]
    (_S : MR01Spec.SplittingSystemData G p O K) {a b : Z[O,G]},
    IsIdempotentElem a → IsIdempotentElem b →
    (centerReductionValue O G a * centerReductionValue O G b = 0 ↔ a * b = 0)

def sumOneType : Prop :=
  ∀ (O : Type uO) [CommRing O] (G : Type uG) [Group G] [Finite G]
    {p : ℕ} {K : Type uK} [Field K] [Algebra O K] [IsDomain O] [IsDiscreteValuationRing O]
    (_S : MR01Spec.SplittingSystemData G p O K)
    {ι : Type uI} (b : ι → Z[O,G]) (s : Finset ι),
    (∀ i, IsIdempotentElem (b i)) →
    Pairwise (fun i j => centerReductionValue O G (b i) * centerReductionValue O G (b j) = 0) →
    ((∑ i ∈ s, centerReductionValue O G (b i)) = 1 ↔ (∑ i ∈ s, b i) = 1)

def blockReductionEquivType : Prop :=
  ∀ (O : Type uO) [CommRing O] (G : Type uG) [Group G] [Finite G]
    {p : ℕ} {K : Type uK} [Field K] [Algebra O K] [IsDomain O] [IsDiscreteValuationRing O]
    (_S : MR01Spec.SplittingSystemData G p O K),
    ∃ e : BlockIdempotent O G ≃ BlockIdempotent (IsLocalRing.ResidueField O) G,
      ∀ b, (e b).1 = centerReductionValue O G b.1

def integralBlockDecompositionType : Prop :=
  ∀ (O : Type uO) [CommRing O] (G : Type uG) [Group G] [Finite G]
    {p : ℕ} {K : Type uK} [Field K] [Algebra O K] [IsDomain O] [IsDiscreteValuationRing O]
    (_S : MR01Spec.SplittingSystemData G p O K),
    ∃ s : Finset (BlockIdempotent O G), (∀ b, b ∈ s) ∧
      (∑ b ∈ s, b.element) = 1 ∧
      Pairwise (fun b c : BlockIdempotent O G => b.element * c.element = 0)

end RepTheorySurvey.Modular.MR08IntegralSpec
