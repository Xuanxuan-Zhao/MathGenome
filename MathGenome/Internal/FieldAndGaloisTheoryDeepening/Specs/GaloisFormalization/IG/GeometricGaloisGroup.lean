import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.RationalConstantFields

namespace GaloisFormalization.IG.Specs

open IntermediateField

universe u v

set_option linter.checkUnivs false in
def isRegularOverType : Type (max (u + 1) (v + 1)) :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L], Prop

/-- Regularity means that every element of the extension algebraic over the
constant field lies in the image of that field. -/
def isRegularOver (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] : Prop :=
  algebraicClosure k L = ⊥

set_option linter.checkUnivs false in
/-- The domain and codomain of restriction from the geometric group. -/
def geometricRestrictionType : Type (max (u + 1) (v + 1)) :=
  ∀ {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω]
    (t : Ω) (L : IntermediateField (adjoin k {t}) Ω) [IsGalois (adjoin k {t}) L],
    let B := rationalWithConstants t (algebraicClosure k Ω)
    let P := L ⊔ B
    letI : Algebra B P := (inclusion le_sup_right).toAlgebra
    (P ≃ₐ[B] P) →* (L ≃ₐ[adjoin k {t}] L)

/-- Restrict the action on the compositum to its normal subfield `L`. -/
noncomputable def geometricRestriction {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω]
    (t : Ω) (L : IntermediateField (adjoin k {t}) Ω) [IsGalois (adjoin k {t}) L] :
    let B := rationalWithConstants t (algebraicClosure k Ω)
    let P := L ⊔ B
    letI : Algebra B P := (inclusion le_sup_right).toAlgebra
    (P ≃ₐ[B] P) →* (L ≃ₐ[adjoin k {t}] L) := by
  dsimp only
  let K := adjoin k {t}
  let B := rationalWithConstants t (algebraicClosure k Ω)
  let P := L ⊔ B
  letI : Algebra B P := (inclusion le_sup_right).toAlgebra
  letI : Algebra L P := (inclusion le_sup_left).toAlgebra
  letI : IsScalarTower K B P := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L P := IsScalarTower.of_algebraMap_eq' rfl
  exact (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)

/-- Restriction embeds the geometric group into the arithmetic group. Its
image is the group over the intersection, and it is onto exactly for
regular realizations. -/
def geometricGaloisGroup : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (t : Ω) (_ : Transcendental k t) [Algebra.IsAlgebraic (adjoin k {t}) Ω]
    (L : IntermediateField (adjoin k {t}) Ω)
    [FiniteDimensional (adjoin k {t}) L] [IsGalois (adjoin k {t}) L],
    let K := adjoin k {t}
    let B := rationalWithConstants t (algebraicClosure k Ω)
    let P := L ⊔ B
    let I := L ⊓ B
    letI : Algebra B P := (inclusion le_sup_right).toAlgebra
    letI : Algebra I L := (inclusion inf_le_left).toAlgebra
    letI : IsScalarTower K I L := IsScalarTower.of_algebraMap_eq' rfl
    let ρ := geometricRestriction t L
    (∀ (σ : P ≃ₐ[B] P) (x : L), ((ρ σ x : L) : Ω) =
      (σ ⟨(x : Ω), (le_sup_left : L ≤ P) x.property⟩ : Ω)) ∧
    Function.Injective ρ ∧
    ρ.range = (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[I] L) →* (L ≃ₐ[K] L)).range ∧
    (Function.Surjective ρ ↔ isRegularOver k L)

end GaloisFormalization.IG.Specs
