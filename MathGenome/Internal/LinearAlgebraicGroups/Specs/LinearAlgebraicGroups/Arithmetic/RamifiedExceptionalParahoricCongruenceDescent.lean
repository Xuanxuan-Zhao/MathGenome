import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceReduction

namespace LinearAlgebraicGroups.Specs.RamifiedExceptionalParahoricCongruenceDescent

open ExceptionalAffineBruhat (ExceptionalNumbering FoldedApartment RamifiedReference coefficientPoints)
open ExceptionalAffineBuilding (IsBarycenter cotype rationalPoint simplexPoint Weights)
open ExceptionalAffineRootSystems (e6Partner)
open ExceptionalLocalRootCoordinates (normalizedValuation ramificationIndex)
open ExceptionalValuedTorusNormalizer (invariantApartment)
open IntegralSemisimpleModel (Model)
open Pinning (BasedRootDatum)
open RamifiedExceptionalAuxiliaryTower (UnramifiedLevel)
open RamifiedExceptionalFaceReduction (ScaledParahoricTower)
open RamifiedExceptionalLocalFaceCoordinates (MarkedLevel)
open scoped CategoryTheory.MonObj TensorProduct

universe u

/-- A cocycle with identity scaled reduction is a coboundary in the
reduction kernel at that very stage of the marked tower. -/
def ParahoricCongruenceDescent : Prop :=
  ∀ {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    [FiniteDimensional F L] [IsGalois F L] [IsSepClosed S] [Algebra.IsSeparable F S]
    (σ : Gal(L/F)), Module.finrank F L = 2 → σ ≠ 1 → 1 < ramificationIndex F L →
    ∀ {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M)
      (numbering : Fin 6 ≃ D.base.support),
    ExceptionalNumbering D 6 numbering → D.datum.rootSpan ℤ = ⊤ →
    (∀ i, (R.diagram σ).val.indexEquiv (numbering i) = numbering (e6Partner i)) →
    ∀ (A : FoldedApartment (R.diagram σ))
      (X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field)
      (J : Set (A.roots.SimpleWall A.basepoint)), J ≠ Set.univ →
    ∀ (k₀ : UnramifiedLevel F S)
      (t : Weights (A.roots.SimpleWall A.basepoint)) (x : invariantApartment D (R.diagram σ)),
    IsBarycenter J t → cotype t = J →
    rationalPoint (X k₀).building.realization.coordinates x =
      simplexPoint (X k₀).building.realization.coordinates (X k₀).building.realization.vertex t →
    ∀ (π : Lˣ), normalizedValuation L (π : L) = WithZero.exp (-1 : ℤ) →
    ∀ (d : ℕ), 0 < d → ∀ y : D.Y, (1 : ℚ) ⊗ₜ[ℤ] y = (2 * (d : ℚ)) • x.val →
    ∀ (P : ScaledParahoricTower X J π d y) (k : UnramifiedLevel F S),
    let scale := P.scale k
    let act (g : Gal(k.field/F)) (h : (X k).parahoric J) : (X k).parahoric J :=
      ⟨coefficientPoints R.descent.group.val g.toAlgHom h.val, scale.coefficient_mem g h⟩
    ∀ a : Gal(k.field/F) → (X k).parahoric J,
    (∀ g h, a (g * h) = a g * act g (a h)) →
    (∀ g, scale.reduction (a g) = 1) →
    ∃ b : scale.reduction.ker, ∀ g,
      a g = (b : (X k).parahoric J) * (act g b)⁻¹

end LinearAlgebraicGroups.Specs.RamifiedExceptionalParahoricCongruenceDescent
