import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceReduction

namespace LinearAlgebraicGroups.Specs.RamifiedExceptionalParahoricResidueDescent

open CategoryTheory ValuativeRel
open scoped CategoryTheory.MonObj
open ExceptionalAffineBruhat (RamifiedReference FoldedApartment coefficientPoints)
open ExceptionalValuedTorusNormalizer (invariantApartment)
open IntegralSemisimpleModel (Model)
open Pinning (BasedRootDatum)
open RamifiedExceptionalAuxiliaryTower (UnramifiedLevel)
open RamifiedExceptionalFaceReduction (ScaledParahoricTower GeometricReduction faceInclusion)
open RamifiedExceptionalLocalFaceCoordinates (MarkedLevel)

universe u

noncomputable section

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]

/-- Restriction to the actual smaller coefficient field in the chosen closure. -/
def restrictCoefficient {k k' : UnramifiedLevel F S} (h : k ≤ k') :
    Gal(k'.field/F) →* Gal(k.field/F) :=
  let f := UnramifiedLevel.inclusion h
  letI : Algebra k.field k'.field := f.toRingHom.toAlgebra
  letI : IsScalarTower F k.field k'.field := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  AlgEquiv.restrictNormalHom k.field

variable {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {τ : Gal(L/F)} {A : FoldedApartment (R.diagram τ)}
  {X : ∀ k : UnramifiedLevel F S, MarkedLevel R τ A k.field}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}

/-- The actual coefficient automorphism on the point group restricts to the
same marked face at each level. -/
def faceCoefficient (P : ScaledParahoricTower X J π d y) (k : UnramifiedLevel F S)
    (s : Gal(k.field/F)) (g : (X k).parahoric J) : (X k).parahoric J :=
  ⟨coefficientPoints R.descent.group.val s.toAlgHom g.val, (P.scale k).coefficient_mem s g⟩

/-- A cocycle in the marked parahoric admits a first correction at a finite
unramified enlargement. Its corrected values reduce to the identity in the
local residue field of the same scaled model at that level. -/
def ParahoricResidueDescent : Prop :=
  ∀ {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    [IsSepClosed S] [Algebra.IsSeparable F S]
    {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
    {τ : Gal(L/F)} {A : FoldedApartment (R.diagram τ)}
    {X : ∀ k : UnramifiedLevel F S, MarkedLevel R τ A k.field}
    {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
    {ϖ : Fˣ} {x : invariantApartment D (R.diagram τ)}
    (P : ScaledParahoricTower X J π d y), GeometricReduction P ϖ x →
    ∀ (k : UnramifiedLevel F S) (c : Gal(k.field/F) → (X k).parahoric J),
      (∀ s t, c (s * t) = c s * faceCoefficient P k s (c t)) →
      ∃ (k' : UnramifiedLevel F S) (h : k ≤ k') (b : (X k').parahoric J),
        ∀ s : Gal(k'.field/F),
          (P.scale k').reduction
            (b⁻¹ * faceInclusion X h J (P.face_comap h) (c (restrictCoefficient h s)) *
              faceCoefficient P k' s b) = 1

end

end LinearAlgebraicGroups.Specs.RamifiedExceptionalParahoricResidueDescent
