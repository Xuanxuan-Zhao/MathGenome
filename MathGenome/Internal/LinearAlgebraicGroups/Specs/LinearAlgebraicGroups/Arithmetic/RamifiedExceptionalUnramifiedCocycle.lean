import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison
open CategoryTheory
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.RamifiedExceptionalUnramifiedCocycle

open AutomorphismSequence (AdjointQuotient SplitSequence)
open ExceptionalAffineBruhat (IsUnramifiedLocalExtension)
open ExceptionalFormsOverUnramifiedFields (HasTypeE)
open ExceptionalTwistedTraceComparison (PointCocycle)
open GeometricRadicals (IsSemisimple)
open Pinning (AttachedDatum PinnedGroup)
open QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction
  basedAutTopology fieldGalTopology)
open RootGroups (AdditiveLine)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology
open ValuativeRel

attribute [local instance] basedAutTopology fieldGalTopology
attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

universe u

noncomputable abbrev integers (K : Type u) [Field K] [ValuativeRel K] := (valuation K).valuationSubring

noncomputable abbrev residueField (K : Type u) [Field K] [ValuativeRel K] :=
  IsLocalRing.ResidueField (integers K)

/-- The residue automorphism is induced by applying the field automorphism to integral
elements and reducing. -/
def Reduces {F K : Type u} [Field F] [Field K] [Algebra F K]
    [ValuativeRel F] [ValuativeRel K] [ValuativeExtension F K]
    (σ : Gal(K/F)) (τ : Gal(residueField K / residueField F)) : Prop :=
  ∀ x : integers K, ∃ y : integers K, (y : K) = σ (x : K) ∧
    τ (IsLocalRing.residue (integers K) x) = IsLocalRing.residue (integers K) y

/-- A cocycle of the full adjoint quotient of the pinned reference becomes an
inflated cocycle on actual points at a finite unramified level. -/
def FiniteUnramifiedInflation : Prop :=
  ∀ (F S : Type u) [Field F] [Field S] [Algebra F S] [IsSepClosure F S]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    {E : SplitSequence P D l Q}
    {ω : Cocycle (trivialOuterAction (k := F) (S := S) D.toBased)}
    (V : PinnedRepresentative (S := S) E ω),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G → HasTypeE D 6 →
    ∀ (Q₀ : AdjointQuotient V.model.val),
      letI : TopologicalSpace (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points
        F S Q₀.quotient.val.X) := ⊥
      ∀ (a : Cocycle (pointAction F S Q₀.quotient.val.X)),
    ∃ (K : FiniteGaloisIntermediateField F S)
      (r : ValuativeRel K) (T : TopologicalSpace K),
      letI := r
      letI := T
      ∃ (hlocal : IsNonarchimedeanLocalField K) (_ : ValuativeExtension F K),
        letI := hlocal
        IsUnramifiedLocalExtension F K ∧
        ∃ (b : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S Q₀.quotient.val.X)
          (c : Gal(K/F) → _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F K
            Q₀.quotient.val.X),
          (∀ σ τ, c (σ * τ) = c σ * pointAction F K Q₀.quotient.val.X σ (c τ)) ∧
          ∀ σ, pointMap F K Q₀.quotient.val.X K.toIntermediateField.val (c (restriction K σ)) =
            b⁻¹ * a σ * pointAction F S Q₀.quotient.val.X σ b

/-- Reduction identifies the Galois group at every finite unramified level with the
Galois group of its actual residue extension. -/
def ResidueGaloisComparison : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [ValuativeRel K] [TopologicalSpace F] [TopologicalSpace K]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∃ e : Gal(K/F) ≃* Gal(residueField K / residueField F), ∀ σ, Reduces σ (e σ)

/-- The reduction identifications commute with restriction in a tower. -/
def ResidueGaloisRestriction : Prop :=
  ∀ (F K L : Type u) [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    [FiniteDimensional F K] [FiniteDimensional F L] [IsGalois F K] [IsGalois F L]
    [ValuativeRel F] [ValuativeRel K] [ValuativeRel L]
    [TopologicalSpace F] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K]
    [IsNonarchimedeanLocalField L]
    [ValuativeExtension F K] [ValuativeExtension F L] [ValuativeExtension K L],
    ∀ (σ : Gal(L/F)) (τ : Gal(residueField L / residueField F))
      (υ : Gal(residueField K / residueField F)),
      Reduces σ τ → Reduces (AlgEquiv.restrictNormalHom K σ) υ →
      ∀ x, τ (algebraMap (residueField K) (residueField L) x) =
        algebraMap (residueField K) (residueField L) (υ x)

/-- Any finite extension of the residue field at an unramified level embeds into the
residue field of a larger finite unramified level in the same separable closure. -/
def UnramifiedResidueEnlargement : Prop :=
  ∀ (F S : Type u) [Field F] [Field S] [Algebra F S] [IsSepClosure F S]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (K : FiniteGaloisIntermediateField F S)
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∀ (R : Type u) [Field R] [Algebra (residueField K) R] [Finite R],
    ∃ (L : FiniteGaloisIntermediateField F S)
      (hle : K.toIntermediateField ≤ L.toIntermediateField)
      (r : ValuativeRel L) (T : TopologicalSpace L),
      letI := r
      letI := T
      letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
      ∃ (hlocal : IsNonarchimedeanLocalField L) (_ : ValuativeExtension F L)
        (_ : ValuativeExtension K L),
        letI := hlocal
        IsUnramifiedLocalExtension F L ∧ IsUnramifiedLocalExtension K L ∧
          Nonempty (R →ₐ[residueField K] residueField L)

end LinearAlgebraicGroups.Specs.RamifiedExceptionalUnramifiedCocycle
