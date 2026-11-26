import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison

namespace LinearAlgebraicGroups.Specs.ExceptionalUnramifiedCocycleSupport

open CategoryTheory
open scoped CategoryTheory.MonObj
open Arithmetic.MaximalUnramifiedBrauer (IsUnramified maximalUnramified)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open ExceptionalFormsOverUnramifiedFields (IsExceptionalReference)
open ExceptionalTwistedTraceComparison (PointCocycle Twist)
open Pinning (AttachedDatum PinnedGroup)
open QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction basedAutTopology fieldGalTopology)
open RootGroups (AdditiveLine)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology
  (Cocycle restriction pointMap pointAction)
open ValuativeRel

attribute [local instance] basedAutTopology fieldGalTopology

universe u

local notation "CohPoints" => _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points
noncomputable section

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The finite-level cocycle and its inflation agree pointwise with the indicated function. -/
def HasUnramifiedSupport {G : GroupScheme F}
    (L₀ : FiniteGaloisIntermediateField F (SeparableClosure F))
    (a : Gal(SeparableClosure F/F) → CohPoints F (SeparableClosure F) G.X) : Prop :=
  ∃ (L : FiniteGaloisIntermediateField F (SeparableClosure F))
    (c : Gal(L/F) → CohPoints F L G.X),
    L₀ ≤ L ∧ IsUnramified F L ∧
    (∀ σ τ, c (σ * τ) = c σ * pointAction F L G.X σ (c τ)) ∧
    ∀ σ, pointMap F L G.X L.toIntermediateField.val (c (restriction L σ)) = a σ

/-- A cocycle vanishing on the subgroup fixing the maximal unramified field
inflates from a finite unramified level above the given level. -/
def DescentFromFixingSubgroup : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {G : GroupScheme F}
    (L₀ : FiniteGaloisIntermediateField F (SeparableClosure F)), IsUnramified F L₀ →
    ∀ a : PointCocycle (S := SeparableClosure F) G,
      (∀ σ ∈ (maximalUnramified F).fixingSubgroup, a.val σ = 1) →
      HasUnramifiedSupport (G := G) L₀ a.val

/-- Every adjoint cocycle of the given pinned exceptional reference with
unramified diagram action is cohomologous to inflation from an unramified level. -/
def ExceptionalCocycleSupport : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    {E : SplitSequence P D l Q}
    {ω : Cocycle (trivialOuterAction (k := F) (S := SeparableClosure F) D.toBased)}
    (V : PinnedRepresentative (S := SeparableClosure F) E ω),
    IsExceptionalReference D →
    ∀ (Q₀ : AdjointQuotient V.model.val)
      (L₀ : FiniteGaloisIntermediateField F (SeparableClosure F)),
      IsUnramified F L₀ →
      (∃ ω₀ : Gal(L₀/F) →* Aut D.toBased, ∀ σ, ω₀ (restriction L₀ σ) = ω σ) →
      ∀ a : PointCocycle (S := SeparableClosure F) Q₀.quotient.val,
        ∃ b : CohPoints F (SeparableClosure F) Q₀.quotient.val.X,
          HasUnramifiedSupport (G := Q₀.quotient.val) L₀
            (fun σ => b⁻¹ *
              (show CohPoints F (SeparableClosure F) Q₀.quotient.val.X from a.val σ) *
              pointAction F (SeparableClosure F) Q₀.quotient.val.X σ b)

end Local

/-- The actual arithmetic Frobenius is the unique element inducing the power
given by the cardinality of the base residue field. Its powers exhaust the Galois group. -/
def ArithmeticFrobenius : Prop :=
  ∀ {F L : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field L] [Algebra F L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L],
    Function.Surjective (fun x : F => valuation L (algebraMap F L x)) →
    let O := Valuation.integer (valuation L)
    let q := Nat.card (IsLocalRing.ResidueField (Valuation.integer (valuation F)))
    ∃ σ : Gal(L/F),
      (∀ x : O, ∃ y : O, (y : L) = σ x ∧
        IsLocalRing.residue O y = (IsLocalRing.residue O x) ^ q) ∧
      (∀ τ : Gal(L/F), (∀ x : O, ∃ y : O, (y : L) = τ x ∧
        IsLocalRing.residue O y = (IsLocalRing.residue O x) ^ q) → τ = σ) ∧
      orderOf σ = Module.finrank F L ∧
      Function.Bijective (fun i : Fin (Module.finrank F L) => σ ^ i.val)

/-- An unramified enlargement in the same separable closure with the actual
field inclusion and the compatible restriction of automorphisms. -/
def UnramifiedEnlargement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (L₀ : FiniteGaloisIntermediateField F (SeparableClosure F)), IsUnramified F L₀ →
    ∀ n : ℕ, 0 < n →
      ∃ (L : FiniteGaloisIntermediateField F (SeparableClosure F))
        (h : L₀.toIntermediateField ≤ L.toIntermediateField),
        IsUnramified F L ∧
        letI : Algebra L₀ L := (IntermediateField.inclusion h).toAlgebra
        n ∣ Module.finrank L₀ L ∧
        ∃ r : Gal(L/F) →* Gal(L₀/F), Function.Surjective r ∧
          (∀ σ x, (IntermediateField.inclusion h) (r σ x) =
            σ ((IntermediateField.inclusion h) x)) ∧
          ∀ σ, r (restriction L σ) = restriction L₀ σ

/-- A twist presented by its actual relative trivialization and a neutral
adjoint cocycle is isomorphic to the reference over the ground field. -/
def NeutralTwist : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G}
    (a : PointCocycle (S := S) Q.quotient.val) (T : Twist a),
    (∃ b : CohPoints k S Q.quotient.val.X, ∀ σ,
      1 = b⁻¹ * (show CohPoints k S Q.quotient.val.X from a.val σ) *
        pointAction k S Q.quotient.val.X σ b) →
    Nonempty (G.val ≅ T.group.val)

end
end LinearAlgebraicGroups.Specs.ExceptionalUnramifiedCocycleSupport
