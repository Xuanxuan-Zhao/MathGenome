import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.DecompositionMatrix
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.ModularProjectiveCovers

/-! The multiplicity and lattice assertions in Brauer reciprocity. -/

namespace RepTheorySurvey.Modular.MR09ReciprocitySpec

open IsLocalRing CompositionMultiplicity

set_option backward.isDefEq.respectTransparency false

/-- The image of one group-algebra element acting on a native left module. -/
noncomputable abbrev actionImage (F G : Type*) [Field F] [Group G]
    (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra F G) M]
    (e : MonoidAlgebra F G) :=
  LinearMap.range (RestrictScalars.lsmul F (MonoidAlgebra F G) M e)

def evaluation : Prop :=
  ∀ {F A M : Type*} [Field F] [Ring A] [Algebra F A]
    [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M]
    (e : A), IsIdempotentElem e →
    ∃ equiv : (MR09CoversSpec.principalLeftIdealValue e →ₗ[A] M) ≃ₗ[F]
      LinearMap.range (Algebra.lsmul F F M e),
      ∀ f, (equiv f : M) = f ⟨e, Ideal.mem_span_singleton_self e⟩

def modularImageMultiplicity : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] [Finite G] {r : ℕ} {d : Fin r → ℕ}
    (split : MR01Spec.radicalQuotientValue F G ≃ₐ[F]
      ((j : Fin r) → Matrix (Fin (d j)) (Fin (d j)) F)),
    (∀ j, 0 < d j) →
    ∀ (i : Fin r) (e : MonoidAlgebra F G), IsIdempotentElem e →
    let q := SplitMatrixColumnsSpec.modularColumnMap split
    (q e i).rank = 1 → (∀ j, j ≠ i → q e j = 0) →
    ∀ (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra F G) M] [GroundFinite F G M],
      Module.finrank F (actionImage F G M e) =
        Spec.multiplicity F G M (SplitMatrixColumnsSpec.columnModule q i)

def ordinaryImageMultiplicity : Prop :=
  ∀ {F G : Type*} [Field F] [Group G] [Finite G],
    MR01Spec.splitMatrixAlgebraValue F (MonoidAlgebra F G) →
    ∀ (e : MonoidAlgebra F G), IsIdempotentElem e →
    ∀ (V : Type*) [AddCommGroup V] [Module (MonoidAlgebra F G) V]
      [IsSimpleModule (MonoidAlgebra F G) V],
      Module.finrank F (actionImage F G V e) =
        Spec.multiplicity F G (MR09CoversSpec.principalLeftIdealValue e) V

section Integral

variable {G : Type*} [Group G] {O K : Type*} [CommRing O] [Field K] [Algebra O K]

/-- The integral action on the carrier of a native stable lattice. -/
noncomputable abbrev latticeAction {V : Type*} [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    (L : MR04LatticeSpec.NativeLatticeData O K G V) :=
  letI := RestrictScalars.module K (MonoidAlgebra K G) V
  letI := Module.restrictScalars O K (RestrictScalars K (MonoidAlgebra K G) V)
  letI := IsScalarTower.restrictScalars O K (RestrictScalars K (MonoidAlgebra K G) V)
  (MR04LatticeSpec.integralAction O L).asAlgebraHom

def stableLatticeImage : Prop :=
  ∀ {G : Type*} [Group G] {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    {V : Type*} [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    (L : MR04LatticeSpec.NativeLatticeData O K G V)
    (e : MonoidAlgebra O G), IsIdempotentElem e →
    let T := latticeAction L e
    let U := actionImage K G V (MR01Spec.fractionMapValue O K G e)
    let W := actionImage (ResidueField O) G (MR04LatticeSpec.nativeReduction L)
      (MR01Spec.reductionValue O G e)
    Module.Finite O (LinearMap.range T) ∧ Module.Free O (LinearMap.range T) ∧
    IsCompl (LinearMap.range T) (LinearMap.ker T) ∧
    Nonempty (MR04LatticeSpec.ResidueQuotient O (LinearMap.range T) ≃ₗ[ResidueField O] W) ∧
    Module.finrank K U = Module.finrank O (LinearMap.range T) ∧
    Module.finrank (ResidueField O) W = Module.finrank O (LinearMap.range T)

def brauerReciprocity : Prop :=
  ∀ {G : Type*} [Group G] [Finite G] {p : ℕ}
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type*} [Field K] [Algebra O K] (system : MR01Spec.SplittingSystemData G p O K)
    {r : ℕ} {d : Fin r → ℕ}
    (split : MR01Spec.radicalQuotientValue (ResidueField O) G ≃ₐ[ResidueField O]
      ((j : Fin r) → Matrix (Fin (d j)) (Fin (d j)) (ResidueField O))),
    (∀ j, 0 < d j) → ∀ (i : Fin r) (e : MonoidAlgebra O G), IsIdempotentElem e →
    let q := SplitMatrixColumnsSpec.modularColumnMap split
    let eBar := MR01Spec.reductionValue O G e
    (q eBar i).rank = 1 → (∀ j, j ≠ i → q eBar j = 0) →
    ∀ (V : Type*) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
      [IsSimpleModule (MonoidAlgebra K G) V],
      Spec.multiplicity K G (MR09CoversSpec.principalLeftIdealValue
        (MR01Spec.fractionMapValue O K G e)) V =
        MR06Spec.decompositionMultiplicityValue system V (SplitMatrixColumnsSpec.columnModule q i)

def principalIdealLattice : Prop :=
  ∀ {G : Type*} [Group G] [Finite G] {p : ℕ}
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type*} [Field K] [Algebra O K], MR01Spec.SplittingSystemData G p O K →
    ∀ (e : MonoidAlgebra O G), IsIdempotentElem e →
    let P := MR09CoversSpec.principalLeftIdealValue (MR01Spec.fractionMapValue O K G e)
    let Pbar := MR09CoversSpec.principalLeftIdealValue (MR01Spec.reductionValue O G e)
    letI := RestrictScalars.module K (MonoidAlgebra K G) P
    letI := Module.restrictScalars O K (RestrictScalars K (MonoidAlgebra K G) P)
    letI := IsScalarTower.restrictScalars O K (RestrictScalars K (MonoidAlgebra K G) P)
    ∃ L : MR04LatticeSpec.NativeLatticeData O K G P,
      (∀ x : P, (x : RestrictScalars K (MonoidAlgebra K G) P) ∈ L.carrier ↔
        ∃ a : MR09CoversSpec.principalLeftIdealValue e,
          MR01Spec.fractionMapValue O K G (a : MonoidAlgebra O G) = (x : MonoidAlgebra K G)) ∧
      Nonempty (MR04LatticeSpec.nativeReduction L ≃ₗ[MonoidAlgebra (ResidueField O) G] Pbar)

end Integral
end RepTheorySurvey.Modular.MR09ReciprocitySpec
