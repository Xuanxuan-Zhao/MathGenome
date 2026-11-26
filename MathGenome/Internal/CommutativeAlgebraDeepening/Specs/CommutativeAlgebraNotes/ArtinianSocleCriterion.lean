import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ResidueHullArtinian

/-! Proposition M04 and the essential socle and embedding used in its proof. -/

namespace Specs.CommutativeAlgebraNotes.ArtinianSocleCriterion

open IsLocalRing AdvCommAlg.Depth

universe u v

abbrev residueHullArtinianType :=
  Specs.CommutativeAlgebraNotes.ResidueHullArtinian.residueHullArtinianType.{u}

/-- Every element of an Artinian module is killed by a positive power of the maximal ideal. -/
def artinianPowerTorsionType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] [IsArtinian R T],
    IdealTorsion.idealTorsion (maximalIdeal R) T = ⊤

/-- Every nonzero submodule of a power-torsion module meets its socle nontrivially. -/
def powerTorsionSocleEssentialType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {T : Type u} [AddCommGroup T] [Module R T],
    IdealTorsion.idealTorsion (maximalIdeal R) T = ⊤ →
    ∀ N : Submodule R T, N ≠ ⊥ → N ⊓ Socle R T ≠ ⊥

/-- A module with finite-dimensional socle embeds in the corresponding power of the hull
when it is power torsion. The embedding identifies the two socles. -/
def powerTorsionHullEmbeddingType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    (E : _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs.residueFieldEnvelopeValue R)
    {T : Type u} [AddCommGroup T] [Module R T],
    IdealTorsion.idealTorsion (maximalIdeal R) T = ⊤ →
    FiniteDimensional (ResidueField R) (Socle R T) →
    ∃ f : T →ₗ[R] (Fin (Module.finrank (ResidueField R) (Socle R T)) → E.carrier),
      Function.Injective f ∧ (Socle R T).map f = Socle R _

/-- The Artinian criterion for maximal-ideal power-torsion modules. -/
def artinianIffSocleFiniteType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type u} [AddCommGroup T] [Module R T],
    IdealTorsion.idealTorsion (maximalIdeal R) T = ⊤ →
    (IsArtinian R T ↔ FiniteDimensional (ResidueField R) (Socle R T))

end Specs.CommutativeAlgebraNotes.ArtinianSocleCriterion
