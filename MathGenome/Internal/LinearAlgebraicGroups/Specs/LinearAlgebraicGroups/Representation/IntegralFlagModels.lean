import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.IntegralFlagGeometry

universe u

namespace LinearAlgebraicGroups.Specs.IntegralFlagModels

open Pinning (BasedRootDatum)
open IntegralFlagGeometry (BaseRing PrimeField PinnedModel rationalMap primeMap)
open FlagCohomology (cohomology)
open ArithmeticCohomologyBaseChange (CohomologyBaseChange CohomologyReduction IsFiniteAffineCover)

/-- A single smooth flat projective model with its equivariant opposite-Borel
line works over the rational field and at all non-inverted primes. Its derived
cohomology is finite and carries the canonical generic and prime comparisons.
An ordered affine cover of the model supplies the intersections used in prime
reduction in every degree. -/
def Statement : Prop :=
  ∀ (D : BasedRootDatum.{u}), RootData.rationalRootAnnihilator D.datum = ⊥ →
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∀ weight : D.X, ∃ M : PinnedModel D weight,
      (∀ i : ℕ, Module.Finite (BaseRing.{u} M.m)
        ((cohomology M.model.flag i).obj M.model.line)) ∧
      CohomologyBaseChange (rationalMap M.nonzero) M.model.flag M.model.line ∧
      (∃ (Idx : Type u) (_ : LinearOrder Idx) (_ : Fintype Idx)
        (U : Idx → M.model.flag.left.Opens), IsFiniteAffineCover U) ∧
      ∀ (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ M.m),
        (∃ e : (BaseRing.{u} M.m ⧸ Ideal.span {(p : BaseRing.{u} M.m)}) ≃+* PrimeField.{u} p,
          ∀ x : BaseRing.{u} M.m, e (Ideal.Quotient.mk _ x) = primeMap hp x) ∧
        CohomologyReduction (primeMap hp) (p : BaseRing.{u} M.m) M.model.flag M.model.line

end LinearAlgebraicGroups.Specs.IntegralFlagModels
