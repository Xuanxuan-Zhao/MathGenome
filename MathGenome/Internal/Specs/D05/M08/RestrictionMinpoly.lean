import MathGenome.Internal.Specs.D05.M06.Invariant
import MathGenome.Internal.Specs.D05.M08.Minpoly

/-! Independent specifications for K05.08.restriction_minpoly,
paper.tex:1233–1236. The operators, evaluation and minimal polynomial are
exactly those of the prerequisite interfaces. Powers and annihilator transfer
hold in arbitrary dimension; the minimal-polynomial conclusions use the
chapter's finite-dimensional hypothesis. No splitting or characteristic
condition, complement, or nonzero-dimension assumption is imposed. -/

noncomputable section

namespace Specs.D05.M08.RestrictionMinpoly

open Specs.D05.M06.Invariant
open Specs.D05.M08.Evaluation Specs.D05.M08.Minpoly

/-- Iterating the restriction agrees with iterating the ambient operator. -/
def restriction_pow_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T)
    (j : ℕ) (x : U),
    ((restriction_value K V U T h ^ j) x : V) = (T ^ j) (x : V)

/-- Iterating the quotient operator sends the class of x to the class of T^j x. -/
def quotient_pow_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T)
    (j : ℕ) (x : V),
    (inducedMap_value K V U T h ^ j) (U.mkQ x) = U.mkQ ((T ^ j) x)

/-- Polynomial evaluation commutes with inclusion of the invariant subspace. -/
def restriction_eval_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T)
    (p : Polynomial K) (x : U),
    (evaluation_value K U (restriction_value K V U T h) p x : V) =
      evaluation_value K V T p (x : V)

/-- Polynomial evaluation commutes with the canonical quotient projection. -/
def quotient_eval_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T)
    (p : Polynomial K) (x : V),
    evaluation_value K (V ⧸ U) (inducedMap_value K V U T h) p (U.mkQ x) =
      U.mkQ (evaluation_value K V T p x)

/-- Every ambient annihilator annihilates the restricted operator. -/
def restriction_annihilates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T)
    (p : Polynomial K),
    evaluation_value K V T p = 0 →
      evaluation_value K U (restriction_value K V U T h) p = 0

/-- Every ambient annihilator annihilates the induced quotient operator. -/
def quotient_annihilates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T)
    (p : Polynomial K),
    evaluation_value K V T p = 0 →
      evaluation_value K (V ⧸ U) (inducedMap_value K V U T h) p = 0

/-- The minimal polynomial of the restriction divides the ambient one. -/
def restriction_minpoly_dvd : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T),
    minimalPolynomial_value K U (restriction_value K V U T h) ∣
      minimalPolynomial_value K V T

/-- The minimal polynomial on the quotient divides the ambient one. -/
def quotient_minpoly_dvd : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T),
    minimalPolynomial_value K (V ⧸ U) (inducedMap_value K V U T h) ∣
      minimalPolynomial_value K V T

end Specs.D05.M08.RestrictionMinpoly
