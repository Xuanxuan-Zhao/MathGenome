import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Defs

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing

section

variable (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]

/-- The extension of the maximal ideal of the source. -/
abbrev extendedMaximalIdeal : Ideal B :=
  (maximalIdeal A).map (algebraMap A B)

/-- The algebra on the closed fibre induced by the given map from the source. -/
noncomputable abbrev closedFiberAlgebra :
    Algebra (ResidueField A) (B ⧸ extendedMaximalIdeal A B) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.le_comap_map : maximalIdeal A ≤
      (extendedMaximalIdeal A B).comap (algebraMap A B))

end

namespace Specs

def AdicPowersCofinal : Prop :=
  ∀ {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B],
  let J := extendedMaximalIdeal A B
  J.radical = maximalIdeal B →
    (∀ n : ℕ, J ^ n ≤ maximalIdeal B ^ n) ∧
      (∃ e : ℕ, ∀ n : ℕ, maximalIdeal B ^ (e * n) ≤ J ^ n)

def SpanOfLifts : Prop :=
  ∀ {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B],
  let J := extendedMaximalIdeal A B
  letI := closedFiberAlgebra A B
  ∀ {ι : Type*} [Fintype ι] (b : ι → B),
    J.radical = maximalIdeal B →
    Submodule.span (ResidueField A) (Set.range fun i ↦ Ideal.Quotient.mk J (b i)) = ⊤ →
    Submodule.span A (Set.range b) = ⊤

def FiniteOfFiniteClosedFiber : Prop :=
  ∀ {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B],
  let J := extendedMaximalIdeal A B
  letI := closedFiberAlgebra A B
  J.radical = maximalIdeal B →
    Module.Finite (ResidueField A) (B ⧸ J) → Module.Finite A B

def SurjectiveOfOneSpansClosedFiber : Prop :=
  ∀ {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B],
  let J := extendedMaximalIdeal A B
  letI := closedFiberAlgebra A B
  J.radical = maximalIdeal B →
    Submodule.span (ResidueField A) ({1} : Set (B ⧸ J)) = ⊤ →
    Function.Surjective (algebraMap A B)

def SurjectiveOfMaximalIdealAndResidue : Prop :=
  ∀ {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B],
  extendedMaximalIdeal A B = maximalIdeal B →
    Function.Surjective (ResidueField.map (algebraMap A B)) →
    Function.Surjective (algebraMap A B)

end Specs

end CommutativeAlgebraNotes.CoefficientRings
