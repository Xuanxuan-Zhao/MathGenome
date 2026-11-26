import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Homological.RegularQuotientProjectiveDimension
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.RegularLocalRing.Defs

noncomputable section

open CategoryTheory
open scoped TensorProduct
open P103.Specs.Ch10.Comparison (LeftResolution)
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport.Specs (Tor)

namespace CommutativeAlgebraNotes.Intersection.OneSpecialFibreTor.Specs

universe u

variable {R : Type u} [CommRing R]

abbrev SpecialFibre (x : R) := R ⧸ Ideal.span {x}

/-- The original module, with its scalar action factored through the principal quotient. -/
abbrev killedModule {x : R} {M : ModuleCat.{u} R} (h : Module.IsTorsionBy R M x) :
    ModuleCat.{u} (SpecialFibre x) :=
  letI := h.module
  ModuleCat.of (SpecialFibre x) M

abbrev reduceModule (x : R) (N : ModuleCat.{u} R) : ModuleCat.{u} (SpecialFibre x) :=
  (AdvCommAlg.regularQuotientFunctor x).obj N

abbrev reducedTor {x : R} {M : ModuleCat.{u} R}
    (h : Module.IsTorsionBy R M x) (N : ModuleCat.{u} R) (i : ℕ) :=
  Tor (killedModule h) (reduceModule x N) i

/-- The termwise quotient, with its reduced augmentation, is a free resolution.
Finite generation and the vanishing bound of the original terms are preserved. -/
def reducedResolution : Prop :=
  ∀ {R : Type u} [CommRing R] (x : R) (N : ModuleCat.{u} R)
    (Q : LeftResolution R N) (b : ℕ),
    IsSMulRegular R x → IsSMulRegular N x →
    (∀ i, Module.Finite R (Q.complex.X i) ∧ Module.Free R (Q.complex.X i)) →
    (∀ i, b < i → Subsingleton (Q.complex.X i)) →
    ∃ Q' : LeftResolution (SpecialFibre x) (reduceModule x N),
      Q'.complex = ((AdvCommAlg.regularQuotientFunctor x).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj Q.complex ∧
      HEq (ModuleCat.ofHom Q'.ε) ((AdvCommAlg.regularQuotientFunctor x).map
        (ModuleCat.ofHom Q.ε)) ∧
      (∀ i, Module.Finite (SpecialFibre x) (Q'.complex.X i) ∧
        Module.Free (SpecialFibre x) (Q'.complex.X i)) ∧
      (∀ i, b < i → Subsingleton (Q'.complex.X i))

def torComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] [CharZero R]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p],
    (p : R) ∉ (IsLocalRing.maximalIdeal R) ^ 2 →
    ∀ (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
      (hM : Module.IsTorsionBy R M (p : R)), IsSMulRegular N (p : R) →
    ∀ i, Nonempty (Tor M N i ≃ₗ[R] RestrictScalars R (SpecialFibre (p : R)) (reducedTor hM N i))

def tensorComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] [CharZero R]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p],
    (p : R) ∉ (IsLocalRing.maximalIdeal R) ^ 2 →
    ∀ (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
      (hM : Module.IsTorsionBy R M (p : R)), IsSMulRegular N (p : R) →
    Nonempty ((M ⊗[R] N) ≃ₗ[R] RestrictScalars R (SpecialFibre (p : R))
      (killedModule hM ⊗[SpecialFibre (p : R)] reduceModule (p : R) N))

def lengthComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] [CharZero R]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p],
    (p : R) ∉ (IsLocalRing.maximalIdeal R) ^ 2 →
    ∀ (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
      (hM : Module.IsTorsionBy R M (p : R)), IsSMulRegular N (p : R) →
    IsFiniteLength R (M ⊗[R] N) →
    ∀ i, IsFiniteLength R (Tor M N i) ∧
      IsFiniteLength (SpecialFibre (p : R)) (reducedTor hM N i) ∧
      Module.length R (Tor M N i) = Module.length (SpecialFibre (p : R)) (reducedTor hM N i)

def dimensionComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] [CharZero R]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p],
    (p : R) ∉ (IsLocalRing.maximalIdeal R) ^ 2 →
    ∀ (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
      [Nontrivial M] [Nontrivial N]
      (hM : Module.IsTorsionBy R M (p : R)), IsSMulRegular N (p : R) →
    Nontrivial (reduceModule (p : R) N) ∧
      Module.supportDim (SpecialFibre (p : R)) (killedModule hM) = Module.supportDim R M ∧
      Module.supportDim (SpecialFibre (p : R)) (reduceModule (p : R) N) =
        Module.supportDim R (QuotSMulTop (p : R) N) ∧
      Module.supportDim (SpecialFibre (p : R)) (reduceModule (p : R) N) + 1 =
        Module.supportDim R N

end CommutativeAlgebraNotes.Intersection.OneSpecialFibreTor.Specs
