import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch12.DerivedLocalization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Resolution
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.Module

noncomputable section

open CategoryTheory
open scoped TensorProduct
open P103.Specs.Ch10.Comparison (LeftResolution)
open P103.Specs.Ch11.TorBalance (commRightFunctor)
open P103.Specs.Ch12.TorBaseChange (commutativeTor)

namespace CommutativeAlgebraNotes.Intersection.IsolatedTorSupport.Specs

universe u v w

set_option linter.checkUnivs false in
def torType :=
  ∀ {R : Type u} [CommRing R], ModuleCat.{v} R → ModuleCat.{w} R → ℕ → Type (max u v w)

/-- The ordinary Tor of the chapter, with its canonical coefficient module action. -/
def Tor {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (N : ModuleCat.{w} R) (i : ℕ) : Type _ :=
  P103.Ch11.ExtTorDefinitions.Tor R ((commRightFunctor R).obj M) N i

instance {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (N : ModuleCat.{w} R) (i : ℕ) : AddCommGroup (Tor M N i) :=
  inferInstanceAs (AddCommGroup (P103.Ch11.ExtTorDefinitions.Tor R
    ((commRightFunctor R).obj M) N i))

instance {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (N : ModuleCat.{w} R) (i : ℕ) : Module R (Tor M N i) :=
  P103.Ch11.ExtTorDefinitions.canonicalTorModule R ((commRightFunctor R).obj M) N i

def tensorSupport : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N],
    Module.support R (M ⊗[R] N) = Module.support R M ∩ Module.support R N

def tensorNontrivial : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N],
    Nontrivial (M ⊗[R] N)

def finiteLengthIffSupport : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M],
    IsFiniteLength R M ↔ Module.support R M ⊆ {IsLocalRing.closedPoint R}

def isolatedTensorIff : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N],
    IsFiniteLength R (M ⊗[R] N) ↔
      Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R}

def torSymmetry : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (i : ℕ),
    Nonempty (Tor M N i ≃ₗ[R] Tor N M i)

def torZero : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R),
    Nonempty (Tor M N 0 ≃ₗ[R] M ⊗[R] N)

def torComputeLeft : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (P : LeftResolution R M),
    P.IsProjective → ∀ i, Nonempty (Tor M N i ≃ₗ[R] commutativeTor P N i)

def torComputeRight : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (Q : LeftResolution R N),
    Q.IsProjective → ∀ i, Nonempty (Tor M N i ≃ₗ[R] commutativeTor Q M i)

def flatTorBaseChange : Prop :=
  ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (P : LeftResolution R M),
    P.IsProjective → ∀ i, Nonempty (S ⊗[R] Tor M N i ≃ₗ[S]
      Tor (ModuleCat.of S (S ⊗[R] M)) (ModuleCat.of S (S ⊗[R] N)) i)

def torLocalization : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (T : Submonoid R) (i : ℕ),
    Nonempty (LocalizedModule T (Tor M N i) ≃ₗ[Localization T]
      Tor (ModuleCat.of (Localization T) (LocalizedModule T M))
        (ModuleCat.of (Localization T) (LocalizedModule T N)) i)

def torSupport : Prop :=
  ∀ {R : Type u} [CommRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (i : ℕ),
    Module.support R (Tor M N i) ⊆ Module.support R M ∩ Module.support R N

def homologyFinite : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) [Module.Finite R N]
    (P : LeftResolution R M), (∀ j, Module.Finite R (P.complex.X j)) →
    ∀ i, Module.Finite R (commutativeTor P N i)

def torFinite : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] (i : ℕ), Module.Finite R (Tor M N i)

def torFiniteLength : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N],
    Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R} →
    ∀ i, IsFiniteLength R (Tor M N i)

def torFiniteLengthOfTensor : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N],
    IsFiniteLength R (M ⊗[R] N) → ∀ i, IsFiniteLength R (Tor M N i)

open _root_.AdvCommAlg.Koszul in
def koszulTorModel : Prop :=
  ∀ {R : Type u} [CommRing R]
    (N : ModuleCat.{w} R) (x : List R)
    (_ : RingTheory.Sequence.IsRegular R x) (i : ℕ),
    Nonempty (((quotientTorFunctor (listIdeal x) i).obj N) ≃ₗ[R]
      Tor (ModuleCat.of R (R ⧸ listIdeal x)) N i)

open _root_.AdvCommAlg.Koszul in
def koszulHomologyTor : Prop :=
  ∀ {R : Type u} [CommRing R]
    (N : ModuleCat.{w} R) (x : List R)
    (_ : RingTheory.Sequence.IsRegular R x) (i : ℕ),
    Nonempty (homology N x i ≃ₗ[R] Tor (ModuleCat.of R (R ⧸ listIdeal x)) N i)

end CommutativeAlgebraNotes.Intersection.IsolatedTorSupport.Specs
