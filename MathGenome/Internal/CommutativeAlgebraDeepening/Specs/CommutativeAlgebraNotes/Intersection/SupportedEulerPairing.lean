import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.TensorComplexIsolatedHomology
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.BigOperators.Finprod

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators TensorProduct

noncomputable section

namespace CommutativeAlgebraNotes.Intersection.SupportedEulerPairing.Specs

universe u

variable {R : Type u} [CommRing R]

abbrev Complex (R : Type u) [CommRing R] := ChainComplex (ModuleCat.{u} R) ℤ

/-- A bounded complex with finitely generated free terms, including zero terms. -/
def BoundedFiniteFree (F : Complex R) : Prop :=
  Bounded F ∧ (∀ i, Module.Free R (F.X i)) ∧ ∀ i, Module.Finite R (F.X i)

def BoundedFiniteProjective (F : Complex R) : Prop :=
  Bounded F ∧ (∀ i, Projective (F.X i)) ∧ ∀ i, Module.Finite R (F.X i)

def Isolated [IsLocalRing R] (F G : Complex R) : Prop :=
  homologySupport F ∩ homologySupport G ⊆ {IsLocalRing.closedPoint R}

/-- The length sum over the homological grading, including negative degrees. -/
def homologyLengthEuler (K : Complex R) : ℤ :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * ((Module.length R (K.homology i)).toNat : ℤ)

def pairing (F G : Complex R) : ℤ := homologyLengthEuler (tensorTotal F G)

def pairingType := ∀ {R : Type u} [CommRing R], Complex R → Complex R → ℤ

def finiteType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (F G : Complex R), BoundedFiniteFree F → BoundedFiniteFree G → Isolated F G →
      (∀ i, IsFiniteLength R ((tensorTotal F G).homology i)) ∧
      (Function.support (fun i : ℤ => Module.length R ((tensorTotal F G).homology i))).Finite

def additiveLeft : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (S : ShortComplex (Complex R)) (G : Complex R),
    BoundedFiniteFree S.X₁ → BoundedFiniteFree S.X₂ → BoundedFiniteFree S.X₃ →
    BoundedFiniteFree G → S.ShortExact →
    Isolated S.X₁ G → Isolated S.X₂ G → Isolated S.X₃ G →
    pairing S.X₂ G = pairing S.X₁ G + pairing S.X₃ G

def additiveRight : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (F : Complex R) (S : ShortComplex (Complex R)),
    BoundedFiniteFree F → BoundedFiniteFree S.X₁ → BoundedFiniteFree S.X₂ →
    BoundedFiniteFree S.X₃ → S.ShortExact →
    Isolated F S.X₁ → Isolated F S.X₂ → Isolated F S.X₃ →
    pairing F S.X₂ = pairing F S.X₁ + pairing F S.X₃

def quasiIsoLeft : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {F F' : Complex R} (f : F ⟶ F') (G : Complex R),
    BoundedFiniteFree F → BoundedFiniteFree F' → BoundedFiniteFree G →
    QuasiIso f → Isolated F G → Isolated F' G ∧ pairing F G = pairing F' G

def quasiIsoRight : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (F : Complex R) {G G' : Complex R} (g : G ⟶ G'),
    BoundedFiniteFree F → BoundedFiniteFree G → BoundedFiniteFree G' →
    QuasiIso g → Isolated F G → Isolated F G' ∧ pairing F G = pairing F G'

/-- Reindex homological degree `i` to cohomological degree `-i`. -/
def reverseDegrees : (ComplexShape.down ℤ).Embedding (ComplexShape.up ℤ) where
  f := Neg.neg
  injective_f := neg_injective
  rel := by intro i j h; change j + 1 = i at h; change -i + 1 = -j; omega

instance : reverseDegrees.IsRelIff where
  rel' := by intro i j h; change -i + 1 = -j at h; change j + 1 = i; omega

/-- A perfect representative together with its identification in the derived category. -/
def RepresentsPerfect [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (D : DerivedCategory (ModuleCat.{u} R)) (F : Complex R) : Prop :=
  BoundedFiniteProjective F ∧ Nonempty (DerivedCategory.Q.obj (F.extend reverseDegrees) ≅ D)

/-- The homology supports of two perfect complexes have isolated intersection. -/
def IsolatedPerfectPair [IsLocalRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (D E : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ F G : Complex R, RepresentsPerfect D F ∧ RepresentsPerfect E G ∧ Isolated F G

/-- Compute the pairing on any chosen bounded finite projective representatives. -/
def perfectPairing [IsLocalRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (D E : DerivedCategory (ModuleCat.{u} R)) (h : IsolatedPerfectPair D E) : ℤ :=
  pairing h.choose h.choose_spec.choose

def perfectPairingType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (D E : DerivedCategory (ModuleCat.{u} R)), IsolatedPerfectPair D E → ℤ

def perfectPairingWellDefined : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (D E : DerivedCategory (ModuleCat.{u} R)) (h : IsolatedPerfectPair D E)
    (F G : Complex R), RepresentsPerfect D F → RepresentsPerfect E G →
      Isolated F G ∧
      (∀ i, IsFiniteLength R ((tensorTotal F G).homology i)) ∧
      pairing F G = perfectPairing D E h

open P103.Specs.Ch10.Comparison (LeftResolution)
open P103.Specs.Ch10.Complexes (extendNonnegativeChain)

def agreesWithIntersectionEuler : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (P : LeftResolution R M) (Q : LeftResolution R N),
    BoundedFiniteFree (extendNonnegativeChain P.complex) →
    BoundedFiniteFree (extendNonnegativeChain Q.complex) →
    IsFiniteLength R (M ⊗[R] N) →
    Isolated (extendNonnegativeChain P.complex) (extendNonnegativeChain Q.complex) ∧
    pairing (extendNonnegativeChain P.complex) (extendNonnegativeChain Q.complex) =
      IsolatedIntersectionEuler.Specs.intersectionEuler M N

end CommutativeAlgebraNotes.Intersection.SupportedEulerPairing.Specs
