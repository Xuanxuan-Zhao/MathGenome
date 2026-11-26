import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.TotalComplexConstruction
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.HopkinsLevitzki

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CommutativeAlgebraNotes.Intersection

/-- A bounded homologically graded complex, with possibly negative degrees. -/
def Bounded {C : Type*} [Category* C] [HasZeroMorphisms C] (K : ChainComplex C ℤ) : Prop :=
  ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → Limits.IsZero (K.X i)

/-- The homological tensor total, with differential `d ⊗ 1 + (-1)^i (1 ⊗ d)`
on the summand of bidegree `(i,j)`. -/
abbrev tensorTotal {R : Type u} [CommRing R]
    (F G : ChainComplex (ModuleCat.{u} R) ℤ) : ChainComplex (ModuleCat.{u} R) ℤ :=
  HomologicalComplex.tensorObj F G

/-- The union of the supports of all homology modules. -/
def homologySupport {R : Type u} [CommRing R] (F : ChainComplex (ModuleCat.{v} R) ℤ) :
    Set (PrimeSpectrum R) :=
  ⋃ i : ℤ, Module.support R (F.homology i)

namespace Specs

def boundedExactProjectiveContractibleType : Prop :=
  ∀ {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{v} R) ℤ),
    Bounded K → (∀ i, CategoryTheory.Projective (K.X i)) → K.Acyclic →
      Nonempty (Homotopy (𝟙 K) 0)

def tensorTotalContractibleType : Prop :=
  ∀ {R : Type u} [CommRing R] (F G : ChainComplex (ModuleCat.{u} R) ℤ),
    (Nonempty (Homotopy (𝟙 F) 0) ∨ Nonempty (Homotopy (𝟙 G) 0)) →
      Nonempty (Homotopy (𝟙 (tensorTotal F G)) 0)

def tensorTotalFiniteLengthType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (F G : ChainComplex (ModuleCat.{u} R) ℤ),
    Bounded F → Bounded G →
    (∀ i, Module.Free R (F.X i)) → (∀ i, Module.Finite R (F.X i)) →
    (∀ i, Module.Free R (G.X i)) → (∀ i, Module.Finite R (G.X i)) →
    homologySupport F ∩ homologySupport G ⊆ {IsLocalRing.closedPoint R} →
    ∀ i : ℤ, IsFiniteLength R ((tensorTotal F G).homology i)

end Specs
end CommutativeAlgebraNotes.Intersection
