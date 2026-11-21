import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.StandardAndPointwiseDefinitions

/-! ET-07, paper.tex 1665–1689. The simple-root assertion has no monicity
hypothesis. Standard form retains the monicity convention of ET-06.
All test rings, including the zero ring, and arbitrary base changes are allowed. -/
namespace Specs.AdvCommAlg.Etale.SimpleRoot

universe u v w
open Polynomial
open StandardAndPointwise
open scoped TensorProduct

/-- The distinguished root in the localized quotient. -/
noncomputable def rootImage {A : Type u} [CommRing A] (f g : A[X]) :
    LocalizedQuotient f g :=
  algebraMap (AdjoinRoot f) (LocalizedQuotient f g) (AdjoinRoot.root f)

def simpleRootEtale : Prop := ∀ (A : Type u) [CommRing A] (f g : A[X]),
  IsUnit (derivativeImage f g) → etaleValue A (LocalizedQuotient f g)

/-- The first-order correction for every representative of the root of every
map to a square-zero quotient, with uniqueness among all roots over that root. -/
def simpleRootCorrection : Prop := ∀ {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] [Algebra A D] (f g : A[X]),
  IsUnit (derivativeImage f g) → ∀ (J : Ideal D), J ^ 2 = ⊥ →
  ∀ (φ : LocalizedQuotient f g →ₐ[A] D ⧸ J) (x : D),
  Ideal.Quotient.mk J x = φ (rootImage f g) →
  ∃ v : Dˣ, (v : D) = aeval x f.derivative ∧
    let y := x - aeval x f * (↑(v⁻¹) : D)
    Ideal.Quotient.mk J y = φ (rootImage f g) ∧
    aeval y f = 0 ∧ IsUnit (aeval y g) ∧
    ∀ z : D, Ideal.Quotient.mk J z = φ (rootImage f g) → aeval z f = 0 → z = y

/-- The corresponding algebra map has exactly one lift. -/
def simpleRootLifting : Prop := ∀ {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] [Algebra A D] (f g : A[X]),
  IsUnit (derivativeImage f g) → ∀ (J : Ideal D), J ^ 2 = ⊥ →
  ∀ φ : LocalizedQuotient f g →ₐ[A] D ⧸ J,
    ∃! ψ : LocalizedQuotient f g →ₐ[A] D, (Ideal.Quotient.mkₐ A J).comp ψ = φ

/-- The inverted localization generator has a forced image under every map. -/
def localizationInverseForced : Prop := ∀ {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] [Algebra A D] (f g : A[X])
    (ψ : LocalizedQuotient f g →ₐ[A] D) (z : D),
  aeval (ψ (rootImage f g)) g * z = 1 ↔
    z = ψ (IsLocalization.Away.invSelf (AdjoinRoot.mk f g))

def standardEtaleEtale : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B],
  standardEtaleValue A B → etaleValue A B

def standardLocalization : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B],
  standardEtaleValue A B → ∀ b : B, standardEtaleValue A (Localization.Away b)

def standardBaseChange : Prop := ∀ (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'],
  standardEtaleValue A B → standardEtaleValue A' (A' ⊗[A] B)

end Specs.AdvCommAlg.Etale.SimpleRoot
