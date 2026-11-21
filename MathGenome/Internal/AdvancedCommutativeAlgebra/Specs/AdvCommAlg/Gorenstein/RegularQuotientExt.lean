import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ReesChangeOfRings
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings

/-! Independent statements for the final assertion of GC-03, paper.tex:4466–4468.
The rings and modules are arbitrary. Regular means injectivity of multiplication,
so the zero coefficient module and a unit element are included. -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian
universe u

namespace AdvCommAlg.Gorenstein.RegularQuotientExt
open AdvCommAlg.Depth.Rees AdvCommAlg.Gorenstein.ConcentratedChangeOfRings
variable {S : Type u} [CommRing S]

/-- Ext over the quotient, with its canonical quotient coefficient and maps. -/
def quotientExtFunctor (x : S) (N : ModuleCat.{u} S) (i : ℕ) :
    (ModuleCat.{u} (S ⧸ Ideal.span {x}))ᵒᵖ ⥤ ModuleCat.{u} (S ⧸ Ideal.span {x}) where
  obj M := ModuleCat.of _ (Ext M.unop (quotientModule (Ideal.span {x}) N) i)
  map f := ModuleCat.ofHom (Ext.precompOfLinear (Ext.mk₀ f.unop) _ _ (zero_add i))

end AdvCommAlg.Gorenstein.RegularQuotientExt

namespace Specs.AdvCommAlg.Gorenstein.RegularQuotientExt
open _root_.AdvCommAlg.Depth.Rees
open _root_.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings
open _root_.AdvCommAlg.Gorenstein.RegularQuotientExt

/-- Ext from S/(x) is concentrated in degree one. -/
def concentration : Prop :=
  ∀ (S : Type u) [CommRing S] (x : S) (N : ModuleCat.{u} S),
    IsSMulRegular S x → IsSMulRegular N x →
      Concentrated (Ideal.Quotient.mk (Ideal.span {x})) N 1

/-- The degree-one coefficient is N/xN, linearly over S/(x), naturally in N.
The action on the Ext coefficient is the actual action from its first argument. -/
def coefficientIdentification : Prop :=
  ∀ (S : Type u) [CommRing S] (x : S), IsSMulRegular S x →
    ∃ e : ∀ (N : ModuleCat.{u} S), IsSMulRegular N x →
      (coefficient (Ideal.Quotient.mk (Ideal.span {x})) N 1 ≅
        quotientModule (Ideal.span {x}) N),
      ∀ (N N' : ModuleCat.{u} S) (hN : IsSMulRegular N x)
        (hN' : IsSMulRegular N' x) (f : N ⟶ N')
        (a : FirstExt (Ideal.Quotient.mk (Ideal.span {x}))
          (ModuleCat.of (S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x})) N 1),
        (e N' hN').hom (a.comp (Ext.mk₀ f) (add_zero 1)) =
          quotientMap (Ideal.span {x}) f ((e N hN).hom a)

/-- The full shifted comparison is a natural isomorphism of quotient-module
valued functors of the arbitrary source M, in every nonnegative degree. -/
def comparison : Prop :=
  ∀ (S : Type u) [CommRing S] (x : S) (N : ModuleCat.{u} S),
    IsSMulRegular S x → IsSMulRegular N x → ∀ i : ℕ,
      Nonempty (quotientExtFunctor x N i ≅
        shiftedExtFunctor (Ideal.Quotient.mk (Ideal.span {x})) N 1 i)

/-- Hom over S from every quotient-module to N vanishes. -/
def homVanishing : Prop :=
  ∀ (S : Type u) [CommRing S] (x : S) (N : ModuleCat.{u} S),
    IsSMulRegular S x → IsSMulRegular N x →
      ∀ M : ModuleCat.{u} (S ⧸ Ideal.span {x}),
        Subsingleton (((ModuleCat.restrictScalars
          (Ideal.Quotient.mk (Ideal.span {x}))).obj M) ⟶ N)

end Specs.AdvCommAlg.Gorenstein.RegularQuotientExt
