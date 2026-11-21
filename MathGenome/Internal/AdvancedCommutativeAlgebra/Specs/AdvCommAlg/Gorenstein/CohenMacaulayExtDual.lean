import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.RingTheory.Regular.Category

/-! GC-09, paper.tex:4653–4700. These statements include dimension zero and
all M-regular elements of the maximal ideal, without regularity on the base.
The reduction map is specified by the connecting homomorphism of the actual
short exact sequence; this fixes the canonical, natural isomorphism. -/
noncomputable section
universe u
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.Gorenstein.CMExtDual
open ConcentratedChangeOfRings
variable {R : Type u} [CommRing R]

abbrev Dual (M : ModuleCat.{u} R) (c : ℕ) := Ext M (ModuleCat.of R R) c

/-- Ext of M/xM with its natural first-argument R/(x)-action. -/
abbrev ReducedExt (M : ModuleCat.{u} R) (x : R) (c : ℕ) :=
  FirstExt (Ideal.Quotient.mk (Ideal.span {x}))
    (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) (ModuleCat.of R R) (c + 1)

/-- The connecting map for 0 → M → M → M/xM → 0. -/
def connecting (M : ModuleCat.{u} R) (x : R) (hx : IsSMulRegular M x) (c : ℕ) :
    Dual M c →ₗ[R] Ext (ModuleCat.of R (QuotSMulTop x M)) (ModuleCat.of R R) (c + 1) :=
  hx.smulShortComplex_shortExact.extClass.precompOfLinear R _ (by omega)

end AdvCommAlg.Gorenstein.CMExtDual

namespace AdvCommAlg.Gorenstein.CMExtDualSpecs
open CMExtDual ConcentratedChangeOfRings

def dualPropertiesType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R →
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
      CohenMacaulay.Specs.LocalCohenMacaulayValue R M →
      ∀ s e : ℕ, ringKrullDim R = (s : WithBot ℕ∞) →
        Module.supportDim R M = (e : WithBot ℕ∞) →
        e ≤ s ∧ Module.Finite R (Dual M (s - e)) ∧ Nontrivial (Dual M (s - e)) ∧
          CohenMacaulay.Specs.LocalCohenMacaulayValue R (Dual M (s - e)) ∧
          Module.supportDim R (Dual M (s - e)) = (e : WithBot ℕ∞)

def reductionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R →
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
      CohenMacaulay.Specs.LocalCohenMacaulayValue R M →
      ∀ s e : ℕ, ringKrullDim R = (s : WithBot ℕ∞) →
        Module.supportDim R M = (e : WithBot ℕ∞) →
        ∀ (x : R), x ∈ IsLocalRing.maximalIdeal R → ∀ hx : IsSMulRegular M x,
          IsSMulRegular (Dual M (s - e)) x ∧
          ∃ f : QuotSMulTop x (Dual M (s - e)) ≃ₗ[R ⧸ Ideal.span {x}]
              ReducedExt M x (s - e),
            ∀ a : Dual M (s - e),
              firstExtAddEquiv _ _ _ _ (f (Submodule.Quotient.mk a)) =
                connecting M x hx (s - e) a

/-- Naturality of the connecting maps that induce the reduction equivalences. -/
def connectingNaturalityType : Prop :=
  ∀ (R : Type u) [CommRing R] (M M' : ModuleCat.{u} R) (x : R)
    (hx : IsSMulRegular M x) (hx' : IsSMulRegular M' x) (f : M ⟶ M')
    (c : ℕ) (a : Dual M' c),
    connecting M x hx c ((Ext.mk₀ f).comp a (zero_add c)) =
      (Ext.mk₀ (ModuleCat.ofHom (QuotSMulTop.map x f.hom))).comp
        (connecting M' x hx' c a) (zero_add (c + 1))

end AdvCommAlg.Gorenstein.CMExtDualSpecs
