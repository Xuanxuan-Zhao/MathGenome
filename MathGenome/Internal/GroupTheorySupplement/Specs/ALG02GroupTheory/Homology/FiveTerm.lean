import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.Transgression
import Mathlib.Algebra.Exact.Basic

open CategoryTheory

universe u

namespace ALG02GroupTheory.FiveTerm

open IntegralBar BarProjectionKernel Transgression

noncomputable section

variable {N E Q N' E' Q' : Type u}
variable [Group N] [Group E] [Group Q] [Group N'] [Group E'] [Group Q']

/-- Regard an additive map of integral modules as a group homomorphism. -/
abbrev asMultiplicative {X Y : ModuleCat.{u} Integers.{u}} (f : X ⟶ Y) :
    Multiplicative X →* Multiplicative Y :=
  f.hom.toAddMonoidHom.toMultiplicative

namespace Spec

/-- Exactness at the three middle objects and at the final first homology group. -/
def SequenceExact (S : GroupExtension N E Q)
    (d : Multiplicative (homology Q 2) →* KernelQuotient S)
    (i : KernelQuotient S →* Multiplicative (homology E 1)) : Prop :=
  Function.MulExact (asMultiplicative (homologyMap S.rightHom 2)) d ∧
    Function.MulExact d i ∧
    Function.MulExact i (asMultiplicative (homologyMap S.rightHom 1)) ∧
    Function.Surjective (homologyMap S.rightHom 1)

/-- The identifications of the two second-page terms are given by projection
of a representative cycle and by sending the class of [i(n)] to the class of n.
Under them, the transgression is the map induced by the bar boundary. -/
def IsSignedTransgression (S : GroupExtension N E Q)
    (d : Multiplicative (homology Q 2) →* KernelQuotient S) : Prop :=
  ∃ (s : PageTwoSource S ≃ₗ[Integers.{u}] homology Q 2)
    (t : Multiplicative (PageTwoTarget S) ≃* KernelQuotient S),
    (∀ (x : sourceCycles S)
      (hx : barBoundary Q 1 ((normalizedChainsMap S.rightHom).f 2 x.val) = 0),
      HomologicalComplex.homologyMap (normalization Q) 2
          (s ((sourceRelations S).mkQ x)) =
        classOf (normalizedChains Q) ((normalizedChainsMap S.rightHom).f 2 x.val) hx) ∧
    (∀ (n : N) (x : barFiltration S 0 1) (_hx : x.val = normalizedBar 1 ![S.inl n]),
      t (Multiplicative.ofAdd ((targetRelations S).mkQ x)) = QuotientGroup.mk n) ∧
    (∀ x : PageTwoSource S,
      t (Multiplicative.ofAdd (pageTwoDifferential S x)) = d (Multiplicative.ofAdd (s x)))

/-- The four squares of the five-term sequence for a morphism of extensions. -/
def SequenceNatural {S : GroupExtension N E Q} {T : GroupExtension N' E' Q'}
    (f : ExtensionHom S T)
    (dS : Multiplicative (homology Q 2) →* KernelQuotient S)
    (iS : KernelQuotient S →* Multiplicative (homology E 1))
    (dT : Multiplicative (homology Q' 2) →* KernelQuotient T)
    (iT : KernelQuotient T →* Multiplicative (homology E' 1)) : Prop :=
  (∀ (x : homology E 2),
    homologyMap T.rightHom 2 (homologyMap f.middle 2 x) =
      homologyMap f.quotient 2 (homologyMap S.rightHom 2 x)) ∧
  (∀ (x : homology Q 2),
    dT (Multiplicative.ofAdd (homologyMap f.quotient 2 x)) =
      quotientMap f (dS (Multiplicative.ofAdd x))) ∧
  (∀ x : KernelQuotient S,
    iT (quotientMap f x) = asMultiplicative (homologyMap f.middle 1) (iS x)) ∧
  (∀ (x : homology E 1),
    homologyMap T.rightHom 1 (homologyMap f.middle 1 x) =
      homologyMap f.quotient 1 (homologyMap S.rightHom 1 x))

/-- The natural homological five-term sequence for arbitrary discrete group extensions. -/
def NaturalFiveTerm : Prop :=
  ∃ (d : ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q),
        Multiplicative (homology Q 2) →* KernelQuotient S)
    (i : ∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q),
        KernelQuotient S →* Multiplicative (homology E 1)),
    (∀ {N E Q : Type u} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q),
      SequenceExact S (d S) (i S) ∧
      (∀ n : N, i S (QuotientGroup.mk n) =
        Multiplicative.ofAdd (homologyMap S.inl 1 (generatorClass n))) ∧
      IsSignedTransgression S (d S)) ∧
    (∀ {N E Q N' E' Q' : Type u} [Group N] [Group E] [Group Q]
      [Group N'] [Group E'] [Group Q'] {S : GroupExtension N E Q}
      {T : GroupExtension N' E' Q'} (f : ExtensionHom S T),
      SequenceNatural f (d S) (i S) (d T) (i T))

end Spec

end

end ALG02GroupTheory.FiveTerm
