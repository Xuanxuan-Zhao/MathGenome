import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.FieldTheory.RatFunc.Basic

/-! The examples in paper.tex:3019–3023. We represent k[x,y] as k[y][x].
The inner polynomial variable is y, and the outer variable is x. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace AdvCommAlg.Depth.LocalizationExamples

abbrev Plane (k : Type u) [Field k] := Polynomial (Polynomial k)

instance planeCommRing (k : Type u) [Field k] : CommRing (Plane k) :=
  inferInstanceAs (CommRing (Polynomial (Polynomial k)))

def originEvaluation (k : Type u) [Field k] : Plane k →+* k :=
  Polynomial.constantCoeff.comp Polynomial.constantCoeff

def originIdeal (k : Type u) [Field k] : Ideal (Plane k) :=
  RingHom.ker (originEvaluation k)

instance originIdeal_isMaximal (k : Type u) [Field k] : (originIdeal k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (originEvaluation k)
    (fun a => ⟨Polynomial.C (Polynomial.C a), by simp [originEvaluation]⟩)

abbrev LocalPlane (k : Type u) [Field k] := Localization.AtPrime (originIdeal k)

instance localPlaneCommRing (k : Type u) [Field k] : CommRing (LocalPlane k) :=
  inferInstanceAs (CommRing (Localization (originIdeal k).primeCompl))

def x (k : Type u) [Field k] : LocalPlane k :=
  algebraMap (Plane k) (LocalPlane k) Polynomial.X

def y (k : Type u) [Field k] : LocalPlane k :=
  algebraMap (Plane k) (LocalPlane k) (Polynomial.C Polynomial.X)

def axisIdeal (k : Type u) [Field k] : Ideal (Plane k) :=
  RingHom.ker (Polynomial.constantCoeff : Plane k →+* Polynomial k)

instance axisIdeal_isPrime (k : Type u) [Field k] : (axisIdeal k).IsPrime :=
  RingHom.ker_isPrime _

lemma axisIdeal_le_originIdeal (k : Type u) [Field k] : axisIdeal k ≤ originIdeal k := by
  intro f hf
  change Polynomial.constantCoeff (Polynomial.constantCoeff f) = 0
  change Polynomial.constantCoeff f = 0 at hf
  simp [hf]

def localAxisIdeal (k : Type u) [Field k] : Ideal (LocalPlane k) :=
  (axisIdeal k).map (algebraMap (Plane k) (LocalPlane k))

instance localAxisIdeal_isPrime (k : Type u) [Field k] : (localAxisIdeal k).IsPrime := by
  apply IsLocalization.isPrime_of_isPrime_disjoint (originIdeal k).primeCompl
    (LocalPlane k) (axisIdeal k) inferInstance
  exact Set.disjoint_left.mpr fun _ hs hp => hs (axisIdeal_le_originIdeal k hp)

abbrev AxisLocalization (k : Type u) [Field k] := Localization.AtPrime (localAxisIdeal k)

/-- The residue action on the original field, by evaluation at the origin. -/
def residueMap (k : Type u) [Field k] : LocalPlane k →+* k :=
  IsLocalization.lift (M := (originIdeal k).primeCompl)
    (g := originEvaluation k) (fun s => isUnit_iff_ne_zero.mpr s.property)

instance residueAlgebra (k : Type u) [Field k] : Algebra (LocalPlane k) k :=
  (residueMap k).toAlgebra

abbrev SplitModule (k : Type u) [Field k] := LocalPlane k × k
abbrev LocalizedSplitModule (k : Type u) [Field k] :=
  LocalizedModule.AtPrime (localAxisIdeal k) (SplitModule k)

/-- k(y)[x], with y the rational-function variable and x the polynomial variable. -/
abbrev GenericLine (k : Type u) [Field k] := Polynomial (RatFunc k)

def genericAxisIdeal (k : Type u) [Field k] : Ideal (GenericLine k) :=
  RingHom.ker (Polynomial.constantCoeff : GenericLine k →+* RatFunc k)

instance genericAxisIdeal_isPrime (k : Type u) [Field k] : (genericAxisIdeal k).IsPrime :=
  RingHom.ker_isPrime _

abbrev GenericLocalLine (k : Type u) [Field k] :=
  Localization.AtPrime (genericAxisIdeal k)

end AdvCommAlg.Depth.LocalizationExamples

namespace AdvCommAlg.Depth.LocalizationExamples.Specs
open AdvCommAlg.Depth.Specs

def maximalIdealType : Prop := ∀ (k : Type u) [Field k],
  IsLocalRing.maximalIdeal (LocalPlane k) = Ideal.span {x k, y k}

def localAxisIdealType : Prop := ∀ (k : Type u) [Field k],
  localAxisIdeal k = Ideal.span {x k}

def parametersRegularType : Prop := ∀ (k : Type u) [Field k],
  RingTheory.Sequence.IsRegular (LocalPlane k) [x k, y k]

def dimensionType : Prop := ∀ (k : Type u) [Field k], ringKrullDim (LocalPlane k) = 2

def ringDepthType : Prop := ∀ (k : Type u) [Field k],
  depthValue (LocalPlane k) (LocalPlane k) = 2

def localizationEquivType : Prop := ∀ (k : Type u) [Field k],
  Nonempty (AxisLocalization k ≃+* GenericLocalLine k)

def localizedRingDepthType : Prop := ∀ (k : Type u) [Field k],
  depthValue (AxisLocalization k) (AxisLocalization k) = 1

def moduleDepthType : Prop := ∀ (k : Type u) [Field k],
  depthValue (LocalPlane k) (SplitModule k) = 0

def localizedModuleEquivType : Prop := ∀ (k : Type u) [Field k],
  Nonempty (LocalizedSplitModule k ≃ₗ[AxisLocalization k] AxisLocalization k)

def localizedModuleDepthType : Prop := ∀ (k : Type u) [Field k],
  depthValue (AxisLocalization k) (LocalizedSplitModule k) = 1

end AdvCommAlg.Depth.LocalizationExamples.Specs
