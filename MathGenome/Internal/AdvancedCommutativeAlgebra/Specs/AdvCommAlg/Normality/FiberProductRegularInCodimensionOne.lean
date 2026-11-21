import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Independent objects and obligations for the second example in SN-12.
The two copies of the same local polynomial ring have independent coordinates:
`(x,y)` in the first projection, `(z,w)` in the second.
-/
noncomputable section
universe u
namespace AdvCommAlg.Normality.FiberProduct

variable (k : Type u) [Field k]

abbrev PolynomialRing (n : ℕ) := MvPolynomial (Fin n) k

def origin (n : ℕ) : Ideal (PolynomialRing k n) :=
  RingHom.ker (MvPolynomial.eval (fun _ => (0 : k)))

instance origin_isMaximal (n : ℕ) : (origin k n).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, by simp⟩)

abbrev LocalPlane := Localization.AtPrime (origin k 2)

/-- Evaluation at the origin extended to fractions whose denominator is nonzero there. -/
def planeResidue : LocalPlane k →+* k :=
  IsLocalization.lift (S := LocalPlane k)
    (g := MvPolynomial.eval (fun _ : Fin 2 => (0 : k)))
    (fun s : (origin k 2).primeCompl => isUnit_iff_ne_zero.mpr s.property)

abbrev Ring := (planeResidue k).pullback (planeResidue k)
abbrev first : Ring k →+* LocalPlane k := (planeResidue k).pullbackFst (planeResidue k)
abbrev second : Ring k →+* LocalPlane k := (planeResidue k).pullbackSnd (planeResidue k)
abbrev firstKernel : Ideal (Ring k) := RingHom.ker (first k)
abbrev secondKernel : Ideal (Ring k) := RingHom.ker (second k)

/-- The library pullback theorem supplies the local structure needed to name
its maximal ideal in the specifications. -/
instance canonicalLocal : IsLocalRing (Ring k) := by
  letI : IsLocalHom (planeResidue k) := IsLocalHom.of_surjective _ (by
    intro a
    exact ⟨algebraMap (PolynomialRing k 2) (LocalPlane k) (MvPolynomial.C a), by
      simp [planeResidue]⟩)
  exact RingHom.isLocalRing_pullback _ _

def crossIdeal : Ideal (PolynomialRing k 4) :=
  Ideal.span {p | ∃ i j : Fin 2,
    p = MvPolynomial.X (Fin.castAdd 2 i) * MvPolynomial.X (Fin.natAdd 2 j)}

abbrev CoordinateRing := PolynomialRing k 4 ⧸ crossIdeal k

def coordinateResidue : CoordinateRing k →+* k :=
  Ideal.Quotient.lift (crossIdeal k) (MvPolynomial.eval (fun _ => (0 : k))) (by
    change crossIdeal k ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    rintro p ⟨i, j, rfl⟩
    simp)

def coordinateOrigin : Ideal (CoordinateRing k) := RingHom.ker (coordinateResidue k)

instance coordinateOrigin_isMaximal : (coordinateOrigin k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun a =>
    ⟨Ideal.Quotient.mk (crossIdeal k) (MvPolynomial.C a), by simp [coordinateResidue]⟩)

abbrev PresentedRing := Localization.AtPrime (coordinateOrigin k)

def planeVariable (i : Fin 2) : LocalPlane k :=
  algebraMap (PolynomialRing k 2) (LocalPlane k) (MvPolynomial.X i)

def pairVariable (i : Fin 4) : Ring k :=
  if h : i.val < 2 then
    ⟨(planeVariable k ⟨i.val, h⟩, 0), by simp [planeVariable, planeResidue]⟩
  else
    ⟨(0, planeVariable k ⟨i.val - 2, by omega⟩), by
      simp [planeVariable, planeResidue]⟩

def presentedVariable (i : Fin 4) : PresentedRing k :=
  algebraMap (CoordinateRing k) (PresentedRing k)
    (Ideal.Quotient.mk (crossIdeal k) (MvPolynomial.X i))

namespace Specs

def planeResidue_surjectiveType : Prop :=
  ∀ (k : Type u) [Field k], Function.Surjective (planeResidue k)

def localType : Prop := ∀ (k : Type u) [Field k], IsLocalRing (Ring k)

def noetherianType : Prop := ∀ (k : Type u) [Field k], IsNoetherianRing (Ring k)

/-- The isomorphism carries each of the four displayed variables to its named
coordinate, and carries coefficients diagonally. -/
def presentationType : Prop :=
  ∀ (k : Type u) [Field k], ∃ e : PresentedRing k ≃+* Ring k,
    (∀ i, e (presentedVariable k i) = pairVariable k i) ∧
    (∀ a : k, e (algebraMap (CoordinateRing k) (PresentedRing k)
      (Ideal.Quotient.mk (crossIdeal k) (MvPolynomial.C a))) =
      ⟨(algebraMap (PolynomialRing k 2) (LocalPlane k) (MvPolynomial.C a),
        algebraMap (PolynomialRing k 2) (LocalPlane k) (MvPolynomial.C a)), by
        simp [planeResidue]⟩)

def dimensionType : Prop := ∀ (k : Type u) [Field k], ringKrullDim (Ring k) = 2

def kernels_mulType : Prop :=
  ∀ (k : Type u) [Field k], firstKernel k * secondKernel k = ⊥

def kernels_supType : Prop :=
  ∀ (k : Type u) [Field k],
    firstKernel k ⊔ secondKernel k = IsLocalRing.maximalIdeal (Ring k)

def nonmaximal_primeType : Prop :=
  ∀ (k : Type u) [Field k] (p : Ideal (Ring k)) [p.IsPrime],
    p ≠ IsLocalRing.maximalIdeal (Ring k) →
      (firstKernel k ≤ p ∧ ¬ secondKernel k ≤ p) ∨
      (secondKernel k ≤ p ∧ ¬ firstKernel k ≤ p)

/-- Each branch uses the image under the appropriate surjective projection;
local dimension/height is part of the conclusion. -/
def localization_firstType : Prop :=
  ∀ (k : Type u) [Field k] (p : Ideal (Ring k)) [p.IsPrime],
    ¬ secondKernel k ≤ p →
    ∃ (q : Ideal (LocalPlane k)) (_ : q.IsPrime),
      q = p.map (first k) ∧ q.comap (first k) = p ∧
      Nonempty (Localization.AtPrime p ≃+* Localization.AtPrime q) ∧
      q.height = p.height

def localization_secondType : Prop :=
  ∀ (k : Type u) [Field k] (p : Ideal (Ring k)) [p.IsPrime],
    ¬ firstKernel k ≤ p →
    ∃ (q : Ideal (LocalPlane k)) (_ : q.IsPrime),
      q = p.map (second k) ∧ q.comap (second k) = p ∧
      Nonempty (Localization.AtPrime p ≃+* Localization.AtPrime q) ∧
      q.height = p.height

def regularInCodimensionOneType : Prop :=
  ∀ (k : Type u) [Field k], ∀ p : PrimeSpectrum (Ring k),
    p.asIdeal.height ≤ (1 : ℕ∞) → IsRegularLocalRing (Localization.AtPrime p.asIdeal)

end Specs
end AdvCommAlg.Normality.FiberProduct
