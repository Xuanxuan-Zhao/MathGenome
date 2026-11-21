import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Canonical objects for the plane cusp of CM-14 (paper.tex:3730–3742).
The coordinate origin is defined by evaluation at zero, and the local ring
is the localization of the polynomial quotient at that field-valued point.
No assumption on the characteristic of the field is made.
-/
noncomputable section
universe u
namespace AdvCommAlg.CohenMacaulay.Cusp

abbrev Plane (k : Type u) [Field k] := MvPolynomial (Fin 2) k

def equation (k : Type u) [Field k] : Plane k :=
  MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3

def origin (k : Type u) [Field k] : Ideal (Plane k) :=
  RingHom.ker MvPolynomial.constantCoeff

instance origin_isMaximal (k : Type u) [Field k] : (origin k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (fun a => ⟨MvPolynomial.C a, MvPolynomial.constantCoeff_C _ a⟩)

abbrev Ambient (k : Type u) [Field k] := Localization.AtPrime (origin k)

def relationIdeal (k : Type u) [Field k] : Ideal (Plane k) :=
  Ideal.span {equation k}

abbrev CoordinateRing (k : Type u) [Field k] := Plane k ⧸ relationIdeal k

/-- Evaluation at the singular point descends through the cusp equation. -/
def residue (k : Type u) [Field k] : CoordinateRing k →+* k :=
  Ideal.Quotient.lift _ MvPolynomial.constantCoeff (by
    change relationIdeal k ≤ RingHom.ker MvPolynomial.constantCoeff
    rw [relationIdeal, Ideal.span_le]
    rintro _ rfl
    simp [equation, RingHom.mem_ker])

def cuspOrigin (k : Type u) [Field k] : Ideal (CoordinateRing k) :=
  RingHom.ker (residue k)

instance cuspOrigin_isMaximal (k : Type u) [Field k] : (cuspOrigin k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (fun a => ⟨Ideal.Quotient.mk _ (MvPolynomial.C a),
      MvPolynomial.constantCoeff_C _ a⟩)

/-- The local ring in the source, with localization performed after quotienting. -/
abbrev LocalRing (k : Type u) [Field k] := Localization.AtPrime (cuspOrigin k)

def ambientEquation (k : Type u) [Field k] : Ambient k :=
  algebraMap (Plane k) (Ambient k) (equation k)

/-- The alternative presentation, quotienting the local polynomial ring. -/
abbrev Hypersurface (k : Type u) [Field k] :=
  Ambient k ⧸ (relationIdeal k).map (algebraMap (Plane k) (Ambient k))

end AdvCommAlg.CohenMacaulay.Cusp

namespace AdvCommAlg.CohenMacaulay.Specs
open Cusp

def origin_eq_span_coordinatesType : Prop := ∀ (k : Type u) [Field k],
  origin k = Ideal.span (Set.range (MvPolynomial.X : Fin 2 → Plane k))

def cuspOrigin_eq_span_coordinatesType : Prop := ∀ (k : Type u) [Field k],
  cuspOrigin k = Ideal.span
    (Set.range (fun i : Fin 2 => Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X i)))

def equation_ne_zeroType : Prop := ∀ (k : Type u) [Field k], equation k ≠ 0

def equation_mem_origin_sqType : Prop := ∀ (k : Type u) [Field k],
  equation k ∈ origin k ^ 2

def ambient_regularType : Prop := ∀ (k : Type u) [Field k], IsRegularLocalRing (Ambient k)

def ambient_dimensionType : Prop := ∀ (k : Type u) [Field k],
  ringKrullDim (Ambient k) = (2 : WithBot ℕ∞)

def ambientEquation_ne_zeroType : Prop := ∀ (k : Type u) [Field k], ambientEquation k ≠ 0

def ambientEquation_regularType : Prop := ∀ (k : Type u) [Field k],
  Function.Injective (fun a : Ambient k => ambientEquation k * a)

def ambientEquation_mem_maximal_sqType : Prop := ∀ (k : Type u) [Field k],
  ambientEquation k ∈ IsLocalRing.maximalIdeal (Ambient k) ^ 2

def exists_localEquivHypersurfaceType : Prop := ∀ (k : Type u) [Field k],
  Nonempty (LocalRing k ≃+* Hypersurface k)

def local_noetherianType : Prop := ∀ (k : Type u) [Field k], IsNoetherianRing (LocalRing k)

def local_isLocalRingType : Prop := ∀ (k : Type u) [Field k], IsLocalRing (LocalRing k)

def local_cohenMacaulayType : Prop := ∀ (k : Type u) [Field k],
  LocalCohenMacaulayValue (LocalRing k) (LocalRing k)

def local_dimensionType : Prop := ∀ (k : Type u) [Field k],
  ringKrullDim (LocalRing k) = (1 : WithBot ℕ∞)

def local_cotangent_finrankType : Prop := ∀ (k : Type u) [Field k],
  Module.finrank (IsLocalRing.ResidueField (LocalRing k))
    (IsLocalRing.CotangentSpace (LocalRing k)) = 2

def local_not_regularType : Prop := ∀ (k : Type u) [Field k],
  ¬ IsRegularLocalRing (LocalRing k)

end AdvCommAlg.CohenMacaulay.Specs
