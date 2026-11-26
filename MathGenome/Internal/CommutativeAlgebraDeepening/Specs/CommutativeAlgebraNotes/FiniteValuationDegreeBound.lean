import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.OrderedValuationGroups
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Specs.CommutativeAlgebraNotes.FiniteValuationDegreeBound

open Specs.CommutativeAlgebraNotes.OrderedValuationGroups

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The inclusion of valuation rings obtained by contracting along the field inclusion. -/
def inclusion (V : ValuationSubring K) (W : ValuationSubring L)
    (h : W.comap (algebraMap K L) = V) : V →+* W :=
  (algebraMap K L).restrict V.toSubring W.toSubring fun _ hx =>
    ValuationSubring.mem_comap.mp (h.symm ▸ hx)

/-- The fundamental inequality for a finite extension of valued fields. -/
def DegreeBound : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (h : W.comap (algebraMap K L) = V),
    ∃ (g : valueGroup V →+o valueGroup W)
      (r : IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField W),
      StrictMono g ∧ Function.Injective r ∧
      (∀ a : Kˣ, g (value V (Additive.ofMul a)) =
        value W (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom a))) ∧
      r.comp (IsLocalRing.residue V) = (IsLocalRing.residue W).comp (inclusion V W h) ∧
      Finite (valueGroup W ⧸ g.toAddMonoidHom.range) ∧
      (letI := r.toAlgebra
       FiniteDimensional (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField W) ∧
       Nat.card (valueGroup W ⧸ g.toAddMonoidHom.range) *
         Module.finrank (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField W) ≤
           Module.finrank K L)

end Specs.CommutativeAlgebraNotes.FiniteValuationDegreeBound
