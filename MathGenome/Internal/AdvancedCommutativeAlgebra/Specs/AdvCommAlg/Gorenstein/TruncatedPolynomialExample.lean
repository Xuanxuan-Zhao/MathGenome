import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Artinian.Module

noncomputable section
universe u
namespace AdvCommAlg.Gorenstein.TruncatedPolynomial
open Polynomial

/-- The actual polynomial quotient k[t]/(t^n). -/
abbrev Ring (k : Type u) [Field k] (n : ℕ) := AdjoinRoot ((Polynomial.X : k[X]) ^ n)

/-- The class of the polynomial variable. -/
abbrev t (k : Type u) [Field k] (n : ℕ) : Ring k n :=
  AdjoinRoot.root ((Polynomial.X : k[X]) ^ n)

namespace Specs
/-- GC-14, first example, with the residue field and the explicit socle generator.
The local and Noetherian structures are conclusions, not extra assumptions. -/
def exampleType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 1 ≤ n →
    IsArtinianRing (Ring k n) ∧
    ∃ hLocal : IsLocalRing (Ring k n), letI := hLocal;
      ∃ hNoeth : IsNoetherianRing (Ring k n), letI := hNoeth;
        Nonempty (IsLocalRing.ResidueField (Ring k n) ≃ₐ[k] k) ∧
        t k n ^ (n - 1) ≠ 0 ∧
        (∀ z : Ring k n, z ∈ Gorenstein.Specs.socleValue (Ring k n) (Ring k n) ↔
          ∃ c : k, z = c • t k n ^ (n - 1)) ∧
        Module.finrank (IsLocalRing.ResidueField (Ring k n))
          (Gorenstein.Specs.socleValue (Ring k n) (Ring k n)) = 1 ∧
        Gorenstein.Specs.LocalGorensteinValue (Ring k n)
end Specs
end AdvCommAlg.Gorenstein.TruncatedPolynomial
