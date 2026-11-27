import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KummerCoefficients

/-! The Kummer isomorphism and its specialization to continuous characters. -/

namespace Specs.GaloisFormalization.GH.KummerConnecting

open _root_.GaloisFormalization.GH.Model
open KummerCoefficients

universe u v

variable {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
  [IsSepClosure k S] [TopologicalSpace Sˣ] [DiscreteTopology Sˣ]

attribute [local instance] rootsAction

/-- On the discrete roots of unity, stabilizers are the open stabilizers of the
underlying field elements for the Krull topology. -/
local instance (m : ℕ) : ContinuousSMul Gal(S/k) (Roots S m) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro z
  convert stabilizer_isOpen_of_isIntegral (K := k) ((z : Sˣ) : S) using 1
  ext g
  change g • z = z ↔ g ((z : Sˣ) : S) = ((z : Sˣ) : S)
  exact ⟨congrArg (fun w : Roots S m => ((w : Sˣ) : S)),
    fun h => Subtype.ext (Units.ext h)⟩

section

variable (k S) (m : ℕ)

abbrev RootCocycles := continuousCocycles Gal(S/k) (Additive (Roots S m)) 1

abbrev RootCohomology := ContinuousMulH Gal(S/k) (Roots S m) 1

/-- The class of a scalar unit is represented by the ratio cocycle for every root
of its scalar image in the chosen separable closure. -/
def KummerFormula (e : PowerClasses k m ≃* RootCohomology k S m) : Prop :=
  ∀ (a : kˣ) (α : Sˣ), α ^ m = Units.map (algebraMap k S) a →
    ∃ c : RootCocycles k S m,
      e (powerClass k m a) =
        continuousMulClass Gal(S/k) (Roots S m) 1 (Multiplicative.ofAdd c) ∧
      ∀ g : Gal(S/k), ((c.val.val ![g]).toMul : Sˣ) = (g • α) / α

end

/-- The Kummer isomorphism with the natural Galois action on the roots. -/
def KummerIsomorphism : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] {m : ℕ}, 1 ≤ m → IsUnit (m : k) →
    ∃ e : PowerClasses k m ≃* RootCohomology k S m, KummerFormula k S m e

/-- When all roots are scalar units, a class gives the character defined by the
values of any of its cocycle representatives. -/
def CohomologyCharacters : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] {m : ℕ}, rootsInBase k S m →
    ∃ e : RootCohomology k S m ≃* (Gal(S/k) →ₜ* Roots S m),
      ∀ (c : RootCocycles k S m) (g : Gal(S/k)),
        e (continuousMulClass Gal(S/k) (Roots S m) 1 (Multiplicative.ofAdd c)) g =
          (c.val.val ![g]).toMul

/-- The resulting character of a power class is given by the ratio at every
Galois element for every representative and every choice of root. -/
def KummerCharacters : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] {m : ℕ},
    1 ≤ m → IsUnit (m : k) → rootsInBase k S m →
    ∃ e : PowerClasses k m ≃* (Gal(S/k) →ₜ* Roots S m),
      ∀ (a : kˣ) (α : Sˣ), α ^ m = Units.map (algebraMap k S) a →
        ∀ g : Gal(S/k), (e (powerClass k m a) g : Sˣ) = (g • α) / α

end Specs.GaloisFormalization.GH.KummerConnecting
