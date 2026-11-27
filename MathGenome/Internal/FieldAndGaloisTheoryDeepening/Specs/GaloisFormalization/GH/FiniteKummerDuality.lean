import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KummerRadicals

/-! Finite Kummer correspondence and its evaluation pairing. -/

namespace Specs.GaloisFormalization.GH.FiniteKummerDuality

open KummerCoefficients KummerRadicals

universe u v

/-- The finite subgroups of the quotient of scalar units by `m`-th powers. -/
abbrev FinitePowerSubgroups (k : Type u) [Field k] (m : ℕ) :=
  {D : Subgroup (PowerClasses k m) // Finite D}

/-- The finite Galois intermediate fields with abelian Galois group of exponent dividing `m`. -/
abbrev AbelianKummerLayers (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    (m : ℕ) :=
  {L : FiniteGaloisIntermediateField k S //
    (∀ g h : Gal(L/k), g * h = h * g) ∧ (∀ g : Gal(L/k), g ^ m = 1)}

/-- Adjoining radicals and taking the classes that become powers are inverse
on the specified subgroups and embedded fields. -/
def FiniteKummerCorrespondence : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {m : ℕ}, 1 ≤ m → IsUnit (m : k) → rootsInBase k S m →
    ∃ e : FinitePowerSubgroups k m ≃ AbelianKummerLayers k S m,
      (∀ D, (e D).val.toIntermediateField = radicalField D.val) ∧
      (∀ L, (e.symm L).val = classesOfField m L.val.toIntermediateField)

/-- Evaluation in either variable gives the character group of the other
factor. The formula is valid for every representative and every root of it. -/
def PerfectRadicalPairing : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {m : ℕ}, 1 ≤ m → IsUnit (m : k) → rootsInBase k S m →
    ∀ (D : Subgroup (PowerClasses k m)) [Finite D]
      (L : FiniteGaloisIntermediateField k S), L.toIntermediateField = radicalField D →
      ∃ (eG : Gal(L/k) ≃* (D →* Roots S m)) (eD : D ≃* (Gal(L/k) →* Roots S m)),
        (∀ (g : Gal(L/k)) (d : D), eG g d = eD d g) ∧
        ∀ (d : D) (a : kˣ), powerClass k m a = d.val →
          (∃ α : Lˣ, α ^ m = Units.map (algebraMap k L) a) ∧
          ∀ (α : Lˣ), α ^ m = Units.map (algebraMap k L) a →
            ∀ g : Gal(L/k), (eG g d : Sˣ) =
              Units.map (algebraMap L S) ((g • α) / α)

end Specs.GaloisFormalization.GH.FiniteKummerDuality
