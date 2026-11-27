import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KummerConnecting

/-! Radical fields and their characters inside a chosen separable closure. -/

namespace Specs.GaloisFormalization.GH.KummerRadicals

open IntermediateField
open KummerCoefficients

universe u v w

section Definitions

variable {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]

/-- Adjoin all roots of all representatives of the indicated power classes.
The generator theorem identifies this field with that obtained from any
choice of representatives and roots of a generating family. -/
noncomputable def radicalField {m : ℕ} (D : Subgroup (PowerClasses k m)) :
    IntermediateField k S :=
  adjoin k {x : S | ∃ (a : kˣ) (α : Sˣ), powerClass k m a ∈ D ∧
    α ^ m = Units.map (algebraMap k S) a ∧ (α : S) = x}

/-- The image in the power quotient of the scalar units that become powers in `L`. -/
def classesOfField (m : ℕ) (L : IntermediateField k S) : Subgroup (PowerClasses k m) :=
  (((powerMap L m).range.map (Units.map (algebraMap L S).toMonoidHom)).comap
    (Units.map (algebraMap k S).toMonoidHom)).map (powerClass k m)

variable [TopologicalSpace Sˣ] [DiscreteTopology Sˣ]

/-- The intersection in the absolute Galois group of the kernels for classes in `D`. -/
def characterKernelIntersection {m : ℕ} (D : Subgroup (PowerClasses k m))
    (e : PowerClasses k m ≃* (Gal(S/k) →ₜ* Roots S m)) : Subgroup Gal(S/k) :=
  ⨅ d : D, (e d).toMonoidHom.ker

/-- The ratio property of the character isomorphism supplied by GH06. -/
def HasKummerRatios {m : ℕ} (e : PowerClasses k m ≃* (Gal(S/k) →ₜ* Roots S m)) : Prop :=
  ∀ (a : kˣ) (α : Sˣ), α ^ m = Units.map (algebraMap k S) a →
    ∀ g : Gal(S/k), (e (powerClass k m a) g : Sˣ) = (g • α) / α

end Definitions

-- Full types for the definitions exposed to the implementation.
set_option linter.checkUnivs false in
def radicalField_type :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] {m : ℕ},
    Subgroup (PowerClasses k m) → IntermediateField k S

set_option linter.checkUnivs false in
def classesOfField_type :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S],
    ∀ m : ℕ, IntermediateField k S → Subgroup (PowerClasses k m)

set_option linter.checkUnivs false in
def characterKernelIntersection_type :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] {m : ℕ},
    Subgroup (PowerClasses k m) →
      (PowerClasses k m ≃* (Gal(S/k) →ₜ* Roots S m)) → Subgroup Gal(S/k)

/-- The pointwise stabilizer of a single radical extension is its character kernel. -/
def FixingSubgroupAdjoinRoot : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] {m : ℕ}
    {e : PowerClasses k m ≃* (Gal(S/k) →ₜ* Roots S m)}, HasKummerRatios e →
    ∀ (a : kˣ) (α : Sˣ), α ^ m = Units.map (algebraMap k S) a →
      (adjoin k ({(α : S)} : Set S)).fixingSubgroup =
        (e (powerClass k m a)).toMonoidHom.ker

/-- Every family of roots of representatives of a generating family gives the
same intermediate field. In particular this applies to any finite generating set. -/
def RadicalFieldOfGenerators : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {m : ℕ}, 1 ≤ m → IsUnit (m : k) → rootsInBase k S m →
    ∀ (D : Subgroup (PowerClasses k m)) {ι : Type w} (a : ι → kˣ) (α : ι → Sˣ),
      Subgroup.closure (Set.range fun i => powerClass k m (a i)) = D →
      (∀ i, α i ^ m = Units.map (algebraMap k S) (a i)) →
      radicalField (S := S) D = adjoin k (Set.range fun i => (α i : S))

/-- The radical field and the intersection of character kernels recover each other. -/
def RadicalFieldFixedField : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] {m : ℕ}, 1 ≤ m → IsUnit (m : k) →
    ∀ {e : PowerClasses k m ≃* (Gal(S/k) →ₜ* Roots S m)}, HasKummerRatios e →
    ∀ D : Subgroup (PowerClasses k m),
      (radicalField (S := S) D).fixingSubgroup = characterKernelIntersection D e ∧
      radicalField (S := S) D = fixedField (characterKernelIntersection D e)

/-- A finite subgroup of classes gives an open normal kernel and a finite Galois layer. -/
def RadicalFieldFiniteGalois : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] {m : ℕ}, 1 ≤ m → IsUnit (m : k) →
    ∀ {e : PowerClasses k m ≃* (Gal(S/k) →ₜ* Roots S m)}, HasKummerRatios e →
    ∀ (D : Subgroup (PowerClasses k m)) [Finite D],
      IsOpen (characterKernelIntersection D e : Set Gal(S/k)) ∧
      (characterKernelIntersection D e).Normal ∧
      ∃ L : FiniteGaloisIntermediateField k S, L.toIntermediateField = radicalField (S := S) D

/-- The Galois group embeds by evaluation on the classes in `D`. Consequently it
is abelian and every element has order dividing `m`. -/
def RadicalGaloisGroup : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] {m : ℕ}, 1 ≤ m → IsUnit (m : k) →
    ∀ {e : PowerClasses k m ≃* (Gal(S/k) →ₜ* Roots S m)}, HasKummerRatios e →
    ∀ (D : Subgroup (PowerClasses k m)) (L : FiniteGaloisIntermediateField k S),
      L.toIntermediateField = radicalField (S := S) D →
      (∃ f : Gal(L/k) →* (D → Roots S m), Function.Injective f ∧
        ∀ (g : Gal(S/k)) (d : D), f (KrullLayers.restrict L g) d = e d g) ∧
      (∀ g h : Gal(L/k), g * h = h * g) ∧ (∀ g : Gal(L/k), g ^ m = 1)

/-- Membership in `D_L` is equivalent to the chosen root of the given
representative lying in `L`. This applies to every representative and root. -/
def MemClassesOfField : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {m : ℕ}, 1 ≤ m → IsUnit (m : k) → rootsInBase k S m →
    ∀ (L : IntermediateField k S) (a : kˣ) (α : Sˣ),
      α ^ m = Units.map (algebraMap k S) a →
      (powerClass k m a ∈ classesOfField m L ↔ (α : S) ∈ L)

/-- The classes of a finite Galois layer are exactly the characters trivial on
its restriction kernel. The induced equivalence with homomorphisms on the
layer is compatible with restriction and with the root-ratio pairing in `L`. -/
def ClassesOfFieldCharacters : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] {m : ℕ},
    1 ≤ m → IsUnit (m : k) → rootsInBase k S m →
    ∀ {e : PowerClasses k m ≃* (Gal(S/k) →ₜ* Roots S m)}, HasKummerRatios e →
    ∀ L : FiniteGaloisIntermediateField k S,
      (∀ a : PowerClasses k m, a ∈ classesOfField m L.toIntermediateField ↔
        L.toIntermediateField.fixingSubgroup ≤ (e a).toMonoidHom.ker) ∧
      ∃ eL : classesOfField m L.toIntermediateField ≃* (Gal(L/k) →* Roots S m),
        (∀ (a : classesOfField m L.toIntermediateField) (g : Gal(S/k)),
          eL a (KrullLayers.restrict L g) = e a g) ∧
        ∀ (a : kˣ) (α : Lˣ), α ^ m = Units.map (algebraMap k L) a →
          ∀ (ha : powerClass k m a ∈ classesOfField m L.toIntermediateField) (g : Gal(L/k)),
            (eL ⟨powerClass k m a, ha⟩ g : Sˣ) =
              Units.map (algebraMap L S) ((g • α) / α)

end Specs.GaloisFormalization.GH.KummerRadicals
