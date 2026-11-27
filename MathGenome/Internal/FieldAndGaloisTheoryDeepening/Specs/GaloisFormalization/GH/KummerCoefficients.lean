import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Discrete Kummer coefficients for the chosen separable closure. -/

namespace Specs.GaloisFormalization.GH.KummerCoefficients

universe u v

variable (F : Type v) [Field F] (m : ℕ)

/-- The group of (m)-th roots of unity, as a subgroup of the units. -/
abbrev Roots : Subgroup Fˣ := rootsOfUnity m F

def powerMap : Fˣ →* Fˣ := powMonoidHom m

abbrev PowerClasses := Fˣ ⧸ (powerMap F m).range

def powerClass : Fˣ →* PowerClasses F m := QuotientGroup.mk' (powerMap F m).range

def rootsInclusion : Roots F m →* Fˣ := (Roots F m).subtype

def additiveInclusion : Additive (Roots F m) →+ Additive Fˣ :=
  (rootsInclusion F m).toAdditive

def additivePowerMap : Additive Fˣ →+ Additive Fˣ :=
  (powerMap F m).toAdditive

variable (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]

/-- All roots of unity in the extension are in the image of the scalar units. -/
def rootsInBase (m : ℕ) : Prop :=
  ∀ z : Roots S m, ∃ a : kˣ, Units.map (algebraMap k S) a = (z : Sˣ)

/-- The restriction of the usual action on the units. -/
abbrev rootsAction (m : ℕ) : MulDistribMulAction Gal(S/k) (Roots S m) :=
  letI : SMul Gal(S/k) (Roots S m) :=
    ⟨fun g z => ⟨g • (z : Sˣ), by
      change (g • (z : Sˣ)) ^ m = 1
      rw [← smul_pow', z.property, smul_one]⟩⟩
  Function.Injective.mulDistribMulAction (rootsInclusion S m) Subtype.val_injective
    (fun _ _ => rfl)

/-- The same coefficient action with the unit multiplication written additively. -/
private abbrev additiveAction (G A : Type*) [Monoid G] [Monoid A]
    [MulDistribMulAction G A] : DistribMulAction G (Additive A) where
  smul g a := Additive.ofMul (g • a.toMul)
  one_smul a := congrArg Additive.ofMul (one_smul G a.toMul)
  mul_smul g h a := congrArg Additive.ofMul (mul_smul g h a.toMul)
  smul_zero g := congrArg Additive.ofMul (smul_one g : g • (1 : A) = 1)
  smul_add g a b := congrArg Additive.ofMul (smul_mul' g a.toMul b.toMul)

attribute [local instance] rootsAction

abbrev additiveRootsAction (m : ℕ) : DistribMulAction Gal(S/k) (Additive (Roots S m)) :=
  additiveAction _ _

abbrev additiveUnitsAction : DistribMulAction Gal(S/k) (Additive Sˣ) :=
  additiveAction _ _

attribute [local instance] additiveRootsAction additiveUnitsAction

section DefinitionTypes

set_option linter.checkUnivs false

def Roots_type :=
  ∀ (F : Type v) [Field F], ℕ → Subgroup Fˣ

def powerMap_type :=
  ∀ (F : Type v) [Field F], ℕ → (Fˣ →* Fˣ)

def PowerClasses_type :=
  ∀ (F : Type v) [Field F], ℕ → Type v

def powerClass_type :=
  ∀ (F : Type v) [Field F] (m : ℕ), Fˣ →* PowerClasses F m

def rootsInclusion_type :=
  ∀ (F : Type v) [Field F] (m : ℕ), Roots F m →* Fˣ

def additiveInclusion_type :=
  ∀ (F : Type v) [Field F] (m : ℕ), Additive (Roots F m) →+ Additive Fˣ

def additivePowerMap_type :=
  ∀ (F : Type v) [Field F], ℕ → (Additive Fˣ →+ Additive Fˣ)

def rootsInBase_type :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S], ℕ → Prop

def rootsAction_type :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] (m : ℕ),
    MulDistribMulAction Gal(S/k) (Roots S m)

def additiveRootsAction_type :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] (m : ℕ),
    DistribMulAction Gal(S/k) (Additive (Roots S m))

def additiveUnitsAction_type :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S],
    DistribMulAction Gal(S/k) (Additive Sˣ)

end DefinitionTypes

def powerMap_ker_type : Prop :=
  ∀ (F : Type v) [Field F] (m : ℕ), (powerMap F m).ker = Roots F m

def rootsInclusion_equivariant_type : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
    {m : ℕ} (g : Gal(S/k)) (z : Roots S m),
    rootsInclusion S m (g • z) = g • rootsInclusion S m z

def powerMap_equivariant_type : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
    (m : ℕ) (g : Gal(S/k)) (a : Sˣ),
    powerMap S m (g • a) = g • powerMap S m a

def powerMap_surjective_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {m : ℕ}, 1 ≤ m → IsUnit (m : k) → Function.Surjective (powerMap S m)

def coefficients_exact_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {m : ℕ}, 1 ≤ m → IsUnit (m : k) →
    Function.Injective (rootsInclusion S m) ∧
      Function.MulExact (rootsInclusion S m) (powerMap S m) ∧
      Function.Surjective (powerMap S m)

def continuous_coefficientMaps_type : Prop :=
  ∀ (F : Type v) [Field F] (m : ℕ) [TopologicalSpace Fˣ] [DiscreteTopology Fˣ],
    Continuous (rootsInclusion F m) ∧ Continuous (powerMap F m)

def continuous_unitsAction_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ], ContinuousSMul Gal(S/k) Sˣ

def continuous_rootsAction_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] (m : ℕ),
    ContinuousSMul Gal(S/k) (Roots S m)

def fixedUnits_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S],
    ∃ e : kˣ ≃* FixedPoints.subgroup Gal(S/k) Sˣ,
      ∀ a : kˣ, (e a : Sˣ) = Units.map (algebraMap k S) a

def roots_cyclic_type : Prop :=
  ∀ (F : Type v) [Field F] (m : ℕ), 1 ≤ m → IsCyclic (Roots F m)

def roots_card_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {m : ℕ}, 1 ≤ m → IsUnit (m : k) → Nat.card (Roots S m) = m

def primitiveRoot_exists_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {m : ℕ}, 1 ≤ m → IsUnit (m : k) → ∃ ζ : S, IsPrimitiveRoot ζ m

def rootsInBase_of_primitiveRoot_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    {m : ℕ}, 1 ≤ m → (∃ ζ : k, IsPrimitiveRoot ζ m) → rootsInBase k S m

def rootsInBase_iff_trivial_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (m : ℕ), rootsInBase k S m ↔ ∀ (g : Gal(S/k)) (z : Roots S m), g • z = z

def additiveCoefficients_exact_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {m : ℕ}, 1 ≤ m → IsUnit (m : k) →
    Function.Injective (additiveInclusion S m) ∧
      Function.Exact (additiveInclusion S m) (additivePowerMap S m) ∧
      Function.Surjective (additivePowerMap S m)

def additiveInclusion_equivariant_type : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
    {m : ℕ} (g : Gal(S/k)) (z : Additive (Roots S m)),
    additiveInclusion S m (g • z) = g • additiveInclusion S m z

def additivePowerMap_equivariant_type : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
    (m : ℕ) (g : Gal(S/k)) (a : Additive Sˣ),
    additivePowerMap S m (g • a) = g • additivePowerMap S m a

def continuous_additiveCoefficients_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] (m : ℕ),
    ContinuousSMul Gal(S/k) (Additive (Roots S m)) ∧
      ContinuousSMul Gal(S/k) (Additive Sˣ) ∧
      Continuous (additiveInclusion S m) ∧ Continuous (additivePowerMap S m)

end Specs.GaloisFormalization.GH.KummerCoefficients
