import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KummerCoefficients
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.KrullLayers

/-! The Kummer short exact sequence over the specified separable closure. -/

namespace GaloisFormalization.GH.KummerCoefficients

universe u v

open Polynomial

variable (F : Type v) [Field F] (m : ℕ)

abbrev Roots : Subgroup Fˣ := rootsOfUnity m F

/-- The power homomorphism on the units of a field. -/
def powerMap : Fˣ →* Fˣ := powMonoidHom m

/-- The quotient of the units by the subgroup of (m)-th powers. -/
abbrev PowerClasses := Fˣ ⧸ (powerMap F m).range

def powerClass : Fˣ →* PowerClasses F m := QuotientGroup.mk' (powerMap F m).range

def rootsInclusion : Roots F m →* Fˣ := (Roots F m).subtype

def additiveInclusion : Additive (Roots F m) →+ Additive Fˣ :=
  (rootsInclusion F m).toAdditive

def additivePowerMap : Additive Fˣ →+ Additive Fˣ :=
  (powerMap F m).toAdditive

theorem powerMap_ker : (powerMap F m).ker = Roots F m :=
  rootsOfUnity_eq_ker.symm

theorem continuous_coefficientMaps [TopologicalSpace Fˣ] [DiscreteTopology Fˣ] :
    Continuous (rootsInclusion F m) ∧ Continuous (powerMap F m) :=
  ⟨continuous_of_discreteTopology, continuous_of_discreteTopology⟩

theorem roots_cyclic (hm : 1 ≤ m) : IsCyclic (Roots F m) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  exact rootsOfUnity.isCyclic F m

variable (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]

/-- All roots of unity in the extension are scalar units. -/
def rootsInBase (m : ℕ) : Prop :=
  ∀ z : Roots S m, ∃ a : kˣ, Units.map (algebraMap k S) a = (z : Sˣ)

instance rootsAction (m : ℕ) : MulDistribMulAction Gal(S/k) (Roots S m) :=
  Specs.GaloisFormalization.GH.KummerCoefficients.rootsAction k S m

instance additiveRootsAction (m : ℕ) : DistribMulAction Gal(S/k) (Additive (Roots S m)) :=
  Specs.GaloisFormalization.GH.KummerCoefficients.additiveRootsAction k S m

instance additiveUnitsAction : DistribMulAction Gal(S/k) (Additive Sˣ) :=
  Specs.GaloisFormalization.GH.KummerCoefficients.additiveUnitsAction k S

variable {k S} in
@[simp]
theorem rootsInclusion_equivariant {m : ℕ} (g : Gal(S/k)) (z : Roots S m) :
    rootsInclusion S m (g • z) = g • rootsInclusion S m z :=
  rfl

variable {k S} in
@[simp]
theorem powerMap_equivariant (m : ℕ) (g : Gal(S/k)) (a : Sˣ) :
    powerMap S m (g • a) = g • powerMap S m a :=
  (smul_pow' g a m).symm

theorem rootsInBase_of_primitiveRoot {m : ℕ} (hm : 1 ≤ m)
    (h : ∃ ζ : k, IsPrimitiveRoot ζ m) : rootsInBase k S m := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨ζ, hζ⟩ := h
  have hmap : (Roots k m).map (Units.map (algebraMap k S)) = Roots S m :=
    hζ.map_rootsOfUnity (algebraMap k S).injective
  intro z
  obtain ⟨a, _, ha⟩ := Subgroup.mem_map.mp (hmap.ge z.property)
  exact ⟨a, ha⟩

private theorem cast_ne_zero {m : ℕ} (hu : IsUnit (m : k)) : (m : S) ≠ 0 := by
  intro h
  apply hu.ne_zero
  apply (algebraMap k S).injective
  simpa only [map_natCast, map_zero] using h

variable {k S} in
@[simp]
theorem additiveInclusion_equivariant {m : ℕ} (g : Gal(S/k)) (z : Additive (Roots S m)) :
    additiveInclusion S m (g • z) = g • additiveInclusion S m z :=
  rootsInclusion_equivariant g z.toMul

variable {k S} in
@[simp]
theorem additivePowerMap_equivariant (m : ℕ) (g : Gal(S/k)) (a : Additive Sˣ) :
    additivePowerMap S m (g • a) = g • additivePowerMap S m a :=
  powerMap_equivariant m g a.toMul

variable [IsSepClosure k S]

theorem powerMap_surjective {m : ℕ} (hm : 1 ≤ m) (hu : IsUnit (m : k)) :
    Function.Surjective (powerMap S m) := by
  let : IsSepClosed S := IsSepClosure.sep_closed k
  let : NeZero (m : S) := ⟨cast_ne_zero k S hu⟩
  intro a
  obtain ⟨x, hx⟩ := IsSepClosed.exists_pow_nat_eq (a : S) m
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa only [zero_pow (Nat.ne_of_gt hm)] using hx.symm)
  exact ⟨Units.mk0 x hx0, Units.ext hx⟩

theorem coefficients_exact {m : ℕ} (hm : 1 ≤ m) (hu : IsUnit (m : k)) :
    Function.Injective (rootsInclusion S m) ∧
      Function.MulExact (rootsInclusion S m) (powerMap S m) ∧
      Function.Surjective (powerMap S m) := by
  refine ⟨Subtype.val_injective, ?_, powerMap_surjective k S hm hu⟩
  intro a
  exact ⟨fun ha => ⟨⟨a, ha⟩, rfl⟩, fun ⟨z, hz⟩ => hz ▸ z.property⟩

theorem continuous_unitsAction [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] :
    ContinuousSMul Gal(S/k) Sˣ :=
  KrullLayers.continuous_unitsAction k S

theorem continuous_rootsAction [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] (m : ℕ) :
    ContinuousSMul Gal(S/k) (Roots S m) := by
  have := continuous_unitsAction k S
  refine ⟨?_⟩
  apply Continuous.subtype_mk
  exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

theorem fixedUnits :
    ∃ e : kˣ ≃* FixedPoints.subgroup Gal(S/k) Sˣ,
      ∀ a : kˣ, (e a : Sˣ) = Units.map (algebraMap k S) a :=
  KrullLayers.fixedUnits_base k S

theorem roots_card {m : ℕ} (hm : 1 ≤ m) (hu : IsUnit (m : k)) :
    Nat.card (Roots S m) = m := by
  classical
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let : IsSepClosed S := IsSepClosure.sep_closed k
  have hsep : (X ^ m - C (1 : S)).Separable :=
    separable_X_pow_sub_C 1 (cast_ne_zero k S hu) one_ne_zero
  have hsplit := IsSepClosed.splits_of_separable _ hsep
  let roots := (nthRoots m (1 : S)).toFinset
  let e : Roots S m ≃ ↥roots :=
    (rootsOfUnityEquivNthRoots S m).trans
      (Equiv.subtypeEquivRight fun _ => Multiset.mem_toFinset.symm)
  calc
    Nat.card (Roots S m) = roots.card := by
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = (nthRoots m (1 : S)).card := Multiset.toFinset_card_of_nodup (nodup_roots hsep)
    _ = m := hsplit.natDegree_eq_card_roots.symm.trans natDegree_X_pow_sub_C

theorem primitiveRoot_exists {m : ℕ} (hm : 1 ≤ m) (hu : IsUnit (m : k)) :
    ∃ ζ : S, IsPrimitiveRoot ζ m := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  exact card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp (roots_card k S hm hu)

theorem rootsInBase_iff_trivial (m : ℕ) :
    rootsInBase k S m ↔ ∀ (g : Gal(S/k)) (z : Roots S m), g • z = z := by
  obtain ⟨e, he⟩ := fixedUnits k S
  constructor
  · intro h g z
    obtain ⟨a, ha⟩ := h z
    apply Subtype.ext
    change g • (z : Sˣ) = (z : Sˣ)
    rw [← ha, ← he]
    exact (FixedPoints.mem_subgroup Gal(S/k) Sˣ (e a)).mp (e a).property g
  · intro h z
    have hz : (z : Sˣ) ∈ FixedPoints.subgroup Gal(S/k) Sˣ :=
      (FixedPoints.mem_subgroup Gal(S/k) Sˣ (z : Sˣ)).mpr
        (fun g => congrArg Subtype.val (h g z))
    obtain ⟨a, ha⟩ := e.surjective ⟨z, hz⟩
    exact ⟨a, (he a).symm.trans (congrArg Subtype.val ha)⟩

theorem additiveCoefficients_exact {m : ℕ} (hm : 1 ≤ m) (hu : IsUnit (m : k)) :
    Function.Injective (additiveInclusion S m) ∧
      Function.Exact (additiveInclusion S m) (additivePowerMap S m) ∧
      Function.Surjective (additivePowerMap S m) :=
  coefficients_exact k S hm hu

theorem continuous_additiveCoefficients [TopologicalSpace Sˣ] [DiscreteTopology Sˣ] (m : ℕ) :
    ContinuousSMul Gal(S/k) (Additive (Roots S m)) ∧
      ContinuousSMul Gal(S/k) (Additive Sˣ) ∧
      Continuous (additiveInclusion S m) ∧ Continuous (additivePowerMap S m) :=
  ⟨continuous_rootsAction k S m, continuous_unitsAction k S,
    (continuous_coefficientMaps S m).1, (continuous_coefficientMaps S m).2⟩

end GaloisFormalization.GH.KummerCoefficients
