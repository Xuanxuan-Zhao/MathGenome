import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.RationalKummer
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.FiniteKummerDuality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Degree

/-! The order of the rational Kummer class and its radical extension. -/

namespace GaloisFormalization.GH.RationalKummer

open Specs.GaloisFormalization.GH.RationalKummer
open Specs.GaloisFormalization.GH.KummerCoefficients
open Specs.GaloisFormalization.GH.FiniteKummerDuality

universe u v

/-- On units, the negative of the valuation at infinity is additive under multiplication. -/
private noncomputable def degreeOnUnits (F : Type u) [Field F] :
    (RatFunc F)ˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (RatFunc.intDegree (x : RatFunc F))
  map_one' := congrArg Multiplicative.ofAdd RatFunc.intDegree_one
  map_mul' x y := congrArg Multiplicative.ofAdd (RatFunc.intDegree_mul x.ne_zero y.ne_zero)

private theorem parameterOrder (F : Type u) [Field F] (m : ℕ) :
    orderOf (powerClass (RatFunc F) m (parameterUnit F)) = m := by
  let x := parameterUnit F
  let c := powerClass (RatFunc F) m x
  have hm : c ^ m = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (x ^ m)).mpr ⟨x, rfl⟩
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hm) ?_
  have h := pow_orderOf_eq_one c
  rw [← map_pow] at h
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff (x ^ orderOf c)).mp h
  change y ^ m = x ^ orderOf c at hy
  have hd := congrArg (fun z => Multiplicative.toAdd (degreeOnUnits F z)) hy
  have hx : Multiplicative.toAdd (degreeOnUnits F x) = 1 := RatFunc.intDegree_X
  simp only [map_pow, toAdd_pow, nsmul_eq_mul, hx, mul_one] at hd
  exact Int.natCast_dvd_natCast.mp ⟨_, hd.symm⟩

theorem parameterClassOrder : ParameterClassOrder.{u} := by
  intro F _ _ m _ _
  exact parameterOrder F m

private theorem cyclicCharactersEquiv {D M : Type*} [Group D] [CommGroup M]
    [IsCyclic D] [IsCyclic M] (hcard : Nat.card D = Nat.card M) :
    Nonempty ((D →* M) ≃* M) := by
  obtain ⟨d, hd⟩ := IsCyclic.exists_generator (α := D)
  let e : D ≃* M := mulEquivOfCyclicCardEq hcard
  let eval : (D →* M) →* M :=
    { toFun := fun f => f d
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨MulEquiv.ofBijective eval ⟨?_, ?_⟩⟩
  · intro f g h
    ext x
    obtain ⟨i, rfl⟩ := hd x
    change f d = g d at h
    rw [map_zpow, map_zpow, h]
  · intro x
    obtain ⟨i, hi⟩ := hd (e.symm x)
    change d ^ i = e.symm x at hi
    refine ⟨(zpowGroupHom i).comp e.toMonoidHom, ?_⟩
    change e d ^ i = x
    rw [← map_zpow, hi, e.apply_symm_apply]

private theorem finiteFieldKummerConditions (F : Type u) [Field F] [Finite F]
    {m : ℕ} (hdvd : m ∣ Nat.card F - 1) :
    IsUnit (m : RatFunc F) ∧ ∃ ζ : RatFunc F, IsPrimitiveRoot ζ m := by
  let := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hdvd
  have hq : (((Fintype.card F - 1 : ℕ) : F)) = -1 := by
    rw [Nat.cast_sub Fintype.card_pos, FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub]
  have hmF : (m : F) ≠ 0 := by
    intro h
    obtain ⟨b, hb⟩ := hdvd
    rw [hb, Nat.cast_mul, h, zero_mul] at hq
    exact neg_ne_zero.mpr one_ne_zero hq.symm
  have hu : IsUnit (m : RatFunc F) := by
    simpa only [map_natCast] using hmF.isUnit.map (algebraMap F (RatFunc F))
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgcard : orderOf g = Fintype.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card]
  let z := g ^ (orderOf g / m)
  have hz : orderOf z = m := orderOf_pow_orderOf_div
    (orderOf_pos g).ne' (hgcard ▸ hdvd)
  have hζ : IsPrimitiveRoot (z : F) m :=
    (IsPrimitiveRoot.iff_orderOf).mpr (orderOf_units.trans hz)
  exact ⟨hu, algebraMap F (RatFunc F) z,
    hζ.map_of_injective (algebraMap F (RatFunc F)).injective⟩

theorem parameterRadicalExtension : ParameterRadicalExtension.{u,v} := by
  intro F _ _ S _ _ _ m hm hdvd
  let k := RatFunc F
  let t := parameterUnit F
  let c := powerClass k m t
  let D := Subgroup.zpowers c
  have hm' : 1 ≤ m := hm.le
  obtain ⟨hu, hζ⟩ := finiteFieldKummerConditions F hdvd
  have hμ : rootsInBase k S m :=
    KummerCoefficients.rootsInBase_of_primitiveRoot k S hm' hζ
  have hp := KummerCoefficients.powerMap_surjective k S hm' hu
    (Units.map (algebraMap k S) t)
  refine ⟨hp, ?_⟩
  intro α hα
  have hcard : Nat.card D = m := (Nat.card_zpowers c).trans (parameterOrder F m)
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.ne_of_gt hm')
  obtain ⟨corr, hcorr, _⟩ :=
    FiniteKummerDuality.finiteKummerCorrespondence (k := k) (S := S) hm' hu hμ
  let L := (corr ⟨D, inferInstance⟩).val
  have hL : L.toIntermediateField = KummerRadicals.radicalField D := hcorr ⟨D, inferInstance⟩
  have hadjoin := KummerRadicals.radicalFieldOfGenerators (k := k) (S := S)
    hm' hu hμ D (fun _ : Unit => t) (fun _ => α) (by
      rw [Set.range_const]
      exact (Subgroup.zpowers_eq_closure c).symm) (fun _ => hα)
  obtain ⟨eG, _, _⟩ :=
    FiniteKummerDuality.perfectRadicalPairing (k := k) (S := S) hm' hu hμ D L hL
  let : IsCyclic (Roots S m) := KummerCoefficients.roots_cyclic S m hm'
  have hroots := KummerCoefficients.roots_card k S hm' hu
  obtain ⟨eχ⟩ := cyclicCharactersEquiv (hcard.trans hroots.symm)
  let e := eG.trans eχ
  refine ⟨L, hL.trans (hadjoin.trans ?_), ?_, ?_⟩
  · rw [Set.range_const]
  · exact isCyclic_of_injective e.toMonoidHom e.injective
  · rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr e.toEquiv, hroots]

end GaloisFormalization.GH.RationalKummer
