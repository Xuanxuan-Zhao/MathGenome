import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalTorusTorsionCoordinates
import LinearAlgebraicGroups.RootData.RootGroups
import LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
import Mathlib.RingTheory.RootsOfUnity.Complex
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalTorusTorsionCoordinates

open Specs.ExceptionalTorusTorsionCoordinates
open Specs.AbstractPairing (Datum Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (characterValue)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricRadicals (IsSplitTorus)
open CocharacterDynamics (cocharacterPoint)

open private characterUnit characterUnitOnPoints characterEvaluation characterUnit_cocharacter
  characterValue_eq_unit from LinearAlgebraicGroups.RootData.RootGroups
open private splitPresentation from LinearAlgebraicGroups.RootData.CharacterPairing
open private diagonalPointEquiv splitCharacter splitCharacter_eval standardMultiplicativePoints
  from LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private unitEquiv from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

noncomputable section

local notation "R" => CommAlgCat.of ℂ ℂ

variable {G : AffineAlgebraicGroup ℂ} {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]

private theorem splitTorus_points_ext {k : Type*} [Field k] {S : GroupScheme k}
    (hS : IsSplitTorus S) (A : TestAlgebra k) (s t : GroupPoints S A)
    (h : ∀ χ : Character S, characterUnit χ A s = characterUnit χ A t) : s = t := by
  obtain ⟨n, ⟨b⟩⟩ := splitPresentation hS
  have hdiagonal : s ≫ b.inv.hom.hom = t ≫ b.inv.hom.hom := by
    apply (diagonalPointEquiv _ A).injective
    apply MonoidHom.ext
    intro m
    let χ := splitCharacter b m
    have he : s ≫ χ.hom.hom = t ≫ χ.hom.hom := (unitEquiv A).injective (h χ)
    rw [← splitCharacter_eval b m A s, ← splitCharacter_eval b m A t]
    exact congrArg ((standardMultiplicativePoints k).hom.app A) he
  let e := (Grp.forget (SchemeOver k)).mapIso b
  exact (cancel_mono e.inv).mp hdiagonal

private theorem exists_linearMap_zpow {X : Type*} [AddCommGroup X] [Module.Free ℤ X]
    (f : X →ₗ[ℤ] Additive ℂˣ) {d : ℕ} [NeZero d] {ζ : ℂˣ}
    (hζ : IsPrimitiveRoot ζ d) (hf : ∀ x, (f x).toMul ^ d = 1) :
    ∃ g : X →ₗ[ℤ] ℤ, ∀ x, ζ ^ g x = (f x).toMul := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hex (i : Module.Free.ChooseBasisIndex ℤ X) : ∃ n : ℤ, ζ ^ n = (f (b i)).toMul := by
    obtain ⟨n, _, hn⟩ := hζ.eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity d (f (b i)).toMul).mpr (hf (b i)))
    exact ⟨n, by simpa only [zpow_natCast] using hn⟩
  choose n hn using hex
  let g := b.constr ℤ n
  let e := ((zpowersHom ℂˣ ζ).toAdditiveRight).toIntLinearMap
  have heg : e.comp g = f := by
    refine b.ext fun i => ?_
    rw [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact hn i
  exact ⟨g, fun x => LinearMap.congr_fun heg x⟩

private theorem pairing_dvd_iff {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] (B : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) [B.IsPerfPair] (d : ℤ) (v : Y) :
    (∀ x, d ∣ B x v) ↔ ∃ a : Y, v = d • a := by
  classical
  constructor
  · intro h
    let b := Module.Free.chooseBasis ℤ X
    choose n hn using fun i : Module.Free.ChooseBasisIndex ℤ X => h (b i)
    let f := b.constr ℤ n
    let a := B.flip.toPerfPair.symm f
    refine ⟨a, B.flip.toPerfPair.injective ?_⟩
    refine b.ext fun i => ?_
    change B (b i) v = B (b i) (d • a)
    rw [map_smul, LinearMap.apply_toPerfPair_flip, Module.Basis.constr_basis, smul_eq_mul]
    exact hn i
  · rintro ⟨a, rfl⟩ x
    exact ⟨B x a, by rw [map_smul, smul_eq_mul]⟩

private theorem characterUnit_at_coordinate (D : Datum T)
    (y : Additive (Cocharacter T.group)) (ζ : ℂˣ) (χ : Character T.group) :
    characterUnit χ R (cocharacterPoint y.toMul R ζ) =
      ζ ^ D.rootDatum.toLinearMap (Additive.ofMul χ) y := by
  rw [characterUnit_cocharacter, ← D.pairing_eq χ y.toMul]
  rfl

theorem evaluateCharacter : CharacterEvaluation := by
  intro G T _ D y ζ χ
  rw [characterValue_eq_unit, characterUnit_at_coordinate D]

private theorem cocharacterPoint_conjugation (D : Datum T) (I : Identification D)
    (w : D.rootDatum.weylGroup) (y : Additive (Cocharacter T.group)) (ζ : ℂˣ) :
    cocharacterPoint y.toMul R ζ ≫ (I.image.conjugation (I.labelEquiv w)).hom.hom.hom =
      cocharacterPoint (w.val.coweightEquiv.symm y).toMul R ζ := by
  rw [show w.val.coweightEquiv.symm y =
    Additive.ofMul (y.toMul ≫ (I.image.conjugation (I.labelEquiv w)).hom) from
    I.cocharacterAction w y.toMul]
  exact Category.assoc _ _ _

private theorem point_eq_iff (D : Datum T) (hT : IsSplitTorus T.group)
    {d : ℕ} {ζ : ℂˣ} (hζ : IsPrimitiveRoot ζ d) (u v : Additive (Cocharacter T.group)) :
    cocharacterPoint u.toMul R ζ = cocharacterPoint v.toMul R ζ ↔
      ∃ a : Additive (Cocharacter T.group), u - v = (d : ℤ) • a := by
  let _ := D.freeCharacters
  rw [← pairing_dvd_iff D.rootDatum.toLinearMap (d : ℤ) (u - v)]
  constructor
  · intro h x
    have he := congrArg (characterUnit x.toMul R) h
    rw [characterUnit_at_coordinate D, characterUnit_at_coordinate D] at he
    change ζ ^ D.rootDatum.toLinearMap x u = ζ ^ D.rootDatum.toLinearMap x v at he
    rw [map_sub, ← hζ.zpow_eq_one_iff_dvd, zpow_sub, he, mul_inv_cancel]
  · intro h
    apply splitTorus_points_ext hT
    intro χ
    rw [characterUnit_at_coordinate D, characterUnit_at_coordinate D]
    have hd := (hζ.zpow_eq_one_iff_dvd _).mpr (h (Additive.ofMul χ))
    rw [map_sub, zpow_sub, mul_inv_eq_iff_eq_mul, one_mul] at hd
    exact hd

theorem primitiveCoordinateCongruences : PrimitiveCoordinateCongruences := by
  intro G T _ D I hT t d ζ y _ hζ ht
  subst t
  constructor
  · intro w
    rw [cocharacterPoint_conjugation D I]
    exact point_eq_iff D hT hζ _ _
  · intro α
    rw [evaluateCharacter D y ζ α.val, D.root_eq α, ← hζ.zpow_eq_one_iff_dvd]
    exact ⟨fun h => Units.ext h, fun h => congrArg (Units.val : ℂˣ → ℂ) h⟩

private theorem exists_coordinate (D : Datum T) (hT : IsSplitTorus T.group)
    (t : GroupPoints T.group R) {d : ℕ} [NeZero d] (ht : t ^ d = 1) {ζ : ℂˣ}
    (hζ : IsPrimitiveRoot ζ d) : ∃ y : Additive (Cocharacter T.group),
      t = cocharacterPoint y.toMul R ζ := by
  let _ := D.freeCharacters
  let e := (characterEvaluation R t).toAdditive.toIntLinearMap
  have he (x : Additive (Character T.group)) : (e x).toMul ^ d = 1 := by
    let f := characterUnitOnPoints x.toMul R
    change f t ^ d = 1
    rw [← map_pow, ht, map_one]
  obtain ⟨g, hg⟩ := exists_linearMap_zpow e hζ he
  let y := D.rootDatum.toLinearMap.flip.toPerfPair.symm g
  refine ⟨y, splitTorus_points_ext hT R _ _ fun χ => ?_⟩
  rw [characterUnit_at_coordinate D, LinearMap.apply_toPerfPair_flip]
  exact (hg (Additive.ofMul χ)).symm

theorem torsionCoordinates : TorsionCoordinates := by
  intro G T _ D I hT t ht
  obtain ⟨d, hd, htd⟩ := isOfFinOrder_iff_pow_eq_one.mp ht
  let _ : NeZero d := ⟨hd.ne'⟩
  let ζ := ((Complex.isPrimitiveRoot_exp d hd.ne').isUnit hd.ne').unit
  have hζ : IsPrimitiveRoot ζ d := (Complex.isPrimitiveRoot_exp d hd.ne').isUnit_unit hd.ne'
  obtain ⟨y, hy⟩ := exists_coordinate D hT t htd hζ
  refine ⟨d, ζ, y, hd, htd, hζ, hy, ?_, primitiveCoordinateCongruences D I hT t d ζ y hd hζ hy⟩
  intro χ
  rw [hy]
  exact evaluateCharacter D y ζ χ

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalTorusTorsionCoordinates
