import Specs.LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
import LinearAlgebraicGroups.Albert.SpinFunctor
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.Flat.Equalizer
import Batteries.Tactic.OpenPrivate

/-! Base change of the represented Clifford spin group and hyperbolic cocharacter. -/

namespace LinearAlgebraicGroups.Arithmetic.SpinScalarExtension

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct
open CliffordAlgebra
open LinearAlgebraicGroups.Albert
open SpinSpecification (ScalarClifford vectors reversion spinUnits coefficientMap
  IsSpinPointRepresentation conjugate)
open CliffordSpecification (coefficientForm)
open CliffordModel (coefficientForm_tmul baseChangeEquiv baseChangeEquiv_ι)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.Arithmetic.SpinScalarExtension
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Module

open private polar_baseChange_tmul from LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_evenOdd baseChangeEquiv_reverse from
  LinearAlgebraicGroups.Albert.CliffordModel
open private gm_baseChange unitEquiv unitEquiv_unitPoint from
  LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

universe u v w

noncomputable section

local notation "𝔾ₘ(" k ")" => specGroup (groupAlgebra k IntegerCharacters)

set_option backward.isDefEq.respectTransparency false

section QuadraticForm

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {I : Type w} [LinearOrder I]

private theorem polarRadical_eq [Module.Finite K V] (q : QuadraticForm K V) (b : Basis I K V) :
    LinearMap.ker (coefficientForm F q b).polarBilin =
      (LinearMap.ker q.polarBilin).baseChange F := by
  let h := TensorProduct.isBaseChange K V F
  let E := h.toDualBaseChange
  have hp : (coefficientForm F q b).polarBilin =
      E.toLinearMap.comp (LinearMap.baseChange F (q.polarBilin : V →ₗ[K] Dual K V)) := by
    apply h.algHom_ext
    intro x
    apply h.algHom_ext
    intro y
    change (coefficientForm F q b).polarBilin (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) =
      E (LinearMap.baseChange F (q.polarBilin : V →ₗ[K] Dual K V) (1 ⊗ₜ[K] x)) (1 ⊗ₜ[K] y)
    rw [LinearMap.baseChange_tmul]
    have he := h.toDualBaseChange_tmul 1 (q.polarBilin x) y
    rw [one_mul] at he
    exact (polar_baseChange_tmul q F b x y).trans he.symm
  rw [hp, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr E.injective)]
  exact Module.Flat.ker_lTensor_eq F F q.polarBilin

theorem polarRadicalExtension : PolarRadicalExtension.{u,v,w} := by
  intro K F _ _ _ V _ _ _ I _ q b
  have h := polarRadical_eq (F := F) q b
  refine ⟨h, fun h₀ => by simp [h, h₀], ?_⟩
  intro r hr hline
  refine ⟨?_, ?_⟩
  · simpa [coefficientForm_tmul] using
      ((map_ne_zero (algebraMap K F)).2 hr : algebraMap K F (q r) ≠ 0)
  · rw [h, hline, Submodule.baseChange_span, Set.image_singleton]
    rfl

theorem hyperbolicPairExtension : HyperbolicPairExtension.{u,v,w} := by
  intro K F _ _ _ V _ _ I _ q b e f he hf hef
  refine ⟨by simp [coefficientForm_tmul, he], by simp [coefficientForm_tmul, hf], ?_⟩
  rw [polar_baseChange_tmul q F b e f, hef, map_one]

end QuadraticForm

theorem testQuadraticFormComparison : TestQuadraticFormComparison.{u,v,w} := by
  intro K F _ _ _ V _ _ I _ q b R
  let U := vectorComparison (K := K) (V := V) R
  let Q := coefficientForm R (coefficientForm F q b) (b.baseChange F)
  let P := coefficientForm (restricted K R) q b
  have hQ : Q.comp U.symm.toLinearMap = P := by
    apply (CliffordModel.coefficient_form_unique (restricted K R) q b _).2
    intro x
    change Q (1 ⊗ₜ[F] (1 ⊗ₜ[K] x)) = algebraMap K (restricted K R) (q x)
    simp only [Q, coefficientForm_tmul, one_mul]
    rfl
  have h (x : R ⊗[F] (F ⊗[K] V)) : Q x = P (U x) := by
    have he := congrArg (fun a : QuadraticForm R ((restricted K R) ⊗[K] V) => a (U x)) hQ
    change Q (U.symm (U x)) = P (U x) at he
    rwa [LinearEquiv.symm_apply_apply] at he
  refine ⟨h, fun x y => ?_⟩
  change Q.polarBilin x y = P.polarBilin (U x) (U y)
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h, map_add]

theorem multiplicativeComparison : MultiplicativeComparison.{u} := by
  intro K F _ _ _
  exact gm_baseChange K F

section Clifford

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable {V : Type u} [AddCommGroup V] [Module K V]
variable {I : Type w} [LinearOrder I]
variable (q : QuadraticForm K V) (b : Basis I K V)

local notation "Q" => coefficientForm F q b

private def cliffordComparison (R : TestAlgebra F) :
    ScalarClifford q (restricted K R) ≃ₐ[R] ScalarClifford Q R := by
  letI : Algebra K R := ((algebraMap F R).comp (algebraMap K F)).toAlgebra
  letI : IsScalarTower K F R := IsScalarTower.of_algebraMap_eq' rfl
  let L := (TensorProduct.AlgebraTensorModule.cancelBaseChange K F R R (CliffordAlgebra q)).symm
  let C := AlgEquiv.ofLinearEquiv L
    (by simp [L, Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ => by simp [L]))
  exact C.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (baseChangeEquiv F q b))

private theorem cliffordComparison_tmul (R : TestAlgebra F) (s : R) (a : CliffordAlgebra q) :
    cliffordComparison q b R (s ⊗ₜ[K] a) = s ⊗ₜ[F] baseChangeEquiv F q b (1 ⊗ₜ[K] a) :=
  rfl

private theorem cliffordComparison_vector (R : TestAlgebra F) (x : R ⊗[F] (F ⊗[K] V)) :
    cliffordComparison q b R (vectors q (restricted K R) (vectorComparison R x)) =
      vectors Q R x := by
  let U := vectorComparison (K := K) (V := V) R
  have h (y : (restricted K R) ⊗[K] V) :
      cliffordComparison q b R (vectors q (restricted K R) y) = vectors Q R (U.symm y) := by
    induction y using TensorProduct.inductionOn with
    | tmul s v =>
      change cliffordComparison q b R (s ⊗ₜ[K] CliffordAlgebra.ι q v) =
        vectors Q R (s ⊗ₜ[F] (1 ⊗ₜ[K] v))
      rw [cliffordComparison_tmul, baseChangeEquiv_ι, LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  simpa only [LinearEquiv.symm_apply_apply] using h (U x)

private theorem cliffordComparison_reversion (R : TestAlgebra F)
    (x : ScalarClifford q (restricted K R)) :
    cliffordComparison q b R (reversion q (restricted K R) x) =
      reversion Q R (cliffordComparison q b R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    have h := baseChangeEquiv_reverse F q b (1 ⊗ₜ[K] a)
    rw [LinearMap.baseChange_tmul] at h
    rw [LinearMap.baseChange_tmul, cliffordComparison_tmul q b R s (reverse a),
      cliffordComparison_tmul q b R s a, LinearMap.baseChange_tmul, h]
  | add a c ha hc => simp only [map_add, ha, hc]

private theorem cliffordComparison_natural {R S : TestAlgebra F} (f : R ⟶ S)
    (x : ScalarClifford q (restricted K R)) :
    cliffordComparison q b S
        (coefficientMap q (restricted K R) ((restrictTestAlgebra K F).map f).hom x) =
      coefficientMap Q R f.hom (cliffordComparison q b R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    simp only [coefficientMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [cliffordComparison_tmul q b R s a, Algebra.TensorProduct.map_tmul]
    rfl
  | add a c ha hc => simp only [map_add, ha, hc]

private theorem cliffordComparison_grade (R : TestAlgebra F) (j : ZMod 2)
    (x : ScalarClifford q (restricted K R)) :
    cliffordComparison q b R x ∈ (evenOdd Q j).baseChange R ↔
      x ∈ (evenOdd q j).baseChange (restricted K R) := by
  let E := baseChangeEquiv F q b
  have hF : evenOdd Q j =
      Submodule.span F ((fun a : CliffordAlgebra q => E (1 ⊗ₜ[K] a)) '' (evenOdd q j : Set _)) := by
    rw [← baseChangeEquiv_evenOdd F q b j, Submodule.baseChange_eq_span, Submodule.map_span]
    rw [Submodule.map_coe, Set.image_image]
    rfl
  have hR : ((evenOdd q j).baseChange (restricted K R)).map
      (cliffordComparison q b R).toLinearEquiv.toLinearMap = (evenOdd Q j).baseChange R := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, hF, Submodule.baseChange_span,
      Submodule.map_coe, Set.image_image, Set.image_image]
    congr 1
  rw [← hR, Submodule.mem_map_equiv]
  exact Iff.of_eq (congrArg (fun y => y ∈ (evenOdd q j).baseChange (restricted K R))
    ((cliffordComparison q b R).symm_apply_apply x))

private theorem cliffordComparison_spin (R : TestAlgebra F)
    (a : (ScalarClifford q (restricted K R))ˣ) :
    Units.map (cliffordComparison q b R).toMonoidHom a ∈ spinUnits Q R ↔
      a ∈ spinUnits q (restricted K R) := by
  let A := cliffordComparison q b R
  let U := vectorComparison (K := K) (V := V) R
  let φ := Units.map A.toMonoidHom
  have hvec (x : R ⊗[F] (F ⊗[K] V)) : A (vectors q (restricted K R) (U x)) = vectors Q R x :=
    cliffordComparison_vector q b R x
  have hrange (x : ScalarClifford q (restricted K R)) :
      A x ∈ LinearMap.range (vectors Q R) ↔ x ∈ LinearMap.range (vectors q (restricted K R)) := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨U y, A.injective ((hvec y).trans hy)⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨y, rfl⟩ := U.surjective z
      exact ⟨y, (hvec y).symm⟩
  have hconj (g : (ScalarClifford q (restricted K R))ˣ) (x : ScalarClifford q (restricted K R)) :
      A (conjugate q (restricted K R) g x) = conjugate Q R (φ g) (A x) := by
    simp only [conjugate, map_mul, φ, Units.coe_map, Units.coe_map_inv]
    rfl
  have hnormal (g : (ScalarClifford q (restricted K R))ˣ) :
      Set.MapsTo (conjugate Q R (φ g)) (LinearMap.range (vectors Q R)) (LinearMap.range (vectors Q R)) ↔
      Set.MapsTo (conjugate q (restricted K R) g) (LinearMap.range (vectors q (restricted K R)))
        (LinearMap.range (vectors q (restricted K R))) := by
    constructor
    · intro h x hx
      exact (hrange _).mp (hconj g x ▸ h ((hrange x).mpr hx))
    · intro h y hy
      obtain ⟨x, rfl⟩ := A.surjective y
      rw [← hconj]
      exact (hrange _).mpr (h ((hrange x).mp hy))
  have hnorm :
      reversion Q R (φ a).val * (φ a).val = 1 ↔
        reversion q (restricted K R) a.val * a.val = 1 := by
    change reversion Q R (A a.val) * A a.val = 1 ↔ _
    rw [← show A (reversion q (restricted K R) a.val) = _ from
      cliffordComparison_reversion q b R a.val, ← map_mul, ← A.map_one]
    exact A.injective.eq_iff
  change (A a.val ∈ (evenOdd Q 0).baseChange R ∧
      reversion Q R (φ a).val * (φ a).val = 1 ∧ _ ∧
      Set.MapsTo (conjugate Q R (φ a)⁻¹) _ _) ↔ _
  rw [cliffordComparison_grade, hnorm, hnormal, ← φ.map_inv, hnormal]
  rfl

end Clifford

section Scheme

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

private theorem cocharacterPoint_baseChange {G : GroupScheme K} (c : Cocharacter G)
    (m : 𝔾ₘ(F) ≅ (groupBaseChange K F).obj (𝔾ₘ(K)))
    (hm : IsMultiplicativeComparison m) (R : TestAlgebra F) (s : Rˣ) :
    baseChangePoint K F G.X R
        (cocharacterPoint (m.hom ≫ (groupBaseChange K F).map c) R s) =
      cocharacterPoint c (restricted K R) s := by
  change baseChangePoint K F G.X R
      (unitPoint R s ≫ m.hom.hom.hom ≫ ((groupBaseChange K F).map c).hom.hom) =
    unitPoint (restricted K R) s ≫ c.hom.hom
  rw [← Category.assoc]
  let p : Points ((baseChange K F).obj (𝔾ₘ(K)).X) R :=
    unitPoint R s ≫ m.hom.hom.hom
  exact (baseChangePointsSchemeNaturality K F c.hom.hom R p).trans
    (congrArg (fun x : Points (𝔾ₘ(K)).X (restricted K R) => x ≫ c.hom.hom)
      (hm R s))

private theorem cocharacter_ext {H : GroupScheme F} {c d : Cocharacter H}
    (h : ∀ (R : TestAlgebra F) (s : Rˣ), cocharacterPoint c R s = cocharacterPoint d R s) :
    c = d := by
  apply (groupHomComparison F _ _ (by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)))
    infer_instance)).1
  ext R p
  let s := unitEquiv R p
  have hp : unitPoint R s = p := (unitEquiv R).injective (unitEquiv_unitPoint R s)
  change (p ≫ c.hom.hom) = p ≫ d.hom.hom
  rw [← hp]
  exact h R s

theorem spinRepresentationExtension : SpinRepresentationExtension.{u,w} := by
  intro K F _ _ _ V _ _ I _ q b G ρ hρ
  let Q := coefficientForm F q b
  let H := baseChangedAlgebraicGroup F G
  let A := cliffordComparison (F := F) q b
  let E (R : TestAlgebra F) := baseChangePointGroupEquiv F G.val R
  let ρF (R : TestAlgebra F) : GroupPoints H.val R →* (ScalarClifford Q R)ˣ :=
    (Units.map (A R).toMonoidHom).comp ((ρ (restricted K R)).comp (E R).toMonoidHom)
  have hpoint (R : TestAlgebra F) (p : GroupPoints H.val R) :
      ρF R p = Units.map (A R).toMonoidHom
        (ρ (restricted K R) (baseChangePoint K F G.val.X R p)) := rfl
  have hrange (R : TestAlgebra K) :
      Set.range (ρ R : GroupPoints G.val R → (ScalarClifford q R)ˣ) = spinUnits q R := (hρ.1 R).2
  have hrep : IsSpinPointRepresentation Q H.val ρF := by
    constructor
    · intro R
      have hmap (a : (ScalarClifford q (restricted K R))ˣ) :
          Units.mapEquiv (A R).toMulEquiv a = Units.map (A R).toMonoidHom a := rfl
      refine ⟨(Units.mapEquiv (A R).toMulEquiv).injective.comp
        ((hρ.1 (restricted K R)).1.comp (E R).injective), Set.ext ?_⟩
      intro a
      change a ∈ Set.range (ρF R : GroupPoints H.val R → (ScalarClifford Q R)ˣ) ↔
        a ∈ spinUnits Q R
      constructor
      · rintro ⟨p, rfl⟩
        rw [hpoint, cliffordComparison_spin, ← hrange (restricted K R)]
        exact ⟨_, rfl⟩
      · intro ha
        obtain ⟨a₀, rfl⟩ := (Units.mapEquiv (A R).toMulEquiv).surjective a
        rw [hmap, cliffordComparison_spin, ← hrange (restricted K R)] at ha
        obtain ⟨p, hp⟩ := ha
        refine ⟨(E R).symm p, ?_⟩
        change Units.map (A R).toMonoidHom (ρ (restricted K R) (E R ((E R).symm p))) = _
        rw [MulEquiv.apply_symm_apply, hp, hmap]
    · intro R S f p
      change ρF S (mapPoints f p) = Units.map (coefficientMap Q R f.hom).toMonoidHom (ρF R p)
      have hn := hρ.2 ((restrictTestAlgebra K F).map f) (E R p)
      change ρ (restricted K S) (mapPoints ((restrictTestAlgebra K F).map f) (E R p)) = _ at hn
      rw [hpoint S, hpoint R, baseChangePointsNaturality K F G.val.X f p]
      change Units.map (A S).toMonoidHom
        (ρ (restricted K S) (mapPoints ((restrictTestAlgebra K F).map f) (E R p))) = _
      rw [hn]
      apply Units.ext
      exact cliffordComparison_natural q b f ((ρ (restricted K R) (E R p)).val)
  refine ⟨A, ρF, cliffordComparison_vector q b, cliffordComparison_reversion q b,
    cliffordComparison_grade q b, cliffordComparison_natural q b,
    cliffordComparison_spin q b, hpoint, hrep, ?_⟩
  intro e f _ _ _ c hc m hm
  let cF : Cocharacter H.val := m.hom ≫ (groupBaseChange K F).map c
  have hbc (R : TestAlgebra F) (s : Rˣ) :
      baseChangePoint K F G.val.X R (cocharacterPoint cF R s) =
        cocharacterPoint c (restricted K R) s := cocharacterPoint_baseChange c m hm R s
  have hformula : HasSpinCocharacterFormula Q ρF (1 ⊗ₜ[K] e) (1 ⊗ₜ[K] f) cF := by
    intro R s
    dsimp only
    rw [hpoint, hbc R s, Units.coe_map]
    change A R ((ρ (restricted K R) (cocharacterPoint c (restricted K R) s)).val) = _
    rw [hc, map_add, map_smul, map_smul, map_mul, map_mul]
    have hv (x : V) :
        A R (vectors q (restricted K R) (1 ⊗ₜ[K] x)) = vectors Q R (1 ⊗ₜ[F] (1 ⊗ₜ[K] x)) :=
      by simpa [vectorComparison] using
        cliffordComparison_vector q b R (1 ⊗ₜ[F] (1 ⊗ₜ[K] x))
    rw [hv, hv]
  refine ⟨hbc, hformula, ?_⟩
  intro d hd
  apply cocharacter_ext
  intro R s
  apply (hrep.1 R).1
  apply Units.ext
  exact (hd R s).trans (hformula R s).symm

end Scheme

end
end LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
