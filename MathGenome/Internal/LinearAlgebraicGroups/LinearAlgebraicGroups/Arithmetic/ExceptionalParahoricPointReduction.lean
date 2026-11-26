import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricPointReduction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricRationalBruhat
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricResidueWeyl
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.NormalizerComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.TorsorObstruction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Lang
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricPointReduction

noncomputable section

section ScalingField

universe u

open ValuativeRel WithZero Polynomial
open Specs.ExceptionalLocalRootCoordinates
  (canonicalExtension normalizedValuation normalizedValueGroupMap residueMap)
open scoped WithZero

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

set_option quotPrecheck false in
local notation "O(" K ")" => (valuation K).valuationSubring

private theorem normalized_le (x y : K) :
    normalizedValuation K x ≤ normalizedValuation K y ↔ valuation K x ≤ valuation K y :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.le_iff_le

private theorem normalized_lt (x y : K) :
    normalizedValuation K x < normalizedValuation K y ↔ valuation K x < valuation K y :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.lt_iff_lt

private theorem normalized_le_one (x : K) :
    normalizedValuation K x ≤ 1 ↔ valuation K x ≤ 1 := by
  simpa only [map_one] using normalized_le x 1

private theorem normalized_lt_one (x : K) :
    normalizedValuation K x < 1 ↔ valuation K x < 1 := by
  simpa only [map_one] using normalized_lt x 1

variable {L : Type u} [Field L] [Algebra K L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

private theorem normalized_value_map (x : K) :
    normalizedValueGroupMap K L (normalizedValuation K x) =
      normalizedValuation L (algebraMap K L x) := by
  let eK := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let eL := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  change eL (ValuativeExtension.mapValueGroupWithZero K L (eK.symm (eK (valuation K x)))) =
    eL (valuation L (algebraMap K L x))
  rw [eK.symm_apply_apply, ValuativeExtension.mapValueGroupWithZero_valuation]

private theorem scaled_uniformizer_values {d : ℕ} (hd : 0 < d) {π : K} {ξ : L}
    (hπ : normalizedValuation K π = exp (-1 : ℤ)) (hξ : ξ ^ d = algebraMap K L π) :
    ∃ c : ℤ, 0 < c ∧ normalizedValuation L ξ = exp (-c) ∧
      ∀ x : K, x ≠ 0 → normalizedValuation L (algebraMap K L x) =
        exp ((d : ℤ) * c * log (normalizedValuation K x)) := by
  have hπ₀ : π ≠ 0 := fun hz => exp_ne_zero (a := (-1 : ℤ)) (hπ.symm.trans (by simp [hz]))
  have hξ₀ : ξ ≠ 0 := fun hz => ((_root_.map_ne_zero (algebraMap K L)).mpr hπ₀)
    (by simpa [hz, Nat.ne_of_gt hd] using hξ.symm)
  let c := -(log (normalizedValuation L ξ))
  have hξv : normalizedValuation L ξ = exp (-c) := by
    simpa only [c, neg_neg] using (exp_log ((_root_.map_ne_zero (normalizedValuation L)).mpr hξ₀)).symm
  have hall : normalizedValuation L (algebraMap K L π) = exp (-c) ^ d := by rw [← hξ, map_pow, hξv]
  have hπlt : normalizedValuation L (algebraMap K L π) < 1 := by
    let := canonicalExtension K L
    refine (normalized_lt_one _).mpr
      ((Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) π).mpr ?_)
    apply (normalized_lt_one π).mp
    rw [hπ, ← exp_zero]
    exact exp_lt_exp.mpr (by decide)
  have hc : 0 < c := by
    have hp : exp (-c) ^ d < 1 := hall ▸ hπlt
    have hv : exp (-c) < 1 := by
      by_contra! h
      exact (not_le_of_gt hp) (one_le_pow₀ h)
    have : -c < 0 := exp_lt_exp.mp (by simpa only [exp_zero] using hv)
    omega
  refine ⟨c, hc, hξv, ?_⟩
  intro x hx
  let n := log (normalizedValuation K x)
  let f := normalizedValueGroupMap K L
  have hexp (z : ℤ) (e : ℤ) : (exp z : ℤᵐ⁰) ^ e = exp (e * z) := by
    change (((↑(Multiplicative.ofAdd z)) : ℤᵐ⁰) ^ e) =
      ↑(Multiplicative.ofAdd (e * z))
    rw [← WithZero.coe_zpow]
    rfl
  have hπ' : f (exp (-1 : ℤ)) = exp (-((d : ℤ) * c)) := by
    rw [← hπ, normalized_value_map, hall, ← zpow_natCast, hexp]
    congr 1
    simp
  have hz (z : ℤ) : exp z = (exp (-1 : ℤ) : ℤᵐ⁰) ^ (-z) := by rw [hexp]; simp
  calc
    normalizedValuation L (algebraMap K L x) = f (exp n) := by
      rw [exp_log ((_root_.map_ne_zero (normalizedValuation K)).mpr hx), normalized_value_map]
    _ = exp ((d : ℤ) * c * n) := by
      rw [hz n, map_zpow₀, hπ', hexp]
      congr 1
      simp [mul_comm]

end ScalingField

section ComparisonLemmas

universe u

open ValuativeRel WithZero
open scoped WithZero TensorProduct CategoryTheory.MonObj
open CategoryTheory
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel)
open Specs.ExceptionalAffineBuilding (Weights SplitBuildingLevel cotype parahoric)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.IntegralSemisimpleModel (Model)
open Specs.Pinning (BasedRootDatum)

/-- The valuation of the scalar-extended root coordinate after conjugation. -/
theorem scaled_root_parameter_value
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    {d : ℕ} (hd : 0 < d) {π : K} {ξ : L}
    (hπ : normalizedValuation K π = exp (-1 : ℤ)) (hξ : ξ ^ d = algebraMap K L π) :
    ∃ c : ℤ, 0 < c ∧ ∀ (a : K) (_ha : a ≠ 0) (m : ℤ),
      normalizedValuation L (ξ ^ m * algebraMap K L a) =
        exp (c * ((d : ℤ) * log (normalizedValuation K a) - m)) := by
  obtain ⟨c, hc, hξv, hv⟩ := scaled_uniformizer_values hd hπ hξ
  refine ⟨c, hc, ?_⟩
  intro a ha m
  rw [map_mul, map_zpow₀, hξv, hv a ha]
  have hm : (exp (-c) : ℤᵐ⁰) ^ m = exp (m * -c) := by
    change ((↑(Multiplicative.ofAdd (-c)) : ℤᵐ⁰) ^ m) = _
    rw [← WithZero.coe_zpow]
    rfl
  rw [hm, ← exp_add, exp_inj]
  ring

/-- A root evaluates on the integral multiple of a rational point by the
same integer pairing used in the marked torus conjugation formula. -/
theorem root_at_scaled_point {E : BasedRootDatum.{u}}
    (a : E.I) (x : ℚ ⊗[ℤ] E.Y) (d : ℕ) (y : E.Y)
    (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y) :
    (d : ℚ) * (ApartmentRoots.split E.datum ℚ).root a x =
      (E.datum.toLinearMap (E.datum.root a) y : ℚ) := by
  let f := (ApartmentRoots.split E.datum ℚ).root a
  calc
    (d : ℚ) * f x = f ((d : ℚ) • x) := by rw [map_smul, smul_eq_mul]
    _ = f ((1 : ℚ) ⊗ₜ[ℤ] y) := congrArg f hy
    _ = _ := RootData.extendFunctional_one_tmul ℚ (E.datum.root' a) y

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (B : SplitBuildingLevel Y)
  (t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p'))

private theorem threshold_le_iff_positive (a : ℚ) (n : ℤ) :
    Specs.ExceptionalAffineRootSystems.threshold a ≤ n ↔ 0 < a + (n : ℚ) := by
  rw [Specs.ExceptionalAffineRootSystems.threshold, ← Int.lt_iff_add_one_le, Int.floor_lt]
  constructor <;> intro h <;> linarith

private theorem realWallValue_rationalPoint
    (r : Specs.ExceptionalAffineBuilding.RealCoordinates (ℚ ⊗[ℤ] E.Y))
    (a : E.I × ℤ) (x : ℚ ⊗[ℤ] E.Y) :
    Specs.ExceptionalAffineBuilding.realWallValue (ApartmentRoots.split E.datum ℚ) r a
      (Specs.ExceptionalAffineBuilding.rationalPoint r x) =
      ((ApartmentRoots.split E.datum ℚ).wallValue a x : ℝ) := by
  let A := ApartmentRoots.split E.datum ℚ
  change (TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ)
    ((A.root a.1).baseChange ℝ (r.symm (r (1 ⊗ₜ[ℚ] x)))) + (a.2 : ℝ) = _
  rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  change (A.root a.1 x) • (1 : ℝ) + (a.2 : ℝ) = (↑(A.root a.1 x + (a.2 : ℚ)) : ℝ)
  simp [Algebra.smul_def]

/-- The closed-alcove condition in the rational coordinates. -/
theorem closed_alcove_wall_value
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    (a : E.I × ℤ) (ha : (ApartmentRoots.split E.datum ℚ).positive p' a) :
    0 ≤ (ApartmentRoots.split E.datum ℚ).wallValue a x := by
  let A := ApartmentRoots.split E.datum ℚ
  let C := B.ad.realization
  have hmem : Specs.ExceptionalAffineBuilding.simplexPoint C.coordinates C.vertex t ∈
      {z | ∀ a, A.positive p' a →
        0 ≤ Specs.ExceptionalAffineBuilding.realWallValue A C.coordinates a z} :=
    C.closed_alcove ▸ Set.mem_range_self t
  have h := hmem a ha
  rw [← hx, realWallValue_rationalPoint] at h
  exact_mod_cast h

/-- The slots at zero scaled depth are precisely the integral roots with
positive affine wall at the base alcove. -/
theorem face_positive_roots_iff_zero_depth
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t) (a : E.I) :
    let A := ApartmentRoots.split E.datum ℚ
    (∃ j : ℤ, A.root a x = j ∧ A.positive p' (a, -j)) ↔
      A.wallValue (a, Specs.ExceptionalAffineRootSystems.threshold (A.root a p')) x = 0 := by
  let A := ApartmentRoots.split E.datum ℚ
  let n := Specs.ExceptionalAffineRootSystems.threshold (A.root a p')
  change (∃ j : ℤ, A.root a x = j ∧ A.positive p' (a, -j)) ↔ A.root a x + (n : ℚ) = 0
  have hpos : A.positive p' (a, n) := (threshold_le_iff_positive _ _).mp le_rfl
  have hx' : 0 ≤ A.root a x + (n : ℚ) := closed_alcove_wall_value B t x hx (a, n) hpos
  constructor
  · rintro ⟨j, hj, hp⟩
    have hn : n ≤ -j := (threshold_le_iff_positive _ _).mpr hp
    have hq : (n : ℚ) ≤ -(j : ℚ) := by exact_mod_cast hn
    linarith
  · intro h
    refine ⟨-n, ?_, ?_⟩
    · rw [Int.cast_neg]
      linarith
    · simpa only [neg_neg] using hpos

/-- The affine Weyl subgroup of the standard face fixes its marked rational point. -/
theorem face_weyl_fixes_point
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    (w : Specs.ExceptionalAffineBuilding.standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)) :
    w.val.val x = x := by
  let A := ApartmentRoots.split E.datum ℚ
  let v : A.affineWeylGroup := w.val
  change v.val x = x
  have hw : v ∈ Specs.ExceptionalAffineBuilding.standardWallSubgroup
      Y.ad.coxeter.coxeter (cotype t) := w.property
  rw [B.ad.realization.wall_group t] at hw
  refine Subgroup.closure_induction (p := fun v _ => v.val x = x) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨a, ha, rfl⟩
    have hzero : A.wallValue a x = 0 := by
      change Specs.ExceptionalAffineBuilding.realWallValue A B.ad.realization.coordinates a
        (Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
          B.ad.realization.vertex t) = 0 at ha
      rw [← hx, realWallValue_rationalPoint] at ha
      exact_mod_cast ha
    have hval : A.root a.1 x = -(a.2 : ℚ) := by
      change A.root a.1 x + (a.2 : ℚ) = 0 at hzero
      linarith
    change (-a.2) • A.coroot a.1 + Module.reflection (A.diagonal a.1) x = x
    rw [Module.reflection_apply, hval, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_neg]
    abel
  · rfl
  · intro v z _ _ hv hz
    change v.val (z.val x) = x
    rw [hz, hv]
  · intro v _ hv
    change v.val.symm x = x
    exact (congrArg v.val.symm hv).symm.trans (v.val.symm_apply_apply x)

private theorem rational_cocharacter_injective (E : BasedRootDatum.{u}) :
    Function.Injective (fun y : E.Y => (1 : ℚ) ⊗ₜ[ℤ] y) := by
  intro y z h
  apply E.datum.toLinearMap.flip.toPerfPair.injective
  ext χ
  change E.datum.toLinearMap χ y = E.datum.toLinearMap χ z
  exact_mod_cast (show (E.datum.toLinearMap χ y : ℚ) = (E.datum.toLinearMap χ z : ℚ) by
    simpa only [RootData.extendFunctional_one_tmul] using
      congrArg (RootData.extendFunctional ℚ (E.datum.toLinearMap χ)) h)

/-- The affine fixing equation gives the integral cocharacter relation for
the torus component of a marked lift. -/
theorem face_lift_translation_cancel
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    (d : ℕ) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    (w : Specs.ExceptionalAffineBuilding.standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)) :
    let N := Y.ad.localIwahori.normalizer
    let n := Y.ad.lift w.val
    y = (N.label n).val.coweightEquiv.symm y + d • (N.translation (N.torusPart n)).toAdd := by
  let N := Y.ad.localIwahori.normalizer
  let n := Y.ad.lift w.val
  let r := (N.label n).val.coweightEquiv.symm
  let ν := (N.translation (N.torusPart n)).toAdd
  have hfix : Y.ad.affine n x = x :=
    congrArg (fun f : (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y) => f x)
      (Y.ad.lift_label w.val) |>.trans (face_weyl_fixes_point B t x hx w)
  obtain ⟨_, _, _, _, _, _, hAff, _, _⟩ := Y.ad_points
  have hn : r.baseChange ℤ ℚ E.Y E.Y x + (1 : ℚ) ⊗ₜ[ℤ] ν = x :=
    (hAff n x).symm.trans hfix
  have h := congrArg (fun z : ℚ ⊗[ℤ] E.Y => (d : ℚ) • z) hn
  change (d : ℚ) • (r.baseChange ℤ ℚ E.Y E.Y x + (1 : ℚ) ⊗ₜ[ℤ] ν) = (d : ℚ) • x at h
  rw [smul_add, ← map_smul, hy, LinearEquiv.baseChange_tmul] at h
  have hv : (d : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] ν) = (1 : ℚ) ⊗ₜ[ℤ] (d • ν) := by
    have hd' : (d : ℚ) = (d : ℤ) • (1 : ℚ) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul, mul_one, Int.cast_natCast]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hd', TensorProduct.smul_tmul,
      natCast_zsmul]
  rw [hv, ← TensorProduct.tmul_add] at h
  exact (rational_cocharacter_injective E h).symm

/-- A marked affine Weyl label of the face is determined by its finite label. -/
theorem face_lift_finite_label_injective
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t) :
    Function.Injective (fun w : Specs.ExceptionalAffineBuilding.standardWallSubgroup
        Y.ad.coxeter.coxeter (cotype t) => Y.ad.localIwahori.normalizer.label (Y.ad.lift w.val)) := by
  let N := Y.ad.localIwahori.normalizer
  obtain ⟨_, _, _, _, _, _, hAff, _, _⟩ := Y.ad_points
  intro v w hw
  let n := Y.ad.lift v.val
  let m := Y.ad.lift w.val
  change N.label n = N.label m at hw
  have hn : Y.ad.affine n x = x :=
    congrArg (fun f : (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y) => f x)
      (Y.ad.lift_label v.val) |>.trans (face_weyl_fixes_point B t x hx v)
  have hm : Y.ad.affine m x = x :=
    congrArg (fun f : (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y) => f x)
      (Y.ad.lift_label w.val) |>.trans (face_weyl_fixes_point B t x hx w)
  rw [hAff n x, hw] at hn
  rw [hAff m x] at hm
  have ht : ((1 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd) =
      ((1 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart m)).toAdd) :=
    add_left_cancel (hn.trans hm.symm)
  apply Subtype.ext
  apply Subtype.ext
  rw [← Y.ad.lift_label v.val, ← Y.ad.lift_label w.val]
  ext z
  rw [hAff n z, hAff m z, hw, ht]

variable {L : Type u} [Field L] [Algebra K L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

/-- An Iwahori root parameter remains integral after scaling at the closed
face. It has positive depth if its affine wall misses the face. -/
theorem scaled_parameter_integral
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    {d : ℕ} (hd : 0 < d) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : K} {ξ : L} (hπ : normalizedValuation K π = exp (-1 : ℤ))
    (hξ : ξ ^ d = algebraMap K L π) (a : E.I) (n : ℤ)
    (hn : Specs.ExceptionalAffineRootSystems.threshold ((ApartmentRoots.split E.datum ℚ).root a p') ≤ n)
    (z : K) (hz : normalizedValuation K z ≤ exp (-n)) :
    let A := ApartmentRoots.split E.datum ℚ
    let w := ξ ^ E.datum.toLinearMap (E.datum.root a) y * algebraMap K L z
    normalizedValuation L w ≤ 1 ∧
      (0 < A.wallValue (a, n) x → normalizedValuation L w < 1) := by
  let A := ApartmentRoots.split E.datum ℚ
  let m := E.datum.toLinearMap (E.datum.root a) y
  let w := ξ ^ m * algebraMap K L z
  change normalizedValuation L w ≤ 1 ∧
    (0 < A.root a x + (n : ℚ) → normalizedValuation L w < 1)
  have ha : A.positive p' (a, n) := (threshold_le_iff_positive _ _).mp hn
  have hw : 0 ≤ A.root a x + (n : ℚ) := closed_alcove_wall_value B t x hx (a, n) ha
  by_cases h0 : z = 0
  · simp [w, h0]
  have hlog : log (normalizedValuation K z) ≤ -n := by
    apply exp_le_exp.mp
    rw [exp_log ((_root_.map_ne_zero (normalizedValuation K)).mpr h0)]
    exact hz
  obtain ⟨c, hc, hv⟩ := scaled_root_parameter_value hd hπ hξ
  have hm : (d : ℚ) * A.root a x = (m : ℚ) := root_at_scaled_point a x d y hy
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hdz : (0 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd.le
  have hle : (d : ℤ) * (-n) ≤ m := by
    apply_mod_cast (show (d : ℚ) * (-(n : ℚ)) ≤ (m : ℚ) by
      rw [← hm]
      exact mul_le_mul_of_nonneg_left (by linarith) hdq.le)
  have hle' := (mul_le_mul_of_nonneg_left hlog hdz).trans hle
  rw [hv z h0 m, ← exp_zero]
  constructor
  · exact exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr hle'))
  · intro hs
    have hlt : (d : ℤ) * (-n) < m := by
      apply_mod_cast (show (d : ℚ) * (-(n : ℚ)) < (m : ℚ) by
        rw [← hm]
        exact mul_lt_mul_of_pos_left (by linarith) hdq)
    exact exp_lt_exp.mpr (mul_neg_of_pos_of_neg hc
      (sub_neg.mpr ((mul_le_mul_of_nonneg_left hlog hdz).trans_lt hlt)))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] in
/-- The prescribed base-field depth cancels the cocharacter scale on a wall
through the face. -/
theorem scaled_parameter_on_wall
    (x : ℚ ⊗[ℤ] E.Y) {d : ℕ} (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hξ : (ξ : L) ^ d = algebraMap K L (π : K))
    (a : E.I) (n : ℤ) (ha : (ApartmentRoots.split E.datum ℚ).root a x = -(n : ℚ)) (z : K) :
    (ξ : L) ^ E.datum.toLinearMap (E.datum.root a) y *
      algebraMap K L ((π : K) ^ n * z) = algebraMap K L z := by
  have hm := root_at_scaled_point a x d y hy
  rw [ha] at hm
  have hm' : E.datum.toLinearMap (E.datum.root a) y = -((d : ℤ) * n) := by
    exact_mod_cast (hm.symm.trans (mul_neg _ _))
  rw [hm', map_mul, map_zpow₀, ← hξ, ← zpow_natCast, ← zpow_mul, ← mul_assoc,
    ← zpow_add₀ ξ.ne_zero, neg_add_cancel, zpow_zero, one_mul]

/-- The torus component of the scaled face normalizer has unit value
on each character. -/
theorem scaled_face_lift_torus_value
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    {d : ℕ} (hd : 0 < d) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hπ : normalizedValuation K (π : K) = exp (-1 : ℤ))
    (hξ : (ξ : L) ^ d = algebraMap K L (π : K))
    (w : Specs.ExceptionalAffineBuilding.standardWallSubgroup Y.ad.coxeter.coxeter (cotype t))
    (v : Specs.IntegralSemisimpleModel.TorusValues E
      (Specs.ExceptionalIwahoriCongruence.integralRing K))
    (hv : let N := Y.ad.localIwahori.normalizer
      (N.torusPart (Y.ad.lift w.val) : FieldPoints M' K) =
        Specs.IntegralSemisimpleModel.torusPoint E _ v ≫ M'.torus.hom.hom)
    (χ : E.X) :
    let N := Y.ad.localIwahori.normalizer
    let r := (N.label (Y.ad.lift w.val)).val.coweightEquiv.symm
    normalizedValuation L
      ((ξ : L) ^ (E.datum.toLinearMap χ y - E.datum.toLinearMap χ (r y)) *
        algebraMap K L (v (Multiplicative.ofAdd χ) : K)) = 1 := by
  let N := Y.ad.localIwahori.normalizer
  let n := Y.ad.lift w.val
  let r := (N.label n).val.coweightEquiv.symm
  let a := v (Multiplicative.ofAdd χ)
  let f := E.datum.toLinearMap χ
  change normalizedValuation L ((ξ : L) ^ (f y - f (r y)) * algebraMap K L (a : K)) = 1
  have h := face_lift_translation_cancel B t x hx d y hy w
  change y = r y + d • (N.translation (N.torusPart n)).toAdd at h
  have hν := N.characterLog (N.torusPart n) v hv χ
  change f (N.translation (N.torusPart n)).toAdd = log (normalizedValuation K (a : K)) at hν
  have he := congrArg f h
  rw [map_add, map_nsmul, hν, nsmul_eq_mul] at he
  obtain ⟨c, _, hc⟩ := scaled_root_parameter_value hd hπ hξ
  have he' : f y - f (r y) = (d : ℤ) * log (normalizedValuation K (a : K)) := by omega
  rw [hc _ a.ne_zero, he', sub_self, mul_zero, exp_zero]

end ComparisonLemmas

section ParahoricIntegralLift

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel scalarPoints)
open Specs.ExceptionalAffineBuilding (Weights cotype parahoric)
open Specs.ExceptionalIwahoriCongruence (changeRingHom integralRing localIntegers localIntegersInclusion)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.IntegralSemisimpleModel (Model Integers IntegralPoints IntegralAlgebra integralSpec cocharacter torusPoint)
open Specs.Pinning (BasedRootDatum)

private theorem changeRingHom_injective {D : BasedRootDatum.{u}} (M : Model D)
    {R S : IntegralAlgebra.{u}} (a : R ⟶ S) (ha : Function.Injective a.hom) :
    Function.Injective (changeRingHom M.group a) := by
  let ff := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of Integers.{u})).mpr M.affine
  intro p q hpq
  have he : integralSpec.map a.op ≫ (p ≫ e.inv) = integralSpec.map a.op ≫ (q ≫ e.inv) := by
    change integralSpec.map a.op ≫ p = integralSpec.map a.op ≫ q at hpq
    simpa only [Category.assoc] using congrArg (· ≫ e.inv) hpq
  let f := ff.preimage (p ≫ e.inv)
  let g := ff.preimage (q ≫ e.inv)
  have h := ff.map_injective (f := a.op ≫ f) (g := a.op ≫ g) (by
    rw [Functor.map_comp, Functor.map_comp, ff.map_preimage, ff.map_preimage]
    exact he)
  have hfg : f = g := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    ext x
    exact ha (DFunLike.congr_fun (congrArg (fun j => j.unop.hom) h) x)
  have := congrArg (integralSpec.map) hfg
  rw [ff.map_preimage, ff.map_preimage] at this
  exact (cancel_mono e.inv).mp this

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The scalar point map conjugated by the given cocharacter at the chosen root. -/
def conjugatedScalarPoints {D : BasedRootDatum.{u}} (M : Model D) (y : D.Y) (ξ : Lˣ) :
    FieldPoints M K →* FieldPoints M L :=
  let R := integralRing L
  let s := torusPoint D R (cocharacter D y R ξ) ≫ M.torus.hom.hom
  (MulAut.conj s).toMonoidHom.comp (scalarPoints M (algebraMap K L))

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

/-- Integrality on the Iwahori and the generating wall lifts gives a unique
integral group homomorphism on the actual standard parahoric. -/
theorem exists_integral_parahoric_lift
    (t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')) (y : E.Y) (ξ : Lˣ)
    (hI : ∀ g ∈ Y.ad.I, conjugatedScalarPoints M' y ξ g ∈
      (changeRingHom M'.group (localIntegersInclusion L)).range)
    (hW : ∀ i ∈ cotype t,
      conjugatedScalarPoints M' y ξ (Y.ad.lift (Y.ad.coxeter.coxeter.simple i) : FieldPoints M' K) ∈
        (changeRingHom M'.group (localIntegersInclusion L)).range) :
    ∃! f : parahoric Y.ad (cotype t) →* IntegralPoints M'.group (localIntegers L),
      ∀ g, changeRingHom M'.group (localIntegersInclusion L) (f g) =
        conjugatedScalarPoints M' y ξ (g : FieldPoints M' K) := by
  let j := changeRingHom M'.group (localIntegersInclusion L)
  let F := conjugatedScalarPoints (K := K) M' y ξ
  let P := parahoric Y.ad (cotype t)
  have hinj : Function.Injective j :=
    changeRingHom_injective M' (localIntegersInclusion L) Subtype.val_injective
  have hP : P ≤ j.range.comap F := by
    change Subgroup.closure ((Y.ad.I : Set (FieldPoints M' K)) ∪ _) ≤ _
    apply (Subgroup.closure_le (j.range.comap F)).mpr
    rintro g (hg | ⟨i, hi, rfl⟩)
    · exact hI g hg
    · exact hW i hi
  let q := (F.comp P.subtype).codRestrict j.range (fun g => hP g.property)
  let eq := MonoidHom.ofInjective hinj
  let f := eq.symm.toMonoidHom.comp q
  have hf (g : P) : j (f g) = F g :=
    congrArg Subtype.val (eq.apply_symm_apply (q g))
  exact ⟨f, hf, fun a ha => MonoidHom.ext (fun g => hinj ((ha g).trans (hf g).symm))⟩

end ParahoricIntegralLift

section IntegralCellComparison

universe u

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct WithZero
open Specs.ExceptionalAffineRootSystems (ApartmentRoots threshold)
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel RootSlots)
open Specs.ExceptionalAffineBuilding (Weights SplitBuildingLevel)
open Specs.ExceptionalIwahoriCongruence
  (changeRingHom integralRing integralRingMap localIntegers localIntegersInclusion residueHom
    rootValuePoint cellValuePoint CellValues cellValue mapCellValues)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (markedRootPoint)
open Specs.IntegralSemisimpleModel
  (Model IntegralMarking Integers IntegralPoints IntegralAlgebra integralSpec cocharacter
    torusPoint TorusValues splitTorus rootProduct cellMap additivePoint)
open Specs.Pinning (BasedRootDatum)

open private affineTorusPointEquiv torusPoint_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private def torusPointHom (D : BasedRootDatum.{u}) (R : IntegralAlgebra.{u}) :
    TorusValues D R →* IntegralPoints (splitTorus D) R :=
  (@affineTorusPointEquiv Integers.{u} _ (Multiplicative D.X) _ R R.commRing R.algebra).toMonoidHom

private theorem markedRootPoint_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (a : D.I) (z : R) :
    changeRingHom M.group f (markedRootPoint M R a z) = markedRootPoint M S a (f.hom z) := by
  change integralSpec.map f.op ≫
      integralSpec.map (CommAlgCat.ofHom (Polynomial.aeval z : Polynomial Integers.{u} →ₐ[_] R)).op ≫
      (M.root a).hom.hom =
    integralSpec.map (CommAlgCat.ofHom (Polynomial.aeval (f.hom z) :
      Polynomial Integers.{u} →ₐ[_] S)).op ≫ (M.root a).hom.hom
  rw [← Category.assoc, ← Functor.map_comp]
  have he : f.op ≫ (CommAlgCat.ofHom (Polynomial.aeval z :
      Polynomial Integers.{u} →ₐ[_] R)).op =
      (CommAlgCat.ofHom (Polynomial.aeval (f.hom z) : Polynomial Integers.{u} →ₐ[_] S)).op := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    exact (Polynomial.aeval_algHom f.hom z).symm
  rw [he]

private def rootSlotProduct {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) : (l : List D.I) → (Fin l.length → R) → IntegralPoints M.group R
  | [], _ => 1
  | a :: l, r => markedRootPoint M R a (r 0) * rootSlotProduct M R l (Fin.tail r)

set_option backward.isDefEq.respectTransparency false in
private theorem rootSlotProduct_eq {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l : List D.I) (r : Fin l.length → R) :
    rootValuePoint M.line R l r ≫ rootProduct M.line M.root l = rootSlotProduct M R l r := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons a l ih =>
    simp only [rootValuePoint, rootProduct, rootSlotProduct]
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, ih]
    rfl

private theorem cellValue_mul_eq {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l r : List D.I) (z : CellValues D R l r) :
    cellValue M R l r z =
      rootSlotProduct M R l z.1 * ((torusPoint D R z.2.1 ≫ M.torus.hom.hom) *
        rootSlotProduct M R r z.2.2) := by
  simp only [cellValue, cellValuePoint, cellMap, MonObj.comp_mul,
    lift_fst_assoc, lift_snd_assoc, rootSlotProduct_eq]

private theorem rootSlotProduct_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (l : List D.I) (z : Fin l.length → R) :
    changeRingHom M.group f (rootSlotProduct M R l z) =
      rootSlotProduct M S l (fun i => f.hom (z i)) := by
  induction l with
  | nil => exact map_one _
  | cons a l ih =>
    rw [rootSlotProduct, map_mul, markedRootPoint_map, ih, rootSlotProduct]
    rfl

private theorem rootSlotProduct_conj {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (S : IntegralAlgebra.{u}) (v : TorusValues D S) (l : List D.I) (z : Fin l.length → S) :
    MulAut.conj (torusPoint D S v ≫ M.torus.hom.hom) (rootSlotProduct M S l z) =
      rootSlotProduct M S l (fun i => (v (Multiplicative.ofAdd (D.datum.root l[i])) : S) * z i) := by
  let s := torusPoint D S v ≫ M.torus.hom.hom
  change MulAut.conj s _ = _
  induction l with
  | nil => exact map_one (MulAut.conj s)
  | cons a l ih =>
    rw [rootSlotProduct, map_mul, ih, rootSlotProduct]
    change (s * markedRootPoint M S a (z 0) * s⁻¹) * _ = _
    have h : s * markedRootPoint M S a (z 0) * s⁻¹ =
        markedRootPoint M S a ((v (Multiplicative.ofAdd (D.datum.root a)) : S) * z 0) :=
      M.conjugation S v a (z 0)
    rw [h]
    rfl

private theorem torusPoint_conj {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (s t : TorusValues D R) :
    MulAut.conj (torusPoint D R s ≫ M.torus.hom.hom) (torusPoint D R t ≫ M.torus.hom.hom) =
      torusPoint D R t ≫ M.torus.hom.hom := by
  let i := (Specs.ExceptionalIwahoriImageComparison.integralPointHom M.torus R).comp (torusPointHom D R)
  change i s * i t * (i s)⁻¹ = i t
  rw [← map_inv, ← map_mul, ← map_mul, mul_comm s t, mul_assoc, mul_inv_cancel, mul_one]

private theorem scaled_cellValue {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (v : TorusValues D S)
    (l r : List D.I) (z : CellValues D R l r) :
    let s := torusPoint D S v ≫ M.torus.hom.hom
    MulAut.conj s (changeRingHom M.group f (cellValue M R l r z)) =
      cellValue M S l r
        (fun i => (v (Multiplicative.ofAdd (D.datum.root l[i])) : S) * f.hom (z.1 i),
         (Units.map f.hom.toMonoidHom).comp z.2.1,
         fun i => (v (Multiplicative.ofAdd (D.datum.root r[i])) : S) * f.hom (z.2.2 i)) := by
  dsimp only
  simp only [cellValue_mul_eq, map_mul, rootSlotProduct_map]
  have htor : changeRingHom M.group f (torusPoint D R z.2.1 ≫ M.torus.hom.hom) =
      torusPoint D S ((Units.map f.hom.toMonoidHom).comp z.2.1) ≫ M.torus.hom.hom := by
    change integralSpec.map f.op ≫ torusPoint D R z.2.1 ≫ M.torus.hom.hom = _
    rw [← Category.assoc, torusPoint_natural]
  rw [htor, torusPoint_conj, rootSlotProduct_conj M S v l, rootSlotProduct_conj M S v r]

section IwahoriParameters

open ValuativeRel WithZero
attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

private def localUnitOfValueOne (a : Lˣ)
    (ha : normalizedValuation L (a : L) = 1) : (localIntegers L)ˣ where
  val := ⟨a, (normalized_le_one _).mp ha.le⟩
  inv := ⟨↑a⁻¹, (normalized_le_one _).mp (by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one])⟩
  val_inv := Subtype.ext a.val_inv
  inv_val := Subtype.ext a.inv_val

private def liftUnitTorus {D : BasedRootDatum.{u}} (v : TorusValues D (integralRing L))
    (hv : ∀ χ, normalizedValuation L (v χ : L) = 1) : TorusValues D (localIntegers L) where
  toFun χ := localUnitOfValueOne (v χ) (hv χ)
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val (map_one v)
  map_mul' χ ψ := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val (map_mul v χ ψ)

omit [ValuativeExtension K L] in
private theorem liftUnitTorus_map {D : BasedRootDatum.{u}} (v : TorusValues D (integralRing L))
    (hv : ∀ χ, normalizedValuation L (v χ : L) = 1) :
    (Units.map (localIntegersInclusion L).hom.toMonoidHom).comp (liftUnitTorus v hv) = v := by
  apply MonoidHom.ext
  intro χ
  apply Units.ext
  rfl

/-- Each ordered root slot of the actual Iwahori chart has the valuation
bound for its marked absolute root. -/
private theorem iwahori_chart_parameters
    (g : FieldPoints M' K) (hg : g ∈ Y.ad.I) :
    let C := Y.ad.chart
    let A := ApartmentRoots.split E.datum ℚ
    ∃ z : CellValues E (integralRing K) C.negative C.positive,
      cellValue M'.toIntegralMarking _ C.negative C.positive z = g ∧
      (∀ χ, normalizedValuation K (z.2.1 χ : K) = 1) ∧
      (∀ i : Fin C.negative.length,
        normalizedValuation K (z.1 i) ≤ exp (-threshold (A.root C.negative[i] p'))) ∧
      (∀ i : Fin C.positive.length,
        normalizedValuation K (z.2.2 i) ≤ exp (-threshold (A.root C.positive[i] p'))) := by
  let C := Y.ad.chart
  obtain ⟨z, ⟨hz, ht, hdepth⟩, _⟩ := (Y.ad_bruhat.base_chart g).mp hg
  obtain ⟨_, _, hdir, hnegUnit, hposUnit, hparam, _⟩ := Y.ad_points
  refine ⟨C.chart.coordinates z.1 z.2, hz, ht, ?_, ?_⟩
  · intro i
    have hslot : C.chart.neg i = C.negative[i] := (C.neg_slots i).trans (congrFun hdir _)
    obtain ⟨e, he, hmap, _⟩ := hparam (C.chart.neg i)
    change normalizedValuation K
        (algebraMap Integers.{u} K (C.chart.negUnit i : Integers.{u}) *
          C.chart.negMap i (z.2 (C.chart.neg i))) ≤ _
    rw [hnegUnit i, Units.val_one, map_one, one_mul, hmap i rfl, ← he]
    exact hslot ▸ hdepth (C.chart.neg i)
  · intro i
    have hslot : C.chart.pos i = C.positive[i] := (C.pos_slots i).trans (congrFun hdir _)
    obtain ⟨e, he, _, hmap⟩ := hparam (C.chart.pos i)
    change normalizedValuation K
        (algebraMap Integers.{u} K (C.chart.posUnit i : Integers.{u}) *
          C.chart.posMap i (z.2 (C.chart.pos i))) ≤ _
    rw [hposUnit i, Units.val_one, map_one, one_mul, hmap i rfl, ← he]
    exact hslot ▸ hdepth (C.chart.pos i)

/-- After scaling, the actual Iwahori has an integral lift in the same
ordered chart. The residue coordinates vanish at the slots of positive depth. -/
theorem scaled_iwahori_integral
    (B : SplitBuildingLevel Y) (t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p'))
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    {d : ℕ} (hd : 0 < d) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hπ : normalizedValuation K (π : K) = exp (-1 : ℤ))
    (hξ : (ξ : L) ^ d = algebraMap K L (π : K))
    (g : FieldPoints M' K) (hg : g ∈ Y.ad.I) :
    let C := Y.ad.chart
    let A := ApartmentRoots.split E.datum ℚ
    ∃ z : CellValues E (localIntegers L) C.negative C.positive,
      changeRingHom M'.group (localIntegersInclusion L)
          (cellValue M'.toIntegralMarking _ C.negative C.positive z) =
        conjugatedScalarPoints M' y ξ g ∧
      (∀ i : Fin C.negative.length,
        0 < A.wallValue (C.negative[i], threshold (A.root C.negative[i] p')) x →
        (residueHom (localIntegers L)).hom (z.1 i) = 0) ∧
      (∀ i : Fin C.positive.length,
        0 < A.wallValue (C.positive[i], threshold (A.root C.positive[i] p')) x →
        (residueHom (localIntegers L)).hom (z.2.2 i) = 0) := by
  let C := Y.ad.chart
  let A := ApartmentRoots.split E.datum ℚ
  obtain ⟨z, hz, ht, hn, hp⟩ := iwahori_chart_parameters g hg
  let f := integralRingMap (algebraMap K L)
  let v := cocharacter E y (integralRing L) ξ
  let u (a : E.I) (b : K) : L :=
    (ξ : L) ^ E.datum.toLinearMap (E.datum.root a) y * algebraMap K L b
  have hint (a : E.I) (b : K)
      (hb : normalizedValuation K b ≤ exp (-threshold (A.root a p'))) :=
    scaled_parameter_integral B t x hx hd y hy hπ hξ a _ le_rfl b hb
  let zn (i : Fin C.negative.length) : localIntegers L :=
    ⟨u C.negative[i] (z.1 i), (normalized_le_one _).mp (hint _ _ (hn i)).1⟩
  let zp (i : Fin C.positive.length) : localIntegers L :=
    ⟨u C.positive[i] (z.2.2 i), (normalized_le_one _).mp (hint _ _ (hp i)).1⟩
  let vt := (Units.map f.hom.toMonoidHom).comp z.2.1
  have hv (χ : Multiplicative E.X) : normalizedValuation L (vt χ : L) = 1 := by
    change normalizedValuation L (algebraMap K L (z.2.1 χ : K)) = 1
    rw [← normalized_value_map, ht χ, map_one]
  let zl : CellValues E (localIntegers L) C.negative C.positive := (zn, liftUnitTorus vt hv, zp)
  refine ⟨zl, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [← hz]
    change changeRingHom M'.group (localIntegersInclusion L)
      (cellValue M'.toIntegralMarking _ C.negative C.positive zl) =
      MulAut.conj (torusPoint E (integralRing L) v ≫ M'.torus.hom.hom)
        (changeRingHom M'.group f (cellValue M'.toIntegralMarking _ C.negative C.positive z))
    rw [scaled_cellValue, cellValue_mul_eq, cellValue_mul_eq, map_mul, map_mul, rootSlotProduct_map,
      rootSlotProduct_map]
    have htor := torusPoint_natural (localIntegersInclusion L) (liftUnitTorus vt hv)
    have ht' : changeRingHom M'.group (localIntegersInclusion L)
          (torusPoint E (localIntegers L) zl.2.1 ≫ M'.torus.hom.hom) =
        torusPoint E (integralRing L) vt ≫ M'.torus.hom.hom := by
      change integralSpec.map (localIntegersInclusion L).op ≫
        torusPoint E (localIntegers L) zl.2.1 ≫ M'.torus.hom.hom = _
      rw [← Category.assoc]
      exact congrArg (· ≫ M'.torus.hom.hom)
        (htor.trans (congrArg (torusPoint E (integralRing L)) (liftUnitTorus_map vt hv)))
    rw [ht']
    have hn' (i : Fin C.negative.length) :
        (localIntegersInclusion L).hom (zl.1 i) =
          (v (Multiplicative.ofAdd (E.datum.root C.negative[i])) : L) * f.hom (z.1 i) := by
      change u C.negative[i] (z.1 i) =
        ((ξ ^ E.datum.toLinearMap (E.datum.root C.negative[i]) y : Lˣ) : L) * algebraMap K L (z.1 i)
      rw [Units.val_zpow_eq_zpow_val]
    have hp' (i : Fin C.positive.length) :
        (localIntegersInclusion L).hom (zl.2.2 i) =
          (v (Multiplicative.ofAdd (E.datum.root C.positive[i])) : L) * f.hom (z.2.2 i) := by
      change u C.positive[i] (z.2.2 i) =
        ((ξ ^ E.datum.toLinearMap (E.datum.root C.positive[i]) y : Lˣ) : L) * algebraMap K L (z.2.2 i)
      rw [Units.val_zpow_eq_zpow_val]
    simp only [hn', hp', vt]
  · change IsLocalRing.residue (localIntegers L) (zn i) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff L (valuation L)).mpr
      ((normalized_lt_one _).mp ((hint _ _ (hn i)).2 hi))
  · change IsLocalRing.residue (localIntegers L) (zp i) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff L (valuation L)).mpr
      ((normalized_lt_one _).mp ((hint _ _ (hp i)).2 hi))

end IwahoriParameters

open Specs.IntegralRootRelations (upper lower diagonal)
open Specs.ExceptionalMarkedRootDescent (rankOneMatrixWord wallMatrix markedWall markedWeylWord)
open scoped Matrix

private theorem wallMatrix_diagonal {R : Type*} [CommRing R] (s : Rˣ) :
    wallMatrix s = diagonal s * wallMatrix 1 := by
  apply Subtype.ext
  change (↑(wallMatrix s) : Matrix (Fin 2) (Fin 2) R) = ↑(diagonal s * wallMatrix (1 : Rˣ))
  simp only [wallMatrix, rankOneMatrixWord, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, lower, diagonal, Matrix.SpecialLinearGroup.coe_mk,
      Matrix.mul_apply, Fin.sum_univ_two]

set_option backward.isDefEq.respectTransparency false in
private theorem markedWall_torus_conjugation {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) (t : TorusValues D R) :
    let n := markedWall M R a 1
    let g := torusPoint D R t ≫ M.torus.hom.hom
    let s := t (Multiplicative.ofAdd (D.datum.root a))
    g * n * g⁻¹ =
      (torusPoint D R (cocharacter D (D.datum.coroot a) R s) ≫ M.torus.hom.hom) * n := by
  intro n g s
  let F : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    (M.rankOne a).app R |>.hom
  have hneg : D.datum.root (D.datum.reflectionPerm a a) = -D.datum.root a := by
    rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self]
  have hu (r : R) : MulAut.conj g (F (upper r)) = F (upper ((s : R) * r)) := by
    change MulAut.conj g ((M.rankOne a).app R (upper r)) = (M.rankOne a).app R (upper ((s : R) * r))
    simp only [M.rankOneUpper]
    exact M.conjugation R t a r
  have hl (r : R) : MulAut.conj g (F (lower r)) = F (lower ((↑s⁻¹ : R) * r)) := by
    change MulAut.conj g ((M.rankOne a).app R (lower r)) =
      (M.rankOne a).app R (lower ((↑s⁻¹ : R) * r))
    simp only [M.rankOneLower]
    have he : t (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm a a))) = s⁻¹ := by
      rw [hneg]
      exact map_inv t _
    have hh := M.conjugation R t (D.datum.reflectionPerm a a) r
    rw [he] at hh
    exact hh
  change MulAut.conj g (F (wallMatrix 1)) = _
  have hw : MulAut.conj g (F (wallMatrix 1)) = F (wallMatrix s) := by
    simp only [wallMatrix, rankOneMatrixWord, map_mul, hu, hl]
    simp [Units.val_neg, Units.val_one, mul_neg]
  rw [hw, wallMatrix_diagonal, map_mul]
  exact congrArg (· * n) (M.rankOneDiagonal a R s)

private theorem markedWall_conjugates_cocharacter {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) (y : D.Y) (z : Rˣ) :
    let T (y : D.Y) := torusPoint D R (cocharacter D y R z) ≫ M.torus.hom.hom
    let n := markedWall M R a 1
    n * T y * n⁻¹ = T (D.datum.coreflection a y) := by
  intro T n
  let v := cocharacter D y R z
  let q := D.datum.toLinearMap (D.datum.root a) y
  let V := cocharacter D (D.datum.coroot a) R (z ^ q)
  let F := (Specs.ExceptionalIwahoriImageComparison.integralPointHom M.torus R).comp (torusPointHom D R)
  have h : T y * n * (T y)⁻¹ = F V * n := markedWall_torus_conjugation M R a v
  have hv : T y * n * (T y)⁻¹ * n⁻¹ = F V := by rw [h, mul_inv_cancel_right]
  have hc : V⁻¹ * v = cocharacter D (D.datum.coreflection a y) R z := by
    apply MonoidHom.ext
    intro χ
    change ((z ^ q) ^ D.datum.toLinearMap (Multiplicative.toAdd χ) (D.datum.coroot a))⁻¹ *
      z ^ D.datum.toLinearMap (Multiplicative.toAdd χ) y =
        z ^ D.datum.toLinearMap (Multiplicative.toAdd χ) (D.datum.coreflection a y)
    rw [D.datum.coreflection_apply]
    change _ = z ^ D.datum.toLinearMap (Multiplicative.toAdd χ) (y - q • D.datum.coroot a)
    rw [map_sub, map_zsmul, zsmul_eq_mul, zpow_sub, zpow_mul]
    exact mul_comm _ _
  calc
    n * T y * n⁻¹ = (F V)⁻¹ * T y := by rw [← hv]; group
    _ = F (V⁻¹ * v) := by
      change (F V)⁻¹ * F v = F (V⁻¹ * v)
      rw [map_mul]
      exact congrArg (· * F v) (map_inv F V).symm
    _ = T (D.datum.coreflection a y) := by rw [hc]; rfl

private theorem markedWeylWord_cons {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) (l : List D.I) :
    markedWeylWord M R (a :: l) = markedWall M R a 1 * markedWeylWord M R l := rfl

/-- The integral word in the marked Weyl representatives acts on the
cocharacter by the cocharacter action of its finite label. -/
theorem markedWeylWord_conjugates_cocharacter {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l : List D.I) (y : D.Y) (z : Rˣ) :
    let T (y : D.Y) := torusPoint D R (cocharacter D y R z) ≫ M.torus.hom.hom
    let n := markedWeylWord M R l
    n * T y * n⁻¹ = T ((((l.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val.coweightEquiv).symm y) := by
  intro T n
  dsimp only [n]
  induction l with
  | nil =>
    change (1 : IntegralPoints M.group R) * T y * 1⁻¹ =
      T (((1 : D.datum.weylGroup).val.coweightEquiv).symm y)
    simp
    apply congrArg T
    let c := (1 : RootPairing.Aut D.datum).coweightEquiv
    change y = c.symm y
    apply c.injective
    rw [LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (RootPairing.Equiv.coweightEquiv_one D.datum) y
  | cons a l ih =>
    rw [markedWeylWord_cons]
    let p := markedWall M R a 1
    let q := markedWeylWord M R l
    have he : (p * q) * T y * (p * q)⁻¹ = p * (q * T y * q⁻¹) * p⁻¹ := by group
    rw [he, ih]
    let w := (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod
    change p * T (w.val.coweightEquiv.symm y) * p⁻¹ =
      T (((RootPairing.weylGroup.ofIdx D.datum a * w).val.coweightEquiv).symm y)
    rw [markedWall_conjugates_cocharacter]
    change T (D.datum.coreflection a (w.val.coweightEquiv.symm y)) =
      T (((RootPairing.Equiv.reflection D.datum a * w.val).coweightEquiv).symm y)
    rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.coweightEquiv_comp_toLin,
      LinearEquiv.trans_symm, LinearEquiv.trans_apply, RootPairing.Equiv.reflection_coweightEquiv]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem markedWall_one_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (a : D.I) :
    changeRingHom M.group f (markedWall M R a 1) = markedWall M S a 1 := by
  have hw : Matrix.SpecialLinearGroup.map f.hom.toRingHom (wallMatrix (1 : Rˣ)) = wallMatrix (1 : Sˣ) := by
    apply Subtype.ext
    change f.hom.toRingHom.mapMatrix (↑(wallMatrix (1 : Rˣ))) =
      (↑(wallMatrix (1 : Sˣ)) : Matrix (Fin 2) (Fin 2) S)
    simp only [wallMatrix, rankOneMatrixWord, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RingHom.mapMatrix_apply, upper, lower, Matrix.SpecialLinearGroup.coe_mk,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hn := ConcreteCategory.congr_hom ((M.rankOne a).naturality f) (wallMatrix (1 : Rˣ))
  change (M.rankOne a).app S (Matrix.SpecialLinearGroup.map f.hom.toRingHom (wallMatrix (1 : Rˣ))) =
    changeRingHom M.group f (markedWall M R a 1) at hn
  rw [hw] at hn
  exact hn.symm

private theorem markedWeylWord_map {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (l : List D.I) :
    changeRingHom M.group f (markedWeylWord M R l) = markedWeylWord M S l := by
  induction l with
  | nil => exact map_one _
  | cons a l ih => rw [markedWeylWord_cons, map_mul, markedWall_one_map, ih, markedWeylWord_cons]

section ScaledNormalizer

open ValuativeRel WithZero

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

private theorem map_torusPoint_in_group (M' : Model E) {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (v : TorusValues E R) :
    changeRingHom M'.group f (torusPoint E R v ≫ M'.torus.hom.hom) =
      torusPoint E S ((Units.map f.hom.toMonoidHom).comp v) ≫ M'.torus.hom.hom := by
  change integralSpec.map f.op ≫ torusPoint E R v ≫ M'.torus.hom.hom = _
  rw [← Category.assoc, torusPoint_natural]

set_option backward.isDefEq.respectTransparency false in
/-- A face normalizer lift becomes a unit-torus point times the integral
marked finite Weyl word after scaling. -/
theorem scaled_face_lift_integral
    (B : SplitBuildingLevel Y) (t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p'))
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    {d : ℕ} (hd : 0 < d) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hπ : normalizedValuation K (π : K) = exp (-1 : ℤ))
    (hξ : (ξ : L) ^ d = algebraMap K L (π : K))
    (w : Specs.ExceptionalAffineBuilding.standardWallSubgroup Y.ad.coxeter.coxeter
      (Specs.ExceptionalAffineBuilding.cotype t)) :
    let N := Y.ad.localIwahori.normalizer
    let n := Y.ad.lift w.val
    ∃ u : TorusValues E (localIntegers L),
      changeRingHom M'.group (localIntegersInclusion L)
          ((torusPoint E (localIntegers L) u ≫ M'.torus.hom.hom) *
            markedWeylWord M'.toIntegralMarking (localIntegers L) (N.word (N.label n))) =
        conjugatedScalarPoints M' y ξ (n : FieldPoints M' K) := by
  let N := Y.ad.localIwahori.normalizer
  let n := Y.ad.lift w.val
  let l := N.word (N.label n)
  let r := (N.label n).val.coweightEquiv.symm
  let f := integralRingMap (algebraMap K L)
  obtain ⟨v, hv⟩ := (N.torusPoints (N.torusPart n : FieldPoints M' K)).mp (N.torusPart n).property
  change (N.torusPart n : FieldPoints M' K) = torusPoint E (integralRing K) v ≫ M'.torus.hom.hom at hv
  have hn : (n : FieldPoints M' K) =
      (torusPoint E (integralRing K) v ≫ M'.torus.hom.hom) *
        markedWeylWord M'.toIntegralMarking (integralRing K) l := by
    rw [← hv]
    have h := N.lift_point (N.label n)
    change ((N.lift (N.label n)) : FieldPoints M' K) = _ at h
    rw [← h]
    change (n : FieldPoints M' K) =
      ((n : FieldPoints M' K) * ((N.lift (N.label n) : Y.ad.N) : FieldPoints M' K)⁻¹) *
        ((N.lift (N.label n)) : FieldPoints M' K)
    group
  let S := integralRing L
  let q := markedWeylWord M'.toIntegralMarking S l
  let a := cocharacter E y S ξ
  let b := cocharacter E (r y) S ξ
  let a₀ := (Units.map f.hom.toMonoidHom).comp v
  let T := (Specs.ExceptionalIwahoriImageComparison.integralPointHom M'.torus S).comp (torusPointHom E S)
  have hw : q * T a * q⁻¹ = T b := by
    obtain ⟨_, hlabels, _⟩ := Y.ad_points
    obtain ⟨_, _, _, hword⟩ := hlabels
    have he := markedWeylWord_conjugates_cocharacter M'.toIntegralMarking S l y ξ
    rw [hword (N.label n)] at he
    exact he
  let v' := a * a₀ * b⁻¹
  have hu (χ : Multiplicative E.X) : normalizedValuation L (v' χ : L) = 1 := by
    let A := E.datum.toLinearMap χ.toAdd y
    let targetWeight := E.datum.toLinearMap χ.toAdd (r y)
    let z := algebraMap K L (v χ : K)
    change normalizedValuation L
      (((ξ ^ A : Lˣ) : L) * z * (↑((ξ ^ targetWeight : Lˣ)⁻¹) : L)) = 1
    rw [Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
    have hmul : (ξ : L) ^ A * z * ((ξ : L) ^ targetWeight)⁻¹ = (ξ : L) ^ (A - targetWeight) * z := by
      rw [zpow_sub₀ ξ.ne_zero]
      ring
    rw [hmul]
    exact scaled_face_lift_torus_value B t x hx hd y hy hπ hξ w v hv χ.toAdd
  refine ⟨liftUnitTorus v' hu, ?_⟩
  change changeRingHom M'.group (localIntegersInclusion L) _ = MulAut.conj (T a)
    (changeRingHom M'.group f (n : FieldPoints M' K))
  rw [map_mul, map_torusPoint_in_group, liftUnitTorus_map, markedWeylWord_map, hn, map_mul,
    map_torusPoint_in_group, markedWeylWord_map]
  change T v' * q = T a * (T a₀ * q) * (T a)⁻¹
  calc
    _ = ((T a * T a₀) * (T b)⁻¹) * q := by
      simp only [v', map_mul]
      rw [map_inv T b]
    _ = _ := by rw [← hw]; group

/-- The marked parahoric has a unique integral lift of scalar extension
followed by conjugation by the scaling cocharacter. -/
theorem scaled_parahoric_integral
    (B : SplitBuildingLevel Y) (t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p'))
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    {d : ℕ} (hd : 0 < d) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hπ : normalizedValuation K (π : K) = exp (-1 : ℤ))
    (hξ : (ξ : L) ^ d = algebraMap K L (π : K)) :
    ∃! f : Specs.ExceptionalAffineBuilding.parahoric Y.ad
        (Specs.ExceptionalAffineBuilding.cotype t) →* IntegralPoints M'.group (localIntegers L),
      ∀ g, changeRingHom M'.group (localIntegersInclusion L) (f g) =
        conjugatedScalarPoints M' y ξ (g : FieldPoints M' K) := by
  apply exists_integral_parahoric_lift t y ξ
  · intro g hg
    obtain ⟨z, h, _, _⟩ := scaled_iwahori_integral B t x hx hd y hy hπ hξ g hg
    exact ⟨cellValue M'.toIntegralMarking _ _ _ z, h⟩
  · intro i hi
    let w : Specs.ExceptionalAffineBuilding.standardWallSubgroup Y.ad.coxeter.coxeter
        (Specs.ExceptionalAffineBuilding.cotype t) :=
      ⟨Y.ad.coxeter.coxeter.simple i, Subgroup.subset_closure ⟨i, hi, rfl⟩⟩
    obtain ⟨u, h⟩ := scaled_face_lift_integral B t x hx hd y hy hπ hξ w
    exact ⟨(torusPoint E (localIntegers L) u ≫ M'.torus.hom.hom) *
      markedWeylWord M'.toIntegralMarking (localIntegers L) _, h⟩

end ScaledNormalizer

end IntegralCellComparison

section FaceLabels

universe u

open CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalAffineBruhat (SplitLevel)
open Specs.ExceptionalAffineBuilding
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.IntegralSemisimpleModel (Model)
open Specs.Pinning (BasedRootDatum)

private def rationalWeylAction (E : BasedRootDatum.{u}) :
    E.datum.weylGroup →* ((ℚ ⊗[ℤ] E.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)) where
  toFun w := w.val.coweightEquiv.symm.baseChange ℤ ℚ E.Y E.Y
  map_one' := by
    have h := congrArg MulOpposite.unop (map_one (RootPairing.Equiv.coweightHom E.datum))
    change (1 : E.datum.Aut).coweightEquiv = (1 : E.Y ≃ₗ[ℤ] E.Y) at h
    change (1 : E.datum.Aut).coweightEquiv.symm.baseChange ℤ ℚ E.Y E.Y = 1
    rw [h]
    exact LinearEquiv.baseChange_one ℤ ℚ E.Y
  map_mul' a b := by
    change (a.val * b.val).coweightEquiv.symm.baseChange ℤ ℚ E.Y E.Y = _
    rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.coweightEquiv_comp_toLin,
      LinearEquiv.trans_symm]
    exact LinearEquiv.baseChange_mul ℤ ℚ E.Y _ _

private theorem rationalWeylAction_injective (E : BasedRootDatum.{u}) :
    Function.Injective (rationalWeylAction E) := by
  intro a b h
  have he : a.val.coweightEquiv.symm = b.val.coweightEquiv.symm := by
    ext y
    apply rational_cocharacter_injective E
    exact LinearEquiv.congr_fun h ((1 : ℚ) ⊗ₜ[ℤ] y)
  apply Subtype.ext
  apply RootPairing.Equiv.coweightHom_injective E.datum
  exact congrArg (fun m : E.Y ≃ₗ[ℤ] E.Y => MulOpposite.op m.symm) he

private theorem rationalWeylAction_reflection (E : BasedRootDatum.{u}) (a : E.I) (j : ℤ) :
    rationalWeylAction E (RootPairing.weylGroup.ofIdx E.datum a) =
      ((ApartmentRoots.split E.datum ℚ).reflection (a, j)).linear := by
  ext z
  change ((RootPairing.Equiv.reflection E.datum a).coweightEquiv.symm.baseChange ℤ ℚ E.Y E.Y) z =
    Module.reflection ((ApartmentRoots.split E.datum ℚ).diagonal a) z
  have he : (RootPairing.Equiv.reflection E.datum a).coweightEquiv.symm =
      E.datum.coreflection a := by
    rw [RootPairing.Equiv.reflection_coweightEquiv]
    rfl
  rw [he]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul q y =>
    rw [LinearEquiv.baseChange_tmul, Module.reflection_apply, RootPairing.coreflection_apply]
    change q ⊗ₜ[ℤ] (y - E.datum.root' a y • E.datum.coroot a) =
      q ⊗ₜ[ℤ] y - RootData.extendFunctional ℚ (E.datum.root' a) (q ⊗ₜ[ℤ] y) •
        ((1 : ℚ) ⊗ₜ[ℤ] E.datum.coroot a)
    have hq (z : E.Y) : q ⊗ₜ[ℤ] z = q • ((1 : ℚ) ⊗ₜ[ℤ] z) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [TensorProduct.tmul_sub, TensorProduct.tmul_smul, hq y, hq (E.datum.coroot a), map_smul,
      RootData.extendFunctional_one_tmul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_eq_mul,
      mul_comm (q : ℚ)]

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

local notation "A" => ApartmentRoots.split E.datum ℚ

private theorem finiteLabel_action (w : (A).affineWeylGroup) :
    rationalWeylAction E (Y.ad.localIwahori.normalizer.label (Y.ad.lift w)) = w.val.linear := by
  obtain ⟨_, _, _, _, _, _, hAff, _, _⟩ := Y.ad_points
  let n := Y.ad.lift w
  ext z
  have hz : w.val z =
      rationalWeylAction E (Y.ad.localIwahori.normalizer.label n) z + w.val 0 := by
    rw [← Y.ad.lift_label w, hAff, hAff]
    simp [rationalWeylAction, n]
  have hlin : w.val z = w.val.linear z + w.val 0 := by
    simpa using w.val.map_vadd (0 : ℚ ⊗[ℤ] E.Y) z
  exact add_right_cancel (hz.symm.trans hlin)

/-- The finite labels of the marked face lifts are exactly the subgroup
generated by reflections of roots taking integral values at the face point. -/
theorem face_finite_labels (B : SplitBuildingLevel Y)
    (t : Weights ((A).SimpleWall p')) (x : ℚ ⊗[ℤ] E.Y)
    (hx : rationalPoint B.ad.realization.coordinates x =
      simplexPoint B.ad.realization.coordinates B.ad.realization.vertex t) :
    Set.range (fun w : standardWallSubgroup Y.ad.coxeter.coxeter (cotype t) =>
      Y.ad.localIwahori.normalizer.label (Y.ad.lift w.val)) =
      (Subgroup.closure (RootPairing.weylGroup.ofIdx E.datum '' {a | ∃ j : ℤ, (A).root a x = j})
        : Set E.datum.weylGroup) := by
  let V := ℚ ⊗[ℤ] E.Y
  let ϕ : (A).affineWeylGroup →* (V ≃ₗ[ℚ] V) := AffineEquiv.linearHom.comp ((A).affineWeylGroup).subtype
  let S := standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)
  let U := {a : E.I | ∃ j : ℤ, (A).root a x = j}
  let F := Subgroup.closure (RootPairing.weylGroup.ofIdx E.datum '' U)
  have hImage : S.map ϕ = F.map (rationalWeylAction E) := by
    change (standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)).map ϕ =
      (Subgroup.closure (RootPairing.weylGroup.ofIdx E.datum '' U)).map (rationalWeylAction E)
    rw [B.ad.realization.wall_group, MonoidHom.map_closure, MonoidHom.map_closure]
    congr 1
    rw [Set.image_image, Set.image_image]
    ext z
    constructor
    · rintro ⟨⟨a, j⟩, ha, rfl⟩
      change realWallValue (A) B.ad.realization.coordinates (a, j)
        (simplexPoint B.ad.realization.coordinates B.ad.realization.vertex t) = 0 at ha
      rw [← hx, realWallValue_rationalPoint] at ha
      have hzero : (A).root a x + (j : ℚ) = 0 := by exact_mod_cast ha
      exact ⟨a, ⟨-j, by rw [Int.cast_neg]; linarith⟩, rationalWeylAction_reflection E a j⟩
    · rintro ⟨a, ⟨j, hj⟩, rfl⟩
      refine ⟨(a, -j), ?_, (rationalWeylAction_reflection E a (-j)).symm⟩
      change realWallValue (A) B.ad.realization.coordinates (a, -j)
        (simplexPoint B.ad.realization.coordinates B.ad.realization.vertex t) = 0
      rw [← hx, realWallValue_rationalPoint]
      change (↑((A).root a x + ((-j : ℤ) : ℚ)) : ℝ) = 0
      simp [hj]
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    have hz : ϕ w.val ∈ S.map ϕ := ⟨w.val, w.property, rfl⟩
    rw [hImage] at hz
    change w.val.val.linear ∈ F.map (rationalWeylAction E) at hz
    rw [← finiteLabel_action (Y := Y) w.val] at hz
    obtain ⟨q, hq, he⟩ := hz
    change Y.ad.localIwahori.normalizer.label (Y.ad.lift w.val) ∈ F
    rw [← rationalWeylAction_injective E he]
    exact hq
  · intro hz
    have hmem : rationalWeylAction E z ∈ F.map (rationalWeylAction E) := ⟨z, hz, rfl⟩
    rw [← hImage] at hmem
    obtain ⟨w, hw, he⟩ := hmem
    exact ⟨⟨w, hw⟩, rationalWeylAction_injective E ((finiteLabel_action (Y := Y) w).trans he)⟩

/-- Taking the linear part identifies the affine face group with the group
generated by the surviving finite reflections. -/
private def faceFiniteWeylEquiv (B : SplitBuildingLevel Y)
    (t : Weights ((A).SimpleWall p')) (x : ℚ ⊗[ℤ] E.Y)
    (hx : rationalPoint B.ad.realization.coordinates x =
      simplexPoint B.ad.realization.coordinates B.ad.realization.vertex t) :
    standardWallSubgroup Y.ad.coxeter.coxeter (cotype t) ≃*
      Subgroup.closure (RootPairing.weylGroup.ofIdx E.datum '' {a | ∃ j : ℤ, (A).root a x = j}) := by
  let W := standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)
  let W₀ := Subgroup.closure
    (RootPairing.weylGroup.ofIdx E.datum '' {a | ∃ j : ℤ, (A).root a x = j})
  let label (w : W) := Y.ad.localIwahori.normalizer.label (Y.ad.lift w.val)
  have hRange : Set.range label = (W₀ : Set E.datum.weylGroup) := face_finite_labels B t x hx
  let linear : W →* ((ℚ ⊗[ℤ] E.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)) :=
    (AffineEquiv.linearHom.comp ((A).affineWeylGroup).subtype).comp W.subtype
  have hLinear (w : W) : rationalWeylAction E (label w) = linear w :=
    finiteLabel_action (Y := Y) w.val
  let labelHom : W →* W₀ :=
    { toFun := fun w => ⟨label w, by
        change label w ∈ (W₀ : Set E.datum.weylGroup)
        rw [← hRange]
        exact Set.mem_range_self w⟩
      map_one' := by
        apply Subtype.ext
        apply rationalWeylAction_injective E
        change rationalWeylAction E (label 1) = rationalWeylAction E 1
        rw [hLinear, map_one, map_one]
      map_mul' := fun v w => by
        apply Subtype.ext
        apply rationalWeylAction_injective E
        change rationalWeylAction E (label (v * w)) = rationalWeylAction E (label v * label w)
        rw [map_mul, hLinear, hLinear, hLinear, map_mul] }
  refine MulEquiv.ofBijective labelHom ⟨?_, ?_⟩
  · intro v w h
    exact face_lift_finite_label_injective B t x hx (congrArg Subtype.val h)
  · intro w
    have hw : w.val ∈ (W₀ : Set E.datum.weylGroup) := w.property
    rw [← hRange] at hw
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, Subtype.ext hv⟩

private theorem faceFiniteWeylEquiv_val (B : SplitBuildingLevel Y)
    (t : Weights ((A).SimpleWall p')) (x : ℚ ⊗[ℤ] E.Y)
    (hx : rationalPoint B.ad.realization.coordinates x =
      simplexPoint B.ad.realization.coordinates B.ad.realization.vertex t)
    (w : standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)) :
    (faceFiniteWeylEquiv B t x hx w).val = Y.ad.localIwahori.normalizer.label (Y.ad.lift w.val) :=
  rfl

end FaceLabels

section ResiduePoints

universe u

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj WithZero
open ValuativeRel
open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel residue)
open Specs.ExceptionalAffineBuilding (Weights cotype parahoric SplitBuildingLevel)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots threshold)
open Specs.ExceptionalIwahoriCongruence
  (integralRing localIntegers localIntegersInclusion residueHom changeRingHom cellValue)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (markedRootPoint)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom)
open Specs.IntegralSemisimpleModel
  (fibre forgetFibrePoint IntegralPoints Model TorusValues torusPoint splitTorus)
open Specs.Pinning (BasedRootDatum)

open private forgetFibrePoint_comp forgetFibrePoint_mul additivePoint_zero
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private def fieldPointsHom {k : Type u} [Field k] {G H : GroupScheme k} (f : G ⟶ H) :
    GroupPoints G (CommAlgCat.of k k) →* GroupPoints H (CommAlgCat.of k k) :=
  IsMonHom.monoidHom f.hom.hom ((testSpec k).obj (op (CommAlgCat.of k k)))

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

private def integralFibreHom {k : Type u} [Field k]
    (G : Specs.IntegralSemisimpleModel.IntegralGroup.{u}) :
    GroupPoints ((fibre k).obj G) (CommAlgCat.of k k) →* IntegralPoints G (integralRing k) where
  toFun := forgetFibrePoint G (CommAlgCat.of k k)
  map_one' := by
    have h := forgetFibrePoint_mul G (CommAlgCat.of k k) 1 1
    have h' := mul_left_cancel (a := forgetFibrePoint G (CommAlgCat.of k k) 1)
      (b := forgetFibrePoint G (CommAlgCat.of k k) 1) (c := 1)
    apply h'
    rw [mul_one, ← h, one_mul]
  map_mul' := forgetFibrePoint_mul G (CommAlgCat.of k k)

private theorem fieldSubgroupPoints_injective {k : Type u} [Field k]
    {G : GroupScheme k} (C : ClosedSubgroup G) :
    Function.Injective (fieldPointsHom C.inclusion) := by
  haveI : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedImmersion
  letI : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
  exact fun _ _ h => (cancel_mono C.inclusion.hom.hom).1 h

set_option backward.isDefEq.respectTransparency false in
private theorem rootPoint_mem_range {k : Type u} [Field k]
    {E : BasedRootDatum.{u}} (M : Model E)
    {G : GroupScheme k} (i : G ⟶ (fibre k).obj M.group)
    (a : E.I) (z : k)
    (h : ∃ r : (fibre k).obj M.line.group ⟶ G, r ≫ i = (fibre k).map (M.root a)) :
    markedRootPoint M.toIntegralMarking (integralRing k) a z ∈
      MonoidHom.range ((integralFibreHom M.group).comp (fieldPointsHom i)) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨v, hv⟩ := (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective
    M.line.group (CommAlgCat.of k k)).2 (M.line.point (integralRing k) z)
  refine ⟨v ≫ r.hom.hom, ?_⟩
  change forgetFibrePoint M.group (CommAlgCat.of k k)
      ((v ≫ r.hom.hom) ≫ i.hom.hom) = _
  rw [Category.assoc, show r.hom.hom ≫ i.hom.hom = ((fibre k).map (M.root a)).hom.hom from
    congrArg (fun f => f.hom.hom) hr, forgetFibrePoint_comp, hv]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem torusPoint_mem_range {k : Type u} [Field k]
    {E : BasedRootDatum.{u}} (M : Model E)
    {G : GroupScheme k} (i : G ⟶ (fibre k).obj M.group)
    (v : TorusValues E (integralRing k))
    (h : ∃ r : (fibre k).obj (splitTorus E) ⟶ G, r ≫ i = (fibre k).map M.torus) :
    (torusPoint E (integralRing k) v ≫ M.torus.hom.hom) ∈
      MonoidHom.range ((integralFibreHom M.group).comp (fieldPointsHom i)) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨s, hs⟩ := (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective
    (splitTorus E) (CommAlgCat.of k k)).2 (torusPoint E (integralRing k) v)
  refine ⟨s ≫ r.hom.hom, ?_⟩
  change forgetFibrePoint M.group (CommAlgCat.of k k)
      ((s ≫ r.hom.hom) ≫ i.hom.hom) = _
  rw [Category.assoc, show r.hom.hom ≫ i.hom.hom = ((fibre k).map M.torus).hom.hom from
    congrArg (fun f => f.hom.hom) hr, forgetFibrePoint_comp, hs]

private theorem rootSlotProduct_mem {k : Type u} [Field k]
    {E : BasedRootDatum.{u}} (M : Model E)
    (S : Subgroup (IntegralPoints M.group (integralRing k)))
    (l : List E.I) (z : Fin l.length → k)
    (hz : ∀ j, markedRootPoint M.toIntegralMarking (integralRing k) l[j] (z j) ∈ S) :
    rootSlotProduct M.toIntegralMarking (integralRing k) l z ∈ S := by
  induction l with
  | nil => exact S.one_mem
  | cons a l ih =>
    exact S.mul_mem (hz 0) (ih (Fin.tail z) (fun j => hz j.succ))

private theorem markedRootPoint_zero {k : Type u} [Field k] {E : BasedRootDatum.{u}}
    (M : Model E) (a : E.I) :
    markedRootPoint M.toIntegralMarking (integralRing k) a 0 = 1 := by
  letI := M.line.operations
  change integralPointHom (M.root a) (integralRing k) (M.line.point _ 0) = 1
  have h : M.line.point (integralRing k) 0 = 1 := additivePoint_zero M.line (integralRing k)
  rw [h, map_one]

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

local notation "A" => ApartmentRoots.split E.datum ℚ

/-- The actual scaled Iwahori reduces into the given Borel by the marked
torus and exactly the root slots of zero depth. -/
private theorem scaled_iwahori_residue_mem
    (B : SplitBuildingLevel Y) (t : Weights ((A).SimpleWall p'))
    (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    {d : ℕ} (hd : 0 < d) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hπ : normalizedValuation K (π : K) = WithZero.exp (-1 : ℤ))
    (hξ : (ξ : L) ^ d = algebraMap K L (π : K))
    {G : GroupScheme (residue L)} (i : G ⟶ (fibre (residue L)).obj M'.group)
    (ht : ∃ r : (fibre (residue L)).obj (splitTorus E) ⟶ G,
      r ≫ i = (fibre (residue L)).map M'.torus)
    (hr : ∀ a : E.I, (∃ j : ℤ, (A).root a x = j ∧ (A).positive p' (a, -j)) →
      ∃ r : (fibre (residue L)).obj M'.line.group ⟶ G,
        r ≫ i = (fibre (residue L)).map (M'.root a))
    (g : FieldPoints M' K) (hg : g ∈ Y.ad.I)
    (q : IntegralPoints M'.group (localIntegers L))
    (hq : changeRingHom M'.group (localIntegersInclusion L) q =
      conjugatedScalarPoints M' y ξ g) :
    changeRingHom M'.group (residueHom (localIntegers L)) q ∈
      MonoidHom.range ((integralFibreHom M'.group).comp (fieldPointsHom i)) := by
  classical
  let C := Y.ad.chart
  let f := residueHom (localIntegers L)
  let S := MonoidHom.range ((integralFibreHom M'.group).comp (fieldPointsHom i))
  obtain ⟨z, he, hn, hp⟩ := scaled_iwahori_integral B t x hx hd y hy hπ hξ g hg
  have hi := changeRingHom_injective M' (localIntegersInclusion L)
    (fun a b h => Subtype.ext h)
  have hq' : q = cellValue M'.toIntegralMarking _ C.negative C.positive z :=
    hi (hq.trans he.symm)
  change changeRingHom M'.group f q ∈ S
  rw [hq', cellValue_mul_eq, map_mul, map_mul, rootSlotProduct_map, rootSlotProduct_map,
    map_torusPoint_in_group]
  have hroot (a : E.I) (z : localIntegers L)
      (hz : 0 < (A).wallValue (a, threshold ((A).root a p')) x → f.hom z = 0) :
      markedRootPoint M'.toIntegralMarking (integralRing (residue L)) a (f.hom z) ∈ S := by
    have hpos : (A).positive p' (a, threshold ((A).root a p')) :=
      (threshold_le_iff_positive _ _).mp le_rfl
    rcases (closed_alcove_wall_value B t x hx _ hpos).eq_or_lt with h | h
    · exact rootPoint_mem_range M' i a _
        (hr a ((face_positive_roots_iff_zero_depth B t x hx a).2 h.symm))
    · rw [hz h, markedRootPoint_zero]
      exact S.one_mem
  exact S.mul_mem (rootSlotProduct_mem M' S _ _ (fun j => hroot _ _ (hn j)))
    (S.mul_mem (torusPoint_mem_range M' i _ ht)
      (rootSlotProduct_mem M' S _ _ (fun j => hroot _ _ (hp j))))

end ResiduePoints

section ResidueWeylWords

universe u

open scoped TensorProduct CategoryTheory.MonObj
open Specs.ExceptionalAffineBruhat (SplitLevel)
open Specs.ExceptionalAffineBuilding (Weights cotype standardWallSubgroup SplitBuildingLevel)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.IntegralSemisimpleModel (Model)
open Specs.Pinning (BasedRootDatum)

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

private abbrev oppositeRoot {E : BasedRootDatum.{u}} (a : E.I) : E.I :=
  E.datum.reflectionPerm a a

private theorem opposite_root_value {E : BasedRootDatum.{u}} (a : E.I)
    (x : ℚ ⊗[ℤ] E.Y) :
    (ApartmentRoots.split E.datum ℚ).root (oppositeRoot a) x =
      -(ApartmentRoots.split E.datum ℚ).root a x := by
  have hneg : E.datum.root (oppositeRoot a) = -E.datum.root a := by
    change E.datum.root (E.datum.reflectionPerm a a) = -E.datum.root a
    rw [E.datum.root_reflectionPerm, E.datum.reflection_apply_self]
  have hroot : E.datum.root' (oppositeRoot a) = -E.datum.root' a := by
    change E.datum.toLinearMap (E.datum.root (oppositeRoot a)) =
      -E.datum.toLinearMap (E.datum.root a)
    rw [hneg, map_neg]
  change RootData.extendFunctional ℚ (E.datum.root' (oppositeRoot a)) x =
    -RootData.extendFunctional ℚ (E.datum.root' a) x
  rw [hroot]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, neg_add]
  | tmul q y =>
    simp [RootData.extendFunctional]

private theorem reflection_word_exists {E : BasedRootDatum.{u}} (S : Set E.I)
    (w : E.datum.weylGroup) (hw : w ∈ Subgroup.closure (RootPairing.weylGroup.ofIdx E.datum '' S)) :
    ∃ l : List E.I, (∀ a ∈ l, a ∈ S) ∧
      (l.map (RootPairing.weylGroup.ofIdx E.datum)).prod = w := by
  let s := RootPairing.weylGroup.ofIdx E.datum
  have hInv (a : E.I) : (s a)⁻¹ = s a := by
    apply Subtype.ext
    exact RootPairing.Equiv.reflection_inv E.datum a
  have hRev (l : List E.I) : (l.reverse.map s).prod = (l.map s).prod⁻¹ := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.reverse_cons, List.map_append, List.prod_append, ih, List.map_cons,
        List.prod_cons, List.map_nil, List.prod_nil, mul_one, mul_inv_rev, hInv]
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, rfl⟩ := hw
    exact ⟨[a], fun b hb => (List.mem_singleton.mp hb).symm ▸ ha, by simp⟩
  | one => exact ⟨[], by simp, rfl⟩
  | mul a b _ _ ha hb =>
    obtain ⟨la, hla, rfl⟩ := ha
    obtain ⟨lb, hlb, rfl⟩ := hb
    refine ⟨la ++ lb, fun c hc => (List.mem_append.mp hc).elim (hla c) (hlb c), ?_⟩
    rw [List.map_append, List.prod_append]
  | inv a _ ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    exact ⟨l.reverse, fun c hc => hl c (List.mem_reverse.mp hc), hRev l⟩

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

local notation "A" => ApartmentRoots.split E.datum ℚ

/-- Each finite label of a face lift is a word in the surviving reflections. -/
private theorem surviving_face_word
    (B : SplitBuildingLevel Y) (t : Weights ((A).SimpleWall p')) (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    (w : standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)) :
    ∃ l : List E.I, (∀ a ∈ l, ∃ j : ℤ, (A).root a x = j) ∧
      (l.map (RootPairing.weylGroup.ofIdx E.datum)).prod =
        Y.ad.localIwahori.normalizer.label (Y.ad.lift w.val) := by
  have hw : Y.ad.localIwahori.normalizer.label (Y.ad.lift w.val) ∈
      Set.range (fun v : standardWallSubgroup Y.ad.coxeter.coxeter (cotype t) =>
        Y.ad.localIwahori.normalizer.label (Y.ad.lift v.val)) := Set.mem_range_self w
  rw [face_finite_labels B t x hx] at hw
  exact reflection_word_exists _ _ hw

end ResidueWeylWords

section LiftingResidueCoordinates

universe u

open ValuativeRel WithZero CategoryTheory
open scoped TensorProduct WithZero
open Specs.ExceptionalAffineBruhat (residue)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalIwahoriCongruence (localIntegers residueHom)
open Specs.ExceptionalLocalRootCoordinates (canonicalExtension normalizedValuation residueMap)
open Specs.Pinning (BasedRootDatum)

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

private theorem residueInteger_surjective (hres : Function.Surjective (residueMap K L)) :
    Function.Surjective
      (fun z : localIntegers K => residueMap K L (IsLocalRing.residue (localIntegers K) z)) :=
  hres.comp IsLocalRing.residue_surjective

/-- At zero scaled depth, an arbitrary residue root parameter lifts through
the indicated base-field layer. -/
theorem lift_scaled_wall_parameter
    (hres : Function.Surjective (residueMap K L))
    {E : BasedRootDatum.{u}} (a : E.I) (x : ℚ ⊗[ℤ] E.Y)
    {d : ℕ} (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hπ : normalizedValuation K (π : K) = exp (-1 : ℤ))
    (hξ : (ξ : L) ^ d = algebraMap K L (π : K)) (n : ℤ)
    (ha : (ApartmentRoots.split E.datum ℚ).root a x = -(n : ℚ)) (b : residue L) :
    ∃ (v : K) (z : localIntegers L),
      normalizedValuation K v ≤ exp (-n) ∧
      (z : L) = (ξ : L) ^ E.datum.toLinearMap (E.datum.root a) y * algebraMap K L v ∧
      (residueHom (localIntegers L)).hom z = b := by
  letI := canonicalExtension K L
  obtain ⟨c, hc⟩ := residueInteger_surjective hres b
  let z : localIntegers L :=
    algebraMap (valuation K).valuationSubring (valuation L).valuationSubring c
  refine ⟨(π : K) ^ n * (c : K), z, ?_, ?_, ?_⟩
  · rw [map_mul, map_zpow₀, hπ, ← exp_zsmul]
    have he : n • (-1 : ℤ) = -n := by simp
    rw [he]
    apply mul_le_of_le_one_right zero_le
    exact (normalized_le_one _).2 c.property
  · exact (scaled_parameter_on_wall x y hy hξ a n ha (c : K)).symm
  · change IsLocalRing.residue (valuation L).valuationSubring z = b
    rw [← Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
      (valuation K) (valuation L)]
    exact hc


open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.IntegralSemisimpleModel (TorusValues)

def baseResidueUnits : (localIntegers K)ˣ →* (residue L)ˣ :=
  (Units.map (residueMap K L).toMonoidHom).comp
    (Units.map (IsLocalRing.residue (localIntegers K)).toMonoidHom)

private theorem baseResidueUnits_surjective (hres : Function.Surjective (residueMap K L)) :
    Function.Surjective (baseResidueUnits (K := K) (L := L)) := by
  intro u
  obtain ⟨a, ha⟩ := residueInteger_surjective hres (u : residue L)
  have hne : IsLocalRing.residue (localIntegers K) a ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [← ha]
    exact (congrArg (residueMap K L) h).trans (map_zero (residueMap K L))
  have hunit := (IsLocalRing.residue_ne_zero_iff_isUnit a).1 hne
  refine ⟨hunit.unit, Units.ext ?_⟩
  change residueMap K L (IsLocalRing.residue (localIntegers K) (hunit.unit : localIntegers K)) =
    (u : residue L)
  rwa [IsUnit.unit_spec]

/-- Unit torus parameters lift through the residue field identification
because the full marked character lattice is free. -/
theorem lift_residue_torus {E : BasedRootDatum.{u}}
    (hres : Function.Surjective (residueMap K L)) (v : TorusValues E (integralRing (residue L))) :
    ∃ u : TorusValues E (localIntegers K), (baseResidueUnits (K := K) (L := L)).comp u = v := by
  letI := E.freeX
  let b := Module.Free.chooseBasis ℤ E.X
  let f := baseResidueUnits (K := K) (L := L)
  have h (i : Module.Free.ChooseBasisIndex ℤ E.X) : ∃ u, f u = v (Multiplicative.ofAdd (b i)) :=
    baseResidueUnits_surjective hres _
  let liftBasis (i : Module.Free.ChooseBasisIndex ℤ E.X) := (h i).choose
  let liftLinear : E.X →ₗ[ℤ] Additive (localIntegers K)ˣ :=
    b.constr ℤ (Additive.ofMul ∘ liftBasis)
  let u : TorusValues E (localIntegers K) := liftLinear.toAddMonoidHom.toMultiplicativeLeft
  refine ⟨u, ?_⟩
  apply AddMonoidHom.toMultiplicativeLeft.symm.injective
  let f₁ : E.X →ₗ[ℤ] Additive (residue L)ˣ :=
    (AddMonoidHom.toMultiplicativeLeft.symm (f.comp u)).toIntLinearMap
  let f₂ : E.X →ₗ[ℤ] Additive (residue L)ˣ :=
    (AddMonoidHom.toMultiplicativeLeft.symm v).toIntLinearMap
  have he : f₁ = f₂ := by
    apply b.ext
    intro i
    change Additive.ofMul (f (Additive.toMul (liftLinear (b i)))) =
      Additive.ofMul (v (Multiplicative.ofAdd (b i)))
    rw [show liftLinear (b i) = Additive.ofMul (liftBasis i) from b.constr_basis _ _ i]
    exact congrArg Additive.ofMul (h i).choose_spec
  exact congrArg LinearMap.toAddMonoidHom he

end LiftingResidueCoordinates

section ConverseChart

open private affineTorusPointEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

universe u

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj WithZero
open Specs.ExceptionalAffineRootSystems (ApartmentRoots threshold)
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel RootSlots)
open Specs.ExceptionalIwahoriCongruence
  (integralRing cellValue cellValuePoint CellValues rootValuePoint)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.IntegralSemisimpleModel
  (IntegralAlgebra IntegralMarking AdditiveLine Integers integralSpec additivePoint Model
    torusPoint cellMap)
open Specs.Pinning (BasedRootDatum)
open Specs.OrderedRootProducts (Enumerates)

private theorem integralAdditivePoint_injective (R : IntegralAlgebra.{u}) :
    Function.Injective (additivePoint R) := by
  intro a b h
  let ff := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
  have h' := congrArg (fun m => m.unop.hom (Polynomial.X : Polynomial Integers.{u}))
    (ff.map_injective h)
  simpa using h'

private theorem rootValuePoint_injective {I : Type u} (L : AdditiveLine.{u})
    (R : IntegralAlgebra.{u}) (l : List I) :
    Function.Injective (rootValuePoint L R l) := by
  induction l with
  | nil =>
    intro a b _
    funext i
    exact Fin.elim0 i
  | cons a l ih =>
    intro z w h
    have h0 := congrArg (· ≫ fst _ _) h
    have ht := congrArg (· ≫ snd _ _) h
    simp only [rootValuePoint, lift_fst] at h0
    simp only [rootValuePoint, lift_snd] at ht
    funext j
    refine Fin.cases (integralAdditivePoint_injective R h0) (fun i => congrFun (ih ht) i) j

set_option backward.isDefEq.respectTransparency false in
private theorem cellValue_injective {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l r : List D.I)
    (hl : Enumerates l {a | ¬ D.base.IsPos a}) (hr : Enumerates r {a | D.base.IsPos a}) :
    Function.Injective (cellValue M R l r) := by
  let f := cellMap M.line M.torus M.root l r
  haveI : IsOpenImmersion f.left := M.openCell l r hl hr
  letI : Mono f := Over.mono_of_mono_left _
  intro a b h
  have he : cellValuePoint M.line R l r a = cellValuePoint M.line R l r b :=
    (cancel_mono f).1 h
  have hl' := congrArg (· ≫ fst _ _) he
  have hr' := congrArg (· ≫ snd _ _) he
  simp only [cellValuePoint, lift_fst] at hl'
  simp only [cellValuePoint, lift_snd] at hr'
  have ht := congrArg (· ≫ fst _ _) hr'
  have hp := congrArg (· ≫ snd _ _) hr'
  simp only [lift_fst] at ht
  simp only [lift_snd] at hp
  exact Prod.ext (rootValuePoint_injective M.line R l hl')
    (Prod.ext ((@affineTorusPointEquiv Integers.{u} _ (Multiplicative D.X) _
      R R.commRing R.algebra).injective ht)
      (rootValuePoint_injective M.line R r hp))

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

local notation "A" => ApartmentRoots.split E.datum ℚ

/-- The integral depth conditions in the marked absolute chart suffice for
membership in the actual Iwahori. -/
private theorem iwahori_of_chart_parameters
    (z : CellValues E (integralRing K) Y.ad.chart.negative Y.ad.chart.positive)
    (ht : ∀ χ, normalizedValuation K (z.2.1 χ : K) = 1)
    (hn : ∀ i : Fin Y.ad.chart.negative.length,
      normalizedValuation K (z.1 i) ≤
        WithZero.exp (-threshold ((A).root Y.ad.chart.negative[i] p')))
    (hp : ∀ i : Fin Y.ad.chart.positive.length,
      normalizedValuation K (z.2.2 i) ≤
        WithZero.exp (-threshold ((A).root Y.ad.chart.positive[i] p'))) :
    cellValue M'.toIntegralMarking _ Y.ad.chart.negative Y.ad.chart.positive z ∈ Y.ad.I := by
  classical
  let C := Y.ad.chart
  let g := cellValue M'.toIntegralMarking _ C.negative C.positive z
  obtain ⟨u, v, huv⟩ := (C.rational z).1 ⟨g, rfl⟩
  obtain ⟨_, _, hdir, hnegUnit, hposUnit, hparam, _⟩ := Y.ad_points
  have hnslot (i : Fin C.negative.length) : C.chart.neg i = C.negative[i] :=
    (C.neg_slots i).trans (congrFun hdir _)
  have hpslot (i : Fin C.positive.length) : C.chart.pos i = C.positive[i] :=
    (C.pos_slots i).trans (congrFun hdir _)
  have hslot (a : E.I) : (∃ i, C.chart.neg i = a) ∨ (∃ i, C.chart.pos i = a) := by
    by_cases ha : E.base.IsPos a
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((C.positive_enumerates.2 a).2 ha)
      exact Or.inr ⟨i, (hpslot i).trans hi⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((C.negative_enumerates.2 a).2 ha)
      exact Or.inl ⟨i, (hnslot i).trans hi⟩
  have negCoord (t : C.chart.torus) (x : ∀ a, C.parameter a) (i : Fin C.negative.length) :
      (C.chart.coordinates t x).1 i = C.chart.negMap i (x (C.chart.neg i)) := by
    change algebraMap Integers.{u} K (C.chart.negUnit i : Integers.{u}) * _ = _
    rw [hnegUnit i, Units.val_one, map_one, one_mul]
  have posCoord (t : C.chart.torus) (x : ∀ a, C.parameter a) (i : Fin C.positive.length) :
      (C.chart.coordinates t x).2.2 i = C.chart.posMap i (x (C.chart.pos i)) := by
    change algebraMap Integers.{u} K (C.chart.posUnit i : Integers.{u}) * _ = _
    rw [hposUnit i, Units.val_one, map_one, one_mul]
  apply (Y.ad_bruhat.base_chart g).2
  refine ⟨(u, v), ⟨congrArg (cellValue M'.toIntegralMarking _ C.negative C.positive) huv,
    ?_, ?_⟩, ?_⟩
  · intro χ
    exact (congrArg (fun d => normalizedValuation K (d.2.1 χ : K)) huv).trans (ht χ)
  · intro a
    rcases hslot a with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨f, hf, hmap, _⟩ := hparam (C.chart.neg i)
      rw [hf, ← hmap i rfl, ← negCoord u v i]
      exact (congrArg (fun d => normalizedValuation K (d.1 i)) huv) ▸
        (hnslot i ▸ hn i)
    · obtain ⟨f, hf, _, hmap⟩ := hparam (C.chart.pos i)
      rw [hf, ← hmap i rfl, ← posCoord u v i]
      exact (congrArg (fun d => normalizedValuation K (d.2.2 i)) huv) ▸
        (hpslot i ▸ hp i)
  · rintro ⟨u', v'⟩ ⟨hv', _, _⟩
    have hz := cellValue_injective M'.toIntegralMarking (integralRing K) _ _
      C.negative_enumerates C.positive_enumerates hv'
    refine Prod.ext (Subtype.ext ((congrArg (fun a => a.2.1) hz).trans
      (congrArg (fun a => a.2.1) huv).symm)) ?_
    funext a
    have he := hz.trans huv.symm
    rcases hslot a with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · apply (C.chart.negMap i).injective
      rw [← negCoord u' v' i, ← negCoord u v i]
      exact congrArg (fun a => a.1 i) he
    · apply (C.chart.posMap i).injective
      rw [← posCoord u' v' i, ← posCoord u v i]
      exact congrArg (fun a => a.2.2 i) he

end ConverseChart

section SchemeTorusAction

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj
open Specs.ExceptionalMarkedRootDescent (markedWall markedWeylWord)
open Specs.ExceptionalIwahoriImageComparison (integralPointHom)
open Specs.IntegralSemisimpleModel
  (IntegralAlgebra IntegralMarking IntegralPoints TorusValues torusPoint cocharacter)
open Specs.Pinning (BasedRootDatum)

private def reflectedCharacter (E : BasedRootDatum.{u}) (w : E.datum.weylGroup) :
    Multiplicative E.X →* Multiplicative E.X where
  toFun χ := Multiplicative.ofAdd (w.val.weightEquiv.symm χ.toAdd)
  map_one' := congrArg Multiplicative.ofAdd (map_zero w.val.weightEquiv.symm)
  map_mul' a b := congrArg Multiplicative.ofAdd
    (map_add w.val.weightEquiv.symm a.toAdd b.toAdd)

private theorem reflectedCharacter_one (E : BasedRootDatum.{u}) :
    reflectedCharacter E 1 = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro χ
  apply Multiplicative.toAdd.injective
  change (1 : RootPairing.Aut E.datum).weightEquiv.symm χ.toAdd = χ.toAdd
  let f := (1 : RootPairing.Aut E.datum).weightEquiv
  apply f.injective
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun (RootPairing.Equiv.weightEquiv_one E.datum) χ.toAdd).symm

private theorem reflectedCharacter_mul (E : BasedRootDatum.{u}) (w v : E.datum.weylGroup) :
    reflectedCharacter E (w * v) = (reflectedCharacter E v).comp (reflectedCharacter E w) := by
  apply MonoidHom.ext
  intro χ
  apply Multiplicative.toAdd.injective
  change (w.val * v.val).weightEquiv.symm χ.toAdd =
    v.val.weightEquiv.symm (w.val.weightEquiv.symm χ.toAdd)
  rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.weightEquiv_comp_toLin,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem markedWall_conjugates_torus {E : BasedRootDatum.{u}} (M : IntegralMarking E)
    (R : IntegralAlgebra.{u}) (a : E.I) (v : TorusValues E R) :
    let n := markedWall M R a 1
    let T (v : TorusValues E R) := torusPoint E R v ≫ M.torus.hom.hom
    n * T v * n⁻¹ = T (v.comp (reflectedCharacter E (RootPairing.weylGroup.ofIdx E.datum a))) := by
  intro n T
  let b := v (Multiplicative.ofAdd (E.datum.root a))
  let u := cocharacter E (E.datum.coroot a) R b
  let f := (integralPointHom M.torus R).comp (torusPointHom E R)
  have h : T v * n * (T v)⁻¹ = f u * n := markedWall_torus_conjugation M R a v
  have he : T v * n * (T v)⁻¹ * n⁻¹ = f u := by rw [h, mul_inv_cancel_right]
  have hu : u⁻¹ * v = v.comp (reflectedCharacter E (RootPairing.weylGroup.ofIdx E.datum a)) := by
    apply MonoidHom.ext
    intro χ
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]
    change (b ^ E.datum.toLinearMap χ.toAdd (E.datum.coroot a))⁻¹ * v χ =
      v (Multiplicative.ofAdd ((RootPairing.Equiv.reflection E.datum a).weightEquiv.symm χ.toAdd))
    rw [RootPairing.Equiv.reflection_weightEquiv]
    change _ = v (Multiplicative.ofAdd (E.datum.reflection a χ.toAdd))
    rw [RootPairing.reflection_apply]
    let m := E.datum.toLinearMap χ.toAdd (E.datum.coroot a)
    change (b ^ m)⁻¹ * v χ =
      v (χ / (Multiplicative.ofAdd (E.datum.root a)) ^ m)
    rw [map_div, map_zpow]
    exact mul_comm _ _
  calc
    n * T v * n⁻¹ = (f u)⁻¹ * T v := by rw [← he]; group
    _ = f (u⁻¹ * v) := by
      change (f u)⁻¹ * f v = _
      rw [map_mul]
      exact congrArg (· * f v) (map_inv f u).symm
    _ = _ := by rw [hu]; rfl

/-- The marked Weyl word conjugates the full marked torus by its lattice
action, over arbitrary integral test algebras. -/
theorem markedWeylWord_conjugates_torus {E : BasedRootDatum.{u}} (M : IntegralMarking E)
    (R : IntegralAlgebra.{u}) (l : List E.I) (v : TorusValues E R) :
    let T (v : TorusValues E R) := torusPoint E R v ≫ M.torus.hom.hom
    let n := markedWeylWord M R l
    n * T v * n⁻¹ = T (v.comp
      (reflectedCharacter E (l.map (RootPairing.weylGroup.ofIdx E.datum)).prod)) := by
  intro T n
  dsimp only [n]
  induction l with
  | nil =>
    change (1 : IntegralPoints M.group R) * T v * 1⁻¹ = T (v.comp (reflectedCharacter E 1))
    rw [reflectedCharacter_one, MonoidHom.comp_id, one_mul, inv_one, mul_one]
  | cons a l ih =>
    rw [markedWeylWord_cons]
    let p := markedWall M R a 1
    let q := markedWeylWord M R l
    have he : (p * q) * T v * (p * q)⁻¹ = p * (q * T v * q⁻¹) * p⁻¹ := by group
    rw [he, ih]
    let w := (l.map (RootPairing.weylGroup.ofIdx E.datum)).prod
    let s := RootPairing.weylGroup.ofIdx E.datum a
    change p * T (v.comp (reflectedCharacter E w)) * p⁻¹ =
      T (v.comp (reflectedCharacter E (s * w)))
    rw [markedWall_conjugates_torus, reflectedCharacter_mul, MonoidHom.comp_assoc]

end SchemeTorusAction

section PointGroups

universe u

/-- A comparison of both double-coset decompositions lifts the point map
through the residue subgroup and identifies the inverse image of the Borel. -/
private theorem reductionOfDoubleCosets
    {P H A W : Type u} [Group P] [Group H] [Group A]
    (I : Subgroup P) (B : Subgroup H) (r : P →* A) (i : H →* A)
    (hi : Function.Injective i)
    (n : W → P) (m : W → H)
    (hI : I.map r = B.map i)
    (hn : ∀ w, r (n w) = i (m w))
    (hP : ∀ g : P, ∃ a b : I, ∃ w : W, g = a.val * n w * b.val)
    (hH : ∀ h : H, ∃ a b : B, ∃ w : W, h = a.val * m w * b.val)
    (hB : ∀ w, m w ∈ B → n w ∈ I) :
    ∃ q : P →* H, (∀ g, i (q g) = r g) ∧ Function.Surjective q ∧
      (∀ g, q g ∈ B ↔ g ∈ I) ∧ I.map q = B := by
  have liftI (a : I) : ∃ b : B, i b = r a := by
    have h : r a ∈ I.map r := ⟨a, a.property, rfl⟩
    rw [hI] at h
    obtain ⟨b, hb, he⟩ := h
    exact ⟨⟨b, hb⟩, he⟩
  have liftB (b : B) : ∃ a : I, r a = i b := by
    have h : i b ∈ B.map i := ⟨b, b.property, rfl⟩
    rw [← hI] at h
    obtain ⟨a, ha, he⟩ := h
    exact ⟨⟨a, ha⟩, he⟩
  have hLift (g : P) : ∃ h : H, i h = r g := by
    obtain ⟨a, b, w, rfl⟩ := hP g
    obtain ⟨a', ha'⟩ := liftI a
    obtain ⟨b', hb'⟩ := liftI b
    exact ⟨a'.val * m w * b'.val, by simp only [map_mul, ha', hb', hn]⟩
  let f (g : P) : H := (hLift g).choose
  have hf (g : P) : i (f g) = r g := (hLift g).choose_spec
  let q : P →* H :=
    { toFun := f
      map_one' := hi (by rw [hf, map_one, map_one])
      map_mul' := fun a b => hi (by rw [hf, map_mul i, hf, hf, map_mul]) }
  have hq (g : P) : i (q g) = r g := hf g
  have hqI (a : I) : q a ∈ B := by
    obtain ⟨b, hb⟩ := liftI a
    exact (hi ((hq a).trans hb.symm)).symm ▸ b.property
  have hqm (w : W) : q (n w) = m w := hi ((hq _).trans (hn w))
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨a, b, w, rfl⟩ := hH h
    obtain ⟨a', ha'⟩ := liftB a
    obtain ⟨b', hb'⟩ := liftB b
    refine ⟨a'.val * n w * b'.val, ?_⟩
    simp only [map_mul, hqm, hi ((hq a').trans ha'), hi ((hq b').trans hb')]
  · intro g
    constructor
    · intro hg
      obtain ⟨a, b, w, rfl⟩ := hP g
      have he : q (n w) = (q a)⁻¹ * q (a.val * n w * b.val) * (q b)⁻¹ := by
        simp only [map_mul]
        group
      have hw : q (n w) ∈ B := he ▸ B.mul_mem
        (B.mul_mem (B.inv_mem (hqI a)) hg) (B.inv_mem (hqI b))
      exact I.mul_mem (I.mul_mem a.property (hB w (hqm w ▸ hw))) b.property
    · exact fun hg => hqI ⟨g, hg⟩
  · apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact hqI ⟨a, ha⟩
    · intro b hb
      obtain ⟨a, ha⟩ := liftB ⟨b, hb⟩
      exact ⟨a, a.property, hi ((hq _).trans ha)⟩

end PointGroups

section RationalFlags

universe u

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Fppf (fieldBase)
open Specs.TorsorObstruction (rationalCosetMap fieldNeutralClass fieldGroupSectionsAreSheaf)

open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections
open private kBorel_smooth_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private representedProjection_apply projection_eq_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

set_option backward.isDefEq.respectTransparency false in
/-- Rational flags for the given Borel over the finite residue field.
The formulas use the projection of the representing right quotient. -/
theorem borelFlagPresentation {k : Type u} [Field k] [Finite k]
    (G : AffineAlgebraicGroup k) (B : ClosedSubgroup G.val) (hB : IsKBorel B) :
    ∃ Q : QuotientEmbedding.Presentation B,
      Function.Surjective (fun g : GroupPoints G.val (CommAlgCat.of k k) => g ≫ Q.projection) ∧
      ∀ a b : GroupPoints G.val (CommAlgCat.of k k),
        a ≫ Q.projection = b ≫ Q.projection ↔
          ∃ r : GroupPoints B.group (CommAlgCat.of k k),
            r ≫ B.inclusion.hom.hom = a⁻¹ * b := by
  classical
  letI := Fintype.ofFinite k
  letI : ConnectedSpace B.group.X.left := (kBorel_smooth_connected G B hB).2
  let G' := Unipotent.closedSubgroupAlgebraicGroup B
  letI : LocallyOfFiniteType B.group.X.hom := G'.property.2.1
  letI : QuasiCompact B.group.X.hom := G'.property.2.2
  obtain ⟨δ, _, hδ, _, _, _, _, hrange, _, _⟩ := TorsorObstruction.pointedExactness B
  have hCosets : Function.Surjective (rationalCosetMap B) := by
    intro s
    change s ∈ Set.range (rationalCosetMap B)
    rw [hrange]
    change δ s = fieldNeutralClass B.group
    obtain ⟨h, hh⟩ := hδ s
    rw [hh]
    exact langFppfTorsor k B.group (fieldGroupSectionsAreSheaf B.group) ⟨_, h⟩
  obtain ⟨Q⟩ := LinearAlgebraicGroups.QuotientEmbedding.quotientEmbedding k G B
  refine ⟨Q, ?_, fun a b => projection_eq_iff Q a b⟩
  intro x
  let baseIso : (testSpec k).obj (op (CommAlgCat.of k k)) ≅ fieldBase k := groundIso
  let projectIso := Q.quotientIso.hom.hom.app (op (fieldBase k))
  obtain ⟨s, hs⟩ :=
    (ConcreteCategory.bijective_of_isIso projectIso).2 (ULift.up (baseIso.inv ≫ x))
  obtain ⟨c, hc⟩ := hCosets s
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have hg : g ≫ Q.projection = baseIso.inv ≫ x :=
    ULift.up.inj <| (representedProjection_apply Q g).symm.trans
      ((congrArg projectIso hc).trans hs)
  refine ⟨baseIso.hom ≫ g, ?_⟩
  change (baseIso.hom ≫ g) ≫ Q.projection = x
  rw [Category.assoc, hg, Iso.hom_inv_id_assoc]

end RationalFlags

section IwahoriCoordinateLifts

universe u

open AlgebraicGeometry CategoryTheory ValuativeRel WithZero
open scoped TensorProduct CategoryTheory.MonObj WithZero
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel residue)
open Specs.ExceptionalAffineBuilding (Weights SplitBuildingLevel)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots threshold)
open Specs.ExceptionalIwahoriCongruence
  (integralRing integralRingMap localIntegers localIntegersInclusion residueHom changeRingHom
    cellValue CellValues)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom)
open Specs.ExceptionalLocalRootCoordinates (canonicalExtension normalizedValuation residueMap)
open Specs.ExceptionalMarkedRootDescent (markedRootPoint)
open Specs.IntegralSemisimpleModel (Model IntegralMarking IntegralAlgebra IntegralPoints
  TorusValues torusPoint cocharacter)
open Specs.Pinning (BasedRootDatum)

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra
open private additivePoint_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private theorem rootPoint_zero {E : BasedRootDatum.{u}} (M : IntegralMarking E)
    (R : IntegralAlgebra.{u}) (a : E.I) :
    markedRootPoint M R a 0 = 1 := by
  letI := M.line.operations
  change integralPointHom (M.root a) R (M.line.point R 0) = 1
  have h : M.line.point R 0 = 1 := additivePoint_zero M.line R
  rw [h, map_one]

private theorem rootSlotProduct_single {E : BasedRootDatum.{u}} (M : IntegralMarking E)
    (R : IntegralAlgebra.{u}) (a : E.I) (v : R) (l : List E.I) (hl : l.Nodup)
    [DecidableEq E.I] :
    rootSlotProduct M R l (fun j => if l[j] = a then v else 0) =
      if a ∈ l then markedRootPoint M R a v else 1 := by
  induction l with
  | nil => simp [rootSlotProduct]
  | cons b l ih =>
    have ht := ih (List.nodup_cons.1 hl).2
    change markedRootPoint M R b (if b = a then v else 0) *
      rootSlotProduct M R l (fun j => if l[j] = a then v else 0) = _
    rw [ht]
    by_cases hb : b = a
    · subst b
      simp [(List.nodup_cons.1 hl).1]
    · simp [hb, Ne.symm hb, rootPoint_zero]

private theorem rootSlotProduct_zero {E : BasedRootDatum.{u}} (M : IntegralMarking E)
    (R : IntegralAlgebra.{u}) (l : List E.I) :
    rootSlotProduct M R l 0 = 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change markedRootPoint M R a 0 * rootSlotProduct M R l 0 = 1
    rw [rootPoint_zero, ih, mul_one]

private theorem torusPoint_one_in_group {E : BasedRootDatum.{u}} (M : IntegralMarking E)
    (R : IntegralAlgebra.{u}) : torusPoint E R 1 ≫ M.torus.hom.hom = 1 :=
  map_one ((integralPointHom M.torus R).comp (torusPointHom E R))

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

local notation "A" => ApartmentRoots.split E.datum ℚ

set_option backward.isDefEq.respectTransparency false in
private theorem rootPoint_mem_iwahori (a : E.I) (v : K)
    (hv : normalizedValuation K v ≤ exp (-threshold ((A).root a p'))) :
    markedRootPoint M'.toIntegralMarking (integralRing K) a v ∈ Y.ad.I := by
  classical
  let C := Y.ad.chart
  let z : CellValues E (integralRing K) C.negative C.positive :=
    (fun j => if C.negative[j] = a then v else 0, 1,
     fun j => if C.positive[j] = a then v else 0)
  have h := iwahori_of_chart_parameters (Y := Y) z
    (by intro χ; change normalizedValuation K 1 = 1; exact map_one _)
    (by intro j; dsimp only [z]; split; next h => rw [h]; exact hv
        next _ => rw [map_zero]; exact zero_le)
    (by intro j; dsimp only [z]; split; next h => rw [h]; exact hv
        next _ => rw [map_zero]; exact zero_le)
  change cellValue M'.toIntegralMarking (integralRing K) C.negative C.positive z ∈ Y.ad.I at h
  rw [cellValue_mul_eq] at h
  simp only [z, torusPoint_one_in_group, one_mul] at h
  rw [rootSlotProduct_single _ _ _ _ _ C.negative_enumerates.1,
    rootSlotProduct_single _ _ _ _ _ C.positive_enumerates.1] at h
  by_cases ha : E.base.IsPos a
  · have hp := (C.positive_enumerates.2 a).2 ha
    have hn : a ∉ C.negative := fun hm => (C.negative_enumerates.2 a).1 hm ha
    simpa only [if_neg hn, if_pos hp, one_mul] using h
  · have hn := (C.negative_enumerates.2 a).2 ha
    have hp : a ∉ C.positive := fun hm => ha ((C.positive_enumerates.2 a).1 hm)
    simpa only [if_neg hp, if_pos hn, mul_one] using h

set_option backward.isDefEq.respectTransparency false in
private theorem torusPoint_mem_iwahori (v : TorusValues E (integralRing K))
    (hv : ∀ χ, normalizedValuation K (v χ : K) = 1) :
    (torusPoint E (integralRing K) v ≫ M'.torus.hom.hom) ∈ Y.ad.I := by
  let C := Y.ad.chart
  let z : CellValues E (integralRing K) C.negative C.positive := (0, v, 0)
  have h := iwahori_of_chart_parameters (Y := Y) z hv
    (by intro j; change normalizedValuation K 0 ≤ _; rw [map_zero]; exact zero_le)
    (by intro j; change normalizedValuation K 0 ≤ _; rw [map_zero]; exact zero_le)
  change cellValue M'.toIntegralMarking (integralRing K) C.negative C.positive z ∈ Y.ad.I at h
  rw [cellValue_mul_eq] at h
  simpa only [z, rootSlotProduct_zero, one_mul, mul_one] using h

variable {L : Type u} [Field L] [Algebra K L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

local notation "Rₖ" => integralRing (residue L)

set_option backward.isDefEq.respectTransparency false in
private theorem lift_iwahori_root_point
    (B : SplitBuildingLevel Y) (t : Weights ((A).SimpleWall p')) (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    (hres : Function.Surjective (residueMap K L))
    {d : ℕ} (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hπ : normalizedValuation K (π : K) = exp (-1 : ℤ))
    (hξ : (ξ : L) ^ d = algebraMap K L (π : K)) (a : E.I)
    (ha : ∃ j : ℤ, (A).root a x = j ∧ (A).positive p' (a, -j)) (b : residue L) :
    ∃ (g : FieldPoints M' K) (_ : g ∈ Y.ad.I) (u : IntegralPoints M'.group (localIntegers L)),
      changeRingHom M'.group (localIntegersInclusion L) u = conjugatedScalarPoints M' y ξ g ∧
      changeRingHom M'.group (residueHom (localIntegers L)) u =
        markedRootPoint M'.toIntegralMarking Rₖ a b := by
  let n := threshold ((A).root a p')
  have hwall := (face_positive_roots_iff_zero_depth B t x hx a).1 ha
  have ha' : (A).root a x = -(n : ℚ) := by
    change (A).root a x + (n : ℚ) = 0 at hwall
    linarith
  obtain ⟨v, z, hv, hz, hr⟩ := lift_scaled_wall_parameter hres a x y hy hπ hξ n ha' b
  refine ⟨markedRootPoint M'.toIntegralMarking (integralRing K) a v,
    rootPoint_mem_iwahori (Y := Y) a v hv,
    markedRootPoint M'.toIntegralMarking (localIntegers L) a z, ?_, ?_⟩
  · let w := cocharacter E y (integralRing L) ξ
    change changeRingHom M'.group (localIntegersInclusion L)
        (markedRootPoint M'.toIntegralMarking _ a z) =
      MulAut.conj (torusPoint E (integralRing L) w ≫ M'.torus.hom.hom)
        (changeRingHom M'.group (integralRingMap (algebraMap K L))
          (markedRootPoint M'.toIntegralMarking _ a v))
    rw [markedRootPoint_map, markedRootPoint_map]
    refine Eq.trans ?_ (M'.conjugation (integralRing L) w a _).symm
    apply congrArg (markedRootPoint M'.toIntegralMarking (integralRing L) a)
    change (z : L) =
      (↑(ξ ^ E.datum.toLinearMap (E.datum.root a) y) : L) * algebraMap K L v
    rw [Units.val_zpow_eq_zpow_val]
    exact hz
  · rw [markedRootPoint_map]
    exact congrArg (markedRootPoint M'.toIntegralMarking Rₖ a) hr

set_option backward.isDefEq.respectTransparency false in
private theorem lift_iwahori_torus_point (hres : Function.Surjective (residueMap K L))
    (y : E.Y) (ξ : Lˣ) (v : TorusValues E Rₖ) :
    ∃ (g : FieldPoints M' K) (_ : g ∈ Y.ad.I) (u : IntegralPoints M'.group (localIntegers L)),
      changeRingHom M'.group (localIntegersInclusion L) u = conjugatedScalarPoints M' y ξ g ∧
      changeRingHom M'.group (residueHom (localIntegers L)) u =
        torusPoint E Rₖ v ≫ M'.torus.hom.hom := by
  letI := canonicalExtension K L
  obtain ⟨v₀, hv₀⟩ := lift_residue_torus hres v
  let f : localIntegers K ⟶ localIntegers L := CommAlgCat.ofHom
    { toRingHom := algebraMap (valuation K).valuationSubring (valuation L).valuationSubring
      commutes' := fun n => map_intCast
        (algebraMap (valuation K).valuationSubring (valuation L).valuationSubring) n.down }
  let vK := (Units.map (localIntegersInclusion K).hom.toMonoidHom).comp v₀
  let vL := (Units.map f.hom.toMonoidHom).comp v₀
  have hvK (χ : Multiplicative E.X) : normalizedValuation K (vK χ : K) = 1 := by
    have h := (normalized_le_one _).2 (v₀ χ : localIntegers K).property
    have hh := (normalized_le_one _).2 (↑((v₀ χ)⁻¹) : localIntegers K).property
    change normalizedValuation K (vK χ : K) ≤ 1 at h
    change normalizedValuation K (↑(vK χ)⁻¹ : K) ≤ 1 at hh
    rw [Units.val_inv_eq_inv_val, map_inv₀] at hh
    have hne := (_root_.map_ne_zero (normalizedValuation K)).2 (vK χ).ne_zero
    have hle := mul_le_mul_of_nonneg_left hh (zero_le (a := normalizedValuation K (vK χ : K)))
    rw [mul_inv_cancel₀ hne, mul_one] at hle
    exact le_antisymm h hle
  refine ⟨torusPoint E (integralRing K) vK ≫ M'.torus.hom.hom,
    torusPoint_mem_iwahori (Y := Y) vK hvK, torusPoint E (localIntegers L) vL ≫ M'.torus.hom.hom,
    ?_, ?_⟩
  · change changeRingHom M'.group (localIntegersInclusion L) _ =
      MulAut.conj (torusPoint E (integralRing L) (cocharacter E y (integralRing L) ξ) ≫
        M'.torus.hom.hom)
        (changeRingHom M'.group (integralRingMap (algebraMap K L))
          (torusPoint E (integralRing K) vK ≫ M'.torus.hom.hom))
    rw [map_torusPoint_in_group, map_torusPoint_in_group, torusPoint_conj]
    apply congrArg (fun z => torusPoint E (integralRing L) z ≫ M'.torus.hom.hom)
    apply MonoidHom.ext
    intro χ
    apply Units.ext
    exact Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
      (vK := valuation K) (vL := valuation L) (v₀ χ : localIntegers K)
  · rw [map_torusPoint_in_group]
    apply congrArg (fun z => torusPoint E Rₖ z ≫ M'.torus.hom.hom)
    rw [← hv₀]
    apply MonoidHom.ext
    intro χ
    apply Units.ext
    change IsLocalRing.residue (valuation L).valuationSubring
      (algebraMap (valuation K).valuationSubring (valuation L).valuationSubring
        (v₀ χ : localIntegers K)) =
      residueMap K L (IsLocalRing.residue (valuation K).valuationSubring (v₀ χ : localIntegers K))
    rw [Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
      (valuation K) (valuation L)]

end IwahoriCoordinateLifts

section ResidueRootData

universe u

open AlgebraicGeometry CategoryTheory
open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedRootPoint)
open Specs.IntegralSemisimpleModel (Model fibre forgetFibrePoint)
open Specs.Pinning (BasedRootDatum transportCharacter)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open scoped CategoryTheory.MonObj

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

open private exists_additiveFibreIso forgetFibrePoint_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private hom_ext_on_affine_tests rootPoint_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private rootPoint_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private root_of_scalar_action from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.NormalizerComparison

variable {k : Type u} [Field k]

private abbrev markedFieldRoot {E : BasedRootDatum.{u}} {M : Model E}
    (F : MarkedFibre M k) (a : E.I) :
    F.line.group ⟶ F.realization.pinned.pair.G.val :=
  (F.coordinate a).val.hom ≫
    (F.realization.pinned.roots (F.realization.datumIso.val.indexEquiv a)).val.inclusion

set_option backward.isDefEq.respectTransparency false in
private theorem markedFieldRoot_eq {E : BasedRootDatum.{u}} {M : Model E}
    (F : MarkedFibre M k) (a : E.I)
    (e : F.line.group ≅ (fibre k).obj M.line.group)
    (he : ∀ (R : TestAlgebra k) (z : R),
      forgetFibrePoint M.line.group R (rootPoint e.hom R z) =
        M.line.point (CommAlgCat.of Specs.IntegralSemisimpleModel.Integers.{u} R) z) :
    markedFieldRoot F a ≫ F.groupIso.inv = e.hom ≫ (fibre k).map (M.root a) := by
  apply Grp.hom_ext
  apply hom_ext_on_affine_tests
  intro R t
  obtain ⟨z, hz⟩ := rootPoint_surjective (Iso.refl F.line.group) R t
  have hz' := rootPoint_comp (𝟙 F.line.group) (markedFieldRoot F a ≫ F.groupIso.inv) R z
  have hz'' := rootPoint_comp (𝟙 F.line.group) (e.hom ≫ (fibre k).map (M.root a)) R z
  simp only [Category.id_comp] at hz' hz''
  change t ≫ (markedFieldRoot F a ≫ F.groupIso.inv).hom.hom =
    t ≫ (e.hom ≫ (fibre k).map (M.root a)).hom.hom
  rw [← hz, Iso.refl_hom, ← hz', ← hz'', rootPoint_comp e.hom]
  apply (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective M.group R).1
  rw [forgetFibrePoint_comp, he]
  simpa only [markedFieldRoot, Category.assoc, markedRootPoint] using F.root_eval a R z

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_action_of_restriction {G H : GroupScheme k}
    {T : ClosedSubgroup G} {S : ClosedSubgroup H}
    (f : G ⟶ H) [Mono f.hom.hom] (e : T.group ≅ S.group)
    (hT : T.inclusion ≫ f = e.hom ≫ S.inclusion)
    {A : AdditiveLine k} (x : A.group ⟶ G) (α : Character S.group)
    (hx : HasScalarAction S α (x ≫ f)) : HasScalarAction T (e.hom ≫ α) x := by
  intro R t a
  let F := IsMonHom.monoidHom f.hom.hom ((testSpec k).obj (Opposite.op R))
  let s : GroupPoints S.group R := t ≫ e.hom.hom.hom
  let g : GroupPoints G R := t ≫ T.inclusion.hom.hom
  have hg : F g = s ≫ S.inclusion.hom.hom := by
    change (t ≫ T.inclusion.hom.hom) ≫ f.hom.hom = (t ≫ e.hom.hom.hom) ≫ S.inclusion.hom.hom
    rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hT]
  have hχ : characterValue (e.hom ≫ α) R t = characterValue α R s := by
    unfold characterValue
    rw [Grp.comp_hom_hom, ← Category.assoc]
  have hroot (z : R) : F (rootPoint x R z) = rootPoint (x ≫ f) R z :=
    (rootPoint_comp x f R z).symm
  apply (cancel_mono f.hom.hom).mp
  change F (g * rootPoint x R a * g⁻¹) = F (rootPoint x R (characterValue _ R t * a))
  rw [map_mul, map_mul, map_inv, hg, hroot, hroot, hχ]
  exact hx R s a

set_option backward.isDefEq.respectTransparency false in
private theorem fieldRootFactors {E : BasedRootDatum.{u}} {M : Model E}
    (F : MarkedFibre M k) {G : GroupScheme k} (f : G ⟶ (fibre k).obj M.group) (a : E.I) :
    (∃ r : (fibre k).obj M.line.group ⟶ G, r ≫ f = (fibre k).map (M.root a)) ↔
      ∃ x : F.line.group ⟶ G, x ≫ f ≫ F.groupIso.hom = markedFieldRoot F a := by
  obtain ⟨e, he⟩ := exists_additiveFibreIso M.line F.line
  have hm := markedFieldRoot_eq F a e he
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨e.hom ≫ r, ?_⟩
    rw [Category.assoc, ← Category.assoc r, hr, ← Category.assoc, ← hm, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · rintro ⟨x, hx⟩
    refine ⟨e.inv ≫ x, ?_⟩
    have h : x ≫ f = markedFieldRoot F a ≫ F.groupIso.inv := by
      apply (cancel_mono F.groupIso.hom).1
      rw [Category.assoc, hx, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Category.assoc, h, hm, Iso.inv_hom_id_assoc]

private abbrev fieldRootCharacter {E : BasedRootDatum.{u}} {M : Model E}
    (F : MarkedFibre M k) (a : E.I) :
    Character F.realization.pinned.pair.T.group :=
  (F.realization.datumIso.val.indexEquiv a).val

set_option backward.isDefEq.respectTransparency false in
private theorem inherited_marked_root {E : BasedRootDatum.{u}} {M : Model E}
    (F : MarkedFibre M k) {G : GroupScheme k}
    (f : G ⟶ F.realization.pinned.pair.G.val) (hf : IsClosedImmersion f.hom.hom.left)
    (T : ClosedSubgroup G) (e : F.realization.pinned.pair.T.group ≅ T.group)
    (he : T.inclusion ≫ f = e.inv ≫ F.realization.pinned.pair.T.inclusion)
    (a : E.I) (x : F.line.group ⟶ G) (hx : x ≫ f = markedFieldRoot F a) :
    ∃ h : IsClosedImmersion x.hom.hom.left,
      IsRootSubgroup T ⟨F.line.group, x, h⟩ (transportCharacter e (fieldRootCharacter F a)) := by
  let S := (F.realization.pinned.roots (F.realization.datumIso.val.indexEquiv a)).val
  let r := (F.coordinate a).val
  haveI : IsClosedImmersion f.hom.hom.left := hf
  haveI : Mono f.hom.hom := Over.mono_of_mono_left _
  haveI : IsClosedImmersion S.inclusion.hom.hom.left := S.isClosedImmersion
  haveI : IsIso r.hom.hom.hom.left :=
    (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso r).isIso_hom
  haveI hcomp : IsClosedImmersion (x.hom.hom.left ≫ f.hom.hom.left) := by
    change IsClosedImmersion (x ≫ f).hom.hom.left
    rw [hx]
    change IsClosedImmersion (r.hom.hom.hom.left ≫ S.inclusion.hom.hom.left)
    infer_instance
  have hclosed := IsClosedImmersion.of_comp_isClosedImmersion x.hom.hom.left f.hom.hom.left
  let U : ClosedSubgroup G := ⟨F.line.group, x, hclosed⟩
  refine ⟨hclosed, root_of_scalar_action U _ (Iso.refl _) ?_ ?_ ?_⟩
  · change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr
        (show Algebra.Smooth k (Polynomial k) from ⟨inferInstance, inferInstance⟩))
  · exact ⟨F.line.operations, F.line.comultiplication, F.line.counit, F.line.antipode, ⟨Iso.refl _⟩⟩
  · rw [Iso.refl_hom, Category.id_comp]
    exact scalar_action_of_restriction f e.symm he x _ (hx ▸ (F.coordinate a).property)

end ResidueRootData

section BorelGeneration

set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelPositivity (RadicalDecomposition)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.OrderedRootProducts (RootSubgroupFamily Enumerates product rootProduct Parametrizes)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)

open private factor_group_through_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
  (U : RootSubgroupFamily T)

private def rootProductIdentity (X : SchemeOver k) :
    (l : List (Root T)) → X ⟶ product (fun i => (U i).val.group.X) l
  | [] => toUnit X
  | i :: l => lift 1 (rootProductIdentity X l)

private theorem rootProductIdentity_apply (X : SchemeOver k) (l : List (Root T)) :
    rootProductIdentity U X l ≫ rootProduct U l = 1 := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons i l ih =>
    simp only [rootProductIdentity, rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      MonObj.one_comp, ih, mul_one]

private theorem rootProduct_factor (l : List (Root T)) (i : Root T) (hi : i ∈ l) :
    ∃ f : (U i).val.group.X ⟶ product (fun j => (U j).val.group.X) l,
      f ≫ rootProduct U l = (U i).val.inclusion.hom.hom := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.mem_cons.1 hi with he | he
    · subst j
      refine ⟨lift (𝟙 _) (rootProductIdentity U _ l), ?_⟩
      simp only [rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        rootProductIdentity_apply, mul_one]
    · obtain ⟨f, hf⟩ := ih he
      refine ⟨lift 1 f, ?_⟩
      simp only [rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        MonObj.one_comp, hf, one_mul]

private theorem subgroupOf_borel_of_parametrizes (B : ClosedSubgroup G.val) (R : ClosedSubgroup B.group)
    (l : List (Root T)) (hprod : Parametrizes U l (R.inclusion.hom.hom ≫ B.inclusion.hom.hom))
    (i : Root T) (hi : i ∈ l) :
    IsSubgroupOf (U i).val B := by
  obtain ⟨e, he⟩ := hprod
  obtain ⟨f, hf⟩ := rootProduct_factor U l i hi
  have heq : (f ≫ e.hom ≫ R.inclusion.hom.hom) ≫ B.inclusion.hom.hom =
      (U i).val.inclusion.hom.hom := by
    simpa only [Category.assoc] using (congrArg (f ≫ ·) he).trans hf
  exact factor_group_through_subgroup B (U i).val.inclusion _ heq

local notation "pt(" G ")" => GroupPoints G (CommAlgCat.of k k)

private theorem rootProduct_mem_subgroup {A : Type u} [Group A] (q : pt(G.val) →* A) (S : Subgroup A)
    (l : List (Root T))
    (hroot : ∀ i ∈ l, ∀ p : pt((U i).val.group), q (p ≫ (U i).val.inclusion.hom.hom) ∈ S)
    (p : Points (product (fun i => (U i).val.group.X) l) (CommAlgCat.of k k)) :
    q (p ≫ rootProduct U l) ∈ S := by
  induction l with
  | nil =>
    change q (p ≫ (1 : 𝟙_ (SchemeOver k) ⟶ G.val.X)) ∈ S
    rw [MonObj.comp_one, map_one]
    exact S.one_mem
  | cons i l ih =>
    rw [rootProduct, MonObj.comp_mul, map_mul, ← Category.assoc p, ← Category.assoc p]
    exact S.mul_mem (hroot i List.mem_cons_self (p ≫ fst _ _))
      (ih (fun j hj => hroot j (List.mem_cons_of_mem _ hj)) (p ≫ snd _ _))

set_option backward.isDefEq.respectTransparency false in
private theorem borel_points_mem_subgroup {A : Type u} [Group A]
    (q : pt(G.val) →* A) (S : Subgroup A) (B : ClosedSubgroup G.val)
    (l : List (Root T)) (hlist : Enumerates l (subgroupRoots T B))
    (hdec : RadicalDecomposition T B)
    (htorus : ∀ t : pt(T.group), q (t ≫ T.inclusion.hom.hom) ∈ S)
    (hroot : ∀ i : Root T, IsSubgroupOf (U i).val B →
      ∀ p : pt((U i).val.group), q (p ≫ (U i).val.inclusion.hom.hom) ∈ S)
    (b : pt(B.group)) : q (b ≫ B.inclusion.hom.hom) ∈ S := by
  obtain ⟨R, j, _, _, _, hj, _, _, hIso, hProd⟩ := hdec
  letI := hIso
  let e := asIso (multiplyFactors j R.inclusion)
  let z := b ≫ e.inv
  have hz : z ≫ multiplyFactors j R.inclusion = b := by
    change (b ≫ e.inv) ≫ e.hom = b
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hg : b ≫ B.inclusion.hom.hom = (z ≫ fst _ _ ≫ T.inclusion.hom.hom) *
      (z ≫ snd _ _ ≫ R.inclusion.hom.hom ≫ B.inclusion.hom.hom) := by
    rw [← hz]
    simp only [multiplyFactors, MonObj.comp_mul, MonObj.mul_comp, Category.assoc]
    rw [← Grp.comp_hom_hom, hj]
  obtain ⟨s, hs⟩ := hProd U l hlist
  let p := z ≫ snd _ _ ≫ s.inv
  have hp : p ≫ rootProduct U l =
      z ≫ snd _ _ ≫ R.inclusion.hom.hom ≫ B.inclusion.hom.hom := by
    change (z ≫ snd _ _ ≫ s.inv) ≫ rootProduct U l = _
    rw [← hs]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hg, ← hp, map_mul]
  exact S.mul_mem (htorus (z ≫ fst _ _))
    (rootProduct_mem_subgroup U q S l (fun i hi =>
      hroot i (subgroupOf_borel_of_parametrizes U B R l ⟨s, hs⟩ i hi)) p)

end BorelGeneration

section MarkedBorelGeneration

universe u

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedRootPoint)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.IntegralSemisimpleModel
  (Model Integers IntegralPoints fibre forgetFibrePoint splitTorus torusPoint TorusValues)
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily)
open Specs.Pinning (BasedRootDatum transportCharacter)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.RootGroups (rootPoint)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra
open private affineTorusPointEquiv forgetFibrePoint_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private rootPoint_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts

variable {k : Type u} [Field k] {E : BasedRootDatum.{u}} {M : Model E}

local notation "pt(" G ")" => GroupPoints G (CommAlgCat.of k k)

private def pointsInIntegralModel {G : GroupScheme k} (f : G ⟶ (fibre k).obj M.group) :
    pt(G) →* IntegralPoints M.group (integralRing k) :=
  (integralFibreHom M.group).comp (fieldPointsHom f)

set_option backward.isDefEq.respectTransparency false in
private theorem pointsInIntegralModel_comp {G H : GroupScheme k}
    (g : G ⟶ H) (f : H ⟶ (fibre k).obj M.group) (b : pt(G)) :
    pointsInIntegralModel (g ≫ f) b = pointsInIntegralModel f (fieldPointsHom g b) := by
  change forgetFibrePoint M.group (CommAlgCat.of k k) (b ≫ (g ≫ f).hom.hom) =
    forgetFibrePoint M.group (CommAlgCat.of k k) ((b ≫ g.hom.hom) ≫ f.hom.hom)
  rw [Grp.comp_hom_hom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem markedFieldRoot_point (F : MarkedFibre M k)
    {G : GroupScheme k} (f : G ⟶ (fibre k).obj M.group)
    (a : E.I) (r : F.line.group ⟶ G) (hr : r ≫ f ≫ F.groupIso.hom = markedFieldRoot F a)
    (p : pt(F.line.group)) :
    ∃ b : k, pointsInIntegralModel f (p ≫ r.hom.hom) =
      markedRootPoint M.toIntegralMarking (integralRing k) a b := by
  obtain ⟨z, hz⟩ := rootPoint_surjective (Iso.refl F.line.group) (CommAlgCat.of k k) p
  refine ⟨z, ?_⟩
  have hrf : r ≫ f = markedFieldRoot F a ≫ F.groupIso.inv := by
    apply (cancel_mono F.groupIso.hom).1
    rw [Category.assoc, hr, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := rootPoint_comp (𝟙 F.line.group) (r ≫ f) (CommAlgCat.of k k) z
  rw [Category.id_comp] at h
  change forgetFibrePoint M.group (CommAlgCat.of k k) ((p ≫ r.hom.hom) ≫ f.hom.hom) = _
  rw [Category.assoc, ← Grp.comp_hom_hom, ← hz, Iso.refl_hom, ← h, hrf]
  simpa only [markedFieldRoot, Category.assoc] using F.root_eval a (CommAlgCat.of k k) z

set_option backward.isDefEq.respectTransparency false in
private theorem markedTorus_point {G : GroupScheme k}
    (f : G ⟶ (fibre k).obj M.group) (T : ClosedSubgroup G)
    (τ : (fibre k).obj (splitTorus E) ≅ T.group)
    (hMark : τ.hom ≫ T.inclusion ≫ f = (fibre k).map M.torus) (p : pt(T.group)) :
    ∃ v : TorusValues E (integralRing k), pointsInIntegralModel f (p ≫ T.inclusion.hom.hom) =
      torusPoint E (integralRing k) v ≫ M.torus.hom.hom := by
  let p' : pt((fibre k).obj (splitTorus E)) := p ≫ τ.inv.hom.hom
  let R := integralRing k
  obtain ⟨v, hv⟩ := (@affineTorusPointEquiv Integers.{u} _ (Multiplicative E.X) _
    R R.commRing R.algebra).surjective (forgetFibrePoint (splitTorus E) (CommAlgCat.of k k) p')
  refine ⟨v, ?_⟩
  have h : τ.inv ≫ (fibre k).map M.torus = T.inclusion ≫ f := by
    rw [← hMark, Iso.inv_hom_id_assoc]
  change forgetFibrePoint M.group (CommAlgCat.of k k) ((p ≫ T.inclusion.hom.hom) ≫ f.hom.hom) = _
  rw [Category.assoc, ← Grp.comp_hom_hom, ← h, Grp.comp_hom_hom, ← Category.assoc, forgetFibrePoint_comp]
  exact congrArg (· ≫ M.torus.hom.hom) hv.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 620000 in
private theorem marked_borel_points_mem
    (F : MarkedFibre M k) (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (f : G.val ⟶ (fibre k).obj M.group) (hf : IsClosedImmersion f.hom.hom.left)
    (T : ClosedSubgroup G.val) (τ : (fibre k).obj (splitTorus E) ≅ T.group)
    (hMark : τ.hom ≫ T.inclusion ≫ f = (fibre k).map M.torus)
    (hSplit : IsSplitTorus T.group) (hMax : IsGeometricallyMaximal T)
    (B : ClosedSubgroup G.val) (hB : IsKBorel B) (hTB : IsSubgroupOf T B)
    (roots positive : Set E.I)
    (hCharacters : CharacterPairing.absoluteRoots T =
      (fun a : E.I => transportCharacter (F.torusIso.symm ≪≫ τ) (fieldRootCharacter F a)) '' roots)
    (hRoot : ∀ a ∈ roots, ∃ r : (fibre k).obj M.line.group ⟶ G.val,
      r ≫ f = (fibre k).map (M.root a))
    (hPositive : ∀ a : E.I, (∃ r : (fibre k).obj M.line.group ⟶ B.group,
      r ≫ B.inclusion ≫ f = (fibre k).map (M.root a)) → a ∈ positive)
    (S : Subgroup (IntegralPoints M.group (integralRing k)))
    (htorus : ∀ v : TorusValues E (integralRing k),
      (torusPoint E (integralRing k) v ≫ M.torus.hom.hom) ∈ S)
    (hroot : ∀ a ∈ positive, ∀ z : k, markedRootPoint M.toIntegralMarking (integralRing k) a z ∈ S)
    (b : pt(B.group)) :
    pointsInIntegralModel f (b ≫ B.inclusion.hom.hom) ∈ S := by
  classical
  let e := F.torusIso.symm ≪≫ τ
  let f' := f ≫ F.groupIso.hom
  haveI : IsClosedImmersion f.hom.hom.left := hf
  haveI : IsIso F.groupIso.hom.hom.hom.left :=
    (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso F.groupIso).isIso_hom
  have hf' : IsClosedImmersion f'.hom.hom.left := by
    change IsClosedImmersion (f.hom.hom.left ≫ F.groupIso.hom.hom.hom.left)
    infer_instance
  have he : T.inclusion ≫ f' = e.inv ≫ F.realization.pinned.pair.T.inclusion := by
    change T.inclusion ≫ f ≫ F.groupIso.hom = (τ.inv ≫ F.torusIso.hom) ≫ _
    apply (cancel_epi τ.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [show (τ.hom ≫ T.inclusion) ≫ f = (fibre k).map M.torus by
      simpa only [Category.assoc] using hMark, F.torus_comm]
  have hidx (α : Root T) : ∃ a ∈ roots, transportCharacter e (fieldRootCharacter F a) = α.val := by
    have h := congrArg (fun s : Set _ => α.val ∈ s) hCharacters
    exact h.mp α.property
  choose a ha hchar using hidx
  have hex (α : Root T) : ∃ r : F.line.group ⟶ G.val, r ≫ f' = markedFieldRoot F (a α) :=
    (fieldRootFactors F f (a α)).1 (hRoot _ (ha α))
  choose r hr using hex
  have hclosed (α : Root T) : ∃ h : IsClosedImmersion (r α).hom.hom.left,
      Specs.RootGroups.IsRootSubgroup T ⟨F.line.group, r α, h⟩ α.val := by
    rw [← hchar α]
    exact inherited_marked_root F f' hf' T e he (a α) (r α) (hr α)
  choose hCls hR using hclosed
  let U : RootSubgroupFamily T := fun α => ⟨⟨F.line.group, r α, hCls α⟩, hR α⟩
  obtain ⟨hComm, hData⟩ := RootData.BorelPositivity.borelPositivity G hG T hSplit hMax
  letI := hComm
  obtain ⟨D, _, _, _, _, hDec⟩ := hData
  letI := D.finiteRoots
  let s := (Set.toFinite (subgroupRoots T B)).toFinset
  let l := s.toList
  have hl : Enumerates l (subgroupRoots T B) :=
    ⟨Finset.nodup_toList _, fun α => by simp [l, s]⟩
  apply borel_points_mem_subgroup U (pointsInIntegralModel f) S B l hl (hDec B hB hTB) _ _ b
  · intro t
    obtain ⟨v, hv⟩ := markedTorus_point f T τ hMark t
    rw [hv]
    exact htorus v
  · intro α hα p
    obtain ⟨j, hj⟩ := hα
    have hPos : a α ∈ positive := by
      apply hPositive
      apply (fieldRootFactors F (B.inclusion ≫ f) (a α)).2
      refine ⟨j, ?_⟩
      have h := (congrArg (· ≫ f') hj).trans (hr α)
      simpa only [f', Category.assoc] using h
    obtain ⟨z, hz⟩ := markedFieldRoot_point F f (a α) (r α) (hr α) p
    change pointsInIntegralModel f (p ≫ (r α).hom.hom) ∈ S
    rw [hz]
    exact hroot (a α) hPos z

end MarkedBorelGeneration

section EqualWeylLabels

universe u

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalIwahoriCongruence (changeRingHom integralRing integralRingMap)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedWeylWord)
open Specs.IntegralSemisimpleModel
  (IntegralGroup IntegralAlgebra Integers IntegralPoints fibre forgetFibrePoint torusPoint
    TorusValues splitTorus Model)
open Specs.Pinning (BasedRootDatum)

open private centralizes_iff_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections
open private fibrePointsEquiv forgetFibrePoint_comp affineTorusPointEquiv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

private theorem forgetFibrePoint_mapPoints {k : Type u} [Field k] (G : IntegralGroup.{u})
    {R S : TestAlgebra k} (f : R ⟶ S) (g : GroupPoints ((fibre k).obj G) R) :
    forgetFibrePoint G S (mapPoints f g) =
      changeRingHom G (integralRingMap f.hom.toRingHom) (forgetFibrePoint G R g) := by
  apply Over.OverMorphism.ext
  exact Category.assoc _ _ _

set_option maxHeartbeats 550000 in
set_option backward.isDefEq.respectTransparency false in
private theorem markedWord_ratio_in_torus {k : Type u} [Field k] {E : BasedRootDatum.{u}}
    {M : Model E} (F : MarkedFibre M k)
    (l l' : List E.I)
    (he : (l.map (RootPairing.weylGroup.ofIdx E.datum)).prod =
      (l'.map (RootPairing.weylGroup.ofIdx E.datum)).prod) :
    ∃ v : TorusValues E (integralRing k),
      (markedWeylWord M.toIntegralMarking (integralRing k) l)⁻¹ *
          markedWeylWord M.toIntegralMarking (integralRing k) l' =
        torusPoint E (integralRing k) v ≫ M.torus.hom.hom := by
  let R₀ := CommAlgCat.of k k
  let P := F.realization.pinned.pair
  let Q := (testSpec k).obj (op R₀)
  let ratio (R : IntegralAlgebra.{u}) :=
    (markedWeylWord M.toIntegralMarking R l)⁻¹ * markedWeylWord M.toIntegralMarking R l'
  obtain ⟨g, hg⟩ := (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective
    M.group R₀).2 (ratio (integralRing k))
  have hcomm (R : IntegralAlgebra.{u}) (v : TorusValues E R) :
      Commute (ratio R) (torusPoint E R v ≫ M.torus.hom.hom) := by
    let a := markedWeylWord M.toIntegralMarking R l
    let b := markedWeylWord M.toIntegralMarking R l'
    let z := torusPoint E R v ≫ M.torus.hom.hom
    have h : a * z * a⁻¹ = b * z * b⁻¹ := by
      change markedWeylWord M.toIntegralMarking R l * z * _ =
        markedWeylWord M.toIntegralMarking R l' * z * _
      rw [markedWeylWord_conjugates_torus, markedWeylWord_conjugates_torus, he]
    change (a⁻¹ * b) * z = z * (a⁻¹ * b)
    calc
      _ = a⁻¹ * (b * z * b⁻¹) * b := by group
      _ = _ := by rw [← h]; group
  let Fpoints (R : TestAlgebra k) :
      GroupPoints P.G.val R →* IntegralPoints M.group (integralRing R) :=
    (fibrePointsEquiv M.group R).toMonoidHom.comp
      (IsMonHom.monoidHom F.groupIso.inv.hom.hom ((testSpec k).obj (op R)))
  have hInjective (R : TestAlgebra k) : Function.Injective (Fpoints R) := by
    haveI := ((Grp.forget (SchemeOver k)).mapIso F.groupIso).isIso_inv
    exact (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective M.group R).1.comp
      (fun _ _ h => (cancel_mono F.groupIso.inv.hom.hom).mp h)
  have hTor (R : TestAlgebra k) (t : GroupPoints P.T.group R) :
      ∃ v : TorusValues E (integralRing R),
        Fpoints R (t ≫ P.T.inclusion.hom.hom) =
          torusPoint E (integralRing R) v ≫ M.torus.hom.hom := by
    let tr : GroupPoints ((fibre k).obj (splitTorus E)) R := t ≫ F.torusIso.inv.hom.hom
    obtain ⟨v, hv⟩ := (@affineTorusPointEquiv Integers.{u} _ (Multiplicative E.X) _
      (integralRing R) (integralRing R).commRing (integralRing R).algebra).surjective
        (forgetFibrePoint (splitTorus E) R tr)
    have hdiagram : F.torusIso.inv ≫ (fibre k).map M.torus =
        P.T.inclusion ≫ F.groupIso.inv := by
      apply (cancel_mono F.groupIso.hom).1
      rw [Category.assoc, Category.assoc, F.torus_comm,
        Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    refine ⟨v, ?_⟩
    change forgetFibrePoint M.group R ((t ≫ P.T.inclusion.hom.hom) ≫ F.groupIso.inv.hom.hom) = _
    rw [Category.assoc, ← show F.torusIso.inv.hom.hom ≫ ((fibre k).map M.torus).hom.hom =
        P.T.inclusion.hom.hom ≫ F.groupIso.inv.hom.hom from congrArg (fun f => f.hom.hom) hdiagram,
      ← Category.assoc, forgetFibrePoint_comp]
    exact congrArg (· ≫ M.torus.hom.hom) hv.symm
  have hiHom : F.groupIso.hom.hom.hom ≫ F.groupIso.inv.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) F.groupIso.hom_inv_id
  let p : GroupPoints P.G.val R₀ := g ≫ F.groupIso.hom.hom.hom
  have hCent : Centralizes P.T.inclusion p := by
    apply (centralizes_iff_affine _ _).mpr
    intro R t z
    let f : R₀ ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have ht : t = (testSpec k).map f.op := by
      haveI := (groundIso (k := k)).isIso_hom
      apply (cancel_mono (groundIso (k := k)).hom).mp
      exact toUnit_unique _ _
    obtain ⟨v, hv⟩ := hTor R z
    have hp : Fpoints R (t ≫ p) = ratio (integralRing R) := by
      change forgetFibrePoint M.group R ((t ≫ p) ≫ F.groupIso.inv.hom.hom) = _
      have hcomp : (t ≫ p) ≫ F.groupIso.inv.hom.hom = t ≫ g := by
        dsimp only [p]
        simp only [Category.assoc, hiHom, Category.comp_id]
      rw [hcomp, ht]
      change forgetFibrePoint M.group R (mapPoints f g) = _
      rw [forgetFibrePoint_mapPoints, hg]
      simp only [ratio, map_mul, map_inv]
      exact congrArg₂ (fun a b => a⁻¹ * b)
        (markedWeylWord_map M.toIntegralMarking (integralRingMap f.hom.toRingHom) l)
        (markedWeylWord_map M.toIntegralMarking (integralRingMap f.hom.toRingHom) l')
    let a : GroupPoints P.G.val R := t ≫ p
    let b : GroupPoints P.G.val R := z ≫ P.T.inclusion.hom.hom
    change a * b = b * a
    apply hInjective R
    have ha : Fpoints R a = ratio (integralRing R) := hp
    have hb : Fpoints R b = torusPoint E (integralRing R) v ≫ M.torus.hom.hom := hv
    rw [map_mul, map_mul, ha, hb]
    exact (hcomm _ _).eq
  obtain ⟨t, ht⟩ := (Reductive.TorusCentralizer.maximalTorusCentralizer P.G P.reductive
    P.T (isTorus_of_split P.split) P.maximal Q p).mp hCent
  obtain ⟨v, hv⟩ := hTor R₀ t
  have hp : Fpoints R₀ p = ratio (integralRing k) := by
    change forgetFibrePoint M.group R₀ ((g ≫ F.groupIso.hom.hom.hom) ≫ F.groupIso.inv.hom.hom) = _
    simpa only [Category.assoc, hiHom, Category.comp_id] using hg
  exact ⟨v, hp.symm.trans ((congrArg (Fpoints R₀) ht).symm.trans hv)⟩

end EqualWeylLabels

section FaceLiftResidue

universe u

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj WithZero
open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel residue)
open Specs.ExceptionalAffineBuilding (Weights cotype standardWallSubgroup SplitBuildingLevel)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalIwahoriCongruence
  (integralRing localIntegers localIntegersInclusion residueHom changeRingHom)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedWeylWord)
open Specs.IntegralSemisimpleModel (Model IntegralPoints fibre TorusValues splitTorus torusPoint)
open Specs.Pinning (BasedRootDatum)

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

local notation "A" => ApartmentRoots.split E.datum ℚ
local notation "k" => residue L

set_option backward.isDefEq.respectTransparency false in
/-- The scaled residue of the actual face lift is the signed surviving word
of the same finite label, with a marked torus factor on each side. -/
private theorem scaled_face_lift_residue_word
    (B : SplitBuildingLevel Y) (t : Weights ((A).SimpleWall p')) (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    {d : ℕ} (hd : 0 < d) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hπ : normalizedValuation K (π : K) = WithZero.exp (-1 : ℤ))
    (hξ : (ξ : L) ^ d = algebraMap K L (π : K))
    (F : MarkedFibre M' k)
    (w : standardWallSubgroup Y.ad.coxeter.coxeter (cotype t))
    (u : IntegralPoints M'.group (localIntegers L))
    (hu : changeRingHom M'.group (localIntegersInclusion L) u =
      conjugatedScalarPoints M' y ξ (Y.ad.lift w.val : FieldPoints M' K)) :
    ∃ l : List E.I, (∀ a ∈ l, ∃ j : ℤ, (A).root a x = j) ∧
      (l.map (RootPairing.weylGroup.ofIdx E.datum)).prod =
        Y.ad.localIwahori.normalizer.label (Y.ad.lift w.val) ∧
      ∃ v₁ v₂ : TorusValues E (integralRing k),
        changeRingHom M'.group (residueHom (localIntegers L)) u =
          (torusPoint E (integralRing k) v₁ ≫ M'.torus.hom.hom) *
            (markedWeylWord M'.toIntegralMarking (integralRing k) l *
              (torusPoint E (integralRing k) v₂ ≫ M'.torus.hom.hom)) := by
  let N := Y.ad.localIwahori.normalizer
  let n := Y.ad.lift w.val
  let l := N.word (N.label n)
  obtain ⟨v, hv⟩ := scaled_face_lift_integral B t x hx hd y hy hπ hξ w
  have hv' : u =
      (torusPoint E (localIntegers L) v ≫ M'.torus.hom.hom) *
        markedWeylWord M'.toIntegralMarking (localIntegers L) l :=
    changeRingHom_injective M' (localIntegersInclusion L)
      (fun a b h => Subtype.ext h) (hu.trans hv.symm)
  obtain ⟨l', hsurvives, hl'⟩ := surviving_face_word B t x hx w
  obtain ⟨_, hlabels, _⟩ := Y.ad_points
  obtain ⟨_, _, _, hword⟩ := hlabels
  obtain ⟨v', hratio⟩ := markedWord_ratio_in_torus F l' l (hl'.trans (hword (N.label n)).symm)
  have hw : markedWeylWord M'.toIntegralMarking (integralRing k) l =
      markedWeylWord M'.toIntegralMarking (integralRing k) l' * (torusPoint E (integralRing k) v' ≫ M'.torus.hom.hom) := by
    rw [← hratio]
    group
  let v₀ : TorusValues E (integralRing k) :=
    (Units.map (residueHom (localIntegers L)).hom.toMonoidHom).comp v
  refine ⟨l', hsurvives, hl', v₀, v', ?_⟩
  rw [hv', map_mul, map_torusPoint_in_group, markedWeylWord_map]
  change (torusPoint E (integralRing k) v₀ ≫ M'.torus.hom.hom) *
    markedWeylWord M'.toIntegralMarking (integralRing k) l = _
  rw [hw]

end FaceLiftResidue

section ParahoricPointMaps

universe u

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.MonoidalCategory WithZero
open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BruhatOrbitParametrization (IsRepresentative)
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel residue)
open Specs.ExceptionalAffineBuilding (Weights cotype parahoric standardWallSubgroup SplitBuildingLevel)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalIwahoriCongruence
  (integralRing localIntegers localIntegersInclusion residueHom changeRingHom)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation residueMap)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedWeylWord)
open Specs.ExceptionalParahoricPointReduction (PointReduction SplitParahoricPointReduction)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.IntegralSemisimpleModel (Model IntegralPoints fibre forgetFibrePoint splitTorus torusPoint)
open Specs.Pinning (BasedRootDatum transportCharacter)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

local notation "A" => ApartmentRoots.split E.datum ℚ
local notation "k" => residue L
local notation "pt(" G ")" => GroupPoints G (CommAlgCat.of k k)

set_option backward.isDefEq.respectTransparency false in
private theorem iwahori_le_parahoric (t : Weights ((A).SimpleWall p')) :
    Y.ad.I ≤ parahoric Y.ad (cotype t) :=
  fun _ hg => Subgroup.subset_closure (Or.inl hg)

set_option backward.isDefEq.respectTransparency false in
private def faceLiftPoint (B : SplitBuildingLevel Y) (t : Weights ((A).SimpleWall p'))
    (w : standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)) :
    parahoric Y.ad (cotype t) :=
  ⟨Y.ad.lift w.val, by
    have h := B.ad.realization.face_union (cotype t)
    change (Y.ad.lift w.val : FieldPoints M' K) ∈
      (parahoric Y.ad (cotype t) : Set (FieldPoints M' K))
    rw [h]
    exact Set.mem_iUnion.2 ⟨w, DoubleCoset.mem_doubleCoset_self Y.ad.I Y.ad.I _⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem face_point_decomposition
    (B : SplitBuildingLevel Y) (t : Weights ((A).SimpleWall p'))
    (g : parahoric Y.ad (cotype t)) :
    ∃ (a b : (Y.ad.I.subgroupOf (parahoric Y.ad (cotype t))))
      (w : standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)),
      g = a.val * faceLiftPoint B t w * b.val := by
  have hg : (g : FieldPoints M' K) ∈
      ⋃ w : standardWallSubgroup Y.ad.coxeter.coxeter (cotype t),
        DoubleCoset.doubleCoset (Y.ad.lift w.val : FieldPoints M' K) Y.ad.I Y.ad.I :=
    (B.ad.realization.face_union (cotype t)) ▸ g.property
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg
  obtain ⟨a, ha, b, hb, h⟩ := DoubleCoset.mem_doubleCoset.1 hw
  exact ⟨⟨⟨a, iwahori_le_parahoric t ha⟩, ha⟩, ⟨⟨b, iwahori_le_parahoric t hb⟩, hb⟩, w,
    Subtype.ext h⟩

set_option backward.isDefEq.respectTransparency false in
private theorem faceLiftPoint_one_mem_iwahori (B : SplitBuildingLevel Y)
    (t : Weights ((A).SimpleWall p')) :
    (faceLiftPoint B t 1 : FieldPoints M' K) ∈ Y.ad.I := by
  let n := Y.ad.lift (1 : (A).affineWeylGroup)
  have hn : n ∈ Y.ad.affine.ker := MonoidHom.mem_ker.mpr (Y.ad.lift_label 1)
  have hKernel : Y.ad.affine.ker.map Y.ad.N.subtype = Y.ad.T₀ := Y.ad.kernel
  have ht : (n : FieldPoints M' K) ∈ Y.ad.T₀ := by
    rw [← hKernel]
    exact ⟨n, hn, rfl⟩
  rw [← B.ad.iwahori_inter_normalizer] at ht
  exact ht.1

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
/-- The scaled face lifts give representatives for the rational Bruhat
decomposition of the marked residue group, up to the residue torus. -/
private theorem faceResidueBruhat
    (B : SplitBuildingLevel Y) (t : Weights ((A).SimpleWall p')) (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    {d : ℕ} (hd : 0 < d) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hπ : normalizedValuation K (π : K) = WithZero.exp (-1 : ℤ))
    (hξ : (ξ : L) ^ d = algebraMap K L (π : K))
    (F : MarkedFibre M' k)
    (G : AffineAlgebraicGroup k) (hRed : IsReductive G)
    (i : G.val ⟶ (fibre k).obj M'.group) (hi : IsClosedImmersion i.hom.hom.left)
    (T : ClosedSubgroup G.val) (τ : (fibre k).obj (splitTorus E) ≅ T.group)
    (hMark : τ.hom ≫ T.inclusion ≫ i = (fibre k).map M'.torus)
    (hSplit : IsSplitTorus T.group) (hMax : IsGeometricallyMaximal T)
    (hCharacters : CharacterPairing.absoluteRoots T =
      (fun a : E.I => transportCharacter (F.torusIso.symm ≪≫ τ) (fieldRootCharacter F a)) ''
        {a | ∃ j : ℤ, (A).root a x = j})
    (hRoot : ∀ a : E.I, (∃ j : ℤ, (A).root a x = j) →
      ∃ r : (fibre k).obj M'.line.group ⟶ G.val, r ≫ i = (fibre k).map (M'.root a))
    (Bψ : ClosedSubgroup G.val) (hBorel : IsKBorel Bψ) (hBT : IsSubgroupOf T Bψ)
    (f : parahoric Y.ad (cotype t) →* IntegralPoints M'.group (localIntegers L))
    (hf : ∀ g, changeRingHom M'.group (localIntegersInclusion L) (f g) =
      conjugatedScalarPoints M' y ξ (g : FieldPoints M' K)) :
    let W := standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)
    let B₀ := (fieldPointsHom Bψ.inclusion).range
    ∃ m : W → pt(G.val),
      (∀ w, changeRingHom M'.group (residueHom (localIntegers L)) (f (faceLiftPoint B t w)) =
        pointsInIntegralModel i (m w)) ∧
      (∀ g : pt(G.val), ∃ a b : B₀, ∃ w : W, g = a.val * m w * b.val) ∧
      ∀ w, m w ∈ B₀ → w = 1 := by
  classical
  let W := standardWallSubgroup Y.ad.coxeter.coxeter (cotype t)
  let S : Set E.I := {a | ∃ j : ℤ, (A).root a x = j}
  let bPoint := fieldPointsHom Bψ.inclusion
  let B₀ := bPoint.range
  let j := pointsInIntegralModel i
  let R := CommAlgCat.of k k
  let Y₀ := (testSpec k).obj (Opposite.op R)
  obtain ⟨hComm, D₀, J, hBruhat⟩ :=
    ExceptionalParahoricRationalBruhat.rationalBruhat G hRed T Bψ hSplit hMax hBorel hBT
  letI := hComm
  have hOpp (a : E.I) (ha : a ∈ S) : E.datum.reflectionPerm a a ∈ S := by
    obtain ⟨z, hz⟩ := ha
    refine ⟨-z, ?_⟩
    change (A).root (oppositeRoot a) x = ((-z : ℤ) : ℚ)
    rw [opposite_root_value, hz, Int.cast_neg]
  obtain ⟨θ, _, hWord⟩ :=
    ExceptionalParahoricResidueWeyl.markedResidueWeylComparison M' F G hRed T hSplit hMax i hi τ
      hMark S hOpp hCharacters.symm hRoot D₀ J
  let φ := faceFiniteWeylEquiv B t x hx
  let e := φ.trans θ
  obtain ⟨tB, htB⟩ := hBT
  have hTorus : (τ.hom ≫ tB) ≫ (Bψ.inclusion ≫ i) = (fibre k).map M'.torus := by
    rw [Category.assoc, ← Category.assoc tB Bψ.inclusion i, htB]
    exact hMark
  let point (n : 𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X) : pt(G.val) :=
    toUnit Y₀ ≫ n ≫ J.normalizer.inclusion.hom.hom
  have hLift (w : W) : ∃ (n : 𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X) (a b : B₀),
      IsRepresentative J (e w) n ∧
      changeRingHom M'.group (residueHom (localIntegers L)) (f (faceLiftPoint B t w)) =
        j (a.val * point n * b.val) := by
    obtain ⟨l, hl, hLabel, v₁, v₂, hr⟩ :=
      scaled_face_lift_residue_word B t x hx hd y hy hπ hξ F w _ (hf (faceLiftPoint B t w))
    have hφ : (φ w).val = (l.map (RootPairing.weylGroup.ofIdx E.datum)).prod :=
      (faceFiniteWeylEquiv_val B t x hx w).trans hLabel.symm
    obtain ⟨n, hn, hp⟩ := hWord l hl (φ w) hφ
    obtain ⟨a, ha⟩ := torusPoint_mem_range M' (Bψ.inclusion ≫ i) v₁ ⟨_, hTorus⟩
    obtain ⟨b, hb⟩ := torusPoint_mem_range M' (Bψ.inclusion ≫ i) v₂ ⟨_, hTorus⟩
    refine ⟨n, ⟨bPoint a, ⟨a, rfl⟩⟩, ⟨bPoint b, ⟨b, rfl⟩⟩, hn, ?_⟩
    have ha' : j (bPoint a) = torusPoint E (integralRing k) v₁ ≫ M'.torus.hom.hom :=
      (pointsInIntegralModel_comp Bψ.inclusion i a).symm.trans ha
    have hb' : j (bPoint b) = torusPoint E (integralRing k) v₂ ≫ M'.torus.hom.hom :=
      (pointsInIntegralModel_comp Bψ.inclusion i b).symm.trans hb
    have hp' : j (point n) = markedWeylWord M'.toIntegralMarking (integralRing k) l := by
      change forgetFibrePoint M'.group R ((toUnit Y₀ ≫ n ≫ J.normalizer.inclusion.hom.hom) ≫
        i.hom.hom) = _
      simpa only [Category.assoc] using hp
    change _ = j (bPoint a * point n * bPoint b)
    rw [map_mul, map_mul, ha', hb', hp', mul_assoc]
    exact hr
  choose n left right hn hred using hLift
  let representatives (v : D₀.rootDatum.weylGroup) := n (e.symm v)
  have hRep (v : D₀.rootDatum.weylGroup) : IsRepresentative J v (representatives v) := by
    simpa only [representatives, e.apply_symm_apply] using hn (e.symm v)
  obtain ⟨hCover, hIdentity⟩ := hBruhat representatives hRep
  let m (w : W) := (left w).val * point (n w) * (right w).val
  refine ⟨m, hred, ?_, ?_⟩
  · intro g
    obtain ⟨v, a, b, hv⟩ := hCover g
    let w := e.symm v
    let a' : B₀ := ⟨bPoint a, ⟨a, rfl⟩⟩
    let b' : B₀ := ⟨bPoint b, ⟨b, rfl⟩⟩
    have hg : g = a'.val * point (n w) * b'.val := hv
    refine ⟨a' * (left w)⁻¹, (right w)⁻¹ * b', w, ?_⟩
    change g = (a'.val * (left w).val⁻¹) *
      ((left w).val * point (n w) * (right w).val) * ((right w).val⁻¹ * b'.val)
    rw [hg]
    group
  · intro w hw
    have hPoint : point (n w) ∈ B₀ := by
      have h : point (n w) = (left w).val⁻¹ * m w * (right w).val⁻¹ := by
        dsimp only [m]
        group
      rw [h]
      exact B₀.mul_mem (B₀.mul_mem (B₀.inv_mem (left w).property) hw) (B₀.inv_mem (right w).property)
    have hB : ∃ b : pt(Bψ.group), b ≫ Bψ.inclusion.hom.hom = point (representatives (e w)) := by
      obtain ⟨b, hb⟩ := hPoint
      change b ≫ Bψ.inclusion.hom.hom = point (n w) at hb
      exact ⟨b, by simpa only [representatives, e.symm_apply_apply] using hb⟩
    have hOne : e w = 1 := (hIdentity (e w)).mp hB
    exact e.injective (hOne.trans (map_one e).symm)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1150000 in
private theorem parahoricPointReduction
    (B : SplitBuildingLevel Y) (t : Weights ((A).SimpleWall p')) (x : ℚ ⊗[ℤ] E.Y)
    (hx : Specs.ExceptionalAffineBuilding.rationalPoint B.ad.realization.coordinates x =
      Specs.ExceptionalAffineBuilding.simplexPoint B.ad.realization.coordinates
        B.ad.realization.vertex t)
    {d : ℕ} (hd : 0 < d) (y : E.Y) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    {π : Kˣ} {ξ : Lˣ} (hπ : normalizedValuation K (π : K) = WithZero.exp (-1 : ℤ))
    (hξ : (ξ : L) ^ d = algebraMap K L (π : K))
    (hres : Function.Surjective (residueMap K L))
    (F : MarkedFibre M' k)
    (C : ClosedSubgroup ((fibre k).obj M'.group)) (H : ClosedSubgroup C.group)
    (hAff : IsAffine H.group.X.left) (hLft : LocallyOfFiniteType H.group.X.hom)
    (hQc : QuasiCompact H.group.X.hom)
    (hRed : IsReductive ⟨H.group, hAff, hLft, hQc⟩)
    (T : ClosedSubgroup H.group) (τ : (fibre k).obj (splitTorus E) ≅ T.group)
    (hMark : τ.hom ≫ T.inclusion ≫ H.inclusion ≫ C.inclusion = (fibre k).map M'.torus)
    (hSplit : IsSplitTorus T.group) (hMax : IsGeometricallyMaximal T)
    (hCharacters : CharacterPairing.absoluteRoots T =
      (fun a : E.I => transportCharacter (F.torusIso.symm ≪≫ τ) (fieldRootCharacter F a)) ''
        {a | ∃ j : ℤ, (A).root a x = j})
    (hRoot : ∀ a, (∃ r : (fibre k).obj M'.line.group ⟶ H.group,
      r ≫ H.inclusion ≫ C.inclusion = (fibre k).map (M'.root a)) ↔
        ∃ j : ℤ, (A).root a x = j)
    (Bψ : ClosedSubgroup H.group) (hBorel : IsKBorel Bψ) (hBT : IsSubgroupOf T Bψ)
    (hBorelRoot : ∀ a, (∃ r : (fibre k).obj M'.line.group ⟶ Bψ.group,
      r ≫ Bψ.inclusion ≫ H.inclusion ≫ C.inclusion = (fibre k).map (M'.root a)) ↔
        ∃ j : ℤ, (A).root a x = j ∧ (A).positive p' (a, -j)) :
    Nonempty (PointReduction (Y := Y) t y L ξ C H Bψ) := by
  classical
  let P := parahoric Y.ad (cotype t)
  let G : AffineAlgebraicGroup k := ⟨H.group, hAff, hLft, hQc⟩
  let i := H.inclusion ≫ C.inclusion
  let j := pointsInIntegralModel i
  let I := Y.ad.I.subgroupOf P
  let bPoint := fieldPointsHom Bψ.inclusion
  let B₀ := bPoint.range
  let red := changeRingHom M'.group (residueHom (localIntegers L))
  have hj : Function.Injective j :=
    (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective M'.group
      (CommAlgCat.of k k)).1.comp
      ((fieldSubgroupPoints_injective C).comp (fieldSubgroupPoints_injective H))
  haveI : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedImmersion
  haveI : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  have hi : IsClosedImmersion i.hom.hom.left := by
    change IsClosedImmersion (H.inclusion.hom.hom.left ≫ C.inclusion.hom.hom.left)
    infer_instance
  have hIP : Y.ad.I ≤ P := fun g hg => Subgroup.subset_closure (Or.inl hg)
  have ht : τ.hom ≫ T.inclusion ≫ i = (fibre k).map M'.torus := hMark
  obtain ⟨tB, htB⟩ := hBT
  have hTB : (τ.hom ≫ tB) ≫ (Bψ.inclusion ≫ i) = (fibre k).map M'.torus := by
    rw [Category.assoc, ← Category.assoc tB Bψ.inclusion i, htB]
    exact ht
  obtain ⟨f, hf, _⟩ := scaled_parahoric_integral B t x hx hd y hy hπ hξ
  let r := red.comp f
  have hIB (g : P) (hg : (g : FieldPoints M' K) ∈ Y.ad.I) :
      r g ∈ (pointsInIntegralModel (Bψ.inclusion ≫ i)).range :=
    scaled_iwahori_residue_mem B t x hx hd y hy hπ hξ _ ⟨_, hTB⟩
      (fun a ha => (hBorelRoot a).2 ha) g hg (f g) (hf g)
  have liftPoint (g : FieldPoints M' K) (hg : g ∈ Y.ad.I)
      (u : IntegralPoints M'.group (localIntegers L))
      (hu : changeRingHom M'.group (localIntegersInclusion L) u = conjugatedScalarPoints M' y ξ g) :
      red u ∈ I.map r := by
    let g' : P := ⟨g, hIP hg⟩
    refine ⟨g', hg, ?_⟩
    change red (f g') = red u
    exact congrArg red (changeRingHom_injective M' (localIntegersInclusion L)
      Subtype.val_injective ((hf g').trans hu.symm))
  have hBI (b : pt(Bψ.group)) : pointsInIntegralModel (Bψ.inclusion ≫ i) b ∈ I.map r :=
    marked_borel_points_mem F G hRed i hi T τ ht hSplit hMax Bψ hBorel ⟨tB, htB⟩
      {a | ∃ j : ℤ, (A).root a x = j}
      {a | ∃ j : ℤ, (A).root a x = j ∧ (A).positive p' (a, -j)}
      hCharacters (fun a ha => (hRoot a).2 ha) (fun a ha => (hBorelRoot a).1 ha) (I.map r)
      (fun v => by
        obtain ⟨g, hg, u, hu, hr⟩ := lift_iwahori_torus_point (Y := Y) hres y ξ v
        exact hr ▸ liftPoint g hg u hu)
      (fun a ha z => by
        obtain ⟨g, hg, u, hu, hr⟩ := lift_iwahori_root_point B t x hx hres y hy hπ hξ a ha z
        exact hr ▸ liftPoint g hg u hu) b
  have hIwahori : I.map r = B₀.map j := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨b, hb⟩ := hIB g hg
      exact ⟨bPoint b, ⟨b, rfl⟩, (pointsInIntegralModel_comp Bψ.inclusion i b).symm.trans hb⟩
    · rintro _ ⟨g, ⟨b, rfl⟩, rfl⟩
      exact (pointsInIntegralModel_comp Bψ.inclusion i b) ▸ hBI b
  obtain ⟨m, hm, hCover, hIdentity⟩ :=
    faceResidueBruhat B t x hx hd y hy hπ hξ F G hRed i hi T τ ht hSplit hMax hCharacters
      (fun a ha => (hRoot a).2 ha) Bψ hBorel ⟨tB, htB⟩ f hf
  obtain ⟨q, hq, hSurj, hPreimage, hImage⟩ :=
    reductionOfDoubleCosets I B₀ r j hj (faceLiftPoint B t) m hIwahori hm
      (face_point_decomposition B t) hCover
      (fun w hw => by rw [hIdentity w hw]; exact faceLiftPoint_one_mem_iwahori B t)
  letI : Finite k :=
    IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation L
  obtain ⟨Q, hFlags, hFibres⟩ := borelFlagPresentation G Bψ hBorel
  refine ⟨{
    integral := f
    scale := hf
    reduction := q
    reduction_eq := ?_
    reduction_surjective := hSurj
    preimage_borel := hPreimage
    iwahori_image := ?_
    flags := Q
    flag_surjective := hFlags
    flag_fibres := hFibres
  }⟩
  · intro g
    have h := hq g
    change forgetFibrePoint M'.group (CommAlgCat.of k k)
      (q g ≫ (H.inclusion ≫ C.inclusion).hom.hom) =
        changeRingHom M'.group (residueHom (localIntegers L)) (f g) at h
    simpa only [Grp.comp_hom_hom, Category.assoc] using h
  · intro b
    have hb : bPoint b ∈ I.map q := by
      rw [hImage]
      exact ⟨b, rfl⟩
    obtain ⟨g, hg, h⟩ := hb
    exact ⟨g, hg, h⟩

/-- Reduction of the parahoric at the specified uniformizer root, with the
Iwahori and the rational flags of the given marked residue Borel. -/
theorem splitParahoricPointReduction : SplitParahoricPointReduction.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y B t x hx d y hd hy π hπ L _ _ _ _ _ _ _ ξ hξ hres
  dsimp only
  intro C H hAff hLft hQc hRed T τ hMark hSplit hMax F hCharacters hRoot Bψ hBorel hBT hBorelRoot
  exact parahoricPointReduction B t x hx hd y hy hπ hξ hres.2 F C H hAff hLft hQc hRed
    T τ hMark hSplit hMax hCharacters hRoot Bψ hBorel hBT hBorelRoot

end ParahoricPointMaps

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricPointReduction
