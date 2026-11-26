import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuaternionSpinScaleCover
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.Etale.Descent
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
namespace LinearAlgebraicGroups.Arithmetic.QuaternionSpinScaleCover

open CliffordAlgebra
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Albert
open private exteriorImplementer exteriorUnit exterior_implementer_action
  exterior_implementer_even exterior_implementer_norm unitConj from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

noncomputable section

universe u v

private abbrev splitExteriorEquiv (R : Type u) [CommRing R] (m : ℕ) :
    SplitClifford R m ≃ₐ[R] Module.End R (ExteriorAlgebra R (CreationSpace R m)) :=
  CliffordModel.hyperbolicEquiv (Pi.basisFun R (Fin m))

private theorem split_scalar_injective (R : Type u) [CommRing R] (m : ℕ) :
    Function.Injective (algebraMap R (SplitClifford R m)) := by
  intro a b h
  have h' := congrArg (fun z : SplitClifford R m => splitExteriorEquiv R m z 1) h
  change splitExteriorEquiv R m (algebraMap R (SplitClifford R m) a) 1 =
    splitExteriorEquiv R m (algebraMap R (SplitClifford R m) b) 1 at h'
  rw [AlgEquiv.commutes, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h'
  exact (ExteriorAlgebra.algebraMap_leftInverse (CreationSpace R m)).injective
    (by simpa only [Algebra.algebraMap_eq_smul_one] using h')

private def splitScalar (R : Type u) [CommRing R] (m : ℕ) : Rˣ →* (SplitClifford R m)ˣ :=
  Units.map (algebraMap R _).toMonoidHom

private theorem exteriorImplementer_value {R : Type u} [CommRing R] {m : ℕ}
    (t : CreationSpace R m ≃ₗ[R] CreationSpace R m) :
    splitExteriorEquiv R m (exteriorImplementer t).val =
      (ExteriorAlgebra.map t.toLinearMap).toLinearMap :=
  (splitExteriorEquiv R m).apply_symm_apply _

private theorem exteriorImplementer_mul {R : Type u} [CommRing R] {m : ℕ}
    (t w : CreationSpace R m ≃ₗ[R] CreationSpace R m) :
    exteriorImplementer (t * w) = exteriorImplementer t * exteriorImplementer w := by
  apply Units.ext
  apply (splitExteriorEquiv R m).injective
  rw [Units.val_mul, map_mul]
  rw [exteriorImplementer_value, exteriorImplementer_value, exteriorImplementer_value]
  apply LinearMap.ext
  intro x
  change ExteriorAlgebra.map (t.toLinearMap.comp w.toLinearMap) x =
    ExteriorAlgebra.map t.toLinearMap (ExteriorAlgebra.map w.toLinearMap x)
  rw [← ExteriorAlgebra.map_comp_map]
  rfl

private theorem exteriorImplementer_one (R : Type u) [CommRing R] (m : ℕ) :
    exteriorImplementer (1 : CreationSpace R m ≃ₗ[R] CreationSpace R m) = 1 := by
  apply Units.ext
  apply (splitExteriorEquiv R m).injective
  rw [Units.val_one, map_one, exteriorImplementer_value]
  change (ExteriorAlgebra.map (LinearMap.id : Module.End R (CreationSpace R m))).toLinearMap = 1
  rw [ExteriorAlgebra.map_id]
  rfl

private def normalizedExteriorLift (R : Type u) [CommRing R] (m : ℕ) :
    ((CreationSpace R m ≃ₗ[R] CreationSpace R m) × Rˣ) →* (SplitClifford R m)ˣ where
  toFun p := splitScalar R m p.2⁻¹ * exteriorImplementer p.1
  map_one' := by simp [exteriorImplementer_one]
  map_mul' p p' := by
    change splitScalar R m (p.2 * p'.2)⁻¹ * exteriorImplementer (p.1 * p'.1) = _
    rw [mul_inv_rev, mul_comm p'.2⁻¹ p.2⁻¹, map_mul, exteriorImplementer_mul]
    have h : Commute (splitScalar R m p'.2⁻¹) (exteriorImplementer p.1) := by
      apply Units.val_injective
      exact Algebra.commutes (↑p'.2⁻¹ : R) (exteriorImplementer p.1).val
    change _ = (splitScalar R m p.2⁻¹ * exteriorImplementer p.1) *
      (splitScalar R m p'.2⁻¹ * exteriorImplementer p'.1)
    simpa only [mul_assoc] using congrArg
      (fun z => splitScalar R m p.2⁻¹ * z * exteriorImplementer p'.1) h.eq

private theorem implementer_intertwines {R : Type u} [CommRing R] {m : ℕ}
    (t : CreationSpace R m ≃ₗ[R] CreationSpace R m)
    (x : Module.Dual R (CreationSpace R m) × CreationSpace R m) :
    (exteriorImplementer t).val * ι _ x =
      ι _ (splitScaleAction t x) * (exteriorImplementer t).val := by
  have he := exterior_implementer_action t x.1 x.2
  simpa [unitConj, splitScaleAction, mul_assoc] using
    congrArg (fun z => z * (exteriorImplementer t).val) he

private theorem scalar_unit_of_commutes {R : Type u} [CommRing R] {m : ℕ}
    (a : (SplitClifford R m)ˣ)
    (ha : ∀ x, Commute a.val (ι (QuadraticForm.dualProd R (CreationSpace R m)) x)) :
    ∃ r : Rˣ, a = splitScalar R m r := by
  obtain ⟨r, hr⟩ := (CliffordModel.hyperbolic_scalar_centralizer (Pi.basisFun R (Fin m)) _).mp ha
  have ha' : ∀ x, Commute (↑a⁻¹ : SplitClifford R m)
      (ι (QuadraticForm.dualProd R (CreationSpace R m)) x) := fun x => (ha x).units_inv_left
  obtain ⟨s, hs⟩ := (CliffordModel.hyperbolic_scalar_centralizer (Pi.basisFun R (Fin m)) _).mp ha'
  have hrs : r * s = 1 := by
    apply split_scalar_injective R m
    rw [map_mul, ← hr, ← hs, Units.mul_inv, map_one]
  let r' : Rˣ := ⟨r, s, hrs, (mul_comm s r).trans hrs⟩
  exact ⟨r', Units.ext hr⟩

set_option maxHeartbeats 1200000 in
private theorem splitExteriorScaleCover_proof : SplitExteriorScaleCover.{u} := by
  intro R _ m
  let e := splitExteriorEquiv R m
  let L := normalizedExteriorLift R m
  refine ⟨e, L, CliffordModel.hyperbolicEquiv_ι _, ?_, ?_, ?_⟩
  · intro t s
    let b : (SplitClifford R m)ˣ := exteriorImplementer t
    let r : R := ↑s⁻¹
    have hl : (L (t, s)).val = algebraMap R (SplitClifford R m) r * b.val := rfl
    have hx : (L (t, s)).val = r • b.val := hl.trans (Algebra.smul_def r b.val).symm
    have hn : reverse (L (t, s)).val * (L (t, s)).val =
        algebraMap R _ (r ^ 2 * LinearMap.det t.toLinearMap) := by
      rw [hx, map_smul, smul_mul_smul_comm, exterior_implementer_norm,
        ← pow_two, Algebra.smul_def, ← map_mul]
    refine ⟨?_, ?_, ?_, hn, ?_⟩
    · rw [hx, map_smul, exteriorImplementer_value]
    · rw [hx]
      exact Submodule.smul_mem _ _ (exterior_implementer_even t)
    · intro x
      rw [hx, smul_mul_assoc, mul_smul_comm, implementer_intertwines]
    · rw [hn, ← map_one (algebraMap R (SplitClifford R m)), (split_scalar_injective R m).eq_iff]
      have hrs : r ^ 2 * (s : R) ^ 2 = 1 := by
        rw [← mul_pow]
        simp [r]
      constructor
      · intro h
        calc
          LinearMap.det t.toLinearMap = ((s : R) ^ 2 * r ^ 2) * LinearMap.det t.toLinearMap := by
            rw [mul_comm _ (r ^ 2), hrs, one_mul]
          _ = (s : R) ^ 2 := by rw [mul_assoc, h, mul_one]
      · rintro h
        rwa [h]
  · intro t a ha
    let b : (SplitClifford R m)ˣ := exteriorImplementer t
    have hc (x : Module.Dual R (CreationSpace R m) × CreationSpace R m) :
        Commute (↑(b⁻¹ * a) : SplitClifford R m) (ι (QuadraticForm.dualProd R (CreationSpace R m)) x) := by
      let X := ι (QuadraticForm.dualProd R (CreationSpace R m)) x
      let Y := ι (QuadraticForm.dualProd R (CreationSpace R m)) (splitScaleAction t x)
      have hb : b.val * X = Y * b.val := implementer_intertwines t x
      have hb' : (↑b⁻¹ : SplitClifford R m) * Y = X * (↑b⁻¹ : SplitClifford R m) := by
        calc
          _ = (↑b⁻¹ : SplitClifford R m) * (Y * b.val) * (↑b⁻¹ : SplitClifford R m) := by
            rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
          _ = _ := by rw [← hb, ← mul_assoc, Units.inv_mul, one_mul]
      change ((↑b⁻¹ : SplitClifford R m) * a.val) * X = X * ((↑b⁻¹ : SplitClifford R m) * a.val)
      rw [mul_assoc, show a.val * X = Y * a.val from ha x, ← mul_assoc, hb', mul_assoc]
    obtain ⟨r, hr⟩ := scalar_unit_of_commutes (b⁻¹ * a) hc
    have h₀ : a = b * splitScalar R m r :=
      inv_mul_eq_iff_eq_mul.mp hr
    have h₁ : a = L (t, r⁻¹) := by
      change a = splitScalar R m (r⁻¹)⁻¹ * b
      rw [inv_inv, h₀]
      apply Units.ext
      exact (Algebra.commutes (r : R) b.val).symm
    refine ⟨r⁻¹, h₁, fun s hs => ?_⟩
    have h : splitScalar R m s⁻¹ = splitScalar R m r := by
      have he := hs.symm.trans h₁
      change splitScalar R m s⁻¹ * b = splitScalar R m (r⁻¹)⁻¹ * b at he
      rw [inv_inv] at he
      exact mul_right_cancel he
    apply inv_injective
    rw [inv_inv]
    exact Units.ext (split_scalar_injective R m (congrArg Units.val h))
  · intro s
    change splitScalar R m s⁻¹ * exteriorImplementer (1 : CreationSpace R m ≃ₗ[R] CreationSpace R m) = _
    rw [exteriorImplementer_one, mul_one]
    rfl

open scoped TensorProduct
open _root_.Specs.RM03.CSA (isCentralSimple degree reducedNorm)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open _root_.RM03.CSA (algEquiv_matrix_algebraicClosure reducedNorm_map
  reducedNorm_mul reducedNorm_one)
open _root_.RM03.CSA.NormOneGroup (normHom normAt_eq_det normAt_natural changeCoefficients)

private theorem quaternionNormOnUnits_proof : QuaternionNormOnUnits.{u} := by
  intro F B _ _ _ hB hdeg J _ b R _ _
  refine ⟨Units.map (normHom hB b), fun _ => rfl, ?_⟩
  intro s
  apply Units.ext
  change normAt hB b (algebraMap R (R ⊗[F] B) s.val) = s.val ^ 2
  obtain ⟨d⟩ := algEquiv_matrix_algebraicClosure hB
  let K := AlgebraicClosure F
  let T := K ⊗[F] R
  let f : R →ₐ[F] T := Algebra.TensorProduct.includeRight
  apply Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  change f (_root_.RM03.CSA.NormOneGroup.normAt hB b
    (algebraMap R (R ⊗[F] B) s.val)) = f (s.val ^ 2)
  rw [← normAt_natural hB b f, map_pow, normAt_eq_det hB b d]
  have hs : changeCoefficients f (algebraMap R (R ⊗[F] B) s.val) =
      algebraMap T (T ⊗[F] B) (f s.val) := by
    change changeCoefficients f (s.val ⊗ₜ[F] 1) = f s.val ⊗ₜ[F] 1
    rfl
  rw [hs, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin]
  exact congrArg (fun n : ℕ => f s.val ^ n) hdeg

private def quaternionNorm {F B : Type u} [Field F] [Ring B] [Algebra F B]
    (hB : isCentralSimple F B) : Bˣ →* Fˣ :=
  Units.map
    { toFun := reducedNorm hB
      map_one' := reducedNorm_one hB
      map_mul' := reducedNorm_mul hB }

private theorem quaternionNorm_scalar {F B : Type u} [Field F] [Ring B] [Algebra F B]
    (hB : isCentralSimple F B) (hdeg : degree F B = 2) (s : Fˣ) :
    quaternionNorm hB (Units.map (algebraMap F B).toMonoidHom s) = s ^ 2 := by
  apply Units.ext
  change _root_.RM03.CSA.reducedNorm hB (algebraMap F B s.val) = s.val ^ 2
  obtain ⟨d⟩ := algEquiv_matrix_algebraicClosure hB
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [reducedNorm_map hB _ d, map_pow, ← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply F (AlgebraicClosure F) (AlgebraicClosure F ⊗[F] B),
    AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]
  exact congrArg (fun n : ℕ => (algebraMap F (AlgebraicClosure F) s.val) ^ n) hdeg

private theorem scale_equation {B F : Type u} [Ring B] [CommRing F] {N : Bˣ →* Fˣ}
    (x : scalePairs N) : N x.val.1 = x.val.2 ^ 2 := x.property

private def localProduct {F B : Type u} [Field F] [Ring B] [Algebra F B]
    (hB : isCentralSimple F B) (hdeg : degree F B = 2) :
    scalePairs (quaternionNorm hB) ≃* (quaternionNorm hB).ker × Fˣ := by
  let N : Bˣ →* Fˣ := quaternionNorm hB
  let scalar : Fˣ →* Bˣ := Units.map (algebraMap F B).toMonoidHom
  have hscalar (s : Fˣ) : N (scalar s) = s ^ 2 := quaternionNorm_scalar hB hdeg s
  have hcomm (s : Fˣ) (b : Bˣ) : Commute (scalar s) b := by
    apply Units.val_injective
    exact Algebra.commutes (s : F) b.val
  refine
    { toFun := fun x => (⟨x.val.1 * (scalar x.val.2)⁻¹, ?_⟩, x.val.2)
      invFun := fun x => ⟨(x.1.val * scalar x.2, x.2), ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · change N (x.val.1 * (scalar x.val.2)⁻¹) = 1
    rw [map_mul, map_inv, scale_equation, hscalar, mul_inv_cancel]
  · change N (x.1.val * scalar x.2) = x.2 ^ 2
    rw [map_mul, hscalar, x.1.property, one_mul]
  · intro x
    apply Subtype.ext
    exact Prod.ext (by change x.val.1 * (scalar x.val.2)⁻¹ * scalar x.val.2 = x.val.1; simp) rfl
  · intro x
    apply Prod.ext
    swap
    · rfl
    apply Subtype.ext
    change x.1.val * scalar x.2 * (scalar x.2)⁻¹ = x.1.val
    simp
  · intro x y
    apply Prod.ext
    swap
    · rfl
    apply Subtype.ext
    change (x.val.1 * y.val.1) * (scalar (x.val.2 * y.val.2))⁻¹ =
      (x.val.1 * (scalar x.val.2)⁻¹) * (y.val.1 * (scalar y.val.2)⁻¹)
    rw [map_mul, mul_inv_rev, (hcomm y.val.2 (scalar x.val.2)).inv_inv.eq]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, (hcomm x.val.2 y.val.1).inv_left.symm.eq, mul_assoc]

private theorem localScaleCover_proof : LocalScaleCover.{u} := by
  intro F B _ _ _ _ _ _ _ _ hB hdeg
  let scalar : Fˣ →* Bˣ := Units.map (algebraMap F B).toMonoidHom
  have hs : Continuous scalar := (continuous_algebraMap F B).units_map _
  let e : scalePairs (quaternionNorm hB) ≃ₜ* (quaternionNorm hB).ker × Fˣ :=
    { __ := localProduct hB hdeg
      continuous_toFun := by
        change Continuous (fun x : scalePairs (quaternionNorm hB) =>
          ((⟨x.val.1 * (scalar x.val.2)⁻¹, _⟩ : (quaternionNorm hB).ker), x.val.2))
        refine (Continuous.subtype_mk ?_ _).prodMk continuous_subtype_val.snd
        exact continuous_subtype_val.fst.mul (hs.comp continuous_subtype_val.snd).inv
      continuous_invFun := by
        change Continuous (fun x : (quaternionNorm hB).ker × Fˣ =>
          (⟨(x.1.val * scalar x.2, x.2), _⟩ : scalePairs (quaternionNorm hB)))
        refine Continuous.subtype_mk
          (((continuous_subtype_val.comp continuous_fst).mul (hs.comp continuous_snd)).prodMk
            continuous_snd) _ }
  refine ⟨quaternionNorm hB, e, fun _ => rfl, fun _ => ⟨rfl,rfl⟩, fun _ _ => rfl, ?_⟩
  intro H A hH hA hscalar hnorm
  have hclosed := hH.preimage (e.symm.continuous.comp
    ((continuous_id : Continuous (fun x : (quaternionNorm hB).ker => x)).prodMk
      (continuous_const (y := (1 : Fˣ)))))
  have hfull : ∀ b : (quaternionNorm hB).ker, e.symm (b,1) ∈ H := by
    intro b
    exact closure_minimal hnorm hclosed (hA b)
  apply top_unique
  intro x _
  obtain ⟨⟨b,s⟩, rfl⟩ := e.symm.surjective x
  have h := H.mul_mem (hfull b) (hscalar s)
  rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] at h
  exact h

private theorem normalizedSquareRoot : NormalizedSquareRoot.{u} := by
  intro F C _ _ _ _ point x y hx hy hp
  apply Units.ext
  have h : x.val ^ 2 = y.val ^ 2 := congrArg Units.val hp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with he | he
  · exact he
  · have hs := congrArg point he
    rw [map_neg, hx, hy] at hs
    have hneg : (1 : C) = -1 := by
      have hmap := congrArg (algebraMap F C) hs
      simpa only [map_one, map_neg] using hmap
    have hy' : -y.val = y.val := by
      have heq := congrArg (fun a : C => a * y.val) hneg.symm
      simpa only [neg_mul, one_mul] using heq
    exact he.trans hy'

private theorem valuedSquareRoot_proof : ValuedSquareRoot.{u} := by
  intro F _ _ _ _ _
  have hsub (x y : F) : x ^ 2 - y ^ 2 = (x - y) ^ 2 := by
    calc
      _ = x ^ 2 + (-y) ^ 2 := by rw [sub_eq_add_neg, neg_sq, CharTwo.neg_eq]
      _ = _ := by rw [← CharTwo.add_sq, sub_eq_add_neg]
  refine ⟨?_, ?_⟩
  · apply Topology.isInducing_iff_nhds.mpr
    intro x
    let b := IsValuativeTopology.hasBasis_nhds x
    let c := (IsValuativeTopology.hasBasis_nhds (x ^ 2)).comap (fun s : F => s ^ 2)
    apply le_antisymm
    · apply (b.le_basis_iff c).mpr
      intro a _
      refine ⟨min a 1, trivial, ?_⟩
      intro y hy
      change ValuativeRel.valuation F (y - x) < ↑(min a 1) at hy
      change ValuativeRel.valuation F (y ^ 2 - x ^ 2) < _
      rw [hsub, map_pow]
      have h₁ : (↑(min a 1) : ValuativeRel.ValueGroupWithZero F) ≤
          ↑(1 : (ValuativeRel.ValueGroupWithZero F)ˣ) :=
        (show min a 1 ≤ 1 from min_le_right _ _)
      have h₂ : (↑(min a 1) : ValuativeRel.ValueGroupWithZero F) ≤ ↑a :=
        (show min a 1 ≤ a from min_le_left _ _)
      have hle : ValuativeRel.valuation F (y - x) ≤ 1 := hy.le.trans h₁
      rw [pow_two]
      exact (mul_le_of_le_one_right zero_le hle).trans_lt (hy.trans_le h₂)
    · apply (c.le_basis_iff b).mpr
      intro a _
      refine ⟨a ^ 2, trivial, ?_⟩
      intro y hy
      change ValuativeRel.valuation F (y ^ 2 - x ^ 2) < _ at hy
      rw [hsub, map_pow, Units.val_pow_eq_pow_val,
        pow_lt_pow_iff_left₀ zero_le zero_le (by decide : (2 : ℕ) ≠ 0)] at hy
      exact hy
  · intro x y h
    change x ^ 2 = y ^ 2 at h
    have hs : (x - y) ^ 2 = 0 := by rw [← hsub, h, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hs)

section GaloisDescent

variable {F K C : Type u} [Field F] [Field K] [Algebra F K]
  [CommRing C] [Algebra F C]

private abbrev scalarExtension : C →ₐ[F] K ⊗[F] C :=
  Algebra.TensorProduct.includeRight

private abbrev tensorAut (σ : K ≃ₐ[F] K) : K ⊗[F] C →ₐ[F] K ⊗[F] C :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id F C)

private theorem tensorAut_scalarExtension (σ : K ≃ₐ[F] K) (x : C) :
    tensorAut σ (scalarExtension (K := K) x) = scalarExtension (K := K) x := by
  change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id F C) (1 ⊗ₜ[F] x) = _
  simp [Algebra.TensorProduct.map_tmul]

private theorem extendPoint_tensorAut (p : C →ₐ[F] F) (σ : K ≃ₐ[F] K) (x : K ⊗[F] C) :
    extendPoint p (tensorAut σ x) = σ (extendPoint p x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul k c =>
    simp [extendPoint, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul,
      Algebra.smul_def, AlgEquiv.commutes]

private theorem tensorAut_coord {J : Type u} (b : Module.Basis J F C)
    (σ : K ≃ₐ[F] K) (x : K ⊗[F] C) (i : J) :
    (b.baseChange K).repr (tensorAut σ x) i = σ ((b.baseChange K).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul k c =>
    simp [Algebra.TensorProduct.map_tmul, Algebra.smul_def, AlgEquiv.commutes]

private theorem tensor_fixed_descends [FiniteDimensional F K] [IsGalois F K]
    (x : K ⊗[F] C) (hx : ∀ σ : K ≃ₐ[F] K, tensorAut σ x = x) :
    ∃ y : C, scalarExtension y = x := by
  classical
  let b := Module.Free.chooseBasis F C
  let coords := (b.baseChange K).repr x
  have hcoeff (i : Module.Free.ChooseBasisIndex F C) :
      ∃ y : F, algebraMap F K y = coords i :=
    (IsGalois.mem_range_algebraMap_iff_fixed (coords i)).mpr fun σ =>
      (tensorAut_coord b σ x i).symm.trans (congrArg (fun z => (b.baseChange K).repr z i) (hx σ))
  choose a ha using hcoeff
  refine ⟨∑ i ∈ coords.support, a i • b i, ?_⟩
  rw [map_sum]
  have hterm (i : Module.Free.ChooseBasisIndex F C) :
      scalarExtension (a i • b i) = coords i • (b.baseChange K) i := by
    rw [← ha i, Module.Basis.baseChange_apply]
    change (1 : K) ⊗ₜ[F] (a i • b i) = (algebraMap F K (a i)) • ((1 : K) ⊗ₜ[F] b i)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    rw [Algebra.smul_def (R := F), mul_one]
    simp
  simp_rw [hterm]
  exact (b.baseChange K).linearCombination_repr x

private theorem galoisSquareRootDescent : GaloisSquareRootDescent.{u} := by
  intro F K C _ _ _ _ _ _ _ _ p n s hp hs
  let f : C →ₐ[F] K ⊗[F] C := scalarExtension
  have hf : Function.Injective f :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hfixed (σ : K ≃ₐ[F] K) : Units.map (tensorAut σ).toMonoidHom s = s := by
    refine normalizedSquareRoot (extendPoint p) _ _ ?_ hp ?_
    · change extendPoint p (tensorAut σ s.val) = 1
      rw [extendPoint_tensorAut, hp, map_one]
    · rw [← map_pow, hs]
      apply Units.ext
      exact tensorAut_scalarExtension σ n.val
  obtain ⟨r, hr⟩ := tensor_fixed_descends s.val (fun σ => congrArg Units.val (hfixed σ))
  obtain ⟨rinv, hri⟩ := tensor_fixed_descends ((s⁻¹ : (K ⊗[F] C)ˣ) : K ⊗[F] C)
    (fun σ => by
      have h := congrArg (fun z : (K ⊗[F] C)ˣ => (↑z⁻¹ : K ⊗[F] C)) (hfixed σ)
      rw [← map_inv] at h
      exact h)
  have hrri : r * rinv = 1 := by
    apply hf
    rw [map_mul, map_one, hr, hri, Units.mul_inv]
  let r' : Cˣ := ⟨r, rinv, hrri, (mul_comm _ _).trans hrri⟩
  exact ⟨r', Units.ext hr, fun y hy => Units.ext (hf (congrArg Units.val hy |>.trans hr.symm))⟩

set_option maxHeartbeats 1000000 in
private theorem scaleComparisonDescent_proof : ScaleComparisonDescent.{u} := by
  intro F K A C D _ _ _ _ _ _ _ _ _ _ _ _
    i j p n s hsq hgen e he hp
  let f : C →ₐ[F] K ⊗[F] C := scalarExtension
  let g : D →ₐ[F] K ⊗[F] D := scalarExtension
  have hf : Function.Injective f :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hg : Function.Injective g :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  let k : D →ₐ[F] K ⊗[F] C := (e.toAlgHom.restrictScalars F).comp g
  have hk (a : A) : k (j a) = f (i a) := he a
  have hnorm : (Units.map k.toMonoidHom s) ^ 2 = Units.map f.toMonoidHom (Units.map i.toMonoidHom n) := by
    rw [← map_pow, hsq]
    exact Units.ext (hk n.val)
  have hp' : extendPoint p (Units.map k.toMonoidHom s).val = 1 := hp
  obtain ⟨s₀, hs₀, _⟩ :=
    galoisSquareRootDescent p (Units.map i.toMonoidHom n) (Units.map k.toMonoidHom s) hp' hnorm
  have hval : f s₀.val = k s.val := congrArg Units.val hs₀
  have hfixed (σ : K ≃ₐ[F] K) : (tensorAut σ).comp k = k :=
    hgen _ _ (by
      apply AlgHom.ext
      intro a
      change tensorAut σ (k (j a)) = k (j a)
      rw [hk]
      exact tensorAut_scalarExtension σ (i a)) (by
      change tensorAut σ (k s.val) = k s.val
      rw [← hval]
      exact tensorAut_scalarExtension σ s₀.val)
  have hfixed' (σ : K ≃ₐ[F] K) (a : D) : tensorAut σ (k a) = k a :=
    DFunLike.congr_fun (hfixed σ) a
  have e_tmul (a : K) (y : D) : e (a ⊗ₜ[F] y) = (a ⊗ₜ[F] (1 : C)) * k y := by
    calc
      _ = e ((a ⊗ₜ[F] (1 : D)) * (1 ⊗ₜ[F] y)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      _ = _ := by
        rw [map_mul]
        exact congrArg (· * k y) (e.commutes a)
  have hcomm (σ : K ≃ₐ[F] K) (z : K ⊗[F] D) :
      tensorAut σ (e z) = e (tensorAut σ z) := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a y =>
      rw [e_tmul, map_mul, show tensorAut σ (a ⊗ₜ[F] (1 : C)) = (σ a) ⊗ₜ[F] (1 : C) from rfl,
        hfixed' σ y,
        show tensorAut σ (a ⊗ₜ[F] y) = (σ a) ⊗ₜ[F] y from rfl, e_tmul]
  have H (a : D) : ∃ b : C, f b = k a :=
    tensor_fixed_descends (k a) (fun σ => hfixed' σ a)
  choose e₀ h₀ using H
  let d : D →ₐ[F] C := {
    toFun := e₀
    map_zero' := hf (by rw [h₀, map_zero, map_zero])
    map_one' := hf (by rw [h₀, map_one, map_one])
    map_add' := fun x y => hf (by rw [h₀, map_add, map_add, h₀, h₀])
    map_mul' := fun x y => hf (by rw [h₀, map_mul, map_mul, h₀, h₀])
    commutes' := fun r => hf (by rw [h₀, k.commutes, f.commutes]) }
  have hbij : Function.Bijective d := by
    constructor
    · intro x y h
      apply hg
      apply e.injective
      change k x = k y
      exact (h₀ x).symm.trans ((congrArg f h).trans (h₀ y))
    · intro b
      have hz (σ : K ≃ₐ[F] K) : tensorAut σ (e.symm (f b)) = e.symm (f b) := by
        apply e.injective
        rw [← hcomm, e.apply_symm_apply, tensorAut_scalarExtension]
      obtain ⟨a, ha⟩ := tensor_fixed_descends _ hz
      refine ⟨a, hf ?_⟩
      change f (e₀ a) = f b
      rw [h₀]
      change e (g a) = f b
      rw [show g a = _ from ha, e.apply_symm_apply]
  let E := AlgEquiv.ofBijective d hbij
  refine ⟨E, ?_, ?_⟩
  · apply AlgHom.ext
    intro a
    apply hf
    change f (e₀ (j a)) = f (i a)
    rw [h₀, hk]
  · apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a y =>
      change a ⊗ₜ[F] (e₀ y) = e (a ⊗ₜ[F] y)
      rw [e_tmul, ← h₀]
      change a ⊗ₜ[F] (e₀ y) = (a ⊗ₜ[F] (1 : C)) * ((1 : K) ⊗ₜ[F] e₀ y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end GaloisDescent

private theorem scalePairKernel_proof : ScalePairKernel.{u} := by
  intro C R _ _ N
  have hfirst (x : (scaleProjection (N := N)).ker) : x.val.val.1 = 1 := x.property
  have hsecond (x : (scaleProjection (N := N)).ker) : x.val.val.2 ^ 2 = 1 := by
    rw [← scale_equation x.val, hfirst, map_one]
  let toRoot (x : (scaleProjection (N := N)).ker) : rootsOfUnity 2 R :=
    ⟨x.val.val.2, (mem_rootsOfUnity 2 _).mpr (hsecond x)⟩
  let fromRoot (x : rootsOfUnity 2 R) : (scaleProjection (N := N)).ker :=
    ⟨⟨(1, x.val), (map_one N).trans ((mem_rootsOfUnity 2 _).mp x.property).symm⟩, rfl⟩
  refine ⟨{ toFun := toRoot
            invFun := fromRoot
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_ }, fun _ => rfl⟩
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (hfirst x).symm rfl
  · intro x
    rfl
  · intro x y
    rfl

open SplitSpinSpecification (NormOneBlock scaleRow)

private theorem splitScaleParameters_proof : SplitScaleParameters.{u} := by
  intro R _
  dsimp only
  let D := {p : Matrix (Fin 2) (Fin 2) R × Rˣ // p.1.det = (p.2 : R) ^ 2}
  let h : D ≃ NormOneBlock 2 R :=
    { toFun := fun p => ⟨(p.val.1, p.val.2⁻¹), by
        rw [p.property, ← mul_pow, Units.inv_mul, one_pow]⟩
      invFun := fun p => ⟨(p.val.1, p.val.2⁻¹), by
        change p.val.1.det = (↑p.val.2⁻¹ : R) ^ 2
        calc
          p.val.1.det = ((↑p.val.2⁻¹ : R) ^ 2 * (p.val.2 : R) ^ 2) * p.val.1.det := by
            rw [← mul_pow, Units.inv_mul, one_pow, one_mul]
          _ = (↑p.val.2⁻¹ : R) ^ 2 := by rw [mul_assoc, p.property, mul_one]⟩
      left_inv := fun p => Subtype.ext (Prod.ext rfl (inv_inv p.val.2))
      right_inv := fun p => Subtype.ext (Prod.ext rfl (inv_inv p.val.2)) }
  obtain ⟨e, he⟩ := SplitSpin.normalizeMiddle 2 R (0 : Fin 2)
  let p : ({A : Matrix (Fin 2) (Fin 2) R // A.det = 1} × Rˣ) ≃
      (Matrix.SpecialLinearGroup (Fin 2) R × Rˣ) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.inv Rˣ)
  refine ⟨h.trans (e.trans p), fun x => ⟨(he (h x)).1, ?_⟩⟩
  change (e (h x)).2⁻¹ = x.val.2
  rw [(he (h x)).2]
  exact inv_inv x.val.2

private theorem splitScaleDeterminant : SplitScaleDeterminant.{u} := by
  intro R _ t d j T
  change LinearMap.det
    (j.symm.toLinearMap.comp ((t.toLinearMap.prodMap LinearMap.id).comp j.toLinearMap)) = _
  let f := t.toLinearMap.prodMap (LinearMap.id : Module.End R (CreationSpace R d))
  calc
    _ = LinearMap.det f := LinearMap.det_conj f j.symm
    _ = _ := by simp [f, LinearMap.det_prodMap]

private theorem normalizedScaleFamilies_proof : NormalizedScaleFamilies.{u} := by
  intro F B C _ _ _ _ _ _ hB hdeg J _ b point
  obtain ⟨N, hN, hscalar⟩ := quaternionNormOnUnits_proof hB hdeg b C
  constructor
  · intro c s hc hs h
    refine normalizedSquareRoot point s c hs hc (Units.ext ?_)
    have he := congrArg Units.val (hscalar c)
    change (N (Units.map (algebraMap C (C ⊗[F] B)).toMonoidHom c) : C) = c.val ^ 2 at he
    rw [hN] at he
    exact h.symm.trans he
  · intro a d s hs h
    refine normalizedSquareRoot point s 1 hs (map_one point) (Units.ext ?_)
    have he : N (a * d * a⁻¹ * d⁻¹) = 1 := by
      simp [mul_assoc]
    have he' := congrArg Units.val he
    rw [hN, h] at he'
    simpa using he'

section SplitCoordinates

open Polynomial

private theorem splitScaleCoordinateDomain : SplitScaleCoordinateDomain.{u} := by
  intro F _
  let U := MvPolynomial (Fin 3) F
  let a : Polynomial U := X
  let c : U := MvPolynomial.X 0 * MvPolynomial.X 1 + 1
  have hc : c ≠ 0 := by
    intro h
    have hz := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0 : F))) h
    simp [c] at hz
  have hdvd : ¬a ∣ -C c := by
    rintro ⟨p, hp⟩
    have h := congrArg (Polynomial.eval (0 : U)) hp
    simp [a, hc] at h
  have hrel : IsRelPrime (-C c) a :=
    ((Polynomial.prime_X (R := U)).irreducible.isRelPrime_iff_not_dvd.mpr hdvd).symm
  have hdegree : (splitScaleRelation F).degree = 1 := by
    unfold splitScaleRelation
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · rw [Polynomial.degree_C_mul_X (Polynomial.X_ne_zero)]
    · rw [Polynomial.degree_C_mul_X (Polynomial.X_ne_zero)]
      exact Polynomial.degree_C_le.trans_lt (by decide)
  have hprime : Prime (splitScaleRelation F) := by
    apply Irreducible.prime
    apply Polynomial.irreducible_of_degree_eq_one_of_isRelPrime_coeff hdegree
    simpa [splitScaleRelation, Polynomial.coeff_C_mul_X, Polynomial.coeff_one, a, c] using hrel
  let _ : IsDomain (SplitScaleAffineRing F) := AdjoinRoot.isDomain_of_prime hprime
  have hu : splitScaleVariable F ≠ 0 := by
    intro hz
    have hX : (MvPolynomial.X (2 : Fin 3) : U) ≠ 0 := MvPolynomial.X_ne_zero _
    have hne : (Polynomial.C (MvPolynomial.X (2 : Fin 3) : U) : Polynomial U) ≠ 0 :=
      Polynomial.C_ne_zero.mpr hX
    apply hne
    apply AdjoinRoot.of.injective_of_degree_ne_zero (show (splitScaleRelation F).degree ≠ 0 by
      rw [hdegree]
      decide)
    rwa [map_zero]
  exact Localization.Away.isDomain hu

end SplitCoordinates

section ScaleRepresentation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Opposite
open MulOpposite (unop)
open scoped TensorProduct CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair SpinModel)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (antiValue extendAnti tensorMap)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (isCentralSimple)



variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F}
  {hB : isCentralSimple F B} {d : ℕ}
  (P : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)

private theorem pairMatrix_natural {R S : TestAlgebra F} (f : R ⟶ S)
    (x : R ⊗[F] ρ.fixedSubalgebra) :
    Q.matrixAt S (tensorMap _ f.hom x) = (Q.matrixAt R x).map (tensorMap B f.hom) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    ext i j
    simp [tensorMap, Q.matrixAtFormula]
  | add x y hx hy => simp [hx, hy, Matrix.map_add]

private theorem quaternionConjugation_natural {R S : TestAlgebra F} (f : R ⟶ S)
    (x : R ⊗[F] B) :
    antiValue (extendAnti Q.conjugation.anti S) (tensorMap B f.hom x) =
      tensorMap B f.hom (antiValue (extendAnti Q.conjugation.anti R) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r b => simp [antiValue, extendAnti, tensorMap]
  | add x y hx hy => simpa [antiValue, map_add, MulOpposite.unop_add] using congrArg₂ (· + ·) hx hy

private theorem spinVectorProjection_natural {R S : TestAlgebra F} (f : R ⟶ S)
    (g : Points G.val.X R) :
    spinVectorProjection P S (mapPoints f g) =
      Units.map (tensorMap _ f.hom).toMonoidHom (spinVectorProjection P R g) := by
  change P.fullPoints S (mapPoints f g ≫ (P.projection ≫ P.inclusion).hom.hom) =
    Units.map (tensorMap _ f.hom).toMonoidHom
      (P.fullPoints R (g ≫ (P.projection ≫ P.inclusion).hom.hom))
  rw [Category.assoc]
  exact P.fullNatural R S f _

private def scaleDiagonal {C : Type u} [Ring C] (d : ℕ) (t z : C) :
    Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) C :=
  diagonal (Sum.elim ![t, z] fun _ => 1)

private abbrev firstLine (d : ℕ) : QuaternionPairIndex d := Sum.inl 0

@[simp] private theorem scaleDiagonal_first {C : Type u} [Ring C] (t z : C) :
    scaleDiagonal d t z (firstLine d) (firstLine d) = t := by
  simp [scaleDiagonal]

private theorem scaleDiagonal_map {C C' : Type u} [Ring C] [Ring C'] (f : C →+* C')
    (t z : C) : (scaleDiagonal d t z).map f = scaleDiagonal d (f t) (f z) := by
  have hv (i : QuaternionPairIndex d) :
      f (Sum.elim ![t, z] (fun _ => 1) i) = Sum.elim ![f t, f z] (fun _ => 1) i := by
    rcases i with i | i
    · fin_cases i <;> rfl
    · exact f.map_one
  ext i j
  by_cases h : i = j
  · subst j
    simpa [scaleDiagonal] using hv i
  · simp [scaleDiagonal, diagonal_apply_ne _ h]

private theorem diagonalQuaternionScale_val {C : Type u} [Ring C] (σ : C →* Cᵐᵒᵖ)
    (t : Cˣ) : (diagonalQuaternionScale σ d t).val =
      scaleDiagonal d t.val (unop (σ t.inv)) := by
  change diagonal (fun i => ((Sum.elim ![t, inverseConjugateUnit σ t] (fun _ => 1)) i).val) = _
  rw [scaleDiagonal]
  congr 1
  funext i
  rcases i with i | i
  · fin_cases i <;> rfl
  · rfl

private def spinScaleMatrix (R : TestAlgebra F) (g : Points G.val.X R) :
    (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))ˣ :=
  Units.map (Q.matrixAt R).toMonoidHom (spinVectorProjection P R g)

private theorem spinScaleMatrix_natural {R S : TestAlgebra F} (f : R ⟶ S)
    (g : Points G.val.X R) :
    spinScaleMatrix P Q S (mapPoints f g) =
      Units.map (RingHom.mapMatrix (tensorMap B f.hom).toRingHom).toMonoidHom
        (spinScaleMatrix P Q R g) := by
  apply Units.ext
  change Q.matrixAt S (spinVectorProjection P S (mapPoints f g)).val =
    (Q.matrixAt R (spinVectorProjection P R g).val).map (tensorMap B f.hom)
  rw [spinVectorProjection_natural, Units.coe_map]
  exact pairMatrix_natural Q f _

private def scaleMatrixEquation (R : TestAlgebra F)
    (M : (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))ˣ) :
    Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B) :=
  M.val - scaleDiagonal d (M.val (firstLine d) (firstLine d))
    (antiValue (extendAnti Q.conjugation.anti R) (M.inv (firstLine d) (firstLine d)))

private theorem scaleMatrixEquation_natural {R S : TestAlgebra F} (f : R ⟶ S)
    (M : (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))ˣ) :
    scaleMatrixEquation Q S
        (Units.map (RingHom.mapMatrix (tensorMap B f.hom).toRingHom).toMonoidHom M) =
      (scaleMatrixEquation Q R M).map (tensorMap B f.hom) := by
  change _ = RingHom.mapMatrix (tensorMap B f.hom).toRingHom (scaleMatrixEquation Q R M)
  let f' := (tensorMap B f.hom).toRingHom
  let m := f'.mapMatrix (m := QuaternionPairIndex d)
  have hi : (Units.map m.toMonoidHom M).inv = m M.inv := rfl
  have hv : (Units.map m.toMonoidHom M).val = m M.val := rfl
  change scaleMatrixEquation Q S (Units.map m.toMonoidHom M) = m (scaleMatrixEquation Q R M)
  rw [scaleMatrixEquation, hi, hv, scaleMatrixEquation, map_sub]
  change M.val.map f' - scaleDiagonal d (f' _) (antiValue _ (f' _)) =
    M.val.map f' - (scaleDiagonal d _ _).map f'
  rw [scaleDiagonal_map]
  exact congrArg (fun a => M.val.map f' - scaleDiagonal d (f' _) a)
    (quaternionConjugation_natural Q f _)

private theorem scaleMatrixEquation_iff (R : TestAlgebra F)
    (M : (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))ˣ) :
    scaleMatrixEquation Q R M = 0 ↔
      ∃ t : (R ⊗[F] B)ˣ, M = diagonalQuaternionScale (extendAnti Q.conjugation.anti R).toMonoidHom d t := by
  change M.val - scaleDiagonal d _ _ = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    let w := firstLine d
    have hl := congrArg (fun A : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d)
        (R ⊗[F] B) => A w w) M.val_inv
    have hr := congrArg (fun A : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d)
        (R ⊗[F] B) => A w w) M.inv_val
    change (M.val * M.inv) w w = _ at hl
    change (M.inv * M.val) w w = _ at hr
    rw [h] at hl hr
    simp only [scaleDiagonal, diagonal_mul, mul_diagonal, Sum.elim_inl,
      Matrix.cons_val_zero, Matrix.one_apply_eq, w] at hl hr
    let t : (R ⊗[F] B)ˣ := ⟨M.val w w, M.inv w w, hl, hr⟩
    exact ⟨t, Units.ext (by rw [diagonalQuaternionScale_val]; exact h)⟩
  · rintro ⟨t, rfl⟩
    rw [diagonalQuaternionScale_val]
    have hi : (diagonalQuaternionScale (extendAnti Q.conjugation.anti R).toMonoidHom d t).inv =
        scaleDiagonal d t.inv
          (unop ((extendAnti Q.conjugation.anti R).toMonoidHom (t⁻¹ : (R ⊗[F] B)ˣ).inv)) := by
      change (((diagonalQuaternionScale (extendAnti Q.conjugation.anti R).toMonoidHom d) t)⁻¹).val = _
      rw [← map_inv, diagonalQuaternionScale_val]
      rfl
    rw [hi, scaleDiagonal_first, scaleDiagonal_first]
    rfl

private theorem quaternionScale_natural {R S : TestAlgebra F} (f : R ⟶ S)
    (t : (R ⊗[F] B)ˣ) :
    quaternionScale Q S (Units.map (tensorMap B f.hom).toMonoidHom t) =
      Units.map (tensorMap _ f.hom).toMonoidHom (quaternionScale Q R t) := by
  apply Units.ext
  apply (Q.matrixAt S).injective
  change (Q.matrixAt S) ((Q.matrixAt S).symm
    (diagonalQuaternionScale (extendAnti Q.conjugation.anti S).toMonoidHom d
      (Units.map (tensorMap B f.hom).toMonoidHom t)).val) =
    Q.matrixAt S (tensorMap _ f.hom (quaternionScale Q R t).val)
  rw [AlgEquiv.apply_symm_apply, pairMatrix_natural Q, show Q.matrixAt R (quaternionScale Q R t).val =
    (diagonalQuaternionScale (extendAnti Q.conjugation.anti R).toMonoidHom d t).val from
      (Q.matrixAt R).apply_symm_apply _]
  rw [diagonalQuaternionScale_val, diagonalQuaternionScale_val]
  change scaleDiagonal d (tensorMap B f.hom t.val)
    (antiValue (extendAnti Q.conjugation.anti S) (tensorMap B f.hom t.inv)) =
    (scaleDiagonal d t.val (antiValue (extendAnti Q.conjugation.anti R) t.inv)).map
      (tensorMap B f.hom).toRingHom
  rw [scaleDiagonal_map]
  exact congrArg (scaleDiagonal d (tensorMap B f.hom t.val)) (quaternionConjugation_natural Q f t.inv)

private theorem spinScaleMatrixEquation_iff (R : TestAlgebra F) (g : Points G.val.X R) :
    scaleMatrixEquation Q R (spinScaleMatrix P Q R g) = 0 ↔
      ∃ t : (R ⊗[F] B)ˣ, spinVectorProjection P R g = quaternionScale Q R t := by
  rw [scaleMatrixEquation_iff]
  refine exists_congr fun t => ?_
  let q := Units.mapEquiv (Q.matrixAt R).toMulEquiv
  change q (spinVectorProjection P R g) = _ ↔ spinVectorProjection P R g = q.symm _
  exact q.eq_symm_apply.symm

private theorem quaternionScale_injective (R : TestAlgebra F) : Function.Injective (quaternionScale Q R) := by
  intro a b h
  have h' : (diagonalQuaternionScale (extendAnti Q.conjugation.anti R).toMonoidHom d a).val =
      (diagonalQuaternionScale (extendAnti Q.conjugation.anti R).toMonoidHom d b).val :=
    (Q.matrixAt R).symm.injective (congrArg Units.val h)
  simp only [diagonalQuaternionScale_val] at h'
  apply Units.ext
  simpa using congrArg (fun M => M (firstLine d) (firstLine d)) h'

private def spinScalePointMap {R S : TestAlgebra F} (f : R ⟶ S) :
    spinScalePreimage P Q R →* spinScalePreimage P Q S where
  toFun x := ⟨(mapPoints f x.val.1, Units.map (tensorMap B f.hom).toMonoidHom x.val.2), by
    change spinVectorProjection P S (mapPoints f x.val.1) =
      quaternionScale Q S (Units.map (tensorMap B f.hom).toMonoidHom x.val.2)
    rw [spinVectorProjection_natural, quaternionScale_natural]
    exact congrArg (Units.map (tensorMap _ f.hom).toMonoidHom) x.property⟩
  map_one' := Subtype.ext (Prod.ext (MonObj.comp_one _) (map_one _))
  map_mul' x y := Subtype.ext (Prod.ext (MonObj.comp_mul _ _ _) (map_mul _ _ _))

private theorem scaleTensor_id (R : TestAlgebra F) :
    tensorMap B (AlgHom.id F R) = AlgHom.id F (R ⊗[F] B) :=
  Algebra.TensorProduct.map_id

private theorem scaleTensor_comp {R S T : TestAlgebra F} (f : R ⟶ S) (g : S ⟶ T) :
    tensorMap B (g.hom.comp f.hom) = (tensorMap B g.hom).comp (tensorMap B f.hom) := by
  unfold tensorMap
  rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]

private def scalePreimageFunctor : TestAlgebra F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (spinScalePreimage P Q R)
  map f := GrpCat.ofHom (spinScalePointMap P Q f)
  map_id R := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · change (testSpec F).map (𝟙 (op R)) ≫ x.val.1 = x.val.1
      simp
    · apply Units.ext
      change tensorMap B (AlgHom.id F R) x.val.2.val = x.val.2.val
      rw [scaleTensor_id]
      rfl
  map_comp f g := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · change (testSpec F).map (g.op ≫ f.op) ≫ x.val.1 =
        (testSpec F).map g.op ≫ (testSpec F).map f.op ≫ x.val.1
      rw [Functor.map_comp, Category.assoc]
    · apply Units.ext
      change tensorMap B (g.hom.comp f.hom) x.val.2.val = tensorMap B g.hom (tensorMap B f.hom x.val.2.val)
      rw [scaleTensor_comp]
      rfl

private def scalePreimageProjection : scalePreimageFunctor P Q ⟶ (groupPointsFunctor F).obj G.val where
  app R := GrpCat.ofHom ((MonoidHom.fst _ _).comp (spinScalePreimage P Q R).subtype)
  naturality _ _ f := by
    apply GrpCat.ext
    intro x
    rfl

private theorem scalePreimageProjection_injective (R : TestAlgebra F) :
    Function.Injective (fun x : spinScalePreimage P Q R => x.val.1) := by
  intro x y h
  apply Subtype.ext
  refine Prod.ext h (quaternionScale_injective Q R ?_)
  calc
    quaternionScale Q R x.val.2 = spinVectorProjection P R x.val.1 := x.property.symm
    _ = spinVectorProjection P R y.val.1 := congrArg (spinVectorProjection P R) h
    _ = quaternionScale Q R y.val.2 := y.property

open LinearAlgebraicGroups.WeilRestriction
  (affineSpectrum spectrumPoints groupFromPoints groupFromPointsIso)
open private affineCoordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
open private coord_change from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
open RM03.CSA.NormOneGroup (changeCoefficients)

variable {J : Type u} (b : Module.Basis J F B)
  (A : TestAlgebra F) (a : Points G.val.X A)

private def scaleDefiningIdeal : Ideal A :=
  Ideal.span (Set.range fun (ijk : QuaternionPairIndex d × QuaternionPairIndex d × J) =>
    (b.baseChange A).repr (scaleMatrixEquation Q A (spinScaleMatrix P Q A a) ijk.1 ijk.2.1) ijk.2.2)

private theorem scaleDefiningIdeal_iff {R : TestAlgebra F} (f : A ⟶ R) :
    scaleDefiningIdeal P Q b A a ≤ RingHom.ker f.hom.toRingHom ↔
      scaleMatrixEquation Q R (spinScaleMatrix P Q R (mapPoints f a)) = 0 := by
  rw [spinScaleMatrix_natural P Q, scaleMatrixEquation_natural, scaleDefiningIdeal, Ideal.span_le]
  constructor
  · intro h
    ext i j
    apply (b.baseChange R).repr.injective
    apply Finsupp.ext
    intro k
    change (b.baseChange R).repr
      (tensorMap B f.hom (scaleMatrixEquation Q A (spinScaleMatrix P Q A a) i j)) k =
      (b.baseChange R).repr 0 k
    change (b.baseChange R).repr (changeCoefficients f.hom _) k = _
    rw [coord_change, map_zero, Finsupp.zero_apply]
    exact h ⟨(i,j,k), rfl⟩
  · rintro hz _ ⟨⟨i,j,k⟩, rfl⟩
    have he := congrArg (fun M : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B) =>
      (b.baseChange R).repr (M i j) k) hz
    change (b.baseChange R).repr
      (tensorMap B f.hom (scaleMatrixEquation Q A (spinScaleMatrix P Q A a) i j)) k =
      (b.baseChange R).repr 0 k at he
    change (b.baseChange R).repr (changeCoefficients f.hom _) k = _ at he
    rwa [coord_change, map_zero, Finsupp.zero_apply] at he

private abbrev scaleCoordinateRing := A ⧸ scaleDefiningIdeal P Q b A a

private abbrev scaleQuotientHom : A ⟶ CommAlgCat.of F (scaleCoordinateRing P Q b A a) :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ F _)

private theorem scaleQuotient_surjective : Function.Surjective (scaleQuotientHom P Q b A a).hom :=
  Ideal.Quotient.mkₐ_surjective F _

private def scaleQuotientPoints (R : TestAlgebra F)
    (f : CommAlgCat.of F (scaleCoordinateRing P Q b A a) ⟶ R) : spinScalePreimage P Q R := by
  let q := scaleQuotientHom P Q b A a
  have h : scaleDefiningIdeal P Q b A a ≤ RingHom.ker (q ≫ f).hom.toRingHom := by
    intro x hx
    change f.hom (Ideal.Quotient.mk _ x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  let ht := (spinScaleMatrixEquation_iff P Q R _).mp ((scaleDefiningIdeal_iff P Q b A a _).mp h)
  exact ⟨(mapPoints (q ≫ f) a, ht.choose), ht.choose_spec⟩

private theorem scaleQuotientPoints_first (R : TestAlgebra F)
    (f : CommAlgCat.of F (scaleCoordinateRing P Q b A a) ⟶ R) :
    (scaleQuotientPoints P Q b A a R f).val.1 = mapPoints (scaleQuotientHom P Q b A a ≫ f) a := rfl

private theorem scaleQuotientPoints_natural {R S : TestAlgebra F} (g : R ⟶ S)
    (f : CommAlgCat.of F (scaleCoordinateRing P Q b A a) ⟶ R) :
    scaleQuotientPoints P Q b A a S (f ≫ g) =
      spinScalePointMap P Q g (scaleQuotientPoints P Q b A a R f) := by
  apply scalePreimageProjection_injective P Q
  change mapPoints (scaleQuotientHom P Q b A a ≫ f ≫ g) a =
    mapPoints g (mapPoints (scaleQuotientHom P Q b A a ≫ f) a)
  change (testSpec F).map ((scaleQuotientHom P Q b A a ≫ f) ≫ g).op ≫ a =
    (testSpec F).map g.op ≫ (testSpec F).map (scaleQuotientHom P Q b A a ≫ f).op ≫ a
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

variable {A} (eA : (testSpec F).obj (op A) ≅ G.val.X)

private theorem scaleQuotientPoints_bijective (R : TestAlgebra F) :
    Function.Bijective (scaleQuotientPoints P Q b A eA.hom R) := by
  let q := scaleQuotientHom P Q b A eA.hom
  constructor
  · intro f g h
    have he := congrArg (fun p : spinScalePreimage P Q R => p.val.1) h
    change (testSpec F).map (q ≫ f).op ≫ eA.hom = (testSpec F).map (q ≫ g).op ≫ eA.hom at he
    have he' := (algSpec.fullyFaithful (R := CommRingCat.of F)).map_injective
      ((cancel_mono eA.hom).mp he)
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := scaleQuotient_surjective P Q b A eA.hom x
    exact congrArg (fun s : (op R : (TestAlgebra F)ᵒᵖ) ⟶ op A => s.unop.hom y) he'
  · intro p
    let FF := algSpec.fullyFaithful (R := CommRingCat.of F)
    let f : A ⟶ R := (FF.preimage (p.val.1 ≫ eA.inv)).unop
    have hf : mapPoints f eA.hom = p.val.1 := by
      change (testSpec F).map (FF.preimage (p.val.1 ≫ eA.inv)) ≫ eA.hom = _
      rw [Functor.FullyFaithful.map_preimage]
      simp
    have hi : scaleDefiningIdeal P Q b A eA.hom ≤ RingHom.ker f.hom.toRingHom := by
      rw [scaleDefiningIdeal_iff, hf, spinScaleMatrixEquation_iff]
      exact ⟨p.val.2, p.property⟩
    let g := CommAlgCat.ofHom (Ideal.Quotient.liftₐ (scaleDefiningIdeal P Q b A eA.hom) f.hom hi)
    have hg : q ≫ g = f := CommAlgCat.hom_ext (Ideal.Quotient.liftₐ_comp _ _ _)
    refine ⟨g, scalePreimageProjection_injective P Q R ?_⟩
    exact (scaleQuotientPoints_first P Q b A eA.hom R g).trans (hg ▸ hf)

private def scaleQuotientPointsIso :
    coyoneda.obj (op (CommAlgCat.of F (scaleCoordinateRing P Q b A eA.hom))) ≅
      scalePreimageFunctor P Q ⋙ forget GrpCat :=
  NatIso.ofComponents (fun R => (Equiv.ofBijective _ (scaleQuotientPoints_bijective P Q b eA R)).toIso)
    (by
      intro R S f
      apply ConcreteCategory.hom_ext
      intro p
      exact scaleQuotientPoints_natural P Q b A eA.hom f p)

/-- The represented pullback embeds as a closed subgroup of the spin group. -/
private structure RepresentedScalePreimage where
  group : AffineAlgebraicGroup F
  inclusion : group.val ⟶ G.val
  closed : IsClosedImmersion inclusion.hom.hom.left
  points : (groupPointsFunctor F).obj group.val ≅ scalePreimageFunctor P Q
  comparison : points.hom ≫ scalePreimageProjection P Q = (groupPointsFunctor F).map inclusion

private def representScalePreimage : RepresentedScalePreimage P Q := by
  let A := affineCoordinates ⟨G.val.X, G.property⟩
  let eA := A.property.2.some
  let C := CommAlgCat.of F (scaleCoordinateRing P Q b A.val eA.hom)
  letI := A.property.1
  let X := affineSpectrum C inferInstance
  let eX := spectrumPoints C X.val (Iso.refl _)
  let e := eX.symm ≪≫ scaleQuotientPointsIso P Q b eA
  let H := groupFromPoints X (scalePreimageFunctor P Q) e
  let iH := groupFromPointsIso X (scalePreimageFunctor P Q) e
  let j := iH.hom ≫ scalePreimageProjection P Q
  let E := LinearAlgebraicGroups.groupHomEquiv H.val G.val H.property.1
  let i := E.symm j
  have hi : (groupPointsFunctor F).map i = j := E.apply_symm_apply j
  let q := scaleQuotientHom P Q b A.val eA.hom
  have hqi : i.hom.hom = (testSpec F).map q.op ≫ eA.hom := by
    let z : ((groupPointsFunctor F).obj H.val).obj C := 𝟙 H.val.X
    have h := congrArg (fun f => f.app C z) hi
    have hX : eX.hom.app C (𝟙 C) = (𝟙 H.val.X : Points X.val C) := by
      change (testSpec F).map (𝟙 (op C)) ≫ 𝟙 ((testSpec F).obj (op C)) = 𝟙 ((testSpec F).obj (op C))
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    have hC : eX.inv.app C (𝟙 H.val.X : Points X.val C) = 𝟙 C := by
      rw [← hX]
      exact (eX.app C).toEquiv.symm_apply_apply _
    change (𝟙 H.val.X) ≫ i.hom.hom =
      (scaleQuotientPoints P Q b A.val eA.hom C (eX.inv.app C (𝟙 H.val.X))).val.1 at h
    rw [Category.id_comp, hC, scaleQuotientPoints_first, Category.comp_id] at h
    exact h
  refine ⟨H, i, ?_, iH, hi.symm⟩
  rw [hqi]
  change IsClosedImmersion (((testSpec F).map q.op).left ≫ eA.hom.left)
  have : IsIso eA.hom.left := by
    change IsIso ((Over.forget _).map eA.hom)
    infer_instance
  have : IsClosedImmersion ((testSpec F).map q.op).left :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom q.hom.toRingHom)
      (scaleQuotient_surjective P Q b A.val eA.hom)
  exact IsClosedImmersion.comp _ _

end ScaleRepresentation

section QuaternionCorners

open Matrix
open scoped TensorProduct
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (isCentralSimple degree)


section CornerEndomorphisms

variable {k C V : Type u} {ι : Type v} [Field k] [Ring C] [Algebra k C] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (E : Matrix ι ι C ≃ₐ[k] Module.End k V) (i : ι)

private abbrev cornerProjection : Module.End k V := E (Matrix.single i i 1)

private abbrev cornerSpace : Submodule k V := LinearMap.range (cornerProjection E i)

private theorem cornerProjection_mul_self : cornerProjection E i * cornerProjection E i = cornerProjection E i := by
  rw [← map_mul]
  simp

private theorem cornerProjection_on_range (x : cornerSpace E i) : cornerProjection E i x.val = x.val := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact DFunLike.congr_fun (cornerProjection_mul_self E i) y

private def cornerEndomorphism (a : C) : Module.End k (cornerSpace E i) :=
  ((E (Matrix.single i i a)).comp (cornerSpace E i).subtype).codRestrict (cornerSpace E i) (by
    intro x
    refine ⟨E (Matrix.single i i a) x.val, ?_⟩
    have h : E (Matrix.single i i (1 : C)) * E (Matrix.single i i a) = E (Matrix.single i i a) := by
      rw [← map_mul, Matrix.single_mul_single_same, one_mul]
    exact DFunLike.congr_fun h x.val)

private theorem cornerEndomorphism_apply (a : C) (x : cornerSpace E i) :
    (cornerEndomorphism E i a x).val = E (Matrix.single i i a) x.val := rfl

private def cornerEndomorphismHom : C →ₐ[k] Module.End k (cornerSpace E i) := by
  apply AlgHom.mk' ({
    toFun := cornerEndomorphism E i
    map_zero' := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change E (Matrix.single i i 0) x.val = 0
      simp
    map_one' := by
      apply LinearMap.ext
      intro x
      exact Subtype.ext (cornerProjection_on_range E i x)
    map_add' := by
      intro a b
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change E (Matrix.single i i (a + b)) x.val = E (Matrix.single i i a) x.val + E (Matrix.single i i b) x.val
      rw [Matrix.single_add, map_add, LinearMap.add_apply]
    map_mul' := by
      intro a b
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change E (Matrix.single i i (a * b)) x.val = E (Matrix.single i i a) (E (Matrix.single i i b) x.val)
      rw [← Matrix.single_mul_single_same a i i i b, map_mul]
      rfl } : C →+* Module.End k (cornerSpace E i))
  intro r a
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change E (Matrix.single i i (r • a)) x.val = r • E (Matrix.single i i a) x.val
  rw [← Matrix.smul_single, map_smul, LinearMap.smul_apply]

private theorem cornerEndomorphism_injective : Function.Injective (cornerEndomorphismHom E i) := by
  intro a b hab
  have h (c : C) : E (Matrix.single i i c) * cornerProjection E i = E (Matrix.single i i c) := by
    rw [← map_mul, Matrix.single_mul_single_same, mul_one]
  have h' : Matrix.single i i a = Matrix.single i i b := by
    apply E.injective
    apply LinearMap.ext
    intro x
    let z : cornerSpace E i := ⟨cornerProjection E i x, ⟨x, rfl⟩⟩
    have h₁ := congrArg (fun f : Module.End k (cornerSpace E i) => (f z).val) hab
    change E (Matrix.single i i a) (cornerProjection E i x) = E (Matrix.single i i b) (cornerProjection E i x) at h₁
    exact (DFunLike.congr_fun (h a) x).symm.trans (h₁.trans (DFunLike.congr_fun (h b) x))
  have he := congrArg (fun M : Matrix ι ι C => M i i) h'
  simpa using he

private theorem cornerEndomorphism_surjective : Function.Surjective (cornerEndomorphismHom E i) := by
  intro f
  let p := cornerProjection E i
  let U := cornerSpace E i
  let l : Module.End k V := U.subtype.comp (f.comp p.rangeRestrict)
  let M := E.symm l
  have hpl : p * l = l := by
    apply LinearMap.ext
    intro x
    exact cornerProjection_on_range E i (f (p.rangeRestrict x))
  have hlp : l * p = l := by
    apply LinearMap.ext
    intro x
    have h : p.rangeRestrict (p x) = p.rangeRestrict x :=
      Subtype.ext (DFunLike.congr_fun (cornerProjection_mul_self E i) x)
    exact congrArg (fun z => (f z).val) h
  have hm : Matrix.single i i (M i i) = M := by
    have hs : Matrix.single i i (1 : C) * M * Matrix.single i i 1 = Matrix.single i i (M i i) := by simp
    rw [← hs]
    apply E.injective
    rw [map_mul, map_mul, show E M = l from E.apply_symm_apply _, ← show p = E (Matrix.single i i 1) from rfl, hpl, hlp]
  refine ⟨M i i, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change E (Matrix.single i i (M i i)) x.val = (f x).val
  rw [hm, E.apply_symm_apply]
  exact congrArg (fun z => (f z).val) (Subtype.ext (cornerProjection_on_range E i x))

/-- A diagonal corner of the split endomorphism algebra acts on the image of its idempotent. -/
private def cornerEndomorphismEquiv : C ≃ₐ[k] Module.End k (cornerSpace E i) :=
  AlgEquiv.ofBijective (cornerEndomorphismHom E i)
    ⟨cornerEndomorphism_injective E i, cornerEndomorphism_surjective E i⟩

end CornerEndomorphisms

section QuaternionSplitting

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d)

private abbrev splitQuaternionBlock : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (K ⊗[F] B) ≃ₐ[K]
    Module.End K ((I ⊕ I) → K) :=
  ((Q.matrixAt (CommAlgCat.of F K)).symm.trans D.splitting).trans Matrix.toLinAlgEquiv'

private theorem quaternionCorner_finrank (hd : degree F B = 2) (i : QuaternionPairIndex d) :
    Module.finrank K (cornerSpace (splitQuaternionBlock Q) i) = 2 := by
  let U := cornerSpace (splitQuaternionBlock Q) i
  let e := cornerEndomorphismEquiv (splitQuaternionBlock Q) i
  let b := Module.finBasis K U
  have hdim : Module.finrank K (K ⊗[F] B) = 4 := by
    have hd' : RM03.CSA.degree F B = 2 := hd
    rw [RM03.CSA.finrank_baseChange hB, RM03.CSA.finrank_eq_degree_sq hB, hd']
    decide
  rw [e.toLinearEquiv.finrank_eq, (LinearMap.toMatrixAlgEquiv b).toLinearEquiv.finrank_eq,
    Module.finrank_matrix] at hdim
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hdim
  change Module.finrank K U = 2
  nlinarith

private def splitQuaternionEquiv (hd : degree F B = 2) (i : QuaternionPairIndex d) :
    (K ⊗[F] B) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  let b := (Module.finBasis K (cornerSpace (splitQuaternionBlock Q) i)).reindex
    (finCongr (quaternionCorner_finrank Q hd i))
  (cornerEndomorphismEquiv (splitQuaternionBlock Q) i).trans (LinearMap.toMatrixAlgEquiv b)

end QuaternionSplitting
end QuaternionCorners

section QuadraticPairComparison

open CliffordAlgebra Matrix
open scoped TensorProduct Matrix
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (degree reducedCharpoly)


section SplitQuadraticForm

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  (D : DescendedQuadraticPair ρ)

private theorem trace_descendedMatrix (x : ρ.fixedSubalgebra) :
    algebraMap F K (-(reducedCharpoly D.centralSimple x).coeff (degree F ρ.fixedSubalgebra - 1)) =
      (D.splitting (1 ⊗ₜ[F] x)).trace := by
  have hd : Fintype.card (I ⊕ I) = degree F ρ.fixedSubalgebra := by
    rw [Fintype.card_sum, D.degree, two_mul]
  let j := (Fintype.equivFin (I ⊕ I)).trans (finCongr hd)
  let E := D.splitting.trans (Matrix.reindexAlgEquiv K K j)
  calc
    _ = (E (1 ⊗ₜ[F] x)).trace :=
      by
        let : Nonempty (Fin (degree F ρ.fixedSubalgebra)) := ⟨⟨0, RM03.CSA.degree_pos D.centralSimple⟩⟩
        rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
        have h := congrArg (fun p : Polynomial K => -(p.coeff (degree F ρ.fixedSubalgebra - 1)))
          (RM03.CSA.reducedCharpoly_map D.centralSimple x E)
        rw [Polynomial.coeff_map, ← map_neg] at h
        exact h
    _ = _ := by
      change (∑ i, D.splitting (1 ⊗ₜ[F] x) (j.symm i) (j.symm i)) =
        ∑ i, D.splitting (1 ⊗ₜ[F] x) i i
      exact j.symm.sum_comp (fun i => D.splitting (1 ⊗ₜ[F] x) i i)

private theorem evaluate_semitrace_lift (ell : ρ.fixedSubalgebra)
    (h : ∀ s : symmetricPart D.involution, D.semitrace s =
      -(reducedCharpoly D.centralSimple (ell * s.val)).coeff (degree F ρ.fixedSubalgebra - 1))
    (hsplit : QuadraticPairScalarExtension.{u}) :
    ∀ x : selfAdjoint (hyperbolicGram I K),
      (D.splitting (1 ⊗ₜ[F] ell) * x.val).trace = semitrace (hyperbolicGram I K) (hyperbolicProjection I K) x := by
  obtain ⟨E, hE, _, Eσ, hEσ, htrace⟩ := hsplit D K
  have he (x : K ⊗[F] ρ.fixedSubalgebra) : E x = D.splitting x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul a x => rw [hE, D.splittingFormula]; simp
  intro x
  obtain ⟨y, rfl⟩ := Eσ.surjective x
  rw [htrace, hEσ, he]
  induction y using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, mul_add, trace_add, ha, hb]
  | tmul r s =>
    change (D.splitting (1 ⊗ₜ[F] ell) * D.splitting (r ⊗ₜ[F] s.val)).trace =
      TensorProduct.AlgebraTensorModule.rid F K K (r ⊗ₜ[F] D.semitrace s)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, D.splittingFormula, trace_smul,
      TensorProduct.AlgebraTensorModule.rid_tmul, h]
    have ht := trace_descendedMatrix D (ell * s.val)
    rw [D.splittingFormula, one_smul] at ht
    change r • (ell * s.val).val.trace = _
    rw [← ht]
    simp [Algebra.smul_def, mul_comm]

private theorem hyperbolicGram_properties : (hyperbolicGram I K).transpose = hyperbolicGram I K ∧
    hyperbolicGram I K * hyperbolicGram I K = 1 := by
  constructor
  · rw [hyperbolicGram, Matrix.fromBlocks_transpose]
    simp
  · simp [hyperbolicGram, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

/-- The semitrace representative in the quaternion presentation evaluates to the
actual split quadratic form, including its diagonal in characteristic two. -/
private theorem splitQuadraticForm_from_semitrace (h₂ : (2 : K) = 0)
    (ell : ρ.fixedSubalgebra)
    (h : ∀ s : symmetricPart D.involution, D.semitrace s =
      -(reducedCharpoly D.centralSimple (ell * s.val)).coeff (degree F ρ.fixedSubalgebra - 1))
    (hscalar : QuadraticPairScalarExtension.{u}) (htrace : TraceOrthogonality.{u})
    (hsplit : SplitSemitrace.{u}) (v : (I ⊕ I) → K) :
    diagonalValue (hyperbolicGram I K * D.splitting (1 ⊗ₜ[F] ell)) v =
      LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels.hyperbolicForm I K v := by
  let J := hyperbolicGram I K
  let M := D.splitting (1 ⊗ₜ[F] ell)
  let L := hyperbolicProjection I K
  have hz (x : selfAdjoint J) : semitrace J (M - L) x = 0 := by
    change ((M - L) * x.val).trace = 0
    rw [sub_mul, trace_sub]
    exact sub_eq_zero.mpr (evaluate_semitrace_lift D ell h hscalar x)
  obtain ⟨hJT, hJ⟩ := hyperbolicGram_properties (I := I) (K := K)
  have hv := ((htrace h₂ J (M - L) hJT hJ).mp hz).1 v
  have he : diagonalValue (J * M) v = diagonalValue (J * L) v := by
    rw [mul_sub] at hv
    exact sub_eq_zero.mp (by simpa [diagonalValue, Matrix.sub_mulVec, dotProduct_sub] using hv)
  exact he.trans ((hsplit I K h₂).2.1 v)

end SplitQuadraticForm
end QuadraticPairComparison

section ScaleCoordinateRing

open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open Polynomial Matrix
open scoped Matrix


section ScaleGeometry

variable (F : Type u) [Field F]

private def splitScaleMatrix : Matrix (Fin 2) (Fin 2) (SplitScaleAffineRing F) :=
  let of := AdjoinRoot.of (splitScaleRelation F)
  !![of X, of (C (MvPolynomial.X 0)); of (C (MvPolynomial.X 1)), AdjoinRoot.root (splitScaleRelation F)]

private theorem splitScaleMatrix_det : (splitScaleMatrix F).det = 1 := by
  let r := splitScaleRelation F
  have h := AdjoinRoot.eval₂_root r
  unfold r splitScaleRelation at h
  simp only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_one, eval₂_C, eval₂_X, map_add, map_mul, map_one] at h
  rw [Matrix.det_fin_two]
  change AdjoinRoot.of r X * AdjoinRoot.root r -
    AdjoinRoot.of r (C (MvPolynomial.X 0)) * AdjoinRoot.of r (C (MvPolynomial.X 1)) = 1
  change AdjoinRoot.of r X * AdjoinRoot.root r -
    (AdjoinRoot.of r (C (MvPolynomial.X 0)) * AdjoinRoot.of r (C (MvPolynomial.X 1)) + 1) = 0 at h
  linear_combination h

variable {F} {R : Type u} [CommRing R] [Algebra F R]

private abbrev splitScaleLocMap : SplitScaleAffineRing F →ₐ[F] SplitScaleCoordinateRing F :=
  IsScalarTower.toAlgHom F (SplitScaleAffineRing F) (SplitScaleCoordinateRing F)

private def coordinateScaleUnit : (SplitScaleCoordinateRing F)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := SplitScaleCoordinateRing F) (splitScaleVariable F)).unit

private theorem coordinateScaleUnit_val : (coordinateScaleUnit (F := F)).val = splitScaleLocMap (splitScaleVariable F) :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := SplitScaleCoordinateRing F) (splitScaleVariable F)).unit_spec

private def evaluateSplitCoordinates (f : SplitScaleCoordinateRing F →ₐ[F] R) :
    Matrix.SpecialLinearGroup (Fin 2) R × Rˣ :=
  (⟨(splitScaleMatrix F).map (f.comp splitScaleLocMap), by
      change ((f.comp splitScaleLocMap).toRingHom.mapMatrix (splitScaleMatrix F)).det = 1
      rw [← RingHom.map_det, splitScaleMatrix_det, map_one]⟩,
    Units.map f.toMonoidHom coordinateScaleUnit)

private def splitScaleCoefficients (M : Matrix (Fin 2) (Fin 2) R) (s : R) :
    Polynomial (MvPolynomial (Fin 3) F) →ₐ[F] R :=
  eval₂AlgHom (MvPolynomial.aeval ![M 0 1, M 1 0, s]) (M 0 0) fun _ => Commute.all _ _

private theorem splitScaleCoefficients_C (M : Matrix (Fin 2) (Fin 2) R) (s : R)
    (i : Fin 3) : splitScaleCoefficients (F := F) M s (C (MvPolynomial.X i)) = ![M 0 1, M 1 0, s] i := by
  change eval₂ (MvPolynomial.aeval (R := F) ![M 0 1, M 1 0, s]).toRingHom
    (M 0 0) (C (MvPolynomial.X i)) = _
  rw [eval₂_C]
  exact MvPolynomial.aeval_X _ _

private def liftSplitAffine (M : Matrix.SpecialLinearGroup (Fin 2) R) (s : Rˣ) :
    SplitScaleAffineRing F →ₐ[F] R :=
  AdjoinRoot.liftAlgHom (splitScaleRelation F) (splitScaleCoefficients M.val s.val) (M.val 1 1) (by
    have h := M.property
    rw [Matrix.det_fin_two] at h
    rw [splitScaleRelation, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_C]
    change splitScaleCoefficients M.val s.val X * M.val 1 1 -
      splitScaleCoefficients M.val s.val (C (MvPolynomial.X 0 * MvPolynomial.X 1 + 1)) = 0
    rw [show splitScaleCoefficients (F := F) M.val s.val X = M.val 0 0 from eval₂_X _ _,
      C.map_add, C.map_mul, C.map_one, map_add, map_mul, map_one,
      splitScaleCoefficients_C, splitScaleCoefficients_C]
    change M.val 0 0 * M.val 1 1 - (M.val 0 1 * M.val 1 0 + 1) = 0
    rw [← sub_sub, h, sub_self])

private theorem liftSplitAffine_variable (M : Matrix.SpecialLinearGroup (Fin 2) R) (s : Rˣ) :
    liftSplitAffine M s (splitScaleVariable F) = s.val := by
  rw [liftSplitAffine, AdjoinRoot.liftAlgHom_of, splitScaleCoefficients_C]
  rfl

private theorem liftSplitAffine_matrix (M : Matrix.SpecialLinearGroup (Fin 2) R) (s : Rˣ) :
    (splitScaleMatrix F).map (liftSplitAffine M s) = M.val := by
  ext i j
  fin_cases i <;> fin_cases j
  · change liftSplitAffine M s (AdjoinRoot.of (splitScaleRelation F) X) = M.val 0 0
    rw [liftSplitAffine, AdjoinRoot.liftAlgHom_of]
    exact eval₂_X _ _
  · change liftSplitAffine M s (AdjoinRoot.of (splitScaleRelation F) (C (MvPolynomial.X 0))) = M.val 0 1
    rw [liftSplitAffine, AdjoinRoot.liftAlgHom_of, splitScaleCoefficients_C]
    rfl
  · change liftSplitAffine M s (AdjoinRoot.of (splitScaleRelation F) (C (MvPolynomial.X 1))) = M.val 1 0
    rw [liftSplitAffine, AdjoinRoot.liftAlgHom_of, splitScaleCoefficients_C]
    rfl
  · change liftSplitAffine M s (AdjoinRoot.root (splitScaleRelation F)) = M.val 1 1
    rw [liftSplitAffine, AdjoinRoot.liftAlgHom_root]

private def liftSplitCoordinates (p : Matrix.SpecialLinearGroup (Fin 2) R × Rˣ) :
    SplitScaleCoordinateRing F →ₐ[F] R :=
  IsLocalization.Away.liftAlgHom (splitScaleVariable F)
    (f := liftSplitAffine p.1 p.2) (by rw [liftSplitAffine_variable]; exact p.2.isUnit)

private theorem liftSplitCoordinates_apply (p : Matrix.SpecialLinearGroup (Fin 2) R × Rˣ)
    (x : SplitScaleAffineRing F) : liftSplitCoordinates (F := F) p (splitScaleLocMap x) = liftSplitAffine p.1 p.2 x :=
  IsLocalization.Away.lift_eq _ (by
    change IsUnit (liftSplitAffine p.1 p.2 (splitScaleVariable F))
    rw [liftSplitAffine_variable]
    exact p.2.isUnit) _

private theorem splitScaleAffine_ext {f g : SplitScaleAffineRing F →ₐ[F] R}
    (hM : (splitScaleMatrix F).map f = (splitScaleMatrix F).map g)
    (hs : f (splitScaleVariable F) = g (splitScaleVariable F)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext'
    · apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) hM
      · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) hM
      · exact hs
    · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) hM
  · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 1) hM

private theorem splitScaleCoordinate_ext {f g : SplitScaleCoordinateRing F →ₐ[F] R}
    (hm : (evaluateSplitCoordinates f).1 = (evaluateSplitCoordinates g).1)
    (hs : (evaluateSplitCoordinates f).2 = (evaluateSplitCoordinates g).2) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (splitScaleVariable F))
  apply splitScaleAffine_ext
  · exact congrArg Subtype.val hm
  · change f (splitScaleLocMap (splitScaleVariable F)) = g (splitScaleLocMap (splitScaleVariable F))
    rw [← coordinateScaleUnit_val]
    exact congrArg Units.val hs

private theorem evaluate_liftSplitCoordinates (p : Matrix.SpecialLinearGroup (Fin 2) R × Rˣ) :
    evaluateSplitCoordinates (liftSplitCoordinates (F := F) p) = p := by
  refine Prod.ext (Subtype.ext ?_) (Units.ext ?_)
  · change (splitScaleMatrix F).map ((liftSplitCoordinates (F := F) p).comp splitScaleLocMap) = p.1.val
    have h : (liftSplitCoordinates (F := F) p).comp splitScaleLocMap = liftSplitAffine p.1 p.2 :=
      AlgHom.ext (liftSplitCoordinates_apply p)
    rw [h, liftSplitAffine_matrix]
  · change liftSplitCoordinates (F := F) p coordinateScaleUnit.val = p.2.val
    rw [coordinateScaleUnit_val, liftSplitCoordinates_apply, liftSplitAffine_variable]

/-- The split affine ring realizes determinant-one matrix coordinates and a unit. -/
private def splitScaleCoordinateEquiv :
    (SplitScaleCoordinateRing F →ₐ[F] R) ≃ (Matrix.SpecialLinearGroup (Fin 2) R × Rˣ) where
  toFun := evaluateSplitCoordinates
  invFun := liftSplitCoordinates
  left_inv f := splitScaleCoordinate_ext
    (congrArg Prod.fst (evaluate_liftSplitCoordinates (evaluateSplitCoordinates f)))
    (congrArg Prod.snd (evaluate_liftSplitCoordinates (evaluateSplitCoordinates f)))
  right_inv := evaluate_liftSplitCoordinates

private theorem splitScaleCoordinateEquiv_natural {S : Type u} [CommRing S] [Algebra F S]
    (g : R →ₐ[F] S) (f : SplitScaleCoordinateRing F →ₐ[F] R) :
    splitScaleCoordinateEquiv (g.comp f) =
      (Matrix.SpecialLinearGroup.map g.toRingHom (splitScaleCoordinateEquiv f).1,
        Units.map g.toMonoidHom (splitScaleCoordinateEquiv f).2) := by
  refine Prod.ext (Subtype.ext ?_) (Units.ext ?_)
  · ext i j
    rfl
  · rfl

open private scaleRow_det scaleRow_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open LinearAlgebraicGroups.Albert.SplitSpinSpecification (scaleRow)

private theorem isUnit_of_squareZero_quotient {A : Type u} [CommRing A] (J : Ideal A)
    (hJ : J ^ 2 = ⊥) (x : A) (hx : IsUnit (Ideal.Quotient.mk J x)) : IsUnit x := by
  let v := hx.unit
  have hv : v.val = Ideal.Quotient.mk J x := hx.unit_spec
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (v⁻¹ : (A ⧸ J)ˣ).val
  have h : x * y - 1 ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, map_one, hy, ← hv, Units.mul_inv, sub_self]
  have hz : (x * y - 1) ^ 2 = 0 := by
    have hm : (x * y - 1) * (x * y - 1) ∈ J * J := Ideal.mul_mem_mul h h
    simpa [← pow_two, hJ] using hm
  have hnil : IsNilpotent (x * y - 1) := ⟨2, hz⟩
  exact isUnit_of_mul_isUnit_left (by simpa using hnil.isUnit_add_one : IsUnit (x * y))

private theorem splitScaleCoordinateFormallySmooth : Algebra.FormallySmooth F (SplitScaleCoordinateRing F) := by
  apply Algebra.FormallySmooth.iff_comp_surjective.mpr
  intro A _ _ J hJ f
  let q := Ideal.Quotient.mkₐ F J
  let p := splitScaleCoordinateEquiv f
  choose m hm using fun i j => Ideal.Quotient.mk_surjective (p.1.val i j)
  let M : Matrix (Fin 2) (Fin 2) A := Matrix.of m
  have hM : M.map q = p.1.val := Matrix.ext hm
  have hdet : q M.det = 1 := by
    change q.toRingHom M.det = 1
    rw [RingHom.map_det]
    exact (congrArg Matrix.det hM).trans p.1.property
  have h : IsUnit M.det := isUnit_of_squareZero_quotient J hJ _ (by
    change IsUnit (q M.det)
    rw [hdet]
    exact isUnit_one)
  let v := h.unit
  have hv : v.val = M.det := h.unit_spec
  let N := scaleRow 0 v.inv M
  have hN : N.det = 1 := by
    rw [scaleRow_det, ← hv]
    exact v.inv_val
  have hq : q v.inv = 1 := by
    have hq' : Units.map q.toMonoidHom v = 1 := Units.ext (by
      change q v.val = 1
      rw [hv, hdet])
    exact congrArg Units.inv hq'
  have hNm : N.map q = p.1.val := by
    change (scaleRow 0 v.inv M).map q.toRingHom = _
    rw [scaleRow_map, show q.toRingHom v.inv = 1 from hq]
    change scaleRow 0 1 (M.map q) = _
    rw [hM]
    simp [scaleRow]
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective p.2.val
  have hu : IsUnit s := isUnit_of_squareZero_quotient J hJ _ (hs ▸ p.2.isUnit)
  refine ⟨splitScaleCoordinateEquiv.symm (⟨N, hN⟩, hu.unit), ?_⟩
  apply splitScaleCoordinateEquiv.injective
  rw [splitScaleCoordinateEquiv_natural, Equiv.apply_symm_apply]
  exact Prod.ext (Subtype.ext hNm) (Units.ext (by
    change q hu.unit.val = p.2.val
    exact (congrArg q hu.unit_spec).trans hs))

private theorem splitScaleCoordinateSmooth (F : Type u) [Field F] :
    Algebra.Smooth F (SplitScaleCoordinateRing F) := by
  let U := MvPolynomial (Fin 3) F
  have : Algebra.FiniteType F (Polynomial U) :=
    Algebra.FiniteType.trans (S := U) inferInstance inferInstance
  have : Algebra.FiniteType F (SplitScaleAffineRing F) :=
    Algebra.FiniteType.trans (S := Polynomial U) inferInstance inferInstance
  have : Algebra.FiniteType F (SplitScaleCoordinateRing F) :=
    Algebra.FiniteType.trans (S := SplitScaleAffineRing F) inferInstance inferInstance
  exact ⟨splitScaleCoordinateFormallySmooth, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end ScaleGeometry

end ScaleCoordinateRing

section QuaternionPlaneMatrices

open Matrix
open scoped Matrix TensorProduct
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair symmetricPart)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (antiValue dagger hermitianValue Involution)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (isCentralSimple degree reducedCharpoly)


section QuaternionPlane

variable {d : ℕ}

private abbrev leftLine (d : ℕ) : QuaternionPairIndex d := Sum.inl 0
private abbrev rightLine (d : ℕ) : QuaternionPairIndex d := Sum.inl 1

variable {C : Type u} [Ring C] (W : Matrix (Fin d) (Fin d) C)

private theorem gram_left_row (j : QuaternionPairIndex d) :
    quaternionHyperbolicGram W (leftLine d) j = (Pi.single (rightLine d) 1 : QuaternionPairIndex d → C) j := by
  rcases j with j | j
  · fin_cases j <;> rfl
  · rfl

private theorem gram_right_row (j : QuaternionPairIndex d) :
    quaternionHyperbolicGram W (rightLine d) j = (Pi.single (leftLine d) (-1) : QuaternionPairIndex d → C) j := by
  rcases j with j | j
  · fin_cases j <;> rfl
  · rfl

private theorem gram_left_col (i : QuaternionPairIndex d) :
    quaternionHyperbolicGram W i (leftLine d) = (Pi.single (rightLine d) (-1) : QuaternionPairIndex d → C) i := by
  rcases i with i | i
  · fin_cases i <;> rfl
  · rfl

private theorem gram_right_col (i : QuaternionPairIndex d) :
    quaternionHyperbolicGram W i (rightLine d) = (Pi.single (leftLine d) 1 : QuaternionPairIndex d → C) i := by
  rcases i with i | i
  · fin_cases i <;> rfl
  · rfl

private theorem gram_mul_leftSingle (j : QuaternionPairIndex d) (x : C) :
    quaternionHyperbolicGram W * Matrix.single (leftLine d) j x = Matrix.single (rightLine d) j (-x) := by
  ext a b
  by_cases h : b = j
  · subst b
    rw [Matrix.mul_single_apply_same, gram_left_col]
    by_cases h : a = rightLine d
    · subst a
      simp
    · simp [Matrix.single, Matrix.of_apply, Ne.symm h]
  · rw [Matrix.mul_single_apply_of_ne x _ _ _ _ h]
    simp [Matrix.single, Matrix.of_apply, Ne.symm h]

private theorem gram_mul_rightSingle (j : QuaternionPairIndex d) (x : C) :
    quaternionHyperbolicGram W * Matrix.single (rightLine d) j x = Matrix.single (leftLine d) j x := by
  ext a b
  by_cases h : b = j
  · subst b
    rw [Matrix.mul_single_apply_same, gram_right_col]
    by_cases h : a = leftLine d
    · subst a
      simp
    · simp [Matrix.single, Matrix.of_apply, Ne.symm h]
  · rw [Matrix.mul_single_apply_of_ne x _ _ _ _ h]
    simp [Matrix.single, Matrix.of_apply, Ne.symm h]

private theorem leftSingle_mul_gram (i : QuaternionPairIndex d) (x : C) :
    Matrix.single i (leftLine d) x * quaternionHyperbolicGram W = Matrix.single i (rightLine d) x := by
  ext a b
  by_cases h : a = i
  · subst a
    rw [Matrix.single_mul_apply_same, gram_left_row]
    by_cases h : b = rightLine d
    · subst b
      simp
    · simp [Matrix.single, Matrix.of_apply, Ne.symm h]
  · rw [Matrix.single_mul_apply_of_ne x _ _ _ _ h]
    simp [Matrix.single, Matrix.of_apply, Ne.symm h]

private theorem rightSingle_mul_gram (i : QuaternionPairIndex d) (x : C) :
    Matrix.single i (rightLine d) x * quaternionHyperbolicGram W = Matrix.single i (leftLine d) (-x) := by
  ext a b
  by_cases h : a = i
  · subst a
    rw [Matrix.single_mul_apply_same, gram_right_row]
    by_cases h : b = leftLine d
    · subst b
      simp
    · simp [Matrix.single, Matrix.of_apply, Ne.symm h]
  · rw [Matrix.single_mul_apply_of_ne x _ _ _ _ h]
    simp [Matrix.single, Matrix.of_apply, Ne.symm h]

private theorem quaternionGram_cancel (U : (Matrix (Fin d) (Fin d) C)ˣ)
    {X Y : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) C}
    (h : quaternionHyperbolicGram U.val * X = quaternionHyperbolicGram U.val * Y) : X = Y := by
  let inv : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) C := Matrix.fromBlocks !![0, -1; 1, 0] 0 0 U.inv
  have hplane : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) C) * !![0, 1; -1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hinv : inv * quaternionHyperbolicGram U.val = 1 := by
    simp [inv, quaternionHyperbolicGram, fromBlocks_multiply, hplane, Matrix.fromBlocks_one]
  have h' := congrArg (inv * ·) h
  simpa only [← mul_assoc, hinv, one_mul] using h'

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} (Q : QuaternionHyperbolicPresentation D hB d)

private theorem dagger_single {ι : Type*} [DecidableEq ι] (s : Involution F B) (i j : ι) (x : B) :
    dagger s.anti (Matrix.single i j x) = Matrix.single j i (antiValue s.anti x) := by
  ext a b
  by_cases ha : j = a <;> by_cases hb : i = b <;>
    simp [dagger, Matrix.single, Matrix.of_apply, ha, hb, antiValue]

private def pairEntry (i j : QuaternionPairIndex d) (x : B) : ρ.fixedSubalgebra :=
  Q.matrixModel.symm (Matrix.single i j x)

private theorem adjoint_leftProjection (x : B) :
    D.involution.toLinearMap (pairEntry Q (leftLine d) (leftLine d) x) =
      pairEntry Q (rightLine d) (rightLine d) (antiValue Q.conjugation.anti x) := by
  apply Q.matrixModel.injective
  apply quaternionGram_cancel Q.complement
  rw [Q.adjoint, pairEntry, pairEntry, Q.matrixModel.apply_symm_apply, Q.matrixModel.apply_symm_apply,
    dagger_single, leftSingle_mul_gram, gram_mul_rightSingle]

private theorem adjoint_rightProjection (x : B) :
    D.involution.toLinearMap (pairEntry Q (rightLine d) (rightLine d) x) =
      pairEntry Q (leftLine d) (leftLine d) (antiValue Q.conjugation.anti x) := by
  apply Q.matrixModel.injective
  apply quaternionGram_cancel Q.complement
  rw [Q.adjoint, pairEntry, pairEntry, Q.matrixModel.apply_symm_apply, Q.matrixModel.apply_symm_apply,
    dagger_single, rightSingle_mul_gram, gram_mul_leftSingle]

private theorem adjoint_leftToRight (x : B) :
    D.involution.toLinearMap (pairEntry Q (rightLine d) (leftLine d) x) =
      pairEntry Q (rightLine d) (leftLine d) (-antiValue Q.conjugation.anti x) := by
  apply Q.matrixModel.injective
  apply quaternionGram_cancel Q.complement
  rw [Q.adjoint, pairEntry, pairEntry, Q.matrixModel.apply_symm_apply, Q.matrixModel.apply_symm_apply,
    dagger_single, rightSingle_mul_gram, gram_mul_rightSingle]

private theorem adjoint_rightToLeft (x : B) :
    D.involution.toLinearMap (pairEntry Q (leftLine d) (rightLine d) x) =
      pairEntry Q (leftLine d) (rightLine d) (-antiValue Q.conjugation.anti x) := by
  apply Q.matrixModel.injective
  apply quaternionGram_cancel Q.complement
  rw [Q.adjoint, pairEntry, pairEntry, Q.matrixModel.apply_symm_apply, Q.matrixModel.apply_symm_apply,
    dagger_single, leftSingle_mul_gram, gram_mul_leftSingle, neg_neg]

private theorem quaternionHyperbolicSemitrace (h₂ : (2 : F) = 0) :
    ∃ ell : ρ.fixedSubalgebra,
      (∀ s : symmetricPart D.involution, D.semitrace s =
        -(reducedCharpoly D.centralSimple (ell * s.val)).coeff (degree F ρ.fixedSubalgebra - 1)) ∧
      Q.matrixModel ell (rightLine d) (leftLine d) ∈ Set.range (algebraMap F B) ∧
      Q.matrixModel ell (leftLine d) (rightLine d) ∈ Set.range (algebraMap F B) := by
  obtain ⟨ell, L, _, ht, hv⟩ := Q.quadratic h₂
  have hleft := hv 1 0 0
  have hright := hv 0 1 0
  let u : QuaternionPairIndex d → B := Pi.single (leftLine d) 1
  let v : QuaternionPairIndex d → B := Pi.single (rightLine d) 1
  have hu : Sum.elim (![1, 0] : Fin 2 → B) (0 : Fin d → B) = u := by
    funext i
    rcases i with i | i
    · fin_cases i <;> rfl
    · rfl
  have hv' : Sum.elim (![0, 1] : Fin 2 → B) (0 : Fin d → B) = v := by
    funext i
    rcases i with i | i
    · fin_cases i <;> rfl
    · rfl
  have h0 : hermitianValue Q.conjugation.anti Q.complement.val 0 (0 : Fin d → B) = 0 := by
    simp [hermitianValue, antiValue]
  have hab (i : QuaternionPairIndex d) :
      (fun j => antiValue Q.conjugation.anti ((Pi.single i 1 : QuaternionPairIndex d → B) j)) = Pi.single i 1 := by
    funext j
    by_cases h : j = i
    · subst j; simp [antiValue]
    · simp [Pi.single_eq_of_ne h, antiValue]
  have hl : hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val) u (Q.matrixModel ell *ᵥ u) =
      Q.matrixModel ell (rightLine d) (leftLine d) := by
    unfold hermitianValue u
    rw [hab, single_dotProduct, one_mul, Matrix.mulVec]
    simp_rw [gram_left_row]
    rw [single_dotProduct, one_mul, Matrix.mulVec_single_one]
    rfl
  have hr : hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val) v (Q.matrixModel ell *ᵥ v) =
      -Q.matrixModel ell (leftLine d) (rightLine d) := by
    unfold hermitianValue v
    rw [hab, single_dotProduct, one_mul, Matrix.mulVec]
    simp_rw [gram_right_row]
    rw [single_dotProduct, neg_one_mul, Matrix.mulVec_single_one]
    rfl
  dsimp only at hleft hright
  rw [hu, hl, Matrix.mulVec_zero, h0] at hleft
  rw [hv', hr, Matrix.mulVec_zero, h0] at hright
  simp only [mul_zero, antiValue, map_zero, MulOpposite.unop_zero, zero_mul, sub_zero, add_zero] at hleft hright
  refine ⟨ell, ht, hleft, ?_⟩
  obtain ⟨c, hc⟩ := hright
  exact ⟨-c, by rw [map_neg, hc, neg_neg]⟩

end QuaternionPlane
end QuaternionPlaneMatrices

section SplitGeometryTransfer

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
open LinearAlgebraicGroups.WeilRestriction (spectrumPullbackIso)

/-- Obtain the coordinate-ring comparison from natural bijections of algebra points. -/
private def algebraEquivOfPoints {k C D : Type u} [CommRing k] [CommRing C] [CommRing D]
    [Algebra k C] [Algebra k D]
    (η : ∀ (A : Type u) [CommRing A] [Algebra k A], (C →ₐ[k] A) ≃ (D →ₐ[k] A))
    (hη : ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
      (q : A →ₐ[k] B) (f : C →ₐ[k] A), η B (q.comp f) = q.comp (η A f)) : D ≃ₐ[k] C := by
  let i := η C (AlgHom.id k C)
  let j := (η D).symm (AlgHom.id k D)
  have h (A : Type u) [CommRing A] [Algebra k A] (f : C →ₐ[k] A) : η A f = f.comp i := by
    simpa [i] using hη f (AlgHom.id k C)
  have hj : j.comp i = AlgHom.id k D := (h D j).symm.trans ((η D).apply_symm_apply _)
  have hi : i.comp j = AlgHom.id k C := by
    apply (η C).injective
    rw [h C _, AlgHom.comp_assoc, hj, AlgHom.comp_id]
  exact { i with
    invFun := j
    left_inv := DFunLike.congr_fun hj
    right_inv := DFunLike.congr_fun hi }

private def splitScaleCoordinateBaseChange {k L : Type u} [Field k] [Field L] [Algebra k L] :
    SplitScaleCoordinateRing L ≃ₐ[L] L ⊗[k] SplitScaleCoordinateRing k := by
  let e (R : Type u) [CommRing R] [Algebra L R] := by
    letI : Algebra k R := ((algebraMap L R).comp (algebraMap k L)).toAlgebra
    letI : IsScalarTower k L R := IsScalarTower.of_algebraMap_eq' rfl
    exact (AlgHom.liftEquiv k L (SplitScaleCoordinateRing k) R).symm.trans
      ((splitScaleCoordinateEquiv (F := k) (R := R)).trans (splitScaleCoordinateEquiv (F := L) (R := R)).symm)
  refine algebraEquivOfPoints e ?_
  intro A B _ _ _ _ g f
  let : Algebra k A := ((algebraMap L A).comp (algebraMap k L)).toAlgebra
  let : Algebra k B := ((algebraMap L B).comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L A := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k L B := IsScalarTower.of_algebraMap_eq' rfl
  apply (splitScaleCoordinateEquiv (F := L) (R := B)).injective
  have h : (AlgHom.liftEquiv k L (SplitScaleCoordinateRing k) B).symm (g.comp f) =
      (g.restrictScalars k).comp ((AlgHom.liftEquiv k L (SplitScaleCoordinateRing k) A).symm f) :=
    AlgHom.ext fun _ => rfl
  change splitScaleCoordinateEquiv ((splitScaleCoordinateEquiv (F := L)).symm
    (splitScaleCoordinateEquiv ((AlgHom.liftEquiv k L (SplitScaleCoordinateRing k) B).symm (g.comp f)))) =
      splitScaleCoordinateEquiv (g.comp (e A f))
  rw [Equiv.apply_symm_apply, splitScaleCoordinateEquiv_natural g, h,
    splitScaleCoordinateEquiv_natural (g.restrictScalars k)]
  have he : splitScaleCoordinateEquiv (F := L) (e A f) =
      splitScaleCoordinateEquiv (F := k) ((AlgHom.liftEquiv k L (SplitScaleCoordinateRing k) A).symm f) :=
    (splitScaleCoordinateEquiv (F := L)).apply_symm_apply _
  rw [he]
  rfl

private theorem scaleCoordinateGeometricallyDomain {F K C : Type u} [Field F] [Field K]
    [Algebra F K] [FiniteDimensional F K] [CommRing C] [Algebra F C]
    (e : (K ⊗[F] C) ≃ₐ[K] SplitScaleCoordinateRing K)
    (L : Type u) [Field L] [Algebra F L] : IsDomain (L ⊗[F] C) := by
  let W := AlgebraicClosure L
  let aFW : Algebra F W := ((algebraMap L W).comp (algebraMap F L)).toAlgebra
  let : SMul F W := aFW.toSMul
  let i : K →ₐ[F] W := IsAlgClosed.lift
  let aKW : Algebra K W := i.toAlgebra
  let : SMul K W := aKW.toSMul
  let : IsScalarTower F K W := by
    exact @IsScalarTower.of_algebraMap_eq' F K W _ _ _ _ aKW aFW
      (RingHom.ext fun x => (i.commutes x).symm)
  let j : L →ₐ[F] W := ⟨algebraMap L W, fun _ => rfl⟩
  let assoc := (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid K W W).symm
    (AlgEquiv.refl : C ≃ₐ[F] C)).trans (Algebra.TensorProduct.assoc F K W W K C)
  let comp := (assoc.trans (Algebra.TensorProduct.congr (AlgEquiv.refl : W ≃ₐ[W] W) e)).trans
    (splitScaleCoordinateBaseChange (k := K) (L := W)).symm
  have : IsDomain (SplitScaleCoordinateRing W) := splitScaleCoordinateDomain W
  have : IsDomain (W ⊗[F] C) := comp.injective.isDomain comp
  let f := Algebra.TensorProduct.map j (AlgHom.id F C)
  exact Function.Injective.isDomain f
    (TensorProduct.map_injective_of_flat_flat j.toLinearMap (LinearMap.id : C →ₗ[F] C) j.injective Function.injective_id)

private theorem splitScaleGeometry {F K C : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [CommRing C] [Algebra F C]
    (e : (K ⊗[F] C) ≃ₐ[K] SplitScaleCoordinateRing K) :
    let X := (testSpec F).obj (op (CommAlgCat.of F C))
    Smooth X.hom ∧ GeometricallyConnected X.hom ∧ GeometricallyReduced X.hom := by
  let X := (testSpec F).obj (op (CommAlgCat.of F C))
  change Smooth X.hom ∧ GeometricallyConnected X.hom ∧ GeometricallyReduced X.hom
  have : Algebra.Smooth K (SplitScaleCoordinateRing K) := splitScaleCoordinateSmooth K
  have : Algebra.Smooth K (K ⊗[F] C) := Algebra.Smooth.of_equiv e.symm
  have : Algebra.Smooth F C := Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K
  constructor
  · change Smooth (Spec.map (CommRingCat.ofHom (algebraMap F C)))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr ‹Algebra.Smooth F C›
  let : ObjectProperty.IsClosedUnderIsomorphisms (@IsIntegral) :=
    ⟨fun i h => @IsIntegral.of_isIso _ _ h i.hom inferInstance⟩
  have hInt : GeometricallyIntegral X.hom := by
    rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro L _ _
    have : IsDomain (L ⊗[F] C) := scaleCoordinateGeometricallyDomain e L
    let i := spectrumPullbackIso (L := L) (CommAlgCat.of F C)
    let t := (Over.forget _).mapIso i
    have : IsIntegral ((Over.forget _).obj ((testSpec L).obj (op (CommAlgCat.of L (L ⊗[F] C))))) := by
      change IsIntegral (Spec (CommRingCat.of (L ⊗[F] C)))
      infer_instance
    exact IsIntegral.of_isIso t.inv
  refine ⟨⟨?_⟩, inferInstance⟩
  intro L _ Y Z t s h
  have : IsIntegral Z := hInt.geometrically_isIntegral Y t s h
  infer_instance

end SplitGeometryTransfer


section SplitQuaternionIsotropy

open Matrix
open scoped Matrix TensorProduct
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (antiValue)
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels (quaternionConjugate)
open LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction (reducedTrace)
open RM03.Brauer.SemilinearDescent (AlgebraAction)

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d)

private theorem quaternionTraceOne (hd : degree F B = 2) :
    ∃ x : B, x + antiValue Q.conjugation.anti x = 1 := by
  let E := splitQuaternionEquiv Q hd (leftLine d)
  have htrace (x : B) : algebraMap F K (reducedTrace hB x) = (E (1 ⊗ₜ[F] x)).trace := by
    have hx (e : (K ⊗[F] B) ≃ₐ[K] Matrix (Fin (degree F B)) (Fin (degree F B)) K) :
        algebraMap F K (reducedTrace hB x) = (e (1 ⊗ₜ[F] x)).trace := by
      let : Nonempty (Fin (degree F B)) := ⟨⟨0, RM03.CSA.degree_pos hB⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
      have h := congrArg (fun p : Polynomial K => -(p.coeff (degree F B - 1)))
        (RM03.CSA.reducedCharpoly_map hB x e)
      rw [Polynomial.coeff_map, ← map_neg] at h
      exact h
    have h' (n : ℕ) (hn : degree F B = n) (e : (K ⊗[F] B) ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
        algebraMap F K (reducedTrace hB x) = (e (1 ⊗ₜ[F] x)).trace := by
      subst n
      exact hx e
    exact h' 2 hd E
  have hex : ∃ x : B, reducedTrace hB x ≠ 0 := by
    by_contra! hz
    have h (a : K ⊗[F] B) : (E a).trace = 0 := by
      induction a using TensorProduct.inductionOn with
      | add a b ha hb => simp [ha, hb]
      | tmul r x =>
        have hr : r ⊗ₜ[F] x = r • ((1 : K) ⊗ₜ[F] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hr, map_smul, trace_smul, ← htrace, hz, map_zero, smul_zero]
    obtain ⟨a, ha⟩ := E.surjective (Matrix.single 0 0 1)
    have h := h a
    rw [ha, Matrix.trace_single_eq_same] at h
    exact one_ne_zero h
  obtain ⟨x, hx⟩ := hex
  let r := (reducedTrace hB x)⁻¹
  let y := r • x
  have hy : reducedTrace hB y = 1 := by
    apply (algebraMap F K).injective
    have hr (a : K ⊗[F] B) : E (r • a) = r • E a := (E.restrictScalars F).toLinearEquiv.map_smul r a
    rw [map_one, htrace, show y = r • x from rfl, TensorProduct.tmul_smul, hr,
      trace_smul, ← htrace, Algebra.smul_def, ← map_mul]
    simp [r, hx]
  refine ⟨y, ?_⟩
  rw [Q.canonical, quaternionConjugate, hy, map_one]
  simp [sub_eq_add_neg]

private theorem cornerOffDiagonal_alternating (hd : degree F B = 2) (h₂ : (2 : F) = 0)
    (c : F) :
    (∃ a, pairEntry Q (rightLine d) (leftLine d) (algebraMap F B c) = a + D.involution.toLinearMap a) ∧
    (∃ a, pairEntry Q (leftLine d) (rightLine d) (algebraMap F B c) = a + D.involution.toLinearMap a) := by
  obtain ⟨x, hx⟩ := quaternionTraceOne Q hd
  let z := c • x
  have hneg (a : B) : -a = a := by
    apply neg_eq_iff_add_eq_zero.mpr
    rw [← two_mul, show (2 : B) = 0 from ((map_ofNat (algebraMap F B) 2).symm.trans (by rw [h₂, map_zero])), zero_mul]
  have hbar : antiValue Q.conjugation.anti z = c • antiValue Q.conjugation.anti x := by
    change MulOpposite.unop (Q.conjugation.anti (c • x)) = _
    rw [map_smul]
    rfl
  have hz : z + -antiValue Q.conjugation.anti z = algebraMap F B c := by
    rw [hneg, hbar, ← smul_add, hx, Algebra.smul_def, mul_one]
  constructor
  · refine ⟨pairEntry Q (rightLine d) (leftLine d) z, ?_⟩
    apply Q.matrixModel.injective
    rw [adjoint_leftToRight]
    simp only [pairEntry, map_add, AlgEquiv.apply_symm_apply, ← Matrix.single_add, hz]
  · refine ⟨pairEntry Q (leftLine d) (rightLine d) z, ?_⟩
    apply Q.matrixModel.injective
    rw [adjoint_rightToLeft]
    simp only [pairEntry, map_add, AlgEquiv.apply_symm_apply, ← Matrix.single_add, hz]

omit [DecidableEq I] in
private theorem diagonalValue_pullback {A P : Matrix (I ⊕ I) (I ⊕ I) K} (v : I ⊕ I → K) :
    diagonalValue A (P *ᵥ v) = diagonalValue (P.transpose * A * P) v := by
  unfold diagonalValue
  calc
    (P *ᵥ v) ⬝ᵥ (A *ᵥ (P *ᵥ v)) = (v ᵥ* (P.transpose * A)) ⬝ᵥ (P *ᵥ v) := by
      rw [dotProduct_mulVec, vecMul_mulVec]
    _ = _ := by rw [← dotProduct_mulVec, Matrix.mulVec_mulVec]

private theorem diagonalValue_alternating (h₂ : (2 : K) = 0) (M : Matrix (I ⊕ I) (I ⊕ I) K)
    (v : I ⊕ I → K) : diagonalValue
      (hyperbolicGram I K * (M + adjoint (hyperbolicGram I K) M)) v = 0 := by
  let J := hyperbolicGram I K
  obtain ⟨hJT, hJ⟩ := hyperbolicGram_properties (I := I) (K := K)
  have he : J * adjoint J M = (J * M).transpose := by
    rw [adjoint, Matrix.transpose_mul, hJT, ← mul_assoc J, ← mul_assoc J J, hJ, one_mul]
  change diagonalValue (J * (M + adjoint J M)) v = 0
  rw [mul_add, he]
  unfold diagonalValue
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.dotProduct_transpose_mulVec, ← two_mul, h₂, zero_mul]

private theorem splitQuadratic_zero_on_projection {p l ell : ρ.fixedSubalgebra}
    (hp : D.involution.toLinearMap p = l)
    (hy : ∃ a, l * ell * p = a + D.involution.toLinearMap a)
    (h₂ : (2 : K) = 0) (v : I ⊕ I → K)
    (hform : ∀ w, diagonalValue (hyperbolicGram I K * D.splitting (1 ⊗ₜ[F] ell)) w =
      LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels.hyperbolicForm I K w) :
    LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels.hyperbolicForm I K (D.splitting (1 ⊗ₜ[F] p) *ᵥ v) = 0 := by
  let J := hyperbolicGram I K
  let P := D.splitting (1 ⊗ₜ[F] p)
  let L := D.splitting (1 ⊗ₜ[F] l)
  let M := D.splitting (1 ⊗ₜ[F] ell)
  have hsplit (x : ρ.fixedSubalgebra) :
      adjoint J (D.splitting (1 ⊗ₜ[F] x)) = D.splitting (1 ⊗ₜ[F] D.involution.toLinearMap x) :=
    (D.splittingInvolution (1 ⊗ₜ[F] x)).symm
  have hJ := (hyperbolicGram_properties (I := I) (K := K)).2
  have he : P.transpose * J = J * L := by
    have h : L = adjoint J P := by rw [hsplit, hp]
    rw [h, adjoint, ← Matrix.mul_assoc J, ← Matrix.mul_assoc J J, hJ, one_mul]
  obtain ⟨a, ha⟩ := hy
  have hs (x y : ρ.fixedSubalgebra) :
      D.splitting (1 ⊗ₜ[F] x) * D.splitting (1 ⊗ₜ[F] y) = D.splitting (1 ⊗ₜ[F] (x * y)) := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hM : L * M * P = D.splitting (1 ⊗ₜ[F] a) + adjoint J (D.splitting (1 ⊗ₜ[F] a)) := by
    change (D.splitting (1 ⊗ₜ[F] l) * D.splitting (1 ⊗ₜ[F] ell)) * D.splitting (1 ⊗ₜ[F] p) = _
    rw [hs, hs, ha, TensorProduct.tmul_add, map_add, hsplit]
  rw [← hform, diagonalValue_pullback]
  change diagonalValue (P.transpose * (J * M) * P) v = 0
  rw [← mul_assoc, he, mul_assoc J L, mul_assoc J, hM]
  exact diagonalValue_alternating h₂ _ _

private theorem cornerEntry_sandwich (ell : ρ.fixedSubalgebra) (i j : QuaternionPairIndex d) :
    pairEntry Q i i 1 * ell * pairEntry Q j j 1 = pairEntry Q i j (Q.matrixModel ell i j) := by
  apply Q.matrixModel.injective
  simp [pairEntry, Matrix.single_mul_mul_single]

/-- In characteristic two the two displayed quaternion lines are isotropic for
 the split quadratic form recovered from the actual semitrace. -/
private theorem splitQuaternionLinesIsotropic (hd : degree F B = 2) (h₂ : (2 : F) = 0)
    (hscalar : QuadraticPairScalarExtension.{u}) (htrace : TraceOrthogonality.{u})
    (hsplit : SplitSemitrace.{u}) (v : I ⊕ I → K) :
    let q := LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels.hyperbolicForm I K
    q (D.splitting (1 ⊗ₜ[F] pairEntry Q (leftLine d) (leftLine d) 1) *ᵥ v) = 0 ∧
    q (D.splitting (1 ⊗ₜ[F] pairEntry Q (rightLine d) (rightLine d) 1) *ᵥ v) = 0 := by
  obtain ⟨ell, hsem, ⟨a, ha⟩, ⟨b, hb⟩⟩ := quaternionHyperbolicSemitrace Q h₂
  have h₂K : (2 : K) = 0 := (map_ofNat (algebraMap F K) 2).symm.trans (by rw [h₂, map_zero])
  have hf := splitQuadraticForm_from_semitrace D h₂K ell hsem hscalar htrace hsplit
  have h1 : antiValue Q.conjugation.anti (1 : B) = 1 := by
    simp [antiValue]
  constructor
  · apply splitQuadratic_zero_on_projection (D := D) (h₂ := h₂K) (hform := hf)
    · rw [adjoint_leftProjection Q, h1]
    · rw [cornerEntry_sandwich Q, ← ha]
      exact (cornerOffDiagonal_alternating Q hd h₂ a).1
  · apply splitQuadratic_zero_on_projection (D := D) (h₂ := h₂K) (hform := hf)
    · rw [adjoint_rightProjection Q, h1]
    · rw [cornerEntry_sandwich Q, ← hb]
      exact (cornerOffDiagonal_alternating Q hd h₂ b).2

end SplitQuaternionIsotropy

section SplitQuaternionOddIsotropy

open Matrix
open scoped Matrix TensorProduct
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair)
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (antiValue)
open RM03.Brauer.SemilinearDescent (AlgebraAction)

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d)

private theorem hyperbolic_two_mul (v : I ⊕ I → K) :
    (2 : K) * hyperbolicForm I K v = diagonalValue (hyperbolicGram I K) v := by
  let A : Matrix (I ⊕ I) (I ⊕ I) K := Matrix.fromBlocks 0 1 0 0
  have hA : hyperbolicGram I K = A + A.transpose := by
    simp [A, hyperbolicGram, Matrix.fromBlocks_add, Matrix.fromBlocks_transpose]
  have he : hyperbolicForm I K v = diagonalValue A v := by
    rw [hyperbolicForm, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
    rfl
  rw [hA, he]
  unfold diagonalValue
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.dotProduct_transpose_mulVec, two_mul]

private theorem splitQuadratic_zero_on_orthogonal_projection {p l : ρ.fixedSubalgebra}
    (h₂ : (2 : K) ≠ 0) (hp : D.involution.toLinearMap p = l) (hlp : l * p = 0)
    (v : I ⊕ I → K) : hyperbolicForm I K (D.splitting (1 ⊗ₜ[F] p) *ᵥ v) = 0 := by
  let J := hyperbolicGram I K
  let P := D.splitting (1 ⊗ₜ[F] p)
  let L := D.splitting (1 ⊗ₜ[F] l)
  have h : L = adjoint J P := by
    change D.splitting (1 ⊗ₜ[F] l) = adjoint J (D.splitting (1 ⊗ₜ[F] p))
    rw [← D.splittingInvolution]
    exact congrArg (fun x => D.splitting (1 ⊗ₜ[F] x)) hp.symm
  have hJ := (hyperbolicGram_properties (I := I) (K := K)).2
  have he : P.transpose * J = J * L := by
    rw [h, adjoint, ← Matrix.mul_assoc J, ← Matrix.mul_assoc J J, hJ, one_mul]
  have hLP : L * P = 0 := by
    change D.splitting (1 ⊗ₜ[F] l) * D.splitting (1 ⊗ₜ[F] p) = 0
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, hlp, TensorProduct.tmul_zero, map_zero]
  apply (mul_eq_zero.mp ?_).resolve_left h₂
  change (2 : K) * hyperbolicForm I K (P *ᵥ v) = 0
  rw [hyperbolic_two_mul, diagonalValue_pullback, he, mul_assoc J, hLP, mul_zero]
  simp [diagonalValue]

/-- Both split quaternion summands are totally singular for the quadratic norm. -/
private theorem quaternionIsotropicSummands (hd : degree F B = 2)
    (hscalar : QuadraticPairScalarExtension.{u}) (htrace : TraceOrthogonality.{u})
    (hsplit : SplitSemitrace.{u}) (v : I ⊕ I → K) :
    hyperbolicForm I K (D.splitting (1 ⊗ₜ[F] pairEntry Q (leftLine d) (leftLine d) 1) *ᵥ v) = 0 ∧
    hyperbolicForm I K (D.splitting (1 ⊗ₜ[F] pairEntry Q (rightLine d) (rightLine d) 1) *ᵥ v) = 0 := by
  by_cases h₂ : (2 : F) = 0
  · exact splitQuaternionLinesIsotropic Q hd h₂ hscalar htrace hsplit v
  have h₂K : (2 : K) ≠ 0 := fun h => h₂ ((algebraMap F K).injective (by simpa only [map_ofNat, map_zero] using h))
  have h1 : antiValue Q.conjugation.anti (1 : B) = 1 := by simp [antiValue]
  have hne : leftLine d ≠ rightLine d := fun h => (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj h)
  constructor
  · apply splitQuadratic_zero_on_orthogonal_projection (D := D) (h₂ := h₂K)
    · rw [adjoint_leftProjection Q, h1]
    · apply Q.matrixModel.injective
      simp [pairEntry, Matrix.single_mul_single_of_ne (c := (1 : B)) _ _ _ hne.symm]
  · apply splitQuadratic_zero_on_orthogonal_projection (D := D) (h₂ := h₂K)
    · rw [adjoint_rightProjection Q, h1]
    · apply Q.matrixModel.injective
      simp [pairEntry, Matrix.single_mul_single_of_ne (c := (1 : B)) _ _ _ hne]

end SplitQuaternionOddIsotropy

section ScalePointDescent

open AlgebraicGeometry CategoryTheory Opposite

variable {F K C : Type u} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K] [CommRing C] [Algebra F C]

/-- Descend a normalized unit coordinate from the scalar extension. Its
agreement on all test algebras follows by evaluation at the universal point. -/
private theorem descendNormalizedUnitCoordinate [IsDomain (K ⊗[F] C)]
    (p : C →ₐ[F] F) (n : Cˣ)
    (s : ∀ (S : Type u) [CommRing S] [Algebra F S] [Algebra K S] [IsScalarTower F K S],
      (C →ₐ[F] S) → Sˣ)
    (hs : ∀ (S : Type u) [CommRing S] [Algebra F S] [Algebra K S] [IsScalarTower F K S] (f : C →ₐ[F] S),
      s S f ^ 2 = Units.map f.toMonoidHom n)
    (h₁ : s K ((Algebra.ofId F K).comp p) = 1)
    (hn : ∀ (S T : Type u) [CommRing S] [CommRing T] [Algebra F S] [Algebra F T]
      [Algebra K S] [Algebra K T] [IsScalarTower F K S] [IsScalarTower F K T]
      (f : C →ₐ[F] S) (g : S →ₐ[K] T),
      s T ((g.restrictScalars F).comp f) = Units.map g.toMonoidHom (s S f)) :
    ∃ r : Cˣ, r ^ 2 = n ∧ p r.val = 1 ∧
      ∀ (S : Type u) [CommRing S] [Algebra F S] [Algebra K S] [IsScalarTower F K S] (f : C →ₐ[F] S),
        s S f = Units.map f.toMonoidHom r := by
  let E := K ⊗[F] C
  let j : C →ₐ[F] E := scalarExtension
  let x := s E j
  have hj : Function.Injective j := Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hh : ((extendPoint (K := K) p).restrictScalars F).comp j =
      (Algebra.ofId F K).comp p := by
    apply AlgHom.ext
    intro c
    simp [j, scalarExtension, extendPoint, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]
  have hp : extendPoint p x.val = 1 := by
    have h := hn E K j (extendPoint p)
    rw [hh, h₁] at h
    exact congrArg Units.val h.symm
  obtain ⟨r, hr, _⟩ := galoisSquareRootDescent p n x hp (hs E j)
  have sq : r ^ 2 = n := by
    apply Units.ext
    apply hj
    change (Units.map j.toMonoidHom (r ^ 2)).val = (Units.map j.toMonoidHom n).val
    rw [map_pow, hr]
    exact congrArg Units.val (hs E j)
  refine ⟨r, sq, ?_, ?_⟩
  · have h : extendPoint p (j r.val) = (algebraMap F K) (p r.val) := DFunLike.congr_fun hh r.val
    apply (algebraMap F K).injective
    rw [← h, map_one]
    exact (congrArg (extendPoint p) (congrArg Units.val hr)).trans hp
  · intro S _ _ _ _ f
    let g := (AlgHom.liftEquiv F K C S) f
    have hf : (g.restrictScalars F).comp j = f := (AlgHom.liftEquiv F K C S).symm_apply_apply _
    have h := hn E S j g
    rw [hf] at h
    change s S f = Units.map g.toMonoidHom x at h
    rw [h, ← hr]
    apply Units.ext
    exact DFunLike.congr_fun hf r.val

private theorem algebraPoint_descends {R : Type u} [CommRing R] [Algebra F R]
    (f : C →ₐ[F] K ⊗[F] R) (hf : ∀ σ : K ≃ₐ[F] K, (tensorAut σ).comp f = f) :
    ∃ g : C →ₐ[F] R, (scalarExtension (K := K)).comp g = f := by
  let j : R →ₐ[F] K ⊗[F] R := scalarExtension
  have hj : Function.Injective j := Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have h (c : C) : f c ∈ j.range := by
    apply j.mem_range.mpr
    exact tensor_fixed_descends (f c) (fun σ => DFunLike.congr_fun (hf σ) c)
  let e := AlgEquiv.ofInjective j hj
  let g := e.symm.toAlgHom.comp (f.codRestrict _ h)
  refine ⟨g, AlgHom.ext fun c => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (f.codRestrict _ h c))

/-- A natural point map from an affine scheme is bijective once it becomes
bijective over a finite Galois extension and the target has injective scalar extension. -/
private theorem affinePoints_bijective_of_galois {A : TestAlgebra F}
    {Y : TestAlgebra F ⥤ Type u} (τ : coyoneda.obj (op A) ⟶ Y)
    (hK : ∀ (S : TestAlgebra F) [Algebra K S] [IsScalarTower F K S], Function.Bijective (τ.app S))
    (hY : ∀ {R S : TestAlgebra F} (f : R ⟶ S), Function.Injective f.hom → Function.Injective (Y.map f))
    (R : TestAlgebra F) : Function.Bijective (τ.app R) := by
  let T := CommAlgCat.of F (K ⊗[F] R)
  let i : R ⟶ T := CommAlgCat.ofHom (scalarExtension (K := K))
  have hi : Function.Injective i.hom := Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hT := hK T
  have hn {U V : TestAlgebra F} (f : U ⟶ V) (p : A ⟶ U) :
      τ.app V (p ≫ f) = Y.map f (τ.app U p) := τ.naturality_apply f p
  constructor
  · intro f g h
    have h' : f ≫ i = g ≫ i := hT.1 (by rw [hn, hn, h])
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    exact hi (congrArg (fun p : A ⟶ T => p.hom a) h')
  · intro y
    obtain ⟨f, hf⟩ := hT.2 (Y.map i y)
    change A ⟶ T at f
    have hσ (σ : K ≃ₐ[F] K) : (tensorAut σ).comp f.hom = f.hom := by
      let m : T ⟶ T := CommAlgCat.ofHom (tensorAut σ)
      have hm : i ≫ m = i := CommAlgCat.hom_ext (AlgHom.ext (tensorAut_scalarExtension σ))
      have h : f ≫ m = f := hT.1 (calc
        τ.app T (f ≫ m) = Y.map m (τ.app T f) := hn m f
        _ = Y.map (i ≫ m) y := by rw [hf, CategoryTheory.Functor.map_comp]; rfl
        _ = τ.app T f := by rw [hm, hf])
      apply AlgHom.ext
      intro a
      exact congrArg (fun p : A ⟶ T => p.hom a) h
    obtain ⟨g, hg⟩ := algebraPoint_descends f.hom hσ
    let j := CommAlgCat.ofHom g
    have hj : j ≫ i = f := CommAlgCat.hom_ext (AlgHom.ext (DFunLike.congr_fun hg))
    refine ⟨j, hY i hi ?_⟩
    rw [← hn, hj, hf]

end ScalePointDescent

section ScaleTestRings

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory Matrix
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup IsSchemeKernel)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.RM03.CSA.NormOneGroup (extendSplitting extendSplitting_natural)

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} {D : DescendedQuadraticPair ρ}
  {G : AffineAlgebraicGroup F} {hB : isCentralSimple F B} {d : ℕ}
  (P : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)

private def splitQuaternionAt (E : (K ⊗[F] B) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)
    (S : TestAlgebra K) : let R := (restrictTestAlgebra F K).obj S
      (R ⊗[F] B) ≃ₐ[S] Matrix (Fin 2) (Fin 2) S := by
  letI : Algebra F S := ((restrictTestAlgebra F K).obj S).algebra
  letI : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  exact extendSplitting E

private theorem splitQuaternionAt_natural (E : (K ⊗[F] B) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)
    {S T : TestAlgebra K} (f : S ⟶ T) :
    let R := (restrictTestAlgebra F K).obj S
    ∀ x : R ⊗[F] B,
      splitQuaternionAt E T (tensorMap B ((restrictTestAlgebra F K).map f).hom x) =
        (splitQuaternionAt E S x).map f.hom := by
  let : Algebra F S := ((restrictTestAlgebra F K).obj S).algebra
  let : Algebra F T := ((restrictTestAlgebra F K).obj T).algebra
  let : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F K T := IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro x
  exact extendSplitting_natural E f.hom x

variable {J : Type u} [Fintype J] (b : Module.Basis J F B)

private def quaternionNormAt (hB : isCentralSimple F B) (R : TestAlgebra F) : (R ⊗[F] B)ˣ →* Rˣ :=
  Units.map (normHom hB b)

private theorem quaternionNormAt_natural (hB : isCentralSimple F B)
    {R S : TestAlgebra F} (f : R ⟶ S) (t : (R ⊗[F] B)ˣ) :
    quaternionNormAt b hB S (Units.map (tensorMap B f.hom).toMonoidHom t) =
      Units.map f.hom.toMonoidHom (quaternionNormAt b hB R t) := by
  apply Units.ext
  exact normAt_natural hB b f.hom t.val

private theorem splitQuaternionAt_norm (n : ℕ) (hd : degree F B = n)
    (E : (K ⊗[F] B) ≃ₐ[K] Matrix (Fin n) (Fin n) K) (S : TestAlgebra K) :
    let R := (restrictTestAlgebra F K).obj S
    let _ : Algebra F S := R.algebra
    let _ : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (t : (R ⊗[F] B)ˣ), (extendSplitting E t.val).det = (quaternionNormAt b hB R t : R) := by
  subst n
  intro R alg inst t
  exact (normAt_eq_det hB b E t.val).symm

private def kernelScalePoint (R : TestAlgebra F) (z : Points P.kernel.group.X R) :
    spinScalePreimage P Q R := by
  refine ⟨(z ≫ P.kernel.inclusion.hom.hom, 1), ?_⟩
  have hw := P.isKernel.w
  have h : (z ≫ P.kernel.inclusion.hom.hom) ≫ P.projection.hom.hom = (1 : Points P.neutral.val.X R) := by
    change (z ≫ P.kernel.inclusion.hom.hom) ≫ P.projection.hom.hom = toUnit _ ≫ η[P.neutral.val.X]
    rw [Category.assoc, hw, ← Category.assoc]
    exact congrArg (· ≫ η[P.neutral.val.X]) (toUnit_unique _ _)
  change P.fullPoints R ((z ≫ P.kernel.inclusion.hom.hom) ≫ (P.projection ≫ P.inclusion).hom.hom) =
    quaternionScale Q R 1
  have hh : ((z ≫ P.kernel.inclusion.hom.hom) ≫ (P.projection ≫ P.inclusion).hom.hom) =
      (1 : Points P.full.val.X R) := by
    change ((z ≫ P.kernel.inclusion.hom.hom) ≫ P.projection.hom.hom ≫ P.inclusion.hom.hom) = _
    rw [← Category.assoc, h, MonObj.one_comp]
  rw [hh, map_one, map_one]

end ScaleTestRings

section QuaternionNormPairFunctor

open AlgebraicGeometry CategoryTheory Matrix
open scoped TensorProduct
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)
open LinearAlgebraicGroups.Albert.SplitSpinSpecification (scaleRow)
open private scaleRow_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

variable {F K B J : Type u} [Field F] [Field K] [Algebra F K]
  [DivisionRing B] [Algebra F B] [Fintype J]
  (hB : isCentralSimple F B) (b : Module.Basis J F B)

private def mapNormSquarePair {R S : TestAlgebra F} (f : R ⟶ S) :
    scalePairs (quaternionNormAt b hB R) →* scalePairs (quaternionNormAt b hB S) where
  toFun x := ⟨(Units.map (tensorMap B f.hom).toMonoidHom x.val.1,
      Units.map f.hom.toMonoidHom x.val.2), by
    change quaternionNormAt b hB S (Units.map (tensorMap B f.hom).toMonoidHom x.val.1) =
      (Units.map f.hom.toMonoidHom x.val.2) ^ 2
    rw [quaternionNormAt_natural, ← map_pow]
    exact congrArg (Units.map f.hom.toMonoidHom) x.property⟩
  map_one' := Subtype.ext (Prod.ext (map_one _) (map_one _))
  map_mul' x y := Subtype.ext (Prod.ext (map_mul _ _ _) (map_mul _ _ _))

private def normSquarePairFunctor : TestAlgebra F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (scalePairs (quaternionNormAt b hB R))
  map f := GrpCat.ofHom (mapNormSquarePair hB b f)
  map_id R := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      change tensorMap B (AlgHom.id F R) x.val.1.val = x.val.1.val
      rw [scaleTensor_id]
      rfl
    · rfl
  map_comp f g := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      change tensorMap B (g.hom.comp f.hom) x.val.1.val =
        tensorMap B g.hom (tensorMap B f.hom x.val.1.val)
      rw [scaleTensor_comp]
      rfl
    · rfl

private theorem normSquarePairMap_injective {R S : TestAlgebra F} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (mapNormSquarePair hB b f) := by
  have ht : Function.Injective (tensorMap B f.hom) :=
    TensorProduct.map_injective_of_flat_flat f.hom.toLinearMap (LinearMap.id : B →ₗ[F] B) hf Function.injective_id
  intro x y h
  apply Subtype.ext
  refine Prod.ext (Units.ext (ht ?_)) (Units.ext (hf ?_))
  · exact congrArg (fun z : scalePairs (quaternionNormAt b hB S) => z.val.1.val) h
  · exact congrArg (fun z : scalePairs (quaternionNormAt b hB S) => z.val.2.val) h

variable (hd : degree F B = 2) (E : (K ⊗[F] B) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)

private def splitNormSquareMatrix (S : TestAlgebra K) :
    let R := (restrictTestAlgebra F K).obj S
    scalePairs (quaternionNormAt b hB R) ≃ {p : Matrix (Fin 2) (Fin 2) S × Sˣ // p.1.det = (p.2 : S) ^ 2} := by
  let R := (restrictTestAlgebra F K).obj S
  let e := splitQuaternionAt E S
  have hN (t : (R ⊗[F] B)ˣ) : (e t.val).det = (quaternionNormAt b hB R t : R) :=
    splitQuaternionAt_norm b 2 hd E S t
  let forward (x : scalePairs (quaternionNormAt b hB R)) :=
    (⟨(e x.val.1.val, x.val.2), (hN x.val.1).trans (congrArg Units.val x.property)⟩ :
      {p : Matrix (Fin 2) (Fin 2) S × Sˣ // p.1.det = (p.2 : S) ^ 2})
  let matUnit (x : {p : Matrix (Fin 2) (Fin 2) S × Sˣ // p.1.det = (p.2 : S) ^ 2}) :
      IsUnit x.val.1 := (Matrix.isUnit_iff_isUnit_det x.val.1).mpr (by rw [x.property]; exact x.val.2.isUnit.pow 2)
  let backward (x : {p : Matrix (Fin 2) (Fin 2) S × Sˣ // p.1.det = (p.2 : S) ^ 2}) :
      scalePairs (quaternionNormAt b hB R) := by
    let t := Units.map e.symm.toMonoidHom (matUnit x).unit
    refine ⟨(t, x.val.2), Units.ext ?_⟩
    change (quaternionNormAt b hB R t : R) = (x.val.2 : S) ^ 2
    rw [← hN]
    change (e (e.symm (matUnit x).unit.val)).det = _
    rw [e.apply_symm_apply, (matUnit x).unit_spec]
    exact x.property
  refine ⟨forward, backward, fun x => Subtype.ext (Prod.ext (Units.ext ?_) rfl),
    fun x => Subtype.ext (Prod.ext ?_ rfl)⟩
  · change e.symm (matUnit (forward x)).unit.val = x.val.1.val
    rw [(matUnit (forward x)).unit_spec]
    exact e.symm_apply_apply _
  · change e (e.symm (matUnit x).unit.val) = x.val.1
    rw [e.apply_symm_apply, (matUnit x).unit_spec]

private def splitNormSquareParameters (S : TestAlgebra K) :
    scalePairs (quaternionNormAt b hB ((restrictTestAlgebra F K).obj S)) ≃
      (Matrix.SpecialLinearGroup (Fin 2) S × Sˣ) :=
  (splitNormSquareMatrix hB b hd E S).trans (splitScaleParameters_proof S).choose

private theorem splitNormSquareParameters_coordinates (S : TestAlgebra K)
    (x : scalePairs (quaternionNormAt b hB ((restrictTestAlgebra F K).obj S))) :
    (splitNormSquareParameters hB b hd E S x).1.val =
      scaleRow 0 ((↑x.val.2⁻¹ : S) ^ 2) (splitQuaternionAt E S x.val.1.val) ∧
    (splitNormSquareParameters hB b hd E S x).2 = x.val.2 :=
  (splitScaleParameters_proof S).choose_spec (splitNormSquareMatrix hB b hd E S x)

private theorem splitNormSquareParameters_natural {S T : TestAlgebra K} (f : S ⟶ T)
    (x : scalePairs (quaternionNormAt b hB ((restrictTestAlgebra F K).obj S))) :
    splitNormSquareParameters hB b hd E T (mapNormSquarePair hB b ((restrictTestAlgebra F K).map f) x) =
      (Matrix.SpecialLinearGroup.map f.hom.toRingHom (splitNormSquareParameters hB b hd E S x).1,
        Units.map f.hom.toMonoidHom (splitNormSquareParameters hB b hd E S x).2) := by
  have hS := splitNormSquareParameters_coordinates hB b hd E S x
  have hT := splitNormSquareParameters_coordinates hB b hd E T
    (mapNormSquarePair hB b ((restrictTestAlgebra F K).map f) x)
  refine Prod.ext (Subtype.ext ?_) (hT.2.trans (congrArg (Units.map f.hom.toMonoidHom) hS.2.symm))
  rw [hT.1]
  change scaleRow 0 ((f.hom x.val.2.inv) ^ 2)
    (splitQuaternionAt E T (tensorMap B ((restrictTestAlgebra F K).map f).hom x.val.1.val)) =
    (splitNormSquareParameters hB b hd E S x).1.val.map f.hom.toRingHom
  rw [hS.1, scaleRow_map, map_pow]
  exact congrArg (scaleRow 0 ((f.hom x.val.2.inv) ^ 2)) (splitQuaternionAt_natural E f x.val.1.val)

end QuaternionNormPairFunctor

section ScaleSquareRootExtension

open AlgebraicGeometry CategoryTheory Polynomial

/-- A square root of a unit can be adjoined over any test algebra by a
quadratic extension whose coefficient map is injective. -/
private theorem adjoinScaleSquareRoot {k : Type u} [Field k] (R : TestAlgebra k) (a : Rˣ) :
    ∃ (S : TestAlgebra k) (f : R ⟶ S), Function.Injective f.hom ∧
      ∃ z : Sˣ, z ^ 2 = Units.map f.hom.toMonoidHom a := by
  let p : Polynomial R := X ^ 2 - C a.val
  let S := CommAlgCat.of k (AdjoinRoot p)
  let f : R ⟶ S := CommAlgCat.ofHom (AdjoinRoot.ofAlgHom k p)
  have hs : (AdjoinRoot.root p) ^ 2 = f.hom a.val := by
    change (AdjoinRoot.root p) ^ 2 = AdjoinRoot.of p a.val
    have h := AdjoinRoot.eval₂_root p
    change (X ^ 2 - C a.val : Polynomial R).eval₂ (AdjoinRoot.of p) (AdjoinRoot.root p) = 0 at h
    exact sub_eq_zero.mp (by simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] using h)
  have h : IsUnit (AdjoinRoot.root p) := isUnit_of_mul_isUnit_left (by
    rw [← pow_two, hs]
    exact a.isUnit.map f.hom)
  refine ⟨S, f, ?_, h.unit, Units.ext ?_⟩
  · by_cases hR : Nontrivial R
    · apply AdjoinRoot.of.injective_of_monic_of_degree_pos
      · exact monic_X_pow_sub_C _ (by decide)
      · dsimp only [p]
        rw [degree_X_pow_sub_C (by decide : 0 < 2)]
        decide
    · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
      exact Function.injective_of_subsingleton _
  · change h.unit.val ^ 2 = f.hom a.val
    rw [h.unit_spec, hs]

end ScaleSquareRootExtension

section ScaleClosedPointDescent

open AlgebraicGeometry CategoryTheory Opposite

/-- A closed affine subscheme is cut out by equations, so membership descends
along an injective map of coefficient algebras. -/
private theorem factorPointThroughClosed {k : Type u} [Field k] {X Y : SchemeOver k}
    (hY : IsAffine Y.left) (i : X ⟶ Y) (hi : IsClosedImmersion i.left)
    {R S : TestAlgebra k} (f : R ⟶ S) (hf : Function.Injective f.hom)
    (a : Points Y R) (b : Points X S) (hab : mapPoints f a = b ≫ i) :
    ∃ c : Points X R, c ≫ i = a := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hY
  let A' := CommRingCat.of (A.unop : TestAlgebra k)
  let v : Y.left ⟶ Spec A' := e.inv.left
  have hv : IsIso v := by
    change IsIso ((Over.forget _).map e.inv)
    infer_instance
  have hclosed : IsClosedImmersion (i.left ≫ v) := IsClosedImmersion.comp _ _
  obtain ⟨J, eJ, hJ⟩ := (IsClosedImmersion.Spec_iff (R := A')).mp hclosed
  let q : A' ⟶ CommRingCat.of (A' ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  change i.left ≫ v = eJ.hom ≫ Spec.map q at hJ
  let aR : Spec (CommRingCat.of R) ⟶ Y.left := a.left
  let bS : Spec (CommRingCat.of S) ⟶ X.left := b.left
  have ha : ∃ α : A' ⟶ CommRingCat.of R, Spec.map α = aR ≫ v := Spec.map_surjective _
  have hb : ∃ β : CommRingCat.of (A' ⧸ J) ⟶ CommRingCat.of S, Spec.map β = bS ≫ eJ.hom :=
    Spec.map_surjective _
  obtain ⟨α, hα⟩ := ha
  obtain ⟨β, hβ⟩ := hb
  let fR := CommRingCat.ofHom f.hom.toRingHom
  have he : α ≫ fR = q ≫ β := by
    apply Spec.map_injective
    have hbase : Spec.map fR ≫ aR = bS ≫ i.left := congrArg Over.Hom.left hab
    rw [Spec.map_comp, Spec.map_comp, hα, hβ, Category.assoc bS, ← hJ, ← Category.assoc, hbase]
    exact Category.assoc _ _ _
  have hz (x : A') (hx : x ∈ J) : α x = 0 := by
    apply hf
    have h := congrArg (fun t : A' ⟶ CommRingCat.of S => t x) he
    change f.hom (α x) = β (Ideal.Quotient.mk J x) at h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero] at h
    simpa only [map_zero] using h
  let βR : CommRingCat.of (A' ⧸ J) ⟶ CommRingCat.of R := CommRingCat.ofHom (Ideal.Quotient.lift J α.hom hz)
  have hβR : q ≫ βR = α := CommRingCat.hom_ext (RingHom.ext fun x => Ideal.Quotient.lift_mk J α.hom hz (a := x))
  let c := Spec.map βR ≫ eJ.inv
  have hc : c ≫ i.left = aR := by
    apply (cancel_mono v).mp
    rw [Category.assoc, hJ, ← Category.assoc]
    change (Spec.map βR ≫ eJ.inv) ≫ eJ.hom ≫ Spec.map q = _
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, hβR, hα]
  let zR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k) := ((testSpec k).obj (op R)).hom
  have haR : aR ≫ Y.hom = zR := Over.w a
  have hcOver : c ≫ X.hom = zR := calc
    _ = c ≫ (i.left ≫ Y.hom) := congrArg (c ≫ ·) (Over.w i).symm
    _ = (c ≫ i.left) ≫ Y.hom := (Category.assoc _ _ _).symm
    _ = aR ≫ Y.hom := congrArg (· ≫ Y.hom) hc
    _ = zR := haR
  refine ⟨Over.homMk c hcOver, ?_⟩
  exact Over.OverMorphism.ext hc

end ScaleClosedPointDescent

section ScaleMatrixProof
open Matrix AlgebraicGeometry CategoryTheory
open scoped Matrix TensorProduct
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (extendAnti antiValue tensorMap)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (degree isCentralSimple)


variable {I R : Type u} [Fintype I] [DecidableEq I] [CommRing R]

theorem scale_hyperbolic_apply (x : I ⊕ I → R) :
    hyperbolicForm I R x = ∑ i, x (.inl i) * x (.inr i) := by
  rw [hyperbolicForm, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  simp [dotProduct, Fintype.sum_sum_type, Matrix.mulVec, Matrix.one_apply]

theorem scale_hyperbolic_polar (x y : I ⊕ I → R) :
    (hyperbolicForm I R).polarBilin x y = x ⬝ᵥ (hyperbolicGram I R *ᵥ y) := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  simp only [scale_hyperbolic_apply, fromBlocks_mulVec, hyperbolicGram, dotProduct, Pi.add_apply,
    Fintype.sum_sum_type, zero_mulVec, one_mulVec, zero_add, add_zero,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
  ring

theorem scale_hyperbolic_map {S : Type u} [CommRing S] (f : R →+* S) (v : I ⊕ I → R) :
    hyperbolicForm I S (f ∘ v) = f (hyperbolicForm I R v) := by
  simp [scale_hyperbolic_apply, map_sum]

theorem scale_gram_map {S : Type u} [CommRing S] (f : R →+* S) :
    (hyperbolicGram I R).map f = hyperbolicGram I S := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [hyperbolicGram, Matrix.one_apply]

section PairedColumns

variable {k : Type u} [Field k]
variable {I : Type u} [Fintype I] [DecidableEq I]

/-- Rectangular matrices for inclusion and projection on the first isotropic
summand. The polar pairing determines the matrices for the second summand. -/
structure ScalePlane (I k : Type u) [Fintype I] [DecidableEq I] [CommRing k] where
  left : Matrix (I ⊕ I) (Fin 2) k
  leftCoord : Matrix (Fin 2) (I ⊕ I) k
  retract : leftCoord * left = 1
  leftIsotropic : ∀ x, hyperbolicForm I k (left *ᵥ x) = 0
  rightIsotropic : ∀ x, hyperbolicForm I k
    ((hyperbolicGram I k * leftCoord.transpose) *ᵥ x) = 0

namespace ScalePlane

variable {A : Type u} [CommRing A] (p : ScalePlane I A)

abbrev gram (_p : ScalePlane I A) := hyperbolicGram I A

def right : Matrix (I ⊕ I) (Fin 2) A := p.gram * p.leftCoord.transpose

def rightCoord : Matrix (Fin 2) (I ⊕ I) A := p.left.transpose * p.gram

theorem gram_sq : p.gram * p.gram = 1 := by
  simp [gram, hyperbolicGram, fromBlocks_multiply, fromBlocks_one]

theorem gram_transpose : p.gram.transpose = p.gram := by
  simp [gram, hyperbolicGram, fromBlocks_transpose]

theorem right_retract : p.rightCoord * p.right = 1 := by
  rw [right, rightCoord, Matrix.mul_assoc, ← Matrix.mul_assoc p.gram p.gram, p.gram_sq, Matrix.one_mul,
    ← transpose_mul, p.retract, transpose_one]

theorem right_polar_vector (x : Fin 2 → A) (v : I ⊕ I → A) :
    (hyperbolicForm I A).polarBilin (p.right *ᵥ x) v = x ⬝ᵥ (p.leftCoord *ᵥ v) := by
  rw [scale_hyperbolic_polar, ← Matrix.vecMul_transpose, dotProduct_mulVec,
    Matrix.vecMul_vecMul, right, transpose_mul, p.gram_transpose, Matrix.transpose_transpose,
    ← dotProduct_mulVec]
  change x ⬝ᵥ ((p.leftCoord * p.gram * p.gram) *ᵥ v) = _
  rw [Matrix.mul_assoc, p.gram_sq, Matrix.mul_one]

theorem left_polar_vector (x : Fin 2 → A) (v : I ⊕ I → A) :
    (hyperbolicForm I A).polarBilin (p.left *ᵥ x) v = x ⬝ᵥ (p.rightCoord *ᵥ v) := by
  rw [scale_hyperbolic_polar, ← Matrix.vecMul_transpose, dotProduct_mulVec, Matrix.vecMul_vecMul, rightCoord, ← dotProduct_mulVec]

theorem left_right_zero : p.leftCoord * p.right = 0 := by
  ext i j
  have h : (hyperbolicForm I A).polarBilin (p.right *ᵥ Pi.single i 1)
      (p.right *ᵥ Pi.single j 1) = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← Matrix.mulVec_add]
    simp only [right, gram, p.rightIsotropic]
    simp
  rw [right_polar_vector, Matrix.mulVec_mulVec, single_dotProduct,
    Matrix.mulVec_single_one] at h
  simpa using h

theorem right_left_zero : p.rightCoord * p.left = 0 := by
  ext i j
  have h : (hyperbolicForm I A).polarBilin (p.left *ᵥ Pi.single i 1)
      (p.left *ᵥ Pi.single j 1) = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← Matrix.mulVec_add, p.leftIsotropic, p.leftIsotropic, p.leftIsotropic]
    simp
  rw [left_polar_vector, Matrix.mulVec_mulVec, single_dotProduct,
    Matrix.mulVec_single_one] at h
  simpa using h

variable {S : Type u} [CommRing S]

set_option maxHeartbeats 900000 in
theorem map_totallyIsotropic {L : Matrix (I ⊕ I) (Fin 2) A}
    (h : ∀ x, hyperbolicForm I A (L *ᵥ x) = 0) (f : A →+* S) (x : Fin 2 → S) :
    hyperbolicForm I S (L.map f *ᵥ x) = 0 := by
  have hv : x = x 0 • Pi.single 0 (1 : S) + x 1 • Pi.single 1 (1 : S) := by
    funext i
    fin_cases i <;> simp
  have hm (v : Fin 2 → A) : (L.map f) *ᵥ (f ∘ v) = f ∘ (L *ᵥ v) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Function.comp_apply]
  have hs (i : Fin 2) : (f ∘ (Pi.single i (1 : A))) = Pi.single i (1 : S) := by
    funext j
    by_cases hij : i = j <;> simp [hij, eq_comm]
  let q := hyperbolicForm I S
  let v₀ : I ⊕ I → S := L.map f *ᵥ Pi.single 0 1
  let v₁ : I ⊕ I → S := L.map f *ᵥ Pi.single 1 1
  have hq (v : Fin 2 → A) : q (L.map f *ᵥ (f ∘ v)) = 0 := by
    dsimp [q]
    rw [hm, scale_hyperbolic_map, h, map_zero]
  have h₀ : q v₀ = 0 := by simpa only [hs, v₀] using hq (Pi.single 0 1)
  have h₁ : q v₁ = 0 := by simpa only [hs, v₁] using hq (Pi.single 1 1)
  have h₀₁ : q (v₀ + v₁) = 0 := by
    let x₀ : Fin 2 → A := Pi.single 0 1
    let x₁ : Fin 2 → A := Pi.single 1 1
    have he : f ∘ (x₀ + x₁) = (f ∘ x₀) + (f ∘ x₁) := by
      funext i
      exact map_add f (x₀ i) (x₁ i)
    have hh := congrArg (fun y : Fin 2 → S => q ((L.map f) *ᵥ y)) he
    have hh' : q (L.map f *ᵥ ((f ∘ x₀) + (f ∘ x₁))) = 0 :=
      hh.symm.trans (hq (x₀ + x₁))
    simpa only [x₀, x₁, hs, Matrix.mulVec_add, v₀, v₁] using hh'
  have hp : QuadraticMap.polar q (x 0 • v₀) (x 1 • v₁) = 0 := by
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      QuadraticMap.polar, h₀₁, h₀, h₁, sub_zero, sub_zero, smul_zero, smul_zero]
  change q (L.map f *ᵥ x) = _
  rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  change q (x 0 • v₀ + x 1 • v₁) = _
  rw [QuadraticMap.polar, q.map_smul, q.map_smul, h₀, h₁, smul_zero, smul_zero, sub_zero, sub_zero] at hp
  exact hp

def map (f : A →+* S) : ScalePlane I S where
  left := p.left.map f
  leftCoord := p.leftCoord.map f
  retract := by rw [← Matrix.map_mul, p.retract, Matrix.map_one _ (map_zero f) (map_one f)]
  leftIsotropic := map_totallyIsotropic p.leftIsotropic f
  rightIsotropic := by
    rw [← scale_gram_map (I := I) f, ← Matrix.transpose_map, ← Matrix.map_mul]
    exact map_totallyIsotropic p.rightIsotropic f

theorem right_map (f : A →+* S) : (p.map f).right = p.right.map f := by
  unfold right map gram
  rw [Matrix.map_mul, Matrix.transpose_map, scale_gram_map]

theorem rightCoord_map (f : A →+* S) : (p.map f).rightCoord = p.rightCoord.map f := by
  unfold rightCoord map gram
  rw [Matrix.map_mul, Matrix.transpose_map, scale_gram_map]

end ScalePlane
end PairedColumns
end ScaleMatrixProof

section ScaleCornersProof
open Matrix AlgebraicGeometry CategoryTheory
open scoped Matrix TensorProduct
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (extendAnti antiValue tensorMap)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (degree isCentralSimple)
open _root_.RM03.CSA.NormOneGroup (extendSplitting_tmul)


section QuaternionBlockCoordinates

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (hd : degree F B = 2)

abbrev splitCornerBasis :
    Module.Basis (Fin 2) K (cornerSpace (splitQuaternionBlock Q) (leftLine d)) :=
  (Module.finBasis K (cornerSpace (splitQuaternionBlock Q) (leftLine d))).reindex
    (finCongr (quaternionCorner_finrank Q hd (leftLine d)))

def quaternionLeftInclusion : Matrix (I ⊕ I) (Fin 2) K :=
  LinearMap.toMatrix' ((cornerSpace (splitQuaternionBlock Q) (leftLine d)).subtype.comp
    (splitCornerBasis Q hd).equivFun.symm.toLinearMap)

def quaternionLeftCoordinates : Matrix (Fin 2) (I ⊕ I) K :=
  LinearMap.toMatrix' ((splitCornerBasis Q hd).equivFun.toLinearMap.comp
    (cornerProjection (splitQuaternionBlock Q) (leftLine d)).rangeRestrict)

abbrev quaternionMatrixEquiv := splitQuaternionEquiv Q hd (leftLine d)

theorem quaternionLeft_retract : quaternionLeftCoordinates Q hd * quaternionLeftInclusion Q hd = 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, quaternionLeftCoordinates, quaternionLeftInclusion,
    Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
  apply LinearMap.ext
  intro x
  let y := (splitCornerBasis Q hd).equivFun.symm x
  have hy : (cornerProjection (splitQuaternionBlock Q) (leftLine d)).rangeRestrict y.val = y :=
    Subtype.ext (cornerProjection_on_range _ _ y)
  change (splitCornerBasis Q hd).equivFun
    ((cornerProjection (splitQuaternionBlock Q) (leftLine d)).rangeRestrict y.val) = x
  rw [hy, LinearEquiv.apply_symm_apply]

theorem quaternionLeft_entry (a : K ⊗[F] B) :
    D.splitting ((Q.matrixAt (CommAlgCat.of F K)).symm (Matrix.single (leftLine d) (leftLine d) a)) =
      quaternionLeftInclusion Q hd * quaternionMatrixEquiv Q hd a * quaternionLeftCoordinates Q hd := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, quaternionLeftInclusion, quaternionLeftCoordinates,
    Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  let E := splitQuaternionBlock Q
  let p := cornerProjection E (leftLine d)
  let y := p.rangeRestrict v
  let b := splitCornerBasis Q hd
  let A := quaternionMatrixEquiv Q hd a
  have he : Matrix.toLin b b A y = cornerEndomorphism E (leftLine d) a y :=
    DFunLike.congr_fun (Matrix.toLinAlgEquiv_toMatrixAlgEquiv b (cornerEndomorphism E (leftLine d) a)) y
  have ha : b.equivFun.symm (Matrix.toLin' A (b.equivFun y)) =
      cornerEndomorphism E (leftLine d) a y := he
  change E (Matrix.single (leftLine d) (leftLine d) a) v =
    (b.equivFun.symm (Matrix.toLin' A (b.equivFun y))).val
  rw [ha, cornerEndomorphism_apply]
  change E (Matrix.single (leftLine d) (leftLine d) a) v =
    E (Matrix.single (leftLine d) (leftLine d) a) (p v)
  have hm : E (Matrix.single (leftLine d) (leftLine d) a) * p =
      E (Matrix.single (leftLine d) (leftLine d) a) := by
    rw [show p = E (Matrix.single (leftLine d) (leftLine d) 1) from rfl, ← map_mul]
    simp
  exact (DFunLike.congr_fun hm v).symm

theorem pairMatrix_single_tmul (R : TestAlgebra F) (i j : QuaternionPairIndex d)
    (r : R) (a : B) :
    (Q.matrixAt R).symm (Matrix.single i j (r ⊗ₜ[F] a)) = r ⊗ₜ[F] pairEntry Q i j a := by
  apply (Q.matrixAt R).injective
  rw [AlgEquiv.apply_symm_apply, Q.matrixAtFormula, pairEntry, AlgEquiv.apply_symm_apply]
  exact (Matrix.map_single i j a
    ((TensorProduct.mk F R B r : B →ₗ[F] R ⊗[F] B))).symm

theorem quaternionLeft_projection :
    quaternionLeftInclusion Q hd * quaternionLeftCoordinates Q hd =
      D.splitting (1 ⊗ₜ[F] pairEntry Q (leftLine d) (leftLine d) 1) := by
  have h := quaternionLeft_entry Q hd (1 : K ⊗[F] B)
  have h1 : (1 : K ⊗[F] B) = 1 ⊗ₜ[F] 1 := rfl
  rw [map_one, Matrix.mul_one, h1, pairMatrix_single_tmul] at h
  exact h.symm

theorem quaternionRight_projection :
    (hyperbolicGram I K * (quaternionLeftCoordinates Q hd).transpose) *
      ((quaternionLeftInclusion Q hd).transpose * hyperbolicGram I K) =
      D.splitting (1 ⊗ₜ[F] pairEntry Q (rightLine d) (rightLine d) 1) := by
  have h : adjoint (hyperbolicGram I K)
      (D.splitting (1 ⊗ₜ[F] pairEntry Q (leftLine d) (leftLine d) 1)) =
        D.splitting (1 ⊗ₜ[F] pairEntry Q (rightLine d) (rightLine d) 1) := by
    rw [← D.splittingInvolution, LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent.Involution.baseChange_tmul, adjoint_leftProjection]
    simp [antiValue]
  rw [← quaternionLeft_projection Q hd, adjoint, transpose_mul] at h
  simpa only [Matrix.mul_assoc] using h

def quaternionScalePlane (hscalar : QuadraticPairScalarExtension.{u}) (htrace : TraceOrthogonality.{u})
    (hsplit : SplitSemitrace.{u}) : ScalePlane I K where
  left := quaternionLeftInclusion Q hd
  leftCoord := quaternionLeftCoordinates Q hd
  retract := quaternionLeft_retract Q hd
  leftIsotropic := by
    intro x
    have hx := (quaternionIsotropicSummands Q hd hscalar htrace hsplit
      (quaternionLeftInclusion Q hd *ᵥ x)).1
    rwa [← quaternionLeft_projection Q hd, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec _ (quaternionLeftCoordinates Q hd) (quaternionLeftInclusion Q hd),
      quaternionLeft_retract, Matrix.one_mulVec] at hx
  rightIsotropic := by
    intro x
    let R := hyperbolicGram I K * (quaternionLeftCoordinates Q hd).transpose
    let C := (quaternionLeftInclusion Q hd).transpose * hyperbolicGram I K
    have hJ := (hyperbolicGram_properties (I := I) (K := K)).2
    have hCR : C * R = 1 := by
      dsimp only [C, R]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (hyperbolicGram I K) (hyperbolicGram I K),
        hJ, Matrix.one_mul, ← transpose_mul, quaternionLeft_retract, transpose_one]
    have hx := (quaternionIsotropicSummands Q hd hscalar htrace hsplit (R *ᵥ x)).2
    rw [← quaternionRight_projection Q hd] at hx
    change hyperbolicForm I K ((R * C) *ᵥ (R *ᵥ x)) = 0 at hx
    rwa [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ C R, hCR, Matrix.one_mulVec] at hx

variable (R : TestAlgebra F) [Algebra K R] [IsScalarTower F K R]

def quaternionDiagonalEntry (i : QuaternionPairIndex d)
    (a : R ⊗[F] B) : R ⊗[F] ρ.fixedSubalgebra :=
  (Q.matrixAt R).symm (Matrix.single i i a)

variable (eFull : (R ⊗[F] ρ.fixedSubalgebra) ≃ₐ[R] Matrix (I ⊕ I) (I ⊕ I) R)
variable (hC : ∀ (r : R) (x : ρ.fixedSubalgebra),
  eFull (r ⊗ₜ[F] x) = r • x.val.map (algebraMap K R))

include hC in
theorem quaternionLeft_entry_at (a : R ⊗[F] B) :
    eFull (quaternionDiagonalEntry Q R (leftLine d) a) =
      (quaternionLeftInclusion Q hd).map (algebraMap K R) *
        _root_.RM03.CSA.NormOneGroup.extendSplitting (quaternionMatrixEquiv Q hd) a *
          (quaternionLeftCoordinates Q hd).map (algebraMap K R) := by
  induction a using TensorProduct.inductionOn with
  | tmul r x =>
    rw [quaternionDiagonalEntry, pairMatrix_single_tmul, hC]
    rw [extendSplitting_tmul, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.map_mul, ← Matrix.map_mul, ← quaternionLeft_entry Q hd,
      pairMatrix_single_tmul, D.splittingFormula, one_smul]
  | add a b ha hb =>
    rw [quaternionDiagonalEntry, Matrix.single_add, map_add, map_add]
    rw [← quaternionDiagonalEntry, ← quaternionDiagonalEntry, ha, hb, map_add,
      Matrix.mul_add, Matrix.add_mul]

omit [IsScalarTower F K R] in
include hC in
theorem quaternionRight_entry_at (a : R ⊗[F] B) :
    eFull (quaternionDiagonalEntry Q R (rightLine d) (antiValue (extendAnti Q.conjugation.anti R) a)) =
      adjoint (hyperbolicGram I R) (eFull (quaternionDiagonalEntry Q R (leftLine d) a)) := by
  induction a using TensorProduct.inductionOn with
  | tmul r x =>
    change eFull (quaternionDiagonalEntry Q R (rightLine d)
      (r ⊗ₜ[F] antiValue Q.conjugation.anti x)) = _
    rw [quaternionDiagonalEntry, quaternionDiagonalEntry, pairMatrix_single_tmul,
      pairMatrix_single_tmul, hC, hC, ← adjoint_leftProjection Q, D.involutionFormula,
      adjoint, adjoint, transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, scale_gram_map]
  | add a b ha hb =>
    have h : antiValue (extendAnti Q.conjugation.anti R) (a + b) =
        antiValue (extendAnti Q.conjugation.anti R) a + antiValue (extendAnti Q.conjugation.anti R) b := by
      simp [antiValue]
    have he (i : QuaternionPairIndex d) (a b : R ⊗[F] B) :
        quaternionDiagonalEntry Q R i (a+b) =
          quaternionDiagonalEntry Q R i a + quaternionDiagonalEntry Q R i b := by
      simp [quaternionDiagonalEntry, Matrix.single_add]
    rw [h, he, he, map_add, map_add, ha, hb]
    simp [adjoint, Matrix.mul_add, Matrix.add_mul]

theorem scaleDiagonal_as_sum {A : Type u} [Ring A] (d : ℕ) (x y : A) :
    scaleDiagonal d x y = (1 : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) A) -
      Matrix.single (leftLine d) (leftLine d) 1 - Matrix.single (rightLine d) (rightLine d) 1 +
        Matrix.single (leftLine d) (leftLine d) x + Matrix.single (rightLine d) (rightLine d) y := by
  ext i j
  by_cases h : i = j
  · subst j
    rcases i with i | i
    · fin_cases i <;> simp [scaleDiagonal, Matrix.single]
    · simp [scaleDiagonal, Matrix.single]
  · have hn (k : QuaternionPairIndex d) : ¬(k = i ∧ k = j) :=
      fun h' => h (h'.1.symm.trans h'.2)
    simp [scaleDiagonal, Matrix.single, h, hn]

include hC in
theorem quaternionScale_matrix
    (hscalar : QuadraticPairScalarExtension.{u}) (htrace : TraceOrthogonality.{u})
    (hsplit : SplitSemitrace.{u}) (t : (R ⊗[F] B)ˣ) :
    let p := (quaternionScalePlane Q hd hscalar htrace hsplit).map (algebraMap K R)
    let E : (R ⊗[F] B) ≃ₐ[R] Matrix (Fin 2) (Fin 2) R :=
      _root_.RM03.CSA.NormOneGroup.extendSplitting (quaternionMatrixEquiv Q hd)
    let a := Units.map E.toMonoidHom t
    eFull (quaternionScale Q R t).val =
      (1 : Matrix (I ⊕ I) (I ⊕ I) R) - p.left * p.leftCoord - p.right * p.rightCoord +
        p.left * a.val * p.leftCoord + p.right * a.inv.transpose * p.rightCoord := by
  let p := (quaternionScalePlane Q hd hscalar htrace hsplit).map (algebraMap K R)
  let E : (R ⊗[F] B) ≃ₐ[R] Matrix (Fin 2) (Fin 2) R :=
    _root_.RM03.CSA.NormOneGroup.extendSplitting (quaternionMatrixEquiv Q hd)
  let σ := extendAnti Q.conjugation.anti R
  let a := Units.map E.toMonoidHom t
  have hl (x : R ⊗[F] B) : eFull (quaternionDiagonalEntry Q R (leftLine d) x) =
      p.left * E x * p.leftCoord := quaternionLeft_entry_at Q hd R eFull hC x
  have hr (x : R ⊗[F] B) :
      eFull (quaternionDiagonalEntry Q R (rightLine d) (antiValue σ x)) =
        p.right * (E x).transpose * p.rightCoord := by
    rw [quaternionRight_entry_at Q R eFull hC, hl, adjoint, transpose_mul, transpose_mul]
    simp only [ScalePlane.right, ScalePlane.rightCoord, ScalePlane.gram, Matrix.mul_assoc]
  have hr₁ : eFull (quaternionDiagonalEntry Q R (rightLine d) 1) = p.right * p.rightCoord := by
    have hh := hr 1
    simpa only [antiValue, map_one, MulOpposite.unop_one, transpose_one, Matrix.mul_one] using hh
  have hl₁ : eFull (quaternionDiagonalEntry Q R (leftLine d) 1) = p.left * p.leftCoord := by
    simpa only [map_one, Matrix.mul_one] using hl 1
  change eFull ((Q.matrixAt R).symm (diagonalQuaternionScale σ.toMonoidHom d t).val) =
    1 - p.left * p.leftCoord - p.right * p.rightCoord +
      p.left * a.val * p.leftCoord + p.right * a.inv.transpose * p.rightCoord
  rw [diagonalQuaternionScale_val, scaleDiagonal_as_sum]
  simp only [map_add, map_sub, map_one]
  change 1 - eFull (quaternionDiagonalEntry Q R (leftLine d) 1) -
    eFull (quaternionDiagonalEntry Q R (rightLine d) 1) +
    eFull (quaternionDiagonalEntry Q R (leftLine d) t.val) +
    eFull (quaternionDiagonalEntry Q R (rightLine d) (antiValue σ t.inv)) = _
  rw [hl₁, hr₁, hl, hr]
  rfl

end QuaternionBlockCoordinates
end ScaleCornersProof

section ScalePlaneCliffordProof
open Matrix CliffordAlgebra LinearAlgebraicGroups.Albert
open scoped Matrix TensorProduct
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open private map_isometry_reverse map_isometry_evenOdd exteriorImplementer exterior_implementer_even
  exterior_implementer_norm from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin


section PlaneAction
variable {J : Type v} {A : Type u} [Fintype J] [DecidableEq J] [CommRing A]

def dualCoordinates : Module.Dual A (J → A) ≃ₗ[A] (J → A) :=
  (Pi.basisFun A J).dualBasis.equivFun

theorem dualCoordinates_apply (f : Module.Dual A (J → A)) (i : J) :
    dualCoordinates f i = f (Pi.single i 1) := by
  simp [dualCoordinates]

theorem dual_apply_coordinates (f : Module.Dual A (J → A)) (v : J → A) :
    f v = dualCoordinates f ⬝ᵥ v := by
  have hv : ∑ i : J, v i • (Pi.single i 1 : J → A) = v := by
    simpa using (Pi.basisFun A J).sum_repr v
  calc
    f v = f (∑ i : J, v i • (Pi.single i 1 : J → A)) := congrArg f hv.symm
    _ = _ := by simp [dotProduct, dualCoordinates_apply, mul_comm]

def scaleColumnEquiv : (Matrix J J A)ˣ ≃* ((J → A) ≃ₗ[A] (J → A)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv A (J → A))

theorem matrixColumn_apply (a : (Matrix J J A)ˣ) (v : J → A) :
    scaleColumnEquiv a v = a.val *ᵥ v := rfl

theorem matrixColumn_symm (a : (Matrix J J A)ˣ) :
    (scaleColumnEquiv a).symm = scaleColumnEquiv a⁻¹ :=
  (map_inv scaleColumnEquiv a).symm

theorem dualCoordinates_matrix_comp (a : (Matrix J J A)ˣ)
    (f : Module.Dual A (J → A)) :
    dualCoordinates (f.comp (scaleColumnEquiv a).symm.toLinearMap) =
      a.inv.transpose *ᵥ dualCoordinates f := by
  funext i
  rw [dualCoordinates_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, matrixColumn_symm,
    matrixColumn_apply, dual_apply_coordinates, dotProduct_mulVec, dotProduct_single,
    mul_one]
  exact congrFun (vecMul_transpose a.inv.transpose (dualCoordinates f)) i

theorem matrixColumn_det (a : (Matrix J J A)ˣ) :
    LinearMap.det (scaleColumnEquiv a).toLinearMap = a.val.det := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun A J)]
  change (LinearMap.toMatrix (Pi.basisFun A J) (Pi.basisFun A J) (Matrix.toLin' a.val)).det = _
  rw [← Matrix.toLin_eq_toLin', LinearMap.toMatrix_toLin]

namespace ScalePlane

variable {I : Type u} [Fintype I] [DecidableEq I] (p : ScalePlane I A)

def vector : Module.Dual A (CreationSpace A 2) × CreationSpace A 2 →ₗ[A] (I ⊕ I → A) :=
  ((Matrix.toLin' p.right).comp dualCoordinates.toLinearMap).comp (LinearMap.fst _ _ _) +
    (Matrix.toLin' p.left).comp (LinearMap.snd _ _ _)

theorem vector_apply (x : Module.Dual A (CreationSpace A 2) × CreationSpace A 2) :
    p.vector x = p.right *ᵥ dualCoordinates x.1 + p.left *ᵥ x.2 := rfl

def isometry : QuadraticForm.dualProd A (CreationSpace A 2) →qᵢ hyperbolicForm I A where
  toLinearMap := p.vector
  map_app' x := by
    change hyperbolicForm I A (p.vector x) = x.1 x.2
    have h := p.right_polar_vector (dualCoordinates x.1) (p.left *ᵥ x.2)
    rw [Matrix.mulVec_mulVec, p.retract, Matrix.one_mulVec,
      ← dual_apply_coordinates x.1, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar] at h
    have hr : hyperbolicForm I A (p.right *ᵥ dualCoordinates x.1) = 0 := p.rightIsotropic _
    rw [hr, p.leftIsotropic, sub_zero, sub_zero] at h
    exact h

def action (a : (Matrix (Fin 2) (Fin 2) A)ˣ) : Matrix (I ⊕ I) (I ⊕ I) A :=
  1 - p.left * p.leftCoord - p.right * p.rightCoord +
    p.left * a.val * p.leftCoord + p.right * a.inv.transpose * p.rightCoord

def planeComponent (v : I ⊕ I → A) : Module.Dual A (CreationSpace A 2) × CreationSpace A 2 :=
  (dualCoordinates.symm (p.rightCoord *ᵥ v), p.leftCoord *ᵥ v)

def perpendicularComponent (v : I ⊕ I → A) : I ⊕ I → A :=
  v - p.vector (p.planeComponent v)

theorem planeComponent_coords (v : I ⊕ I → A) :
    dualCoordinates (p.planeComponent v).1 = p.rightCoord *ᵥ v :=
  dualCoordinates.apply_symm_apply _

theorem plane_add_perpendicular (v : I ⊕ I → A) :
    p.vector (p.planeComponent v) + p.perpendicularComponent v = v := by
  dsimp [perpendicularComponent]
  abel

theorem leftCoord_perpendicular (v : I ⊕ I → A) : p.leftCoord *ᵥ p.perpendicularComponent v = 0 := by
  rw [perpendicularComponent, Matrix.mulVec_sub, vector_apply, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, p.left_right_zero, p.retract, Matrix.zero_mulVec,
    Matrix.one_mulVec, zero_add]
  exact sub_self _

theorem rightCoord_perpendicular (v : I ⊕ I → A) : p.rightCoord *ᵥ p.perpendicularComponent v = 0 := by
  rw [perpendicularComponent, Matrix.mulVec_sub, vector_apply, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, p.right_left_zero, p.right_retract,
    Matrix.zero_mulVec, Matrix.one_mulVec, add_zero, planeComponent_coords, sub_self]

theorem perpendicular_ortho (v : I ⊕ I → A)
    (x : Module.Dual A (CreationSpace A 2) × CreationSpace A 2) :
    (hyperbolicForm I A).IsOrtho (p.vector x) (p.perpendicularComponent v) := by
  apply QuadraticMap.isOrtho_polarBilin.mp
  rw [p.vector_apply, map_add, LinearMap.add_apply,
    p.left_polar_vector, p.right_polar_vector,
    p.leftCoord_perpendicular, p.rightCoord_perpendicular]
  simp

theorem action_on_vector (a : (Matrix (Fin 2) (Fin 2) A)ˣ) (v : I ⊕ I → A) :
    p.action a *ᵥ v =
      p.vector (splitScaleAction (scaleColumnEquiv a) (p.planeComponent v)) +
        p.perpendicularComponent v := by
  simp only [action, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, vector_apply, splitScaleAction, dualCoordinates_matrix_comp,
    matrixColumn_apply, perpendicularComponent, planeComponent, LinearEquiv.apply_symm_apply]
  change v - p.left *ᵥ (p.leftCoord *ᵥ v) - p.right *ᵥ (p.rightCoord *ᵥ v) +
    p.left *ᵥ (a.val *ᵥ (p.leftCoord *ᵥ v)) + p.right *ᵥ (a.invᵀ *ᵥ (p.rightCoord *ᵥ v)) = _
  abel

theorem action_preserves (a : (Matrix (Fin 2) (Fin 2) A)ˣ) (v : I ⊕ I → A) :
    hyperbolicForm I A (p.action a *ᵥ v) = hyperbolicForm I A v := by
  have hq (x : Module.Dual A (CreationSpace A 2) × CreationSpace A 2) :
      hyperbolicForm I A (p.vector x) = x.1 x.2 := p.isometry.map_app' x
  have h₁ := QuadraticMap.isOrtho_def.mp (p.perpendicular_ortho v (p.planeComponent v))
  have h₂ := QuadraticMap.isOrtho_def.mp
    (p.perpendicular_ortho v (splitScaleAction (scaleColumnEquiv a) (p.planeComponent v)))
  have hv := (congrArg (hyperbolicForm I A) (p.plane_add_perpendicular v)).symm.trans h₁
  rw [p.action_on_vector, h₂, hq, hv, hq]
  simp [splitScaleAction]

end ScalePlane
end PlaneAction

section PlaneClifford
variable {I A : Type u} [Fintype I] [DecidableEq I] [CommRing A] (p : ScalePlane I A)
local notation "q₂" => (QuadraticForm.dualProd A (CreationSpace A 2))
local notation "qᵥ" => (hyperbolicForm I A)

def exteriorVacuum (R : Type u) [CommRing R] : SplitClifford R 2 :=
  let q := QuadraticForm.dualProd R (CreationSpace R 2)
  (1 - ι q (0, Pi.single 0 1) * ι q ((Pi.basisFun R (Fin 2)).coord 0, 0)) *
    (1 - ι q (0, Pi.single 1 1) * ι q ((Pi.basisFun R (Fin 2)).coord 1, 0))

open private create contract create_contract_basis hyperbolicOperator_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel

theorem exteriorVacuum_basis (s : Finset (Fin 2)) :
    splitExteriorEquiv A 2 (exteriorVacuum A) ((Pi.basisFun A (Fin 2)).ExteriorAlgebra s) =
      if s = ∅ then 1 else 0 := by
  classical
  let b := Pi.basisFun A (Fin 2)
  have hv (i : Fin 2) :
      splitExteriorEquiv A 2 (ι q₂ (0, Pi.single i 1) * ι q₂ (b.coord i, 0)) =
        create (b i) * contract (b.coord i) := by
    rw [map_mul, CliffordModel.hyperbolicEquiv_ι, CliffordModel.hyperbolicEquiv_ι]
    congr 1 <;> (apply LinearMap.ext; intro x; simp [hyperbolicOperator_apply, create, b])
  have hp (i : Fin 2) :
      splitExteriorEquiv A 2 (1 - ι q₂ (0, Pi.single i 1) * ι q₂ (b.coord i, 0))
        (b.ExteriorAlgebra s) = if i ∈ s then 0 else b.ExteriorAlgebra s := by
    rw [map_sub, hv, map_one, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply,
      create_contract_basis]
    split <;> simp
  have hemp : b.ExteriorAlgebra ∅ = 1 := by
    rw [ExteriorAlgebra.basis_apply_ofCard b (s := ∅) (n := 0) rfl,
      ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply]
    rfl
  change splitExteriorEquiv A 2 (exteriorVacuum A) (b.ExteriorAlgebra s) = _
  rw [exteriorVacuum, map_mul, Module.End.mul_apply]
  change splitExteriorEquiv A 2
    (1 - ι q₂ (0, Pi.single 0 1) * ι q₂ (b.coord 0, 0))
    (splitExteriorEquiv A 2 (1 - ι q₂ (0, Pi.single 1 1) * ι q₂ (b.coord 1, 0))
      (b.ExteriorAlgebra s)) = _
  rw [hp]
  by_cases h1 : (1 : Fin 2) ∈ s
  · simp [h1, show s ≠ ∅ from fun h => by simp [h] at h1]
  · rw [ite_eq_right h1, hp]
    by_cases h0 : (0 : Fin 2) ∈ s
    · simp [h0, show s ≠ ∅ from fun h => by simp [h] at h0]
    · have hs : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i => by
        fin_cases i
        · exact h0
        · exact h1
      simp [hs, hemp]

theorem exteriorVacuum_ne_zero [Nontrivial A] : exteriorVacuum A ≠ 0 := by
  intro hz
  have h := exteriorVacuum_basis (A := A) ∅
  rw [hz, map_zero, LinearMap.zero_apply, ite_eq_left rfl] at h
  exact zero_ne_one h

theorem exteriorImplementer_vacuum (t : CreationSpace A 2 ≃ₗ[A] CreationSpace A 2) :
    (exteriorImplementer t).val * exteriorVacuum A = exteriorVacuum A := by
  apply (splitExteriorEquiv A 2).injective
  rw [map_mul, exteriorImplementer_value]
  apply ((Pi.basisFun A (Fin 2)).ExteriorAlgebra).ext
  intro s
  rw [Module.End.mul_apply, exteriorVacuum_basis]
  split <;> simp

theorem even_commutes_with_perpendicular (v : I ⊕ I → A) {a : SplitClifford A 2}
    (ha : a ∈ evenOdd q₂ 0) :
    Commute (CliffordAlgebra.map p.isometry a) (ι qᵥ (p.perpendicularComponent v)) := by
  let j := CliffordAlgebra.map p.isometry
  let w := ι qᵥ (p.perpendicularComponent v)
  have swap (x : Module.Dual A (CreationSpace A 2) × CreationSpace A 2) :
      j (ι q₂ x) * w = -(w * j (ι q₂ x)) := by
    rw [show j (ι q₂ x) = ι qᵥ (p.vector x) from map_apply_ι _ _]
    exact eq_neg_of_add_eq_zero_left (ι_mul_ι_add_swap_of_isOrtho (p.perpendicular_ortho v x))
  change Commute (j a) w
  induction a, ha using CliffordAlgebra.even_induction with
  | algebraMap r =>
    change j (algebraMap A _ r) * w = w * j (algebraMap A _ r)
    rw [j.commutes]
    exact Algebra.commutes r w
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact ihx.add_left ihy
  | ι_mul_ι_mul x y a h ih =>
    rw [map_mul, map_mul]
    have hh : Commute (j (ι q₂ x) * j (ι q₂ y)) w := by
      change (j (ι q₂ x) * j (ι q₂ y)) * w = w * (j (ι q₂ x) * j (ι q₂ y))
      rw [mul_assoc, swap y, mul_neg, ← mul_assoc, swap x, neg_mul, neg_neg, mul_assoc]
    exact hh.mul_left ih

def planeCliffordLift (a : (Matrix (Fin 2) (Fin 2) A)ˣ) : (CliffordAlgebra qᵥ)ˣ :=
  Units.map (CliffordAlgebra.map p.isometry).toMonoidHom (exteriorImplementer (scaleColumnEquiv a))

theorem planeClifford_even (a : (Matrix (Fin 2) (Fin 2) A)ˣ) :
    (planeCliffordLift p a).val ∈ evenOdd qᵥ 0 :=
  map_isometry_evenOdd p.isometry (exterior_implementer_even _)

theorem planeClifford_norm (a : (Matrix (Fin 2) (Fin 2) A)ˣ) :
    reverse (planeCliffordLift p a).val * (planeCliffordLift p a).val =
      algebraMap A _ a.val.det := by
  let g := CliffordAlgebra.map p.isometry
  let c := exteriorImplementer (scaleColumnEquiv a)
  change reverse (g c.val) * g c.val = _
  rw [← map_isometry_reverse, ← map_mul, exterior_implementer_norm,
    matrixColumn_det, AlgHom.commutes]

theorem planeClifford_action (a : (Matrix (Fin 2) (Fin 2) A)ˣ) (v : I ⊕ I → A) :
    (planeCliffordLift p a).val * ι qᵥ v =
      ι qᵥ (p.action a *ᵥ v) * (planeCliffordLift p a).val := by
  let x := p.planeComponent v
  let w := p.perpendicularComponent v
  let t := scaleColumnEquiv a
  let j := CliffordAlgebra.map p.isometry
  let c := planeCliffordLift p a
  have h : c.val * ι qᵥ (p.vector x) =
      ι qᵥ (p.vector (splitScaleAction t x)) * c.val := by
    have hh := congrArg j (implementer_intertwines t x)
    have hx (y : Module.Dual A (CreationSpace A 2) × CreationSpace A 2) :
        j (ι q₂ y) = ι qᵥ (p.vector y) := map_apply_ι _ _
    change j (exteriorImplementer t).val * ι qᵥ (p.vector x) =
      ι qᵥ (p.vector (splitScaleAction t x)) * j (exteriorImplementer t).val
    simpa only [map_mul, hx] using hh
  have hw := even_commutes_with_perpendicular p v (exterior_implementer_even t)
  change Commute c.val (ι qᵥ w) at hw
  change c.val * ι qᵥ v = _
  have hv : ι qᵥ v = ι qᵥ (p.vector x) + ι qᵥ w := by
    rw [← map_add, p.plane_add_perpendicular]
  rw [p.action_on_vector, hv, map_add, mul_add, add_mul, h, hw.eq]

theorem planeClifford_vacuum (a : (Matrix (Fin 2) (Fin 2) A)ˣ) :
    (planeCliffordLift p a).val * CliffordAlgebra.map p.isometry (exteriorVacuum A) =
      CliffordAlgebra.map p.isometry (exteriorVacuum A) := by
  change CliffordAlgebra.map p.isometry (exteriorImplementer (scaleColumnEquiv a)).val *
    CliffordAlgebra.map p.isometry (exteriorVacuum A) = _
  rw [← map_mul, exteriorImplementer_vacuum]

end PlaneClifford
end ScalePlaneCliffordProof

section ScaleIntrinsicProof
open AlgebraicGeometry CategoryTheory CliffordAlgebra Matrix LinearAlgebraicGroups.Albert
open scoped TensorProduct Matrix
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (hyperbolicGram matrixColumnEquiv)
open LinearAlgebraicGroups.Albert.SpinSpecification (ScalarClifford vectors evenPart reversion coefficientMap IsVectorAction spinUnits)
open LinearAlgebraicGroups.Albert.CliffordSpecification (coefficientForm)
open private map_isometry_reverse map_isometry_evenOdd from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private baseChangeEquiv_reverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel
open private cliffordEquiv_vector cliffordEquiv_even vectors_injective scalar_tensor_injective
  even_one even_mul reversion_even reversion_mul reversion_scalar scalarCentralizer_baseChange
  changeModule changeModule_coord changeCoefficients_apply changeCoefficients_even
  changeCoefficients_vector changeCoefficients_reverse
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor


section ExtendedClifford

variable {k I S : Type u} [Field k] [Fintype I] [DecidableEq I] [CommRing S] [Algebra k S]

local instance scaleIndexOrder : LinearOrder (I ⊕ I) :=
  LinearOrder.lift' (Fintype.equivFin (I ⊕ I)) (Fintype.equivFin (I ⊕ I)).injective

local notation "qₖ" => (hyperbolicForm I k)
local notation "qₛ" => (hyperbolicForm I S)
local notation "bₖ" => (Pi.basisFun k (I ⊕ I))

abbrev scaleVectorCoordinates : (S ⊗[k] (I ⊕ I → k)) ≃ₗ[S] (I ⊕ I → S) :=
  (Module.Basis.baseChange S bₖ).equivFun

omit [DecidableEq I] in
theorem scaleVectorCoordinates_tmul (r : S) (v : I ⊕ I → k) :
    scaleVectorCoordinates (I := I) (r ⊗ₜ[k] v) = r • (algebraMap k S ∘ v) := by
  funext i
  change ((Module.Basis.baseChange S bₖ).repr (r ⊗ₜ[k] v)) i = _
  rw [Module.Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def, Pi.smul_apply, Function.comp_apply, mul_comm]

omit [DecidableEq I] in
theorem scaleVectorCoordinates_natural {T : Type u} [CommRing T] [Algebra k T]
    (f : S →ₐ[k] T) (v : S ⊗[k] (I ⊕ I → k)) :
    scaleVectorCoordinates (changeModule f v) = f ∘ scaleVectorCoordinates v := by
  funext i
  change (Module.Basis.baseChange T bₖ).repr (changeModule f v) i =
    f ((Module.Basis.baseChange S bₖ).repr v i)
  simpa only [Module.Basis.coord_apply] using changeModule_coord bₖ f v i

def scaleVectorIsometry : (coefficientForm S qₖ bₖ).IsometryEquiv qₛ := by
  let l := scaleVectorCoordinates (k := k) (S := S) (I := I)
  have h := (CliffordModel.coefficient_form_unique S qₖ bₖ (QuadraticMap.comp qₛ l.toLinearMap)).2 (by
    intro v
    change qₛ (l (1 ⊗ₜ[k] v)) = _
    rw [scaleVectorCoordinates_tmul, one_smul]
    exact scale_hyperbolic_map (algebraMap k S) v)
  exact ⟨l, fun x => DFunLike.congr_fun h x⟩

def scaleCliffordEquiv : ScalarClifford qₖ S ≃ₐ[S] CliffordAlgebra qₛ :=
  (CliffordModel.baseChangeEquiv S qₖ bₖ).trans (CliffordAlgebra.equivOfIsometry scaleVectorIsometry)

theorem scaleCliffordEquiv_vector (v : S ⊗[k] (I ⊕ I → k)) :
    scaleCliffordEquiv (vectors qₖ S v) = ι qₛ (scaleVectorCoordinates v) := by
  change CliffordAlgebra.equivOfIsometry (scaleVectorIsometry (k := k) (I := I))
    (CliffordModel.baseChangeEquiv S qₖ bₖ (vectors qₖ S v)) = _
  have hh : CliffordModel.baseChangeEquiv S qₖ bₖ (vectors qₖ S v) = ι _ v :=
    cliffordEquiv_vector qₖ S bₖ v
  rw [hh]
  exact map_apply_ι _ _

theorem scaleCliffordEquiv_reverse (x : ScalarClifford qₖ S) :
    scaleCliffordEquiv (reversion qₖ S x) = reverse (scaleCliffordEquiv x) := by
  change CliffordAlgebra.equivOfIsometry (scaleVectorIsometry (k := k) (I := I))
    (CliffordModel.baseChangeEquiv S qₖ bₖ (reversion qₖ S x)) = _
  rw [baseChangeEquiv_reverse]
  exact map_isometry_reverse _ _

set_option maxHeartbeats 950000 in
theorem scaleCliffordEquiv_even (x : ScalarClifford qₖ S) :
    x ∈ evenPart qₖ S ↔ scaleCliffordEquiv x ∈ evenOdd qₛ 0 := by
  let e := CliffordAlgebra.equivOfIsometry (scaleVectorIsometry (k := k) (S := S) (I := I))
  let x₀ := CliffordModel.baseChangeEquiv S qₖ bₖ x
  have he : e x₀ = scaleCliffordEquiv x := rfl
  have hv : x ∈ evenPart qₖ S ↔ x₀ ∈ evenOdd (coefficientForm S qₖ bₖ) 0 :=
    (cliffordEquiv_even qₖ S bₖ x).symm
  rw [← he, hv]
  constructor
  · intro hx
    change CliffordAlgebra.map (scaleVectorIsometry (k := k) (S := S) (I := I)).toIsometry x₀ ∈ _
    exact map_isometry_evenOdd (scaleVectorIsometry (k := k) (S := S) (I := I)).toIsometry hx
  · intro h
    have h' := map_isometry_evenOdd
      (scaleVectorIsometry (k := k) (I := I) (S := S)).symm.toIsometry h
    change e.symm (e x₀) ∈ _ at h'
    simpa only [AlgEquiv.symm_apply_apply] using h'

/-- Intertwining with the vector action, expressed in the fixed coordinates
on the scalar-extended hyperbolic space. -/
def ScaleCliffordAction (a : (ScalarClifford qₖ S)ˣ) (M : Matrix (I ⊕ I) (I ⊕ I) S) : Prop :=
  ∀ v : S ⊗[k] (I ⊕ I → k),
    a.val * vectors qₖ S v =
      vectors qₖ S (scaleVectorCoordinates.symm (M *ᵥ scaleVectorCoordinates v)) * a.val

theorem scaleCliffordAction_iff {a : (ScalarClifford qₖ S)ˣ}
    {M : (Matrix (I ⊕ I) (I ⊕ I) S)ˣ} :
    ScaleCliffordAction a M.val ↔
      IsVectorAction qₖ S a ((scaleVectorCoordinates.trans (matrixColumnEquiv M)).trans
        scaleVectorCoordinates.symm) := by
  constructor
  · intro h v
    unfold SpinSpecification.conjugate
    change _ = a.val * vectors qₖ S v * a.inv
    rw [h v, mul_assoc, Units.val_inv, mul_one]
    rfl
  · intro h v
    have hv := congrArg (· * a.val) (h v).symm
    change (a.val * vectors qₖ S v * a.inv) * a.val =
      vectors qₖ S (scaleVectorCoordinates.symm (M.val *ᵥ scaleVectorCoordinates v)) * a.val at hv
    rwa [mul_assoc, mul_assoc, a.inv_val, mul_one] at hv

theorem scaleCliffordAction_of_vector {a : (ScalarClifford qₖ S)ˣ}
    {M : Matrix (I ⊕ I) (I ⊕ I) S}
    {g : (S ⊗[k] (I ⊕ I → k)) ≃ₗ[S] (S ⊗[k] (I ⊕ I → k))}
    (hg : IsVectorAction qₖ S a g)
    (hM : LinearMap.toMatrix (Module.Basis.baseChange S bₖ) (Module.Basis.baseChange S bₖ) g.toLinearMap = M) :
    ScaleCliffordAction a M := by
  intro v
  have he : scaleVectorCoordinates (g v) = M *ᵥ scaleVectorCoordinates v := by
    rw [← hM]
    exact (LinearMap.toMatrix_mulVec_repr (Module.Basis.baseChange S bₖ) (Module.Basis.baseChange S bₖ) g.toLinearMap v).symm
  rw [← he, LinearEquiv.symm_apply_apply]
  have h := congrArg (· * a.val) (hg v).symm
  change (a.val * vectors qₖ S v * a.inv) * a.val = vectors qₖ S (g v) * a.val at h
  rwa [mul_assoc, mul_assoc, a.inv_val, mul_one] at h

theorem scaleCliffordAction_unique {a : (ScalarClifford qₖ S)ˣ}
    {M N : Matrix (I ⊕ I) (I ⊕ I) S}
    (hM : ScaleCliffordAction a M) (hN : ScaleCliffordAction a N) : M = N := by
  ext i j
  let v := (scaleVectorCoordinates (k := k) (S := S)).symm (Pi.single j 1)
  have h := a.isUnit.mul_right_cancel ((hM v).symm.trans (hN v))
  have h' := vectors_injective qₖ S bₖ h
  apply_fun (scaleVectorCoordinates (k := k) (S := S)) at h'
  simp only [v, LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at h'
  exact congrFun h' i

theorem scaleCliffordAction_after_map {T : Type u} [CommRing T] [Algebra k T]
    (f : S →ₐ[k] T) {a : (ScalarClifford qₖ S)ˣ} {M : Matrix (I ⊕ I) (I ⊕ I) S}
    (h : ScaleCliffordAction a M) :
    ScaleCliffordAction (Units.map (coefficientMap qₖ S f).toMonoidHom a) (M.map f) := by
  let a' := Units.map (coefficientMap qₖ S f).toMonoidHom a
  let c := scaleVectorCoordinates (k := k) (I := I) (S := T)
  let l := c.symm.toLinearMap.comp ((Matrix.toLin' (M.map f)).comp c.toLinearMap)
  let lhs := (LinearMap.mulLeft T a'.val).comp (vectors qₖ T)
  let rhs := (LinearMap.mulRight T a'.val).comp ((vectors qₖ T).comp l)
  suffices hh : lhs = rhs by
    intro v
    exact DFunLike.congr_fun hh v
  apply (Module.Basis.baseChange T bₖ).ext
  intro j
  let v := (Module.Basis.baseChange S bₖ) j
  have hn : changeModule f v = (Module.Basis.baseChange T bₖ) j := by
    simp [v, Module.Basis.baseChange_apply, changeModule]
  have he : changeModule f (scaleVectorCoordinates.symm (M *ᵥ scaleVectorCoordinates v)) =
      l ((Module.Basis.baseChange T bₖ) j) := by
    apply c.injective
    have hl (x : T ⊗[k] (I ⊕ I → k)) : c (l x) = (M.map f) *ᵥ c x :=
      c.apply_symm_apply _
    rw [hl, scaleVectorCoordinates_natural, LinearEquiv.apply_symm_apply, ← hn]
    change _ = (M.map f) *ᵥ scaleVectorCoordinates (changeModule f v)
    rw [scaleVectorCoordinates_natural]
    funext i
    simp [Matrix.mulVec, dotProduct, Function.comp_apply]
  have hh := congrArg (SpinFunctor.changeCoefficients qₖ f) (h v)
  rw [map_mul, map_mul, changeCoefficients_vector, changeCoefficients_vector, hn, he] at hh
  exact hh

end ExtendedClifford
end ScaleIntrinsicProof

section ScaleNaturalProof
open CliffordAlgebra Matrix LinearAlgebraicGroups.Albert
open scoped Matrix TensorProduct
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (hyperbolicGram matrixColumnEquiv)
open LinearAlgebraicGroups.Albert.SpinSpecification (ScalarClifford vectors reversion evenPart coefficientMap IsVectorAction spinUnits)
open private cliffordEquiv_vector cliffordEquiv_even vectors_injective scalar_tensor_injective
  even_one even_mul reversion_even reversion_mul reversion_scalar scalarCentralizer_baseChange
  changeModule changeModule_coord changeCoefficients_apply changeCoefficients_even
  changeCoefficients_vector changeCoefficients_reverse
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

section NaturalPlaneClifford

universe w

variable {k I S : Type u} [Field k] [Fintype I] [DecidableEq I] [CommRing S] [Algebra k S]

local instance scaleCliffordIndexOrder : LinearOrder (I ⊕ I) :=
  LinearOrder.lift' (Fintype.equivFin (I ⊕ I)) (Fintype.equivFin (I ⊕ I)).injective

local notation "qₖ" => (hyperbolicForm I k)
local notation "qₛ" => (hyperbolicForm I S)
local notation "bₖ" => (Pi.basisFun k (I ⊕ I))

def scalarScaleUnit : Sˣ →* (ScalarClifford qₖ S)ˣ :=
  Units.map (algebraMap S _).toMonoidHom

theorem scalarScale_injective : Function.Injective (scalarScaleUnit (k := k) (I := I) (S := S)) := by
  intro r s h
  exact Units.ext (scalar_tensor_injective qₖ S bₖ (congrArg Units.val h))

theorem even_scalarScale (r : Sˣ) : (scalarScaleUnit (k := k) (I := I) r).val ∈ evenPart qₖ S := by
  change algebraMap S _ (r : S) ∈ _
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (even_one qₖ S bₖ)

theorem even_inverse_of_unit_norm (a : (ScalarClifford qₖ S)ˣ)
    (ha : a.val ∈ evenPart qₖ S) (r : Sˣ) (hr : reversion qₖ S a.val * a.val = algebraMap S _ (r : S)) :
    a.inv ∈ evenPart qₖ S := by
  have h : reversion qₖ S a.val = algebraMap S _ (r : S) * a.inv := by
    have hh := congrArg (· * a.inv) hr
    rwa [mul_assoc, a.val_inv, mul_one] at hh
  have h' : (↑r⁻¹ : S) • reversion qₖ S a.val = a.inv := by
    rw [h, Algebra.smul_def, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [← h']
  exact Submodule.smul_mem _ _ (reversion_even qₖ S bₖ ha)

theorem scaleScalarCentralizer {x : ScalarClifford qₖ S} (he : x ∈ evenPart qₖ S)
    (hc : ∀ v, Commute x (vectors qₖ S v)) : ∃ r : S, x = algebraMap S _ r := by
  apply scalarCentralizer_baseChange qₖ S bₖ _ he hc
  intro s hs _
  obtain ⟨i, hi⟩ := hs
  refine ⟨i, hi, hyperbolicGram I k *ᵥ Pi.single i 1, ?_⟩
  apply LinearMap.ext
  intro v
  have hg := hyperbolicGram_properties (I := I) (K := k)
  rw [scale_hyperbolic_polar, ← Matrix.vecMul_transpose, dotProduct_mulVec, Matrix.vecMul_vecMul,
    hg.1, hg.2, Matrix.vecMul_one, single_dotProduct]
  simp

theorem scaleCliffordAction_ratio {a b : (ScalarClifford qₖ S)ˣ}
    {M : Matrix (I ⊕ I) (I ⊕ I) S}
    (ha : ScaleCliffordAction a M) (hb : ScaleCliffordAction b M)
    (hea : a.val ∈ evenPart qₖ S) (hea' : a.inv ∈ evenPart qₖ S)
    (heb : b.val ∈ evenPart qₖ S) (heb' : b.inv ∈ evenPart qₖ S) :
    ∃! r : Sˣ, a = scalarScaleUnit r * b := by
  let c := b⁻¹ * a
  have hcomm (v : S ⊗[k] (I ⊕ I → k)) : Commute c.val (vectors qₖ S v) := by
    let x := vectors qₖ S v
    let y := vectors qₖ S (scaleVectorCoordinates.symm (M *ᵥ scaleVectorCoordinates v))
    have h : b.inv * y = x * b.inv := by
      calc
        b.inv * y = b.inv * (y * b.val) * b.inv := by
          rw [mul_assoc, mul_assoc, b.val_inv, mul_one]
        _ = x * b.inv := by rw [← hb v, ← mul_assoc b.inv b.val, b.inv_val, one_mul]
    change (b.inv * a.val) * x = x * (b.inv * a.val)
    rw [mul_assoc, ha v, ← mul_assoc, h, mul_assoc]
  obtain ⟨r, hr⟩ := scaleScalarCentralizer (even_mul qₖ S bₖ heb' hea) hcomm
  have hc' : c.inv ∈ evenPart qₖ S := even_mul qₖ S bₖ hea' heb
  obtain ⟨s, hs⟩ := scaleScalarCentralizer hc' (fun v => (hcomm v).units_inv_left)
  have hrs : r * s = 1 := by
    apply scalar_tensor_injective qₖ S bₖ
    rw [map_mul, ← hr, ← hs, map_one]
    exact c.val_inv
  let r' : Sˣ := ⟨r, s, hrs, (mul_comm s r).trans hrs⟩
  have hc : c = scalarScaleUnit r' := Units.ext hr
  have ha' : a = b * scalarScaleUnit r' := inv_mul_eq_iff_eq_mul.mp hc
  have hr' : a = scalarScaleUnit r' * b := by
    rw [ha']
    exact Units.ext (Algebra.commutes (r' : S) b.val).symm
  refine ⟨r', hr', ?_⟩
  intro t ht
  exact scalarScale_injective (mul_right_cancel (ht.symm.trans hr'))

theorem cliffordScalar_action {a : (ScalarClifford qₖ S)ˣ} {M : Matrix (I ⊕ I) (I ⊕ I) S}
    (h : ScaleCliffordAction a M) (r : Sˣ) : ScaleCliffordAction (scalarScaleUnit r * a) M := by
  intro v
  change (algebraMap S _ (r : S) * a.val) * vectors qₖ S v = _ * (algebraMap S _ (r : S) * a.val)
  rw [mul_assoc, h v, ← mul_assoc, Algebra.commutes (r : S), mul_assoc]

theorem cliffordScalar_norm (a : (ScalarClifford qₖ S)ˣ) (r : Sˣ) :
    reversion qₖ S (scalarScaleUnit r * a : (ScalarClifford qₖ S)ˣ).val *
      (scalarScaleUnit r * a : (ScalarClifford qₖ S)ˣ).val =
      algebraMap S _ ((r : S) ^ 2) * (reversion qₖ S a.val * a.val) := by
  change reversion qₖ S (algebraMap S _ (r : S) * a.val) * (algebraMap S _ (r : S) * a.val) = _
  rw [reversion_mul qₖ S bₖ, reversion_scalar qₖ S bₖ, map_pow, pow_two]
  let z := algebraMap S (ScalarClifford qₖ S) (r : S)
  let v := reversion qₖ S a.val
  have hc : z * v = v * z := Algebra.commutes (r : S) v
  change (v * z) * (z * a.val) = (z * z) * (v * a.val)
  calc
    _ = (z * v) * (z * a.val) := congrArg (· * (z * a.val)) hc.symm
    _ = z * ((v * z) * a.val) := by simp only [mul_assoc]
    _ = z * ((z * v) * a.val) := congrArg (fun v' => z * (v' * a.val)) hc.symm
    _ = _ := by simp only [mul_assoc]

theorem cliffordScale_spin {a : (ScalarClifford qₖ S)ˣ} {M : (Matrix (I ⊕ I) (I ⊕ I) S)ˣ}
    (h : ScaleCliffordAction a M.val) (he : a.val ∈ evenPart qₖ S)
    (hn : reversion qₖ S a.val * a.val = 1) :
    a ∈ spinUnits qₖ S := by
  let c := scaleVectorCoordinates (k := k) (I := I) (S := S)
  let g := (c.trans (matrixColumnEquiv M)).trans c.symm
  have hg : IsVectorAction qₖ S a g := scaleCliffordAction_iff.mp h
  refine ⟨he, hn, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨g x, hg x⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨g.symm x, ?_⟩
    have hh := hg (g.symm x)
    rw [LinearEquiv.apply_symm_apply, SpinSpecification.conjugate] at hh
    rw [SpinSpecification.conjugate, hh]
    change _ = a.inv * (a.val * vectors qₖ S (g.symm x) * a.inv) * a.val
    rw [← mul_assoc a.inv, ← mul_assoc a.inv a.val, a.inv_val, one_mul, mul_assoc, a.inv_val, mul_one]

variable (p : ScalePlane I k)

def cliffordPlaneVacuum : CliffordAlgebra qₖ :=
  CliffordAlgebra.map p.isometry (exteriorVacuum k)

theorem cliffordPlaneVacuum_ne_zero : cliffordPlaneVacuum p ≠ 0 := by
  let e := (splitExteriorEquiv k 2).trans
    (LinearMap.toMatrixAlgEquiv ((Pi.basisFun k (Fin 2)).ExteriorAlgebra))
  let : IsSimpleRing (SplitClifford k 2) := IsSimpleRing.of_ringEquiv e.toRingEquiv.symm inferInstance
  obtain ⟨b, _⟩ := CliffordModel.ordered_basis qₖ bₖ
  let : Nontrivial (CliffordAlgebra qₖ) := ⟨⟨_, _, b.ne_zero ∅⟩⟩
  let j := CliffordAlgebra.map p.isometry
  exact fun h => exteriorVacuum_ne_zero (j.toRingHom.injective (h.trans j.map_zero.symm))

def cliffordPlaneVacuumAt : ScalarClifford qₖ S := 1 ⊗ₜ[k] cliffordPlaneVacuum p

theorem cliffordPlaneVacuumAt_scalar (r : S)
    (h : algebraMap S (ScalarClifford qₖ S) r * cliffordPlaneVacuumAt p = cliffordPlaneVacuumAt p) :
    r = 1 := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k (cliffordPlaneVacuum_ne_zero p)
  let f := (TensorProduct.AlgebraTensorModule.rid k S S).toLinearMap.comp (LinearMap.baseChange S l)
  rw [cliffordPlaneVacuumAt, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
  have hf := congrArg f h
  simpa [f, LinearMap.baseChange_tmul, hl] using hf

theorem cliffordPlaneVacuum_value {A : Type u} [CommRing A] (p : ScalePlane I A) (i : Fin 2) :
    p.vector ((Pi.basisFun A (Fin 2)).coord i, 0) = p.right.col i ∧
    p.vector (0, Pi.single i 1) = p.left.col i := by
  have hcoord : dualCoordinates ((Pi.basisFun A (Fin 2)).coord i) = Pi.single i 1 := by
    funext j
    rw [dualCoordinates_apply, ← Pi.basisFun_apply]
    by_cases h : i = j <;> simp [Module.Basis.coord_apply, h, eq_comm]
  simp only [ScalePlane.vector_apply, map_zero, Matrix.mulVec_zero, hcoord,
    Matrix.mulVec_single_one, add_zero, zero_add, and_self]

theorem cliffordPlaneVacuum_map :
    scaleCliffordEquiv (cliffordPlaneVacuumAt (S := S) p) =
      CliffordAlgebra.map (p.map (algebraMap k S)).isometry (exteriorVacuum S) := by
  let e := scaleCliffordEquiv (k := k) (S := S) (I := I)
  let j := (Algebra.TensorProduct.includeRight : CliffordAlgebra qₖ →ₐ[k] ScalarClifford qₖ S)
  have h (v : I ⊕ I → k) : e (j (ι qₖ v)) = ι qₛ (algebraMap k S ∘ v) := by
    change e (vectors qₖ S (1 ⊗ₜ[k] v)) = _
    rw [scaleCliffordEquiv_vector, scaleVectorCoordinates_tmul, one_smul]
  have hv {L : Matrix (I ⊕ I) (Fin 2) k} (i : Fin 2) :
      (L.map (algebraMap k S)).col i = algebraMap k S ∘ L.col i := rfl
  change e (j (CliffordAlgebra.map p.isometry (exteriorVacuum k))) = _
  simp only [exteriorVacuum, map_mul, map_sub, map_one, map_apply_ι]
  change (1 - e (j (ι qₖ (p.vector (0, Pi.single 0 1)))) *
        e (j (ι qₖ (p.vector ((Pi.basisFun k (Fin 2)).coord 0, 0))))) *
      (1 - e (j (ι qₖ (p.vector (0, Pi.single 1 1)))) *
        e (j (ι qₖ (p.vector ((Pi.basisFun k (Fin 2)).coord 1, 0))))) = _
  let pS := p.map (algebraMap k S)
  have hVS (x : Module.Dual S (CreationSpace S 2) × CreationSpace S 2) :
      pS.isometry x = pS.vector x := rfl
  have hL : pS.left = p.left.map (algebraMap k S) := rfl
  have hR : pS.right = p.right.map (algebraMap k S) := p.right_map _
  change _ = (1 - ι qₛ (pS.isometry (0, Pi.single 0 1)) *
      ι qₛ (pS.isometry ((Pi.basisFun S (Fin 2)).coord 0, 0))) *
    (1 - ι qₛ (pS.isometry (0, Pi.single 1 1)) *
      ι qₛ (pS.isometry ((Pi.basisFun S (Fin 2)).coord 1, 0)))
  simp only [h, (cliffordPlaneVacuum_value p _).1, (cliffordPlaneVacuum_value p _).2,
    hVS, (cliffordPlaneVacuum_value pS _).1, (cliffordPlaneVacuum_value pS _).2, hL, hR, hv]

def liftedPlaneAction (a : (Matrix (Fin 2) (Fin 2) S)ˣ) : (ScalarClifford qₖ S)ˣ :=
  Units.map (scaleCliffordEquiv (k := k) (I := I)).symm.toMonoidHom
    (planeCliffordLift (p.map (algebraMap k S)) a)

theorem liftedPlaneAction_properties (a : (Matrix (Fin 2) (Fin 2) S)ˣ) :
    let c := liftedPlaneAction p a
    c.val ∈ evenPart qₖ S ∧
    reversion qₖ S c.val * c.val = algebraMap S _ a.val.det ∧
    ScaleCliffordAction c ((p.map (algebraMap k S)).action a) ∧
    c.val * cliffordPlaneVacuumAt p = cliffordPlaneVacuumAt p := by
  let e := scaleCliffordEquiv (k := k) (S := S) (I := I)
  let pS := p.map (algebraMap k S)
  let c := liftedPlaneAction p a
  have h : e c.val = (planeCliffordLift pS a).val := e.apply_symm_apply _
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (scaleCliffordEquiv_even _).2
    change e c.val ∈ _
    rw [h]
    exact planeClifford_even pS a
  · apply e.injective
    rw [map_mul, show e (reversion qₖ S c.val) = reverse (e c.val) from scaleCliffordEquiv_reverse _,
      h, e.commutes, planeClifford_norm]
  · intro v
    apply e.injective
    change e (c.val * vectors qₖ S v) = e
      (vectors qₖ S (scaleVectorCoordinates.symm (pS.action a *ᵥ scaleVectorCoordinates v)) * c.val)
    have hv (z : S ⊗[k] (I ⊕ I → k)) : e (vectors qₖ S z) = ι qₛ (scaleVectorCoordinates z) :=
      scaleCliffordEquiv_vector z
    rw [map_mul, map_mul, h, hv, hv, LinearEquiv.apply_symm_apply]
    exact planeClifford_action pS a (scaleVectorCoordinates v)
  · apply e.injective
    rw [map_mul, h, show e (cliffordPlaneVacuumAt p) = _
      from cliffordPlaneVacuum_map p, planeClifford_vacuum]

theorem liftedPlaneAction_unique {a b : (ScalarClifford qₖ S)ˣ}
    {M : Matrix (I ⊕ I) (I ⊕ I) S}
    (ha : ScaleCliffordAction a M) (hb : ScaleCliffordAction b M)
    (ea : a.val ∈ evenPart qₖ S) (eb : b.val ∈ evenPart qₖ S)
    (r s : Sˣ)
    (hna : reversion qₖ S a.val * a.val = algebraMap S _ (r : S))
    (hnb : reversion qₖ S b.val * b.val = algebraMap S _ (s : S))
    (hva : a.val * cliffordPlaneVacuumAt p = cliffordPlaneVacuumAt p)
    (hvb : b.val * cliffordPlaneVacuumAt p = cliffordPlaneVacuumAt p) :
    a = b := by
  obtain ⟨c, hc, _⟩ := scaleCliffordAction_ratio ha hb ea
    (even_inverse_of_unit_norm a ea r hna) eb (even_inverse_of_unit_norm b eb s hnb)
  have hh : algebraMap S (ScalarClifford qₖ S) (c : S) * cliffordPlaneVacuumAt p = cliffordPlaneVacuumAt p := by
    rw [hc, Units.val_mul, mul_assoc, hvb] at hva
    exact hva
  have h1 : c = 1 := Units.ext (cliffordPlaneVacuumAt_scalar p c.val hh)
  rw [hc, h1, map_one, one_mul]

open private exteriorImplementer exterior_implementer_even exterior_implementer_norm
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

theorem liftedPlaneAction_one :
    liftedPlaneAction (S := S) p (1 : (Matrix (Fin 2) (Fin 2) S)ˣ) = 1 := by
  simp [liftedPlaneAction, planeCliffordLift, exteriorImplementer_one]

theorem liftedPlaneAction_mul (a b : (Matrix (Fin 2) (Fin 2) S)ˣ) :
    liftedPlaneAction p (a * b) = liftedPlaneAction p a * liftedPlaneAction p b := by
  simp only [liftedPlaneAction, planeCliffordLift, map_mul, exteriorImplementer_mul]

variable {T : Type u} [CommRing T] [Algebra k T]

theorem matrix_algebraMap_comp {k S T : Type u} [CommRing k] [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) {ι : Type v} {κ : Type w} (M : Matrix ι κ k) :
    (M.map (algebraMap k S)).map f = M.map (algebraMap k T) := by
  ext i j
  exact f.commutes (M i j)

theorem planeAction_after_map (f : S →ₐ[k] T) (a : (Matrix (Fin 2) (Fin 2) S)ˣ) :
    ((p.map (algebraMap k S)).action a).map f =
      (p.map (algebraMap k T)).action (Matrix.GeneralLinearGroup.map f.toRingHom a) := by
  have hv : (Matrix.GeneralLinearGroup.map f.toRingHom a).val = a.val.map f := rfl
  have hi : (Matrix.GeneralLinearGroup.map f.toRingHom a).inv = a.inv.map f := rfl
  rw [ScalePlane.action, ScalePlane.action, hv, hi]
  simp only [Matrix.map_add f (map_add f), Matrix.map_sub f (map_sub f),
    Matrix.map_mul, Matrix.transpose_map,
    Matrix.map_one _ (map_zero f) (map_one f), ScalePlane.right_map, ScalePlane.rightCoord_map]
  change _ = 1 - p.left.map (algebraMap k T) * p.leftCoord.map (algebraMap k T) -
    p.right.map (algebraMap k T) * p.rightCoord.map (algebraMap k T) +
    p.left.map (algebraMap k T) * a.val.map f * p.leftCoord.map (algebraMap k T) +
    p.right.map (algebraMap k T) * (a.inv.map f).transpose * p.rightCoord.map (algebraMap k T)
  simp only [ScalePlane.map, matrix_algebraMap_comp f]

theorem scalarScale_natural (f : S →ₐ[k] T) (r : Sˣ) :
    Units.map (coefficientMap qₖ S f).toMonoidHom (scalarScaleUnit r) =
      scalarScaleUnit (Units.map f.toMonoidHom r) := by
  apply Units.ext
  change coefficientMap qₖ S f (algebraMap S _ (r : S)) = algebraMap T _ (f r.val)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem liftedPlaneAction_natural (f : S →ₐ[k] T) (a : (Matrix (Fin 2) (Fin 2) S)ˣ) :
    Units.map (coefficientMap qₖ S f).toMonoidHom (liftedPlaneAction p a) =
      liftedPlaneAction p (Matrix.GeneralLinearGroup.map f.toRingHom a) := by
  let a' := Matrix.GeneralLinearGroup.map f.toRingHom a
  let c := liftedPlaneAction p a
  let c' := Units.map (coefficientMap qₖ S f).toMonoidHom c
  let h := liftedPlaneAction_properties p a
  let h' := liftedPlaneAction_properties p a'
  have hc := scaleCliffordAction_after_map f h.2.2.1
  rw [planeAction_after_map] at hc
  have he : c'.val ∈ evenPart qₖ T := changeCoefficients_even qₖ f h.1
  have hn : reversion qₖ T c'.val * c'.val = algebraMap T _ (f a.val.det) := by
    let j := SpinFunctor.changeCoefficients qₖ f
    change reversion qₖ T (j c.val) * j c.val = _
    rw [← changeCoefficients_reverse, ← map_mul, h.2.1]
    rfl
  have hp : coefficientMap qₖ S f (cliffordPlaneVacuumAt p) =
      cliffordPlaneVacuumAt p := by simp [coefficientMap, cliffordPlaneVacuumAt]
  have hv : c'.val * cliffordPlaneVacuumAt p = cliffordPlaneVacuumAt p := by
    have hh := congrArg (coefficientMap qₖ S f) h.2.2.2
    rw [map_mul, hp] at hh
    exact hh
  apply liftedPlaneAction_unique p hc h'.2.2.1 he h'.1
    (Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det a))
    (Matrix.GeneralLinearGroup.det a') hn h'.2.1 hv h'.2.2.2

end NaturalPlaneClifford
end ScaleNaturalProof

section ScaleTransportProof
open AlgebraicGeometry CategoryTheory Matrix LinearAlgebraicGroups.Albert
open scoped Matrix TensorProduct CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open CliffordAlgebra SpinSpecification

section SplitSpinTransport

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F}
  (P : SpinModel G D)

def splitSpinPointEquiv (S : TestAlgebra K) :
    Points G.val.X ((restrictTestAlgebra F K).obj S) ≃* Points P.splitCover.spin.val.X S :=
  (baseChangePointGroupEquiv K G.val S).symm.trans
    (Iso.groupIsoToMulEquiv (((groupPointsFunctor K).mapIso P.splitSource).app S))

theorem splitSpinPointEquiv_apply (S : TestAlgebra K)
    (g : Points G.val.X ((restrictTestAlgebra F K).obj S)) :
    splitSpinPointEquiv P S g =
      (baseChangePointGroupEquiv K G.val S).symm g ≫ P.splitSource.hom.hom.hom := rfl

theorem splitSpinPointEquiv_natural {S T : TestAlgebra K} (f : S ⟶ T)
    (g : Points G.val.X ((restrictTestAlgebra F K).obj S)) :
    splitSpinPointEquiv P T (mapPoints ((restrictTestAlgebra F K).map f) g) =
      mapPoints f (splitSpinPointEquiv P S g) := by
  rw [splitSpinPointEquiv_apply, splitSpinPointEquiv_apply]
  have he : mapPoints f ((baseChangePointGroupEquiv K G.val S).symm g ≫ P.splitSource.hom.hom.hom) =
      mapPoints f ((baseChangePointGroupEquiv K G.val S).symm g) ≫ P.splitSource.hom.hom.hom :=
    (Category.assoc _ _ _).symm
  rw [he]
  apply congrArg (fun x : Points ((groupBaseChange F K).obj G.val).X T => x ≫ P.splitSource.hom.hom.hom)
  apply (baseChangePointGroupEquiv K G.val T).injective
  rw [MulEquiv.apply_symm_apply]
  change _ = baseChangePoint F K G.val.X T
    (mapPoints f ((baseChangePointGroupEquiv K G.val S).symm g))
  have h := baseChangePointsNaturality F K G.val.X f ((baseChangePointGroupEquiv K G.val S).symm g)
  exact (congrArg (mapPoints ((restrictTestAlgebra F K).map f))
    ((baseChangePointGroupEquiv K G.val S).apply_symm_apply g)).symm.trans h.symm

def restrictedSpinPoints (S : TestAlgebra K) :
    Points G.val.X ((restrictTestAlgebra F K).obj S) →* (ScalarClifford (hyperbolicForm I K) S)ˣ :=
  (P.splitCover.spinPoints S).comp (splitSpinPointEquiv P S).toMonoidHom

theorem restrictedSpinPoints_injective (S : TestAlgebra K) :
    Function.Injective (restrictedSpinPoints P S) :=
  (P.splitCover.spinRepresents.1 S).1.comp (splitSpinPointEquiv P S).injective

theorem restrictedSpinPoints_range (S : TestAlgebra K) :
    Set.range (restrictedSpinPoints P S) = spinUnits (hyperbolicForm I K) S := by
  rw [restrictedSpinPoints, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    (splitSpinPointEquiv P S).surjective.range_comp]
  exact (P.splitCover.spinRepresents.1 S).2

theorem restrictedSpinPoints_natural {S T : TestAlgebra K} (f : S ⟶ T)
    (g : Points G.val.X ((restrictTestAlgebra F K).obj S)) :
    restrictedSpinPoints P T (mapPoints ((restrictTestAlgebra F K).map f) g) =
      Units.map (coefficientMap (hyperbolicForm I K) S f.hom).toMonoidHom (restrictedSpinPoints P S g) := by
  change P.splitCover.spinPoints T
    (splitSpinPointEquiv P T (mapPoints ((restrictTestAlgebra F K).map f) g)) = _
  rw [splitSpinPointEquiv_natural]
  exact P.splitCover.spinRepresents.2 f (splitSpinPointEquiv P S g)

def fullMatrixComparison (S : TestAlgebra K) :=
  (P.matrixComparison S).choose

theorem fullMatrixComparison_formula (S : TestAlgebra K) (r : S) (x : ρ.fixedSubalgebra) :
    fullMatrixComparison P S (r ⊗ₜ[F] x) = r • x.val.map (algebraMap K S) :=
  (P.matrixComparison S).choose_spec.1 r x

theorem restrictedSpinPoints_action (S : TestAlgebra K)
    (g : Points G.val.X ((restrictTestAlgebra F K).obj S)) :
    ScaleCliffordAction (restrictedSpinPoints P S g)
      (fullMatrixComparison P S (spinVectorProjection P _ g).val) := by
  let b := baseChangePointGroupEquiv K G.val S
  let x := b.symm g
  let y := splitSpinPointEquiv P S g
  obtain ⟨a, ha, hmatrix⟩ := P.splitCover.vector S y
  apply scaleCliffordAction_of_vector ha
  let f := P.projection ≫ P.inclusion
  have hc : (groupBaseChange F K).map f ≫ P.splitFull.hom =
      P.splitSource.hom ≫ P.splitCover.projection ≫ P.splitCover.inclusion := by
    unfold f
    rw [Functor.map_comp, Category.assoc, P.inclusionComparison, ← Category.assoc,
      P.projectionComparison, Category.assoc]
  let z : Points ((groupBaseChange F K).obj P.full.val).X S :=
    x ≫ ((groupBaseChange F K).map f).hom.hom
  have hz : baseChangePoint F K P.full.val.X S z = g ≫ f.hom.hom := by
    have h := baseChangePointsSchemeNaturality F K f.hom.hom S x
    exact h.trans (congrArg (· ≫ f.hom.hom) (b.apply_symm_apply g))
  have hy : y ≫ (P.splitCover.projection ≫ P.splitCover.inclusion).hom.hom =
      z ≫ P.splitFull.hom.hom.hom := by
    rw [show y = x ≫ P.splitSource.hom.hom.hom from rfl]
    change (x ≫ P.splitSource.hom.hom.hom) ≫ _ =
      (x ≫ ((groupBaseChange F K).map f).hom.hom) ≫ _
    simp only [Category.assoc]
    exact congrArg (fun c => x ≫ c.hom.hom) hc.symm
  change LinearMap.toMatrix ((Pi.basisFun K (I ⊕ I)).baseChange S) _ a.toLinearMap =
    fullMatrixComparison P S (P.fullPoints _ (g ≫ f.hom.hom)).val
  change LinearMap.toMatrix ((Pi.basisFun K (I ⊕ I)).baseChange S) _ a.toLinearMap =
    (P.splitCover.orthogonal.points S (y ≫ (P.splitCover.projection ≫ P.splitCover.inclusion).hom.hom)).val.val at hmatrix
  rw [hmatrix, hy, ← (P.matrixComparison S).choose_spec.2 z, hz]
  rfl

theorem restrictedSpinPoints_scalar (S : TestAlgebra K)
    (z : Points P.kernel.group.X ((restrictTestAlgebra F K).obj S)) :
    (restrictedSpinPoints P S (z ≫ P.kernel.inclusion.hom.hom)).val =
      algebraMap S _ (P.kernelPoints ((restrictTestAlgebra F K).obj S) z).val.val := by
  let w := (baseChangePointGroupEquiv K P.kernel.group S).symm z
  let a : Points ((groupBaseChange F K).obj G.val).X S :=
    w ≫ ((groupBaseChange F K).map P.kernel.inclusion).hom.hom
  have ha : (baseChangePointGroupEquiv K G.val S).symm
      (z ≫ P.kernel.inclusion.hom.hom) = a := by
    apply (baseChangePointGroupEquiv K G.val S).injective
    rw [MulEquiv.apply_symm_apply]
    have hh := baseChangePointsSchemeNaturality F K P.kernel.inclusion.hom.hom S w
    exact (congrArg (· ≫ P.kernel.inclusion.hom.hom)
      ((baseChangePointGroupEquiv K P.kernel.group S).apply_symm_apply z)).symm.trans hh.symm
  have he : a ≫ P.splitSource.hom.hom.hom =
      (w ≫ P.splitKernel.hom.hom.hom) ≫ P.splitCover.kernel.inclusion.hom.hom := by
    change (w ≫ _) ≫ _ = (w ≫ _) ≫ _
    simp only [Category.assoc]
    exact congrArg (fun c => w ≫ c.hom.hom) P.kernelComparison
  change (P.splitCover.spinPoints S (splitSpinPointEquiv P S _)).val = _
  rw [splitSpinPointEquiv_apply, ha, he, P.splitCover.scalar]
  apply congrArg (algebraMap S (ScalarClifford (hyperbolicForm I K) S))
  have hs := P.scalarComparison S w
  have hz : baseChangePoint F K P.kernel.group.X S w = z :=
    (baseChangePointGroupEquiv K P.kernel.group S).apply_symm_apply z
  rw [hz] at hs
  exact hs.symm

end SplitSpinTransport
end ScaleTransportProof

section ScaleSplitProof
open AlgebraicGeometry CategoryTheory Matrix LinearAlgebraicGroups.Albert
open scoped Matrix TensorProduct CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (degree isCentralSimple)
open LinearAlgebraicGroups.Albert.SpinSpecification

open private even_mul scalar_tensor_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

section SplitScaleEquivalence

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F}
  {hB : isCentralSimple F B} {d : ℕ}
  (P : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
  (hd : degree F B = 2)
  {J : Type u} [Fintype J] (b : Module.Basis J F B)
  (hscalar : QuadraticPairScalarExtension.{u}) (htrace : TraceOrthogonality.{u})
  (hsplit : SplitSemitrace.{u})

local notation "qₖ" => (hyperbolicForm I K)
local notation "pₖ" => (quaternionScalePlane Q hd hscalar htrace hsplit)
local notation "R(" S ")" => (restrictTestAlgebraObj F K S)

def quaternionMatrixUnit (S : TestAlgebra K) :
    (R(S) ⊗[F] B)ˣ →* (Matrix (Fin 2) (Fin 2) S)ˣ :=
  Units.map (splitQuaternionAt (quaternionMatrixEquiv Q hd) S).toMonoidHom

theorem quaternionMatrixUnit_natural {S T : TestAlgebra K} (f : S ⟶ T)
    (t : (R(S) ⊗[F] B)ˣ) :
    quaternionMatrixUnit Q hd T (Units.map (tensorMap B ((restrictTestAlgebra F K).map f).hom).toMonoidHom t) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (quaternionMatrixUnit Q hd S t) :=
  Units.ext (splitQuaternionAt_natural (quaternionMatrixEquiv Q hd) f t.val)

theorem quaternionMatrixUnit_norm (S : TestAlgebra K) (t : (R(S) ⊗[F] B)ˣ) :
    (quaternionMatrixUnit Q hd S t).val.det = (quaternionNormAt b hB (R(S)) t : S) :=
  splitQuaternionAt_norm b 2 hd (quaternionMatrixEquiv Q hd) S t

def spinScaleLift (S : TestAlgebra K) : ((R(S) ⊗[F] B)ˣ × Sˣ) →* (ScalarClifford qₖ S)ˣ where
  toFun z := scalarScaleUnit z.2⁻¹ * liftedPlaneAction pₖ (quaternionMatrixUnit Q hd S z.1)
  map_one' := by simp [liftedPlaneAction_one]
  map_mul' z w := by
    change scalarScaleUnit (z.2 * w.2)⁻¹ * liftedPlaneAction pₖ (quaternionMatrixUnit Q hd S (z.1 * w.1)) = _
    rw [_root_.mul_inv_rev, mul_comm w.2⁻¹ z.2⁻¹, map_mul, map_mul, liftedPlaneAction_mul]
    let L := liftedPlaneAction pₖ (quaternionMatrixUnit Q hd S z.1)
    let M := liftedPlaneAction pₖ (quaternionMatrixUnit Q hd S w.1)
    have h : Commute (scalarScaleUnit w.2⁻¹) L :=
      Units.ext (Algebra.commutes (↑w.2⁻¹ : S) L.val)
    change (scalarScaleUnit z.2⁻¹ * scalarScaleUnit w.2⁻¹) * (L * M) =
      (scalarScaleUnit z.2⁻¹ * L) * (scalarScaleUnit w.2⁻¹ * M)
    calc
      _ = scalarScaleUnit z.2⁻¹ * ((scalarScaleUnit w.2⁻¹ * L) * M) := by simp only [mul_assoc]
      _ = scalarScaleUnit z.2⁻¹ * ((L * scalarScaleUnit w.2⁻¹) * M) := by rw [h.eq]
      _ = _ := by simp only [mul_assoc]

theorem spinScaleLift_natural {S T : TestAlgebra K} (f : S ⟶ T)
    (t : (R(S) ⊗[F] B)ˣ) (s : Sˣ) :
    spinScaleLift Q hd hscalar htrace hsplit T
        (Units.map (tensorMap B ((restrictTestAlgebra F K).map f).hom).toMonoidHom t,
          Units.map f.hom.toMonoidHom s) =
      Units.map (coefficientMap qₖ S f.hom).toMonoidHom
        (spinScaleLift Q hd hscalar htrace hsplit S (t,s)) := by
  change scalarScaleUnit (Units.map f.hom.toMonoidHom s)⁻¹ * liftedPlaneAction pₖ
    (quaternionMatrixUnit Q hd T (Units.map (tensorMap B ((restrictTestAlgebra F K).map f).hom).toMonoidHom t)) =
      Units.map (coefficientMap qₖ S f.hom).toMonoidHom
        (scalarScaleUnit s⁻¹ * liftedPlaneAction pₖ (quaternionMatrixUnit Q hd S t))
  rw [map_mul, scalarScale_natural, ← map_inv, liftedPlaneAction_natural, quaternionMatrixUnit_natural]

theorem spinScaleLift_even (S : TestAlgebra K) (t : (R(S) ⊗[F] B)ˣ) (s : Sˣ) :
    (spinScaleLift Q hd hscalar htrace hsplit S (t, s)).val ∈ evenPart qₖ S := by
  let : LinearOrder (I ⊕ I) :=
    LinearOrder.lift' (Fintype.equivFin (I ⊕ I)) (Fintype.equivFin (I ⊕ I)).injective
  exact even_mul qₖ S (Pi.basisFun K (I ⊕ I))
    (even_scalarScale s⁻¹) (liftedPlaneAction_properties pₖ (quaternionMatrixUnit Q hd S t)).1

theorem spinScaleLift_action (S : TestAlgebra K) (t : (R(S) ⊗[F] B)ˣ) (s : Sˣ) :
    ScaleCliffordAction (spinScaleLift Q hd hscalar htrace hsplit S (t, s))
      (fullMatrixComparison P S (quaternionScale Q (R(S)) t).val) := by
  let R := R(S)
  let : Algebra K R := S.algebra
  let : IsScalarTower F K R := IsScalarTower.of_algebraMap_eq' rfl
  have h := quaternionScale_matrix Q hd R (fullMatrixComparison P S)
    (fullMatrixComparison_formula P S) hscalar htrace hsplit t
  rw [h]
  exact cliffordScalar_action
    (liftedPlaneAction_properties pₖ (quaternionMatrixUnit Q hd S t)).2.2.1 s⁻¹

theorem spinScaleLift_norm (S : TestAlgebra K) (t : (R(S) ⊗[F] B)ˣ) (s : Sˣ) :
    let a := spinScaleLift Q hd hscalar htrace hsplit S (t, s)
    reversion qₖ S a.val * a.val = 1 ↔ quaternionNormAt b hB (R(S)) t = s ^ 2 := by
  let a := quaternionMatrixUnit Q hd S t
  let L := liftedPlaneAction pₖ a
  let c := scalarScaleUnit s⁻¹ * L
  have hnorm : reversion qₖ S c.val * c.val =
      algebraMap S _ ((↑s⁻¹ : S)^2 * (quaternionNormAt b hB (R(S)) t : S)) := by
    rw [cliffordScalar_norm L s⁻¹, (liftedPlaneAction_properties pₖ a).2.1, ← map_mul]
    rw [quaternionMatrixUnit_norm Q hd b]
  change reversion qₖ S c.val * c.val = 1 ↔ _
  rw [hnorm]
  let : LinearOrder (I ⊕ I) :=
    LinearOrder.lift' (Fintype.equivFin (I ⊕ I)) (Fintype.equivFin (I ⊕ I)).injective
  rw [← (algebraMap S (ScalarClifford qₖ S)).map_one, (scalar_tensor_injective qₖ S (Pi.basisFun K (I ⊕ I))).eq_iff]
  have he : ((↑s⁻¹ : S)^2 * (s : S)^2) = 1 := by rw [← mul_pow, Units.inv_mul, one_pow]
  constructor
  · intro h
    apply Units.ext
    change (quaternionNormAt b hB (R(S)) t : S) = (s : S)^2
    calc
      _ = (s : S)^2 * ((↑s⁻¹ : S)^2 * (quaternionNormAt b hB (R(S)) t : S)) := by
        rw [← mul_assoc, mul_comm ((s : S)^2), he, one_mul]
      _ = _ := by rw [h, mul_one]
  · intro h
    rw [congrArg Units.val h]
    exact he

theorem spinScaleLift_injective_scalar (S : TestAlgebra K) (t : (R(S) ⊗[F] B)ˣ) :
    Function.Injective fun s : Sˣ => spinScaleLift Q hd hscalar htrace hsplit S (t, s) := by
  intro r s h
  apply inv_injective
  exact scalarScale_injective (mul_right_cancel h)

theorem splitScalePoint_lift (S : TestAlgebra K) (x : spinScalePreimage P Q (R(S))) :
    ∃ s : Sˣ, quaternionNormAt b hB (R(S)) x.val.2 = s ^ 2 ∧
      restrictedSpinPoints P S x.val.1 = spinScaleLift Q hd hscalar htrace hsplit S (x.val.2, s) := by
  let z := restrictedSpinPoints P S x.val.1
  let t := quaternionMatrixUnit Q hd S x.val.2
  let L := liftedPlaneAction pₖ t
  have hL := liftedPlaneAction_properties pₖ t
  have hz : z ∈ spinUnits qₖ S := by
    rw [← restrictedSpinPoints_range P S]
    exact ⟨x.val.1, rfl⟩
  have hM := restrictedSpinPoints_action P S x.val.1
  have hx : spinVectorProjection P (R(S)) x.val.1 = quaternionScale Q (R(S)) x.val.2 := x.property
  rw [hx] at hM
  have h₁ := spinScaleLift_action P Q hd hscalar htrace hsplit S x.val.2 1
  have hL' : ScaleCliffordAction L (fullMatrixComparison P S (quaternionScale Q (R(S)) x.val.2).val) := by
    change ScaleCliffordAction (scalarScaleUnit (1 : Sˣ)⁻¹ * L)
      (fullMatrixComparison P S (quaternionScale Q (R(S)) x.val.2).val) at h₁
    simpa only [inv_one, map_one, one_mul] using h₁
  obtain ⟨r, hr, _⟩ := scaleCliffordAction_ratio hM hL' hz.1
    (even_inverse_of_unit_norm z hz.1 1 (by simpa only [Units.val_one, map_one] using hz.2.1))
    hL.1 (even_inverse_of_unit_norm L hL.1 (Matrix.GeneralLinearGroup.det t) hL.2.1)
  have hin : z = spinScaleLift Q hd hscalar htrace hsplit S (x.val.2, r⁻¹) := by
    change z = scalarScaleUnit (r⁻¹)⁻¹ * L
    rw [inv_inv]
    exact hr
  refine ⟨r⁻¹, (spinScaleLift_norm Q hd b hscalar htrace hsplit S x.val.2 r⁻¹).mp ?_, hin⟩
  rw [← hin]
  exact hz.2.1

theorem normPairLift_in_range (S : TestAlgebra K) (p : scalePairs (quaternionNormAt b hB (R(S)))) :
    spinScaleLift Q hd hscalar htrace hsplit S p.val ∈ Set.range (restrictedSpinPoints P S) := by
  rw [restrictedSpinPoints_range P S]
  exact cliffordScale_spin
    (M := Units.map (fullMatrixComparison P S).toMonoidHom (quaternionScale Q (R(S)) p.val.1))
    (spinScaleLift_action P Q hd hscalar htrace hsplit S p.val.1 p.val.2)
    (spinScaleLift_even Q hd hscalar htrace hsplit S p.val.1 p.val.2)
    ((spinScaleLift_norm Q hd b hscalar htrace hsplit S p.val.1 p.val.2).mpr p.property)

def normPairToSplitSpin (S : TestAlgebra K) (p : scalePairs (quaternionNormAt b hB (R(S)))) :
    spinScalePreimage P Q (R(S)) := by
  let hz := normPairLift_in_range P Q hd b hscalar htrace hsplit S p
  let g := hz.choose
  have hg := restrictedSpinPoints_action P S g
  rw [hz.choose_spec] at hg
  have hm := scaleCliffordAction_unique hg
    (spinScaleLift_action P Q hd hscalar htrace hsplit S p.val.1 p.val.2)
  exact ⟨(g, p.val.1), Units.ext ((fullMatrixComparison P S).injective hm)⟩

theorem normPairToSplitSpin_clifford (S : TestAlgebra K) (p : scalePairs (quaternionNormAt b hB (R(S)))) :
    restrictedSpinPoints P S (normPairToSplitSpin P Q hd b hscalar htrace hsplit S p).val.1 =
      spinScaleLift Q hd hscalar htrace hsplit S p.val := by
  exact (normPairLift_in_range P Q hd b hscalar htrace hsplit S p).choose_spec

def splitQuaternionScaleEquiv (S : TestAlgebra K) :
    spinScalePreimage P Q (R(S)) ≃* scalePairs (quaternionNormAt b hB (R(S))) := by
  let g := normPairToSplitSpin P Q hd b hscalar htrace hsplit S
  let h : scalePairs (quaternionNormAt b hB (R(S))) →* spinScalePreimage P Q (R(S)) :=
    MonoidHom.mk' g (by
      intro x y
      apply scalePreimageProjection_injective P Q (R(S))
      apply restrictedSpinPoints_injective P S
      change restrictedSpinPoints P S (g (x*y)).val.1 =
        restrictedSpinPoints P S ((g x).val.1 * (g y).val.1)
      rw [map_mul]
      dsimp only [g]
      rw [normPairToSplitSpin_clifford, normPairToSplitSpin_clifford, normPairToSplitSpin_clifford]
      exact map_mul (spinScaleLift Q hd hscalar htrace hsplit S) x.val y.val)
  apply (MulEquiv.ofBijective h ?_).symm
  constructor
  · intro x y hxy
    have h₁ := congrArg (fun z => z.val.2) hxy
    change x.val.1 = y.val.1 at h₁
    have h₂ := congrArg (fun z => restrictedSpinPoints P S z.val.1) hxy
    change restrictedSpinPoints P S (g x).val.1 = restrictedSpinPoints P S (g y).val.1 at h₂
    dsimp only [g] at h₂
    rw [normPairToSplitSpin_clifford, normPairToSplitSpin_clifford] at h₂
    change spinScaleLift Q hd hscalar htrace hsplit S (x.val.1, x.val.2) =
      spinScaleLift Q hd hscalar htrace hsplit S (y.val.1, y.val.2) at h₂
    rw [h₁] at h₂
    exact Subtype.ext (Prod.ext h₁ (spinScaleLift_injective_scalar Q hd hscalar htrace hsplit S y.val.1 h₂))
  · intro x
    obtain ⟨s, hN, hs⟩ := splitScalePoint_lift P Q hd b hscalar htrace hsplit S x
    let y : scalePairs (quaternionNormAt b hB (R(S))) := ⟨(x.val.2, s), hN⟩
    refine ⟨y, scalePreimageProjection_injective P Q (R(S)) ?_⟩
    apply restrictedSpinPoints_injective P S
    change restrictedSpinPoints P S (g y).val.1 = _
    dsimp only [g]
    rw [normPairToSplitSpin_clifford, hs]

theorem splitQuaternionScaleEquiv_clifford (S : TestAlgebra K) (x : spinScalePreimage P Q (R(S))) :
    restrictedSpinPoints P S x.val.1 =
      spinScaleLift Q hd hscalar htrace hsplit S (splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit S x).val := by
  let e := splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit S
  have h := e.symm_apply_apply x
  have h' := normPairToSplitSpin_clifford P Q hd b hscalar htrace hsplit S (e x)
  change restrictedSpinPoints P S (e.symm (e x)).val.1 = _ at h'
  rwa [h] at h'

theorem splitQuaternionScaleEquiv_scale (S : TestAlgebra K) (x : spinScalePreimage P Q (R(S))) :
    (splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit S x).val.1 = x.val.2 := by
  let e := splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit S
  exact congrArg (fun z => z.val.2) (e.symm_apply_apply x)

theorem splitQuaternionScaleEquiv_natural {S T : TestAlgebra K} (f : S ⟶ T) (x : spinScalePreimage P Q (R(S))) :
    splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit T
      (spinScalePointMap P Q ((restrictTestAlgebra F K).map f) x) =
    mapNormSquarePair hB b ((restrictTestAlgebra F K).map f)
      (splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit S x) := by
  let y := spinScalePointMap P Q ((restrictTestAlgebra F K).map f) x
  let z := splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit S x
  let w := splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit T y
  have hs : z.val.1 = x.val.2 := splitQuaternionScaleEquiv_scale P Q hd b hscalar htrace hsplit S x
  have ht : w.val.1 = y.val.2 := splitQuaternionScaleEquiv_scale P Q hd b hscalar htrace hsplit T y
  apply Subtype.ext
  apply Prod.ext
  · change w.val.1 = Units.map (tensorMap B ((restrictTestAlgebra F K).map f).hom).toMonoidHom z.val.1
    rw [ht, hs]
    rfl
  · change w.val.2 = Units.map f.hom.toMonoidHom z.val.2
    apply spinScaleLift_injective_scalar Q hd hscalar htrace hsplit T w.val.1
    have h := splitQuaternionScaleEquiv_clifford P Q hd b hscalar htrace hsplit T y
    have h' := splitQuaternionScaleEquiv_clifford P Q hd b hscalar htrace hsplit S x
    change restrictedSpinPoints P T (mapPoints ((restrictTestAlgebra F K).map f) x.val.1) = _ at h
    rw [restrictedSpinPoints_natural, h', ← spinScaleLift_natural Q hd hscalar htrace hsplit] at h
    let m := Units.map (tensorMap B ((restrictTestAlgebra F K).map f).hom).toMonoidHom
    let L := spinScaleLift Q hd hscalar htrace hsplit T
    change L (m z.val.1, Units.map f.hom.toMonoidHom z.val.2) =
      L (w.val.1, w.val.2) at h
    have hm : m z.val.1 = w.val.1 := (congrArg m hs).trans ht.symm
    change L (w.val.1, w.val.2) = L (w.val.1, Units.map f.hom.toMonoidHom z.val.2)
    rw [hm] at h
    exact h.symm

theorem splitQuaternionScaleEquiv_kernel (S : TestAlgebra K) (z : Points P.kernel.group.X (R(S))) :
    (splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit S (kernelScalePoint P Q (R(S)) z)).val =
      (1, (P.kernelPoints (R(S)) z).val) := by
  let x := kernelScalePoint P Q (R(S)) z
  let e := splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit S
  let s := (e x).val.2
  let u := (P.kernelPoints (R(S)) z).val
  have h₁ : (e x).val.1 = 1 := splitQuaternionScaleEquiv_scale P Q hd b hscalar htrace hsplit S x
  refine Prod.ext h₁ ?_
  have h := splitQuaternionScaleEquiv_clifford P Q hd b hscalar htrace hsplit S x
  change restrictedSpinPoints P S x.val.1 = spinScaleLift Q hd hscalar htrace hsplit S ((e x).val.1, s) at h
  rw [h₁] at h
  have hs : restrictedSpinPoints P S x.val.1 = scalarScaleUnit u := Units.ext (restrictedSpinPoints_scalar P S z)
  rw [hs] at h
  have hh : scalarScaleUnit (k := K) (I := I) u = scalarScaleUnit s⁻¹ := by
    change scalarScaleUnit u = scalarScaleUnit s⁻¹ *
      liftedPlaneAction pₖ (quaternionMatrixUnit Q hd S 1) at h
    simpa only [map_one, liftedPlaneAction_one, mul_one] using h
  have hu : u ^ 2 = 1 := (P.kernelPoints (R(S)) z).property
  have hv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hu)
  calc
    s = (s⁻¹)⁻¹ := (inv_inv s).symm
    _ = u⁻¹ := congrArg Inv.inv (scalarScale_injective hh).symm
    _ = u := hv

end SplitScaleEquivalence
end ScaleSplitProof

section ScaleGlueProof
open AlgebraicGeometry CategoryTheory Opposite Matrix
open scoped Matrix TensorProduct CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)
open LinearAlgebraicGroups.WeilRestriction (spectrumPoints spectrumPullbackIso)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (degree isCentralSimple)

section ScaleGlue

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F}
  {hB : isCentralSimple F B} {d : ℕ}
  {P : SpinModel G D} {Q : QuaternionHyperbolicPresentation D hB d}
  {J : Type u} [Fintype J] (b : Module.Basis J F B)

local notation "R(" S ")" => (restrictTestAlgebraObj F K S)

def testAlgebraTowerIso (R : TestAlgebra F) [Algebra K R] [IsScalarTower F K R] :
    R ≅ R(CommAlgCat.of K R) := by
  let T := R(CommAlgCat.of K R)
  let f : R ⟶ T := ConcreteCategory.ofHom (C := CommAlgCat F) (X := R) (Y := T)
    (@AlgHom.mk F R T _ _ _ R.algebra T.algebra (RingHom.id (R : Type u))
      (fun r => IsScalarTower.algebraMap_apply F K R r))
  let g : T ⟶ R := ConcreteCategory.ofHom (C := CommAlgCat F) (X := T) (Y := R)
    (@AlgHom.mk F T R _ _ _ T.algebra R.algebra (RingHom.id (R : Type u))
      (fun r => (IsScalarTower.algebraMap_apply F K R r).symm))
  refine ⟨f, g, ?_, ?_⟩
  · exact CommAlgCat.hom_ext (@AlgHom.ext F R R _ _ _ R.algebra R.algebra _ _ (fun _ => rfl))
  · exact CommAlgCat.hom_ext (@AlgHom.ext F T T _ _ _ T.algebra T.algebra _ _ (fun _ => rfl))

theorem testAlgebraTowerIso_self (S : TestAlgebra K) :
    let R := R(S)
    let _ : Algebra K R := S.algebra
    let _ : IsScalarTower F K R := IsScalarTower.of_algebraMap_eq' rfl
    testAlgebraTowerIso (K := K) R = Iso.refl R := by
  intro R _ _
  apply Iso.ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro r
  rfl

theorem testAlgebraTowerIso_natural {S T : Type u} [CommRing S] [CommRing T]
    [Algebra F S] [Algebra F T] [Algebra K S] [Algebra K T] [IsScalarTower F K S] [IsScalarTower F K T]
    (f : S →ₐ[K] T) :
    (testAlgebraTowerIso (K := K) (CommAlgCat.of F S)).hom ≫ (restrictTestAlgebra F K).map (CommAlgCat.ofHom f) =
      CommAlgCat.ofHom (f.restrictScalars F) ≫ (testAlgebraTowerIso (K := K) (CommAlgCat.of F T)).hom := by
  let a := CommAlgCat.of F S
  let b := R(CommAlgCat.of K T)
  exact CommAlgCat.hom_ext (@AlgHom.ext F a b _ _ _ a.algebra b.algebra _ _ (fun _ => rfl))

def representedScalePoints (H : AffineAlgebraicGroup F)
    (eH : (groupPointsFunctor F).obj H.val ≅ scalePreimageFunctor P Q)
    (A : TestAlgebra F) (i : (testSpec F).obj (op A) ≅ H.val.X) :
    coyoneda.obj (op A) ≅ scalePreimageFunctor P Q ⋙ forget GrpCat :=
  spectrumPoints A H.val.X i ≪≫ Functor.isoWhiskerRight eH (forget GrpCat)

variable (A : TestAlgebra F) (rep : coyoneda.obj (op A) ≅ scalePreimageFunctor P Q ⋙ forget GrpCat)
  (E : (K ⊗[F] B) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (hd : degree F B = 2)
variable (e : ∀ S : TestAlgebra K, spinScalePreimage P Q (restrictTestAlgebraObj F K S) ≃* scalePairs (quaternionNormAt b hB (restrictTestAlgebraObj F K S)))
variable (he : ∀ {S T : TestAlgebra K} (f : S ⟶ T) (x : spinScalePreimage P Q (restrictTestAlgebraObj F K S)),
    e T (spinScalePointMap P Q ((restrictTestAlgebra F K).map f) x) =
      mapNormSquarePair hB b ((restrictTestAlgebra F K).map f) (e S x))

def scalarExtendedAlgebraPoint (S : TestAlgebra K) :
    ((K ⊗[F] A) →ₐ[K] S) ≃ (A ⟶ R(S)) := by
  let R := R(S)
  letI : Algebra F S := R.algebra
  letI : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  let c : (A →ₐ[F] S) ≃ (A ⟶ R) :=
    ⟨fun f => ConcreteCategory.ofHom (C := CommAlgCat F) (X := A) (Y := R) f,
      fun f => f.hom, fun _ => rfl, fun _ => rfl⟩
  exact (AlgHom.liftEquiv F K A S).symm.trans c

theorem scalarExtendedAlgebraPoint_natural {S T : TestAlgebra K}
    (f : S ⟶ T) (x : (K ⊗[F] A) →ₐ[K] S) :
    scalarExtendedAlgebraPoint A T (f.hom.comp x) =
      scalarExtendedAlgebraPoint A S x ≫ (restrictTestAlgebra F K).map f := by
  let a := R(S)
  let b := R(T)
  exact CommAlgCat.hom_ext (@AlgHom.ext F A b _ _ _ A.algebra b.algebra _ _ (fun _ => rfl))

def splitScaleAlgebraPoints
    (coeffBasis : Module.Basis J F B) (C : TestAlgebra F)
    (rep₀ : coyoneda.obj (op C) ≅ scalePreimageFunctor P Q ⋙ forget GrpCat)
    (split : (K ⊗[F] B) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) (degreeTwo : degree F B = 2)
    (compare : ∀ S : TestAlgebra K, spinScalePreimage P Q (R(S)) ≃*
      scalePairs (quaternionNormAt coeffBasis hB (R(S))))
    (S : Type u) [CommRing S] [Algebra K S] :
    ((K ⊗[F] C) →ₐ[K] S) ≃ (SplitScaleCoordinateRing K →ₐ[K] S) := by
  let T := CommAlgCat.of K S
  let a : ((K ⊗[F] C) →ₐ[K] S) ≃ (C ⟶ R(T)) := scalarExtendedAlgebraPoint C T
  let x : (C ⟶ R(T)) ≃ spinScalePreimage P Q (R(T)) := (rep₀.app (R(T))).toEquiv
  let y := splitNormSquareParameters hB coeffBasis degreeTwo split T
  let z := (splitScaleCoordinateEquiv (F := K) (R := S)).symm
  exact a.trans (x.trans ((compare T).toEquiv.trans (y.trans z)))

include he in
set_option maxHeartbeats 1400000 in
theorem splitScaleAlgebraPoints_natural {S T : Type u} [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (f : S →ₐ[K] T) (x : (K ⊗[F] A) →ₐ[K] S) :
    splitScaleAlgebraPoints b A rep E hd e T (f.comp x) =
      f.comp ((splitScaleAlgebraPoints b A rep E hd e S) x) := by
  let S' := CommAlgCat.of K S
  let T' := CommAlgCat.of K T
  let f' : S' ⟶ T' := CommAlgCat.ofHom f
  let g := (restrictTestAlgebra F K).map f'
  let a := scalarExtendedAlgebraPoint A S' x
  let c := scalarExtendedAlgebraPoint A T' (f.comp x)
  have hc : c = a ≫ g := scalarExtendedAlgebraPoint_natural A f' x
  let y := e S' (rep.hom.app (R(S')) a)
  let p := splitNormSquareParameters hB b hd E S' y
  change splitScaleCoordinateEquiv.symm (splitNormSquareParameters hB b hd E T'
    (e T' (rep.hom.app (R(T')) c))) = f.comp (splitScaleCoordinateEquiv.symm p)
  have h : rep.hom.app (R(T')) (a ≫ g) = spinScalePointMap P Q g (rep.hom.app (R(S')) a) :=
    rep.hom.naturality_apply g a
  apply (splitScaleCoordinateEquiv (F := K) (R := T)).injective
  rw [Equiv.apply_symm_apply, hc, h]
  have hh := he f' ((rep.hom.app (R(S'))) a)
  rw [hh, splitNormSquareParameters_natural hB b hd E f',
    splitScaleCoordinateEquiv_natural f, Equiv.apply_symm_apply]
  rfl

include b rep E hd e he in
def splitScaleCoordinateComparison : (K ⊗[F] A) ≃ₐ[K] SplitScaleCoordinateRing K := by
  let χ (S : Type u) [CommRing S] [Algebra K S] := splitScaleAlgebraPoints b A rep E hd e S
  exact (algebraEquivOfPoints χ (splitScaleAlgebraPoints_natural b A rep E hd e he)).symm

theorem representedScale_geometry [FiniteDimensional F K] {X : SchemeOver F}
    (i : (testSpec F).obj (op A) ≅ X) (l : (K ⊗[F] A) ≃ₐ[K] SplitScaleCoordinateRing K) :
    Smooth X.hom ∧ GeometricallyConnected X.hom ∧ GeometricallyReduced X.hom := by
  have h := splitScaleGeometry l
  let Y := (testSpec F).obj (op A)
  have : IsIso i.inv.left := by
    change IsIso ((Over.forget _).map i.inv)
    infer_instance
  have sq : IsPullback i.inv.left X.hom Y.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id]
      exact Over.w i.inv⟩
  exact ⟨MorphismProperty.of_isPullback sq h.1, MorphismProperty.of_isPullback sq h.2.1,
    MorphismProperty.of_isPullback sq h.2.2⟩

end ScaleGlue
end ScaleGlueProof

section ScaleDescendProof
open AlgebraicGeometry CategoryTheory Opposite Matrix
open scoped Matrix TensorProduct CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (degree isCentralSimple)

section ScaleDescent

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F}
  {hB : isCentralSimple F B} {d : ℕ}
  {P : SpinModel G D} {Q : QuaternionHyperbolicPresentation D hB d}
  {J : Type u} [Fintype J] (b : Module.Basis J F B)
  (A : TestAlgebra F) (rep : coyoneda.obj (op A) ≅ scalePreimageFunctor P Q ⋙ forget GrpCat)

local notation "R(" S ")" => (restrictTestAlgebraObj F K S)

abbrev affineScalePoint {R : TestAlgebra F} (f : A ⟶ R) : spinScalePreimage P Q R := rep.hom.app R f

theorem affineScalePoint_natural {R T : TestAlgebra F} (f : A ⟶ R) (g : R ⟶ T) :
    affineScalePoint A rep (f ≫ g) = spinScalePointMap P Q g (affineScalePoint A rep f) :=
  rep.hom.naturality_apply g f

include b rep in
def scaleNormCoordinate : Aˣ :=
  quaternionNormAt b hB A (affineScalePoint A rep (𝟙 A)).val.2

theorem scaleNormCoordinate_eval {R : TestAlgebra F} (f : A ⟶ R) :
    Units.map f.hom.toMonoidHom (scaleNormCoordinate b A rep) =
      quaternionNormAt b hB R (affineScalePoint A rep f).val.2 := by
  have h := affineScalePoint_natural A rep (𝟙 A) f
  rw [Category.id_comp] at h
  rw [h, scaleNormCoordinate]
  exact (quaternionNormAt_natural b hB f _).symm

variable
  (e : ∀ S : TestAlgebra K, spinScalePreimage P Q (restrictTestAlgebraObj F K S) ≃* scalePairs (quaternionNormAt b hB (restrictTestAlgebraObj F K S)))
variable (he : ∀ {S T : TestAlgebra K} (f : S ⟶ T) (x : spinScalePreimage P Q (restrictTestAlgebraObj F K S)),
    e T (spinScalePointMap P Q ((restrictTestAlgebra F K).map f) x) =
      mapNormSquarePair hB b ((restrictTestAlgebra F K).map f) (e S x))
variable (he₁ : ∀ (S : TestAlgebra K) (x : spinScalePreimage P Q (restrictTestAlgebraObj F K S)), (e S x).val.1 = x.val.2)

def scaleUnitOnTower (S : Type u) [CommRing S] [Algebra F S] [Algebra K S] [IsScalarTower F K S]
    (f : A →ₐ[F] S) : Sˣ :=
  let T := CommAlgCat.of K S
  let j := (testAlgebraTowerIso (K := K) (CommAlgCat.of F S)).hom
  (e T (affineScalePoint A rep (CommAlgCat.ofHom f ≫ j))).val.2

include he₁ in
theorem scaleUnitOnTower_sq (S : Type u) [CommRing S] [Algebra F S] [Algebra K S] [IsScalarTower F K S]
    (f : A →ₐ[F] S) :
    scaleUnitOnTower b A rep e S f ^ 2 = Units.map f.toMonoidHom (scaleNormCoordinate b A rep) := by
  let j := (testAlgebraTowerIso (K := K) (CommAlgCat.of F S)).hom
  let T := CommAlgCat.of K S
  let x := affineScalePoint A rep (CommAlgCat.ofHom f ≫ j)
  have hx := (e T x).property
  change quaternionNormAt b hB (R(T)) (e T x).val.1 = (e T x).val.2 ^ 2 at hx
  rw [he₁] at hx
  rw [scaleUnitOnTower, ← hx, ← scaleNormCoordinate_eval]
  apply Units.ext
  rfl

include rep in
def scaleAugmentation : A →ₐ[F] F :=
  (rep.inv.app (CommAlgCat.of F F) (1 : spinScalePreimage P Q (CommAlgCat.of F F))).hom

theorem scaleUnitOnTower_one :
    scaleUnitOnTower b A rep e K ((Algebra.ofId F K).comp (scaleAugmentation A rep)) = 1 := by
  let f : A ⟶ CommAlgCat.of F F := rep.inv.app _ (1 : spinScalePreimage P Q _)
  let j := (testAlgebraTowerIso (K := K) (CommAlgCat.of F K)).hom
  let g : CommAlgCat.of F F ⟶ R(CommAlgCat.of K K) := CommAlgCat.ofHom (Algebra.ofId F K) ≫ j
  have hf : affineScalePoint A rep f = 1 := (rep.app _).toEquiv.apply_symm_apply _
  change (e (CommAlgCat.of K K) (affineScalePoint A rep (f ≫ g))).val.2 = 1
  rw [affineScalePoint_natural, hf, map_one, map_one]
  rfl

include he in
theorem scaleUnitOnTower_natural (S T : Type u) [CommRing S] [CommRing T] [Algebra F S] [Algebra F T]
    [Algebra K S] [Algebra K T] [IsScalarTower F K S] [IsScalarTower F K T]
    (f : A →ₐ[F] S) (g : S →ₐ[K] T) :
    scaleUnitOnTower b A rep e T ((g.restrictScalars F).comp f) =
      Units.map g.toMonoidHom (scaleUnitOnTower b A rep e S f) := by
  let S' := CommAlgCat.of K S
  let T' := CommAlgCat.of K T
  let jS := (testAlgebraTowerIso (K := K) (CommAlgCat.of F S)).hom
  let jT := (testAlgebraTowerIso (K := K) (CommAlgCat.of F T)).hom
  let g' : S' ⟶ T' := CommAlgCat.ofHom g
  let m := (restrictTestAlgebra F K).map g'
  let f' := CommAlgCat.ofHom f
  have h : CommAlgCat.ofHom ((g.restrictScalars F).comp f) ≫ jT = (f' ≫ jS) ≫ m := by
    change (f' ≫ CommAlgCat.ofHom (g.restrictScalars F)) ≫ jT = (f' ≫ jS) ≫ m
    rw [Category.assoc, Category.assoc, testAlgebraTowerIso_natural g]
  change (e T' (affineScalePoint A rep _)).val.2 = _
  rw [h, affineScalePoint_natural, he]
  rfl

variable [FiniteDimensional F K] [IsGalois F K]

include rep he he₁ in
/-- The normalized character over the splitting field gives a natural group
comparison over the ground field. -/
theorem descendScaleComparison [IsDomain (K ⊗[F] A)] :
    ∃ e₀ : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (quaternionNormAt b hB R),
      (∀ R x, (e₀ R x).val.1 = x.val.2) ∧
      (∀ {R T : TestAlgebra F} (f : R ⟶ T) (x : spinScalePreimage P Q R),
        e₀ T (spinScalePointMap P Q f x) = mapNormSquarePair hB b f (e₀ R x)) ∧
      (∀ S : TestAlgebra K, e₀ (R(S)) = e S) := by
  obtain ⟨r, hr, _, hsplit⟩ := descendNormalizedUnitCoordinate
    (scaleAugmentation A rep) (scaleNormCoordinate b A rep) (scaleUnitOnTower b A rep e)
    (scaleUnitOnTower_sq b A rep e he₁) (scaleUnitOnTower_one b A rep e)
    (scaleUnitOnTower_natural b A rep e he)
  let pair (R : TestAlgebra F) (x : spinScalePreimage P Q R) : scalePairs (quaternionNormAt b hB R) := by
    let f := rep.inv.app R x
    let s := Units.map f.hom.toMonoidHom r
    refine ⟨(x.val.2, s), ?_⟩
    change quaternionNormAt b hB R x.val.2 = s ^ 2
    have hf : affineScalePoint A rep f = x := (rep.app R).toEquiv.apply_symm_apply x
    rw [← hf, ← scaleNormCoordinate_eval, ← hr]
    exact map_pow _ _ _
  have hn {R T : TestAlgebra F} (f : R ⟶ T) (x : spinScalePreimage P Q R) :
      pair T (spinScalePointMap P Q f x) = mapNormSquarePair hB b f (pair R x) := by
    have h : rep.inv.app T (spinScalePointMap P Q f x) = rep.inv.app R x ≫ f := rep.inv.naturality_apply f x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Units.map (rep.inv.app T (spinScalePointMap P Q f x)).hom.toMonoidHom r =
        Units.map f.hom.toMonoidHom (Units.map (rep.inv.app R x).hom.toMonoidHom r)
      rw [h]
      rfl
  have hcomparison (R : TestAlgebra F) [Algebra K R] [IsScalarTower F K R] (x : spinScalePreimage P Q R) :
      e (CommAlgCat.of K R) (spinScalePointMap P Q (testAlgebraTowerIso (K := K) R).hom x) =
        mapNormSquarePair hB b (testAlgebraTowerIso (K := K) R).hom (pair R x) := by
    let j := (testAlgebraTowerIso (K := K) R).hom
    let S := CommAlgCat.of K R
    let f := rep.inv.app R x
    have h := hsplit R f.hom
    have hf : affineScalePoint A rep f = x := (rep.app R).toEquiv.apply_symm_apply x
    apply Subtype.ext
    apply Prod.ext
    · rw [he₁]
      rfl
    · change (e S (spinScalePointMap P Q j x)).val.2 =
        Units.map j.hom.toMonoidHom (Units.map f.hom.toMonoidHom r)
      change (e S (affineScalePoint A rep (f ≫ j))).val.2 = _ at h
      rw [affineScalePoint_natural, hf] at h
      exact h
  have hmul_on_tower (R : TestAlgebra F) [Algebra K R] [IsScalarTower F K R]
      (x y : spinScalePreimage P Q R) : pair R (x * y) = pair R x * pair R y := by
    let j := testAlgebraTowerIso (K := K) R
    let n := ((normSquarePairFunctor hB b).mapIso j).groupIsoToMulEquiv
    apply n.injective
    change mapNormSquarePair hB b j.hom (pair R (x*y)) =
      mapNormSquarePair hB b j.hom (pair R x * pair R y)
    rw [map_mul, ← hcomparison R, ← hcomparison R, ← hcomparison R, map_mul, map_mul]
  have hmul (R : TestAlgebra F) (x y : spinScalePreimage P Q R) : pair R (x * y) = pair R x * pair R y := by
    let T := CommAlgCat.of F (K ⊗[F] R)
    let f : R ⟶ T := CommAlgCat.ofHom (scalarExtension (K := K))
    apply normSquarePairMap_injective hB b f
      (Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective)
    rw [map_mul, ← hn f, ← hn f, ← hn f, map_mul]
    exact hmul_on_tower T _ _
  let τ : coyoneda.obj (op A) ⟶ normSquarePairFunctor hB b ⋙ forget GrpCat :=
    { app := fun R => ↾(fun f => pair R (affineScalePoint A rep f))
      naturality := by
        intro R T f
        apply ConcreteCategory.hom_ext
        intro x
        exact (congrArg (pair T) (affineScalePoint_natural A rep x f)).trans (hn f _) }
  have hτ (R : TestAlgebra F) [Algebra K R] [IsScalarTower F K R] : Function.Bijective (τ.app R) := by
    let j := testAlgebraTowerIso (K := K) R
    let n := ((normSquarePairFunctor hB b).mapIso j).groupIsoToMulEquiv
    let p := ((scalePreimageFunctor P Q).mapIso j).groupIsoToMulEquiv
    have h : n ∘ τ.app R = (e (CommAlgCat.of K R)).toEquiv ∘ p.toEquiv ∘ (rep.app R).toEquiv := by
      funext x
      exact (hcomparison R (affineScalePoint A rep x)).symm
    have hB := (e (CommAlgCat.of K R)).bijective.comp (p.bijective.comp (rep.app R).toEquiv.bijective)
    change Function.Bijective ((e (CommAlgCat.of K R)).toEquiv ∘ p.toEquiv ∘ (rep.app R).toEquiv) at hB
    rw [← h] at hB
    exact ⟨hB.injective.of_comp, hB.surjective.of_comp_left n.injective⟩
  have hb (R : TestAlgebra F) : Function.Bijective (pair R) := by
    have h := affinePoints_bijective_of_galois (K := K) τ hτ
      (fun f hf => normSquarePairMap_injective hB b f hf) R
    have h' : (τ.app R : (A ⟶ R) → _) ∘ (rep.app R).toEquiv.symm = pair R := by
      funext x
      change pair R ((rep.app R).toEquiv ((rep.app R).toEquiv.symm x)) = pair R x
      rw [Equiv.apply_symm_apply]
    rw [← h']
    exact h.comp (rep.app R).toEquiv.symm.bijective
  let e₀ (R : TestAlgebra F) := MulEquiv.ofBijective (MonoidHom.mk' (pair R) (hmul R)) (hb R)
  refine ⟨e₀, fun _ _ => rfl, fun {R T} f x => hn f x, fun S => ?_⟩
  let R := R(S)
  let : Algebra K R := S.algebra
  let : IsScalarTower F K R := IsScalarTower.of_algebraMap_eq' rfl
  apply MulEquiv.ext
  intro x
  have h := hcomparison R x
  rw [testAlgebraTowerIso_self S] at h
  let U := scalePreimageFunctor P Q
  let V := normSquarePairFunctor hB b
  have hu : spinScalePointMap P Q (𝟙 R) x = x :=
    congrArg (fun f : U.obj R ⟶ U.obj R => f x) (U.map_id R)
  have hv : mapNormSquarePair hB b (𝟙 R) (pair R x) = pair R x :=
    congrArg (fun f : V.obj R ⟶ V.obj R => f (pair R x)) (V.map_id R)
  change e S (spinScalePointMap P Q (𝟙 R) x) =
    mapNormSquarePair hB b (𝟙 R) (pair R x) at h
  rw [hu, hv] at h
  exact h.symm

end ScaleDescent
end ScaleDescendProof

section ScaleNeutralProof
open AlgebraicGeometry CategoryTheory Opposite Matrix
open scoped Matrix TensorProduct CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)
open LinearAlgebraicGroups.WeilRestriction (spectrumPoints)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (degree isCentralSimple)
open private affineCoordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction

section NeutralScale

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [Nonempty I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F}
  {hB : isCentralSimple F B} {d : ℕ}
  (P : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
  (hd : degree F B = 2) {J : Type u} [Fintype J] (b : Module.Basis J F B)
  (hscalar : QuadraticPairScalarExtension.{u}) (htrace : TraceOrthogonality.{u})
  (hsplit : SplitSemitrace.{u}) (hpair : PairIsometryScalarExtension.{u})

local notation "R(" S ")" => (restrictTestAlgebraObj F K S)

def neutralVectorPoint (R : TestAlgebra F) (x : Points P.neutral.val.X R) :
    (R ⊗[F] ρ.fixedSubalgebra)ˣ :=
  P.fullPoints R (x ≫ P.inclusion.hom.hom)

omit [Nonempty I] in
theorem neutralVectorPoint_natural {R T : TestAlgebra F} (f : R ⟶ T) (x : Points P.neutral.val.X R) :
    neutralVectorPoint P T (mapPoints f x) =
      Units.map (tensorMap _ f.hom).toMonoidHom (neutralVectorPoint P R x) := by
  change P.fullPoints T ((mapPoints f x) ≫ P.inclusion.hom.hom) = _
  rw [show (mapPoints f x) ≫ P.inclusion.hom.hom = mapPoints f (x ≫ P.inclusion.hom.hom)
    from Category.assoc _ _ _]
  exact P.fullNatural R T f _

omit [Nonempty I] in
theorem neutralVectorPoint_injective (R : TestAlgebra F) :
    Function.Injective (neutralVectorPoint P R) := by
  intro x y h
  have hh := P.fullFaithful R h
  have : IsClosedImmersion P.inclusion.hom.hom.left := P.closedImmersion
  apply Over.OverMorphism.ext
  apply (cancel_mono P.inclusion.hom.hom.left).mp
  exact congrArg Over.Hom.left hh

theorem tensorUnits_comp {R S T : TestAlgebra F} (f : R ⟶ S) (g : S ⟶ T) (t : (R ⊗[F] B)ˣ) :
    Units.map (tensorMap B g.hom).toMonoidHom (Units.map (tensorMap B f.hom).toMonoidHom t) =
      Units.map (tensorMap B (f ≫ g).hom).toMonoidHom t := by
  apply Units.ext
  exact (DFunLike.congr_fun (scaleTensor_comp (B := B) f g) t.val).symm

include hpair hscalar htrace hsplit hd in
theorem splitQuaternionScale_full (S : TestAlgebra K) (t : (R(S) ⊗[F] B)ˣ) :
    ∃ g : Points P.full.val.X (R(S)), P.fullPoints (R(S)) g = quaternionScale Q (R(S)) t := by
  let R := R(S)
  let : Algebra K R := S.algebra
  let : IsScalarTower F K R := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨e, he, hP⟩ := hpair D R
  apply (P.fullRange R (quaternionScale Q R t)).mpr
  apply (hP (quaternionScale Q R t)).mpr
  intro v
  change hyperbolicForm I R (e (quaternionScale Q R t).val *ᵥ v) = hyperbolicForm I R v
  rw [quaternionScale_matrix Q hd R e he hscalar htrace hsplit]
  exact ScalePlane.action_preserves _ _ v

include hpair hscalar htrace hsplit hd b in
theorem splitQuaternionScale_neutral (S : TestAlgebra K) (t : (R(S) ⊗[F] B)ˣ) :
    ∃ g : Points P.neutral.val.X (R(S)), neutralVectorPoint P (R(S)) g = quaternionScale Q (R(S)) t := by
  let R := R(S)
  obtain ⟨g, hg⟩ := splitQuaternionScale_full P Q hd hscalar htrace hsplit hpair S t
  obtain ⟨T, f, hf, s, hs⟩ := adjoinScaleSquareRoot S (quaternionNormAt b hB R t)
  let R' := R(T)
  let f' := (restrictTestAlgebra F K).map f
  let t' := Units.map (tensorMap B f'.hom).toMonoidHom t
  have hn : quaternionNormAt b hB R' t' = s ^ 2 := (quaternionNormAt_natural b hB f' t).trans hs.symm
  let x := normPairToSplitSpin P Q hd b hscalar htrace hsplit T ⟨(t', s), hn⟩
  let y := x.val.1 ≫ P.projection.hom.hom
  have hy : neutralVectorPoint P R' y = quaternionScale Q R' t' := by
    change P.fullPoints R' ((x.val.1 ≫ P.projection.hom.hom) ≫ P.inclusion.hom.hom) = _
    rw [Category.assoc]
    exact x.property
  have hgy : mapPoints f' g = y ≫ P.inclusion.hom.hom := by
    apply P.fullFaithful R'
    change _ = neutralVectorPoint P R' y
    rw [P.fullNatural R R' f', hg, hy, quaternionScale_natural]
    rfl
  obtain ⟨z, hz⟩ := factorPointThroughClosed P.full.property.1 P.inclusion.hom.hom
    P.closedImmersion f' hf g y hgy
  exact ⟨z, (congrArg (P.fullPoints R) hz).trans hg⟩

include hpair hscalar htrace hsplit hd b in
theorem quaternionScale_neutral_on_tower (R : TestAlgebra F) [Algebra K R] [IsScalarTower F K R]
    (t : (R ⊗[F] B)ˣ) :
    ∃ g : Points P.neutral.val.X R, neutralVectorPoint P R g = quaternionScale Q R t := by
  let S := CommAlgCat.of K R
  let T := R(S)
  have ha : T.algebra = R.algebra := by
    apply Algebra.algebra_ext
    intro a
    exact (IsScalarTower.algebraMap_apply F K R a).symm
  have hT : T = R :=
    (congrArg (fun a => @CommAlgCat.of F _ (R : Type u) R.commRing a) ha).trans (by cases R; rfl)
  let HasPoint (A : TestAlgebra F) : Prop := ∀ t : (A ⊗[F] B)ˣ,
    ∃ g : Points P.neutral.val.X A, neutralVectorPoint P A g = quaternionScale Q A t
  have hh : HasPoint T := splitQuaternionScale_neutral P Q hd b hscalar htrace hsplit hpair S
  have hR : HasPoint R := hT ▸ hh
  exact hR t

include hpair hscalar htrace hsplit hd b in
theorem quaternionScale_neutral [FiniteDimensional F K] [IsGalois F K]
    (R : TestAlgebra F) (t : (R ⊗[F] B)ˣ) :
    ∃ g : Points P.neutral.val.X R, neutralVectorPoint P R g = quaternionScale Q R t := by
  let T := CommAlgCat.of F (K ⊗[F] R)
  let j : R ⟶ T := CommAlgCat.ofHom (scalarExtension (K := K))
  let t' := Units.map (tensorMap B j.hom).toMonoidHom t
  obtain ⟨a, ha⟩ := quaternionScale_neutral_on_tower P Q hd b hscalar htrace hsplit hpair T t'
  let A := affineCoordinates ⟨P.neutral.val.X, P.neutral.property⟩
  let e := spectrumPoints A.val P.neutral.val.X A.property.2.some
  let f := e.inv.app T a
  have hf : e.hom.app T f = a := (e.app T).toEquiv.apply_symm_apply a
  have hσ (σ : K ≃ₐ[F] K) : (tensorAut σ).comp f.hom = f.hom := by
    let m : T ⟶ T := CommAlgCat.ofHom (tensorAut σ)
    have hm : j ≫ m = j := CommAlgCat.hom_ext (AlgHom.ext (tensorAut_scalarExtension σ))
    have hfix : mapPoints m a = a := by
      apply neutralVectorPoint_injective P T
      rw [neutralVectorPoint_natural, ha, ← quaternionScale_natural, tensorUnits_comp j m, hm]
    have h := e.hom.naturality_apply m f
    change e.hom.app T (f ≫ m) = mapPoints m (e.hom.app T f) at h
    rw [hf, hfix, ← hf] at h
    exact congrArg CommAlgCat.Hom.hom ((e.app T).toEquiv.injective h)
  obtain ⟨g, hg⟩ := algebraPoint_descends f.hom hσ
  let q := CommAlgCat.ofHom g
  have hq : q ≫ j = f := CommAlgCat.hom_ext (AlgHom.ext (DFunLike.congr_fun hg))
  let z := e.hom.app R q
  have hz : mapPoints j z = a := by
    have h := e.hom.naturality_apply j q
    change e.hom.app T (q ≫ j) = mapPoints j z at h
    rw [hq, hf] at h
    exact h.symm
  refine ⟨z, ?_⟩
  apply Units.ext
  apply TensorProduct.map_injective_of_flat_flat j.hom.toLinearMap
    (LinearMap.id : ρ.fixedSubalgebra →ₗ[F] ρ.fixedSubalgebra) (Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective)
    Function.injective_id
  have h := neutralVectorPoint_natural P j z
  rw [hz, ha, quaternionScale_natural] at h
  exact (congrArg Units.val h).symm

end NeutralScale
end ScaleNeutralProof

section ScaleVarietyProof
open AlgebraicGeometry CategoryTheory Matrix
open scoped Matrix TensorProduct CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (degree isCentralSimple)

section SplitVarietyCoordinates

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F}
  {hB : isCentralSimple F B} {d : ℕ}
  {P : SpinModel G D} {Q : QuaternionHyperbolicPresentation D hB d}
  {J : Type u} [Fintype J]
  (H : AffineAlgebraicGroup F) (pointIso : (groupPointsFunctor F).obj H.val ≅ scalePreimageFunctor P Q)

def scalePointsEquiv (R : TestAlgebra F) : Points H.val.X R ≃* spinScalePreimage P Q R :=
  (pointIso.app R).groupIsoToMulEquiv

theorem scalePointsEquiv_natural {R T : TestAlgebra F} (f : R ⟶ T) (x : Points H.val.X R) :
    scalePointsEquiv H pointIso T (mapPoints f x) =
      spinScalePointMap P Q f (scalePointsEquiv H pointIso R x) :=
  pointIso.hom.naturality_apply f x

theorem scalePointsEquiv_scale_natural {R T : TestAlgebra F} (f : R ⟶ T) (x : Points H.val.X R) :
    (scalePointsEquiv H pointIso T (mapPoints f x)).val.2 =
      Units.map (tensorMap B f.hom).toMonoidHom (scalePointsEquiv H pointIso R x).val.2 :=
  congrArg (fun y : spinScalePreimage P Q T => y.val.2) (scalePointsEquiv_natural H pointIso f x)

variable (b : Module.Basis J F B) (hd : degree F B = 2)
  (E : (K ⊗[F] B) ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)
  (e : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (quaternionNormAt b hB R))
variable (hn : ∀ {R T : TestAlgebra F} (f : R ⟶ T) (x : spinScalePreimage P Q R),
    e T (spinScalePointMap P Q f x) = mapNormSquarePair hB b f (e R x))

def scaleSplitCoordinates (S : TestAlgebra K) :
    Points ((groupBaseChange F K).obj H.val).X S ≃ (Matrix.SpecialLinearGroup (Fin 2) S × Sˣ) :=
  let R := (restrictTestAlgebra F K).obj S
  (baseChangePointGroupEquiv K H.val S).toEquiv.trans ((scalePointsEquiv H pointIso R).toEquiv.trans
    ((e R).toEquiv.trans (splitNormSquareParameters hB b hd E S)))

open LinearAlgebraicGroups.Albert.SplitSpinSpecification (scaleRow)

theorem scaleSplitCoordinates_formula (S : TestAlgebra K) (x : Points ((groupBaseChange F K).obj H.val).X S) :
    let R := (restrictTestAlgebra F K).obj S
    let z := (e R (scalePointsEquiv H pointIso R (baseChangePoint F K H.val.X S x))).val
    (scaleSplitCoordinates H pointIso b hd E e S x).1.val =
      scaleRow 0 ((↑z.2⁻¹ : S)^2) (splitQuaternionAt E S z.1.val) ∧
    (scaleSplitCoordinates H pointIso b hd E e S x).2 = z.2 :=
  splitNormSquareParameters_coordinates hB b hd E S _

include hn in
theorem scaleSplitCoordinates_natural {S T : TestAlgebra K} (f : S ⟶ T)
    (x : Points ((groupBaseChange F K).obj H.val).X S) :
    scaleSplitCoordinates H pointIso b hd E e T (mapPoints f x) =
      (Matrix.SpecialLinearGroup.map f.hom.toRingHom (scaleSplitCoordinates H pointIso b hd E e S x).1,
        Units.map f.hom.toMonoidHom (scaleSplitCoordinates H pointIso b hd E e S x).2) := by
  let S₀ := (restrictTestAlgebra F K).obj S
  let T₀ := (restrictTestAlgebra F K).obj T
  let f₀ := (restrictTestAlgebra F K).map f
  let a := baseChangePoint F K H.val.X S x
  have ha : baseChangePoint F K H.val.X T (mapPoints f x) = mapPoints f₀ a :=
    baseChangePointsNaturality F K H.val.X f x
  change splitNormSquareParameters hB b hd E T
    (e T₀ (scalePointsEquiv H pointIso T₀ (baseChangePoint F K H.val.X T (mapPoints f x)))) = _
  rw [ha, scalePointsEquiv_natural H pointIso f₀ a, hn f₀]
  exact splitNormSquareParameters_natural hB b hd E f _

end SplitVarietyCoordinates
end ScaleVarietyProof

section ScaleMainProof
open AlgebraicGeometry CategoryTheory Opposite Matrix
open scoped Matrix TensorProduct CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (degree isCentralSimple)
open private affineCoordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction

section FinalScaleCover

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F}
  {hB : isCentralSimple F B} {d : ℕ}
  (P : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
  (hd : degree F B = 2) {J : Type u} [Fintype J] (b : Module.Basis J F B)
  (hscalar : QuadraticPairScalarExtension.{u}) (htrace : TraceOrthogonality.{u})
  (hsplit : SplitSemitrace.{u})

local notation "R(" S ")" => (restrictTestAlgebraObj F K S)

theorem kernelScalePoint_natural {R T : TestAlgebra F} (f : R ⟶ T) (z : Points P.kernel.group.X R) :
    spinScalePointMap P Q f (kernelScalePoint P Q R z) =
      kernelScalePoint P Q T (mapPoints f z) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (Category.assoc _ _ _).symm
  · exact map_one _

theorem descendedScaleComparison_kernel
    (e₀ : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (quaternionNormAt b hB R))
    (hproj : ∀ R x, (e₀ R x).val.1 = x.val.2)
    (hn : ∀ {R T : TestAlgebra F} (f : R ⟶ T) (x : spinScalePreimage P Q R),
      e₀ T (spinScalePointMap P Q f x) = mapNormSquarePair hB b f (e₀ R x))
    (he : ∀ S : TestAlgebra K, e₀ (R(S)) = splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit S)
    (R : TestAlgebra F) (z : Points P.kernel.group.X R) :
    (e₀ R (kernelScalePoint P Q R z)).val = (1, (P.kernelPoints R z).val) := by
  let T := CommAlgCat.of F (K ⊗[F] R)
  let S := CommAlgCat.of K T
  let j := testAlgebraTowerIso (K := K) T
  let i : R ⟶ T := CommAlgCat.ofHom (scalarExtension (K := K))
  let f : R ⟶ R(S) := i ≫ j.hom
  have hi : Function.Injective i.hom :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hf : Function.Injective f.hom := by
    intro x y h
    apply hi
    exact h
  apply Prod.ext
  · exact hproj R (kernelScalePoint P Q R z)
  · apply Units.ext
    apply hf
    have h := hn f (kernelScalePoint P Q R z)
    rw [kernelScalePoint_natural, he S] at h
    have h' := congrArg (fun a => a.val.2.val) h
    rw [splitQuaternionScaleEquiv_kernel, P.kernelNatural] at h'
    exact h'.symm

end FinalScaleCover

set_option maxHeartbeats 1800000 in
private theorem spinScaleCover_proof (hpair : PairIsometryScalarExtension.{u})
    (hscalar : QuadraticPairScalarExtension.{u}) (htrace : TraceOrthogonality.{u})
    (hsplit : SplitSemitrace.{u}) : SpinScaleCover.{u} := by
  intro F K I B _ _ _ _ _ _ _ _ _ ρ G D P hI hB hd d Q J _ b
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  refine ⟨quaternionScale_neutral P Q hd b hscalar htrace hsplit hpair, ?_⟩
  let H := representScalePreimage P Q b
  let A := affineCoordinates ⟨H.group.val.X, H.group.property⟩
  let iA := A.property.2.some
  let E := quaternionMatrixEquiv Q hd
  let e := splitQuaternionScaleEquiv P Q hd b hscalar htrace hsplit
  let he {S T : TestAlgebra K} (f : S ⟶ T)
      (x : spinScalePreimage P Q (restrictTestAlgebraObj F K S)) :=
    splitQuaternionScaleEquiv_natural P Q hd b hscalar htrace hsplit f x
  let hproj := splitQuaternionScaleEquiv_scale P Q hd b hscalar htrace hsplit
  let rep := representedScalePoints H.group H.points A.val iA
  let L := splitScaleCoordinateComparison b A.val rep E hd e he
  have : IsDomain (SplitScaleCoordinateRing K) := splitScaleCoordinateDomain K
  have : IsDomain (K ⊗[F] A.val) := L.injective.isDomain L
  obtain ⟨e₀, h₁, hn, he₀⟩ := descendScaleComparison b A.val rep e he hproj
  refine ⟨quaternionNormAt b hB, e₀, fun _ _ => rfl, h₁, ?_, ?_, ?_⟩
  · intro R T f x y hy hz
    have h : y = spinScalePointMap P Q f x := Subtype.ext (Prod.ext hy hz)
    rw [h, hn]
    rfl
  · intro R z
    exact ⟨kernelScalePoint P Q R z, rfl,
      descendedScaleComparison_kernel P Q hd b hscalar htrace hsplit e₀ h₁ hn he₀ R z⟩
  · have hgeo := representedScale_geometry A.val iA L
    let φ := scalePointsEquiv H.group H.points
    let ξ := scaleSplitCoordinates H.group H.points b hd E e₀
    refine ⟨H.group, H.inclusion, φ, H.closed, hgeo.1, hgeo.2.1, hgeo.2.2, ?_, ?_, ?_⟩
    · intro R x
      exact congrArg (fun f => f.app R x) H.comparison
    · intro R T f x
      exact scalePointsEquiv_scale_natural H.group H.points f x
    · exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, splitQuaternionAt E, ξ,
        splitQuaternionAt_norm b 2 hd E,
        scaleSplitCoordinates_formula H.group H.points b hd E e₀,
        fun S T f x => scaleSplitCoordinates_natural H.group H.points b hd E e₀ hn f x⟩

end ScaleMainProof

open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels

section Conditional

-- The conditional protocol requires every premise in the supplied order.
set_option linter.unusedSectionVars false

universe w

variable
    (_hArchimedeanDivision : ArchimedeanDivision.{w})
    (_hCliffordSimilitudeAction : CliffordSimilitudeAction.{w})
    (_hCliffordSimilitudeBaseChange : CliffordSimilitudeBaseChange.{w})
    (_hCorootLattice : CorootLattice.{w})
    (_hDescendedVectorImage : DescendedVectorImage.{w})
    (_hEvenCliffordSimilitude : EvenCliffordSimilitude.{w})
    (_hEvenCliffordVectorAction : EvenCliffordVectorAction.{w})
    (_hFieldOrthogonalModel : FieldOrthogonalModel.{w})
    (_hFiniteEquivariantSpinReference : FiniteEquivariantSpinReference.{w})
    (_hFiniteSpinReference : FiniteSpinReference.{w})
    (_hFixedVertexFiniteLevel : FixedVertexFiniteLevel.{w})
    (_hFixedVertexOuterFactorization : FixedVertexOuterFactorization.{w})
    (_hHyperbolicPartner : HyperbolicPartner.{w,w})
    (_hNeutralPointsReducedNorm : NeutralPointsReducedNorm.{w})
    (_hNonarchimedeanDivision : NonarchimedeanDivision.{w,w})
    (_hNontrialitarianSpinModel : NontrialitarianSpinModel.{w})
    (_hOrthogonalInvolutionDescent : OrthogonalInvolutionDescent.{w})
    (_hPairIsometryModel : PairIsometryModel.{w})
    (_hPairIsometryScalarExtension : PairIsometryScalarExtension.{w})
    (_hPairReducedNormScalarExtension : PairReducedNormScalarExtension.{w})
    (_hProjectiveCliffordAction : ProjectiveCliffordAction.{w})
    (_hProjectiveSimilitudes : ProjectiveSimilitudes.{w})
    (_hQuadraticPairDescent : QuadraticPairDescent.{w})
    (_hQuadraticPairScalarExtension : QuadraticPairScalarExtension.{w})
    (_hQuaternionSkewModel : QuaternionSkewModel.{w})
    (_hQuaternionSpinIsotropy : QuaternionSpinIsotropy.{w})
    (_hSimpleDCoordinates : SimpleDCoordinates.{w})
    (_hSpinChartFibers : SpinChartFibers.{w})
    (_hSpinSimilitudeScalarExtension : SpinSimilitudeScalarExtension.{w})
    (_hSplitOrthogonalModel : SplitOrthogonalModel.{w})
    (_hSplitOrthogonalTangent : SplitOrthogonalTangent.{w})
    (_hSplitOrthogonalTangentBlocks : SplitOrthogonalTangentBlocks.{w})
    (_hSplitPairIsometries : SplitPairIsometries.{w})
    (_hSplitProjectiveSpinAction : SplitProjectiveSpinAction.{w})
    (_hSplitSemitrace : SplitSemitrace.{w})
    (_hSplitSpinBorel : SplitSpinBorel.{w})
    (_hSplitSpinCentralIsogeny : SplitSpinCentralIsogeny.{w})
    (_hSplitSpinChartInImage : SplitSpinChartInImage.{w})
    (_hSplitSpinDeterminant : SplitSpinDeterminant.{w})
    (_hSplitSpinDiagonalTorus : SplitSpinDiagonalTorus.{w})
    (_hSplitSpinDiagramAction : SplitSpinDiagramAction.{w})
    (_hSplitSpinGeometry : SplitSpinGeometry.{w})
    (_hSplitSpinIdentityComponent : SplitSpinIdentityComponent.{w})
    (_hSplitSpinImage : SplitSpinImage.{w})
    (_hSplitSpinIntegralComparison : SplitSpinIntegralComparison.{w})
    (_hSplitSpinOpenImage : SplitSpinOpenImage.{w})
    (_hSplitSpinTorusRestriction : SplitSpinTorusRestriction.{w})
    (_hSplitSpinTypeD : SplitSpinTypeD.{w})
    (_hSplitVectorCentralizer : SplitVectorCentralizer.{w})
    (_hSplitVectorTangent : SplitVectorTangent.{w})
    (_hTraceOrthogonality : TraceOrthogonality.{w})
    (_hTypeDPositiveRoots : TypeDPositiveRoots.{w})
    (_hVectorDiagramSwitch : VectorDiagramSwitch.{w})
    (_hVectorMorphismDescent : VectorMorphismDescent.{w})
    (_hVectorVertexStabilizer : VectorVertexStabilizer)

include
  _hArchimedeanDivision
  _hCliffordSimilitudeAction
  _hCliffordSimilitudeBaseChange
  _hCorootLattice
  _hDescendedVectorImage
  _hEvenCliffordSimilitude
  _hEvenCliffordVectorAction
  _hFieldOrthogonalModel
  _hFiniteEquivariantSpinReference
  _hFiniteSpinReference
  _hFixedVertexFiniteLevel
  _hFixedVertexOuterFactorization
  _hHyperbolicPartner
  _hNeutralPointsReducedNorm
  _hNonarchimedeanDivision
  _hNontrialitarianSpinModel
  _hOrthogonalInvolutionDescent
  _hPairIsometryModel
  _hPairIsometryScalarExtension
  _hPairReducedNormScalarExtension
  _hProjectiveCliffordAction
  _hProjectiveSimilitudes
  _hQuadraticPairDescent
  _hQuadraticPairScalarExtension
  _hQuaternionSkewModel
  _hQuaternionSpinIsotropy
  _hSimpleDCoordinates
  _hSpinChartFibers
  _hSpinSimilitudeScalarExtension
  _hSplitOrthogonalModel
  _hSplitOrthogonalTangent
  _hSplitOrthogonalTangentBlocks
  _hSplitPairIsometries
  _hSplitProjectiveSpinAction
  _hSplitSemitrace
  _hSplitSpinBorel
  _hSplitSpinCentralIsogeny
  _hSplitSpinChartInImage
  _hSplitSpinDeterminant
  _hSplitSpinDiagonalTorus
  _hSplitSpinDiagramAction
  _hSplitSpinGeometry
  _hSplitSpinIdentityComponent
  _hSplitSpinImage
  _hSplitSpinIntegralComparison
  _hSplitSpinOpenImage
  _hSplitSpinTorusRestriction
  _hSplitSpinTypeD
  _hSplitVectorCentralizer
  _hSplitVectorTangent
  _hTraceOrthogonality
  _hTypeDPositiveRoots
  _hVectorDiagramSwitch
  _hVectorMorphismDescent
  _hVectorVertexStabilizer

theorem spinScaleCover_conditional : SpinScaleCover.{w} :=
  spinScaleCover_proof _hPairIsometryScalarExtension _hQuadraticPairScalarExtension
    _hTraceOrthogonality _hSplitSemitrace

theorem splitExteriorScaleCover_conditional : SplitExteriorScaleCover.{w} :=
  splitExteriorScaleCover_proof

theorem quaternionNormOnUnits_conditional : QuaternionNormOnUnits.{w} :=
  quaternionNormOnUnits_proof

theorem scalePairKernel_conditional : ScalePairKernel.{w} :=
  scalePairKernel_proof

theorem splitScaleParameters_conditional : SplitScaleParameters.{w} :=
  splitScaleParameters_proof

theorem normalizedScaleFamilies_conditional : NormalizedScaleFamilies.{w} :=
  normalizedScaleFamilies_proof

theorem localScaleCover_conditional : LocalScaleCover.{w} :=
  localScaleCover_proof

theorem valuedSquareRoot_conditional : ValuedSquareRoot.{w} :=
  valuedSquareRoot_proof

theorem scaleComparisonDescent_conditional : ScaleComparisonDescent.{w} :=
  scaleComparisonDescent_proof

end Conditional

end
end LinearAlgebraicGroups.Arithmetic.QuaternionSpinScaleCover

universe v8_closure_67f16677156aa604_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«localScaleCover» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«QuaternionSpinScaleCover».«LocalScaleCover».{v8_closure_67f16677156aa604_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«localScaleCover_conditional».{v8_closure_67f16677156aa604_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«normalizedScaleFamilies» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«QuaternionSpinScaleCover».«NormalizedScaleFamilies».{v8_closure_67f16677156aa604_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«normalizedScaleFamilies_conditional».{v8_closure_67f16677156aa604_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«quaternionNormOnUnits» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«QuaternionSpinScaleCover».«QuaternionNormOnUnits».{v8_closure_67f16677156aa604_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«quaternionNormOnUnits_conditional».{v8_closure_67f16677156aa604_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«scaleComparisonDescent» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«QuaternionSpinScaleCover».«ScaleComparisonDescent».{v8_closure_67f16677156aa604_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«scaleComparisonDescent_conditional».{v8_closure_67f16677156aa604_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«scalePairKernel» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«QuaternionSpinScaleCover».«ScalePairKernel».{v8_closure_67f16677156aa604_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«scalePairKernel_conditional».{v8_closure_67f16677156aa604_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«spinScaleCover» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«QuaternionSpinScaleCover».«SpinScaleCover».{v8_closure_67f16677156aa604_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«spinScaleCover_conditional».{v8_closure_67f16677156aa604_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«splitExteriorScaleCover» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«QuaternionSpinScaleCover».«SplitExteriorScaleCover».{v8_closure_67f16677156aa604_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«splitExteriorScaleCover_conditional».{v8_closure_67f16677156aa604_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«splitScaleParameters» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«QuaternionSpinScaleCover».«SplitScaleParameters».{v8_closure_67f16677156aa604_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«splitScaleParameters_conditional».{v8_closure_67f16677156aa604_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«valuedSquareRoot» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«QuaternionSpinScaleCover».«ValuedSquareRoot».{v8_closure_67f16677156aa604_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionSpinScaleCover».«valuedSquareRoot_conditional».{v8_closure_67f16677156aa604_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_67f16677156aa604_u0, v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_67f16677156aa604_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
