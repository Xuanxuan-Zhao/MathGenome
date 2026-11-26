import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.HopfAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Filtration

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Opposite Coalgebra Bialgebra WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

private theorem derivation_isNilpotent {k A : Type*} [Field k] [CharZero k] [CommRing A]
    [Algebra k A] (D : Derivation k A A) {x : A} (hx : IsNilpotent x) : IsNilpotent (D x) := by
  have step (n : ℕ) (y : A) (h : x ^ n * y = 0) : IsNilpotent (D x * y) := by
    induction n generalizing y with
    | zero =>
      simp only [pow_zero, one_mul] at h
      simp [h]
    | succ n ih =>
      have hd := congrArg D h
      simp only [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_one_sub_one,
        smul_eq_mul, nsmul_eq_mul, map_zero] at hd
      have hn : IsUnit ((n + 1 : ℕ) : A) :=
        by simpa using (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) :
          IsUnit ((n + 1 : ℕ) : k)).map (algebraMap k A)
      have hz : x ^ n * ((D x * y) * y) = 0 := by
        refine hn.mul_left_cancel ?_
        linear_combination y * hd - D y * h
      have hp := ih _ hz
      apply IsNilpotent.of_pow (m := 2)
      convert hp using 1
      ring
  obtain ⟨n, hn⟩ := hx
  simpa using step n 1 (by simpa using hn)

section Bialgebra

variable {k A : Type*} [Field k] [CommRing A] [Bialgebra k A]

private abbrev augmentationIdeal (k A : Type*) [Field k] [CommRing A] [Bialgebra k A] :=
  RingHom.ker (counitAlgHom k A).toRingHom

local notation "𝔪" => augmentationIdeal k A

/-- Subtract the constant term with respect to the counit. -/
private def augmentationPart : A →ₗ[k] 𝔪 :=
  (LinearMap.id - (Algebra.linearMap k A).comp (counit (R := k))).codRestrict
    ((𝔪).restrictScalars k) (fun x => by
      change counit (R := k) (x - algebraMap k A (counit (R := k) x)) = 0
      simp)

private abbrev cotangentProjection : A →ₗ[k] (𝔪).Cotangent :=
  ((𝔪).toCotangent.restrictScalars k).comp augmentationPart

private theorem cotangentProjection_mul (a b : A) :
    cotangentProjection (k := k) (a * b) =
      counit (R := k) a • cotangentProjection b + counit (R := k) b • cotangentProjection a := by
  let q := (𝔪).toCotangent.restrictScalars k
  change q (augmentationPart (a * b)) =
    counit (R := k) a • q (augmentationPart b) + counit (R := k) b • q (augmentationPart a)
  rw [← q.map_smul, ← q.map_smul, ← q.map_add]
  change (𝔪).toCotangent _ = (𝔪).toCotangent _
  rw [Ideal.toCotangent_eq]
  have he : ((augmentationPart (k := k) (a * b) : 𝔪) : A) -
      ((counit (R := k) a • augmentationPart b +
        counit (R := k) b • augmentationPart a : 𝔪) : A) =
      (augmentationPart (k := k) a : A) * (augmentationPart (k := k) b : A) := by
    change (a * b - algebraMap k A (counit (R := k) (a * b))) -
      (counit (R := k) a • (b - algebraMap k A (counit (R := k) b)) +
        counit (R := k) b • (a - algebraMap k A (counit (R := k) a))) = _
    change _ = (a - algebraMap k A (counit (R := k) a)) *
      (b - algebraMap k A (counit (R := k) b))
    simp only [counit_mul, map_mul, Algebra.smul_def]
    ring
  rw [he, pow_two]
  exact Ideal.mul_mem_mul (augmentationPart a).2 (augmentationPart b).2

private theorem cotangentProjection_algebraMap {A : Type*} [CommRing A] [Bialgebra k A] (c : k) :
    cotangentProjection (k := k) (algebraMap k A c) = 0 := by
  have h : augmentationPart (k := k) (algebraMap k A c) = 0 := by
    apply Subtype.ext
    change algebraMap k A c - algebraMap k A (counit (R := k) (algebraMap k A c)) = 0
    simp
  simp [cotangentProjection, h]

private def tangentHom (l : (𝔪).Cotangent →ₗ[k] k) : A →ₐ[k] TrivSqZeroExt A A := by
  let d := l.comp cotangentProjection
  let f (a : A) : TrivSqZeroExt A A :=
    TrivSqZeroExt.inl (algebraMap k A (counit (R := k) a)) +
      TrivSqZeroExt.inr (algebraMap k A (d a))
  have hfst (a : A) : (f a).fst = algebraMap k A (counit (R := k) a) := by
    simp [f, TrivSqZeroExt.fst_add]
  have hsnd (a : A) : (f a).snd = algebraMap k A (d a) := by
    simp [f, TrivSqZeroExt.snd_add]
  have halg (c : k) : d (algebraMap k A c) = 0 := by
    change l (cotangentProjection (algebraMap k A c)) = _
    rw [cotangentProjection_algebraMap (A := A), map_zero]
  exact
    { toFun := f
      map_one' := by
        have h : d 1 = 0 := by simpa using halg 1
        apply TrivSqZeroExt.ext <;> simp [hfst, hsnd, h]
      map_zero' := by apply TrivSqZeroExt.ext <;> simp [hfst, hsnd]
      map_add' := fun x y => by
        apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, hfst, hsnd]
      map_mul' := fun x y => by
        apply TrivSqZeroExt.ext
        · simp [TrivSqZeroExt.fst_mul, hfst]
        · have hd : d (x * y) = counit (R := k) x * d y + counit (R := k) y * d x := by
            change l (cotangentProjection (x * y)) = _
            rw [cotangentProjection_mul, map_add, map_smul, map_smul]
            rfl
          simp [TrivSqZeroExt.snd_mul, hfst, hsnd, hd, smul_eq_mul, mul_comm]
      commutes' := fun c => by
        rw [TrivSqZeroExt.algebraMap_eq_inl']
        apply TrivSqZeroExt.ext <;> simp [hfst, hsnd, halg] }

@[simp] private theorem tangentHom_fst (l : (𝔪).Cotangent →ₗ[k] k) (a : A) :
    (tangentHom l a).fst = algebraMap k A (counit (R := k) a) := by
  change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : TrivSqZeroExt A A).fst = _
  simp [TrivSqZeroExt.fst_add]

@[simp] private theorem tangentHom_snd (l : (𝔪).Cotangent →ₗ[k] k) (a : A) :
    (tangentHom l a).snd = algebraMap k A (l (cotangentProjection a)) := by
  change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : TrivSqZeroExt A A).snd = _
  simp [TrivSqZeroExt.snd_add]

private abbrev tangentTensorHom (l : (𝔪).Cotangent →ₗ[k] k) :
    A ⊗[k] A →ₐ[k] TrivSqZeroExt A A :=
  Algebra.TensorProduct.lift (tangentHom l) (TrivSqZeroExt.inlAlgHom k A A)
    (fun _ _ => Commute.all _ _)

/-- Extend a tangent functional by applying it to the first factor of comultiplication. -/
private def invariantDerivation (l : (𝔪).Cotangent →ₗ[k] k) : Derivation k A A := by
  let F := tangentTensorHom l
  have hF (a : A) : (F (comul (R := k) a)).fst = a := by
    have H : (TrivSqZeroExt.fstHom k A A).toLinearMap.comp F.toLinearMap =
        (TensorProduct.lid k A).toLinearMap.comp ((counit (R := k)).rTensor A) := by
      apply TensorProduct.ext'
      intro x y
      change (F (x ⊗ₜ[k] y)).fst = _
      simp [F, tangentTensorHom, TrivSqZeroExt.fst_mul, Algebra.smul_def]
    change ((TrivSqZeroExt.fstHom k A A).toLinearMap.comp F.toLinearMap) (comul a) = a
    rw [H, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
    change TensorProduct.lid k A (1 ⊗ₜ[k] a) = a
    simp
  refine Derivation.mk' ((TrivSqZeroExt.sndHom A A).restrictScalars k ∘ₗ
    F.toLinearMap ∘ₗ (comulAlgHom k A).toLinearMap) ?_
  intro a b
  change (F (comul (R := k) (a * b))).snd =
    a • (F (comul (R := k) b)).snd + b • (F (comul (R := k) a)).snd
  rw [comul_mul, map_mul, TrivSqZeroExt.snd_mul, hF, hF, op_smul_eq_smul]

private theorem counit_invariantDerivation (l : (𝔪).Cotangent →ₗ[k] k) (a : A) :
    counit (R := k) (invariantDerivation l a) = l (cotangentProjection a) := by
  have H : (counit (R := k)).comp
      ((TrivSqZeroExt.sndHom A A).restrictScalars k ∘ₗ (tangentTensorHom l).toLinearMap) =
      (l.comp cotangentProjection) ∘ₗ
        (TensorProduct.rid k A).toLinearMap ∘ₗ ((counit (R := k)).lTensor A) := by
    apply TensorProduct.ext'
    intro x y
    change counit ((tangentTensorHom l (x ⊗ₜ[k] y)).snd) = _
    rw [tangentTensorHom, Algebra.TensorProduct.lift_tmul, TrivSqZeroExt.snd_mul]
    change counit ((tangentHom l x).fst • (TrivSqZeroExt.inl y : TrivSqZeroExt A A).snd +
      MulOpposite.op (TrivSqZeroExt.inl y : TrivSqZeroExt A A).fst • (tangentHom l x).snd) =
        l (cotangentProjection (TensorProduct.rid k A (x ⊗ₜ[k] counit (R := k) y)))
    simp [smul_eq_mul, mul_comm]
  have he : counit (R := k) (invariantDerivation l a) =
      ((counit (R := k)).comp ((TrivSqZeroExt.sndHom A A).restrictScalars k ∘ₗ
        (tangentTensorHom l).toLinearMap)) (comul a) := rfl
  rw [he, H]
  change l (cotangentProjection (TensorProduct.rid k A ((counit (R := k)).lTensor A (comul a)))) = _
  rw [Coalgebra.lTensor_counit_comul]
  simp

private theorem counit_smul_cotangent (a : A) (v : (𝔪).Cotangent) :
    a • v = counit (R := k) a • v := by
  have h := Ideal.Cotangent.smul_eq_zero_of_mem (augmentationPart (k := k) a).2 v
  change (a - algebraMap k A (counit (R := k) a)) • v = 0 at h
  rwa [sub_smul, algebraMap_smul, sub_eq_zero] at h

private theorem cotangent_finite [IsNoetherianRing A] : Module.Finite k (𝔪).Cotangent := by
  classical
  obtain ⟨n, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (𝔪))
  let v (i : Fin n) : (𝔪).Cotangent :=
    (𝔪).toCotangent ⟨r i, hr ▸ Submodule.subset_span (Set.mem_range_self i)⟩
  apply Module.Finite.of_fg_top
  refine Submodule.fg_iff_exists_fin_generating_family.mpr ⟨n, v, eq_top_iff.mpr ?_⟩
  intro x _
  obtain ⟨a, rfl⟩ := (𝔪).toCotangent_surjective x
  have hspan : (a : A) ∈ Ideal.span (Set.range r) := by
    change (a : A) ∈ Submodule.span A (Set.range r)
    rw [hr]
    exact a.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hspan
  have ha : a = ∑ i, c i • (⟨r i, hr ▸ Submodule.subset_span (Set.mem_range_self i)⟩ : 𝔪) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul, hc]
  rw [ha, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, counit_smul_cotangent]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- A derivation which is the identity modulo the square of an ideal acts on each
successive quotient of its powers by the degree. -/
private theorem derivation_sub_nsmul_mem_pow (I : Ideal A) (E : Derivation k A A)
    (h₀ : ∀ x, E x ∈ I) (h₁ : ∀ x ∈ I, E x - x ∈ I ^ 2)
    (n : ℕ) {x : A} (hx : x ∈ I ^ n) : E x - n • x ∈ I ^ (n + 1) := by
  induction n generalizing x with
  | zero => simpa using h₀ x
  | succ n ih =>
    rw [Ideal.IsTwoSided.pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have h := Ideal.mul_mem_mul (h₁ a ha) hb
      rw [← pow_add, show 2 + n = n + 1 + 1 by omega] at h
      have h' : a * (E b - n • b) ∈ I ^ (n + 1 + 1) := by
        rw [Ideal.IsTwoSided.pow_succ]
        exact Ideal.mul_mem_mul ha (ih hb)
      have hsum := add_mem h h'
      convert hsum using 1
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    · rw [map_add, nsmul_add, add_sub_add_comm]
      exact add_mem ha hb

/-- Lift a cotangent basis and pair it with the invariant derivations of the dual basis.
The resulting derivation acts by degree on the augmentation filtration, and its
summands carry nilpotents one step deeper in that filtration. -/
private theorem nilpotent_mem_augmentation_pow [CharZero k] [IsNoetherianRing A] :
    ∀ (n : ℕ) (x : A), IsNilpotent x → x ∈ (𝔪) ^ (n + 1) := by
  classical
  let : Module.Finite k (𝔪).Cotangent := cotangent_finite
  let b := Module.finBasis k (𝔪).Cotangent
  let a i := ((𝔪).toCotangent_surjective (b i)).choose
  have ha i : (𝔪).toCotangent (a i) = b i := ((𝔪).toCotangent_surjective (b i)).choose_spec
  let D i := invariantDerivation (b.coord i)
  let E : Derivation k A A := ∑ i, (a i : A) • D i
  let E' (x : A) : 𝔪 := ∑ i, D i x • a i
  have heq (x : A) : E x = (E' x : A) := by
    change (Derivation.coeFnAddMonoidHom (R := k) (A := A) (M := A) E) x = _
    simp only [E, E', map_sum, Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
      Derivation.smul_apply, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul, mul_comm]
  have h₀ (x : A) : E x ∈ 𝔪 := heq x ▸ (E' x).2
  have h₁ (x : A) (hx : x ∈ 𝔪) : E x - x ∈ (𝔪) ^ 2 := by
    have hc : cotangentProjection (k := k) x = (𝔪).toCotangent ⟨x, hx⟩ := by
      change (𝔪).toCotangent (augmentationPart x) = _
      congr 1
      apply Subtype.ext
      change x - algebraMap k A (counit (R := k) x) = x
      rw [show counit (R := k) x = 0 from hx, map_zero, sub_zero]
    rw [heq, ← Ideal.toCotangent_eq (x := E' x) (y := ⟨x, hx⟩), ← hc]
    simp only [E', map_sum, map_smul, counit_smul_cotangent, D, counit_invariantDerivation, ha]
    exact b.sum_repr (cotangentProjection x)
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [zero_add, pow_one]
    exact (hx.map (counitAlgHom k A)).eq_zero
  | succ n ih =>
    intro x hx
    have hE : E x ∈ (𝔪) ^ (n + 1 + 1) := by
      rw [heq]
      simp only [E', Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [Ideal.IsTwoSided.pow_succ]
      rw [Ideal.mul_comm]
      exact Ideal.mul_mem_mul (ih (D i x) (derivation_isNilpotent (D i) hx)) (a i).2
    have h := sub_mem hE (derivation_sub_nsmul_mem_pow (𝔪) E h₀ h₁ (n + 1) (ih x hx))
    have hs : (n + 1) • x ∈ (𝔪) ^ (n + 1 + 1) := by simpa using h
    have hu : IsUnit ((n + 1 : ℕ) : A) := by
      simpa using ((isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) :
        IsUnit ((n + 1 : ℕ) : k)).map (algebraMap k A))
    rw [nsmul_eq_mul] at hs
    exact (Ideal.unit_mul_mem_iff_mem (𝔪 ^ (n + 1 + 1)) hu).mp hs

private theorem nilpotent_eq_zero_at_augmentation [CharZero k] [IsNoetherianRing A] {x : A}
    (hx : IsNilpotent x) : ∃ s : A, counit (R := k) s ≠ 0 ∧ s * x = 0 := by
  have hm : (𝔪).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (counitAlgHom k A).toRingHom Bialgebra.counit_surjective
  let : (𝔪).IsPrime := hm.isPrime
  let B := Localization.AtPrime (𝔪)
  have hz : algebraMap A B x = 0 := by
    rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal B)
      (IsLocalRing.maximalIdeal.isMaximal B).ne_top, Submodule.mem_iInf]
    intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (nilpotent_mem_augmentation_pow (k := k) n x hx)
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (𝔪).primeCompl B x).mp hz
  exact ⟨s, s.2, hs⟩

end Bialgebra

section HopfAlgebra

variable {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]

/-- Pullback along left translation by a rational point. -/
private def translationHom (p : A →ₐ[k] k) : A →ₐ[k] A :=
  (toConv ((Algebra.ofId k A).comp p) * toConv (AlgHom.id k A)).ofConv

private theorem counit_comp_translation (p : A →ₐ[k] k) :
    (counitAlgHom k A).comp (translationHom p) = p := by
  rw [translationHom, AlgHom.comp_convMul_distrib]
  have hp : (counitAlgHom k A).comp ((Algebra.ofId k A).comp p) = p :=
    AlgHom.ext fun a => (counitAlgHom k A).commutes (p a)
  have he : (counitAlgHom k A).comp (AlgHom.id k A) = (1 : WithConv (A →ₐ[k] k)).ofConv := rfl
  rw [hp, he, toConv_ofConv, mul_one, ofConv_toConv]

private theorem translation_comp (p q : A →ₐ[k] k) :
    (translationHom p).comp (translationHom q) = translationHom (toConv q * toConv p).ofConv := by
  change (translationHom p).comp
    (toConv ((Algebra.ofId k A).comp q) * toConv (AlgHom.id k A)).ofConv = _
  rw [AlgHom.comp_convMul_distrib, AlgHom.comp_id]
  have h : (translationHom p).comp ((Algebra.ofId k A).comp q) =
      (Algebra.ofId k A).comp q := AlgHom.ext fun a => (translationHom p).commutes (q a)
  rw [h]
  change (toConv ((Algebra.ofId k A).comp q) *
      (toConv ((Algebra.ofId k A).comp p) * toConv (AlgHom.id k A))).ofConv = _
  rw [← mul_assoc, translationHom, AlgHom.comp_convMul_distrib, toConv_ofConv]

private theorem reduced_hopf_of_isAlgClosed [CharZero k] [IsAlgClosed k]
    [Algebra.FiniteType k A] : _root_.IsReduced A := by
  constructor
  intro x hx
  apply eq_zero_of_localization x
  intro P hP
  let : P.IsMaximal := hP
  let : Field (A ⧸ P) := Ideal.Quotient.field P
  let : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  let e := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let p := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k P)
  have hp (y : A) : p y = 0 ↔ y ∈ P := by
    change e.symm (Ideal.Quotient.mk P y) = 0 ↔ y ∈ P
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  -- The inverse point translates the denominator at the identity back to P.
  let q := ((toConv p)⁻¹).ofConv
  let t := translationHom p
  let s := translationHom q
  have ht₁ : s.comp t = AlgHom.id k A := by
    rw [translation_comp, show toConv q = (toConv p)⁻¹ from rfl, mul_inv_cancel]
    exact congrArg WithConv.ofConv (one_mul (toConv (AlgHom.id k A)))
  have ht₂ : t.comp s = AlgHom.id k A := by
    rw [translation_comp, show toConv q = (toConv p)⁻¹ from rfl, inv_mul_cancel]
    exact congrArg WithConv.ofConv (one_mul (toConv (AlgHom.id k A)))
  have hs : p.comp s = counitAlgHom k A := by
    rw [← counit_comp_translation p, AlgHom.comp_assoc, ht₂, AlgHom.comp_id]
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨y, hy, hyx⟩ := nilpotent_eq_zero_at_augmentation (k := k) (hx.map t)
  have hy' : s y ∉ P := by
    rw [← hp]
    exact fun h => hy ((congrArg (fun f : A →ₐ[k] k => f y) hs).symm ▸ h)
  have hz : s y * x = 0 := by
    have h := congrArg s hyx
    simpa only [map_mul, map_zero, show s (t x) = x from congrArg (fun f => f x) ht₁] using h
  exact (IsLocalization.map_eq_zero_iff P.primeCompl _ x).mpr ⟨⟨s y, hy'⟩, hz⟩

end HopfAlgebra

private theorem affine_group_reduced_of_isAlgClosed {k : Type u} [Field k] [CharZero k]
    [IsAlgClosed k] (G : Specs.GroupScheme k) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    IsReduced G.X.left := by
  obtain ⟨A, ⟨i⟩⟩ := (essImage_hopfSpec (R := CommRingCat.of k)).mpr
    (show IsAffine G.X.left from inferInstance)
  let e : Spec (CommRingCat.of A.unop) ≅ G.X.left :=
    ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso i
  have hc : e.hom ≫ G.X.hom = ((hopfSpec (CommRingCat.of k)).obj A).X.hom :=
    Over.w i.hom.hom.hom
  have h : LocallyOfFiniteType (e.hom ≫ G.X.hom) := inferInstance
  rw [hc] at h
  have : Algebra.FiniteType k A.unop := (hopfSpec_locallyOfFiniteType_iff k A.unop).mp h
  have : _root_.IsReduced A.unop := reduced_hopf_of_isAlgClosed (k := k)
  have : IsReduced (Spec (CommRingCat.of A.unop)) :=
    (affine_isReduced_iff _).mpr inferInstance
  exact isReduced_of_isOpenImmersion e.inv

/-- Cartier's theorem. Every finite-type affine group scheme in characteristic zero is smooth. -/
theorem characteristicZeroSmoothness : Specs.CharacteristicZeroSmoothness.{u} := by
  intro k _ _ G
  let K := AlgebraicClosure k
  let g := fieldSpecMap k K
  let H := (groupBaseChange k K).obj G.1
  have : IsAffine G.1.X.left := G.2.1
  have : LocallyOfFiniteType G.1.X.hom := G.2.2.1
  have : IsAffine H.X.left := inferInstanceAs (IsAffine (pullback G.1.X.hom g))
  have : LocallyOfFiniteType H.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.1.X.hom g))
  have hred : IsReduced H.X.left := affine_group_reduced_of_isAlgClosed H
  have hs : Smooth H.X.hom := smoothOfReducedOverPerfectField K H hred
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := g)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · exact hs

end

end LinearAlgebraicGroups
