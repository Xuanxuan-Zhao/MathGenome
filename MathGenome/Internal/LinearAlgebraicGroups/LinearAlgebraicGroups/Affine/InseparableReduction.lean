import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.InseparableReduction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.TensorProduct.Quotient
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Coalgebra HopfAlgebra
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.InseparableReduction

noncomputable section

open Specs.InseparableReduction

private abbrev Line (k : Type u) [CommRing k] := MvPolynomial (Fin 1) k

private def planeAsPolynomial (k : Type u) [CommRing k] :
    Plane k ≃ₐ[k] Polynomial (Line k) :=
  (MvPolynomial.renameEquiv k Equiv.ulift).trans (MvPolynomial.finSuccEquiv k 1)

private theorem relation_as_polynomial {k : Type u} [CommRing k] (p : ℕ) (c : k) :
    planeAsPolynomial k (relation p c) =
      Polynomial.X ^ p - Polynomial.C (MvPolynomial.C c * (MvPolynomial.X 0 : Line k) ^ p) := by
  have hx : planeAsPolynomial k (x k) = Polynomial.C (MvPolynomial.X 0 : Line k) := by
    simpa [planeAsPolynomial, x] using (MvPolynomial.finSuccEquiv_X_succ (R := k) (j := (0 : Fin 1)))
  have hy : planeAsPolynomial k (y k) = Polynomial.X := by
    simpa [planeAsPolynomial, y] using (MvPolynomial.finSuccEquiv_X_zero (R := k) (n := 1))
  have hc : planeAsPolynomial k (MvPolynomial.C c) =
      Polynomial.C (MvPolynomial.C c) := by
    simp only [planeAsPolynomial, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_C, MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply]
  rw [relation, map_sub, map_pow, map_mul, map_pow, hx, hy, hc, ← map_pow, ← map_mul]

/-- Divide a putative root by the nonzero coordinate X. Its p-th power then lies in
the coefficient ring. Integral closedness places the quotient in that ring, where
evaluation at X = 0 would give a p-th root of c in k. -/
private theorem no_root_in_fraction_field {k : Type u} [Field k] {p : ℕ}
    (hp : p.Prime) {c : k} (hc : ∀ b : k, b ^ p ≠ c)
    (b : FractionRing (Line k)) :
    b ^ p ≠ algebraMap (Line k) (FractionRing (Line k))
      (MvPolynomial.C c * (MvPolynomial.X 0 : Line k) ^ p) := by
  intro hb
  let f := algebraMap (Line k) (FractionRing (Line k))
  let t : Line k := MvPolynomial.X 0
  have ht : f t ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (Line k) (FractionRing (Line k))).ne
        (MvPolynomial.X_ne_zero (R := k) (s := (0 : Fin 1)))
  have hpow : (b / f t) ^ p = f (MvPolynomial.C c) := by
    rw [div_pow, hb, map_mul, map_pow, mul_div_cancel_right₀ _ (pow_ne_zero _ ht)]
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := Line k) hp.pos (hpow ▸ isIntegral_algebraMap (x := (MvPolynomial.C c : Line k)))
  have hqpow : q ^ p = MvPolynomial.C c :=
    (IsFractionRing.injective (Line k) (FractionRing (Line k))) (by
      change f (q ^ p) = f (MvPolynomial.C c)
      rw [map_pow, hq, hpow])
  exact hc (MvPolynomial.eval (fun _ => 0) q) (by
    simpa using congrArg (MvPolynomial.eval (fun _ : Fin 1 => (0 : k))) hqpow)

theorem integralCoordinates : IntegralCoordinates.{u} := by
  intro k _ p hp _ c hc
  let e := (planeAsPolynomial k).toRingEquiv
  let d : Line k := MvPolynomial.C c * MvPolynomial.X 0 ^ p
  have he : e (relation p c) = Polynomial.X ^ p - Polynomial.C d :=
    relation_as_polynomial p c
  have hmonic := Polynomial.monic_X_pow_sub_C d hp.out.ne_zero
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C d) := by
    apply (hmonic.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (Line k))).mpr
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] using
      X_pow_sub_C_irreducible_of_prime hp.out (no_root_in_fraction_field hp.out hc)
  have hprime : Prime (relation p c) := by
    rw [← MulEquiv.prime_iff e, he]
    exact hirr.prime
  exact (Ideal.Quotient.isDomain_iff_prime _).mpr ((Ideal.span_singleton_prime hprime.ne_zero).mpr hprime)

private theorem line_class_ne_zero {K : Type u} [Field K] {p : ℕ} (hp : p.Prime)
    (c a : K) :
    Ideal.Quotient.mk (relationIdeal p c) (y K - MvPolynomial.C a * x K) ≠ 0 := by
  intro h
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let e := planeAsPolynomial K
  have hs : e (y K - MvPolynomial.C a * x K) =
      Polynomial.X - Polynomial.C (MvPolynomial.C a * (MvPolynomial.X 0 : Line K)) := by
    simpa [pow_one, relation] using relation_as_polynomial 1 a
  have hh := map_dvd e hd
  rw [relation_as_polynomial, hs] at hh
  have hle := Polynomial.natDegree_le_of_dvd hh (Polynomial.X_sub_C_ne_zero _)
  rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_X_sub_C] at hle
  exact hp.one_lt.not_ge hle

private def coordinateBaseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    (p : ℕ) (c : k) : K ⊗[k] Coordinates p c ≃ₐ[K] Coordinates p (algebraMap k K c) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := PlaneIndex.{u}) k K
  let I := relationIdeal p c
  let J := I.map (Algebra.TensorProduct.includeRight : Plane k →ₐ[k] K ⊗[k] Plane k)
  have hr : e (1 ⊗ₜ[k] relation p c) = relation p (algebraMap k K c) := by
    change MvPolynomial.algebraTensorAlgEquiv k K (1 ⊗ₜ[k] relation p c) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    simp [relation, x, y]
  have he : relationIdeal p (algebraMap k K c) = J.map (e : _ →+* _) := by
    simp only [J, I, Ideal.map_span, Set.image_singleton]
    change Ideal.span {relation p (algebraMap k K c)} = Ideal.span {e (1 ⊗ₜ[k] relation p c)}
    rw [hr]
  exact (Algebra.TensorProduct.tensorQuotientEquiv K (Plane k) K I).trans
    (Ideal.quotientEquivAlg J _ e he)

theorem scalarExtension : ScalarExtension.{u} := by
  intro k K _ _ _ p hp _ c
  let e := coordinateBaseChange (K := K) p c
  refine ⟨e, ?_, ?_⟩
  · intro f
    simp [e, coordinateBaseChange, MvPolynomial.algebraTensorAlgEquiv_tmul]
  · intro a ha
    let : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
    let : CharP (Plane K) p := charP_of_injective_ringHom (MvPolynomial.C_injective PlaneIndex K) p
    have hfactor : relation p (algebraMap k K c) = (y K - MvPolynomial.C a * x K) ^ p := by
      rw [sub_pow_char, mul_pow, ← map_pow, ha, relation]
    refine ⟨hfactor, line_class_ne_zero hp.out _ _, ?_⟩
    rw [← map_pow, ← hfactor]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

section AdditivePlane

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]

local instance : HopfAlgebra k (Plane k) := StandardGroups.additivePowerHopf k PlaneIndex

local instance (priority := high) : Bialgebra k (Plane k) :=
  (StandardGroups.additivePowerHopf k PlaneIndex).toBialgebra

local instance (priority := high) : Coalgebra k (Plane k) :=
  (StandardGroups.additivePowerHopf k PlaneIndex).toBialgebra.toCoalgebra

local instance (priority := high) : CoalgebraStruct k (Plane k) :=
  (StandardGroups.additivePowerHopf k PlaneIndex).toBialgebra.toCoalgebra.toCoalgebraStruct

private theorem plane_comul (i : PlaneIndex.{u}) :
    comul (R := k) (MvPolynomial.X i : Plane k) =
      MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i :=
  MvPolynomial.aeval_X _ i

private theorem plane_counit (i : PlaneIndex.{u}) :
    counit (R := k) (MvPolynomial.X i : Plane k) = 0 :=
  MvPolynomial.aeval_X _ i

private theorem plane_antipode (i : PlaneIndex.{u}) :
    antipode k (MvPolynomial.X i : Plane k) = -MvPolynomial.X i :=
  MvPolynomial.aeval_X _ i

private theorem primitive_relation (c : k) :
    comul (R := k) (relation p c) = relation p c ⊗ₜ[k] 1 + 1 ⊗ₜ[k] relation p c := by
  let l : Plane k →ₐ[k] Plane k ⊗[k] Plane k := Algebra.TensorProduct.includeLeft
  let r : Plane k →ₐ[k] Plane k ⊗[k] Plane k := Algebra.TensorProduct.includeRight
  let Δ := Bialgebra.comulAlgHom k (Plane k)
  let : CharP (Plane k ⊗[k] Plane k) p :=
    charP_of_injective_algebraMap (algebraMap k (Plane k ⊗[k] Plane k)).injective p
  have hpow (i : PlaneIndex.{u}) :
      Δ (MvPolynomial.X i ^ p) = l (MvPolynomial.X i ^ p) + r (MvPolynomial.X i ^ p) := by
    have hi : Δ (MvPolynomial.X i) = l (MvPolynomial.X i) + r (MvPolynomial.X i) :=
      plane_comul i
    rw [map_pow, hi, add_pow_char, map_pow, map_pow]
  change Δ (relation p c) = l (relation p c) + r (relation p c)
  have hc : (MvPolynomial.C c : Plane k) = algebraMap k (Plane k) c := rfl
  simp only [relation, map_sub, map_mul, hc, Δ.commutes, l.commutes, r.commutes, x, y, hpow]
  ring

private theorem relation_isHopfIdeal (c : k) : (relationIdeal p c).IsHopfIdeal k := by
  let I := relationIdeal p c
  let q := Ideal.Quotient.mkₐ k I
  let Δ := Bialgebra.comulAlgHom k (Plane k)
  let ε := Bialgebra.counitAlgHom k (Plane k)
  let S := HopfAlgebra.antipodeAlgHom k (Plane k)
  let : CharP (Plane k) p := charP_of_injective_ringHom (MvPolynomial.C_injective PlaneIndex k) p
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hq : q (relation p c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hε : ε (relation p c) = 0 := by
    simp [ε, relation, plane_counit, hp]
  have hS : S (relation p c) = -relation p c := by
    have hx : S (x k) = -x k := plane_antipode (ULift.up 1)
    have hy : S (y k) = -y k := plane_antipode (ULift.up 0)
    have hc : S (MvPolynomial.C c) = MvPolynomial.C c := S.commutes c
    have hneg (z : Plane k) : (-z) ^ p = -(z ^ p) := by
      rw [neg_pow, neg_one_pow_char, neg_one_mul]
    simp only [relation, map_sub, map_mul, map_pow, hx, hy, hc, hneg]
    ring
  refine { toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_ }
  · intro z hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hz
    change ε (relation p c * t) = 0
    rw [map_mul, hε, zero_mul]
  · intro z hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hz
    change Algebra.TensorProduct.map q q (Δ (relation p c * t)) = 0
    have hΔ : Δ (relation p c) = relation p c ⊗ₜ[k] 1 + 1 ⊗ₜ[k] relation p c :=
      primitive_relation c
    rw [map_mul, map_mul, hΔ]
    simp [hq]
  · intro z hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (S (relation p c * t)) = 0
    simp [map_mul, hS, hq]

end AdditivePlane

private theorem not_geometricallyReduced {k : Type u} [Field k]
    {p : ℕ} [Fact p.Prime] [CharP k p] (c : k) (hc : ∀ b : k, b ^ p ≠ c) :
    ¬ GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k (Coordinates p c)))) := by
  intro hred
  let P : Polynomial k := Polynomial.X ^ p - Polynomial.C c
  have : Fact (Irreducible P) := ⟨X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) hc⟩
  let K := AdjoinRoot P
  let Q := Coordinates p c
  let f := Spec.map (CommRingCat.ofHom (algebraMap k Q))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsReduced (pullback f g) :=
    hred.geometrically_isReduced g _ _ (.of_hasPullback f g)
  let i := pullbackSymmetry f g ≪≫ pullbackSpecIso k K Q
  have h := isReduced_of_isOpenImmersion i.inv
  have : _root_.IsReduced (K ⊗[k] Q) := (affine_isReduced_iff _).mp h
  obtain ⟨e, _, he⟩ := scalarExtension k K p c
  let a := AdjoinRoot.root P
  have ha : a ^ p = algebraMap k K c := root_X_pow_sub_C_pow p c
  obtain ⟨_, hne, hpow⟩ := he a ha
  have : _root_.IsReduced (Coordinates p (algebraMap k K c)) :=
    isReduced_of_injective e.symm e.symm.injective
  exact hne (IsNilpotent.eq_zero ⟨p, hpow⟩)

open private additivePowerRepresentation Representation.operations from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups in
theorem closedSubgroupExample : ClosedSubgroupExample.{u} := by
  intro k _ p hp _ c hc
  let h := Representation.operations (additivePowerRepresentation (k := k) (ι := PlaneIndex))
  refine ⟨h, plane_comul, plane_counit, plane_antipode,
    primitive_relation c, relation_isHopfIdeal c, ?_⟩
  let _ := h.hopf
  have := relation_isHopfIdeal (p := p) c
  let A := CommHopfAlgCat.of k (Plane k)
  let B := hopfQuotient A (relationIdeal p c)
  let G := specGroup B
  have hFinite : Algebra.FiniteType k (Coordinates p c) := inferInstance
  have : LocallyOfFiniteType G.X.hom := (hopfSpec_locallyOfFiniteType_iff k B).mpr hFinite
  have := integralCoordinates k p c hc
  have hGeom : ¬ GeometricallyReduced G.X.hom := not_geometricallyReduced c hc
  have hAffine : IsAffine G.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (Coordinates p c))))
  have hQuasiCompact : QuasiCompact G.X.hom := inferInstanceAs
    (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (Coordinates p c)))))
  exact ⟨(hopfMapClosedImmersion k _).mpr Ideal.Quotient.mk_surjective, hAffine, inferInstance, hQuasiCompact,
    (affine_isReduced_iff (CommRingCat.of (Coordinates p c))).mpr inferInstance,
    hGeom, fun hs => hGeom ((groupSmoothnessCriteria k G).1.mp hs)⟩

theorem nonperfectFieldExample : NonperfectFieldExample.{u} := by
  intro k _ hk
  obtain ⟨p, hp⟩ := CharP.exists k
  have hpPrime : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right (fun h => by
    subst p
    let _ : CharZero k := CharP.charP_to_charZero k
    exact hk inferInstance)
  have : Fact p.Prime := ⟨hpPrime⟩
  have hsurj : ¬ Function.Surjective (frobenius k p) := fun hs => by
    have := PerfectRing.ofSurjective k p hs
    exact hk (PerfectRing.toPerfectField k p)
  obtain ⟨c, hc⟩ := not_forall.mp hsurj
  have hc' (b : k) : b ^ p ≠ c := fun hb => hc ⟨b, hb⟩
  obtain ⟨h, _, _, _, _, hI, _, hAff, hFinite, hQC, hRed, hGeom, hSmooth⟩ :=
    closedSubgroupExample k p c hc'
  let _ := h.hopf
  let G := specGroup (hopfQuotient (CommHopfAlgCat.of k (Plane k)) (relationIdeal p c))
  exact ⟨⟨G, hAff, hFinite, hQC⟩, hRed, hGeom, hSmooth⟩

end

end LinearAlgebraicGroups.InseparableReduction
