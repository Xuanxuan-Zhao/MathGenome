import Specs.LinearAlgebraicGroups.Unipotent.WoundExample
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Unipotent.ExactOperations
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Bialgebra.Primitive
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Polynomial Coalgebra
open Algebra.TensorProduct
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.WoundExample

open Specs.WoundExample
open Specs.StandardGroups (HopfOperations)
noncomputable section

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {p : ℕ} {c : k}

section Frobenius

variable [Fact p.Prime] [CharP k p]

private lemma pow_add {R : Type u} [CommRing R] [Algebra k R] (a b : R) :
    (a + b) ^ p = a ^ p + b ^ p := by
  have hp : (p : R) = 0 := by
    rw [← map_natCast (algebraMap k R), CharP.cast_eq_zero, map_zero]
  simp [add_pow_prime_eq' (Fact.out : p.Prime), hp]

private lemma pow_sub {R : Type u} [CommRing R] [Algebra k R] (a b : R) :
    (a - b) ^ p = a ^ p - b ^ p := by
  rw [eq_sub_iff_add_eq, ← pow_add (k := k), sub_add_cancel]

end Frobenius

private lemma coordinate_relation :
    y k p c ^ p - x k p c + algebraMap k (Coordinates k p c) c * x k p c ^ p = 0 := by
  let q := Ideal.Quotient.mkₐ k (equationIdeal k p c)
  have h : q (equation k p c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hC : q (MvPolynomial.C c) = algebraMap k (Coordinates k p c) c := q.commutes c
  change q (MvPolynomial.X yIndex) ^ p - q (MvPolynomial.X xIndex) +
    algebraMap k (Coordinates k p c) c * q (MvPolynomial.X xIndex) ^ p = 0
  simpa only [equation, map_add, map_sub, map_mul, map_pow, hC] using h

private def coordinateMap {R : Type u} [CommRing R] [Algebra k R]
    (a b : R) (h : b ^ p - a + algebraMap k R c * a ^ p = 0) :
    Coordinates k p c →ₐ[k] R :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun i : PlaneIndex.{u} => if i.down then b else a)
    (by
      refine (Ideal.span_singleton_le_iff_mem (RingHom.ker _)).mpr ?_
      change MvPolynomial.aeval _ (equation k p c) = 0
      simpa only [equation, map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, ite_true, ite_false, Bool.true_eq_false,
        xIndex, yIndex, ULift.down_up, Bool.false_eq_true] using h)

@[simp] private lemma coordinateMap_x {R : Type u} [CommRing R] [Algebra k R]
    (a b : R) (h : b ^ p - a + algebraMap k R c * a ^ p = 0) :
    coordinateMap (c := c) a b h (x k p c) = a := by
  change MvPolynomial.aeval _ (MvPolynomial.X xIndex) = _
  simp

@[simp] private lemma coordinateMap_y {R : Type u} [CommRing R] [Algebra k R]
    (a b : R) (h : b ^ p - a + algebraMap k R c * a ^ p = 0) :
    coordinateMap (c := c) a b h (y k p c) = b := by
  change MvPolynomial.aeval _ (MvPolynomial.X yIndex) = _
  simp

private lemma coordinate_ext {R : Type u} [CommRing R] [Algebra k R]
    {f g : Coordinates k p c →ₐ[k] R} (hx : f (x k p c) = g (x k p c))
    (hy : f (y k p c) = g (y k p c)) : f = g := by
  apply Ideal.Quotient.algHom_ext k
  apply MvPolynomial.algHom_ext
  rintro ⟨_ | _⟩
  · exact hx
  · exact hy

variable [Fact p.Prime] [CharP k p]

private lemma polynomial_constant (hc : ∀ d : k, d ^ p ≠ c) {a b : Polynomial k}
    (h : b ^ p = a - C c * a ^ p) : a.natDegree = 0 ∧ b.natDegree = 0 := by
  have hp := (Fact.out : p.Prime).two_le
  have hcz : c ≠ 0 := by simpa [zero_pow (show p ≠ 0 by omega)] using (hc 0).symm
  have ha : a.natDegree = 0 := by
    by_contra hn
    have ha0 : a ≠ 0 := fun h0 => hn (h0 ▸ natDegree_zero)
    have hlt : a.natDegree < (C c * a ^ p).natDegree := by
      rw [natDegree_mul (C_ne_zero.mpr hcz) (pow_ne_zero _ ha0),
        natDegree_C, natDegree_pow, zero_add]
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right (by omega : 1 < p)
        (Nat.pos_of_ne_zero hn)
    have hdegree : a.degree < (C c * a ^ p).degree := degree_lt_degree hlt
    have hlead := congrArg leadingCoeff h
    rw [leadingCoeff_pow, leadingCoeff_sub_of_degree_lt' hdegree, leadingCoeff_mul,
      leadingCoeff_C, leadingCoeff_pow] at hlead
    have hα : a.leadingCoeff ≠ 0 := by
      intro hz
      have : a = 0 := leadingCoeff_eq_zero.mp hz
      exact hn (this ▸ natDegree_zero)
    apply hc (-(b.leadingCoeff / a.leadingCoeff))
    have hneg : (-(b.leadingCoeff / a.leadingCoeff)) ^ p =
        -((b.leadingCoeff / a.leadingCoeff) ^ p) := by
      simpa [(Fact.out : p.Prime).ne_zero] using
        pow_sub (k := k) (p := p) (0 : k) (b.leadingCoeff / a.leadingCoeff)
    rw [hneg, div_pow, hlead, neg_div, neg_neg, mul_div_cancel_right₀ _ (pow_ne_zero _ hα)]
  refine ⟨ha, ?_⟩
  have hb := congrArg natDegree h
  rw [eq_C_of_natDegree_eq_zero ha, ← C_pow, ← C_mul, ← C_sub,
    natDegree_C, natDegree_pow] at hb
  exact (mul_eq_zero.mp hb).resolve_left (by omega)

private lemma coordinateMap_constant (hc : ∀ d : k, d ^ p ≠ c)
    (f : Coordinates k p c →ₐ[k] Polynomial k) :
    ∃ g : Coordinates k p c →ₐ[k] k, f = (Algebra.ofId k (Polynomial k)).comp g := by
  have hr := congrArg f (coordinate_relation (k := k) (p := p) (c := c))
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, AlgHom.commutes] at hr
  have h : f (y k p c) ^ p = f (x k p c) - C c * f (x k p c) ^ p := by
    change _ - _ + C c * _ = 0 at hr
    exact eq_sub_of_add_eq (sub_eq_zero.mp (by linear_combination hr))
  obtain ⟨hx, hy⟩ := polynomial_constant hc h
  refine ⟨(Polynomial.aeval (0 : k)).comp f, coordinate_ext ?_ ?_⟩
  · change f (x k p c) = C (Polynomial.aeval (0 : k) (f (x k p c)))
    rw [eq_C_of_natDegree_eq_zero hx, Polynomial.aeval_C, Algebra.algebraMap_self_apply]
  · change f (y k p c) = C (Polynomial.aeval (0 : k) (f (y k p c)))
    rw [eq_C_of_natDegree_eq_zero hy, Polynomial.aeval_C, Algebra.algebraMap_self_apply]

section Extension

variable {K : Type u} [Field K] [Algebra k K] (d : K) (hd : d ^ p = algebraMap k K c)

include hd in
private lemma split_relation :
    (X - C d * X ^ p : Polynomial K) ^ p - X ^ p +
      algebraMap k (Polynomial K) c * (X ^ p) ^ p = 0 := by
  rw [pow_sub (k := k) (p := p), mul_pow, ← C_pow, hd,
    IsScalarTower.algebraMap_apply k K (Polynomial K)]
  change _ - _ + C (algebraMap k K c) * _ = 0
  ring

private def splitForward : K ⊗[k] Coordinates k p c →ₐ[K] Polynomial K :=
  AlgHom.liftEquiv k K _ _ (coordinateMap (c := c) _ _ (split_relation d hd))

@[simp] private lemma splitForward_x :
    splitForward d hd (extendedX k p c K) = X ^ p := by
  simp [splitForward, extendedX]

@[simp] private lemma splitForward_y :
    splitForward d hd (extendedY k p c K) = X - C d * X ^ p := by
  simp [splitForward, extendedY]

private def splitBackward : Polynomial K →ₐ[K] K ⊗[k] Coordinates k p c :=
  Polynomial.aeval (extendedY k p c K + (d ⊗ₜ[k] (1 : Coordinates k p c)) * extendedX k p c K)

include hd in
private lemma splitParameter_pow :
    (extendedY k p c K + (d ⊗ₜ[k] (1 : Coordinates k p c)) * extendedX k p c K) ^ p = extendedX k p c K := by
  have hr := congrArg (Algebra.TensorProduct.includeRight (R := k) (A := K))
    (coordinate_relation (k := k) (p := p) (c := c))
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, AlgHom.commutes] at hr
  have ha := pow_add (k := k) (p := p) (extendedY k p c K)
    ((d ⊗ₜ[k] (1 : Coordinates k p c)) * extendedX k p c K)
  have hm := mul_pow (d ⊗ₜ[k] (1 : Coordinates k p c)) (extendedX k p c K) p
  rw [ha, hm, Algebra.TensorProduct.tmul_pow, one_pow, hd]
  let incl : Coordinates k p c →ₐ[k] K ⊗[k] Coordinates k p c := includeRight
  have hscalar : (algebraMap k K c) ⊗ₜ[k] (1 : Coordinates k p c) =
      incl (algebraMap k (Coordinates k p c) c) :=
    (Algebra.TensorProduct.algebraMap_apply (R := k) (S := k) (A := K)
      (B := Coordinates k p c) c).symm.trans
      (Algebra.TensorProduct.algebraMap_apply' (R := k) (A := K) (B := Coordinates k p c) c)
  rw [hscalar, incl.commutes]
  change incl (y k p c) ^ p + algebraMap k _ c * incl (x k p c) ^ p = incl (x k p c)
  apply sub_eq_zero.mp
  linear_combination hr

private def splitAlgebraEquiv : K ⊗[k] Coordinates k p c ≃ₐ[K] Polynomial K :=
  AlgEquiv.ofAlgHom (splitForward d hd) (splitBackward (p := p) (c := c) d)
    (Polynomial.algHom_ext <| by
      simp only [AlgHom.comp_apply, splitBackward, Polynomial.aeval_X,
        map_add, map_mul, splitForward_x, splitForward_y, AlgHom.id_apply]
      have hd' : splitForward d hd (d ⊗ₜ[k] (1 : Coordinates k p c)) = C d := by
        simp [splitForward, Algebra.smul_def]
      rw [hd']
      exact sub_add_cancel _ _)
    (by
      let b := splitBackward (p := p) (c := c) d
      have bx : b X = extendedY k p c K +
          (d ⊗ₜ[k] (1 : Coordinates k p c)) * extendedX k p c K := Polynomial.aeval_X _
      have bp : b (X ^ p) = extendedX k p c K := by
        have hpow := b.toRingHom.map_pow (X : Polynomial K) p
        change b (X ^ p) = b X ^ p at hpow
        rw [hpow, bx, splitParameter_pow d hd]
      refine Algebra.TensorProduct.ext_ring ?_
      refine coordinate_ext (k := k) (p := p) (c := c)
        (R := K ⊗[k] Coordinates k p c) ?_ ?_
      · change b (splitForward d hd (extendedX k p c K)) = extendedX k p c K
        rw [splitForward_x, bp]
      · change b (splitForward d hd (extendedY k p c K)) = extendedY k p c K
        rw [splitForward_y]
        change b.toRingHom (X - C d * X ^ p) = _
        rw [map_sub, map_mul]
        change b X - b (C d) * b (X ^ p) = _
        have hd' : b (C d) = (d ⊗ₜ[k] (1 : Coordinates k p c)) := b.commutes d
        rw [bx, bp, hd']
        exact add_sub_cancel_right _ _)

end Extension


private def planeOperations (k : Type u) [Field k] : HopfOperations k (Plane k) :=
  Classical.choose (StandardGroups.additivePowerSpecification k (PlaneIndex.{u}))

private lemma planeGenerators (i : PlaneIndex.{u}) :
    Primitive k (planeOperations k) (MvPolynomial.X i) := by
  obtain ⟨hΔ, hε, hS, _⟩ :=
    Classical.choose_spec (StandardGroups.additivePowerSpecification k (PlaneIndex.{u}))
  exact ⟨hΔ i, hε i, hS i⟩

local instance (priority := high) : HopfAlgebra k (Plane k) := (planeOperations k).hopf

local instance (priority := high) : Bialgebra k (Plane k) := (planeOperations k).hopf.toBialgebra

local instance (priority := high) : Coalgebra k (Plane k) :=
  (planeOperations k).hopf.toCoalgebra

local instance (priority := high) : CoalgebraStruct k (Plane k) :=
  (planeOperations k).hopf.toCoalgebra.toCoalgebraStruct

local notation "leftIncl" => (includeLeft : Plane k →ₐ[k] Plane k ⊗[k] Plane k)
local notation "rightIncl" => (includeRight : Plane k →ₐ[k] Plane k ⊗[k] Plane k)

private lemma generator_comul (i : PlaneIndex.{u}) :
    (planeOperations k).delta (MvPolynomial.X i) = leftIncl (MvPolynomial.X i) +
      rightIncl (MvPolynomial.X i) :=
  (planeGenerators i).1

private lemma equation_comul :
    (planeOperations k).delta (equation k p c) = leftIncl (equation k p c) +
      rightIncl (equation k p c) := by
  have hC : ∀ a : k, (planeOperations k).delta (MvPolynomial.C a) = algebraMap k _ a := (planeOperations k).delta.commutes
  have hL : ∀ a : k, (includeLeft : Plane k →ₐ[k] Plane k ⊗[k] Plane k)
      (MvPolynomial.C a) = algebraMap k _ a := includeLeft.commutes
  have hR : ∀ a : k, (includeRight : Plane k →ₐ[k] Plane k ⊗[k] Plane k)
      (MvPolynomial.C a) = algebraMap k _ a := includeRight.commutes
  simp only [equation, map_add, map_sub, map_mul, map_pow, hC, hL, hR, generator_comul,
    pow_add (k := k) (p := p)]
  ring

omit [CharP k p] in
private lemma equation_counit : (planeOperations k).epsilon (equation k p c) = 0 := by
  have hx := (planeGenerators (k := k) xIndex).2.1
  have hy := (planeGenerators (k := k) yIndex).2.1
  simp [equation, hx, hy, (Fact.out : p.Prime).ne_zero]

private lemma equation_antipode : (planeOperations k).inverse (equation k p c) = -equation k p c := by
  have hx := (planeGenerators (k := k) xIndex).2.2
  have hy := (planeGenerators (k := k) yIndex).2.2
  have hC : ∀ a : k, (planeOperations k).inverse (MvPolynomial.C a) = MvPolynomial.C a := (planeOperations k).inverse.commutes
  have hneg (z : Plane k) : (-z) ^ p = -z ^ p := by
    simpa [(Fact.out : p.Prime).ne_zero] using pow_sub (k := k) (p := p) 0 z
  simp only [equation, map_add, map_sub, map_mul, map_pow, hx, hy, hC, hneg]
  ring

omit [Fact p.Prime] [CharP k p] in
private lemma kills_equation {T : Type u} [CommRing T] [Algebra k T]
    (f : Plane k →ₐ[k] T) (hf : f (equation k p c) = 0) :
    ∀ a ∈ equationIdeal k p c, f a = 0 :=
  (Ideal.span_singleton_le_iff_mem (RingHom.ker f)).mpr hf

local instance equationIdeal_isHopf : (equationIdeal k p c).IsHopfIdeal k := by
  let q := Ideal.Quotient.mkₐ k (equationIdeal k p c)
  have hq : q (equation k p c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  refine { toIsCoideal := { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_ }
           antipode_mem := ?_ }
  · exact kills_equation (planeOperations k).epsilon (equation_counit)
  · change ∀ a ∈ equationIdeal k p c, ((map q q).comp (planeOperations k).delta) a = 0
    refine kills_equation (k := k) (p := p) (c := c)
      (T := Coordinates k p c ⊗[k] Coordinates k p c)
      ((Algebra.TensorProduct.map q q).comp (planeOperations k).delta) ?_
    rw [AlgHom.comp_apply, equation_comul, map_add]
    simp [includeLeft_apply, includeRight_apply, hq]
  · intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (q.comp (planeOperations k).inverse) a = 0
    refine kills_equation (q.comp (planeOperations k).inverse) ?_ a ha
    rw [AlgHom.comp_apply, equation_antipode, map_neg, hq, neg_zero]

section Geometry

local notation "A" => Coordinates k p c
local notation "fW" => (Spec.map (CommRingCat.ofHom (algebraMap k A)))

private theorem wound_smooth (d : AlgebraicClosure k)
    (hd : d ^ p = algebraMap k (AlgebraicClosure k) c) : Smooth fW := by
  let e := splitAlgebraEquiv d hd
  have : Algebra.Smooth (AlgebraicClosure k) (Polynomial (AlgebraicClosure k)) := by
    exact Algebra.Smooth.of_equiv (MvPolynomial.uniqueAlgEquiv (AlgebraicClosure k) (PUnit : Type u))
  letI : Algebra.Smooth (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A) :=
    Algebra.Smooth.of_equiv e.symm
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  change RingHom.Smooth (algebraMap k A)
  rw [RingHom.smooth_algebraMap]
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (AlgebraicClosure k)

private theorem wound_geometricallyConnected : GeometricallyConnected fW := by
  rw [GeometricallyConnected.eq_geometrically]
  apply (geometrically_iff_of_commRing (P := (ConnectedSpace ·))).mpr
  intro K _ _ Y f g h
  let L := AlgebraicClosure K
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let j := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hcomp : j ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [← Spec.map_comp]
    rfl
  have hpull := (IsPullback.of_hasPullback g j).paste_horiz h
  rw [hcomp] at hpull
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k L c) (Fact.out : p.Prime).pos
  let e := splitAlgebraEquiv (p := p) d hd
  let E : pullback g j ≅ Spec (CommRingCat.of (Polynomial L)) :=
    hpull.isoPullback ≪≫ pullbackSymmetry _ _ ≪≫ pullbackSpecIso k L A ≪≫
      Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op
  have : ConnectedSpace ↥(pullback g j) :=
    E.hom.homeomorph.connectedSpace_iff.mpr (inferInstanceAs (ConnectedSpace (PrimeSpectrum (Polynomial L))))
  exact (pullback.fst g j).surjective.connectedSpace (pullback.fst g j).continuous

omit [Fact p.Prime] [CharP k p] in
private lemma morphismFromLine (f : affineLine k ⟶ (testSpec k).obj (op (CommAlgCat.of k A))) :
    ∃ a : A →ₐ[k] Polynomial k, f = (testSpec k).map (CommAlgCat.ofHom a).op := by
  obtain ⟨a, ha⟩ := (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective f
  exact ⟨a.unop.hom, ha.symm⟩

private theorem wound_morphisms_constant (hc : ∀ d : k, d ^ p ≠ c)
    (f : affineLine k ⟶ (testSpec k).obj (op (CommAlgCat.of k A))) :
    ∃ q : (testSpec k).obj (op (CommAlgCat.of k k)) ⟶
        (testSpec k).obj (op (CommAlgCat.of k A)),
      f = (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k (Polynomial k))).op ≫ q := by
  obtain ⟨a, rfl⟩ := morphismFromLine f
  obtain ⟨g, rfl⟩ := coordinateMap_constant hc a
  refine ⟨(testSpec k).map (CommAlgCat.ofHom g).op, ?_⟩
  rw [← Functor.map_comp]
  rfl

private lemma wound_no_line_closedImmersion (hc : ∀ d : k, d ^ p ≠ c)
    (f : affineLine k ⟶ (testSpec k).obj (op (CommAlgCat.of k A))) :
    ¬ IsClosedImmersion f.left := by
  obtain ⟨a, rfl⟩ := morphismFromLine f
  intro hf
  let r := CommRingCat.ofHom a.toRingHom
  change IsClosedImmersion (Spec.map r) at hf
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map r)).2
  have he : (Scheme.ΓSpecIso _).inv ≫ (Spec.map r).appTop ≫ (Scheme.ΓSpecIso _).hom = r := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hs : Function.Surjective r := by
    rw [← he]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp
      (hsurj.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2)
  obtain ⟨g, rfl⟩ := coordinateMap_constant hc a
  obtain ⟨z, hz⟩ := hs X
  change C (g z) = X at hz
  have hdeg := congrArg natDegree hz
  simp at hdeg

end Geometry

section HopfSplitting

variable {K : Type u} [Field K] [Algebra k K]

local notation "WCoordinates" => Coordinates k p c
local notation "WExtended" => (K ⊗[k] WCoordinates)
local notation "q" => (Ideal.Quotient.mkₐ k (equationIdeal k p c))
local notation "tensorIncl" => (includeRight : WCoordinates →ₐ[k] WExtended)

private lemma extended_generator_comul (i : PlaneIndex.{u}) :
    comul (R := K) (tensorIncl (q (MvPolynomial.X i))) =
      tensorIncl (q (MvPolynomial.X i)) ⊗ₜ[K] 1 + 1 ⊗ₜ[K] tensorIncl (q (MvPolynomial.X i)) := by
  have hq : comul (R := k) (q (MvPolynomial.X i)) =
      q (MvPolynomial.X i) ⊗ₜ[k] 1 + 1 ⊗ₜ[k] q (MvPolynomial.X i) := by
    rw [show q (MvPolynomial.X i) = Ideal.Quotient.mk _ (MvPolynomial.X i) from rfl,
      Bialgebra.Quotient.comul_mk]
    change TensorProduct.map (q).toLinearMap (q).toLinearMap ((planeOperations k).delta (MvPolynomial.X i)) = _
    rw [(planeGenerators (k := k) i).1]
    simp
  have hh := DFunLike.congr_fun
    (Bialgebra.comul_includeRight (R := k) (A := K) (B := WCoordinates)) (q (MvPolynomial.X i))
  simp only [RingHom.comp_apply, RingHom.coe_coe, Bialgebra.comulAlgHom_apply] at hh
  rw [hq] at hh
  simp only [map_add, Algebra.TensorProduct.mapRingHom_tmul,
    RingHom.coe_coe, map_one] at hh
  exact hh

private lemma splitParameter_primitive (d : K) :
    Bialgebra.IsPrimitiveElem K
      (extendedY k p c K + (d ⊗ₜ[k] (1 : WCoordinates)) * extendedX k p c K) := by
  have hx : comul (R := K) (extendedX k p c K) =
      extendedX k p c K ⊗ₜ[K] 1 + 1 ⊗ₜ[K] extendedX k p c K :=
    extended_generator_comul xIndex
  have hy : comul (R := K) (extendedY k p c K) =
      extendedY k p c K ⊗ₜ[K] 1 + 1 ⊗ₜ[K] extendedY k p c K :=
    extended_generator_comul yIndex
  have hs : (d ⊗ₜ[k] (1 : WCoordinates)) * extendedX k p c K = d • extendedX k p c K :=
    (Algebra.smul_def d (extendedX k p c K)).symm
  rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul, hs, map_add, map_smul, hx, hy,
    smul_add, TensorProduct.tmul_add, TensorProduct.add_tmul, TensorProduct.smul_tmul',
    TensorProduct.tmul_smul]
  abel

open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups

set_option maxHeartbeats 1400000 in
private def splitBialgebraEquiv (d : K) (hd : d ^ p = algebraMap k K c)
    (l : HopfOperations K (Polynomial K))
    (hΔ : l.delta X = X ⊗ₜ[K] 1 + 1 ⊗ₜ[K] X) (hε : l.epsilon X = 0) :
    letI := l.hopf
    Polynomial K ≃ₐc[K] WExtended := by
  letI := l.hopf
  let e : WExtended ≃ₐ[K] Polynomial K := splitAlgebraEquiv d hd
  let t : WExtended := extendedY k p c K +
    (d ⊗ₜ[k] (1 : WCoordinates)) * extendedX k p c K
  have ht : Bialgebra.IsPrimitiveElem K t := splitParameter_primitive (k := k) (p := p) (c := c) d
  have heX : e.symm X = t := Polynomial.aeval_X _
  have hCounit :
      (Bialgebra.counitAlgHom K WExtended).comp e.symm.toAlgHom =
        Bialgebra.counitAlgHom K (Polynomial K) := by
    apply Polynomial.algHom_ext
    have hεX : Bialgebra.counitAlgHom K (Polynomial K) X = 0 := hε
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hεX, heX, Bialgebra.counitAlgHom_apply]
    exact ht.counit_eq_zero
  let g := Algebra.TensorProduct.map (R := K) (S := K) e.symm.toAlgHom e.symm.toAlgHom
  have hComul :
      g.comp (Bialgebra.comulAlgHom K (Polynomial K)) =
        (Bialgebra.comulAlgHom K WExtended).comp e.symm.toAlgHom := by
    apply Polynomial.algHom_ext
    have hΔX : Bialgebra.comulAlgHom K (Polynomial K) X = X ⊗ₜ[K] 1 + 1 ⊗ₜ[K] X := hΔ
    rw [AlgHom.comp_apply, hΔX, map_add]
    simp only [AlgHom.comp_apply, g, Algebra.TensorProduct.map_tmul, map_one,
      AlgEquiv.coe_toAlgHom, heX, Bialgebra.comulAlgHom_apply]
    exact (add_comm (t ⊗ₜ[K] (1 : WExtended)) (1 ⊗ₜ[K] t)).trans
      ht.comul_eq_tmul_add_tmul.symm
  exact BialgEquiv.ofAlgEquiv (R := K) (A := Polynomial K) (B := WExtended) e.symm hCounit hComul

set_option maxHeartbeats 1600000 in
private theorem wound_splits (d : K) (hd : d ^ p = algebraMap k K c) :
    Splits k (planeOperations k) (equationIdeal_isHopf (p := p) (c := c)) K d := by
  obtain ⟨l, hΔ, hε, hS, _⟩ := StandardGroups.additiveGroupSpecification K
  letI := l.hopf
  let E : extendedHopf K (CommHopfAlgCat.of k WCoordinates) ≅
      CommHopfAlgCat.of K (Polynomial K) :=
    CommHopfAlgCat.isoMk (splitBialgebraEquiv d hd l hΔ hε).symm
  refine ⟨l, ⟨hΔ, hε, hS⟩, E, splitForward_x d hd, splitForward_y d hd, ?_, ?_⟩
  · exact Polynomial.aeval_X _
  · exact ⟨(extendedGroupIso K (CommHopfAlgCat.of k WCoordinates)).symm ≪≫
      (hopfSpec (CommRingCat.of K)).mapIso E.symm.op⟩

end HopfSplitting

section Unipotence

open Specs.Unipotent
open private tmul_mem_tensorFiltration from LinearAlgebraicGroups.Unipotent.Criteria

omit [Fact p.Prime] [CharP k p] in
private theorem additive_hasInvariantVectors (l : HopfOperations k (Polynomial k))
    (hΔ : l.delta X = X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] X) :
    letI := l.hopf
    HasInvariantVectors (CommHopfAlgCat.of k (Polynomial k)) := by
  letI := l.hopf
  let P := CommHopfAlgCat.of k (Polynomial k)
  apply Unipotent.hasInvariantVectors_of_filtration (A := P)
  let F (n : ℕ) : Submodule k P :=
    Submodule.span k {a : P | ∃ i ≤ n, X ^ i = a}
  have hF : Monotone F := by
    intro m n hmn
    apply Submodule.span_mono
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨i, hi.trans hmn, rfl⟩
  have hX (n i : ℕ) (hi : i ≤ n) : (X : Polynomial k) ^ i ∈ F n :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · intro a
    refine ⟨a.natDegree, ?_⟩
    have hsum : (∑ i ∈ Finset.range (a.natDegree + 1), C (a.coeff i) * X ^ i) ∈ F a.natDegree := by
      apply Submodule.sum_mem
      intro i hi
      simpa only [Polynomial.smul_eq_C_mul] using Submodule.smul_mem _ (a.coeff i)
        (hX _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    rwa [← a.as_sum_range_C_mul_X_pow] at hsum
  · change Submodule.span k {a : P | ∃ i ≤ (0 : ℕ), X ^ i = a} = Submodule.span k {1}
    have hset : {a : P | ∃ i ≤ (0 : ℕ), X ^ i = a} = {1} := by
      ext a
      simp [eq_comm]
    rw [hset]
  · intro n a ha
    suffices h : F n ≤ Submodule.comap (comul (R := k) (A := P)) (tensorFiltration F n) from h ha
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change l.delta (X ^ i) ∈ tensorFiltration F n
    rw [map_pow, hΔ, _root_.add_pow]
    apply Submodule.sum_mem
    intro j hj
    simp only [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]
    rw [mul_comm, ← nsmul_eq_mul]
    have hj' := Finset.mem_range.mp hj
    exact nsmul_mem (tmul_mem_tensorFiltration (A := P) hF (by omega)
      (hX j j le_rfl) (hX (i - j) (i - j) le_rfl)) _

private theorem wound_unipotent (d : AlgebraicClosure k)
    (hd : d ^ p = algebraMap k (AlgebraicClosure k) c) :
    IsUnipotent (Specs.StandardGroups.spectrum k (Coordinates k p c)) := by
  let K := AlgebraicClosure k
  let W := Specs.StandardGroups.spectrum k (Coordinates k p c)
  apply (Unipotent.unipotenceFieldExtension (K := K) W).mp
  obtain ⟨l, hl, _, _, _, _, ⟨e⟩⟩ := wound_splits (p := p) d hd
  letI := l.hopf
  exact ⟨CommHopfAlgCat.of K (Polynomial K), ⟨e.symm⟩, additive_hasInvariantVectors l hl.1⟩

end Unipotence

theorem woundSubgroup : WoundSubgroup.{u} := by
  intro k _ p _ _ c hc
  let W := Specs.StandardGroups.spectrum k (Coordinates k p c)
  let I := equationIdeal k p c
  let A := CommHopfAlgCat.of k (Plane k)
  obtain ⟨d, hd⟩ :=
    IsAlgClosed.exists_pow_nat_eq (algebraMap k (AlgebraicClosure k) c) (Fact.out : p.Prime).pos
  refine ⟨planeOperations k, planeGenerators, equationIdeal_isHopf, ?_, wound_smooth d hd,
    wound_geometricallyConnected, wound_unipotent d hd, ?_, ?_,
    wound_morphisms_constant hc, ?_⟩
  · exact (hopfMapClosedImmersion k (hopfQuotientMap A I)).mpr Ideal.Quotient.mk_surjective
  · intro K _ _ a ha
    exact wound_splits a ha
  · let K := IntermediateField.adjoin k ({d} : Set (AlgebraicClosure k))
    let d' : K := ⟨d, IntermediateField.subset_adjoin k _ (Set.mem_singleton d)⟩
    refine ⟨d, hd, d', rfl, wound_splits d' ?_⟩
    exact K.subtype.injective hd
  · rintro H ⟨e⟩
    have := H.isClosedImmersion
    haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    exact wound_no_line_closedImmersion hc (e.hom ≫ H.inclusion.hom.hom)
      (IsClosedImmersion.comp e.hom.left H.inclusion.hom.hom.left)


end

end LinearAlgebraicGroups.WoundExample
