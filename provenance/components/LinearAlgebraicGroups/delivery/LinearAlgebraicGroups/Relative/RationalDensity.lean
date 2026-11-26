import Specs.LinearAlgebraicGroups.Relative.RationalDensity
import LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
import Specs.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import LinearAlgebraicGroups.Affine.SchemeImageQuotient
import LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
import LinearAlgebraicGroups.Reductive.TorusCentralizer
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Nakayama
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.HasGoingUp

import LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct Polynomial
open WithConv Coalgebra

universe u

namespace LinearAlgebraicGroups.Relative.RationalDensity

open _root_.LinearAlgebraicGroups.Specs
open _root_.LinearAlgebraicGroups.Specs.Relative.RationalDensity

noncomputable section

variable {k : Type u} [Field k]

/-- Tensoring a family of separating linear forms over a field preserves separation. -/
private theorem tensor_eq_zero_of_forall_lTensor {W V I : Type u}
    [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    (f : I → V →ₗ[k] k) (hf : ∀ v, (∀ i, f i v = 0) → v = 0)
    (x : W ⊗[k] V) (hx : ∀ i, (f i).lTensor W x = 0) : x = 0 := by
  classical
  let b := Module.Free.chooseBasis k W
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := V) b
  let e' := TensorProduct.equivFinsuppOfBasisLeft (N := k) b
  apply e.injective
  ext j
  rw [map_zero, Finsupp.zero_apply]
  apply hf
  intro i
  have hcoord (z : W ⊗[k] V) : f i (e z j) = e' ((f i).lTensor W z) j := by
    induction z using TensorProduct.inductionOn with
    | tmul a v => simp [e, e']
    | add x y h₁ h₂ => simp [h₁, h₂]
  rw [hcoord x, hx i, map_zero, Finsupp.zero_apply]

private theorem tensor_eq_zero_of_forall_liftBaseChange {K V I : Type u}
    [Field K] [Algebra k K] [AddCommGroup V] [Module k V]
    (f : I → V →ₗ[k] k) (hf : ∀ v, (∀ i, f i v = 0) → v = 0)
    (x : K ⊗[k] V)
    (hx : ∀ i, LinearMap.liftBaseChange K
      ((Algebra.linearMap k K).comp (f i)) x = 0) : x = 0 := by
  apply tensor_eq_zero_of_forall_lTensor f hf x
  intro i
  have hmap : (TensorProduct.rid k K).toLinearMap ∘ₗ (f i).lTensor K =
      (LinearMap.liftBaseChange K ((Algebra.linearMap k K).comp (f i))).restrictScalars k := by
    ext a v
    simp [Algebra.smul_def, mul_comm]
  apply (TensorProduct.rid k K).injective
  change ((TensorProduct.rid k K).toLinearMap ∘ₗ (f i).lTensor K) x = _
  rw [hmap, map_zero]
  exact hx i

/-- Over an infinite field a polynomial that vanishes on a nonempty principal
open of affine space vanishes identically. -/
private theorem polynomial_eq_zero_on_basicOpen [Infinite k] {ι : Type u}
    {p q : MvPolynomial ι k} (hq : q ≠ 0)
    (hp : ∀ x : ι → k, MvPolynomial.eval x q ≠ 0 → MvPolynomial.eval x p = 0) :
    p = 0 := by
  have h : p * q = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x q = 0
    · rw [hx, mul_zero]
    · rw [hp x hx, zero_mul]
  exact (mul_eq_zero.mp h).resolve_right hq

private theorem rationalPointOver_natural {K : Type u} [Field K] [Algebra k K]
    {X Y : SchemeOver k} (f : X ⟶ Y)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    rationalPointOver K (x ≫ f) =
      ((baseChange k K).map f).left (rationalPointOver K x) := by
  unfold rationalPointOver
  dsimp only
  change _ = (_ ≫ ((baseChange k K).map f).left) _
  apply congrArg (fun g : Spec (CommRingCat.of K) ⟶ ((baseChange k K).obj Y).left =>
    g (IsLocalRing.closedPoint K))
  apply pullback.hom_ext
  · simp [baseChange, Category.assoc]
  · simp [baseChange]

private theorem denseRationalPoints_of_dominant {X Y : SchemeOver k}
    (f : X ⟶ Y) (hf : IsDominant ((baseChange k (AlgebraicClosure k)).map f).left)
    (hX : GeometricallyDenseRationalPoints X) : GeometricallyDenseRationalPoints Y := by
  let F := baseChange k (AlgebraicClosure k)
  have h := hf.denseRange.dense_image ((F.map f).left.continuous) hX
  apply h.mono
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨x ≫ f, rationalPointOver_natural f x⟩

private theorem denseRationalPoints_of_iso {X Y : SchemeOver k} (e : X ≅ Y)
    (hX : GeometricallyDenseRationalPoints X) : GeometricallyDenseRationalPoints Y := by
  have : IsIso ((baseChange k (AlgebraicClosure k)).map e.hom).left := by
    change IsIso ((Over.forget _).map ((baseChange k (AlgebraicClosure k)).map e.hom))
    infer_instance
  exact denseRationalPoints_of_dominant e.hom inferInstance hX

variable (k)

private abbrev affineOver (A : Type u) [CommRing A] [Algebra k A] : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k A))

variable {k}

private def affineRationalSection {A : Type u} [CommRing A] [Algebra k A]
    (a : A →ₐ[k] k) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ affineOver k A :=
  Over.homMk (Spec.map (CommRingCat.ofHom a.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A)) = _
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (a.toRingHom.comp (algebraMap k A))) = 𝟙 _
    have h : a.toRingHom.comp (algebraMap k A) = RingHom.id k := by
      ext x
      exact a.commutes x
    rw [h, CommRingCat.ofHom_id]
    exact Scheme.Spec.map_id _)

private def affineBaseChangeIso (K A : Type u) [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] :
    Spec (CommRingCat.of (K ⊗[k] A)) ≅ ((baseChange k K).obj (affineOver k A)).left :=
  (pullbackSpecIso k K A).symm ≪≫ pullbackSymmetry (fieldSpecMap k K) (affineOver k A).hom

set_option backward.isDefEq.respectTransparency false in
private theorem affineBaseChangeIso_point {K A : Type u} [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] (a : A →ₐ[k] k) :
    (affineBaseChangeIso K A).hom
      (PrimeSpectrum.comap
        ((AlgHom.liftEquiv k K A K) ((IsScalarTower.toAlgHom k k K).comp a)).toRingHom
        (IsLocalRing.closedPoint K)) =
      rationalPointOver K (affineRationalSection a) := by
  let r := (AlgHom.liftEquiv k K A K) ((IsScalarTower.toAlgHom k k K).comp a)
  unfold rationalPointOver
  change (Spec.map (CommRingCat.ofHom r.toRingHom) ≫ (affineBaseChangeIso K A).hom)
    (IsLocalRing.closedPoint K) = _
  dsimp only
  apply congrArg (fun g : Spec (CommRingCat.of K) ⟶ _ => g (IsLocalRing.closedPoint K))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let h := fieldSpecMap k K
  have hfst : (affineBaseChangeIso K A).hom ≫ pullback.fst g h =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom) := by
    change ((pullbackSpecIso k K A).inv ≫ (pullbackSymmetry h g).hom) ≫
      pullback.fst g h = _
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd k K A
  have hsnd : (affineBaseChangeIso K A).hom ≫ pullback.snd g h =
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A))) := by
    change ((pullbackSpecIso k K A).inv ≫ (pullbackSymmetry h g).hom) ≫
      pullback.snd g h = _
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullbackSpecIso_inv_fst' k K A
  apply pullback.hom_ext (f := g) (g := h)
  · rw [Category.assoc, hfst]
    erw [pullback.lift_fst]
    change Spec.map (CommRingCat.ofHom r.toRingHom) ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ Spec.map (CommRingCat.ofHom a.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    simp [r]
  · rw [Category.assoc, hsnd]
    erw [pullback.lift_snd]
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (r.toRingHom.comp (algebraMap K (K ⊗[k] A)))) = _
    have h : r.toRingHom.comp (algebraMap K (K ⊗[k] A)) = RingHom.id K := by
      ext x
      exact r.commutes x
    rw [h, CommRingCat.ofHom_id]
    exact Scheme.Spec.map_id _

/-- If ground-field evaluations separate elements of the coordinate algebra,
they also separate geometric functions after base change. -/
private theorem affine_dense_eval {A I : Type u} [CommRing A] [Algebra k A]
    (a : I → A →ₐ[k] k) (hA : ∀ x : A, (∀ i, a i x = 0) → x = 0) :
    Dense (Set.range fun i => rationalPointOver (AlgebraicClosure k) (affineRationalSection (a i))) := by
  let K := AlgebraicClosure k
  let p (a : A →ₐ[k] k) : K ⊗[k] A →ₐ[K] K :=
    (AlgHom.liftEquiv k K A K) ((IsScalarTower.toAlgHom k k K).comp a)
  let t := Set.range fun i => PrimeSpectrum.comap (p (a i)).toRingHom (IsLocalRing.closedPoint K)
  have ht : Dense t := by
    rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    suffices PrimeSpectrum.vanishingIdeal t ≤ ⊥ from this.trans bot_le
    intro x hx
    rw [Ideal.mem_bot]
    apply tensor_eq_zero_of_forall_liftBaseChange (fun i => (a i).toLinearMap) hA
    intro i
    let a := a i
    have ha := (PrimeSpectrum.mem_vanishingIdeal _ _).mp hx _ (Set.mem_range_self i)
    have hz : p a x = 0 := by
      change p a x ∈ (IsLocalRing.closedPoint K : PrimeSpectrum K).asIdeal at ha
      simpa [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot] using ha
    have hp : (p a).toLinearMap = LinearMap.liftBaseChange K
        ((Algebra.linearMap k K).comp a.toLinearMap) := by
      apply (LinearMap.liftBaseChangeEquiv K).symm.injective
      ext b
      simp [p]
    exact (LinearMap.congr_fun hp x).symm.trans hz
  let e := (affineBaseChangeIso (k := k) K A).hom.homeomorph
  have h := e.surjective.denseRange.dense_image e.continuous ht
  apply h.mono
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨i, (affineBaseChangeIso_point (a i)).symm⟩

private theorem affine_denseRationalPoints {A : Type u} [CommRing A] [Algebra k A]
    (hA : ∀ x : A, (∀ a : A →ₐ[k] k, a x = 0) → x = 0) :
    GeometricallyDenseRationalPoints (affineOver k A) :=
  (affine_dense_eval (fun a : A →ₐ[k] k => a) hA).mono (by
    rintro _ ⟨a, rfl⟩
    exact ⟨affineRationalSection a, rfl⟩)

open CharacterDescent (StandardLattice)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)

private def latticeEvaluation {R : Type u} [CommRing R] {r : ℕ}
    (x : Fin r → Rˣ) : StandardLattice.{u} r →* Rˣ where
  toFun m := ∏ j, x j ^ (m j).down.toAdd
  map_one' := by simp
  map_mul' m n := by
    change (∏ j, x j ^ ((m j).down.toAdd + (n j).down.toAdd)) = _
    simp_rw [zpow_add, ← Finset.prod_mul_distrib]

private def laurentEvaluation {R : Type u} [CommRing R] [Algebra k R] {r : ℕ}
    (x : Fin r → Rˣ) : groupAlgebra k (StandardLattice.{u} r) →ₐ[k] R :=
  MonoidAlgebra.lift k R _ ((Units.coeHom R).comp (latticeEvaluation x))

private theorem laurentEvaluation_single {R : Type u} [CommRing R] [Algebra k R] {r : ℕ}
    (x : Fin r → Rˣ) (m : StandardLattice.{u} r) :
    laurentEvaluation (k := k) x (MonoidAlgebra.single m (1 : k)) = (latticeEvaluation x m : R) := by
  simp [laurentEvaluation, MonoidAlgebra.lift_single]

private theorem zpow_separates_units [Infinite k] (d : ℤ)
    (h : ∀ x : kˣ, x ^ d = 1) : d = 0 := by
  have hn (n : ℕ) (hnpos : n ≠ 0) (h' : ∀ x : kˣ, x ^ n = 1) : False := by
    let q : k[X] := Polynomial.X ^ n - 1
    have hq : q ≠ 0 := by
      intro he
      have hh := congrArg (fun f : k[X] => f.coeff n) he
      simp [q, Polynomial.coeff_X_pow, Polynomial.coeff_one, hnpos] at hh
    apply hq
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : k))).mono
    rintro t ⟨-, ht⟩
    have ht' : t ≠ 0 := fun ht' => ht (ht' ▸ rfl)
    have hp := congrArg (fun a : kˣ => (a : k)) (h' (Units.mk0 t ht'))
    simpa [Polynomial.IsRoot, q, sub_eq_zero] using hp
  cases d with
  | ofNat n =>
      by_contra hne
      exact hn n (fun hh => hne (by simp [hh])) (by simpa using h)
  | negSucc n =>
      exfalso
      refine hn (n + 1) (Nat.succ_ne_zero _) ?_
      intro x
      have hx := congrArg Inv.inv (h x)
      simpa [zpow_negSucc] using hx

private theorem splitTorus_coordinates_separated [Infinite k] (r : ℕ)
    (b : groupAlgebra k (StandardLattice.{u} r))
    (hb : ∀ x : Fin r → kˣ, laurentEvaluation (k := k) x b = 0) :
    b = 0 := by
  classical
  let M := StandardLattice.{u} r
  let P := Fin r → kˣ
  let χ (m : M) : P →* k :=
    (Units.coeHom k).comp
      { toFun := fun x => latticeEvaluation x m
        map_one' := by change (∏ _ : Fin r, (1 : kˣ) ^ _) = _; simp
        map_mul' := fun x y => by
          change (∏ j, (x j * y j) ^ (m j).down.toAdd) =
            (∏ j, x j ^ (m j).down.toAdd) * (∏ j, y j ^ (m j).down.toAdd)
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun j _ => mul_zpow (x j) (y j) _ }
  have hχ : Function.Injective χ := by
    intro m n hmn
    funext j
    apply ULift.ext
    apply Multiplicative.toAdd.injective
    apply sub_eq_zero.mp
    apply zpow_separates_units (k := k)
    intro t
    have he := congrArg (fun f : P →* k => f (Pi.mulSingle (M := fun _ : Fin r => kˣ) j t)) hmn
    have hprod (a : M) :
        latticeEvaluation (Pi.mulSingle (M := fun _ : Fin r => kˣ) j t) a = t ^ (a j).down.toAdd := by
      change (∏ i, (Pi.mulSingle (M := fun _ : Fin r => kˣ) j t i) ^ (a i).down.toAdd) = _
      rw [Finset.prod_eq_single j]
      · simp
      · intro i _ hi
        simp [Pi.mulSingle_eq_of_ne hi]
      · simp
    change (latticeEvaluation (Pi.mulSingle (M := fun _ : Fin r => kˣ) j t) m : k) =
      (latticeEvaluation (Pi.mulSingle (M := fun _ : Fin r => kˣ) j t) n : k) at he
    rw [hprod, hprod] at he
    rw [zpow_sub, Units.val_injective he, mul_inv_cancel]
  have hli := (linearIndependent_monoidHom P k).comp χ hχ
  apply MonoidAlgebra.coeff_injective
  change b.coeff = 0
  apply linearIndependent_iff.mp hli
  funext x
  simpa [Finsupp.linearCombination_apply, Finsupp.sum, χ, laurentEvaluation,
    MonoidAlgebra.lift_apply] using hb x

/-- An invertible linear change of coordinates underlies the geometric
decomposition of the Weil restriction over a finite Galois extension. -/
private theorem galConjugates_surjective {E I : Type u} [Field E] [Algebra k E]
    [Fintype I] (b : Module.Basis I k E) :
    Function.Surjective (fun (x : I → E) (σ : Gal(E/k)) => ∑ i, σ (b i) * x i) := by
  classical
  let : FiniteDimensional k E := Module.Finite.of_basis b
  let : Fintype Gal(E/k) := Fintype.ofFinite _
  let M : Matrix Gal(E/k) I E := fun σ i => σ (b i)
  have hlin : LinearIndependent E (fun σ : Gal(E/k) => σ.toAlgHom.toLinearMap) :=
    (linearIndependent_algHom_toLinearMap k E E).comp _ AlgEquiv.coe_toAlgHom_injective
  have hrows : LinearIndependent E M.row := by
    refine Fintype.linearIndependent_iff.mpr fun c hc σ => ?_
    refine Fintype.linearIndependent_iff.mp hlin c ?_ σ
    apply b.ext
    intro i
    have hci := congrFun hc i
    simpa [M, Matrix.row, Finset.sum_apply] using hci
  exact hrows.mulVec_surjective

/-- A polynomial over an extension field can be tested at ground-field points,
even with a nonzero denominator removed from the domain. -/
private theorem polynomial_eq_zero_on_ground_basicOpen {E I : Type u} [Field E] [Algebra k E]
    [Infinite k] {p q : MvPolynomial I E} (hq : q ≠ 0)
    (hp : ∀ x : I → k, MvPolynomial.eval (algebraMap k E ∘ x) q ≠ 0 →
      MvPolynomial.eval (algebraMap k E ∘ x) p = 0) : p = 0 := by
  classical
  have h : p * q = 0 := by
    apply MvPolynomial.funext_set (fun _ : I => Set.range (algebraMap k E))
      (fun _ => Set.infinite_range_of_injective (algebraMap k E).injective)
    intro x hx
    choose y hy using fun i => hx i (Set.mem_univ i)
    have he : algebraMap k E ∘ y = x := funext hy
    rw [← he, map_mul, map_zero]
    by_cases hq' : MvPolynomial.eval (algebraMap k E ∘ y) q = 0
    · rw [hq', mul_zero]
    · rw [hp y hq', zero_mul]
  exact (mul_eq_zero.mp h).resolve_right hq

private theorem localization_eq_zero_on_ground_basicOpen {E I : Type u}
    [Field E] [Algebra k E] [Infinite k] {q : MvPolynomial I E} (hq : q ≠ 0)
    (z : Localization.Away q)
    (hz : ∀ (x : I → k) (hx : MvPolynomial.eval (algebraMap k E ∘ x) q ≠ 0),
      (IsLocalization.Away.liftAlgHom q (f := MvPolynomial.aeval (algebraMap k E ∘ x))
        (isUnit_iff_ne_zero.mpr hx) :
        Localization.Away q →ₐ[E] E) z = 0) : z = 0 := by
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers q) z
  have hp : p = 0 := polynomial_eq_zero_on_ground_basicOpen (k := k) hq fun x hx => by
    let f : Localization.Away q →ₐ[E] E :=
      IsLocalization.Away.liftAlgHom q (f := MvPolynomial.aeval (algebraMap k E ∘ x))
        (isUnit_iff_ne_zero.mpr hx)
    have hh := congrArg f hs
    rw [map_mul, hz x hx, zero_mul] at hh
    exact (IsLocalization.Away.lift_eq q (isUnit_iff_ne_zero.mpr hx) p).symm.trans hh.symm
  rw [hp, map_zero] at hs
  exact (IsLocalization.map_units (Localization.Away q) s).mul_right_cancel
    (hs.trans (zero_mul _).symm)

section Norm

variable {E : Type u} [Field E] [Algebra k E]

private def coefficientConjugation (r : ℕ) (σ : Gal(E/k)) :
    groupAlgebra E (StandardLattice.{u} r) →ₐ[k] groupAlgebra E (StandardLattice.{u} r) :=
  MonoidAlgebra.mapAlgHom _ σ.toAlgHom

private theorem laurentEvaluation_natural {R S : Type u}
    [CommRing R] [Algebra E R] [CommRing S] [Algebra E S] {r : ℕ}
    (v : Fin r → Rˣ) (f : R →ₐ[E] S) :
    f.comp (laurentEvaluation v) = laurentEvaluation (fun j => Units.map f.toMonoidHom (v j)) := by
  apply (MonoidAlgebra.lift E S (StandardLattice.{u} r)).symm.injective
  apply DFunLike.ext
  intro m
  rw [MonoidAlgebra.lift_symm_apply, MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply,
    laurentEvaluation_single, laurentEvaluation_single]
  have h : Units.map f.toMonoidHom (latticeEvaluation v m) =
      latticeEvaluation (fun j => Units.map f.toMonoidHom (v j)) m := by
    change Units.map f.toMonoidHom (∏ j, v j ^ (m j).down.toAdd) =
      ∏ j, (Units.map f.toMonoidHom (v j)) ^ (m j).down.toAdd
    rw [map_prod]
    exact Finset.prod_congr rfl fun j _ => map_zpow (Units.map f.toMonoidHom) _ _
  exact congrArg Units.val h

private theorem laurentEvaluation_conjugation {r : ℕ}
    (σ : Gal(E/k)) (v : Fin r → Eˣ) (a : groupAlgebra E (StandardLattice.{u} r)) :
    laurentEvaluation (k := E) (fun j => Units.map σ.toMonoidHom (v j))
      (coefficientConjugation r σ a) = σ (laurentEvaluation (k := E) v a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add] at *
      rw [hx, hy]
  | single m c =>
      rw [show coefficientConjugation r σ (MonoidAlgebra.single m c) =
        MonoidAlgebra.single m (σ c) from MonoidAlgebra.mapAlgHom_single _ _ _]
      rw [show laurentEvaluation (k := E) v (MonoidAlgebra.single m c) =
        c * (latticeEvaluation v m : E) by
          rw [laurentEvaluation, MonoidAlgebra.lift_single]
          rfl]
      rw [show laurentEvaluation (k := E) (fun j => Units.map σ.toMonoidHom (v j))
          (MonoidAlgebra.single m (σ c)) =
          σ c * (latticeEvaluation (fun j => Units.map σ.toMonoidHom (v j)) m : E) by
            rw [laurentEvaluation, MonoidAlgebra.lift_single]
            rfl]
      rw [map_mul]
      congr 1
      have hv : latticeEvaluation (fun j => Units.map σ.toMonoidHom (v j)) m =
          Units.map σ.toMonoidHom (latticeEvaluation v m) := by
        change (∏ j, (Units.map σ.toMonoidHom (v j)) ^ (m j).down.toAdd) =
          Units.map σ.toMonoidHom (∏ j, v j ^ (m j).down.toAdd)
        rw [map_prod]
        exact Finset.prod_congr rfl fun j _ => (map_zpow (Units.map σ.toMonoidHom) _ _).symm
      exact congrArg Units.val hv

private theorem laurentEvaluation_identity {r : ℕ} :
    laurentEvaluation (k := E) (fun _ : Fin r => (1 : Eˣ)) =
      Bialgebra.counitAlgHom E (groupAlgebra E (StandardLattice.{u} r)) := by
  apply (MonoidAlgebra.lift E E (StandardLattice.{u} r)).symm.injective
  apply DFunLike.ext
  intro m
  rw [MonoidAlgebra.lift_symm_apply, MonoidAlgebra.lift_symm_apply, laurentEvaluation_single]
  change (↑(∏ j : Fin r, (1 : Eˣ) ^ (m j).down.toAdd) : E) = _
  simp [groupAlgebra]



private def convolutionPostcomp {A : HopfAlgebraCategory k} [IsCocomm k A]
    {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) : WithConv (A →ₐ[k] R) →* WithConv (A →ₐ[k] S) where
  toFun g := toConv (f.comp g.ofConv)
  map_one' := by
    apply WithConv.ofConv_injective
    ext a
    exact f.commutes (counit a)
  map_mul' g h := WithConv.ofConv_injective (AlgHom.comp_convMul_distrib f g h)

variable [FiniteDimensional k E] [IsGalois k E]

private theorem galoisNorm_is_rational (A : HopfAlgebraCategory k) [IsCocomm k A]
    [Fintype Gal(E/k)] (f : A →ₐ[k] E) :
    ∃ g : A →ₐ[k] k,
      (Algebra.ofId k E).comp g = (∏ σ : Gal(E/k), toConv (σ.toAlgHom.comp f)).ofConv := by
  let n := ∏ σ : Gal(E/k), toConv (σ.toAlgHom.comp f)
  have h (a : A) : n.ofConv a ∈ (Algebra.ofId k E).range := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed (n.ofConv a)).mpr
    intro τ
    have he : convolutionPostcomp (A := A) τ.toAlgHom n = n := by
      unfold n
      rw [map_prod]
      exact Equiv.prod_comp (Equiv.mulLeft τ) (fun σ : Gal(E/k) => toConv (σ.toAlgHom.comp f))
    exact congrArg (fun v : WithConv (A →ₐ[k] E) => v.ofConv a) he
  let e := AlgEquiv.ofInjective (Algebra.ofId k E) (algebraMap k E).injective
  refine ⟨e.symm.toAlgHom.comp (n.ofConv.codRestrict _ h), ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply ⟨n.ofConv a, h a⟩)

/-- The norm family of split torus points separates the original coordinates.
Its independent geometric parameters are the conjugates of a field basis. -/
private theorem torusCoordinatesSeparated [Infinite k]
    (A : HopfAlgebraCategory k) [IsCocomm k A] (r : ℕ)
    (e : groupAlgebra E (StandardLattice.{u} r) ≅ extendedHopf E A)
    (a : A) (ha : ∀ g : A →ₐ[k] k, g a = 0) : a = 0 := by
  classical
  let : Fintype Gal(E/k) := Fintype.ofFinite _
  let I := Module.Free.ChooseBasisIndex k E
  let b : Module.Basis I k E := Module.Free.chooseBasis k E
  let : Fintype I := Fintype.ofFinite _
  let L (σ : Gal(E/k)) (j : Fin r) : MvPolynomial (Fin r × I) E :=
    ∑ i, MvPolynomial.C (σ (b i)) * MvPolynomial.X (j, i)
  let q : MvPolynomial (Fin r × I) E := ∏ s : Gal(E/k) × Fin r, L s.1 s.2
  let P := Localization.Away q
  have hs (v : Gal(E/k) → Fin r → E) : ∃ x : Fin r × I → E,
      ∀ σ j, MvPolynomial.eval x (L σ j) = v σ j := by
    choose x hx using fun j : Fin r => galConjugates_surjective b (fun σ => v σ j)
    refine ⟨fun s => x s.1 s.2, fun σ j => ?_⟩
    simpa [L] using congrFun (hx j) σ
  obtain ⟨x, hx⟩ := hs (fun _ _ => 1)
  have hq : q ≠ 0 := by
    intro h
    have hh := congrArg (MvPolynomial.eval x) h
    simp [q, hx] at hh
  let u (σ : Gal(E/k)) (j : Fin r) : Pˣ :=
    (isUnit_of_dvd_unit
      (map_dvd (algebraMap (MvPolynomial (Fin r × I) E) P)
        (Finset.dvd_prod_of_mem (fun s : Gal(E/k) × Fin r => L s.1 s.2)
          (Finset.mem_univ (σ, j))))
      (IsLocalization.Away.algebraMap_isUnit q)).unit
  have hu (σ : Gal(E/k)) (j : Fin r) :
      (u σ j : P) = algebraMap (MvPolynomial (Fin r × I) E) P (L σ j) :=
    IsUnit.unit_spec _
  let i : A →ₐ[k] groupAlgebra E (StandardLattice.{u} r) :=
    (e.inv.hom.toAlgHom.restrictScalars k).comp Algebra.TensorProduct.includeRight
  let point (σ : Gal(E/k)) : WithConv (A →ₐ[k] P) :=
    toConv (((laurentEvaluation (k := E) (u σ)).restrictScalars k).comp
      ((coefficientConjugation r σ).comp i))
  let norm : WithConv (A →ₐ[k] P) := ∏ σ, point σ
  have hpoint (f : P →ₐ[E] E) (σ : Gal(E/k)) :
      convolutionPostcomp (A := A) (f.restrictScalars k) (point σ) =
        toConv (((laurentEvaluation (k := E)
          (fun j => Units.map f.toMonoidHom (u σ j))).restrictScalars k).comp
          ((coefficientConjugation r σ).comp i)) := by
    apply WithConv.ofConv_injective
    ext z
    change f (laurentEvaluation (u σ) (coefficientConjugation r σ (i z))) = _
    exact DFunLike.congr_fun (laurentEvaluation_natural (u σ) f) _
  have hnorm : norm.ofConv a = 0 := by
    apply localization_eq_zero_on_ground_basicOpen (k := k) hq
    intro w hw
    let f : P →ₐ[E] E := IsLocalization.Away.liftAlgHom q
      (f := MvPolynomial.aeval (algebraMap k E ∘ w)) (isUnit_iff_ne_zero.mpr hw)
    let v : Fin r → Eˣ := fun j => Units.map f.toMonoidHom (u 1 j)
    have hfu (σ : Gal(E/k)) (j : Fin r) :
        (Units.map f.toMonoidHom (u σ j) : E) =
          MvPolynomial.eval (algebraMap k E ∘ w) (L σ j) := by
      change f (u σ j) = _
      rw [hu]
      exact IsLocalization.Away.lift_eq q (isUnit_iff_ne_zero.mpr hw) _
    have hconj (σ : Gal(E/k)) (j : Fin r) :
        Units.map f.toMonoidHom (u σ j) = Units.map σ.toMonoidHom (v j) := by
      apply Units.ext
      change (Units.map f.toMonoidHom (u σ j) : E) =
        σ (Units.map f.toMonoidHom (u 1 j) : E)
      rw [hfu, hfu]
      simp [L, map_sum, map_mul, AlgEquiv.commutes]
    let g : A →ₐ[k] E := (laurentEvaluation (k := E) v).restrictScalars k |>.comp i
    have hmul (σ : Gal(E/k)) :
        convolutionPostcomp (A := A) (f.restrictScalars k) (point σ) =
          toConv (σ.toAlgHom.comp g) := by
      rw [hpoint]
      simp only [hconj]
      apply WithConv.ofConv_injective
      ext z
      exact laurentEvaluation_conjugation σ v (i z)
    obtain ⟨g₀, hg₀⟩ := galoisNorm_is_rational A g
    change ((convolutionPostcomp (A := A) (f.restrictScalars k) norm).ofConv a) = 0
    unfold norm
    rw [map_prod]
    simp_rw [hmul]
    rw [← hg₀]
    change algebraMap k E (g₀ a) = 0
    rw [ha, map_zero]
  have hone (σ : Gal(E/k)) :
      ((laurentEvaluation (k := E) (fun _ : Fin r => (1 : Eˣ))).restrictScalars k).comp
          ((coefficientConjugation r σ).comp i) =
        (1 : WithConv (A →ₐ[k] E)).ofConv := by
    ext z
    have h := laurentEvaluation_conjugation σ (fun _ : Fin r => (1 : Eˣ)) (i z)
    simp only [map_one] at h
    change laurentEvaluation (k := E) (fun _ : Fin r => (1 : Eˣ))
       (coefficientConjugation r σ (i z)) = algebraMap k E (counit (R := k) z)
    rw [h, laurentEvaluation_identity]
    change σ (counit (R := E) (e.inv.hom ((1 : E) ⊗ₜ[k] z))) = _
    have hc := CoalgHomClass.counit_comp_apply (R := E) e.inv.hom
      ((1 : E) ⊗ₜ[k] z)
    rw [hc]
    change σ (counit (R := E) (A := E ⊗[k] A) ((1 : E) ⊗ₜ[k] z)) = _
    simp [Algebra.smul_def]
  have hid : coefficientConjugation r (1 : Gal(E/k)) = AlgHom.id k _ := by
    exact MonoidAlgebra.mapAlgHom_id
  have hall (v : Fin r → Eˣ) : laurentEvaluation (k := E) v (i a) = 0 := by
    obtain ⟨w, hw⟩ := hs (fun σ j => if σ = 1 then v j else 1)
    have hqw : MvPolynomial.eval w q ≠ 0 := by
      rw [show MvPolynomial.eval w q = ∏ s : Gal(E/k) × Fin r,
          (if s.1 = 1 then (v s.2 : E) else 1) by simp [q, hw]]
      exact Finset.prod_ne_zero_iff.mpr fun s _ => by split <;> simp
    let f : P →ₐ[E] E := IsLocalization.Away.liftAlgHom q
      (f := MvPolynomial.aeval w) (isUnit_iff_ne_zero.mpr hqw)
    have hf (σ : Gal(E/k)) (j : Fin r) :
        Units.map f.toMonoidHom (u σ j) = if σ = 1 then v j else 1 := by
      apply Units.ext
      change f (u σ j) = _
      rw [hu]
      have he : f (algebraMap (MvPolynomial (Fin r × I) E) P (L σ j)) =
          MvPolynomial.eval w (L σ j) :=
        IsLocalization.Away.lift_eq q (isUnit_iff_ne_zero.mpr hqw) _
      rw [he, hw]
      split <;> rfl
    have hh := congrArg f hnorm
    change (convolutionPostcomp (A := A) (f.restrictScalars k) norm).ofConv a = f 0 at hh
    unfold norm at hh
    rw [map_prod, map_zero] at hh
    have hp : ∏ σ, convolutionPostcomp (A := A) (f.restrictScalars k) (point σ) =
        toConv (((laurentEvaluation (k := E) v).restrictScalars k).comp i) := by
      rw [Finset.prod_eq_single (1 : Gal(E/k))]
      · rw [hpoint]
        have hv : (fun j => Units.map f.toMonoidHom (u 1 j)) = v :=
          funext (fun j => by rw [hf, ite_eq_left rfl])
        rw [hv, hid, AlgHom.id_comp]
      · intro σ _ hσ
        rw [hpoint]
        have hv : (fun j => Units.map f.toMonoidHom (u σ j)) = (fun _ => 1) :=
          funext (fun j => by rw [hf, ite_eq_right hσ])
        rw [hv, hone, WithConv.toConv_ofConv]
      · simp
    rw [hp] at hh
    exact hh
  have hi : i a = 0 := by
    let : Infinite E := Infinite.of_injective (algebraMap k E) (algebraMap k E).injective
    exact splitTorus_coordinates_separated r _ hall
  have hi' : (1 : E) ⊗ₜ[k] a = 0 := by
    exact (CommHopfAlgCat.ofIso e).symm.injective
      (hi.trans (map_zero (CommHopfAlgCat.ofIso e).symm).symm)
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff k A (A := E) a).mp hi'

end Norm

open private groupLikeIso groupLikeSpanOfSplit groupAlgebraOfCharacters
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent

private theorem finiteGaloisSplitsTorus {A : HopfAlgebraCategory k}
    (h : Specs.CharacterDescent.IsTorus A) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : FiniteDimensional k E)
      (_ : IsGalois k E) (r : ℕ),
      Nonempty (groupAlgebra E (StandardLattice.{u} r) ≅ extendedHopf E A) := by
  let S := SeparableClosure k
  have hm := LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType A h
  obtain ⟨E, _, _, hE⟩ :=
    LinearAlgebraicGroups.CharacterDescent.finiteGaloisSplitting (K := S) A hm
  obtain ⟨r, ⟨c⟩⟩ :=
    (LinearAlgebraicGroups.CharacterDescent.torusAndSplitCriteria (K := S) A hm).1.mp h
  let a := MulEquiv.ofBijective
    (LinearAlgebraicGroups.CharacterDescent.baseChangeCharacterMap S (extendedHopf E A))
    (LinearAlgebraicGroups.CharacterDescent.baseChangeCharacterMap_bijective S
      (extendedHopf E A) hE)
  let b := groupLikeIso (LinearAlgebraicGroups.CharacterDescent.extendedHopfTower (K := E) S A)
  let e := (a.trans b).trans c
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, r, ⟨?_⟩⟩
  exact CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv E E e.symm) ≪≫
    groupAlgebraOfCharacters (extendedHopf E A) (groupLikeSpanOfSplit _ hE)


private theorem torusAlgHom_separates {A : HopfAlgebraCategory k} [Infinite k]
    (hA : Specs.CharacterDescent.IsTorus A)
    (a : A) (ha : ∀ f : A →ₐ[k] k, f a = 0) : a = 0 := by
  have hm := LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType A hA
  let : IsCocomm k A := (hopfSpecCommutativity k A).mp
    (LinearAlgebraicGroups.CharacterDescent.multiplicativeTypeProperties A hm).2
  obtain ⟨E, _, _, _, _, r, ⟨d⟩⟩ := finiteGaloisSplitsTorus hA
  exact torusCoordinatesSeparated A r d a ha

private theorem isTorus_spec_iff (A : HopfAlgebraCategory k) :
    Specs.GeometricRadicals.IsTorus (specGroup A) ↔ Specs.CharacterDescent.IsTorus A :=
  (LinearAlgebraicGroups.CharacterDescent.torusOnSchemes A).symm

private theorem isTorus_of_groupIso {T S : GroupScheme k} (e : T ≅ S)
    (hS : Specs.GeometricRadicals.IsTorus S) : Specs.GeometricRadicals.IsTorus T := by
  obtain ⟨E, _, _, hE, r, ⟨s⟩⟩ := hS
  exact ⟨E, inferInstance, inferInstance, hE, r, ⟨(groupBaseChange k E).mapIso e ≪≫ s⟩⟩

private theorem torus_rational_density : TorusRationalPointsDense.{u} := by
  intro k _ _ T hT
  let := affineHopfSpecEquivalence k
  let F := (affineHopfSpec k).asEquivalence
  let B : AffineGroupCategory k := ⟨T.val, T.property.1⟩
  let A : HopfAlgebraCategory k := (F.inverse.obj B).unop
  let e : specGroup A ≅ T.val := (affineGroupInclusion k).mapIso (F.counitIso.app B)
  apply denseRationalPoints_of_iso ((Grp.forget (SchemeOver k)).mapIso e)
  exact affine_denseRationalPoints
    (torusAlgHom_separates ((isTorus_spec_iff A).mp (isTorus_of_groupIso e hT)))

/-- Geometric density for rational points of tori, with the ordered premises
of the conditional draft. -/
theorem torusRationalPointsDense_conditional
    (_ : Specs.Relative.ReductiveLieCentralizers.ReductiveOfSymmetricRoots.{u})
    (_ : Specs.Relative.ReductiveLieCentralizers.SemisimpleLieCentralizerComponentReductive.{u}) :
    TorusRationalPointsDense.{u} := torus_rational_density

private theorem tensor_eq_zero_of_pairEvaluations {B I : Type u} [CommRing B] [Algebra k B]
    (f : I → B →ₐ[k] k) (hB : ∀ b : B, (∀ i, f i b = 0) → b = 0)
    (z : B ⊗[k] B) (hz : ∀ i j,
      TensorProduct.lid k k (TensorProduct.map (f i).toLinearMap (f j).toLinearMap z) = 0) :
    z = 0 := by
  apply tensor_eq_zero_of_forall_lTensor (fun i => (f i).toLinearMap) hB z
  intro j
  apply (TensorProduct.rid k B).injective
  rw [map_zero]
  apply hB
  intro i
  have he (t : B ⊗[k] B) :
      f i (TensorProduct.rid k B ((f j).toLinearMap.lTensor B t)) =
        TensorProduct.lid k k (TensorProduct.map (f i).toLinearMap (f j).toLinearMap t) := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [smul_eq_mul, mul_comm]
    | add x y hx hy => simp [hx, hy]
  rw [he, hz]

private abbrev CoordinatePoints (A : HopfAlgebraCategory k) :=
  (convolutionPoints A).obj (CommAlgCat.of k k)

/-- The functions vanishing on a subgroup of rational points. -/
private def evaluationIdeal {A : HopfAlgebraCategory k}
    (S : Subgroup (CoordinatePoints A)) : Ideal A :=
  ⨅ f : S, RingHom.ker f.val.ofConv.toRingHom

private theorem mem_evaluationIdeal {A : HopfAlgebraCategory k}
    (S : Subgroup (CoordinatePoints A)) (a : A) :
    a ∈ evaluationIdeal S ↔ ∀ f : S, f.val.ofConv a = 0 := by
  simp [evaluationIdeal, Submodule.mem_iInf, RingHom.mem_ker]

private def quotientEvaluation {A : HopfAlgebraCategory k}
    (S : Subgroup (CoordinatePoints A)) (f : S) : (A ⧸ evaluationIdeal S) →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ f.val.ofConv (fun x hx => (mem_evaluationIdeal S x).mp hx f)

private theorem quotientEvaluation_separates {A : HopfAlgebraCategory k}
    (S : Subgroup (CoordinatePoints A)) (b : A ⧸ evaluationIdeal S)
    (hb : ∀ f : S, quotientEvaluation S f b = 0) : b = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_evaluationIdeal S a).mpr hb)

private theorem evaluationIdeal_isHopf {A : HopfAlgebraCategory k}
    (S : Subgroup (CoordinatePoints A)) : (evaluationIdeal S).IsHopfIdeal k := by
  let I := evaluationIdeal S
  let q := Ideal.Quotient.mkₐ k I
  refine { toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_ }
  · intro a ha
    exact (mem_evaluationIdeal S a).mp ha ⟨1, S.one_mem⟩
  · intro a ha
    change TensorProduct.map q.toLinearMap q.toLinearMap (comul a) = 0
    apply tensor_eq_zero_of_pairEvaluations (quotientEvaluation S) (quotientEvaluation_separates S)
    intro f g
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    exact (mem_evaluationIdeal S a).mp ha (f * g)
  · intro a ha
    apply (mem_evaluationIdeal S _).mpr
    intro f
    exact (mem_evaluationIdeal S a).mp ha f⁻¹

private def rationalEvaluationIdeal (A : HopfAlgebraCategory k) : Ideal A :=
  evaluationIdeal (⊤ : Subgroup (CoordinatePoints A))

private theorem mem_rationalEvaluationIdeal (A : HopfAlgebraCategory k) (a : A) :
    a ∈ rationalEvaluationIdeal A ↔ ∀ f : A →ₐ[k] k, f a = 0 := by
  change a ∈ evaluationIdeal (⊤ : Subgroup (CoordinatePoints A)) ↔ _
  rw [mem_evaluationIdeal]
  exact ⟨fun h f => h ⟨toConv f, trivial⟩, fun h f => h f.val.ofConv⟩

private theorem rationalEvaluationIdeal_isHopf (A : HopfAlgebraCategory k) :
    (rationalEvaluationIdeal A).IsHopfIdeal k :=
  evaluationIdeal_isHopf ⊤

open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private liftHopfQuotient specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups

/-- Generation by tori over the ground field implies geometric rational
density, by applying generation to the closed subgroup cut out by the
functions vanishing at rational points. -/
theorem denseRationalPoints_of_generatedByTori [Infinite k] (G : AffineAlgebraicGroup k)
    (hG : GeneratedByRationalTori G) : GeometricallyDenseRationalPoints G.val.X := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  let I := rationalEvaluationIdeal A
  let : I.IsHopfIdeal k := rationalEvaluationIdeal_isHopf A
  let Q := hopfQuotientMap A I
  let j : specGroup (hopfQuotient A I) ⟶ G.val := specGroupMap Q ≫ e.hom
  have hj : IsClosedImmersion j.hom.hom.left := by
    have : IsClosedImmersion (specGroupMap Q).hom.hom.left :=
      (hopfMapClosedImmersion k Q).mpr Ideal.Quotient.mk_surjective
    have : IsIso e.hom.hom.hom.left := by
      change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map e.hom)
      infer_instance
    change IsClosedImmersion ((specGroupMap Q).hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  let H : ClosedSubgroup G.val := ⟨_, j, hj⟩
  have hH : IsIso j := hG H (by
    intro T hT
    obtain ⟨B, _, ⟨eT₀⟩⟩ := groupPresentation (Unipotent.closedSubgroupAlgebraicGroup T)
    let eT : specGroup B ≅ T.group := eT₀
    let F := hopfSpec.fullyFaithful (R := CommRingCat.of k)
    let f := F.preimage (eT.hom ≫ T.inclusion ≫ e.inv)
    let a : A ⟶ B := f.unop
    have ha : specGroupMap a = eT.hom ≫ T.inclusion ≫ e.inv := F.map_preimage _
    let b := liftHopfQuotient I a (fun x hx => by
      apply torusAlgHom_separates ((isTorus_spec_iff B).mp (isTorus_of_groupIso eT hT))
      intro g
      exact (mem_rationalEvaluationIdeal A x).mp hx (g.comp a.hom.toAlgHom))
    have hab : Q ≫ b = a := by
      apply CommHopfAlgCat.hom_ext
      ext x
      rfl
    refine ⟨eT.inv ≫ specGroupMap b, ?_⟩
    change (eT.inv ≫ specGroupMap b) ≫ (specGroupMap Q ≫ e.hom) = T.inclusion
    rw [Category.assoc, ← Category.assoc (specGroupMap b), ← specGroupMap_comp,
      hab, ha]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id])
  have hQ : IsIso Q := by
    have : IsIso (specGroupMap Q) := IsIso.of_isIso_comp_right (specGroupMap Q) e.hom
    let := (hopfSpec.fullyFaithful (R := CommRingCat.of k)).reflectsIsomorphisms
    have h : IsIso Q.op := isIso_of_reflects_iso Q.op (hopfSpec (CommRingCat.of k))
    exact (isIso_op_iff Q).mp h
  have hI : I = ⊥ := by
    have hinj := (ConcreteCategory.bijective_of_isIso Q).1
    apply bot_unique
    intro x hx
    rw [Ideal.mem_bot]
    exact hinj ((Ideal.Quotient.eq_zero_iff_mem.mpr hx).trans (map_zero Q.hom).symm)
  apply denseRationalPoints_of_iso ((Grp.forget (SchemeOver k)).mapIso e)
  apply affine_denseRationalPoints
  intro x hx
  exact Ideal.mem_bot.mp (hI ▸ (mem_rationalEvaluationIdeal A x).mpr hx)

open SemisimpleLieCentralizer
open LinearAlgebraicGroups.SemisimpleLieCentralizer (adjointNonnilpotentOpen)

/-- Rational vectors in the adjoint nonnilpotent locus span the whole Lie
algebra as soon as there is a geometric noncentral semisimple vector. -/
theorem span_adjointNonnilpotent [Infinite k] (G : AffineAlgebraicGroup k)
    (s : IdentityLieStructure G.val) (hG : HasGeometricNoncentralSemisimple G) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (_ : Module.Basis ι k (Lie k G.val)),
      Submodule.span k {x : Lie k G.val | ¬ IsNilpotent (LieAlgebra.ad k (Lie k G.val) x)} =
        ⊤ := by
  let := s.lieRing
  let := s.lieAlgebra
  intro ι _ _ b
  let V := Lie k G.val
  let W : Submodule k V :=
    Submodule.span k {x : V | ¬ IsNilpotent (LieAlgebra.ad k V x)}
  let M := genericMatrix (adjointMatrixFamily b)
  obtain ⟨_, hmem, hne⟩ := adjointNonnilpotentOpen k G s ι b
  obtain ⟨w, hw⟩ := (hne hG).2 inferInstance
  change ¬ Set.range ((M.charpoly - Polynomial.X ^ Fintype.card ι).coeff) ⊆
    ((evaluationPoint (k := k) k (b.equivFun w)).asIdeal : Set (MvPolynomial ι k)) at hw
  obtain ⟨q, ⟨n, rfl⟩, hn⟩ := Set.not_subset.mp hw
  let q := (M.charpoly - Polynomial.X ^ Fintype.card ι).coeff n
  have hq : q ≠ 0 := by
    intro he
    apply hn
    change q ∈ _
    rw [he]
    exact Ideal.zero_mem _
  apply top_unique
  intro x _
  by_contra hx
  have hxq : (Submodule.Quotient.mk x : V ⧸ W) ≠ 0 :=
    fun h => hx ((Submodule.Quotient.mk_eq_zero W).mp h)
  obtain ⟨d, hd⟩ := Module.Projective.exists_dual_ne_zero k hxq
  let f : V →ₗ[k] k := d.comp W.mkQ
  let p : MvPolynomial ι k := ∑ i, MvPolynomial.C (f (b i)) * MvPolynomial.X i
  have hp (v : ι → k) : MvPolynomial.eval v p = f (b.equivFun.symm v) := by
    rw [Module.Basis.equivFun_symm_apply]
    simp [p, smul_eq_mul, mul_comm]
  have hzero : p = 0 := polynomial_eq_zero_on_basicOpen hq fun v hv => by
    have he : evaluationPoint k (b.equivFun (b.equivFun.symm v)) ∈ charpolyOpen M := by
      rw [LinearEquiv.apply_symm_apply]
      intro hz
      have hqv := hz (Set.mem_range_self n)
      exact hv (by simpa [q, evaluationPoint, MvPolynomial.aeval_eq_eval] using hqv)
    have hn := (hmem (b.equivFun.symm v)).mp he
    have hw' : b.equivFun.symm v ∈ W := Submodule.subset_span hn
    rw [hp]
    change d (Submodule.Quotient.mk (b.equivFun.symm v)) = 0
    rw [(Submodule.Quotient.mk_eq_zero W).mpr hw', map_zero]
  apply hd
  have hpx := hp (b.equivFun x)
  rw [hzero, map_zero, LinearEquiv.symm_apply_apply] at hpx
  exact hpx.symm

private theorem dualReduction_surjective_on_spectra :
    Function.Surjective ((testSpec k).map (dualReduction k).op).left := by
  let r := (TrivSqZeroExt.fstHom k k k).toRingHom
  change Function.Surjective (PrimeSpectrum.comap r)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)]
  apply (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr
  intro x hx
  have hx' : x = TrivSqZeroExt.inr x.snd :=
    (TrivSqZeroExt.mem_kerIdeal_iff_inr k k x).mp hx
  apply mem_nilradical.mpr
  exact ⟨2, by rw [pow_two, hx', TrivSqZeroExt.inr_mul_inr]⟩

/-- An open immersion of group schemes induces a surjection on identity
tangents because dual numbers have the same support as their reduction. -/
private theorem mapPointKernel_surjective_of_openImmersion {C H : GroupScheme k}
    (i : H ⟶ C) [IsOpenImmersion i.hom.hom.left] :
    Function.Surjective (mapPointKernel i) := by
  intro x
  let D := CommAlgCat.of k (DualNumber k)
  let R := CommAlgCat.of k k
  let d := (testSpec k).map (dualReduction k).op
  let p : Points C.X D := x.toMul.val
  let oneC : Points C.X R := (1 : ((groupPointsFunctor k).obj C).obj R)
  let oneH : Points H.X R := (1 : ((groupPointsFunctor k).obj H).obj R)
  have hp : d ≫ p = oneC := x.toMul.property
  have hrange : Set.range p.left ⊆ Set.range i.hom.hom.left := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := dualReduction_surjective_on_spectra (k := k) z
    have ho : oneH ≫ i.hom.hom = oneC :=
      map_one (((groupPointsFunctor k).map i).app R).hom
    refine ⟨oneH.left y, ?_⟩
    exact congrArg (fun z : Points C.X R => z.left y) (ho.trans hp.symm)
  let ql := IsOpenImmersion.lift i.hom.hom.left p.left hrange
  have hql := IsOpenImmersion.lift_fac i.hom.hom.left p.left hrange
  let q : Points H.X D := Over.homMk ql (by
    rw [← Over.w i.hom.hom, ← Category.assoc, hql, Over.w p])
  have hq : q ≫ i.hom.hom = p := Over.OverMorphism.ext hql
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hq0 : d ≫ q = oneH := by
    apply (cancel_mono i.hom.hom).mp
    rw [Category.assoc, hq, hp]
    exact (map_one (((groupPointsFunctor k).map i).app R).hom).symm
  exact ⟨⟨q, hq0⟩, Subtype.ext hq⟩

open SchemeDerivedGroup (IsSubgroupOf)
open Specs.GeometricRadicals (IsReductive)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.SemisimpleLieCentralizer
  (rationalSemisimpleWitness schemeCentralizerOfSemisimple)
open _root_.LinearAlgebraicGroups.Specs.Relative.ReductiveLieCentralizers
  (SemisimpleLieCentralizerComponentReductive IsMatrixCentralizer)
open private isMonHom_of_comp_closed from LinearAlgebraicGroups.Affine.SchemeImageQuotient

private theorem subgroupOf_of_testPoints {G : AffineAlgebraicGroup k}
    (H N : ClosedSubgroup G.val)
    (h : ∀ (R : TestAlgebra k) (p : Points H.group.X R),
      ∃ q : Points N.group.X R, q ≫ N.inclusion.hom.hom = p ≫ H.inclusion.hom.hom) :
    IsSubgroupOf H N := by
  obtain ⟨A, _, ⟨e₀⟩⟩ := groupPresentation (closedSubgroupAlgebraicGroup H)
  let e : specGroup A ≅ H.group := e₀
  let R := CommAlgCat.of k A
  obtain ⟨q, hq⟩ := h R e.hom.hom.hom
  let q' : (specGroup A).X ⟶ N.group.X := q
  have hq' : q' ≫ N.inclusion.hom.hom = e.hom.hom.hom ≫ H.inclusion.hom.hom := hq
  let f : H.group.X ⟶ N.group.X := e.inv.hom.hom ≫ q'
  have hf : f ≫ N.inclusion.hom.hom = H.inclusion.hom.hom := by
    dsimp only [f]
    rw [Category.assoc, hq', ← Category.assoc]
    have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.group.X :=
      ((Grp.forget (SchemeOver k)).mapIso e).inv_hom_id
    rw [he, Category.id_comp]
  let : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  let : IsMonHom f := isMonHom_of_comp_closed f H.inclusion N.inclusion hf
  exact ⟨Grp.homMk f, Grp.hom_ext _ _ hf⟩

private theorem lie_eq_zero_swap {V : Type u} [LieRing V] {x y : V}
    (h : ⁅x, y⁆ = 0) : ⁅y, x⁆ = 0 :=
  neg_eq_zero.mp ((lie_skew x y).trans h)

set_option maxHeartbeats 700000 in
/-- A rational vector in the adjoint open lies in the Lie algebra of a proper
reductive centralizer component. The displayed hypotheses give the faithful
matrix and Hopf presentations used for the rational Jordan construction. -/
theorem exists_reductiveSubgroup_of_adjointNonnilpotent
    (hComponent : SemisimpleLieCentralizerComponentReductive.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (L : AffineGroupCategory k)
    (s : IdentityLieStructure G.val)
    (A : HopfAlgebraCategory k) [Algebra.Smooth k A]
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L.val) (hf : IsClosedImmersion f.hom.hom.left) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ x : Lie k G.val, ¬ IsNilpotent (LieAlgebra.ad k (Lie k G.val) x) →
      ∃ H : ClosedSubgroup G.val,
        IsReductive (closedSubgroupAlgebraicGroup H) ∧
        LinearAlgebraicGroups.CocharacterDynamics.lieImage H x ∧
        ¬ Function.Surjective (mapPointKernel H.inclusion) := by
  let := s.lieRing
  let := s.lieAlgebra
  intro x hx
  let V := Specs.Lie k G.val
  let : AddCommGroup V := s.lieRing.toAddCommGroup
  let z₀ : V := (0 : PointKernel G.val)
  let : Zero V := s.lieRing.toAddCommGroup.toZero
  have hzero : (0 : V) = z₀ :=
    congrArg (fun a : AddGroup (PointKernel G.val) => a.toZero.zero) s.group_law
  obtain ⟨y, hy, hxy, hn, _, _, _⟩ :=
    rationalSemisimpleWitness k G L s A e ι l f hf x hx
  let Y := InfinitesimalCommutator.matrixDifferential f l y
  obtain ⟨C, _, hC, hLie, _⟩ := schemeCentralizerOfSemisimple k G L s hG.1 ι l f hf y hy
  obtain ⟨D, hD, _, H, _, hOpen, hRed⟩ := hComponent k G hG ι L l f hf y hy
  have hRep : IsMatrixCentralizer l f Y C := hC
  have hCD : IsSubgroupOf C D := subgroupOf_of_testPoints C D fun R p =>
    (hD R (p ≫ C.inclusion.hom.hom)).mpr
      ((hRep R (p ≫ C.inclusion.hom.hom)).mp ⟨p, rfl⟩)
  have hDC : IsSubgroupOf D C := subgroupOf_of_testPoints D C fun R p =>
    (hRep R (p ≫ D.inclusion.hom.hom)).mpr
      ((hD R (p ≫ D.inclusion.hom.hom)).mp ⟨p, rfl⟩)
  obtain ⟨i, hi⟩ := hCD
  obtain ⟨j, hj⟩ := hDC
  let B := GeometricBorelConjugacy.subgroupOfSubgroup D H
  refine ⟨B, hRed, ?_, ?_⟩
  · have hcomm : LieAlgebra.ad k V y x = z₀ := by
      rw [← hzero]
      change ⁅y, x⁆ = (0 : V)
      exact @lie_eq_zero_swap V s.lieRing x y (hxy.trans hzero.symm)
    obtain ⟨z, hz⟩ := (hLie x).mpr hcomm
    let : IsOpenImmersion H.inclusion.hom.hom.left := hOpen
    obtain ⟨w, hw⟩ := mapPointKernel_surjective_of_openImmersion H.inclusion (mapPointKernel i z)
    refine ⟨w, ?_⟩
    change mapPointKernel (H.inclusion ≫ D.inclusion) w = x
    rw [(lieFunctoriality k).2.2, hw, ← (lieFunctoriality k).2.2, hi, hz]
  · intro hsur
    apply hn
    apply LinearMap.ext
    intro v
    rw [LinearMap.zero_apply]
    obtain ⟨w, hw⟩ := hsur v
    change LieAlgebra.ad k V y v = (0 : V)
    rw [hzero]
    apply (hLie v).mp
    let w' : Lie k H.group := w
    refine ⟨mapPointKernel j (mapPointKernel H.inclusion w'), ?_⟩
    calc
      _ = mapPointKernel (j ≫ C.inclusion) (mapPointKernel H.inclusion w') :=
        ((lieFunctoriality k).2.2 _ _ _ _ _ _).symm
      _ = mapPointKernel D.inclusion (mapPointKernel H.inclusion w') := by rw [hj]
      _ = mapPointKernel (H.inclusion ≫ D.inclusion) w' :=
        ((lieFunctoriality k).2.2 _ _ _ _ _ _).symm
      _ = v := hw

open Specs.CentralFrobeniusDescent (CentralFrobeniusReduction IsCentral IsAdjointWeight
  IsCharacterPower LiftsTori)
open Specs.GeometricRadicals (GeometricGroup IsMaximalTorus)
open CharacterDescent (Character)

/-- The Frobenius quotients terminate when following any nontrivial weight
with bounded divisibility. This allows the induction on dimension to be kept
separate from the induction on divisibility. -/
theorem centralFrobenius_induction [Infinite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hF : CentralFrobeniusReduction.{u}) (P : AffineAlgebraicGroup k → Prop)
    (terminal : ∀ (G : AffineAlgebraicGroup k), IsReductive G →
      ∀ T : ClosedSubgroup (GeometricGroup G).val, IsMaximalTorus T →
      (IsCentral T.inclusion ∨ HasGeometricNoncentralSemisimple G) → P G)
    (step : ∀ (G Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsReductive G → IsReductive Q → IsFinite q.hom.hom.left →
      Surjective q.hom.hom.left → LiftsTori q → P Q → P G) :
    ∀ (n : ℕ) (G : AffineAlgebraicGroup k), IsReductive G →
      ∀ T : ClosedSubgroup (GeometricGroup G).val, IsMaximalTorus T →
      ∀ χ : Character T.group, χ ≠ 1 → IsAdjointWeight T.inclusion χ →
      ¬ IsCharacterPower (p ^ n) χ → P G := by
  intro n
  induction n with
  | zero =>
    intro G hG T hT χ hχ hw hbound
    exact False.elim (hbound ⟨χ, by simp⟩)
  | succ n ih =>
    intro G hG T hT χ hχ hw hbound
    by_cases hc : IsCentral T.inclusion
    · exact terminal G hG T hT (.inl hc)
    by_cases hs : HasGeometricNoncentralSemisimple G
    · exact terminal G hG T hT (.inr hs)
    have : GeometricallyConnected G.val.X.hom := hG.2.1
    have hconn : ConnectedSpace G.val.X.left :=
      GeometricallyConnected.connectedSpace_of_subsingleton (f := G.val.X.hom)
    obtain ⟨_, hpow, E, Q, q, _, _, _, hq, hfin, _, _, hlift, hred,
      T₁, f, hT₁, _, _, _, hw₁⟩ := hF k p G hG.1 hconn T hT hc hs
    obtain ⟨ψ, hψ⟩ := (hw₁.2.1 χ).mpr (hpow χ hχ hw)
    have hψ₀ : ψ ≠ 1 := by
      intro h
      apply hχ
      rw [← hψ, h]
      apply Grp.hom_ext
      exact MonObj.comp_one f.hom.hom
    have hψw := (hw₁.2.2.1 ψ hψ₀).mpr (hψ ▸ hw)
    have hψbound : ¬ IsCharacterPower (p ^ n) ψ := fun h =>
      hbound (hψ ▸ (hw₁.2.2.2 ψ hψ₀ hψw n).mpr h)
    exact step G Q q hG (hred hG) hfin hq.2.2.1 hlift
      (ih Q (hred hG) T₁ hT₁ ψ hψ₀ hψw hψbound)

private def characterPrecomp {T S : GroupScheme k} (f : T ⟶ S) :
    Character S →* Character T where
  toFun χ := f ≫ χ
  map_one' := by
    apply Grp.hom_ext
    exact MonObj.comp_one f.hom.hom
  map_mul' χ ψ := by
    apply Grp.hom_ext
    exact MonObj.comp_mul f.hom.hom χ.hom.hom ψ.hom.hom

open LinearAlgebraicGroups.CharacterDescent (groupLikeCharacterEquiv baseChangeCharacterMap
  baseChangeCharacterMap_injective monomialCharacterEquiv)

private theorem characterLatticeEmbedding (G : AffineAlgebraicGroup k)
    (hG : Specs.GeometricRadicals.IsTorus G.val) :
    ∃ (r : ℕ) (f : Character G.val →* StandardLattice.{u} r), Function.Injective f := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  have hT := (isTorus_spec_iff A).mp (isTorus_of_groupIso e hG)
  obtain ⟨E, _, _, _, _, r, ⟨d⟩⟩ := finiteGaloisSplitsTorus hT
  let F := (monomialCharacterEquiv (M := StandardLattice.{u} r) E).symm.toMonoidHom.comp
    ((groupLikeIso d).symm.toMonoidHom.comp ((baseChangeCharacterMap E A).comp
      ((groupLikeCharacterEquiv A).symm.toMonoidHom.comp (characterPrecomp e.hom))))
  refine ⟨r, F, (monomialCharacterEquiv (M := StandardLattice.{u} r) E).symm.injective.comp
    ((groupLikeIso d).symm.injective.comp ((baseChangeCharacterMap_injective E A).comp
      ((groupLikeCharacterEquiv A).symm.injective.comp ?_)))⟩
  intro a b h
  exact (cancel_epi e.hom).mp h

/-- In a torus character lattice a nontrivial character has bounded
divisibility by powers of any integer greater than one. -/
theorem characterPowerBound (T : AffineAlgebraicGroup k)
    (hT : Specs.GeometricRadicals.IsTorus T.val) (p : ℕ) (hp : 1 < p)
    (χ : Character T.val) (hχ : χ ≠ 1) :
    ∃ n : ℕ, ¬ IsCharacterPower (p ^ n) χ := by
  obtain ⟨r, f, hf⟩ := characterLatticeEmbedding T hT
  have hχ' : f χ ≠ 1 := fun h => hχ (hf (h.trans (map_one f).symm))
  have hex : ∃ j : Fin r, ((f χ) j).down.toAdd ≠ 0 := by
    by_contra! h
    apply hχ'
    funext j
    apply ULift.ext
    apply Multiplicative.toAdd.injective
    exact h j
  obtain ⟨j, hj⟩ := hex
  let z := ((f χ) j).down.toAdd
  let n := z.natAbs
  have hn : z.natAbs < p ^ n := Nat.lt_pow_self hp
  refine ⟨n, ?_⟩
  rintro ⟨ψ, he⟩
  have hpow := congrArg (fun a : Character T.val => ((f a) j).down.toAdd) he
  change ((f (ψ ^ (p ^ n))) j).down.toAdd = z at hpow
  rw [map_pow] at hpow
  have hmul : ((p ^ n : ℕ) : ℤ) * ((f ψ) j).down.toAdd = z := hpow
  have hdiv : ((p ^ n : ℕ) : ℤ) ∣ z := ⟨_, hmul.symm⟩
  exact (not_le_of_gt hn) (by simpa using Int.natAbs_le_of_dvd_ne_zero hdiv hj)

/-- Reduce the positive-characteristic case to the two terminal cases and
to transport of the assertion across a finite quotient that lifts tori. -/
theorem centralFrobenius_of_terminal [Infinite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hF : CentralFrobeniusReduction.{u}) (P : AffineAlgebraicGroup k → Prop)
    (terminal : ∀ (G : AffineAlgebraicGroup k), IsReductive G →
      ∀ T : ClosedSubgroup (GeometricGroup G).val, IsMaximalTorus T →
      (IsCentral T.inclusion ∨ HasGeometricNoncentralSemisimple G) → P G)
    (step : ∀ (G Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsReductive G → IsReductive Q → IsFinite q.hom.hom.left →
      Surjective q.hom.hom.left → LiftsTori q → P Q → P G)
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup (GeometricGroup G).val) (hT : IsMaximalTorus T) : P G := by
  by_cases hc : IsCentral T.inclusion
  · exact terminal G hG T hT (.inl hc)
  by_cases hs : HasGeometricNoncentralSemisimple G
  · exact terminal G hG T hT (.inr hs)
  have : GeometricallyConnected G.val.X.hom := hG.2.1
  have hconn : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := G.val.X.hom)
  obtain ⟨⟨χ, hχ, hw⟩, _⟩ := hF k p G hG.1 hconn T hT hc hs
  obtain ⟨n, hn⟩ := characterPowerBound (closedSubgroupAlgebraicGroup T) hT.1 p
    (Fact.out : p.Prime).one_lt χ hχ
  exact centralFrobenius_induction p hF P terminal step n G hG T hT χ hχ hw hn

private theorem mono_of_closedSubgroup {G : GroupScheme k} (H : ClosedSubgroup G) :
    Mono H.inclusion := by
  let : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  let : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  exact Functor.mono_of_mono_map (Grp.forget (SchemeOver k))
    (by
      change Mono H.inclusion.hom.hom
      infer_instance)

private theorem isIso_of_subgroup_section {G : GroupScheme k} (H : ClosedSubgroup G)
    (i : G ⟶ H.group) (hi : i ≫ H.inclusion = 𝟙 G) : IsIso H.inclusion := by
  let : Mono H.inclusion := mono_of_closedSubgroup H
  refine ⟨i, ?_, hi⟩
  apply (cancel_mono H.inclusion).mp
  rw [Category.assoc, hi, Category.comp_id, Category.id_comp]

/-- A torus is itself one of the subgroups used in either generation predicate. -/
theorem torus_generatedByRationalTori (G : AffineAlgebraicGroup k)
    (hG : Specs.GeometricRadicals.IsTorus G.val) :
    GeneratedByRationalTori G ∧ GeometricallyGeneratedByRationalTori G := by
  let T : ClosedSubgroup G.val := ⟨G.val, 𝟙 _, by
    change IsClosedImmersion (𝟙 G.val.X.left)
    infer_instance⟩
  constructor
  · intro H hH
    obtain ⟨i, hi⟩ := hH T hG
    exact isIso_of_subgroup_section H i hi
  · intro H hH
    obtain ⟨i, hi⟩ := hH T hG
    let i' : (GeometricGroup G).val ⟶ H.group := i
    have hi' : i' ≫ H.inclusion = (groupBaseChange k (AlgebraicClosure k)).map (𝟙 G.val) := hi
    exact isIso_of_subgroup_section H i' (hi'.trans ((groupBaseChange k _).map_id G.val))

attribute [local instance 100] LieRing.ofAssociativeRing

open private faithfulLieHom faithfulLieHom_injective
  from LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer

set_option maxHeartbeats 700000 in
/-- In the noncentral semisimple case the Lie algebras of proper reductive
subgroups span the entire rational Lie algebra. Properness is recorded by
failure of surjectivity on identity tangents. -/
theorem span_lie_of_proper_reductiveSubgroups [Infinite k]
    (hComponent : SemisimpleLieCentralizerComponentReductive.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (hGeom : HasGeometricNoncentralSemisimple G) (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Submodule.span k {x : Lie k G.val | ∃ H : ClosedSubgroup G.val,
      IsReductive (closedSubgroupAlgebraicGroup H) ∧
      ¬ Function.Surjective (mapPointKernel H.inclusion) ∧
      LinearAlgebraicGroups.CocharacterDynamics.lieImage H x} = ⊤ := by
  classical
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨n, L, ⟨l⟩, f, hf⟩ := faithfulLinearization k G
  let L' : AffineGroupCategory k := ⟨L.val, L.property.1⟩
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  let V := Lie k G.val
  let : AddCommGroup V := s.lieRing.toAddCommGroup
  let : Module k V := s.lieAlgebra.toModule
  let d := faithfulLieHom G' L' s l f hf
  have hd := faithfulLieHom_injective G' L' s l f hf
  let : FiniteDimensional k V := FiniteDimensional.of_injective d.toLinearMap hd
  let b := Module.Free.chooseBasis k V
  let : Fintype (Module.Free.ChooseBasisIndex k V) := Fintype.ofFinite _
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  obtain ⟨p, _, _⟩ := hopfSpecPoints k
  let points := p A ≪≫ (groupPointsFunctor k).mapIso e
  let w : (specGroup A).X.left ≅ G.val.X.left :=
    ((Grp.forget (SchemeOver k)) ⋙ Over.forget (Spec (CommRingCat.of k))).mapIso e
  have hw : w.hom ≫ G.val.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) :=
    Over.w ((Grp.forget (SchemeOver k)).map e.hom)
  let : Algebra.Smooth k A := by
    have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
      rw [← hw]
      let : Smooth G.val.X.hom := hG.1
      let : IsIso w.hom := w.isIso_hom
      let hres : MorphismProperty.Respects (@Smooth.{u}) (@IsOpenImmersion.{u}) :=
        HasRingHomProperty.respects_isOpenImmersion
          (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
            RingHom.Smooth.holdsForLocalizationAway).1
      let : MorphismProperty.RespectsLeft (@Smooth.{u}) (@IsOpenImmersion.{u}) :=
        hres.toRespectsLeft
      exact MorphismProperty.RespectsLeft.precomp (P := @Smooth.{u}) (Q := @IsOpenImmersion.{u})
        w.hom inferInstance G.val.X.hom hG.1
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hs)
  apply top_unique
  rw [← span_adjointNonnilpotent G s hGeom b]
  apply Submodule.span_mono
  intro x hx
  obtain ⟨H, hH, hxH, hproper⟩ := exists_reductiveSubgroup_of_adjointNonnilpotent
    hComponent G hG L' s A points (ULift.{u} (Fin n)) l f hf x hx
  exact ⟨H, hH, hproper, hxH⟩

/-- A formally smooth quotient of a Noetherian domain cannot have a
nonzero defining ideal whose tangent equations all vanish at a proper ideal. -/
private theorem formallySmoothQuotient_ideal_eq_bot
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [IsNoetherianRing A]
    (I m : Ideal A) [Algebra.FormallySmooth k (A ⧸ I)]
    (hm : m ≠ ⊤) (hI : I ≤ m ^ 2) : I = ⊥ := by
  let S := A ⧸ I ^ 2
  let q := Ideal.Quotient.mkₐ k I
  let q₂ := Ideal.Quotient.mkₐ k (I ^ 2)
  have hI₂ : I ^ 2 ≤ I := by rw [pow_two]; exact Ideal.mul_le_left
  have hIm : I ≤ m := hI.trans (by rw [pow_two]; exact Ideal.mul_le_left)
  let p := Ideal.Quotient.factorₐ k hI₂
  have psurj : Function.Surjective p := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨q₂ a, rfl⟩
  have hk : RingHom.ker p.toRingHom = I.map q₂.toRingHom :=
    Ideal.Quotient.factor_ker hI₂
  have hn : IsNilpotent (RingHom.ker p.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [hk, ← Ideal.map_pow]
    change (I ^ 2).map (Ideal.Quotient.mk (I ^ 2)) = 0
    rw [Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k (A ⧸ I)) p psurj hn
  let e := s.comp q
  let δ (a : A) : S := q₂ a - e a
  have hd (a : A) : δ a ∈ I.map q₂.toRingHom := by
    rw [← hk, RingHom.mem_ker]
    change p (q₂ a - s (q a)) = 0
    have h : p (s (q a)) = q a :=
      Algebra.FormallySmooth.liftOfSurjective_apply _ p psurj hn _
    rw [map_sub, h]
    exact sub_self _
  have hmul (a b : A) : δ (a * b) = δ a * q₂ b + e a * δ b := by
    simp only [δ, map_mul]
    ring
  have he (a : A) (ha : a ∈ m) : e a ∈ m.map q₂.toRingHom := by
    have h := Ideal.map_mono (f := q₂.toRingHom) hIm (hd a)
    have hq := Ideal.mem_map_of_mem q₂.toRingHom ha
    convert (m.map q₂.toRingHom).sub_mem hq h using 1
    simp [δ]
  let J := (m * I).map q₂.toRingHom
  have hJ : J = (m.map q₂.toRingHom) * (I.map q₂.toRingHom) := Ideal.map_mul _ _ _
  let D : Ideal A :=
    { carrier := {a | a ∈ m ∧ δ a ∈ J}
      zero_mem' := ⟨m.zero_mem, by simp [δ]⟩
      add_mem' := fun {a b} ha hb => by
        refine ⟨m.add_mem ha.1 hb.1, ?_⟩
        change q₂ (a + b) - e (a + b) ∈ J
        rw [map_add, map_add, add_sub_add_comm]
        exact J.add_mem ha.2 hb.2
      smul_mem' := fun c a ha => by
        refine ⟨m.mul_mem_left c ha.1, ?_⟩
        change δ (c * a) ∈ J
        rw [hmul]
        apply J.add_mem
        · rw [hJ, mul_comm (δ c) (q₂ a)]
          exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem q₂.toRingHom ha.1) (hd c)
        · exact J.mul_mem_left _ ha.2 }
  have hm₂ : m ^ 2 ≤ D := by
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    refine ⟨m.mul_mem_left a hb, ?_⟩
    rw [hmul, hJ]
    apply Ideal.add_mem
    · rw [mul_comm (δ a) (q₂ b)]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem q₂.toRingHom hb) (hd a)
    · exact Ideal.mul_mem_mul (he a ha) (hd b)
  have hi : I ≤ m * I := by
    intro a ha
    have hd' := ((hI.trans hm₂) ha : a ∈ D).2
    have hqa : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    change q₂ a - s (q a) ∈ J at hd'
    rw [hqa, map_zero, sub_zero] at hd'
    obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective q₂.toRingHom
      Ideal.Quotient.mk_surjective).mp hd'
    have hdiff : a - b ∈ I ^ 2 := Ideal.Quotient.eq_zero_iff_mem.mp (by
      change q₂ (a - b) = 0
      rw [map_sub, sub_eq_zero]
      exact hab.symm)
    have hle : I ^ 2 ≤ m * I := by
      rw [pow_two]
      exact mul_le_mul_left hIm I
    have hdiff' : a - b ∈ m * I := hle hdiff
    simpa using (m * I).add_mem hdiff' hb
  obtain ⟨a, ha, hann⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    m I (IsNoetherian.noetherian I) (by simpa [Ideal.smul_eq_mul] using hi)
  have hane : a ≠ 0 := by
    rintro rfl
    apply hm
    apply Ideal.eq_top_of_isUnit_mem _ ha
    simp
  apply bot_unique
  intro x hx
  rw [Ideal.mem_bot]
  exact (mul_eq_zero.mp (hann x hx)).resolve_left hane

open private ideal_le_point_sq_iff hopfPoint_map
  from LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
open private dualKernelIso from LinearAlgebraicGroups.Affine.IdentityTangent

/-- For a smooth closed subgroup of an integral affine group, equality of
identity tangent spaces forces equality of the defining Hopf ideals. -/
theorem hopfQuotient_eq_bot_of_surjective_tangent (A : HopfAlgebraCategory k)
    [IsDomain A] [IsNoetherianRing A] (I : Ideal A) [I.IsHopfIdeal k]
    [Algebra.FormallySmooth k (A ⧸ I)]
    (h : Function.Surjective (mapPointKernel (specGroupMap (hopfQuotientMap A I)))) :
    I = ⊥ := by
  let x := Bialgebra.counitAlgHom k A
  apply formallySmoothQuotient_ideal_eq_bot (k := k) A I (RingHom.ker x.toRingHom)
    (RingHom.ker_ne_top x.toRingHom)
  apply (ideal_le_point_sq_iff A x I).mpr
  intro g v hv
  let B := hopfQuotient A I
  let q := hopfQuotientMap A I
  let eA := hopfSpecPointIso A
  let eB := hopfSpecPointIso B
  let tA := dualKernelIso eA
  let tB := dualKernelIso eB
  let a := (hopfKernelLifts A).symm g
  let R := CommAlgCat.of k (DualNumber k)
  obtain ⟨w, hw⟩ := h (tA a)
  obtain ⟨b, rfl⟩ := tB.surjective w
  have hh := congrArg (fun u : Lie k (specGroup A) => u.toMul.val) hw
  change ((groupPointsFunctor k).map (specGroupMap q)).app R (eB.hom.app R b.toMul.val) =
    eA.hom.app R a.toMul.val at hh
  rw [hopfPoint_map] at hh
  have ht := (ConcreteCategory.bijective_of_isIso (eA.hom.app R)).1 hh
  have he := congrArg WithConv.ofConv ht
  change b.toMul.val.ofConv.comp q.hom.toAlgHom = g.val at he
  change g.val v = 0
  rw [← he]
  change b.toMul.val.ofConv (Ideal.Quotient.mk I v) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hv, map_zero]

private theorem mapPointKernel_injective_of_closedSubgroup {G : GroupScheme k}
    (S : ClosedSubgroup G) : Function.Injective (mapPointKernel S.inclusion) := by
  let : IsClosedImmersion S.inclusion.hom.hom.left := S.isClosedImmersion
  let : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  intro x y h
  change x.toMul = y.toMul
  apply Subtype.ext
  apply (cancel_mono S.inclusion.hom.hom).mp
  exact congrArg (fun z : Lie k G => z.toMul.val) h

private theorem lie_finiteDimensional (G : AffineAlgebraicGroup k)
    (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    FiniteDimensional k (Lie k G.val) := by
  classical
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨n, L, ⟨l⟩, f, hf⟩ := faithfulLinearization k G
  let L' : AffineGroupCategory k := ⟨L.val, L.property.1⟩
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  exact FiniteDimensional.of_injective (faithfulLieHom G' L' s l f hf).toLinearMap
    (faithfulLieHom_injective G' L' s l f hf)

/-- The dimension of the identity tangent of an affine algebraic group. -/
def lieDimension (G : AffineAlgebraicGroup k) : ℕ :=
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  Module.finrank k (Lie k G.val)

/-- A proper image on identity tangents gives the strict dimension
inequality needed for induction on reductive centralizers. -/
theorem closedSubgroup_lieDimension_lt (G : AffineAlgebraicGroup k)
    (H : ClosedSubgroup G.val)
    (hH : ¬ Function.Surjective (mapPointKernel H.inclusion)) :
    lieDimension (closedSubgroupAlgebraicGroup H) < lieDimension G := by
  let S := closedSubgroupAlgebraicGroup H
  let s : IdentityLieStructure H.group := identityLieStructure S
  let t := identityLieStructure G
  let : IsAffine G.val.X.left := G.property.1
  let : IsAffine H.group.X.left := S.property.1
  let := s.lieRing
  let := s.lieAlgebra
  let := t.lieRing
  let := t.lieAlgebra
  have hfinite : FiniteDimensional k (Lie k G.val) := lie_finiteDimensional G t
  obtain ⟨d, hd⟩ := identityDifferentialLieHom k H.group G.val H.inclusion s t
  have hinj : Function.Injective d.toLinearMap := by
    intro x y h
    apply mapPointKernel_injective_of_closedSubgroup H
    exact (hd x).symm.trans (h.trans (hd y))
  have hlt : LinearMap.range d.toLinearMap < ⊤ :=
    lt_top_iff_ne_top.mpr (fun h => hH (fun x => by
      obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp h x
      exact ⟨y, (hd y).symm.trans hy⟩))
  have hrank : Module.finrank k (LinearMap.range d.toLinearMap) <
      Module.finrank k (⊤ : Submodule k (Lie k G.val)) :=
    @Submodule.finrank_strictMono k (Lie k G.val) _ _ _ hfinite _ _ hlt
  calc
    lieDimension S = Module.finrank k (Lie k H.group) := rfl
    _ = Module.finrank k (LinearMap.range d.toLinearMap) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ < Module.finrank k (⊤ : Submodule k (Lie k G.val)) := hrank
    _ = lieDimension G := finrank_top _ _

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

open Specs.AdjointRepresentation (GroupPoints)

open private isIso_of_schemeIso from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

private abbrev rationalSource (k : Type u) [Field k] : SchemeOver k :=
  Over.mk (𝟙 (Spec (CommRingCat.of k)))

private abbrev RationalSections (G : GroupScheme k) :=
  rationalSource k ⟶ G.X

private def rationalSectionsMap {G H : GroupScheme k} (f : G ⟶ H) :
    RationalSections G →* RationalSections H :=
  IsMonHom.monoidHom f.hom.hom _

open private rationalSpec_hom affineBaseTerminal from LinearAlgebraicGroups.Solvable.SplitFixedPoint

private theorem fieldSpecMap_self (k : Type u) [Field k] :
    fieldSpecMap k k = 𝟙 (Spec (CommRingCat.of k)) :=
  rationalSpec_hom k

private def rationalSourceIso (k : Type u) [Field k] : rationalSource k ≅ affineOver k k :=
  (Over.mkIdTerminal : IsTerminal (rationalSource k)).uniqueUpToIso (affineBaseTerminal k)

private theorem rationalSourceIso_hom_left (k : Type u) [Field k] :
    (rationalSourceIso k).hom.left = 𝟙 (Spec (CommRingCat.of k)) := by
  have h := Over.w (rationalSourceIso k).hom
  change (rationalSourceIso k).hom.left ≫ fieldSpecMap k k = _ at h
  rw [fieldSpecMap_self] at h
  exact (Category.comp_id (show Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)
    from (rationalSourceIso k).hom.left)).symm.trans h

private def rationalPointCoordinates {A : HopfAlgebraCategory k} {G : GroupScheme k}
    (e : specGroup A ≅ G) : CoordinatePoints A →* RationalSections G :=
  let R := CommAlgCat.of k k
  let p : GroupPoints (specGroup A) R →* RationalSections (specGroup A) :=
    { toFun := fun a => (rationalSourceIso k).hom ≫ a
      map_one' := MonObj.comp_one _
      map_mul' := MonObj.comp_mul _ }
  (rationalSectionsMap e.hom).comp (p.comp ((hopfSpecPointIso A).hom.app R).hom)

private theorem rationalPointCoordinates_apply {A : HopfAlgebraCategory k} {G : GroupScheme k}
    (e : specGroup A ≅ G) (a : CoordinatePoints A) :
    rationalPointCoordinates e a = affineRationalSection a.ofConv ≫ e.hom.hom.hom := by
  apply Over.OverMorphism.ext
  change (((rationalSourceIso k).hom ≫
    (hopfSpecPointIso A).hom.app (CommAlgCat.of k k) a) ≫ e.hom.hom.hom).left = _
  have h₀ := rationalSourceIso_hom_left k
  have ha : ((hopfSpecPointIso A).hom.app (CommAlgCat.of k k) a).left =
      Spec.map (CommRingCat.ofHom a.ofConv.toRingHom) := rfl
  change ((rationalSourceIso k).hom.left ≫
    ((hopfSpecPointIso A).hom.app (CommAlgCat.of k k) a).left) ≫ e.hom.hom.hom.left =
      Spec.map (CommRingCat.ofHom a.ofConv.toRingHom) ≫ e.hom.hom.hom.left
  rw [h₀, ha]
  exact congrArg (fun g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) =>
    g ≫ e.hom.hom.hom.left) (Category.id_comp (Spec.map (CommRingCat.ofHom a.ofConv.toRingHom)))

private theorem rationalPointCoordinates_surjective {A : HopfAlgebraCategory k}
    {G : GroupScheme k} (e : specGroup A ≅ G) :
    Function.Surjective (rationalPointCoordinates e) := by
  intro p
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
    ((hopfSpecPointIso A).hom.app (CommAlgCat.of k k))).2
      ((rationalSourceIso k).inv ≫ p ≫ e.inv.hom.hom)
  refine ⟨a, ?_⟩
  change ((rationalSourceIso k).hom ≫
    (hopfSpecPointIso A).hom.app (CommAlgCat.of k k) a) ≫ e.hom.hom.hom = p
  have hₑ : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 G.X :=
    (Grp.forget (SchemeOver k)).congr_map e.inv_hom_id
  rw [ha]
  simp only [Category.assoc, hₑ, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem affine_geometricallyReduced_of_separating {A I : Type u} [CommRing A]
    [Algebra k A] (a : I → A →ₐ[k] k) (hA : ∀ x : A, (∀ i, a i x = 0) → x = 0) :
    GeometricallyReduced (affineOver k A).hom := by
  rw [GeometricallyReduced.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let p (i : I) : K ⊗[k] A →ₐ[K] K :=
    (AlgHom.liftEquiv k K A K) ((IsScalarTower.toAlgHom k k K).comp (a i))
  have ht : IsReduced (K ⊗[k] A) := by
    refine ⟨fun x hx => ?_⟩
    apply tensor_eq_zero_of_forall_liftBaseChange (fun i => (a i).toLinearMap) hA
    intro i
    have hp : (p i).toLinearMap = LinearMap.liftBaseChange K
        ((Algebra.linearMap k K).comp (a i).toLinearMap) := by
      apply (LinearMap.liftBaseChangeEquiv K).symm.injective
      ext b
      simp [p]
    rw [← hp]
    exact (hx.map (p i)).eq_zero
  exact isReduced_of_isOpenImmersion (affineBaseChangeIso (k := k) K A).inv

private theorem affineRationalSection_comp {A B : HopfAlgebraCategory k} (q : A ⟶ B)
    (f : B →ₐ[k] k) :
    affineRationalSection f ≫ (specGroupMap q).hom.hom =
      affineRationalSection (f.comp q.hom.toAlgHom) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom q.hom.toAlgHom.toRingHom) =
    Spec.map (CommRingCat.ofHom (f.comp q.hom.toAlgHom).toRingHom)
  rw [← Spec.map_comp]
  rfl

/-- The closure of a subgroup of rational points is smooth and its specified
rational points are geometrically dense. -/
private theorem exists_rationalPointClosure (G : AffineAlgebraicGroup k)
    (S : Subgroup (RationalSections G.val)) :
    ∃ C : ClosedSubgroup G.val, Smooth C.group.X.hom ∧
      ∃ (P : Type u) (p : P → RationalSections C.group),
        (∀ x, p x ≫ C.inclusion.hom.hom ∈ S) ∧
        (∀ s : S, ∃ x, p x ≫ C.inclusion.hom.hom = s.val) ∧
        Dense (Set.range fun x => rationalPointOver (AlgebraicClosure k) (p x)) := by
  obtain ⟨A, hA, ⟨e⟩⟩ := groupPresentation G
  let S₀ := S.comap (rationalPointCoordinates e)
  let I := evaluationIdeal S₀
  letI : I.IsHopfIdeal k := evaluationIdeal_isHopf S₀
  let Q := hopfQuotient A I
  let q := hopfQuotientMap A I
  let j : specGroup Q ⟶ G.val := specGroupMap q ≫ e.hom
  letI : IsClosedImmersion (specGroupMap q).hom.hom.left :=
    (hopfMapClosedImmersion k q).mpr Ideal.Quotient.mk_surjective
  letI : IsIso e.hom.hom.hom.left := ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map_isIso e.hom
  let C : ClosedSubgroup G.val := ⟨specGroup Q, j, by
    change IsClosedImmersion ((specGroupMap q).hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance⟩
  let p (a : S₀) : RationalSections C.group := affineRationalSection (quotientEvaluation S₀ a)
  have hp (a : S₀) : p a ≫ j.hom.hom = rationalPointCoordinates e a.val := by
    rw [rationalPointCoordinates_apply]
    have he : p a ≫ (specGroupMap q).hom.hom = affineRationalSection a.val.ofConv :=
      affineRationalSection_comp q (quotientEvaluation S₀ a)
    change p a ≫ (specGroupMap q).hom.hom ≫ e.hom.hom.hom = _
    rw [← Category.assoc, he]
  refine ⟨C, ?_, S₀, p, fun a => hp a ▸ a.property, ?_, ?_⟩
  · letI : LocallyOfFiniteType C.group.X.hom :=
      (closedSubgroupAlgebraicGroup (G := G) C).property.2.1
    exact (groupSmoothnessCriteria k C.group).1.mpr
      (affine_geometricallyReduced_of_separating (quotientEvaluation S₀)
        (quotientEvaluation_separates S₀))
  · intro s
    obtain ⟨a, ha⟩ := rationalPointCoordinates_surjective e s.val
    have haS : a ∈ S₀ := by
      change rationalPointCoordinates e a ∈ S
      rw [ha]
      exact s.property
    exact ⟨⟨a, haS⟩, (hp _).trans ha⟩
  · exact affine_dense_eval (quotientEvaluation S₀) (quotientEvaluation_separates S₀)

private theorem isIso_of_dense_subgroup {G : GroupScheme k} (H : ClosedSubgroup G)
    [IsReduced G.X.left] (h : DenseRange H.inclusion.hom.hom.left) : IsIso H.inclusion := by
  letI := H.isClosedImmersion
  haveI : Surjective H.inclusion.hom.hom.left :=
    ⟨Set.range_eq_univ.mp (H.isClosedImmersion.isClosedEmbedding.isClosed_range.closure_eq.symm.trans
      h.closure_eq)⟩
  letI := isIso_of_isClosedImmersion_of_surjective H.inclusion.hom.hom.left
  exact isIso_of_schemeIso H.inclusion

private def inverseImageSubgroup {G H : GroupScheme k} (f : G ⟶ H)
    (C : ClosedSubgroup H) : ClosedSubgroup G := by
  let U := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have hp := U.map_isPullback (IsPullback.of_hasPullback f C.inclusion)
  exact ⟨_, pullback.fst f C.inclusion,
    MorphismProperty.of_isPullback hp.flip C.isClosedImmersion⟩

private theorem factors_through_closed_of_range {G H : GroupScheme k} (f : G ⟶ H)
    (C : ClosedSubgroup H) [IsReduced G.X.left]
    (h : Set.range f.hom.hom.left ⊆ Set.range C.inclusion.hom.hom.left) :
    ∃ i : G ⟶ C.group, i ≫ C.inclusion = f := by
  let B := inverseImageSubgroup f C
  let U := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have hp := U.map_isPullback (IsPullback.of_hasPullback f C.inclusion)
  have hr : Set.range B.inclusion.hom.hom.left = Set.univ := by
    change Set.range (U.map (pullback.fst f C.inclusion)) = _
    rw [← hp.isoPullback_hom_fst]
    change Set.range ((pullback.fst (U.map f) (U.map C.inclusion) : _ ⟶ _) ∘
      hp.isoPullback.hom) = _
    have hs : Function.Surjective hp.isoPullback.hom := hp.isoPullback.hom.homeomorph.surjective
    rw [Set.range_comp, hs.range_eq, Set.image_univ, Scheme.Pullback.range_fst]
    exact Set.eq_univ_of_forall fun x => h ⟨x, rfl⟩
  haveI : IsIso B.inclusion := isIso_of_dense_subgroup B (by
    change Dense (Set.range B.inclusion.hom.hom.left)
    rw [hr]
    exact dense_univ)
  refine ⟨inv B.inclusion ≫ pullback.snd f C.inclusion, ?_⟩
  rw [Category.assoc, ← pullback.condition]
  change inv B.inclusion ≫ B.inclusion ≫ f = f
  simp

private theorem dense_rationalSectionValues {X : SchemeOver k} {P : Type u}
    (s : P → (rationalSource k ⟶ X))
    (hs : Dense (Set.range fun a => rationalPointOver (AlgebraicClosure k) (s a))) :
    Dense (Set.range fun a => (s a).left (IsLocalRing.closedPoint k)) := by
  let K := AlgebraicClosure k
  let p := pullback.fst X.hom (fieldSpecMap k K)
  have hfield : Surjective (fieldSpecMap k K) :=
    ⟨Function.surjective_to_subsingleton _⟩
  have hp : Surjective p := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback X.hom (fieldSpecMap k K)).flip hfield
  have he (a : P) : p (rationalPointOver K (s a)) = (s a).left (IsLocalRing.closedPoint k) := by
    let l : Spec (CommRingCat.of K) ⟶ pullback X.hom (fieldSpecMap k K) :=
      pullback.lift (fieldSpecMap k K ≫ (s a).left) (𝟙 (Spec (CommRingCat.of K))) (by
        rw [Category.assoc, Over.w (s a)]
        simp)
    let x : (Spec (CommRingCat.of K)).carrier := IsLocalRing.closedPoint K
    have hcomp : l ≫ p = fieldSpecMap k K ≫ (s a).left := pullback.lift_fst _ _ _
    calc
      _ = (l ≫ p) x := rfl
      _ = (fieldSpecMap k K ≫ (s a).left) x :=
        congrArg (fun f : Spec (CommRingCat.of K) ⟶ X.left => f x) hcomp
      _ = _ := congrArg (s a).left
        (Subsingleton.elim (fieldSpecMap k K x : (Spec (CommRingCat.of k)).carrier)
          (IsLocalRing.closedPoint k))
  have h := hp.surj.denseRange.dense_image p.continuous hs
  apply h.mono
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact ⟨a, (he a).symm⟩

private theorem factors_through_closed_of_dense_rationalSections {G H : GroupScheme k}
    (f : G ⟶ H) (C : ClosedSubgroup H) [IsReduced G.X.left] {P : Type u}
    (p : P → RationalSections G)
    (hp : Dense (Set.range fun a => rationalPointOver (AlgebraicClosure k) (p a)))
    (h : ∀ a, ∃ c : RationalSections C.group, c ≫ C.inclusion.hom.hom = p a ≫ f.hom.hom) :
    ∃ i : G ⟶ C.group, i ≫ C.inclusion = f := by
  apply factors_through_closed_of_range f C
  rw [← Set.image_univ]
  apply Set.image_subset_iff.mpr
  letI := C.isClosedImmersion
  have hClosed := C.isClosedImmersion.isClosedEmbedding.isClosed_range.preimage
    f.hom.hom.left.continuous
  rw [← (dense_rationalSectionValues p hp).closure_eq, hClosed.closure_subset_iff]
  rintro _ ⟨a, rfl⟩
  obtain ⟨c, hc⟩ := h a
  refine ⟨c.left (IsLocalRing.closedPoint k), ?_⟩
  exact congrArg (fun x : RationalSections H => x.left (IsLocalRing.closedPoint k)) hc

private def rationalTorusPoints (G : AffineAlgebraicGroup k) : Subgroup (RationalSections G.val) :=
  Subgroup.closure {p | ∃ T : ClosedSubgroup G.val, Specs.GeometricRadicals.IsTorus T.group ∧
    ∃ t : RationalSections T.group, t ≫ T.inclusion.hom.hom = p}

open private torusCoordinatesDomain from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel

private theorem torus_isReduced (T : AffineAlgebraicGroup k) (hT : Specs.GeometricRadicals.IsTorus T.val) :
    IsReduced T.val.X.left := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation T
  letI : IsDomain A := torusCoordinatesDomain A
    ((isTorus_spec_iff A).mp (isTorus_of_groupIso e hT))
  haveI : IsReduced (specGroup A).X.left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of A)))
  let f : (specGroup A).X.left ≅ T.val.X.left :=
    ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso e
  letI : IsIso f.inv := f.isIso_inv
  exact isReduced_of_isOpenImmersion f.inv

private theorem exists_torusPointClosure [Infinite k] (G : AffineAlgebraicGroup k) :
    ∃ C : ClosedSubgroup G.val, Smooth C.group.X.hom ∧
      (∀ T : ClosedSubgroup G.val, Specs.GeometricRadicals.IsTorus T.group → IsSubgroupOf T C) ∧
      ∃ (P : Type u) (p : P → RationalSections C.group),
        (∀ a, p a ≫ C.inclusion.hom.hom ∈ rationalTorusPoints G) ∧
        Dense (Set.range fun a => rationalPointOver (AlgebraicClosure k) (p a)) := by
  obtain ⟨C, hC, P, p, hmem, hsur, hdense⟩ := exists_rationalPointClosure G (rationalTorusPoints G)
  refine ⟨C, hC, ?_, P, p, hmem, hdense⟩
  intro T hT
  let T₀ := closedSubgroupAlgebraicGroup T
  letI : IsReduced T.group.X.left := torus_isReduced T₀ hT
  apply factors_through_closed_of_dense_rationalSections T.inclusion C id
    (torus_rational_density k T₀ hT)
  intro t
  obtain ⟨a, ha⟩ := hsur ⟨t ≫ T.inclusion.hom.hom, Subgroup.subset_closure ⟨T, hT, t, rfl⟩⟩
  exact ⟨p a, ha⟩

private theorem torusPointClosure_factors (G : AffineAlgebraicGroup k)
    {C H : ClosedSubgroup G.val} [IsReduced C.group.X.left] {P : Type u}
    (p : P → RationalSections C.group)
    (hp : ∀ a, p a ≫ C.inclusion.hom.hom ∈ rationalTorusPoints G)
    (hpd : Dense (Set.range fun a => rationalPointOver (AlgebraicClosure k) (p a)))
    (hH : ∀ T : ClosedSubgroup G.val, Specs.GeometricRadicals.IsTorus T.group → IsSubgroupOf T H) :
    IsSubgroupOf C H := by
  have hS : rationalTorusPoints G ≤ (rationalSectionsMap H.inclusion).range := by
    rw [rationalTorusPoints, Subgroup.closure_le]
    rintro _ ⟨T, hT, t, rfl⟩
    obtain ⟨i, hi⟩ := hH T hT
    exact ⟨t ≫ i.hom.hom, by
      change (t ≫ i.hom.hom) ≫ H.inclusion.hom.hom = _
      rw [Category.assoc]
      exact congrArg (fun f : T.group ⟶ G.val => t ≫ f.hom.hom) hi⟩
  exact factors_through_closed_of_dense_rationalSections C.inclusion H p hpd
    (fun a => hS (hp a))

private theorem geometricallyGeneratedByRationalTori_of_generated [Infinite k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (hgen : GeneratedByRationalTori G) :
    GeometricallyGeneratedByRationalTori G := by
  intro H hH
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let Z := (baseChange k K).obj (rationalSource k)
  let b : RationalSections G.val →* (Z ⟶ (F.obj G.val).X) :=
    (baseChange k K).homMonoidHom
  let m : (Z ⟶ H.group.X) →* (Z ⟶ (F.obj G.val).X) :=
    IsMonHom.monoidHom H.inclusion.hom.hom Z
  have hS : rationalTorusPoints G ≤ m.range.comap b := by
    rw [rationalTorusPoints, Subgroup.closure_le]
    rintro _ ⟨T, hT, t, rfl⟩
    obtain ⟨i, hi⟩ := hH T hT
    refine ⟨(baseChange k K).map t ≫ i.hom.hom, ?_⟩
    change (_ ≫ i.hom.hom) ≫ H.inclusion.hom.hom = (baseChange k K).map (t ≫ T.inclusion.hom.hom)
    rw [Category.assoc, Functor.map_comp]
    exact congrArg (fun f : F.obj T.group ⟶ F.obj G.val =>
      (baseChange k K).map t ≫ f.hom.hom) hi
  obtain ⟨C, _, hC, P, p, hp, hpd⟩ := exists_torusPointClosure G
  letI : IsIso C.inclusion := hgen C hC
  let j := (F.map C.inclusion).hom.hom.left
  letI : IsIso j := ((Grp.forget (SchemeOver K)) ⋙ Over.forget _).map_isIso (F.map C.inclusion)
  have hj := j.homeomorph.surjective.denseRange.dense_image j.continuous hpd
  letI : Smooth (GeometricGroup G).val.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hG.1
  letI := isReduced_of_smooth_over_field (GeometricGroup G).val.X.hom
  apply isIso_of_dense_subgroup H
  apply hj.mono
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  change ((baseChange k K).map C.inclusion.hom.hom).left (rationalPointOver K (p a)) ∈
    Set.range H.inclusion.hom.hom.left
  rw [← rationalPointOver_natural (K := K) C.inclusion.hom.hom (p a)]
  obtain ⟨c, hc⟩ := hS (hp a)
  let z := rationalPointOver K (𝟙 (rationalSource k))
  refine ⟨c.left z, ?_⟩
  have he := congrArg (fun x : Z ⟶ (F.obj G.val).X => x.left z) hc
  change _ = ((baseChange k K).map (p a ≫ C.inclusion.hom.hom)).left z at he
  rw [← rationalPointOver_natural (p a ≫ C.inclusion.hom.hom) (𝟙 (rationalSource k)),
    Category.id_comp] at he
  exact he

open private irreducible_of_geometricallyConnected from LinearAlgebraicGroups.Solvable.WordDomainGeometry

private theorem group_integral_of_reductive (G : AffineAlgebraicGroup k) (hG : IsReductive G) :
    IsIntegral G.val.X.left := by
  letI := hG.1
  letI := hG.2.1
  letI := G.property.2.1
  letI := G.property.2.2
  letI := irreducible_of_geometricallyConnected G.val
  letI := isReduced_of_smooth_over_field G.val.X.hom
  exact isIntegral_of_irreducibleSpace_of_isReduced _

open private smooth_spec_iff from LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus

set_option maxHeartbeats 850000 in
private theorem closedSubgroup_iso_of_smooth_lie_surjective
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (H : ClosedSubgroup G.val)
    (hH : Smooth H.group.X.hom) (hs : Function.Surjective (mapPointKernel H.inclusion)) :
    IsIso H.inclusion := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  let j := H.inclusion ≫ e.inv
  let U := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  letI : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  letI : IsIso e.inv.hom.hom.left := U.map_isIso e.inv
  have hj : IsClosedImmersion j.hom.hom.left := by
    change IsClosedImmersion (H.inclusion.hom.hom.left ≫ e.inv.hom.hom.left)
    infer_instance
  obtain ⟨I, ⟨hI, c, hc⟩, _⟩ := (closedSubgroupClassification k A H.group j).mp hj
  letI := hI
  let π := specGroupMap (hopfQuotientMap A I)
  have hπ : Function.Surjective (mapPointKernel π) := by
    intro x
    obtain ⟨y, hy⟩ := hs (mapPointKernel e.hom x)
    refine ⟨mapPointKernel c.hom y, ?_⟩
    rw [← (lieFunctoriality k).2.2, hc]
    change mapPointKernel (H.inclusion ≫ e.inv) y = x
    rw [(lieFunctoriality k).2.2, hy, ← (lieFunctoriality k).2.2, e.hom_inv_id,
      (lieFunctoriality k).2.1]
  have hsm : Smooth (specGroup (hopfQuotient A I)).X.hom := by
    letI := hH
    letI : IsIso c.inv.hom.hom.left := U.map_isIso c.inv
    rw [← Over.w c.inv.hom.hom]
    infer_instance
  letI : Algebra.Smooth k (A ⧸ I) := (smooth_spec_iff (k := k) (A := A ⧸ I)).mp hsm
  letI : IsIntegral G.val.X.left := group_integral_of_reductive G hG
  have hA : IsIntegral (Spec (CommRingCat.of A)) := IsIntegral.of_isIso e.inv.hom.hom.left
  letI : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).mp hA
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hbot := hopfQuotient_eq_bot_of_surjective_tangent A I hπ
  let q := hopfQuotientMap A I
  have hq : Function.Bijective q.hom := by
    refine ⟨?_, Ideal.Quotient.mk_surjective⟩
    change Function.Injective (Ideal.Quotient.mk I)
    intro a b hab
    have hab' : a - b ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, hab, sub_self])
    rw [hbot, Ideal.mem_bot] at hab'
    exact sub_eq_zero.mp hab'
  let e₀ := CommHopfAlgCat.isoMk (BialgEquiv.ofBijective q.hom hq)
  letI : IsIso π := (hopfSpec (CommRingCat.of k)).map_isIso e₀.op.hom
  letI : IsIso (c.hom ≫ π) := inferInstance
  haveI : IsIso j := hc ▸ (inferInstance : IsIso (c.hom ≫ π))
  have hh : j ≫ e.hom = H.inclusion := by simp [j]
  rw [← hh]
  infer_instance

private theorem factor_of_generated_subgroup {G : AffineAlgebraicGroup k}
    (H C : ClosedSubgroup G.val) (hgen : GeneratedByRationalTori (closedSubgroupAlgebraicGroup H))
    (hC : ∀ T : ClosedSubgroup G.val, Specs.GeometricRadicals.IsTorus T.group → IsSubgroupOf T C) :
    IsSubgroupOf H C := by
  let D := inverseImageSubgroup H.inclusion C
  have hd : IsIso D.inclusion := hgen D (by
    intro T hT
    obtain ⟨i, hi⟩ := hC (GeometricBorelConjugacy.subgroupOfSubgroup H T) hT
    have hti : T.inclusion ≫ H.inclusion = i ≫ C.inclusion := hi.symm
    exact ⟨pullback.lift T.inclusion i hti, pullback.lift_fst _ _ _⟩)
  letI : IsIso D.inclusion := hd
  refine ⟨inv D.inclusion ≫ pullback.snd H.inclusion C.inclusion, ?_⟩
  rw [Category.assoc, ← pullback.condition]
  change inv D.inclusion ≫ D.inclusion ≫ H.inclusion = H.inclusion
  simp

private theorem generatedByRationalTori_of_noncentral [Infinite k]
    (hComponent : SemisimpleLieCentralizerComponentReductive.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (hGeom : HasGeometricNoncentralSemisimple G)
    (ih : ∀ H : ClosedSubgroup G.val, IsReductive (closedSubgroupAlgebraicGroup H) →
      ¬ Function.Surjective (mapPointKernel H.inclusion) →
        GeneratedByRationalTori (closedSubgroupAlgebraicGroup H)) :
    GeneratedByRationalTori G := by
  intro H ht
  obtain ⟨C, hC, hT, P, p, hp, hpd⟩ := exists_torusPointClosure G
  let s := identityLieStructure G
  let C₀ := closedSubgroupAlgebraicGroup C
  let t : IdentityLieStructure C.group := identityLieStructure C₀
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := t.lieRing
  letI := t.lieAlgebra
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine C.group.X.left := C₀.property.1
  obtain ⟨d, hd⟩ := identityDifferentialLieHom k C.group G.val C.inclusion t s
  have hrange : LinearMap.range d.toLinearMap = ⊤ := by
    apply top_unique
    rw [← span_lie_of_proper_reductiveSubgroups hComponent G hG hGeom s]
    apply Submodule.span_le.mpr
    rintro x ⟨D, hD, hproper, y, hy⟩
    obtain ⟨i, hi⟩ := factor_of_generated_subgroup D C (ih D hD hproper) hT
    refine ⟨mapPointKernel i y, ?_⟩
    change d (mapPointKernel i y) = x
    calc
      _ = mapPointKernel C.inclusion (mapPointKernel i y) := hd _
      _ = _ := by rw [← (lieFunctoriality k).2.2, hi, hy]
  have hs : Function.Surjective (mapPointKernel C.inclusion) := by
    intro x
    obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hrange x
    exact ⟨y, (hd y).symm.trans hy⟩
  letI : IsIso C.inclusion := closedSubgroup_iso_of_smooth_lie_surjective G hG C hC hs
  letI := hC
  letI := isReduced_of_smooth_over_field C.group.X.hom
  obtain ⟨i, hi⟩ := torusPointClosure_factors G p hp hpd ht
  exact isIso_of_subgroup_section H (inv C.inclusion ≫ i) (by simp [hi])

private def selfBaseChange (k : Type u) [Field k] : groupBaseChange k k ≅ 𝟭 (GroupScheme k) := by
  have h : baseChange k k = Over.pullback (𝟙 (Spec (CommRingCat.of k))) :=
    congrArg (fun f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) =>
      Over.pullback f) (fieldSpecMap_self k)
  exact (Functor.mapGrpNatIso (eqToIso h ≪≫ Over.pullbackId)) ≪≫ Functor.mapGrpIdIso

private theorem liftsTori_over_base {G Q : GroupScheme k} (q : G ⟶ Q)
    (hlift : LiftsTori q) (T : ClosedSubgroup Q) (hT : Specs.GeometricRadicals.IsTorus T.group) :
    ∃ (S : ClosedSubgroup G) (f : S.group ⟶ T.group),
      Specs.GeometricRadicals.IsTorus S.group ∧ S.inclusion ≫ q = f ≫ T.inclusion ∧
      Surjective f.hom.hom.left := by
  let F := groupBaseChange k k
  let e := selfBaseChange k
  let U := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  let te := e.app Q
  let j : T.group ⟶ F.obj Q := T.inclusion ≫ te.inv
  letI := T.isClosedImmersion
  letI : IsIso te.inv.hom.hom.left := U.map_isIso te.inv
  let T' : ClosedSubgroup (F.obj Q) := ⟨T.group, j, by
    change IsClosedImmersion (T.inclusion.hom.hom.left ≫ te.inv.hom.hom.left)
    infer_instance⟩
  obtain ⟨S', f, hS', hcomp, _, hsur⟩ := hlift k T' hT
  let ge := e.app G
  letI := S'.isClosedImmersion
  letI : IsIso ge.hom.hom.hom.left := U.map_isIso ge.hom
  let S : ClosedSubgroup G := ⟨S'.group, S'.inclusion ≫ ge.hom, by
    change IsClosedImmersion (S'.inclusion.hom.hom.left ≫ ge.hom.hom.hom.left)
    infer_instance⟩
  refine ⟨S, f, hS', ?_, hsur⟩
  change (S'.inclusion ≫ ge.hom) ≫ q = f ≫ T.inclusion
  have hn : F.map q ≫ te.hom = ge.hom ≫ q := e.hom.naturality q
  rw [Category.assoc, ← hn, ← Category.assoc, hcomp]
  change (f ≫ (T.inclusion ≫ te.inv)) ≫ te.hom = _
  simp

private theorem closedSubgroup_iso_of_finite_dominant
    (G Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val)
    (hG : IsReductive G) (hQ : IsReductive Q) (hfin : IsFinite q.hom.hom.left)
    (H : ClosedSubgroup G.val) (hdom : IsDominant (H.inclusion ≫ q).hom.hom.left) :
    IsIso H.inclusion := by
  let g := q.hom.hom.left
  let i := H.inclusion.hom.hom.left
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine Q.val.X.left := Q.property.1
  letI : IsIntegral G.val.X.left := group_integral_of_reductive G hG
  letI : IsIntegral Q.val.X.left := group_integral_of_reductive Q hQ
  letI : IsFinite g := hfin
  letI : IsClosedImmersion i := H.isClosedImmersion
  letI : IsDominant (i ≫ g) := hdom
  letI := IsSchemeTheoreticallyDominant.of_isDominant (i ≫ g)
  letI : QuasiCompact (i ≫ g) := inferInstance
  have hqi : Function.Injective (i ≫ g).appTop := (i ≫ g).app_injective ⊤
  let A := Γ(G.val.X.left, ⊤)
  let B := Γ(Q.val.X.left, ⊤)
  let a : B →+* A := g.appTop.hom
  letI : Algebra B A := a.toAlgebra
  letI : Algebra.IsIntegral B A := ⟨g.finite_appTop.to_isIntegral⟩
  let J : Ideal A := RingHom.ker i.appTop.hom
  have hJ : J = ⊥ := by
    by_contra hn
    apply (Ideal.IsIntegral.under_ne_bot B hn)
    change RingHom.ker (i.appTop.hom.comp a) = ⊥
    rw [← RingHom.injective_iff_ker_eq_bot]
    rw [Scheme.Hom.comp_appTop] at hqi
    exact hqi
  letI : IsIso i := IsClosedImmersion.isIso_of_injective_of_isAffine (f := i)
    ((RingHom.injective_iff_ker_eq_bot i.appTop.hom).mpr hJ)
  exact isIso_of_schemeIso H.inclusion

private theorem generatedByRationalTori_of_finite_torus_lifting
    (G Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val)
    (hG : IsReductive G) (hQ : IsReductive Q) (hfin : IsFinite q.hom.hom.left)
    (hlift : LiftsTori q) (hgen : GeneratedByRationalTori Q) :
    GeneratedByRationalTori G := by
  intro H hH
  obtain ⟨I, p₀, j, hfac₀, _, _⟩ := schemeImageFactorization (closedSubgroupAlgebraicGroup H) Q
    (H.inclusion ≫ q)
  let p : H.group ⟶ I.val := p₀
  have hfac : IsImageFactorization (H.inclusion ≫ q) p j := hfac₀
  let D : ClosedSubgroup Q.val := ⟨I.val, j, hfac.2.2.2.2.2⟩
  letI : IsIso j := hgen D (by
    intro T hT
    obtain ⟨S, f, hs, hf, hsur⟩ := liftsTori_over_base q hlift T hT
    obtain ⟨i, hi⟩ := hH S hs
    letI : IsReduced T.group.X.left := torus_isReduced (closedSubgroupAlgebraicGroup T) hT
    apply factors_through_closed_of_range T.inclusion D
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hsur.surj y
    refine ⟨(i ≫ p).hom.hom.left x, ?_⟩
    have he : (i ≫ p) ≫ j = f ≫ T.inclusion := by
      rw [Category.assoc, hfac.1, ← Category.assoc, hi, hf]
    exact (congrArg (fun m : S.group ⟶ Q.val => m.hom.hom.left x) he).trans
      (congrArg T.inclusion.hom.hom.left hx))
  apply closedSubgroup_iso_of_finite_dominant G Q q hG hQ hfin H
  rw [← hfac.1]
  letI : Surjective p.hom.hom.left := hfac.2.2.1
  letI : IsIso j.hom.hom.left :=
    ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map_isIso j
  change IsDominant (p.hom.hom.left ≫ j.hom.hom.left)
  infer_instance


private theorem baseChange_eigenvalue_over_purelyInseparable
    {K V I : Type u} [Field K] [Algebra k K] [IsPurelyInseparable k K]
    [AddCommGroup V] [Module k V]
    (T : Module.End k V) (b : Module.Basis I K (K ⊗[k] V)) (w : I → K)
    (hb : ∀ i, T.baseChange K (b i) = w i • b i)
    (x : K ⊗[k] V) (hx : x ≠ 0) (c : K) (hc : T.baseChange K x = c • x) :
    ∃ a : k, algebraMap k K a = c := by
  classical
  obtain ⟨p, hp⟩ := ExpChar.exists k
  letI := hp
  letI : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem k p c
  let L := T.baseChange K
  have hpower (y : K ⊗[k] V) (d : K) (hy : L y = d • y) (m : ℕ) :
      (L ^ m) y = d ^ m • y := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Module.End.mul_apply, hy, map_smul, ih, smul_smul, pow_succ']
  let D : Module.End k V := T ^ (p ^ n) - a • (1 : Module.End k V)
  have hD (y : K ⊗[k] V) : D.baseChange K y = (L ^ (p ^ n)) y - (c ^ (p ^ n)) • y := by
    simp [D, L, LinearMap.baseChange_pow, ← ha, algebraMap_smul]
  have hxD : D.baseChange K x = 0 := by
    rw [hD, hpower x c hc, sub_self]
  have hnD : ¬ Function.Injective D := by
    intro hinj
    have hflat := TensorProduct.map_injective_of_flat_flat
      (LinearMap.id : K →ₗ[k] K) D Function.injective_id hinj
    apply hx
    apply hflat
    exact hxD.trans (map_zero _).symm
  obtain ⟨y, hy, hyD⟩ : ∃ y : V, y ≠ 0 ∧ D y = 0 := by
    rw [injective_iff_map_eq_zero] at hnD
    push Not at hnD
    obtain ⟨y, h₁, h₂⟩ := hnD
    exact ⟨y, h₂, h₁⟩
  let z : K ⊗[k] V := (1 : K) ⊗ₜ[k] y
  have hzD : (L ^ (p ^ n)) z = (c ^ (p ^ n)) • z := by
    apply sub_eq_zero.mp
    rw [← hD]
    change (1 : K) ⊗ₜ[k] D y = 0
    rw [hyD, TensorProduct.tmul_zero]
  have hcoord (m : ℕ) (i : I) :
      (b.coord i).comp (L ^ m) = w i ^ m • b.coord i := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, hpower (b j) (w j) (hb j) m, map_smul, LinearMap.smul_apply]
    by_cases hij : i = j
    · subst j
      rfl
    · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hij]
      simp
  have hz : L z = c • z := by
    apply b.repr.injective
    ext i
    change b.coord i (L z) = b.coord i (c • z)
    have hpm : w i ^ (p ^ n) * b.coord i z = c ^ (p ^ n) * b.coord i z := by
      have h := congrArg (b.coord i) hzD
      rw [← LinearMap.comp_apply, hcoord, LinearMap.smul_apply, map_smul, smul_eq_mul,
        smul_eq_mul] at h
      exact h
    have h₁ := LinearMap.congr_fun (hcoord 1 i) z
    simp only [pow_one, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h₁
    rw [h₁, map_smul, smul_eq_mul]
    by_cases hi : b.coord i z = 0
    · simp [hi]
    · have hpow := mul_right_cancel₀ hi hpm
      have he : w i = c := iterateFrobenius_inj K p n hpow
      rw [he]
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hy
  refine ⟨f (T y), ?_⟩
  let fK := LinearMap.liftBaseChange K ((Algebra.linearMap k K).comp f)
  have he := congrArg fK hz
  change fK ((1 : K) ⊗ₜ[k] T y) = fK (c • ((1 : K) ⊗ₜ[k] y)) at he
  simpa [fK, hf] using he

private def coalgebraSlice {A : Type u} [CommRing A] [Bialgebra k A] (f : A →ₗ[k] k) :
    Module.End k A :=
  (TensorProduct.rid k A).toLinearMap.comp ((f.lTensor A).comp comul)

private theorem coalgebraSlice_baseChange {K A : Type u} [Field K] [Algebra k K]
    [CommRing A] [Bialgebra k A] (f : A →ₗ[k] k) :
    (coalgebraSlice f).baseChange K =
      coalgebraSlice (LinearMap.liftBaseChange K ((Algebra.linearMap k K).comp f)) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s a
  change s ⊗ₜ[k] coalgebraSlice f a = _
  simp only [coalgebraSlice, LinearMap.comp_apply, TensorProduct.comul_tmul,
    CommSemiring.comul_apply]
  generalize comul (R := k) a = t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
    change s ⊗ₜ[k] (f y • x) =
      (LinearMap.liftBaseChange K ((Algebra.linearMap k K).comp f) (s ⊗ₜ[k] y)) •
        ((1 : K) ⊗ₜ[k] x)
    rw [← TensorProduct.smul_tmul, LinearMap.liftBaseChange_tmul, TensorProduct.smul_tmul']
    simp [Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

private theorem groupLike_descends_over_purelyInseparable
    {K A I : Type u} [Field K] [Algebra k K] [IsPurelyInseparable k K]
    [CommRing A] [Bialgebra k A]
    (b : Module.Basis I K (K ⊗[k] A)) (hb : ∀ i, IsGroupLikeElem K (b i))
    (x : K ⊗[k] A) (hx : IsGroupLikeElem K x) :
    ∃ a : A, (1 : K) ⊗ₜ[k] a = x := by
  classical
  have hx0 : x ≠ 0 := by
    intro hz
    have he := hx.counit_eq_one
    rw [hz, map_zero] at he
    exact zero_ne_one he
  let b₀ := Module.Free.chooseBasis k A
  let b₁ := b₀.baseChange K
  have hall (f : A →ₗ[k] k) :
      ∃ c : k,
        algebraMap k K c = LinearMap.liftBaseChange K ((Algebra.linearMap k K).comp f) x := by
    let fK := LinearMap.liftBaseChange K ((Algebra.linearMap k K).comp f)
    have he (y : K ⊗[k] A) (hy : IsGroupLikeElem K y) :
        (coalgebraSlice f).baseChange K y = fK y • y := by
      rw [coalgebraSlice_baseChange]
      change (TensorProduct.rid K (K ⊗[k] A)) (fK.lTensor _ (comul y)) = _
      rw [hy.comul_eq_tmul_self, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    exact baseChange_eigenvalue_over_purelyInseparable (coalgebraSlice f) b
      (fun i => fK (b i)) (fun i => he _ (hb i)) x hx0 (fK x) (he x hx)
  have hcoord (i : Module.Free.ChooseBasisIndex k A) :
      LinearMap.liftBaseChange K ((Algebra.linearMap k K).comp (b₀.coord i)) = b₁.coord i := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s a
    simp [b₁, Module.Basis.coord_apply, Algebra.smul_def, mul_comm]
  choose d hd using fun i => hall (b₀.coord i)
  let a : A := ∑ i ∈ (b₁.repr x).support, d i • b₀ i
  refine ⟨a, ?_⟩
  have ha : (1 : K) ⊗ₜ[k] a =
      ∑ i ∈ (b₁.repr x).support, (b₁.repr x i) • b₁ i := by
    simp only [a, TensorProduct.tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Module.Basis.baseChange_apply, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul K,
      hd i, hcoord]
    rfl
  rw [ha]
  exact b₁.linearCombination_repr x

open LinearAlgebraicGroups.CharacterDescent (extendedHopfTower isGroupLikeElem_tmul_one_iff)
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem isTorus_of_geometricallySplit (G : AffineAlgebraicGroup k)
    (hs : Specs.GeometricRadicals.IsSplitTorus (GeometricGroup G).val) :
    Specs.GeometricRadicals.IsTorus G.val := by
  classical
  let K := AlgebraicClosure k
  let E := separableClosure k K
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  obtain ⟨r, ⟨s⟩⟩ := hs
  let M := StandardLattice.{u} r
  obtain ⟨d⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) r
  let f : specGroup (extendedHopf K A) ≅ specGroup (groupAlgebra K M) :=
    extendedGroupIso K A ≪≫ (groupBaseChange k K).mapIso e ≪≫ s ≪≫ d.symm
  let B := extendedHopf E A
  let F := hopfSpec.fullyFaithful (R := CommRingCat.of K)
  let j : groupAlgebra K M ≅ extendedHopf K B :=
    (F.preimageIso f).unop ≪≫ (extendedHopfTower (K := E) K A).symm
  let b := (MonoidAlgebra.basis M K).map (CommHopfAlgCat.ofIso j).toAlgEquiv.toLinearEquiv
  have hb (m : M) : IsGroupLikeElem K (b m) :=
    (MonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K) m).map j.hom.hom
  have hsur : Function.Surjective (baseChangeCharacterMap K B) := by
    intro x
    obtain ⟨y, hy⟩ := groupLike_descends_over_purelyInseparable b hb x.val x.isGroupLikeElem_val
    have hg : IsGroupLikeElem E y := (isGroupLikeElem_tmul_one_iff K B y).mp (hy ▸ x.isGroupLikeElem_val)
    exact ⟨⟨y, hg⟩, GroupLike.val_injective hy⟩
  let w := MulEquiv.ofBijective (baseChangeCharacterMap K B)
    ⟨baseChangeCharacterMap_injective K B, hsur⟩
  have hspan : Submodule.span E (Set.range (GroupLike.val (R := E) (A := B))) = ⊤ := by
    apply top_unique
    intro z _
    by_contra hz
    let V := Submodule.span E (Set.range (GroupLike.val (R := E) (A := B)))
    letI : Module.Free E (B ⧸ V) := Module.Free.of_divisionRing E (B ⧸ V)
    have hpr : Module.Projective E (B ⧸ V) := Module.Projective.of_free
    obtain ⟨l, hlz, hl⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
      (show z ∉ V from hz) hpr
    let lK := LinearMap.liftBaseChange K ((Algebra.linearMap E K).comp l)
    have hlK : lK = 0 := by
      apply b.ext
      intro m
      obtain ⟨y, hy⟩ := hsur ⟨b m, hb m⟩
      have hy' : (1 : K) ⊗ₜ[E] y.val = b m := congrArg GroupLike.val hy
      have hly : l y.val = 0 :=
        by
          have hm : l y.val ∈
              (Submodule.span E (Set.range (GroupLike.val (R := E) (A := B)))).map l :=
            Submodule.mem_map_of_mem (f := l) (Submodule.subset_span (Set.mem_range_self y))
          rw [hl, Submodule.mem_bot] at hm
          exact hm
      change lK (b m) = 0
      rw [← hy']
      simp [lK, hly]
    have hzero := LinearMap.congr_fun hlK ((1 : K) ⊗ₜ[E] z)
    apply hlz
    apply (algebraMap E K).injective
    simpa [lK] using hzero
  let m : M ≃* GroupLike E B :=
    (monomialCharacterEquiv K).trans ((groupLikeIso j).trans w.symm)
  let d' : groupAlgebra E M ≅ groupAlgebra E (GroupLike E B) :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv E E m)
  have hh : Specs.CharacterDescent.IsTorus A :=
    ⟨E, inferInstance, inferInstance, inferInstance, r,
      ⟨d' ≪≫ groupAlgebraOfCharacters B hspan⟩⟩
  exact isTorus_of_groupIso e.symm ((isTorus_spec_iff A).mpr hh)

open private geometricCentralizer from LinearAlgebraicGroups.Reductive.TorusCentralizer
open private torus_split_of_algClosed from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent

private theorem torus_of_central_geometric_maximalTorus
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup (GeometricGroup G).val) (hT : IsMaximalTorus T)
    (hc : IsCentral T.inclusion) : Specs.GeometricRadicals.IsTorus G.val := by
  have hZ := geometricCentralizer
    LinearAlgebraicGroups.Reductive.SubtorusCentralizer.unipotentRadicalInclusion G hG T hT
  obtain ⟨r, hr⟩ := (hZ _ (𝟙 _)).mp (hc _ (𝟙 _))
  letI := T.isClosedImmersion
  letI := isMonHom_of_comp_closed r (𝟙 (GeometricGroup G).val) T.inclusion hr
  let f : (GeometricGroup G).val ⟶ T.group := Grp.homMk r
  have hf : f ≫ T.inclusion = 𝟙 _ := Grp.hom_ext _ _ hr
  letI := isIso_of_subgroup_section T f hf
  apply isTorus_of_geometricallySplit G
  exact torus_split_of_algClosed (GeometricGroup G) (isTorus_of_groupIso (asIso T.inclusion).symm hT.1)

private theorem trivial_isTorus (k : Type u) [Field k] :
    Specs.GeometricRadicals.IsTorus (Grp.trivial (SchemeOver k)) := by
  classical
  let M := StandardLattice.{u} 0
  let A := groupAlgebra k M
  let q := Bialgebra.counitBialgHom k A
  let d : A ≃ₐ[k] k := MonoidAlgebra.uniqueAlgEquiv k M
  have h (c : k) : q (d.symm c) = c := by
    change counit (R := k) ((MonoidAlgebra.uniqueAlgEquiv k M).symm c) = c
    rw [MonoidAlgebra.uniqueAlgEquiv_symm_apply, MonoidAlgebra.counit_single]
    rfl
  have he : (q : A → k) = d := funext fun a =>
    (congrArg q (d.symm_apply_apply a).symm).trans (h (d a))
  have hq : Function.Bijective q := he.symm ▸ d.bijective
  let e : A ≅ CommHopfAlgCat.of k k := CommHopfAlgCat.isoMk (BialgEquiv.ofBijective q hq)
  let S := specGroup (CommHopfAlgCat.of k k)
  have hS : IsTerminal S.X := (Over.mkIdTerminal : IsTerminal (rationalSource k)).ofIso (rationalSourceIso k)
  let f : S ⟶ Grp.trivial (SchemeOver k) := 0
  let e' := hS.uniqueUpToIso (isTerminalTensorUnit (C := SchemeOver k))
  have hf : f.hom.hom = e'.hom := (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  letI : IsIso f.hom.hom := hf.symm ▸ e'.isIso_hom
  letI : IsIso f.hom.hom.left := (Over.forget _).map_isIso f.hom.hom
  letI : IsIso f := isIso_of_schemeIso f
  obtain ⟨j⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) 0
  let t := (asIso f).symm ≪≫ (hopfSpec (CommRingCat.of k)).mapIso e.op ≪≫ j
  exact ⟨k, inferInstance, inferInstance, inferInstance, 0, ⟨(selfBaseChange k).app _ ≪≫ t⟩⟩

open private exists_maximal_torus_over from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem geometricMaximalTorus_exists (G : AffineAlgebraicGroup k) :
    ∃ T : ClosedSubgroup (GeometricGroup G).val, IsMaximalTorus T := by
  obtain ⟨T, hT, _⟩ := exists_maximal_torus_over (GeometricGroup G)
    (Specs.GeometricRadicals.identitySubgroup _) (trivial_isTorus _)
  exact ⟨T, hT⟩

private theorem diagonal_isSemisimple {I : Type u} [Fintype I] [DecidableEq I]
    (d : I → k) : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (Matrix.diagonal d)) := by
  classical
  let S := Finset.univ.image d
  let P : k[X] := ∏ a ∈ S, (Polynomial.X - Polynomial.C a)
  have hsep : P.Separable :=
    Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h => h)
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
  let f : (I → k) →ₐ[k] Module.End k (I → k) :=
    Matrix.toLinAlgEquiv'.toAlgHom.comp (Matrix.diagonalAlgHom k)
  change Polynomial.aeval (f d) P = 0
  rw [Polynomial.aeval_algHom_apply f]
  have he : (Polynomial.aeval d P : I → k) = 0 := by
    funext i
    change (Pi.evalAlgHom k (fun _ : I => k) i) (Polynomial.aeval d P) = 0
    rw [← Polynomial.aeval_algHom_apply (Pi.evalAlgHom k (fun _ : I => k) i)]
    change Polynomial.aeval (d i) P = 0
    simp only [P, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self_apply]
    exact Finset.prod_eq_zero (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) (sub_self _)
  rw [he, map_zero]

open private matrixDiagonal_of_faithfulWeights splitTorus_tangent_probes
  commute_diagonal_of_coordinate_tests pointwise_central_of_affine
  from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent

private theorem characterValue_comp {T S : GroupScheme k} (f : T ⟶ S)
    (χ : Character S) {R : TestAlgebra k} (t : GroupPoints T R) :
    Specs.CentralFrobeniusDescent.characterValue (f ≫ χ) t =
      Specs.CentralFrobeniusDescent.characterValue χ (t ≫ f.hom.hom) := by
  unfold Specs.CentralFrobeniusDescent.characterValue
  simp only [Category.assoc]
  rfl

set_option maxHeartbeats 1000000 in
private theorem central_of_no_geometric_semisimple_charZero [CharZero k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup (GeometricGroup G).val) (hT : IsMaximalTorus T)
    (hn : ¬ HasGeometricNoncentralSemisimple G) : IsCentral T.inclusion := by
  classical
  let K := AlgebraicClosure k
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let A := GeometricGroup G
  let ht := torus_split_of_algClosed (closedSubgroupAlgebraicGroup T) hT.1
  have hsm : Smooth A.val.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hG.1
  have hcon : ConnectedSpace A.val.X.left := by
    letI := hG.2.1
    exact pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace K (fieldSpecMap k K)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hw, _⟩ :=
    LinearAlgebraicGroups.NormalizerLatticeAction.quotientByCentralizer A hsm hcon T hT.1
  obtain ⟨W⟩ := hw ht
  obtain ⟨n, L, l, f, χ, hf, hdiag⟩ :=
    matrixDiagonal_of_faithfulWeights A T.inclusion W.weights W.faithfulWeights
  let I := ULift.{u} (Fin n)
  let L' : AffineGroupCategory K := ⟨L.val, L.property.1⟩
  let Φ := (groupPointsFunctor K).map f ≫ l.hom
  obtain ⟨r, ⟨s⟩⟩ := ht
  obtain ⟨d⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) r
  let M := StandardLattice.{u} r
  let D := specGroup (groupAlgebra K M)
  let e : D ≅ T.group := d ≪≫ s.symm
  let g := e.hom ≫ T.inclusion
  obtain ⟨x, b, hb, hprobe⟩ := splitTorus_tangent_probes (k := K) r
  let w (i : I) : M := b.symm (e.hom ≫ χ i)
  have hwχ (i : I) : b (w i) = e.hom ≫ χ i := b.apply_symm_apply _
  have hdiagD (R : TestAlgebra K) (t : GroupPoints D R) :
      (Φ.app R (t ≫ g.hom.hom) : Matrix.GeneralLinearGroup I R).val =
        Matrix.diagonal (fun i => Specs.CentralFrobeniusDescent.characterValue (b (w i)) t) := by
    have hl := hdiag R (t ≫ e.hom.hom.hom)
    have he : (t ≫ g.hom.hom) ≫ f.hom.hom =
        (t ≫ e.hom.hom.hom) ≫ (T.inclusion ≫ f).hom.hom := by
      change (t ≫ (e.hom.hom.hom ≫ T.inclusion.hom.hom)) ≫ f.hom.hom =
        (t ≫ e.hom.hom.hom) ≫ (T.inclusion.hom.hom ≫ f.hom.hom)
      simp only [Category.assoc]
    change (l.hom.app R ((t ≫ g.hom.hom) ≫ f.hom.hom) :
      Matrix.GeneralLinearGroup I R).val = _
    rw [he, hl]
    congr 1
    funext i
    rw [hwχ, characterValue_comp]
  let a (i : I) (j : Fin r) : K := ((w i j).down.toAdd : K)
  let y (j : Fin r) : Lie K A.val := mapPointKernel g (x j)
  have hmat (j : Fin r) : InfinitesimalCommutator.matrixDifferential f l (y j) =
      Matrix.diagonal (fun i => a i j) := by
    have he := hdiagD (CommAlgCat.of K (DualNumber K)) (x j).toMul.val
    ext i l'
    have h := congrArg (fun m : Matrix I I (DualNumber K) => (m i l').snd) he
    change ((Φ.app _ ((x j).toMul.val ≫ g.hom.hom) :
      Matrix.GeneralLinearGroup I (DualNumber K)).val i l').snd = _
    rw [h]
    by_cases hEq : i = l'
    · subst l'
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hprobe]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hEq, Matrix.diagonal_apply_ne _ hEq]
      rfl
  let sLie : IdentityLieStructure A.val := identityLieStructure A
  have htest (R : TestAlgebra K) (t : GroupPoints A.val R) (j : Fin r) :
      Commute (Φ.app R t : Matrix.GeneralLinearGroup I R).val
        (Matrix.diagonal (fun i => algebraMap K R (a i j))) := by
    have hy : GeometricallySemisimple (InfinitesimalCommutator.matrixDifferential f l (y j)) := by
      unfold GeometricallySemisimple
      rw [hmat, Matrix.diagonal_map (map_zero _)]
      exact diagonal_isSemisimple _
    obtain ⟨C, _, hC, _, hIso⟩ :=
      LinearAlgebraicGroups.SemisimpleLieCentralizer.schemeCentralizerOfSemisimple
        K A L' sLie hsm I l f hf (y j) hy
    letI : IsIso C.inclusion := hIso hcon.toPreconnectedSpace (by
      by_contra hh
      apply hn
      refine ⟨sLie, I, inferInstance, inferInstance, L', l, f, hf, y j, ?_, hh⟩
      rw [hmat]
      exact diagonal_isSemisimple _)
    have hx := (hC R t).mp ((ConcreteCategory.bijective_of_isIso
      (((groupPointsFunctor K).map C.inclusion).app R)).2 t)
    rw [hmat, Matrix.diagonal_map (map_zero _)] at hx
    exact hx
  haveI : IsAffine A.val.X.left := A.property.1
  haveI : IsAffine T.group.X.left := (closedSubgroupAlgebraicGroup T).property.1
  apply pointwise_central_of_affine T.inclusion
  intro R t z
  let z' : GroupPoints D R := z ≫ e.inv.hom.hom
  have hz : z' ≫ g.hom.hom = z ≫ T.inclusion.hom.hom := by
    change (z ≫ e.inv.hom.hom) ≫ e.hom.hom.hom ≫ T.inclusion.hom.hom = _
    have hh : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 T.group.X :=
      (Grp.forget (SchemeOver K)).congr_map e.inv_hom_id
    simp only [Category.assoc, reassoc_of% hh]
  have hu : Function.Injective (Φ.app R) := by
    letI : IsClosedImmersion f.hom.hom.left := hf
    letI : Mono f.hom.hom := Over.mono_of_mono_left _
    exact (ConcreteCategory.bijective_of_isIso (l.hom.app R)).1.comp
      (fun _ _ h => (cancel_mono f.hom.hom).mp h)
  apply hu
  rw [map_mul, map_mul, ← hz]
  apply Matrix.GeneralLinearGroup.ext
  have hcomm : Commute (Φ.app R t : Matrix.GeneralLinearGroup I R).val
      (Φ.app R (z' ≫ g.hom.hom) : Matrix.GeneralLinearGroup I R).val := by
    rw [hdiagD]
    apply commute_diagonal_of_coordinate_tests _ a _ (htest R t)
    intro i j hij
    have he : w i = w j := by
      funext l'
      apply ULift.ext
      apply Multiplicative.toAdd.injective
      exact Int.cast_injective (α := K) (hij l')
    rw [he]
  intro i j
  exact congrArg (fun m : Matrix I I R => m i j) hcomm.eq

private abbrev groupKrullDimension (G : AffineAlgebraicGroup k) : WithBot ℕ∞ :=
  ringKrullDim Γ(G.val.X.left, ⊤)

private theorem groupKrullDimension_bounded (G : AffineAlgebraicGroup k) :
    ∃ n : ℕ, groupKrullDimension G ≤ n := by
  obtain ⟨A, hA, ⟨e⟩⟩ := groupPresentation G
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  let x := ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso e
  let y : Γ(G.val.X.left, ⊤) ≅ CommRingCat.of A :=
    Scheme.Γ.mapIso x.op ≪≫ Scheme.ΓSpecIso (CommRingCat.of A)
  refine ⟨n, ?_⟩
  change ringKrullDim Γ(G.val.X.left, ⊤) ≤ (n : WithBot ℕ∞)
  rw [ringKrullDim_eq_of_ringEquiv y.commRingCatIsoToRingEquiv]
  have h := ringKrullDim_le_of_surjective f.toRingHom hf
  simpa [ringKrullDim_eq_zero_of_field k] using h

private theorem subgroupKrullDimension_succ_le
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (H : ClosedSubgroup G.val)
    (h : ¬ Function.Surjective (mapPointKernel H.inclusion)) :
    groupKrullDimension (closedSubgroupAlgebraicGroup H) + 1 ≤ groupKrullDimension G := by
  let i := H.inclusion.hom.hom.left
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsIntegral G.val.X.left := group_integral_of_reductive G hG
  letI : IsClosedImmersion i := H.isClosedImmersion
  have hn : ¬ Function.Injective i.appTop := by
    intro hi
    letI := IsClosedImmersion.isIso_of_injective_of_isAffine (f := i) hi
    letI := isIso_of_schemeIso H.inclusion
    apply h
    intro x
    refine ⟨mapPointKernel (inv H.inclusion) x, ?_⟩
    rw [← (lieFunctoriality k).2.2, IsIso.inv_hom_id, (lieFunctoriality k).2.1]
  rw [injective_iff_map_eq_zero i.appTop.hom] at hn
  push Not at hn
  obtain ⟨a, ha, hane⟩ := hn
  exact ringKrullDim_succ_le_of_surjective i.appTop.hom
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2 (mem_nonZeroDivisors_of_ne_zero hane) ha

private theorem ringKrullDim_le_of_integral_injective {R S : Type u}
    [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S]
    (ha : Function.Injective (algebraMap R S)) : ringKrullDim R ≤ ringKrullDim S := by
  change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
  rw [Order.krullDim]
  apply iSup_le
  intro l
  letI := l.head.isPrime
  obtain ⟨P, hp, he⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    l.head.asIdeal ((RingHom.injective_iff_ker_eq_bot _).mp ha ▸ bot_le)
  letI := hp
  letI : P.LiesOver l.head.asIdeal := ⟨he.symm⟩
  obtain ⟨m, hm, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hm]
  exact Order.LTSeries.length_le_krullDim m

private theorem groupKrullDimension_le_of_finite_surjective
    (G Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val)
    (hG : IsReductive G) (hQ : IsReductive Q) (hfin : IsFinite q.hom.hom.left)
    (hsur : Surjective q.hom.hom.left) :
    groupKrullDimension Q ≤ groupKrullDimension G := by
  let g := q.hom.hom.left
  letI : IsAffine Q.val.X.left := Q.property.1
  letI : IsIntegral G.val.X.left := group_integral_of_reductive G hG
  letI : IsIntegral Q.val.X.left := group_integral_of_reductive Q hQ
  letI : IsFinite g := hfin
  letI : Surjective g := hsur
  letI := IsSchemeTheoreticallyDominant.of_isDominant g
  let a := g.appTop.hom
  letI : Algebra Γ(Q.val.X.left, ⊤) Γ(G.val.X.left, ⊤) := a.toAlgebra
  letI : Algebra.IsIntegral Γ(Q.val.X.left, ⊤) Γ(G.val.X.left, ⊤) := ⟨g.finite_appTop.to_isIntegral⟩
  exact ringKrullDim_le_of_integral_injective (g.app_injective ⊤)

private theorem generatedByRationalTori_of_reductive
    (hComponent : SemisimpleLieCentralizerComponentReductive.{u}) [Infinite k] :
    ∀ G : AffineAlgebraicGroup k, IsReductive G → GeneratedByRationalTori G := by
  classical
  let P (n : ℕ) := ∀ G : AffineAlgebraicGroup k, groupKrullDimension G ≤ n →
    IsReductive G → GeneratedByRationalTori G
  have hP (n : ℕ) : P n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hdim hG
      let R (Q : AffineAlgebraicGroup k) := groupKrullDimension Q ≤ n → GeneratedByRationalTori Q
      have terminal (Q : AffineAlgebraicGroup k) (hQ : IsReductive Q)
          (T : ClosedSubgroup (GeometricGroup Q).val) (hT : IsMaximalTorus T)
          (h : IsCentral T.inclusion ∨ HasGeometricNoncentralSemisimple Q) : R Q := by
        intro hQdim
        rcases h with hc | hs
        · exact (torus_generatedByRationalTori Q
            (torus_of_central_geometric_maximalTorus Q hQ T hT hc)).1
        · apply generatedByRationalTori_of_noncentral hComponent Q hQ hs
          intro H hH hproper
          let H₀ := closedSubgroupAlgebraicGroup H
          letI : IsIntegral H₀.val.X.left := group_integral_of_reductive H₀ hH
          have hd := (subgroupKrullDimension_succ_le Q hQ H hproper).trans hQdim
          have hn : 0 ≤ groupKrullDimension H₀ := ringKrullDim_nonneg_of_nontrivial
          obtain ⟨z, hz⟩ := WithBot.ne_bot_iff_exists.mp (ne_of_gt ((by simp : (⊥ : WithBot ℕ∞) < 0).trans_le hn))
          have hzn : z ≠ ⊤ := by
            intro he
            change groupKrullDimension H₀ + 1 ≤ (n : WithBot ℕ∞) at hd
            rw [← hz, he, WithBot.coe_top] at hd
            have htop : (⊤ : WithBot ℕ∞) ≤ ⊤ + 1 :=
              le_add_of_nonneg_right (by simp : (0 : WithBot ℕ∞) ≤ 1)
            have hnlt : (n : WithBot ℕ∞) < ⊤ :=
              WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n)
            exact (not_le_of_gt hnlt) (htop.trans hd)
          obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hzn
          have hdimH : (m : WithBot ℕ∞) = groupKrullDimension H₀ :=
            (congrArg (fun a : ℕ∞ => (a : WithBot ℕ∞)) hm).trans hz
          change groupKrullDimension H₀ + 1 ≤ (n : WithBot ℕ∞) at hd
          rw [← hdimH, ← Nat.cast_one, ← Nat.cast_add] at hd
          have hlt : m < n := Nat.lt_of_succ_le (Nat.cast_le.mp hd)
          exact ih m hlt H₀ hdimH.ge hH
      obtain ⟨T, hT⟩ := geometricMaximalTorus_exists G
      obtain ⟨p, hp⟩ := ExpChar.exists k
      letI := hp
      rcases expChar_is_prime_or_one k p with hprime | rfl
      · letI : Fact p.Prime := ⟨hprime⟩
        letI : CharP k p := (expChar_prime_iff k hprime).mp hp
        have step (A Q : AffineAlgebraicGroup k) (q : A.val ⟶ Q.val)
            (hA : IsReductive A) (hQ : IsReductive Q) (hfin : IsFinite q.hom.hom.left)
            (hsur : Surjective q.hom.hom.left) (hlift : LiftsTori q) (hR : R Q) : R A :=
          fun hAdim => generatedByRationalTori_of_finite_torus_lifting A Q q hA hQ hfin hlift
            (hR ((groupKrullDimension_le_of_finite_surjective A Q q hA hQ hfin hsur).trans hAdim))
        exact centralFrobenius_of_terminal p
          LinearAlgebraicGroups.CentralFrobeniusDescent.centralFrobeniusReduction R terminal step G hG T hT hdim
      · letI : CharZero k := charZero_of_expChar_one' k
        exact terminal G hG T hT (Decidable.or_iff_not_imp_right.mpr
          (central_of_no_geometric_semisimple_charZero G hG T hT)) hdim
  intro G hG
  obtain ⟨n, hn⟩ := groupKrullDimension_bounded G
  exact hP n G hn hG

/-- Closed generation by tori defined over the base field, also after scalar
extension to the algebraic closure. -/
theorem reductiveGeneratedByRationalTori_conditional
    (_ : Specs.Relative.ReductiveLieCentralizers.ReductiveOfSymmetricRoots.{u})
    (hComponent : SemisimpleLieCentralizerComponentReductive.{u}) :
    ReductiveGeneratedByRationalTori.{u} := by
  intro k _ _ G hG
  have h := generatedByRationalTori_of_reductive hComponent G hG
  exact ⟨h, geometricallyGeneratedByRationalTori_of_generated G hG h⟩

/-- Geometric density of rational points of a connected reductive group. -/
theorem reductiveRationalPointsDense_conditional
    (hRoots : Specs.Relative.ReductiveLieCentralizers.ReductiveOfSymmetricRoots.{u})
    (hComponent : SemisimpleLieCentralizerComponentReductive.{u}) :
    ReductiveRationalPointsDense.{u} := by
  intro k _ _ G hG
  exact denseRationalPoints_of_generatedByTori G
    (reductiveGeneratedByRationalTori_conditional hRoots hComponent k G hG).1


end

end LinearAlgebraicGroups.Relative.RationalDensity

universe v8_closure_59ae8ca276a9d7de_u0
theorem _root_.«LinearAlgebraicGroups».«Relative».«RationalDensity».«reductiveGeneratedByRationalTori» : _root_.«LinearAlgebraicGroups».«Specs».«Relative».«RationalDensity».«ReductiveGeneratedByRationalTori».{v8_closure_59ae8ca276a9d7de_u0} :=
  @_root_.«LinearAlgebraicGroups».«Relative».«RationalDensity».«reductiveGeneratedByRationalTori_conditional».{v8_closure_59ae8ca276a9d7de_u0} (@_root_.«LinearAlgebraicGroups».«Relative».«ReductiveLieCentralizers».«reductiveOfSymmetricRoots».{v8_closure_59ae8ca276a9d7de_u0}) (@_root_.«LinearAlgebraicGroups».«Relative».«ReductiveLieCentralizers».«semisimpleLieCentralizerComponentReductive».{v8_closure_59ae8ca276a9d7de_u0})
theorem _root_.«LinearAlgebraicGroups».«Relative».«RationalDensity».«reductiveRationalPointsDense» : _root_.«LinearAlgebraicGroups».«Specs».«Relative».«RationalDensity».«ReductiveRationalPointsDense».{v8_closure_59ae8ca276a9d7de_u0} :=
  @_root_.«LinearAlgebraicGroups».«Relative».«RationalDensity».«reductiveRationalPointsDense_conditional».{v8_closure_59ae8ca276a9d7de_u0} (@_root_.«LinearAlgebraicGroups».«Relative».«ReductiveLieCentralizers».«reductiveOfSymmetricRoots».{v8_closure_59ae8ca276a9d7de_u0}) (@_root_.«LinearAlgebraicGroups».«Relative».«ReductiveLieCentralizers».«semisimpleLieCentralizerComponentReductive».{v8_closure_59ae8ca276a9d7de_u0})
theorem _root_.«LinearAlgebraicGroups».«Relative».«RationalDensity».«torusRationalPointsDense» : _root_.«LinearAlgebraicGroups».«Specs».«Relative».«RationalDensity».«TorusRationalPointsDense».{v8_closure_59ae8ca276a9d7de_u0} :=
  @_root_.«LinearAlgebraicGroups».«Relative».«RationalDensity».«torusRationalPointsDense_conditional».{v8_closure_59ae8ca276a9d7de_u0} (@_root_.«LinearAlgebraicGroups».«Relative».«ReductiveLieCentralizers».«reductiveOfSymmetricRoots».{v8_closure_59ae8ca276a9d7de_u0}) (@_root_.«LinearAlgebraicGroups».«Relative».«ReductiveLieCentralizers».«semisimpleLieCentralizerComponentReductive».{v8_closure_59ae8ca276a9d7de_u0})
