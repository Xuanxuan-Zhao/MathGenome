import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.Obj DirectSum TensorProduct CategoryTheory.MonObj LaurentPolynomial

universe u

namespace LinearAlgebraicGroups.CocharacterDynamics

open LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra)
open DiagonalizableFixedLocus WeightDecomposition
open private conjugationAction isFixedBy_conjugation_iff smooth_spec_iff
  coordinateCoaction diagonalSource reflectAction
  weight_induction hom_of_weight weight_mul weight_algebraMap
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private pointHom pointHom_injective centralizes_onAlgebras
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme k}

private theorem limitCentralizerSmooth (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    (cochar : Cocharacter G.val) (D : LimitDecomposition cochar) :
    Smooth D.centralizer.group.X.hom := by
  let := G.property.1
  let : Group.FG IntegerCharacters.{u} :=
    let e : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
    Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  refine DiagonalizableFixedLocus.affineFixedLocusSmooth
    (M := IntegerCharacters) G.val.X (conjugationAction cochar)
    D.centralizer.group.X D.centralizer.inclusion.hom.hom D.centralizer.isClosedImmersion ?_
  intro S g
  exact (isFixedBy_conjugation_iff cochar g).trans (D.centralizer_points S g)

private abbrev affineSpectrum (A : TestAlgebra k) := (testSpec k).obj (op A)

private abbrev specFF (k : Type u) [Field k] :=
  algSpec.fullyFaithful (R := CommRingCat.of k)

private def affinePointEquiv {A : TestAlgebra k} {X : SchemeOver k}
    (e : affineSpectrum A ≅ X) (R : TestAlgebra k) : (A →ₐ[k] R) ≃ Points X R where
  toFun x := (testSpec k).map (CommAlgCat.ofHom x).op ≫ e.hom
  invFun p := ((specFF k).preimage (p ≫ e.inv)).unop.hom
  left_inv x := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Functor.FullyFaithful.preimage_map]
    rfl
  right_inv p := by
    change (testSpec k).map ((specFF k).preimage (p ≫ e.inv)) ≫ e.hom = p
    rw [(specFF k).map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem affinePointEquiv_natural {A : TestAlgebra k} {X : SchemeOver k}
    (e : affineSpectrum A ≅ X) {R S : TestAlgebra k} (f : R ⟶ S) (x : A →ₐ[k] R) :
    affinePointEquiv e S (f.hom.comp x) = mapPoints f (affinePointEquiv e R x) := by
  change (testSpec k).map ((CommAlgCat.ofHom x) ≫ f).op ≫ e.hom = _
  simp only [op_comp, Functor.map_comp, Category.assoc]
  rfl

private theorem smooth_affine_iff {A : TestAlgebra k} {X : SchemeOver k}
    (e : affineSpectrum A ≅ X) : Smooth X.hom ↔ Algebra.Smooth k A := by
  rw [← smooth_spec_iff]
  have h₁ : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have h₂ : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  constructor
  · intro h
    change Smooth (affineSpectrum A).hom
    rw [← Over.w e.hom]
    infer_instance
  · intro h
    rw [← Over.w e.inv]
    infer_instance

private abbrev quotientMap {R : Type u} [CommRing R] [Algebra k R] (I : Ideal R) :
    CommAlgCat.of k R ⟶ CommAlgCat.of k (R ⧸ I) :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)

private theorem affineSmooth_iff_lifts (X : SchemeOver k) (ha : IsAffine X.left)
    (hf : LocallyOfFiniteType X.hom) :
    Smooth X.hom ↔ ∀ (R : Type u) [CommRing R] [Algebra k R]
      (I : Ideal R), I ^ 2 = ⊥ →
      Function.Surjective (mapPoints (X := X) (quotientMap (k := k) I)) := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha
  let e' : affineSpectrum A.unop ≅ X := e
  have : IsIso e'.hom.left := (Over.forget _).map_isIso e'.hom
  have ht : LocallyOfFiniteType (affineSpectrum A.unop).hom := by
    rw [← Over.w e'.hom]
    infer_instance
  have hft : Algebra.FiniteType k A.unop := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A.unop))) at ht
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at ht
    exact RingHom.finiteType_algebraMap.mp ht
  rw [smooth_affine_iff e']
  constructor
  · intro h R _ _ I hI x
    obtain ⟨g, hg⟩ := Algebra.FormallySmooth.iff_comp_surjective.mp
      (inferInstance : Algebra.FormallySmooth k A.unop) I hI
      ((affinePointEquiv e' _).symm x)
    refine ⟨affinePointEquiv e' _ g, ?_⟩
    rw [← affinePointEquiv_natural, show (quotientMap I).hom.comp g = _ from hg,
      Equiv.apply_symm_apply]
  · intro h
    constructor
    · apply Algebra.FormallySmooth.iff_comp_surjective.mpr
      intro R _ _ I hI x
      obtain ⟨y, hy⟩ := h R I hI (affinePointEquiv e' _ x)
      refine ⟨(affinePointEquiv e' _).symm y, (affinePointEquiv e' (CommAlgCat.of k (R ⧸ I))).injective ?_⟩
      change affinePointEquiv e' _ ((quotientMap I).hom.comp ((affinePointEquiv e' _).symm y)) = _
      rw [affinePointEquiv_natural e' (quotientMap I), Equiv.apply_symm_apply, hy]
    · exact Algebra.FinitePresentation.of_finiteType.mp hft

private theorem contractingSmooth_of_parabolic (G : AffineAlgebraicGroup k)
    (cochar : Cocharacter G.val) (D : LimitDecomposition cochar)
    (hP : Smooth D.parabolic.group.X.hom) : Smooth D.contracting.group.X.hom := by
  let P := affineAlgebraicSubgroup D.parabolic G.property.1 G.property.2.1 G.property.2.2
  let U := affineAlgebraicSubgroup D.contracting G.property.1 G.property.2.1 G.property.2.2
  have hLift := (affineSmooth_iff_lifts P.val.X P.property.1 P.property.2.1).mp hP
  apply (affineSmooth_iff_lifts U.val.X U.property.1 U.property.2.1).mpr
  let m := multiplyFactors D.sectionMap D.contractingToParabolic
  let : IsIso m := D.product_iso
  let r := inv m ≫ snd D.centralizer.group.X D.contracting.group.X
  let j := lift (1 : D.contracting.group.X ⟶ D.centralizer.group.X) (𝟙 D.contracting.group.X)
  have hjs : j ≫ m = D.contractingToParabolic.hom.hom := by
    change j ≫ ((fst _ _ ≫ D.sectionMap.hom.hom) *
      (snd _ _ ≫ D.contractingToParabolic.hom.hom)) = _
    simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, j, MonObj.one_comp, one_mul, Category.id_comp]
  have hright : D.contractingToParabolic.hom.hom ≫ r = 𝟙 D.contracting.group.X := by
    rw [← hjs, Category.assoc]
    simp [r, j]
  intro R _ _ I hI x
  change Points D.contracting.group.X (CommAlgCat.of k (R ⧸ I)) at x
  obtain ⟨y, hy⟩ := hLift R I hI (x ≫ D.contractingToParabolic.hom.hom)
  refine ⟨y ≫ r, ?_⟩
  change (testSpec k).map (quotientMap I).op ≫ y ≫ r = x
  rw [← Category.assoc, show (testSpec k).map (quotientMap I).op ≫ y = _ from hy,
    Category.assoc, hright, Category.comp_id]

section Lifting

variable {A R : Type u} [CommRing A] [Algebra k A] [CommRing R] [Algebra k R]

private abbrev exponent (m : IntegerCharacters.{u}) : ℤ := m.down.toAdd

private theorem liftAlongSquareZero {B C : Type u} [CommRing B] [Algebra k B]
    [CommRing C] [Algebra k C] [Algebra.FormallySmooth k A]
    (q : B →ₐ[k] C) (hq : Function.Surjective q) (hsq : RingHom.ker q ^ 2 = ⊥)
    (f : A →ₐ[k] C) : ∃ g : A →ₐ[k] B, q.comp g = f := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hq
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.iff_comp_surjective.mp
    (inferInstance : Algebra.FormallySmooth k A) (RingHom.ker q) hsq (e.symm.toAlgHom.comp f)
  refine ⟨g, AlgHom.ext fun a ↦ ?_⟩
  have hh := congrArg e (DFunLike.congr_fun hg a)
  change e (Ideal.Quotient.mk (RingHom.ker q) (g a)) = e (e.symm (f a)) at hh
  rw [e.apply_symm_apply] at hh
  exact hh

private theorem squareZero_polynomialKer (I : Ideal R) (hI : I ^ 2 = ⊥) :
    RingHom.ker (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ k I)) ^ 2 = ⊥ := by
  rw [pow_two, ← le_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have hc (p : Polynomial R) (hp : Polynomial.mapAlgHom (Ideal.Quotient.mkₐ k I) p = 0)
      (j : ℕ) : p.coeff j ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := congrArg (fun p : Polynomial (R ⧸ I) ↦ p.coeff j) hp
    simpa only [Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_zero,
      Ideal.Quotient.mkₐ_eq_mk] using hh
  change a * b = 0
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_mul, Polynomial.coeff_zero]
  apply Finset.sum_eq_zero
  intro ij _
  have hmem := Ideal.mul_mem_mul (hc a ha ij.1) (hc b hb ij.2)
  simpa [← pow_two, hI] using hmem

/-- Project a lift into the prescribed degrees. Every product of two
off-degree coefficients vanishes in the square-zero ideal. -/
private theorem liftNonnegativeWeights [Algebra.FormallySmooth k A]
    (ρ : CoordinateCoaction (k := k) (M := IntegerCharacters.{u}) (A := A))
    (I : Ideal R) (hI : I ^ 2 = ⊥) (f : A →ₐ[k] (R ⧸ I))
    (hneg : ∀ m, exponent m < 0 → ∀ x ∈ weightSpace ρ.toRightComodule m, f x = 0)
    (p : A →ₐ[k] Polynomial (R ⧸ I))
    (hp : ∀ m x, x ∈ weightSpace ρ.toRightComodule m →
      p x = if 0 ≤ exponent m then Polynomial.monomial (exponent m).toNat (f x) else 0) :
    ∃ g : A →ₐ[k] R, (Ideal.Quotient.mkₐ k I).comp g = f ∧
      ∀ m, exponent m < 0 → ∀ x ∈ weightSpace ρ.toRightComodule m, g x = 0 := by
  let q := Ideal.Quotient.mkₐ k I
  let Q := Polynomial.mapAlgHom q
  obtain ⟨lifted, hlifted⟩ := liftAlongSquareZero Q
    (Polynomial.map_surjective q.toRingHom (Ideal.Quotient.mkₐ_surjective k I))
    (squareZero_polynomialKer I hI) p
  let W := weightSpace ρ.toRightComodule
  let : DecidableEq IntegerCharacters.{u} := fun m n ↦ Classical.propDecidable (m = n)
  let : DirectSum.Decomposition W := (weightDecomposition ρ.toRightComodule).chooseDecomposition
  let c (n : ℕ) : Polynomial R →ₗ[k] R := (Polynomial.lcoeff R n).restrictScalars k
  let h (m : IntegerCharacters.{u}) : W m →ₗ[k] R :=
    if 0 ≤ exponent m then c (exponent m).toNat ∘ₗ lifted.toLinearMap ∘ₗ (W m).subtype else 0
  let L := (DirectSum.toModule k IntegerCharacters R h).comp
    (DirectSum.decomposeLinearEquiv W).toLinearMap
  have onWeight {m x} (hx : x ∈ W m) :
      L x = if 0 ≤ exponent m then (lifted x).coeff (exponent m).toNat else 0 := by
    change DirectSum.toModule k IntegerCharacters R h (DirectSum.decompose W x) = _
    rw [DirectSum.decompose_of_mem W hx]
    change DirectSum.toModule k IntegerCharacters R h
      (DirectSum.lof k IntegerCharacters (fun i ↦ ↥(W i)) m (⟨x, hx⟩ : W m)) = _
    rw [DirectSum.toModule_lof]
    by_cases ht : 0 ≤ exponent m <;> simp [h, c, ht]
  have offDegree {m x} (hx : x ∈ W m) (n : ℕ) (hn : (n : ℤ) ≠ exponent m) :
      (lifted x).coeff n ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := congrArg (fun p : Polynomial (R ⧸ I) ↦ p.coeff n)
      (DFunLike.congr_fun hlifted x)
    change (Q (lifted x)).coeff n = (p x).coeff n at he
    rw [Polynomial.coeff_mapAlgHom_apply, hp m x hx] at he
    change q ((lifted x).coeff n) = _
    rw [he]
    by_cases ht : 0 ≤ exponent m
    · have hne : (exponent m).toNat ≠ n := by omega
      simp [ht, Polynomial.coeff_monomial, hne]
    · simp [ht]
  have hmulWeight (m n) (x y : A) (hx : x ∈ W m) (hy : y ∈ W n) :
      L (x * y) = L x * L y := by
    rw [onWeight (weight_mul ρ hx hy), onWeight hx, onWeight hy]
    have hmn : exponent (m * n) = exponent m + exponent n := rfl
    rw [hmn]
    by_cases hsum : 0 ≤ exponent m + exponent n
    · rw [ite_eq_left hsum, map_mul, Polynomial.coeff_mul]
      let d := (exponent m + exponent n).toNat
      change (∑ ij ∈ Finset.antidiagonal d, (lifted x).coeff ij.1 * (lifted y).coeff ij.2) = _
      have hs (ij : ℕ × ℕ) (hij : ij ∈ Finset.antidiagonal d) (hne : (ij.1 : ℤ) ≠ exponent m) :
          (lifted x).coeff ij.1 * (lifted y).coeff ij.2 = 0 := by
        have hadd := Finset.mem_antidiagonal.mp hij
        have hne' : (ij.2 : ℤ) ≠ exponent n := by dsimp [d] at hadd; omega
        have hmem := Ideal.mul_mem_mul (offDegree hx ij.1 hne) (offDegree hy ij.2 hne')
        simpa [← pow_two, hI] using hmem
      by_cases hm : 0 ≤ exponent m <;> by_cases hn : 0 ≤ exponent n
      · simp only [hm, hn, ite_true]
        let ij := ((exponent m).toNat, (exponent n).toNat)
        have hij : ij ∈ Finset.antidiagonal d := Finset.mem_antidiagonal.mpr (by
          dsimp [ij, d]; omega)
        rw [Finset.sum_eq_single_of_mem ij hij]
        intro ab hab hne
        apply hs ab hab
        intro he
        have hadd := Finset.mem_antidiagonal.mp hab
        apply hne
        apply Prod.ext <;> dsimp [ij, d] at * <;> omega
      · simp only [hm, hn, ite_true, ite_false, mul_zero]
        apply Finset.sum_eq_zero
        intro ij hij
        apply hs ij hij
        have hadd := Finset.mem_antidiagonal.mp hij
        dsimp [d] at hadd
        omega
      · simp only [hm, hn, ite_true, ite_false, zero_mul]
        exact Finset.sum_eq_zero fun ij hij ↦ hs ij hij (by omega)
      · omega
    · rw [ite_eq_right hsum]
      by_cases hm : 0 ≤ exponent m
      · have hn : ¬ 0 ≤ exponent n := by omega
        simp [hm, hn]
      · simp [hm]
  have hmul (x y : A) : L (x * y) = L x * L y := by
    refine weight_induction ρ (fun x ↦ ∀ y, L (x * y) = L x * L y) ?_ (by simp) ?_ y
    · intro m a ha y
      refine weight_induction ρ (fun y ↦ L (a * y) = L a * L y)
        (hmulWeight m · a · ha ·) (by simp) ?_
      intro b c hb hc
      rw [mul_add, map_add, hb, hc, map_add, mul_add]
    · intro a b ha hb y
      rw [add_mul, map_add, ha, hb, map_add, add_mul]
  have hscalar (a : k) : L (algebraMap k A a) = algebraMap k R a := by
    rw [onWeight (weight_algebraMap ρ a), show exponent (1 : IntegerCharacters.{u}) = 0 from rfl,
      ite_eq_left le_rfl, Int.toNat_zero, lifted.commutes]
    change (Polynomial.C (algebraMap k R a)).coeff 0 = _
    exact Polynomial.coeff_C_zero
  let g : A →ₐ[k] R :=
    { toFun := L
      map_zero' := map_zero L
      map_add' := map_add L
      map_mul' := hmul
      map_one' := by simpa using hscalar 1
      commutes' := hscalar }
  refine ⟨g, AlgHom.ext fun x ↦ ?_, fun m hm x hx ↦ ?_⟩
  · change q (L x) = f x
    refine weight_induction ρ (fun x ↦ q (L x) = f x) ?_ (by simp) ?_
    · intro m x hx
      rw [onWeight hx]
      have e := DFunLike.congr_fun hlifted x
      change Q (lifted x) = p x at e
      by_cases hm : 0 ≤ exponent m
      · rw [ite_eq_left hm, ← Polynomial.coeff_mapAlgHom_apply, e, hp m x hx, ite_eq_left hm]
        simp
      · rw [ite_eq_right hm, map_zero]
        -- A negative-weight coordinate is zero in the prescribed point.
        exact (hneg m (lt_of_not_ge hm) x hx).symm
    · intro a b ha hb
      simp only [map_add, ha, hb]
  · change L x = 0
    rw [onWeight hx, ite_eq_right (not_le.mpr hm)]

end Lifting

section CoordinateOrbit

private abbrev characterRing (k : Type u) [Field k] := MonoidAlgebra k IntegerCharacters.{u}

private abbrev affineConjugation {A : TestAlgebra k} (e : affineSpectrum A ≅ G.X)
    (cochar : Cocharacter G) :
    ModObj (specGroup (groupAlgebra k IntegerCharacters)).X (affineSpectrum A) :=
  let T := (specGroup (groupAlgebra k IntegerCharacters)).X
  letI := conjugationAction cochar
  letI : IsMonHom (Iso.refl T).hom := by change IsMonHom (𝟙 T); infer_instance
  ModObj.ofIso (Iso.refl T) e.symm

local instance testSpecIsBraided (k : Type u) [Field k] : (testSpec k).Braided :=
  braidedAlgSpec (R := CommRingCat.of k)

private abbrev reflectedConjugation {A : TestAlgebra k} (e : affineSpectrum A ≅ G.X)
    (cochar : Cocharacter G) :=
  reflectAction (testSpec k) (specFF k) (diagonalSource (k := k) (M := IntegerCharacters))
    (op A) (affineConjugation e cochar)

private abbrev conjugationCoaction {A : TestAlgebra k} (e : affineSpectrum A ≅ G.X)
    (cochar : Cocharacter G) : CoordinateCoaction (k := k) (M := IntegerCharacters) (A := A) :=
  coordinateCoaction (reflectedConjugation e cochar)

private theorem parameter_zpow (R : TestAlgebra k) (n : ℤ) :
    (laurentParameter R ^ n).val = LaurentPolynomial.T n := by
  let t : Multiplicative ℤ →* (laurentAlgebra R)ˣ :=
    { toFun := fun n ↦
        { val := LaurentPolynomial.T n.toAdd
          inv := LaurentPolynomial.T (-n.toAdd)
          val_inv := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
          inv_val := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero] }
      map_one' := Units.ext LaurentPolynomial.T_zero
      map_mul' := fun m n ↦ Units.ext (LaurentPolynomial.T_add m.toAdd n.toAdd) }
  have h := t.map_zpow (Multiplicative.ofAdd 1) n
  have hh := congrArg Units.val h.symm
  change (laurentParameter R ^ n).val = LaurentPolynomial.T ((Multiplicative.ofAdd (1 : ℤ) ^ n).toAdd) at hh
  simpa only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, mul_one, Int.cast_id, id_eq] using hh

private def orbitCoordinates {A : TestAlgebra k} (e : affineSpectrum A ≅ G.X)
    (cochar : Cocharacter G) {R : TestAlgebra k} (f : A →ₐ[k] R) :
    A →ₐ[k] LaurentPolynomial R :=
  (affinePointEquiv e (laurentAlgebra R)).symm (orbit cochar (affinePointEquiv e R f))

private theorem orbitCoordinates_onWeight {A : TestAlgebra k} (e : affineSpectrum A ≅ G.X)
    (cochar : Cocharacter G) {R : TestAlgebra k} (f : A →ₐ[k] R)
    {m : IntegerCharacters.{u}} {x : A}
    (hx : x ∈ weightSpace (conjugationCoaction e cochar).toRightComodule m) :
    orbitCoordinates e cochar f x = LaurentPolynomial.C (f x) * LaurentPolynomial.T (exponent m) := by
  let B := characterRing k
  let F := testSpec k
  let T := op (CommAlgCat.of k B)
  let X := op A
  let a := affineConjugation e cochar
  let l := (reflectedConjugation e cochar).smul
  let s : op (laurentAlgebra R) ⟶ T :=
    (CommAlgCat.ofHom (unitCoordinates (laurentAlgebra R) (laurentParameter R))).op
  let c : op (laurentAlgebra R) ⟶ X := ((CommAlgCat.ofHom f) ≫ laurentConstants R).op
  have hm : F.map l = prodComparison F T X ≫ a.smul := by
    change F.map ((specFF k).preimage (Functor.OplaxMonoidal.δ F T X ≫ a.smul)) = _
    rw [(specFF k).map_preimage, Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
  have hpair : F.map (lift s c) ≫ prodComparison F T X = lift (F.map s) (F.map c) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, prodComparison_fst, ← F.map_comp, lift_fst]
    · simp only [Category.assoc, prodComparison_snd, ← F.map_comp, lift_snd]
  have heq : affinePointEquiv e (laurentAlgebra R) ((lift s c ≫ l).unop.hom) =
      orbit cochar (affinePointEquiv e R f) := by
    change F.map (lift s c ≫ l) ≫ e.hom = _
    rw [F.map_comp, hm, ← Category.assoc, hpair]
    have htransport :
        a.smul ≫ e.hom = (𝟙 (F.obj T) ⊗ₘ e.hom) ≫ (conjugationAction cochar).smul := by
      change ((𝟙 (F.obj T) ⊗ₘ e.hom) ≫ (conjugationAction cochar).smul ≫ e.inv) ≫ e.hom = _
      simp
    rw [Category.assoc, htransport]
    change lift (F.map s) (F.map c) ≫
      (𝟙 (F.obj T) ⊗ₘ e.hom) ≫ cochar.hom.hom ▷ G.X ≫ GrpObj.conj G.X = _
    simp only [lift_map_assoc, lift_whiskerRight_assoc, Category.comp_id,
      GrpObj.conj, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]
    rw [show F.map c = F.map (laurentConstants R).op ≫ F.map (CommAlgCat.ofHom f).op by
      change F.map ((CommAlgCat.ofHom f) ≫ laurentConstants R).op = _
      rw [op_comp, F.map_comp]]
    rfl
  rw [orbitCoordinates, ← heq, Equiv.symm_apply_apply]
  have hweight := hom_of_weight (conjugationCoaction e cochar) hx
  change (Algebra.TensorProduct.comm k B A) (l.unop.hom x) =
    x ⊗ₜ[k] MonoidAlgebra.of k IntegerCharacters m at hweight
  have hu : l.unop.hom x = MonoidAlgebra.of k IntegerCharacters m ⊗ₜ[k] x := by
    apply (Algebra.TensorProduct.comm k B A).injective
    rw [hweight, Algebra.TensorProduct.comm_tmul]
  change (lift s c).unop.hom (l.unop.hom x) = _
  rw [hu, CommAlgCat.lift_unop_hom]
  change Algebra.TensorProduct.lift
    (unitCoordinates (laurentAlgebra R) (laurentParameter R))
    ((laurentConstants R).hom.comp f) (fun _ _ ↦ .all _ _)
    (MonoidAlgebra.of k IntegerCharacters m ⊗ₜ[k] x) = _
  rw [Algebra.TensorProduct.lift_tmul, mul_comm]
  change LaurentPolynomial.C (f x) *
    unitCoordinates (laurentAlgebra R) (laurentParameter R) (MonoidAlgebra.of k IntegerCharacters m) = _
  congr 1
  rw [unitCoordinates, MonoidAlgebra.lift_of]
  exact parameter_zpow R (exponent m)

private theorem orbitCoordinates_lift_iff {A : TestAlgebra k} (e : affineSpectrum A ≅ G.X)
    (cochar : Cocharacter G) {R : TestAlgebra k} (f : A →ₐ[k] R) :
    HasExtension cochar (affinePointEquiv e R f) ↔
      ∃ p : A →ₐ[k] Polynomial R,
        (polynomialToLaurent R).hom.comp p = orbitCoordinates e cochar f := by
  constructor
  · rintro ⟨z, y, hy, _⟩
    let p := (affinePointEquiv e (polynomialAlgebra R)).symm y
    refine ⟨p, (affinePointEquiv e (laurentAlgebra R)).injective ?_⟩
    rw [affinePointEquiv_natural, Equiv.apply_symm_apply, orbitCoordinates, Equiv.apply_symm_apply]
    exact hy
  · rintro ⟨p, hp⟩
    let y : GroupPoints G (polynomialAlgebra R) := affinePointEquiv e (polynomialAlgebra R) p
    refine ⟨mapPoints (polynomialEvaluate R 0) y, y, ?_, rfl⟩
    rw [← affinePointEquiv_natural e (polynomialToLaurent R) p, hp,
      orbitCoordinates, Equiv.apply_symm_apply]

private theorem orbitCoordinates_neg_iff {A : TestAlgebra k} (e : affineSpectrum A ≅ G.X)
    (cochar : Cocharacter G) {R : TestAlgebra k} (f : A →ₐ[k] R) :
    HasExtension cochar (affinePointEquiv e R f) ↔
      ∀ m, exponent m < 0 → ∀ x ∈ weightSpace (conjugationCoaction e cochar).toRightComodule m,
        f x = 0 := by
  classical
  rw [orbitCoordinates_lift_iff]
  change (∃ p, (Polynomial.toLaurentAlg.restrictScalars k).comp p = _) ↔ _
  rw [exists_polynomialLift_iff]
  constructor
  · intro h m hm x hx
    specialize h x (exponent m) hm
    rw [orbitCoordinates_onWeight e cochar f hx, ← LaurentPolynomial.single_eq_C_mul_T] at h
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using h
  · intro h x n hn
    refine weight_induction (conjugationCoaction e cochar)
      (fun x ↦ (orbitCoordinates e cochar f x).coeff n = 0) ?_ (by simp) ?_
    · intro m a ha
      rw [orbitCoordinates_onWeight e cochar f ha, ← LaurentPolynomial.single_eq_C_mul_T]
      by_cases hm : exponent m = n
      · simp [hm, h m (hm.symm ▸ hn) a ha]
      · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right hm]
    · intro a b ha hb
      rw [map_add]
      exact show (orbitCoordinates e cochar f a).coeff n +
        (orbitCoordinates e cochar f b).coeff n = 0 by rw [ha, hb, add_zero]

private theorem parabolicSmooth (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    (cochar : Cocharacter G.val) (D : LimitDecomposition cochar) :
    Smooth D.parabolic.group.X.hom := by
  let P := affineAlgebraicSubgroup D.parabolic G.property.1 G.property.2.1 G.property.2.2
  apply (affineSmooth_iff_lifts P.val.X P.property.1 P.property.2.1).mpr
  obtain ⟨A, ⟨e₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr G.property.1
  let e : affineSpectrum A.unop ≅ G.val.X := e₀
  let : Algebra.Smooth k A.unop := (smooth_affine_iff e).mp inferInstance
  intro R _ _ I hI x
  let R₀ := CommAlgCat.of k (R ⧸ I)
  let R₁ := CommAlgCat.of k R
  let y := pointHom D.parabolic.inclusion R₀ x
  let f := (affinePointEquiv e R₀).symm y
  have hf : affinePointEquiv e R₀ f = y := Equiv.apply_symm_apply _ _
  have hy : HasExtension cochar (affinePointEquiv e R₀ f) := by
    rw [hf]
    exact (D.parabolic_points _ y).mpr ⟨x, rfl⟩
  have hneg := (orbitCoordinates_neg_iff e cochar f).mp hy
  obtain ⟨p, hp⟩ := (orbitCoordinates_lift_iff e cochar f).mp hy
  have hweight (m) (a : A.unop) (ha : a ∈ weightSpace
      (conjugationCoaction e cochar).toRightComodule m) :
      p a = if 0 ≤ exponent m then Polynomial.monomial (exponent m).toNat (f a) else 0 := by
    apply Polynomial.toLaurent_injective
    change (polynomialToLaurent R₀).hom (p a) = _
    rw [← AlgHom.comp_apply, hp, orbitCoordinates_onWeight e cochar f ha]
    by_cases hm : 0 ≤ exponent m
    · simp [hm, Int.toNat_of_nonneg hm]
    · simp [hm, hneg m (lt_of_not_ge hm) a ha]
  obtain ⟨g, hg, hgneg⟩ := liftNonnegativeWeights (conjugationCoaction e cochar) I hI f hneg p hweight
  obtain ⟨x', hx'⟩ := (D.parabolic_points R₁ _).mp
    ((orbitCoordinates_neg_iff e cochar g).mpr hgneg)
  refine ⟨x', pointHom_injective D.parabolic R₀ ?_⟩
  change mapPoints (quotientMap I) x' ≫ D.parabolic.inclusion.hom.hom = y
  rw [show mapPoints (quotientMap I) x' ≫ D.parabolic.inclusion.hom.hom =
    mapPoints (quotientMap I) (pointHom D.parabolic.inclusion R₁ x') by
      exact Category.assoc _ _ _]
  rw [hx', ← affinePointEquiv_natural, show (quotientMap I).hom.comp g = f from hg, hf]

end CoordinateOrbit

theorem limitSubgroupsSmooth : Specs.CocharacterDynamics.LimitSubgroupsSmooth.{u} := by
  intro k _ G _ cochar D
  have hP := parabolicSmooth G cochar D
  exact ⟨hP, contractingSmooth_of_parabolic G cochar D hP, limitCentralizerSmooth G cochar D⟩

section ContractingAction

open private evalLaurent orbit_eval cocharacterPoint_mul centralizes_hasLimit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private closedImmersion_over_affineSpec factorsThrough_affineQuotient
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes

private theorem polynomialToLaurent_evaluate_one (R : TestAlgebra k) :
    polynomialToLaurent R ≫ evalLaurent (𝟙 R) 1 = polynomialEvaluate R 1 := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro p
  change LaurentPolynomial.eval₂ (RingHom.id R) 1 p.toLaurent =
    (Polynomial.aevalTower (AlgHom.id k R) 1) p
  rw [LaurentPolynomial.eval₂_toLaurent]
  rfl

private theorem hasLimit_conjugate (cochar : Cocharacter G) {R : TestAlgebra k}
    {g : GroupPoints G R} (h : HasLimit cochar g 1) (s : Rˣ) :
    HasLimit cochar (cocharacterPoint cochar R s * g * (cocharacterPoint cochar R s)⁻¹) 1 := by
  let c := cocharacterPoint cochar R s
  have hc : Centralizes cochar c := by
    apply (centralizes_onAlgebras cochar c).mpr
    intro S a t
    rw [show mapPoints a c = cocharacterPoint cochar S (Units.map a.hom.toMonoidHom s) from
      mapPoints_cocharacterPoint a cochar s]
    show _ * _ = _ * _
    rw [← cocharacterPoint_mul, ← cocharacterPoint_mul, mul_comm]
  have h₀ := centralizes_hasLimit cochar hc
  simpa only [mul_one, mul_inv_cancel] using (h₀.mul h).mul h₀.inv

private theorem polynomial_factorsThrough {X Y : SchemeOver k} (ha : IsAffine X.left)
    (i : Y ⟶ X) (hi : IsClosedImmersion i.left) {R : TestAlgebra k}
    (p : Points X (polynomialAlgebra R))
    (h : ∃ q : Points Y (laurentAlgebra R), q ≫ i = mapPoints (polynomialToLaurent R) p) :
    ∃ q : Points Y (polynomialAlgebra R), q ≫ i = p := by
  obtain ⟨A, ⟨e₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha
  let e : affineSpectrum A.unop ≅ X := e₀
  let j := i ≫ e.inv
  have hj : IsClosedImmersion j.left := IsClosedImmersion.comp i.left e.inv.left
  obtain ⟨I, s, hs⟩ := closedImmersion_over_affineSpec j hj
  have fact {S : TestAlgebra k} (g : Points X S) :
      (∃ q : Points Y S, q ≫ i = g) ↔ I ≤ RingHom.ker ((affinePointEquiv e S).symm g) := by
    change _ ↔ I ≤ RingHom.ker ((specFF k).preimage (g ≫ e.inv)).unop.hom
    rw [← factorsThrough_affineQuotient I (g ≫ e.inv)]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q ≫ s.hom, ?_⟩
      rw [Category.assoc, ← hs, ← Category.assoc, hq]
    · rintro ⟨q, hq⟩
      refine ⟨q ≫ s.inv, (cancel_mono e.inv).mp ?_⟩
      rw [Category.assoc, Category.assoc, show i ≫ e.inv = j from rfl, hs,
        Iso.inv_hom_id_assoc, hq]
  rw [fact] at h ⊢
  have hn : (affinePointEquiv e (laurentAlgebra R)).symm (mapPoints (polynomialToLaurent R) p) =
      (polynomialToLaurent R).hom.comp ((affinePointEquiv e (polynomialAlgebra R)).symm p) := by
    apply (affinePointEquiv e (laurentAlgebra R)).injective
    rw [Equiv.apply_symm_apply, affinePointEquiv_natural, Equiv.apply_symm_apply]
  rw [hn] at h
  intro a ha
  apply Polynomial.toLaurent_injective
  exact (h ha).trans (map_zero Polynomial.toLaurent).symm

private theorem polynomialContract_exists (ha : IsAffine G.X.left)
    (cochar : Cocharacter G) (D : LimitDecomposition cochar)
    {R : TestAlgebra k} (x : GroupPoints D.contracting.group R) :
    ∃ p : GroupPoints D.contracting.group (polynomialAlgebra R),
      mapPoints (polynomialToLaurent R) (pointHom D.contracting.inclusion _ p) =
        orbit cochar (pointHom D.contracting.inclusion R x) := by
  let g := pointHom D.contracting.inclusion R x
  have h := (D.contracting_points R g).mpr ⟨x, rfl⟩
  obtain ⟨p, hp, _⟩ := (D.contracting_points R g).mpr ⟨x, rfl⟩
  have horbit : HasLimit cochar (orbit cochar g) 1 := by
    have hh := h.map (laurentConstants R)
    have hh' : HasLimit cochar (mapPoints (laurentConstants R) g) 1 := by
      change HasLimit cochar _ ((((groupPointsFunctor k).obj G).map (laurentConstants R)).hom 1) at hh
      simpa only [map_one] using hh
    exact hasLimit_conjugate cochar hh' (laurentParameter R)
  obtain ⟨q, hq⟩ := (D.contracting_points _ _).mp horbit
  obtain ⟨y, hy⟩ := polynomial_factorsThrough ha D.contracting.inclusion.hom.hom
    D.contracting.isClosedImmersion p ⟨q, hq.trans hp.symm⟩
  refine ⟨y, ?_⟩
  change mapPoints (polynomialToLaurent R) (y ≫ D.contracting.inclusion.hom.hom) = _
  rw [hy, hp]

private def polynomialContract (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    (D : LimitDecomposition cochar) {R : TestAlgebra k} (x : GroupPoints D.contracting.group R) :
    GroupPoints D.contracting.group (polynomialAlgebra R) :=
  (polynomialContract_exists ha cochar D x).choose

private theorem polynomialContract_restrict (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    (D : LimitDecomposition cochar) {R : TestAlgebra k} (x : GroupPoints D.contracting.group R) :
    mapPoints (polynomialToLaurent R) (pointHom D.contracting.inclusion _
      (polynomialContract ha cochar D x)) = orbit cochar (pointHom D.contracting.inclusion R x) :=
  (polynomialContract_exists ha cochar D x).choose_spec

private theorem polynomialContract_eq (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    (D : LimitDecomposition cochar) {R : TestAlgebra k} (x : GroupPoints D.contracting.group R)
    (p : GroupPoints D.contracting.group (polynomialAlgebra R))
    (hp : mapPoints (polynomialToLaurent R) (pointHom D.contracting.inclusion _ p) =
      orbit cochar (pointHom D.contracting.inclusion R x)) :
    polynomialContract ha cochar D x = p := by
  apply pointHom_injective D.contracting (polynomialAlgebra R)
  exact polynomialFamily_injective ha R ((polynomialContract_restrict ha cochar D x).trans hp.symm)

private theorem polynomialContract_mul (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    (D : LimitDecomposition cochar) {R : TestAlgebra k} (x y : GroupPoints D.contracting.group R) :
    polynomialContract ha cochar D (x * y) =
      polynomialContract ha cochar D x * polynomialContract ha cochar D y := by
  apply polynomialContract_eq
  rw [map_mul]
  change (((groupPointsFunctor k).obj G).map (polynomialToLaurent R)).hom (_ * _) = _
  rw [map_mul, ← orbitHom_apply, map_mul, map_mul]
  change mapPoints _ (pointHom _ _ _) * mapPoints _ (pointHom _ _ _) = _
  rw [polynomialContract_restrict, polynomialContract_restrict, orbitHom_apply, orbitHom_apply]

private theorem polynomialContract_natural (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    (D : LimitDecomposition cochar) {R S : TestAlgebra k} (a : R ⟶ S)
    (x : GroupPoints D.contracting.group R) :
    polynomialContract ha cochar D (mapPoints a x) =
      mapPoints (mapPolynomial a) (polynomialContract ha cochar D x) := by
  apply polynomialContract_eq
  change mapPoints (polynomialToLaurent S)
      (mapPoints (mapPolynomial a) (pointHom D.contracting.inclusion _ (polynomialContract ha cochar D x))) =
    orbit cochar (mapPoints a (pointHom D.contracting.inclusion _ x))
  rw [← mapPoints_comp, polynomialToLaurent_naturality, mapPoints_comp,
    polynomialContract_restrict, orbit_naturality]

private theorem polynomialContract_zero (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    (D : LimitDecomposition cochar) {R : TestAlgebra k} (x : GroupPoints D.contracting.group R) :
    (mapPoints (polynomialEvaluate R 0) (polynomialContract ha cochar D x) :
      GroupPoints D.contracting.group R) = 1 := by
  apply pointHom_injective D.contracting R
  rw [map_one]
  refine limitIsUnique cochar ?_ ((D.contracting_points R _).mpr ⟨x, rfl⟩)
  exact ⟨pointHom D.contracting.inclusion _ (polynomialContract ha cochar D x),
    polynomialContract_restrict ha cochar D x, rfl⟩

private theorem polynomialContract_one (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    (D : LimitDecomposition cochar) {R : TestAlgebra k} (x : GroupPoints D.contracting.group R) :
    mapPoints (polynomialEvaluate R 1) (polynomialContract ha cochar D x) = x := by
  apply pointHom_injective D.contracting R
  change mapPoints (polynomialEvaluate R 1)
    (pointHom D.contracting.inclusion _ (polynomialContract ha cochar D x)) = _
  rw [← polynomialToLaurent_evaluate_one, mapPoints_comp, polynomialContract_restrict, orbit_eval]
  have h₁ : cocharacterPoint cochar R 1 = 1 := by
    have h := cocharacterPoint_mul cochar R 1 1
    rw [one_mul] at h
    exact (mul_eq_left.mp h.symm)
  simp [h₁, mapPoints]

end ContractingAction

section CoalgebraFiltration

open WithConv

/-- The coefficient images of a natural contraction form an exhaustive coalgebra
filtration. Evaluations at zero and one give the counit and the identity. -/
private theorem filtration_of_polynomialContraction {A : HopfAlgebraCategory k}
    (F : ∀ R : TestAlgebra k, (convolutionPoints A).obj R →
      (convolutionPoints A).obj (polynomialAlgebra R))
    (hMul : ∀ R x y, F R (x * y) = F R x * F R y)
    (hNat : ∀ {R S} (a : R ⟶ S) x,
      F S ((convolutionPoints A).map a x) =
        (convolutionPoints A).map (mapPolynomial a) (F R x))
    (hZero : ∀ R x, (convolutionPoints A).map (polynomialEvaluate R 0) (F R x) = 1)
    (hOne : ∀ R x, (convolutionPoints A).map (polynomialEvaluate R 1) (F R x) = x) :
    Specs.Unipotent.HasCoalgebraFiltration A := by
  let R := CommAlgCat.of k A
  let id : (convolutionPoints A).obj R := toConv (AlgHom.id k A)
  let p : A →ₐ[k] Polynomial A := (F R id).ofConv
  let c (n : ℕ) : A →ₗ[k] A := ((Polynomial.lcoeff A n).restrictScalars k).comp p.toLinearMap
  let C (n : ℕ) : Submodule k A := ⨆ i : Fin (n + 1), LinearMap.range (c i.val)
  have memC (i n : ℕ) (hi : i ≤ n) (a : A) : c i a ∈ C n :=
    Submodule.mem_iSup_of_mem ⟨i, Nat.lt_succ_of_le hi⟩ ⟨a, rfl⟩
  have hzero (a : A) : c 0 a = algebraMap k A (Coalgebra.counit (R := k) a) := by
    have h := congrArg (fun g : (convolutionPoints A).obj R ↦ g.ofConv a) (hZero R id)
    change (p a).eval₂ (RingHom.id A) 0 = _ at h
    rwa [Polynomial.eval₂_at_zero, RingHom.id_apply] at h
  have hone (a : A) : (p a).eval 1 = a := by
    exact congrArg (fun g : (convolutionPoints A).obj R ↦ g.ofConv a) (hOne R id)
  have hΔ (n : ℕ) (a : A) :
      Coalgebra.comul (R := k) (c n a) =
        ∑ ij ∈ Finset.antidiagonal n,
          TensorProduct.map (c ij.1) (c ij.2) (Coalgebra.comul (R := k) a) := by
    let T := A ⊗[k] A
    let S := CommAlgCat.of k T
    let l : A →ₐ[k] T := Algebra.TensorProduct.includeLeft
    let r : A →ₐ[k] T := Algebra.TensorProduct.includeRight
    let Δ := Bialgebra.comulAlgHom k A
    let PL := (Polynomial.mapAlgHom l).comp p
    let PR := (Polynomial.mapAlgHom r).comp p
    have hprod : (toConv l : (convolutionPoints A).obj S) * toConv r = toConv Δ := by
      apply WithConv.ofConv_injective
      ext b
      rw [show ((toConv l : (convolutionPoints A).obj S) * toConv r).ofConv b =
        Algebra.TensorProduct.lift l r (fun _ _ ↦ .all _ _) (Coalgebra.comul (R := k) b)
        from AlgHom.convMul_apply (toConv l) (toConv r) b]
      have hh : Algebra.TensorProduct.lift l r (fun _ _ ↦ .all _ _) = AlgHom.id k T := by
        apply Algebra.TensorProduct.ext <;> ext z <;> simp [l, r] <;> rfl
      rw [hh]
      rfl
    have hAt (g : A →ₐ[k] T) :
        F S (toConv g) = toConv ((Polynomial.mapAlgHom g).comp p) :=
      hNat (CommAlgCat.ofHom g) id
    have he : toConv ((Polynomial.mapAlgHom Δ).comp p) =
        (toConv PL : (convolutionPoints A).obj (polynomialAlgebra S)) * toConv PR := by
      rw [← hAt Δ, ← hprod, hMul, hAt l, hAt r]
    have hc := congrArg (fun f : (convolutionPoints A).obj (polynomialAlgebra S) ↦
      (f.ofConv a).coeff n) he
    let m := Algebra.TensorProduct.lift PL PR (fun _ _ ↦ .all _ _)
    rw [show ((toConv PL : (convolutionPoints A).obj (polynomialAlgebra S)) *
        toConv PR).ofConv a = m (Coalgebra.comul (R := k) a) from
      AlgHom.convMul_apply (toConv PL) (toConv PR) a] at hc
    change (Polynomial.mapAlgHom Δ (p a)).coeff n =
      (m (Coalgebra.comul (R := k) a)).coeff n at hc
    rw [Polynomial.coeff_mapAlgHom_apply] at hc
    change Coalgebra.comul (R := k) (c n a) = _ at hc
    rw [hc]
    generalize Coalgebra.comul (R := k) a = t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [m, Algebra.TensorProduct.lift_tmul, PL, PR, AlgHom.comp_apply,
        Polynomial.coeff_mul, Polynomial.coeff_mapAlgHom_apply, TensorProduct.map_tmul]
      apply Finset.sum_congr rfl
      intro ij _
      change (c ij.1 x ⊗ₜ[k] (1 : A)) * ((1 : A) ⊗ₜ[k] c ij.2 y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp only [map_add, Polynomial.coeff_add, Finset.sum_add_distrib, hx, hy]
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    refine iSup_le fun i ↦ ?_
    rintro _ ⟨a, rfl⟩
    exact memC i.val n (le_trans (Nat.le_of_lt_succ i.isLt) hmn) a
  · intro a
    classical
    let n := (p a).natDegree
    refine ⟨n, ?_⟩
    have hs : a = ∑ i ∈ (p a).support, c i a := by
      calc
        a = (p a).eval 1 := (hone a).symm
        _ = _ := by simp [Polynomial.eval_eq_sum, Polynomial.sum, c]
    rw [hs]
    apply Submodule.sum_mem
    intro i hi
    exact memC i n (Polynomial.le_natDegree_of_mem_supp i hi) a
  · apply le_antisymm
    · refine iSup_le fun i ↦ ?_
      rintro _ ⟨a, rfl⟩
      have hi : i.val = 0 := by omega
      rw [hi, hzero]
      exact Submodule.mem_span_singleton.mpr
        ⟨Coalgebra.counit (R := k) a, by simp [Algebra.smul_def]⟩
    · apply Submodule.span_le.mpr
      intro a ha
      rw [Set.mem_singleton_iff.mp ha, ← show c 0 1 = 1 by
        change (p 1).coeff 0 = 1
        simp]
      exact memC 0 0 le_rfl 1
  · intro n x hx
    refine Submodule.iSup_induction (motive := fun a ↦
      Coalgebra.comul (R := k) a ∈ Specs.Unipotent.tensorFiltration C n)
      (fun i : Fin (n + 1) ↦ LinearMap.range (c i.val)) hx
      (fun i a ha ↦ ?_) (by simp) (fun a b ha hb ↦ by simpa using Submodule.add_mem _ ha hb)
    obtain ⟨b, rfl⟩ := ha
    rw [hΔ]
    apply Submodule.sum_mem
    intro ij hij
    have hh := Finset.mem_antidiagonal.mp hij
    have hi : ij.1 < n + 1 := by have := i.isLt; omega
    have hj : ij.2 ≤ n - ij.1 := by have := i.isLt; omega
    let f := (c ij.1).codRestrict (C ij.1) fun a ↦ memC ij.1 ij.1 le_rfl a
    let g := (c ij.2).codRestrict (C (n - ij.1)) fun a ↦ memC ij.2 (n - ij.1) hj a
    apply Submodule.mem_iSup_of_mem ⟨ij.1, hi⟩
    refine ⟨TensorProduct.map f g (Coalgebra.comul (R := k) b), ?_⟩
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    rfl

theorem contractingSubgroupUnipotent : Specs.CocharacterDynamics.ContractingSubgroupUnipotent.{u} := by
  intro k _ G _ cochar D
  let U := affineAlgebraicSubgroup D.contracting G.property.1 G.property.2.1 G.property.2.2
  let H : AffineGroupCategory k := ⟨U.val, U.property.1⟩
  let := affineHopfSpecEquivalence k
  let A := ((affineHopfSpec k).inv.obj H).unop
  let e : specGroup A ≅ U.val :=
    (affineGroupInclusion k).mapIso ((affineHopfSpec k).asEquivalence.counitIso.app H)
  let I := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso e
  let E (R : TestAlgebra k) := (I.app R).groupIsoToMulEquiv
  let F (R : TestAlgebra k) (x : (convolutionPoints A).obj R) :
      (convolutionPoints A).obj (polynomialAlgebra R) :=
    (E _).symm (polynomialContract G.property.1 cochar D (E _ x))
  have hE {R S : TestAlgebra k} (a : R ⟶ S) (v : (convolutionPoints A).obj R) :
      E S ((convolutionPoints A).map a v) = mapPoints a (E R v) :=
    congrArg (fun f ↦ GrpCat.Hom.hom f v) (I.hom.naturality a)
  refine ⟨A, ⟨e⟩, Unipotent.hasInvariantVectors_of_filtration ?_⟩
  apply filtration_of_polynomialContraction F
  · intro R x y
    apply (E (polynomialAlgebra R)).injective
    simp only [F, MulEquiv.apply_symm_apply, map_mul]
    exact polynomialContract_mul G.property.1 cochar D (E R x) (E R y)
  · intro R S a x
    apply (E (polynomialAlgebra S)).injective
    rw [hE]
    simp only [F, MulEquiv.apply_symm_apply, hE, polynomialContract_natural]
  · intro R x
    apply (E R).injective
    rw [hE]
    simp only [F, MulEquiv.apply_symm_apply, polynomialContract_zero, map_one]
  · intro R x
    apply (E R).injective
    rw [hE]
    simp only [F, MulEquiv.apply_symm_apply, polynomialContract_one]

end CoalgebraFiltration

end
end LinearAlgebraicGroups.CocharacterDynamics
