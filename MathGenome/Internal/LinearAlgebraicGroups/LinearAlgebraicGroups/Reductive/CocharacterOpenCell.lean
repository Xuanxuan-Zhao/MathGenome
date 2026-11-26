import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLieWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.CocharacterDynamics

open LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Specs.CharacterDescent (Cocharacter)
open Specs.AdjointRepresentation (GroupPoints RelativeTangent dualMap reduction)

open private affinePointEquiv affinePointEquiv_natural affineSmooth_iff_lifts
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {k : Type u} [Field k]

private abbrev pointMap {G H : GroupScheme k} (f : G ⟶ H) (R : TestAlgebra k) :=
  ((groupPointsFunctor k).map f).app R

private abbrev algMapPoints (G : GroupScheme k) {R S : TestAlgebra k} (f : R ⟶ S) :=
  (((groupPointsFunctor k).obj G).map f).hom

/-- The trivial scheme intersection makes the two-factor multiplication monic. -/
private theorem multiply_mono (G : AffineAlgebraicGroup k) (c : Cocharacter G.val)
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c)) :
    Mono (multiplyFactors E.contracting.inclusion D.parabolic.inclusion) := by
  let i := E.contracting.inclusion.hom.hom
  let j := D.parabolic.inclusion.hom.hom
  let h := oppositeLimitIntersection G c D E
  constructor
  intro T x y eq
  let x₁ := x ≫ fst E.contracting.group.X D.parabolic.group.X
  let y₁ := y ≫ fst E.contracting.group.X D.parabolic.group.X
  let x₂ := x ≫ snd E.contracting.group.X D.parabolic.group.X
  let y₂ := y ≫ snd E.contracting.group.X D.parabolic.group.X
  have he : (x₁ ≫ i) * (x₂ ≫ j) = (y₁ ≫ i) * (y₂ ≫ j) := by
    simpa only [multiplyFactors, MonObj.comp_mul, Category.assoc, x₁, y₁, x₂, y₂, i, j] using eq
  have hh : (y₁⁻¹ * x₁) ≫ i = (y₂ * x₂⁻¹) ≫ j := by
    change ((yonedaGrp.map E.contracting.inclusion).app (op T)).hom (y₁⁻¹ * x₁) =
      ((yonedaGrp.map D.parabolic.inclusion).app (op T)).hom (y₂ * x₂⁻¹)
    simp only [map_mul, map_inv]
    change (y₁ ≫ i)⁻¹ * (x₁ ≫ i) = (y₂ ≫ j) * (x₂ ≫ j)⁻¹
    calc
      _ = (y₁ ≫ i)⁻¹ * ((x₁ ≫ i) * (x₂ ≫ j)) * (x₂ ≫ j)⁻¹ := by group
      _ = _ := by rw [he]; group
  let p := h.lift (y₁⁻¹ * x₁) (y₂ * x₂⁻¹) hh
  have h₁ : p ≫ η[E.contracting.group.X] = y₁⁻¹ * x₁ := h.lift_fst _ _ _
  have h₂ : p ≫ η[D.parabolic.group.X] = y₂ * x₂⁻¹ := h.lift_snd _ _ _
  apply CartesianMonoidalCategory.hom_ext
  · change x₁ = y₁
    exact (inv_mul_eq_one.mp (h₁.symm.trans (congrArg (· ≫ η[E.contracting.group.X])
      (toUnit_unique p (toUnit T))))).symm
  · change x₂ = y₂
    exact (mul_inv_eq_one.mp (h₂.symm.trans (congrArg (· ≫ η[D.parabolic.group.X])
      (toUnit_unique p (toUnit T))))).symm

section SquareZero

variable {R : Type u} [CommRing R] [Algebra k R]

private abbrev quotient (I : Ideal R) :
    CommAlgCat.of k R ⟶ CommAlgCat.of k (R ⧸ I) :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)

private theorem mul_eq_zero_of_mem {I : Ideal R} (hI : I ^ 2 = ⊥)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have hm := Ideal.mul_mem_mul hx hy
  rwa [← pow_two, hI, Ideal.mem_bot] at hm

/-- The dual numbers whose infinitesimal coefficient belongs to the ideal. -/
private def idealDual (I : Ideal R) : Subalgebra k (DualNumber R) where
  carrier := {z | z.snd ∈ I}
  mul_mem' := fun hx hy ↦ I.add_mem (I.mul_mem_left _ hy) (I.mul_mem_right _ hx)
  add_mem' := I.add_mem
  algebraMap_mem' := fun _ ↦ I.zero_mem
  zero_mem' := I.zero_mem
  one_mem' := I.zero_mem

private abbrev idealDualAlg (I : Ideal R) := CommAlgCat.of k (idealDual (k := k) I)

private abbrev dualIncl (I : Ideal R) : idealDualAlg (k := k) I ⟶ CommAlgCat.of k (DualNumber R) :=
  CommAlgCat.ofHom (idealDual (k := k) I).val

private def dualSum (I : Ideal R) (hI : I ^ 2 = ⊥) :
    idealDualAlg (k := k) I ⟶ CommAlgCat.of k R :=
  CommAlgCat.ofHom {
    toFun := fun z ↦ z.val.fst + z.val.snd
    map_zero' := zero_add 0
    map_one' := add_zero 1
    map_add' := fun x y ↦ by
      change (x.val.fst + y.val.fst) + (x.val.snd + y.val.snd) = _
      ring
    map_mul' := fun x y ↦ by
      change x.val.fst * y.val.fst + (x.val.fst * y.val.snd + x.val.snd * y.val.fst) =
        (x.val.fst + x.val.snd) * (y.val.fst + y.val.snd)
      rw [add_mul, mul_add, mul_add, mul_eq_zero_of_mem hI x.property y.property, add_zero]
      ring
    commutes' := fun _ ↦ add_zero _ }

private theorem dualSum_quotient (I : Ideal R) (hI : I ^ 2 = ⊥) :
    dualSum (k := k) I hI ≫ quotient I =
      dualIncl I ≫ reduction (CommAlgCat.of k R) ≫ quotient I := by
  apply CommAlgCat.hom_ext
  ext x
  change (Ideal.Quotient.mkₐ k I) (x.val.fst + x.val.snd) =
    (Ideal.Quotient.mkₐ k I) x.val.fst
  rw [map_add, show (Ideal.Quotient.mkₐ k I) x.val.snd = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr x.property,
    add_zero]

private def dualDifference {A : TestAlgebra k} (I : Ideal R) (hI : I ^ 2 = ⊥)
    (a b : A →ₐ[k] R) (h : (Ideal.Quotient.mkₐ k I).comp a = (Ideal.Quotient.mkₐ k I).comp b) :
    A →ₐ[k] idealDual (k := k) I := by
  have mem (x : A) : b x - a x ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr ((DFunLike.congr_fun h x).symm)
  refine AlgHom.codRestrict
    ({ toFun := fun x ↦ (a x, b x - a x)
       map_zero' := ?_
       map_one' := ?_
       map_add' := ?_
       map_mul' := ?_
       commutes' := ?_ } : A →ₐ[k] DualNumber R)
    (idealDual I) mem
  · exact TrivSqZeroExt.ext (map_one a) (by simp)
  · intro x y
    apply TrivSqZeroExt.ext
    · exact map_mul a x y
    · change b (x * y) - a (x * y) = a x * (b y - a y) + (b x - a x) * a y
      have hm := mul_eq_zero_of_mem hI (mem x) (mem y)
      rw [map_mul, map_mul]
      linear_combination hm
  · exact TrivSqZeroExt.ext (map_zero a) (by simp)
  · intro x y
    apply TrivSqZeroExt.ext
    · exact map_add a x y
    · change b (x + y) - a (x + y) = (b x - a x) + (b y - a y)
      rw [map_add, map_add]
      ring
  · intro t
    apply TrivSqZeroExt.ext
    · exact a.commutes t
    · change b (algebraMap k A t) - a (algebraMap k A t) = 0
      rw [a.commutes, b.commutes, sub_self]

variable {G : GroupScheme k}

private theorem dualPoint_lift (ha : IsAffine G.X.left) (I : Ideal R)
    (p : GroupPoints G (CommAlgCat.of k (DualNumber R)))
    (hp : algMapPoints G (dualMap (quotient (k := k) I)) p = 1) :
    ∃ q : GroupPoints G (idealDualAlg (k := k) I), algMapPoints G (dualIncl I) q = p := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha
  let a := (affinePointEquiv e _).symm p
  let b := (affinePointEquiv e _).symm (1 : GroupPoints G (CommAlgCat.of k (R ⧸ I)))
  have hb : (dualMap (quotient (k := k) I)).hom.comp a =
      (Specs.AdjointRepresentation.constants (CommAlgCat.of k (R ⧸ I))).hom.comp b := by
    apply (affinePointEquiv e _).injective
    rw [affinePointEquiv_natural, affinePointEquiv_natural]
    unfold a b
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hp.trans (map_one (algMapPoints G _)).symm
  let a' : A.unop →ₐ[k] idealDual (k := k) I := a.codRestrict _ fun x ↦ by
    have hx := congrArg (fun v : DualNumber (R ⧸ I) ↦ v.snd) (DFunLike.congr_fun hb x)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  refine ⟨affinePointEquiv e _ a', ?_⟩
  change mapPoints (dualIncl I) (affinePointEquiv e _ a') = p
  rw [← affinePointEquiv_natural]
  exact (affinePointEquiv e _).apply_symm_apply p

private theorem dualPoint_of_kernel (ha : IsAffine G.X.left) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (g : GroupPoints G (CommAlgCat.of k R)) (hg : algMapPoints G (quotient I) g = 1) :
    ∃ q : GroupPoints G (idealDualAlg (k := k) I),
      algMapPoints G (dualSum I hI) q = g ∧
      algMapPoints G (dualIncl I ≫ reduction (CommAlgCat.of k R)) q = 1 := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha
  let a := (affinePointEquiv e _).symm (1 : GroupPoints G (CommAlgCat.of k R))
  let b := (affinePointEquiv e _).symm g
  have hab : (Ideal.Quotient.mkₐ k I).comp a = (Ideal.Quotient.mkₐ k I).comp b := by
    change (quotient (k := k) I).hom.comp a = (quotient (k := k) I).hom.comp b
    apply (affinePointEquiv e (CommAlgCat.of k (R ⧸ I))).injective
    rw [affinePointEquiv_natural e (quotient I), affinePointEquiv_natural e (quotient I)]
    unfold a b
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (map_one (algMapPoints G _)).trans hg.symm
  let d := dualDifference I hI a b hab
  refine ⟨affinePointEquiv e _ d, ?_, ?_⟩
  · change mapPoints (dualSum I hI) (affinePointEquiv e _ d) = g
    rw [← affinePointEquiv_natural]
    have h : (dualSum I hI).hom.comp d = b := AlgHom.ext fun x ↦ by
      change a x + (b x - a x) = b x
      ring
    rw [h]
    exact (affinePointEquiv e _).apply_symm_apply _
  · change mapPoints (dualIncl I ≫ reduction (CommAlgCat.of k R)) (affinePointEquiv e _ d) = _
    rw [← affinePointEquiv_natural]
    exact (affinePointEquiv e _).apply_symm_apply _

private theorem dualIncl_injective (ha : IsAffine G.X.left) (I : Ideal R) :
    Function.Injective (algMapPoints G (dualIncl (k := k) I)) := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha
  intro p q h
  obtain ⟨a, rfl⟩ := (affinePointEquiv e _).surjective p
  obtain ⟨b, rfl⟩ := (affinePointEquiv e _).surjective q
  change mapPoints (dualIncl I) (affinePointEquiv e _ a) =
    mapPoints (dualIncl I) (affinePointEquiv e _ b) at h
  rw [← affinePointEquiv_natural, ← affinePointEquiv_natural] at h
  have hab := (affinePointEquiv e _).injective h
  exact congrArg (affinePointEquiv e _) (AlgHom.ext fun x ↦
    Subtype.ext (DFunLike.congr_fun hab x))

end SquareZero

variable {G H : GroupScheme k}

private theorem pointMap_natural (f : H ⟶ G) {R S : TestAlgebra k} (a : R ⟶ S)
    (p : GroupPoints H R) :
    algMapPoints G a (pointMap f R p) = pointMap f S (algMapPoints H a p) := by
  exact ConcreteCategory.congr_hom (((groupPointsFunctor k).map f).naturality a).symm p

private theorem algMapPoints_comp (G : GroupScheme k) {R S T : TestAlgebra k} (a : R ⟶ S)
    (b : S ⟶ T) (p : GroupPoints G R) :
    algMapPoints G (a ≫ b) p = algMapPoints G b (algMapPoints G a p) :=
  ConcreteCategory.congr_hom (((groupPointsFunctor k).obj G).map_comp a b) p

private theorem inclusion_injective (S : ClosedSubgroup G) (R : TestAlgebra k) :
    Function.Injective (pointMap S.inclusion R) := by
  let := S.isClosedImmersion
  let : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  exact fun _ _ h ↦ (cancel_mono S.inclusion.hom.hom).mp h

/-- The kernel of reduction modulo a square-zero ideal is the product of the
negative and nonnegative tangent directions. Work with dual numbers whose
infinitesimal coefficients belong to the ideal so that evaluation is defined. -/
private theorem split_infinitesimal (G : AffineAlgebraicGroup k) (c : Cocharacter G.val)
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    {R : Type u} [CommRing R] [Algebra k R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (g : GroupPoints G.val (CommAlgCat.of k R)) (hg : algMapPoints G.val (quotient I) g = 1) :
    ∃ x : GroupPoints E.contracting.group (CommAlgCat.of k R),
    ∃ y : GroupPoints D.parabolic.group (CommAlgCat.of k R),
      algMapPoints E.contracting.group (quotient I) x = 1 ∧
      algMapPoints D.parabolic.group (quotient I) y = 1 ∧
      pointMap E.contracting.inclusion _ x * pointMap D.parabolic.inclusion _ y = g := by
  let R₀ := CommAlgCat.of k R
  let q := quotient (k := k) I
  let s := identityLieStructure G
  obtain ⟨W⟩ := existsAdjointWeightBasis G c s
  let T := W.coordinates
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨p, hsum, hzero⟩ := dualPoint_of_kernel G.property.1 I hI g hg
  let p₀ : RelativeTangent G.val R₀ :=
    ⟨algMapPoints G.val (dualIncl I) p, by
      change algMapPoints G.val (reduction R₀) (algMapPoints G.val (dualIncl I) p) = 1
      rw [← algMapPoints_comp]
      exact hzero⟩
  have hquot : algMapPoints G.val (dualMap q) p₀.toMul.val = 1 := by
    change algMapPoints G.val (dualMap q) (algMapPoints G.val (dualIncl I) p) = 1
    rw [← algMapPoints_comp]
    have heq : dualIncl I ≫ dualMap q =
        dualIncl I ≫ reduction R₀ ≫ q ≫ Specs.AdjointRepresentation.constants _ := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      apply TrivSqZeroExt.ext
      · rfl
      · exact Ideal.Quotient.eq_zero_iff_mem.mpr z.property
    rw [heq, ← Category.assoc, ← Category.assoc, algMapPoints_comp, algMapPoints_comp,
      hzero, map_one, map_one]
  obtain ⟨v, hv⟩ := (T.equiv R₀).surjective p₀
  have hvq : (fun j ↦ q.hom (v j)) = 0 := by
    apply (T.equiv _).injective
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [T.naturality q, hv]
    change algMapPoints G.val (dualMap q) p₀.toMul.val = (T.equiv _ 0).toMul.val
    rw [hquot, map_zero]
    rfl
  let vneg := fun j ↦ if W.weight j < 0 then v j else 0
  let vpos := fun j ↦ if W.weight j < 0 then 0 else v j
  have htotal : vneg + vpos = v := by
    funext j
    by_cases hj : W.weight j < 0 <;> simp [vneg, vpos, hj]
  have hneg := (relativeOppositeContractingWeights G c E s W R₀ vneg).mpr
    (fun j hj ↦ by simp [vneg, not_lt.mpr hj])
  have hpos := (relativeLieWeights G c D s W R₀ vpos).1.mpr
    (fun j hj ↦ by simp [vpos, hj])
  obtain ⟨pneg, hpneg⟩ := hneg
  obtain ⟨ppos, hppos⟩ := hpos
  have liftFactor (S : ClosedSubgroup G.val) (pS : RelativeTangent S.group R₀)
      (w : ULift.{u} (Fin W.dimension) → R₀)
      (hw : ∀ j, q.hom (w j) = 0)
      (hpS : pointMap S.inclusion _ pS.toMul.val = (T.equiv R₀ w).toMul.val) :
      ∃ a : GroupPoints S.group (idealDualAlg (k := k) I),
        algMapPoints S.group (dualIncl I) a = pS.toMul.val ∧
        algMapPoints S.group (quotient I) (algMapPoints S.group (dualSum I hI) a) = 1 := by
    have ha := (affineAlgebraicSubgroup S G.property.1 G.property.2.1 G.property.2.2).property.1
    have hred : algMapPoints S.group (dualMap q) pS.toMul.val = 1 := by
      apply inclusion_injective S
      rw [← pointMap_natural, hpS, map_one]
      change mapPoints (dualMap q) (T.equiv R₀ w).toMul.val = (1 : GroupPoints G.val _)
      rw [← T.naturality q]
      have hw₀ : (fun j ↦ q.hom (w j)) = 0 := funext hw
      rw [hw₀, map_zero]
      rfl
    obtain ⟨a, ha'⟩ := dualPoint_lift (G := S.group) ha I pS.toMul.val hred
    refine ⟨a, ha', ?_⟩
    rw [← algMapPoints_comp, dualSum_quotient, ← Category.assoc,
      algMapPoints_comp, algMapPoints_comp, ha']
    change algMapPoints S.group (quotient I) ((algMapPoints S.group (reduction R₀)) pS.toMul.val) = 1
    rw [show algMapPoints S.group (reduction R₀) pS.toMul.val = 1 from pS.toMul.property, map_one]
  obtain ⟨x, hx, hxq⟩ := liftFactor E.contracting pneg vneg (by
    intro j
    have h := congrFun hvq j
    by_cases hj : W.weight j < 0 <;> simp [vneg, hj, h]) hpneg
  obtain ⟨y, hy, hyq⟩ := liftFactor D.parabolic ppos vpos (by
    intro j
    have h := congrFun hvq j
    by_cases hj : W.weight j < 0 <;> simp [vpos, hj, h]) hppos
  refine ⟨algMapPoints _ (dualSum I hI) x, algMapPoints _ (dualSum I hI) y, hxq, hyq, ?_⟩
  rw [← pointMap_natural, ← pointMap_natural, ← map_mul, ← hsum]
  congr 1
  apply dualIncl_injective G.property.1 I
  rw [map_mul, pointMap_natural, pointMap_natural, hx, hy, hpneg, hppos]
  change ((T.equiv R₀ vneg + T.equiv R₀ vpos).toMul.val) = p₀.toMul.val
  rw [← map_add, htotal, hv]

/-- A square-zero lifting criterion for morphisms of affine schemes of finite type
over a field, phrased on their test-algebra points. -/
private theorem smooth_of_lifts {X Y : SchemeOver k} (haX : IsAffine X.left)
    (haY : IsAffine Y.left) (hfX : LocallyOfFiniteType X.hom) (hfY : LocallyOfFiniteType Y.hom)
    (m : X ⟶ Y)
    (h : ∀ (R : Type u) [CommRing R] [Algebra k R] (I : Ideal R), I ^ 2 = ⊥ →
      ∀ (x : Points X (CommAlgCat.of k (R ⧸ I))) (y : Points Y (CommAlgCat.of k R)),
        x ≫ m = mapPoints (quotient I) y →
        ∃ x' : Points X (CommAlgCat.of k R), mapPoints (quotient I) x' = x ∧ x' ≫ m = y) :
    Smooth m.left := by
  obtain ⟨B, ⟨eX⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr haX
  obtain ⟨A, ⟨eY⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr haY
  let S := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f := (S.preimage (eX.hom ≫ m ≫ eY.inv)).unop
  have hfmap : (testSpec k).map f.op ≫ eY.hom = eX.hom ≫ m := by
    change (testSpec k).map (S.preimage (eX.hom ≫ m ≫ eY.inv)) ≫ _ = _
    rw [S.map_preimage]
    simp
  have point_comp {R : TestAlgebra k} (x : B.unop →ₐ[k] R) :
      affinePointEquiv eX R x ≫ m = affinePointEquiv eY R (x.comp f.hom) := by
    change ((testSpec k).map (CommAlgCat.ofHom x).op ≫ eX.hom) ≫ m =
      (testSpec k).map (f ≫ CommAlgCat.ofHom x).op ≫ eY.hom
    rw [op_comp, Functor.map_comp, Category.assoc, Category.assoc, hfmap]
  have heX : IsIso eX.hom.left := (Over.forget _).map_isIso eX.hom
  have heY : IsIso eY.hom.left := (Over.forget _).map_isIso eY.hom
  have h₁ : LocallyOfFiniteType ((testSpec k).obj A).hom := by
    rw [← Over.w eY.hom]
    infer_instance
  have hA : Algebra.FiniteType k A.unop := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A.unop))) at h₁
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₁
    exact RingHom.finiteType_algebraMap.mp h₁
  have h₂ : LocallyOfFiniteType ((testSpec k).map f.op).left := by
    have heq : ((testSpec k).map f.op).left ≫ eY.hom.left = eX.hom.left ≫ m.left := by
      exact congrArg (fun p ↦ p.left) hfmap
    have : LocallyOfFiniteType (m.left ≫ Y.hom) := by rw [Over.w]; exact hfX
    have := locallyOfFiniteType_of_comp m.left Y.hom
    have : LocallyOfFiniteType (((testSpec k).map f.op).left ≫ eY.hom.left) := by
      rw [heq]
      infer_instance
    exact locallyOfFiniteType_of_comp _ eY.hom.left
  have hft : f.hom.toRingHom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h₂
  let : Algebra A.unop B.unop := f.hom.toRingHom.toAlgebra
  let : IsScalarTower k A.unop B.unop :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r ↦ (f.hom.commutes r).symm)
  have hfs : Algebra.FormallySmooth A.unop B.unop := by
    apply Algebra.FormallySmooth.iff_comp_surjective.mpr
    intro R _ _ I hI x
    let : Algebra k R := ((algebraMap A.unop R).comp (algebraMap k A.unop)).toAlgebra
    let : IsScalarTower k A.unop R := IsScalarTower.of_algebraMap_eq' rfl
    let y : A.unop →ₐ[k] R := (Algebra.ofId A.unop R).restrictScalars k
    -- The two coordinate maps in the lifting square.
    let x₀ : B.unop →ₐ[k] (R ⧸ I) := x.restrictScalars k
    have hx : x₀.comp f.hom = (quotient I).hom.comp y := AlgHom.ext fun a ↦ x.commutes a
    obtain ⟨x', hx', hx'y⟩ := h R I hI (affinePointEquiv eX _ x₀) (affinePointEquiv eY _ y)
      (by rw [point_comp, ← affinePointEquiv_natural, hx])
    let z := (affinePointEquiv eX _).symm x'
    have hz : z.comp f.hom = y := by
      apply (affinePointEquiv eY _).injective
      rw [← point_comp, Equiv.apply_symm_apply]
      exact hx'y
    let z' : B.unop →ₐ[A.unop] R :=
      { toRingHom := z.toRingHom
        commutes' := fun a ↦ DFunLike.congr_fun hz a }
    refine ⟨z', AlgHom.ext fun b ↦ ?_⟩
    have heq : (quotient I).hom.comp z = x₀ := by
      apply (affinePointEquiv eX _).injective
      rw [affinePointEquiv_natural, Equiv.apply_symm_apply]
      exact hx'
    exact DFunLike.congr_fun heq b
  have hsm : f.hom.toRingHom.Smooth := by
    have := Algebra.FiniteType.isNoetherianRing k A.unop
    rw [RingHom.smooth_def]
    exact ⟨RingHom.formallySmooth_algebraMap.mpr hfs, RingHom.FinitePresentation.of_finiteType.mp hft⟩
  have hs : Smooth ((testSpec k).map f.op).left :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr hsm
  have he := congrArg (fun p ↦ (Over.forget _).map p) hfmap
  change ((testSpec k).map f.op).left ≫ eY.hom.left = eX.hom.left ≫ m.left at he
  have h' : Smooth (eX.hom.left ≫ m.left) := he ▸ inferInstanceAs
    (Smooth (((testSpec k).map f.op).left ≫ eY.hom.left))
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) eX.hom.left m.left).mp h'

private theorem product_pullback (X Y : SchemeOver k) :
    IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
  Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct X Y)

private theorem multiply_isOpenImmersion (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    (c : Cocharacter G.val) (D : LimitDecomposition c)
    (E : LimitDecomposition (oppositeCocharacter c)) :
    IsOpenImmersion (multiplyFactors E.contracting.inclusion D.parabolic.inclusion).left := by
  let U := affineAlgebraicSubgroup E.contracting G.property.1 G.property.2.1 G.property.2.2
  let P := affineAlgebraicSubgroup D.parabolic G.property.1 G.property.2.1 G.property.2.2
  let m := multiplyFactors E.contracting.inclusion D.parabolic.inclusion
  have hU := (limitSubgroupsSmooth G (oppositeCocharacter c) E).2.1
  have hP := (limitSubgroupsSmooth G c D).1
  have hpb := product_pullback U.val.X P.val.X
  have hai : IsAffineHom (fst U.val.X P.val.X).left := by
    have : IsAffine P.val.X.left := P.property.1
    exact MorphismProperty.of_isPullback hpb.flip inferInstance
  have ha : IsAffine (U.val.X ⊗ P.val.X).left := by
    have : IsAffine U.val.X.left := U.property.1
    exact isAffine_of_isAffineHom (fst U.val.X P.val.X).left
  have hfp : LocallyOfFiniteType (fst U.val.X P.val.X).left :=
    MorphismProperty.of_isPullback hpb.flip P.property.2.1
  have hf : LocallyOfFiniteType (U.val.X ⊗ P.val.X).hom := by
    rw [← Over.w (fst U.val.X P.val.X)]
    have := U.property.2.1
    infer_instance
  have hmono := multiply_mono G c D E
  have hs : Smooth m.left := by
    apply smooth_of_lifts ha G.property.1 hf G.property.2.1
    intro R _ _ I hI x y hxy
    change Points (E.contracting.group.X ⊗ D.parabolic.group.X) (CommAlgCat.of k (R ⧸ I)) at x
    let q := quotient (k := k) I
    obtain ⟨u, hu⟩ := (affineSmooth_iff_lifts U.val.X U.property.1 U.property.2.1).mp hU
      R I hI (x ≫ fst _ _)
    obtain ⟨p, hp⟩ := (affineSmooth_iff_lifts P.val.X P.property.1 P.property.2.1).mp hP
      R I hI (x ≫ snd _ _)
    change GroupPoints G.val (CommAlgCat.of k R) at y
    change GroupPoints E.contracting.group (CommAlgCat.of k R) at u
    change GroupPoints D.parabolic.group (CommAlgCat.of k R) at p
    let uG := pointMap E.contracting.inclusion _ u
    let pG := pointMap D.parabolic.inclusion _ p
    -- Translate the error to the identity before correcting the two lifts.
    let err : GroupPoints G.val (CommAlgCat.of k R) := uG⁻¹ * y * pG⁻¹
    have he : algMapPoints G.val q err = 1 := by
      have hh : algMapPoints G.val q y = pointMap E.contracting.inclusion _ (x ≫ fst _ _) *
          pointMap D.parabolic.inclusion _ (x ≫ snd _ _) := by
        change mapPoints q y = _
        rw [← hxy]
        simp only [m, multiplyFactors, MonObj.comp_mul]
        rfl
      have huG : algMapPoints G.val q uG = pointMap E.contracting.inclusion _ (x ≫ fst _ _) := by
        unfold uG
        rw [pointMap_natural]
        exact congrArg (pointMap E.contracting.inclusion _) hu
      have hpG : algMapPoints G.val q pG = pointMap D.parabolic.inclusion _ (x ≫ snd _ _) := by
        unfold pG
        rw [pointMap_natural]
        exact congrArg (pointMap D.parabolic.inclusion _) hp
      unfold err
      rw [map_mul, map_mul, map_inv, map_inv, huG, hpG, hh]
      group
    obtain ⟨u', p', hu', hp', herr⟩ := split_infinitesimal G c D E I hI err he
    refine ⟨lift (u * u') (p' * p), ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [mapPoints, Category.assoc, lift_fst]
        change algMapPoints E.contracting.group q (u * u') = _
        rw [map_mul, hu', mul_one]
        exact hu
      · simp only [mapPoints, Category.assoc, lift_snd]
        change algMapPoints D.parabolic.group q (p' * p) = _
        rw [map_mul, hp', one_mul]
        exact hp
    · change lift (u * u') (p' * p) ≫
        multiplyFactors E.contracting.inclusion D.parabolic.inclusion = y
      simp only [multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
      change pointMap E.contracting.inclusion _ (u * u') *
        pointMap D.parabolic.inclusion _ (p' * p) = _
      rw [map_mul, map_mul, mul_assoc, ← mul_assoc (pointMap E.contracting.inclusion _ u'), herr]
      change uG * (err * pG) = y
      rw [show err = uG⁻¹ * y * pG⁻¹ from rfl]
      group
  exact IsOpenImmersion.of_flat_of_mono m.left

theorem bigCell : Specs.CocharacterDynamics.BigCell.{u} := by
  intro k _ G _ c D E
  let m := multiplyFactors E.contracting.inclusion D.parabolic.inclusion
  let s := multiplyFactors D.sectionMap D.contractingToParabolic
  let : IsIso s := D.product_iso
  let j := lift (fst E.contracting.group.X (D.centralizer.group.X ⊗ D.contracting.group.X))
    (snd _ _ ≫ s)
  have hj : IsIso j := by
    change IsIso (E.contracting.group.X ◁ s)
    infer_instance
  have fac : bigCellMap D E = j ≫ m := by
    have hs : s ≫ D.parabolic.inclusion.hom.hom =
        multiplyFactors D.centralizer.inclusion D.contracting.inclusion := by
      have h₁ := congrArg (fun f ↦ (Grp.forget (SchemeOver k)).map f) D.section_in_G
      have h₂ := congrArg (fun f ↦ (Grp.forget (SchemeOver k)).map f) D.contracting_in_G
      change D.sectionMap.hom.hom ≫ D.parabolic.inclusion.hom.hom =
        D.centralizer.inclusion.hom.hom at h₁
      change D.contractingToParabolic.hom.hom ≫ D.parabolic.inclusion.hom.hom =
        D.contracting.inclusion.hom.hom at h₂
      change ((yonedaGrp.map D.parabolic.inclusion).app (op _)).hom
        ((fst _ _ ≫ D.sectionMap.hom.hom) * (snd _ _ ≫ D.contractingToParabolic.hom.hom)) = _
      rw [map_mul]
      change (fst _ _ ≫ D.sectionMap.hom.hom ≫ D.parabolic.inclusion.hom.hom) *
        (snd _ _ ≫ D.contractingToParabolic.hom.hom ≫ D.parabolic.inclusion.hom.hom) = _
      simp only [h₁, h₂]
      rfl
    change (fst _ _ ≫ E.contracting.inclusion.hom.hom) *
      (snd _ _ ≫ multiplyFactors D.centralizer.inclusion D.contracting.inclusion) =
      j ≫ ((fst _ _ ≫ E.contracting.inclusion.hom.hom) * (snd _ _ ≫ D.parabolic.inclusion.hom.hom))
    simp only [j, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, Category.assoc, hs]
  rw [fac, Over.comp_left]
  let : IsOpenImmersion m.left := multiply_isOpenImmersion G c D E
  let : IsIso j.left := (Over.forget _).map_isIso j
  infer_instance

section Irreducibility

open scoped TensorProduct

private theorem exists_specialization {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsDomain A] [IsAlgClosed k] {a : A} (ha : a ≠ 0) :
    ∃ f : A →ₐ[k] k, f a ≠ 0 := by
  let X := (testSpec k).obj (op (CommAlgCat.of k A))
  have hf : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hj : JacobsonSpace (PrimeSpectrum A) := LocallyOfFiniteType.jacobsonSpace X.hom
  let U := PrimeSpectrum.basicOpen a
  have hU : (U : Set (PrimeSpectrum A)).Nonempty := ⟨⟨⊥, Ideal.isPrime_bot⟩, ha⟩
  obtain ⟨x, hx, hx'⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
  let p : Points X (CommAlgCat.of k k) :=
    Over.homMk (pointOfClosedPoint X.hom x hx') (by
      rw [pointOfClosedPoint_comp]
      exact (Spec.map_id (CommRingCat.of k)).symm)
  obtain ⟨f, hf'⟩ := (affinePointEquiv (Iso.refl X) _).surjective p
  refine ⟨f, fun he ↦ hx ?_⟩
  have e : Spec.map (CommRingCat.ofHom f.toRingHom) = p.left :=
    congrArg (fun p ↦ p.left) hf'
  have eq : Spec.map (CommRingCat.ofHom f.toRingHom) (IsLocalRing.closedPoint k) = x :=
    (congrArg (fun m : Spec (CommRingCat.of k) ⟶ X.left ↦ m (IsLocalRing.closedPoint k)) e).trans
      (pointOfClosedPoint_apply _ _ _ _)
  change a ∈ x.asIdeal
  rw [← eq]
  change f a ∈ (IsLocalRing.closedPoint k : PrimeSpectrum k).asIdeal
  rw [he]
  exact Ideal.zero_mem _

/-- Specialization in a basis of the right-hand factor proves that a finite type
domain over an algebraically closed field stays a domain under scalar extension. -/
private theorem tensor_isDomain {A B : Type u} [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsDomain A] [CommRing B] [Algebra k B] [IsDomain B]
    [IsAlgClosed k] : IsDomain (A ⊗[k] B) := by
  classical
  let b := Module.Free.chooseBasis k B
  let ba := b.baseChange A
  have nz (x : A ⊗[k] B) (h : x ≠ 0) : ∃ i, ba.repr x i ≠ 0 := by
    by_contra! H
    apply h
    apply ba.repr.injective
    ext i
    simpa using H i
  have hnt : Nontrivial (A ⊗[k] B) := inferInstance
  suffices NoZeroDivisors (A ⊗[k] B) by exact NoZeroDivisors.to_isDomain _
  constructor
  intro x y hxy
  by_contra! h
  obtain ⟨i, hi⟩ := nz x h.1
  obtain ⟨j, hj⟩ := nz y h.2
  obtain ⟨f, hf⟩ := exists_specialization (k := k) (mul_ne_zero hi hj)
  let v : A ⊗[k] B →ₐ[k] B :=
    Algebra.TensorProduct.lift ((Algebra.ofId k B).comp f) (AlgHom.id k B) (fun _ _ ↦ .all _ _)
  have coeff (x : A ⊗[k] B) (i : _) : b.repr (v x) i = f (ba.repr x i) := by
    induction x using TensorProduct.inductionOn with
    | tmul a r =>
      have hv : v (a ⊗ₜ[k] r) = f a • r := by
        simp only [v, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.id_apply]
        exact (Algebra.smul_def (f a) r).symm
      rw [hv, map_smul]
      simp [ba, Algebra.smul_def, mul_comm]
    | add x y hx hy => simp [hx, hy]
  have hix : v x ≠ 0 := by
    intro hx
    have := coeff x i
    rw [hx, map_zero, Finsupp.zero_apply] at this
    apply hf
    rw [map_mul, ← this, zero_mul]
  have hjy : v y ≠ 0 := by
    intro hy
    have := coeff y j
    rw [hy, map_zero, Finsupp.zero_apply] at this
    apply hf
    rw [map_mul, ← this, mul_zero]
  exact (mul_ne_zero hix hjy) (by rw [← map_mul, hxy, map_zero])

private theorem geometricallyIrreducible_affine {X : SchemeOver k} (hX : IsAffine X.left)
    [LocallyOfFiniteType X.hom] [IrreducibleSpace X.left] [IsAlgClosed k] :
    GeometricallyIrreducible X.hom := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hX
  let S := (testSpec k).obj A
  have hIso : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hS : IrreducibleSpace S.left := e.hom.left.homeomorph.irreducibleSpace_iff.mpr inferInstance
  have hF : LocallyOfFiniteType S.hom := by
    rw [← Over.w e.hom]
    infer_instance
  have hA : Algebra.FiniteType k A.unop :=
    RingHom.finiteType_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hF)
  let I : Ideal A.unop := nilradical A.unop
  have hI : I.IsPrime :=
    (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical).mp hS
  let Q := A.unop ⧸ I
  let : IsDomain Q := Ideal.Quotient.isDomain I
  let d : (testSpec k).obj (op (CommAlgCat.of k Q)) ⟶ S :=
    (testSpec k).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)).op
  have hd : Surjective d.left := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.mk I))
    exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl).2
  have hs : GeometricallyIrreducible S.hom := by
    apply GeometricallyIrreducible.mk
    rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro L _ _
    let ψ := fieldSpecMap k L
    let h := ((testSpec k).obj (op (CommAlgCat.of k Q))).hom
    have hdom : IsDomain (Q ⊗[k] L) := tensor_isDomain
    have hp : IrreducibleSpace (Limits.pullback h ψ : Scheme) :=
      (pullbackSpecIso k Q L).hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
    have hout : IsPullback (Limits.pullback.snd h ψ) (Limits.pullback.fst h ψ)
        ψ (d.left ≫ S.hom) := by
      rw [Over.w d]
      exact (IsPullback.of_hasPullback h ψ).flip
    have hpb := IsPullback.of_right' hout (IsPullback.of_hasPullback S.hom ψ).flip
    have hp' : Surjective _ := MorphismProperty.of_isPullback hpb.flip hd
    exact hp'.surj.irreducibleSpace (Scheme.Hom.continuous _)

  rwa [← Over.w e.hom, MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIrreducible)] at hs

end Irreducibility

open CategoryTheory.Limits

/-- Intersecting irreducible components over an algebraically closed field share
a rational point. Translating by that point, the product of the components
has irreducible image containing both components. -/
private theorem group_irreducible_of_connected (G : AffineAlgebraicGroup k)
    [ConnectedSpace G.val.X.left] [IsAlgClosed k] : IrreducibleSpace G.val.X.left := by
  classical
  let X := G.val.X
  have hX : IsAffine X.left := G.property.1
  have hf : LocallyOfFiniteType X.hom := G.property.2.1
  have hj : JacobsonSpace X.left := hf.jacobsonSpace X.hom
  have hn : IsNoetherian X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian X.hom }
  have eq_of_meet (C D : Set X.left) (hC : C ∈ irreducibleComponents X.left)
      (hD : D ∈ irreducibleComponents X.left) (h : (C ∩ D).Nonempty) : C = D := by
    obtain ⟨x, hx, hx'⟩ := nonempty_inter_closedPoints h
      ((isClosed_of_mem_irreducibleComponents _ hC).inter
        (isClosed_of_mem_irreducibleComponents _ hD)).isLocallyClosed
    let i₀ := X.left.irreducibleComponentι C hC
    let j₀ := X.left.irreducibleComponentι D hD
    let Y := Over.mk (i₀ ≫ X.hom)
    let Z := Over.mk (j₀ ≫ X.hom)
    let i : Y ⟶ X := Over.homMk i₀ rfl
    let j : Z ⟶ X := Over.homMk j₀ rfl
    have hY : IsAffine Y.left := isAffine_of_isAffineHom i₀
    have hi : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (i₀ ≫ X.hom))
    have hj : LocallyOfFiniteType Z.hom := inferInstanceAs (LocallyOfFiniteType (j₀ ≫ X.hom))
    let y : Y.left := ⟨x, hx.1⟩
    let z : Z.left := ⟨x, hx.2⟩
    have hy : IsClosed ({y} : Set Y.left) := by
      have h : i₀ ⁻¹' ({x} : Set X.left) = {y} := by
        ext a
        change i₀ a = i₀ y ↔ a = y
        exact i₀.injective.eq_iff
      rw [← h]
      exact hx'.preimage i₀.continuous
    have hz : IsClosed ({z} : Set Z.left) := by
      have h : j₀ ⁻¹' ({x} : Set X.left) = {z} := by
        ext a
        change j₀ a = j₀ z ↔ a = z
        exact j₀.injective.eq_iff
      rw [← h]
      exact hx'.preimage j₀.continuous
    let y₀ : 𝟙_ (SchemeOver k) ⟶ Y := Over.homMk
      (pointOfClosedPoint Y.hom y hy) (pointOfClosedPoint_comp Y.hom y hy)
    let z₀ : 𝟙_ (SchemeOver k) ⟶ Z := Over.homMk
      (pointOfClosedPoint Z.hom z hz) (pointOfClosedPoint_comp Z.hom z hz)
    have he : y₀ ≫ i = z₀ ≫ j := by
      apply Over.OverMorphism.ext
      apply ext_of_apply_closedPoint_eq X.hom
      · exact Over.w (y₀ ≫ i)
      · exact Over.w (z₀ ≫ j)
      · change (pointOfClosedPoint Y.hom y hy ≫ i₀) _ =
          (pointOfClosedPoint Z.hom z hz ≫ j₀) _
        simp only [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
        rfl
    let e := y₀ ≫ i
    let m : Y ⊗ Z ⟶ X :=
      (fst _ _ ≫ i) * (toUnit (Y ⊗ Z) ≫ e)⁻¹ * (snd _ _ ≫ j)
    have hYZ : IrreducibleSpace (Y ⊗ Z).left := by
      have : IrreducibleSpace Y.left := inferInstanceAs
        (IrreducibleSpace (X.left.irreducibleComponent C hC))
      have : IrreducibleSpace Z.left := inferInstanceAs
        (IrreducibleSpace (X.left.irreducibleComponent D hD))
      have := geometricallyIrreducible_affine hY
      exact (product_pullback Y Z).isoPullback.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
    have hm : IsIrreducible (Set.range m.left) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ m.left.continuous.continuousOn
    have hC' : C ⊆ Set.range m.left := by
      intro a ha
      let t := lift (𝟙 Y) (toUnit Y ≫ z₀)
      have ht : t ≫ m = i := by
        simp only [t, m, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc,
          Category.id_comp, Category.assoc, comp_toUnit_assoc, ← he, e]
        group
      exact ⟨t.left ⟨a, ha⟩, by
        change (t.left ≫ m.left) ⟨a, ha⟩ = a
        rw [← Over.comp_left, ht]
        rfl⟩
    have hD' : D ⊆ Set.range m.left := by
      intro a ha
      let t := lift (toUnit Z ≫ y₀) (𝟙 Z)
      have ht : t ≫ m = j := by
        simp only [t, m, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc,
          Category.id_comp, Category.assoc, comp_toUnit_assoc, e]
        group
      exact ⟨t.left ⟨a, ha⟩, by
        change (t.left ≫ m.left) ⟨a, ha⟩ = a
        rw [← Over.comp_left, ht]
        rfl⟩
    exact (hC'.antisymm (hC.2 hm hC')).trans (hD'.antisymm (hD.2 hm hD')).symm
  obtain ⟨x⟩ := (inferInstance : Nonempty X.left)
  let C := irreducibleComponent x
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have ho : IsOpen C := by
    have e : Cᶜ = ⋃₀ (irreducibleComponents X.left \ {C}) := by
      ext y
      constructor
      · intro hy
        apply Set.mem_sUnion_of_mem mem_irreducibleComponent
        exact ⟨irreducibleComponent_mem_irreducibleComponents y, fun h ↦
          hy ((Set.mem_singleton_iff.mp h) ▸ mem_irreducibleComponent)⟩
      · rintro ⟨D, hD, hyD⟩ hy
        exact hD.2 (Set.mem_singleton_iff.mpr (eq_of_meet _ _ hD.1 hC ⟨y, hyD, hy⟩))
    have hc : IsClosed (⋃₀ (irreducibleComponents X.left \ {C})) := by
      rw [Set.sUnion_eq_biUnion]
      exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        (fun D hD ↦ isClosed_of_mem_irreducibleComponents _ hD.1)
    rw [← isClosed_compl_iff, e]
    exact hc
  have hall := IsClopen.eq_univ ⟨isClosed_of_mem_irreducibleComponents _ hC, ho⟩
    (show C.Nonempty from ⟨x, mem_irreducibleComponent⟩)
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set X.left)
  rw [← hall]
  exact hC.1

/-- Over an algebraic extension the projection is open and closed. The fiber
over the rational section is a singleton, so the image of a clopen set
missing that point has to be empty. -/
private theorem connected_pullback_algebraic {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [ConnectedSpace X]
    (s : Spec (CommRingCat.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (L : Type u) [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] :
    ConnectedSpace (pullback f (fieldSpecMap k L) : Scheme) := by
  let g := fieldSpecMap k L
  let p := pullback.fst f g
  let e : Spec (CommRingCat.of L) ⟶ pullback f g :=
    pullback.lift (g ≫ s) (𝟙 _) (by simp [hs])
  let a := IsLocalRing.closedPoint k
  let b := IsLocalRing.closedPoint L
  have hi : IsIntegralHom g := by
    apply IsIntegralHom.SpecMap_iff.mpr
    exact fun x ↦ Algebra.IsIntegral.isIntegral (R := k) x
  have ho : IsOpenMap p := p.isOpenMap
  have hc : IsClosedMap p := p.isClosedMap
  have huniq {x : (pullback f g : Scheme)} (hx : p x = s a) : x = e b := by
    obtain ⟨y, _, hy⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := p) a x hx.symm
    have : Subsingleton (pullback s p : Scheme) := by
      let iso := pullbackRightPullbackFstIso f g s
      have h : Subsingleton (pullback (s ≫ f) g : Scheme) := by
        rw [hs]
        exact (pullback.snd (𝟙 _) g).homeomorph.subsingleton_congr.mpr inferInstance
      exact iso.hom.homeomorph.subsingleton_congr.mpr h
    let y' : Spec (CommRingCat.of L) ⟶ pullback s p :=
      pullback.lift g e (by simp [p, e])
    rw [← hy, Subsingleton.elim y (y' b)]
    change (y' ≫ pullback.snd s p) b = _
    simp [y']
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨e b⟩, ?_⟩
  intro U hU
  have empty_if_no_identity (V : Set (pullback f g : Scheme)) (hV : IsClopen V)
      (he : e b ∉ V) : V = ∅ := by
    have hV' : IsClopen (p '' V) := ⟨hc _ hV.1, ho _ hV.2⟩
    rcases isClopen_iff.mp hV' with h | h
    · exact Set.image_eq_empty.mp h
    · have : s a ∈ p '' V := h.symm ▸ Set.mem_univ _
      obtain ⟨x, hx, hpx⟩ := this
      exact (he (huniq hpx ▸ hx)).elim
  by_cases h : e b ∈ U
  · right
    have eU : Uᶜ = ∅ := empty_if_no_identity _ hU.compl (by simpa using h)
    simpa using congrArg (fun V : Set (pullback f g : Scheme) ↦ Vᶜ) eU
  · exact Or.inl (empty_if_no_identity _ hU h)

private theorem group_geometricallyIrreducible (G : AffineAlgebraicGroup k)
    [ConnectedSpace G.val.X.left] : GeometricallyIrreducible G.val.X.hom := by
  let L := AlgebraicClosure k
  let J := (groupBaseChange k L).obj G.val
  let hpb := IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k L)
  have hconn : ConnectedSpace J.X.left := connected_pullback_algebraic G.val.X.hom
    (η[G.val.X]).left (Over.w (η[G.val.X])) L
  have hJ : IsAffine J.X.left := by
    have := G.property.1
    have hg : IsAffineHom (fieldSpecMap k L) := inferInstance
    exact IsAffine.of_isPullback hpb
  have hf : LocallyOfFiniteType J.X.hom := MorphismProperty.of_isPullback hpb G.property.2.1
  have hq : QuasiCompact J.X.hom := MorphismProperty.of_isPullback hpb G.property.2.2
  have hi : IrreducibleSpace J.X.left := group_irreducible_of_connected ⟨J, hJ, hf, hq⟩
  have hgeom : GeometricallyIrreducible J.X.hom := geometricallyIrreducible_affine hJ
  refine ⟨?_⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro M _ _
  let N := AlgebraicClosure M
  let t : L →ₐ[k] N := IsAlgClosed.lift
  let φ : Spec (CommRingCat.of N) ⟶ Spec (CommRingCat.of L) :=
    Spec.map (CommRingCat.ofHom t.toRingHom)
  let ψ := fieldSpecMap M N
  let g := fieldSpecMap k M
  let f := G.val.X.hom
  have e₁ : φ ≫ fieldSpecMap k L = ψ ≫ g := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact t.commutes
  let T := pullback J.X.hom φ
  have hT : IrreducibleSpace (T : Scheme) :=
    pullback_of_geometrically hgeom.geometrically_irreducibleSpace N φ
  have hout : IsPullback (pullback.fst J.X.hom φ ≫ pullback.fst f (fieldSpecMap k L))
      (pullback.snd J.X.hom φ) f (ψ ≫ g) := by
    rw [← e₁]
    exact (IsPullback.of_hasPullback J.X.hom φ).paste_horiz hpb
  have hinner := IsPullback.of_bot' hout.flip (IsPullback.of_hasPullback f g).flip
  have hs : Surjective ψ := ⟨fun _ ↦ ⟨IsLocalRing.closedPoint N, Subsingleton.elim _ _⟩⟩
  have hsurj : Surjective _ := MorphismProperty.of_isPullback hinner hs
  exact hsurj.surj.irreducibleSpace (Scheme.Hom.continuous _)

private theorem geometricallyConnected_of_retract {X Y : SchemeOver k}
    (p : X ⟶ Y) (s : Y ⟶ X) (e : s ≫ p = 𝟙 Y)
    [GeometricallyConnected X.hom] : GeometricallyConnected Y.hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ z ↦ ?_⟩
  let f := pullback.map X.hom z Y.hom z p.left (𝟙 _) (𝟙 _) (by simp) (by simp)
  let g := pullback.map Y.hom z X.hom z s.left (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hg : g ≫ f = 𝟙 _ := by
    apply pullback.hom_ext
    · have e' := congrArg (fun m ↦ m.left) e
      change s.left ≫ p.left = 𝟙 _ at e'
      simp [f, g, Category.assoc, e']
    · simp [f, g]
  have hc : ConnectedSpace (pullback X.hom z : Scheme) :=
    pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f := X.hom)) L z
  have hs : Function.Surjective f := fun x ↦ ⟨g x, by change (g ≫ f) x = x; rw [hg]; rfl⟩
  exact hs.connectedSpace f.continuous

theorem geometricallyConnectedLimitSubgroups :
    Specs.CocharacterDynamics.GeometricallyConnectedLimitSubgroups.{u} := by
  intro k _ G _ _ c D
  obtain ⟨E⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  let P := D.parabolic.group.X
  let U := D.contracting.group.X
  let Z := D.centralizer.group.X
  let V := E.contracting.group.X
  let m := multiplyFactors E.contracting.inclusion D.parabolic.inclusion
  have hG := group_geometricallyIrreducible G
  have hm : IsOpenImmersion m.left := multiply_isOpenImmersion G c D E
  have hsurj : Surjective (m.left ≫ G.val.X.hom) := by
    constructor
    intro x
    exact ⟨(lift η[V] η[P]).left (IsLocalRing.closedPoint k), Subsingleton.elim _ _⟩
  have hW : GeometricallyIrreducible (V ⊗ P).hom := by
    rw [← Over.w m]
    infer_instance
  have hc (X : SchemeOver k) [GeometricallyIrreducible X.hom] :
      GeometricallyConnected X.hom := by
    constructor
    intro L _ z T fst snd h
    have := GeometricallyIrreducible.geometrically_irreducibleSpace z fst snd h
    infer_instance
  have hWc := hc (V ⊗ P)
  have hPc : GeometricallyConnected P.hom :=
    geometricallyConnected_of_retract (snd V P) (lift (1 : P ⟶ V) (𝟙 P)) (lift_snd _ _)
  let s := multiplyFactors D.sectionMap D.contractingToParabolic
  have hs : IsIso s := D.product_iso
  have hZUc : GeometricallyConnected (Z ⊗ U).hom :=
    geometricallyConnected_of_retract (inv s) s (IsIso.hom_inv_id s)
  exact ⟨hPc,
    geometricallyConnected_of_retract (snd Z U) (lift (1 : U ⟶ Z) (𝟙 U)) (lift_snd _ _),
    geometricallyConnected_of_retract (fst Z U) (lift (𝟙 Z) (1 : Z ⟶ U)) (lift_fst _ _)⟩

end

end LinearAlgebraicGroups.CocharacterDynamics
