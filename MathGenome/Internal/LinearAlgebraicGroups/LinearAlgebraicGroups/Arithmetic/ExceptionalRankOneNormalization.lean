import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneNormalization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Group
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open scoped Matrix CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneNormalization

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open Specs.ExceptionalRankOneNormalization
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootGroups (AdditiveLine rootPoint)
open RootData.RootGroups (additivePoints)

open private additiveLineGroup additiveLinePointsIso rootPoint_eq rootPoint_comp rootPoint_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private baseChangePointIso isAffine_baseChange groupIsoOfPointIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent
open private additiveIso_linear scaleIso scaleIso_point
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem diagonalConjugate_mul {R : Type u} [CommRing R]
    (t : Rˣ) (x y : SL₂ R) :
    diagonalConjugate t (x * y) = diagonalConjugate t x * diagonalConjugate t y := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp only [diagonalConjugate, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two]
  · change x.val 0 0 * y.val 0 0 + x.val 0 1 * y.val 1 0 =
      x.val 0 0 * y.val 0 0 + ((t : R) * x.val 0 1) * ((↑t⁻¹ : R) * y.val 1 0)
    linear_combination -(x.val 0 1 * y.val 1 0) * (Units.mul_inv t)
  · change (t : R) * (x.val 0 0 * y.val 0 1 + x.val 0 1 * y.val 1 1) =
      x.val 0 0 * ((t : R) * y.val 0 1) + ((t : R) * x.val 0 1) * y.val 1 1
    ring
  · change (↑t⁻¹ : R) * (x.val 1 0 * y.val 0 0 + x.val 1 1 * y.val 1 0) =
      ((↑t⁻¹ : R) * x.val 1 0) * y.val 0 0 + x.val 1 1 * ((↑t⁻¹ : R) * y.val 1 0)
    ring
  · change x.val 1 0 * y.val 0 1 + x.val 1 1 * y.val 1 1 =
      ((↑t⁻¹ : R) * x.val 1 0) * ((t : R) * y.val 0 1) + x.val 1 1 * y.val 1 1
    linear_combination -(x.val 1 0 * y.val 0 1) * (Units.inv_mul t)

private theorem diagonalConjugate_inverse {R : Type u} [CommRing R]
    (t : Rˣ) (m : SL₂ R) :
    diagonalConjugate t⁻¹ (diagonalConjugate t m) = m := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change (↑t⁻¹ : R) * ((t : R) * m.val 0 1) = m.val 0 1
    simp [← mul_assoc]
  · change (t : R) * ((↑t⁻¹ : R) * m.val 1 0) = m.val 1 0
    simp [← mul_assoc]
  · rfl

private theorem diagonalConjugate_upper {R : Type u} [CommRing R] (t : Rˣ) (a : R) :
    diagonalConjugate t (upper a) = upper ((t : R) * a) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagonalConjugate, upper]

private theorem diagonalConjugate_lower {R : Type u} [CommRing R] (t : Rˣ) (a : R) :
    diagonalConjugate t (lower a) = lower ((↑t⁻¹ : R) * a) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagonalConjugate, lower]

private theorem diagonalConjugate_diagonal {R : Type u} [CommRing R] (t s : Rˣ) :
    diagonalConjugate t (diagonal s) = diagonal s := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagonalConjugate, diagonal]

private theorem diagonalConjugate_antiDiagonal {R : Type u} [CommRing R] (t : Rˣ) :
    diagonalConjugate t (antiDiagonal R) = diagonal t * antiDiagonal R := by
  apply Subtype.ext
  simp [diagonalConjugate, diagonal, antiDiagonal]

private def matrixScaling (c : Kˣ) : matrixPoints K ≅ matrixPoints K :=
  NatIso.ofComponents (fun R =>
    let t := Units.map (algebraMap K R) c
    (show SL₂ R ≃* SL₂ R from
      { toFun := diagonalConjugate t
        invFun := diagonalConjugate t⁻¹
        left_inv := diagonalConjugate_inverse t
        right_inv := fun x => by simpa only [inv_inv] using diagonalConjugate_inverse t⁻¹ x
        map_mul' := diagonalConjugate_mul t }).toGrpIso)
    (by
      intro R S f
      apply GrpCat.ext
      intro x
      symm
      change Matrix.SpecialLinearGroup.map f.hom.toRingHom
        (diagonalConjugate (Units.map (algebraMap K R) c) x) =
        diagonalConjugate (Units.map (algebraMap K S) c)
          (Matrix.SpecialLinearGroup.map f.hom.toRingHom x)
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j
      · rfl
      · change f.hom (algebraMap K R (c : K) * x.val 0 1) =
          algebraMap K S (c : K) * f.hom (x.val 0 1)
        rw [map_mul, AlgHom.commutes]
      · change f.hom (algebraMap K R (↑c⁻¹ : K) * x.val 1 0) =
          algebraMap K S (↑c⁻¹ : K) * f.hom (x.val 1 0)
        rw [map_mul, AlgHom.commutes]
      · rfl)

private theorem representedScaling {S : AffineAlgebraicGroup K}
    (m : (groupPointsFunctor K).obj S.val ≅ matrixPoints K) (c : Kˣ) :
    ∃ i : S.val ≅ S.val, (groupPointsFunctor K).map i.hom =
      (m ≪≫ matrixScaling c ≪≫ m.symm).hom := by
  let := S.property.1
  exact ⟨groupIsoOfPointIso _, (groupHomEquiv S.val S.val inferInstance).apply_symm_apply _⟩

/-- The scalar extension of a standard additive line has the same evaluation
coordinate on every test algebra. -/
private theorem additiveScalarExtension (A : AdditiveLine F) (B : AdditiveLine K) :
    ∃ e : B.group ≅ (groupBaseChange F K).obj A.group,
      ∀ (R : TestAlgebra K) (a : R),
        baseChangePoint F K A.group.X R (rootPoint e.hom R a) =
          additivePoints A ((restrictTestAlgebra F K).obj R) a := by
  let := (additiveLineGroup A).property.1
  let := (additiveLineGroup B).property.1
  let := isAffine_baseChange K A.group
  let q : Specs.StandardGroups.additivePoints K ≅
      restrictTestAlgebra F K ⋙ Specs.StandardGroups.additivePoints F :=
    Iso.refl _
  let n := (additiveLinePointsIso B).symm ≪≫ q ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra F K) (additiveLinePointsIso A) ≪≫
      (baseChangePointIso K A.group).symm
  let e := groupIsoOfPointIso n
  refine ⟨e, ?_⟩
  intro R a
  have he : (groupPointsFunctor K).map e.hom = n.hom :=
    (groupHomEquiv B.group ((groupBaseChange F K).obj A.group) inferInstance).apply_symm_apply _
  rw [rootPoint_eq]
  change (baseChangePointGroupEquiv K A.group R)
    ((((groupPointsFunctor K).map e.hom).app R).hom (additivePoints B R a)) = _
  rw [he]
  change (baseChangePointGroupEquiv K A.group R)
    ((baseChangePointGroupEquiv K A.group R).symm
      (additivePoints A ((restrictTestAlgebra F K).obj R)
        ((additivePoints B R).symm (additivePoints B R a)))) = _
  rw [MulEquiv.apply_symm_apply, Equiv.symm_apply_apply]

private theorem coordinateComparison {J L : GroupScheme F} {A : AdditiveLine F}
    {B : AdditiveLine K} (f : L ⟶ J) (x : A.group ≅ L)
    (xK : B.group ≅ (groupBaseChange F K).obj L) :
    ∃ c : Kˣ, ∀ (R : TestAlgebra K) (a : R),
      baseChangePoint F K J.X R
        (rootPoint (xK.hom ≫ (groupBaseChange F K).map f) R (algebraMap K R (c : K) * a)) =
        rootPoint (x.hom ≫ f) ((restrictTestAlgebra F K).obj R) a := by
  obtain ⟨e, he⟩ := additiveScalarExtension A B
  let E := groupBaseChange F K
  let i := e ≪≫ E.mapIso x ≪≫ xK.symm
  obtain ⟨c, hc⟩ := additiveIso_linear B B i
  refine ⟨c, fun R a => ?_⟩
  have h : i.hom ≫ (xK.hom ≫ E.map f) = e.hom ≫ E.map (x.hom ≫ f) := by
    simp [i, E, Functor.map_comp]
  have h' := rootPoint_comp i.hom (xK.hom ≫ E.map f) R a
  rw [h, hc, ← rootPoint_eq] at h'
  rw [← h', rootPoint_comp, rootPoint_eq (x.hom ≫ f)]
  have hn := baseChangePointsSchemeNaturality F K (x.hom ≫ f).hom.hom R (rootPoint e.hom R a)
  rw [he R a] at hn
  exact hn

private theorem exists_diagonal_separator (k : Type u) [Field k] [IsSepClosed k] :
    ∃ t : kˣ, (t : k) ≠ ↑t⁻¹ := by
  suffices ∃ a : k, a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 by
    obtain ⟨a, ha, h₁, h₂⟩ := this
    refine ⟨Units.mk0 a ha, fun h ↦ ?_⟩
    have hsq : a * a = 1 := by
      change (Units.mk0 a ha : k) * (Units.mk0 a ha : k) = 1
      nth_rw 2 [h]
      exact Units.mul_inv _
    have hm : (a - 1) * (a + 1) = 0 := by linear_combination hsq
    exact (mul_ne_zero (sub_ne_zero.mpr h₁) (by
      intro hz
      apply h₂
      linear_combination hz)) hm
  by_cases h₂ : (2 : k) = 0
  · obtain ⟨a, ha⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C
      (n := 2) (1 : k) (-1) (-1) h₂ (by decide) (neg_ne_zero.mpr one_ne_zero)
    have hneg : (-1 : k) = 1 := by linear_combination -h₂
    refine ⟨a, ?_, ?_, ?_⟩
    · rintro rfl
      norm_num at ha
    · rintro rfl
      norm_num at ha
    · rw [hneg]
      rintro rfl
      norm_num at ha
  by_cases h₃ : (3 : k) = 0
  · obtain ⟨a, ha⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C
      (n := 3) (1 : k) (-1) (-1) h₃ (by decide) (neg_ne_zero.mpr one_ne_zero)
    refine ⟨a, ?_, ?_, ?_⟩
    · rintro rfl
      norm_num at ha
    · rintro rfl
      norm_num at ha
    · rintro rfl
      norm_num at ha
  refine ⟨2, h₂, ?_, fun h ↦ h₃ ?_⟩
  · intro h
    have hz : (1 : k) = 0 := by linear_combination h
    exact one_ne_zero hz
  · linear_combination h

private lemma word_entries {k : Type u} [Field k] (v : k) :
    (upper 1 * lower v * upper 1 : SL₂ k).val = !![1 + v, 2 + v; v, 1 + v] := by
  simp only [upper, lower, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

private lemma word_neg_one {k : Type u} [Field k] :
    upper 1 * lower (-1 : k) * upper 1 = antiDiagonal k := by
  apply Subtype.ext
  rw [word_entries]
  simp [antiDiagonal, show (2 : k) + -1 = 1 by ring]

/-- The anti-diagonal is detected among the indicated nonzero Gauss words by
the normalizer of a commutative subgroup containing the diagonal. -/
private theorem word_normalizes_iff {k : Type u} [Field k] [IsSepClosed k]
    {H : Type u} [Group H] (f : SL₂ k →* H) (hf : Function.Injective f)
    (D : Subgroup H) (hcomm : ∀ a ∈ D, ∀ b ∈ D, Commute a b)
    (hd : ∀ t : kˣ, f (diagonal t) ∈ D) (hw : f (antiDiagonal k) ∈ Subgroup.normalizer D)
    {v : k} (hv : v ≠ 0) :
    f (upper 1 * lower v * upper 1) ∈ Subgroup.normalizer D ↔ v = -1 := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := exists_diagonal_separator k
    let p : SL₂ k := upper 1 * lower v * upper 1
    let d := diagonal t
    let z := p * d * p⁻¹
    have hz : f z ∈ D := by
      change f ((p * d) * p⁻¹) ∈ D
      rw [map_mul, map_mul, map_inv]
      exact ((Subgroup.mem_normalizer_iff.mp h) (f d)).mp (hd t)
    have hc : Commute z d := by
      show z * d = d * z
      apply hf
      exact (f.map_mul z d).trans ((hcomm _ hz _ (hd t)).eq.trans (f.map_mul d z).symm)
    have hentries := congrArg (fun m : SL₂ k ↦ m.val 1 0) hc.eq
    change (z.val * d.val) 1 0 = (d.val * z.val) 1 0 at hentries
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at hentries
    change z.val 1 0 * (t : k) + z.val 1 1 * 0 =
      0 * z.val 0 0 + (↑t⁻¹ : k) * z.val 1 0 at hentries
    have hz0 : z.val 1 0 = 0 := by
      have hm : z.val 1 0 * ((t : k) - ↑t⁻¹) = 0 := by linear_combination hentries
      exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr ht)
    have hval : z.val 1 0 = v * (1 + v) * ((t : k) - ↑t⁻¹) := by
      change ((p.val * d.val) * p.val.adjugate) 1 0 = _
      rw [show p.val = !![1 + v, 2 + v; v, 1 + v] from word_entries v]
      simp only [d, diagonal, Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
      change (v * (t : k) + (1 + v) * 0) * (1 + v) +
        (v * 0 + (1 + v) * (↑t⁻¹ : k)) * -v = _
      ring
    rw [hval] at hz0
    have hv1 := (mul_eq_zero.mp ((mul_eq_zero.mp hz0).resolve_right (sub_ne_zero.mpr ht))).resolve_left hv
    linear_combination hv1
  · rintro rfl
    simpa only [word_neg_one] using hw

private abbrev pointHom {k : Type u} [Field k] {G H : GroupScheme k}
    (f : G ⟶ H) (R : TestAlgebra k) : GroupPoints G R →* GroupPoints H R :=
  (((groupPointsFunctor k).map f).app R).hom

private theorem range_commutes {k : Type u} [Field k] {G H : GroupScheme k}
    [IsCommMonObj H.X] (j : H ⟶ G) (R : TestAlgebra k) :
    ∀ a ∈ (pointHom j R).range, ∀ b ∈ (pointHom j R).range, Commute a b := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact (show Commute a b from Hom.commMonoid.mul_comm a b).map (pointHom j R)

private theorem baseChange_pointHom {G T : GroupScheme F} (f : T ⟶ G)
    (R : TestAlgebra K) (p : GroupPoints ((groupBaseChange F K).obj T) R) :
    baseChangePoint F K G.X R (pointHom ((groupBaseChange F K).map f) R p) =
      pointHom f ((restrictTestAlgebra F K).obj R) (baseChangePoint F K T.X R p) :=
  baseChangePointsSchemeNaturality F K f.hom.hom R p

private abbrev pointRangeNormalizer {k : Type u} [Field k] {G T : GroupScheme k}
    (i : T ⟶ G) (R : TestAlgebra k) : Subgroup (GroupPoints G R) :=
  Subgroup.normalizer (pointHom i R).range

private theorem normalizer_mulEquiv {X Y : Type u} [Group X] [Group Y]
    (e : X ≃* Y) {D : Subgroup X} {E : Subgroup Y}
    (he : ∀ q, e q ∈ E ↔ q ∈ D) (p : X) :
    e p ∈ Subgroup.normalizer E ↔ p ∈ Subgroup.normalizer D := by
  have hconj (q : X) : e (p * q * p⁻¹) = e p * e q * (e p)⁻¹ := by simp
  constructor
  · intro h
    apply Subgroup.mem_normalizer_iff.mpr
    intro q
    rw [← he q, ← he (p * q * p⁻¹), hconj]
    exact Subgroup.mem_normalizer_iff.mp h (e q)
  · intro h
    apply Subgroup.mem_normalizer_iff.mpr
    intro q
    obtain ⟨q, rfl⟩ := e.surjective q
    rw [← hconj, he q, he (p * q * p⁻¹)]
    exact Subgroup.mem_normalizer_iff.mp h q

private theorem normalizerOfBaseChange {G T : GroupScheme F} (f : T ⟶ G)
    (R : TestAlgebra K) (p : GroupPoints ((groupBaseChange F K).obj G) R) :
    (baseChangePoint F K G.X R p : GroupPoints G ((restrictTestAlgebra F K).obj R)) ∈
        pointRangeNormalizer f ((restrictTestAlgebra F K).obj R) ↔
      p ∈ pointRangeNormalizer ((groupBaseChange F K).map f) R := by
  let e : GroupPoints ((groupBaseChange F K).obj G) R ≃*
      GroupPoints G ((restrictTestAlgebra F K).obj R) := baseChangePointGroupEquiv K G R
  let eT : GroupPoints ((groupBaseChange F K).obj T) R ≃*
      GroupPoints T ((restrictTestAlgebra F K).obj R) := baseChangePointGroupEquiv K T R
  let D := (pointHom f ((restrictTestAlgebra F K).obj R)).range
  let DK := (pointHom ((groupBaseChange F K).map f) R).range
  have h (q : GroupPoints ((groupBaseChange F K).obj G) R) : e q ∈ D ↔ q ∈ DK := by
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨eT.symm a, e.injective ?_⟩
      exact (baseChange_pointHom f R (eT.symm a)).trans
        ((congrArg (pointHom f _) (eT.apply_symm_apply a)).trans ha)
    · rintro ⟨a, rfl⟩
      exact ⟨eT a, (baseChange_pointHom f R a).symm⟩
  exact normalizer_mulEquiv (D := DK) (E := D) e h p

private theorem mapPoints_range_normalizer {G T : GroupScheme F}
    (i : T ⟶ G) {R : TestAlgebra F} (s : R ≅ R)
    {p : GroupPoints G R} (hp : p ∈ pointRangeNormalizer i R) :
    (mapPoints s.hom p : GroupPoints G R) ∈ pointRangeNormalizer i R := by
  let e := (((groupPointsFunctor F).obj G).mapIso s)
  let eT := (((groupPointsFunctor F).obj T).mapIso s)
  let D := (pointHom i R).range
  have hp' (q : GroupPoints G R) : e.hom q ∈ D ↔ q ∈ D := by
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨eT.inv a, ?_⟩
      change mapPoints s.inv a ≫ i.hom.hom = q
      rw [show mapPoints s.inv a ≫ i.hom.hom = mapPoints s.inv (a ≫ i.hom.hom) from
        Category.assoc _ _ _]
      change e.inv (pointHom i R a) = q
      rw [ha]
      exact ConcreteCategory.congr_hom e.hom_inv_id q
    · rintro ⟨a, rfl⟩
      exact ⟨eT.hom a,
        ConcreteCategory.congr_hom (((groupPointsFunctor F).map i).naturality s.hom) a⟩
  let equiv := MulEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)
  exact (normalizer_mulEquiv (D := D) (E := D) equiv hp' p).mpr hp

private def testAlgebraAutomorphism (R : TestAlgebra F) (e : R ≃+* R)
    (he : ∀ a, e (algebraMap F R a) = algebraMap F R a) : R ≅ R :=
  CommAlgCat.isoMk (show R ≃ₐ[F] R from { toRingEquiv := e, commutes' := he })

private theorem scaledCoordinate_point {G U : GroupScheme F} {A : AdditiveLine F}
    (y : A.group ≅ U) (i : U ⟶ G) (a : Fˣ) (R : TestAlgebra F) (z : R) :
    rootPoint ((scaleIso A A a ≪≫ y).hom ≫ i) R z =
      rootPoint (y.hom ≫ i) R (algebraMap F R (a : F) * z) := by
  rw [Iso.trans_hom, Category.assoc, rootPoint_comp, scaleIso_point, rootPoint_eq (y.hom ≫ i)]

private theorem matrixMap_injective {S : AffineAlgebraicGroup K} {H : GroupScheme K}
    (m : (groupPointsFunctor K).obj S.val ≅ matrixPoints K)
    (j : S.val ⟶ H) (hj : IsClosedImmersion j.hom.hom.left) (R : TestAlgebra K) :
    Function.Injective (matrixMap m j R) := by
  let := hj
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (m.inv.app R)).1
  apply CategoryTheory.Over.OverMorphism.ext
  apply (cancel_mono j.hom.hom.left).mp
  exact congrArg (fun p : GroupPoints H R ↦ p.left) hab

set_option maxHeartbeats 1000000 in
/-- Normalize the positive coordinate by a geometric unit, then use the
rational torus normalizer to recover the remaining change of coordinate
over the ground field. -/
theorem normalizeRootCoordinates : NormalizeRootCoordinates.{u} := by
  intro F K _ _ _ hK G T U V hT A B x y E xK yK S m j hj hx hy hd hw
  obtain ⟨c, hc⟩ := coordinateComparison U.inclusion x xK
  obtain ⟨d, hd'⟩ := coordinateComparison V.inclusion y yK
  obtain ⟨i, hi⟩ := representedScaling m c
  let j' := i.hom ≫ j
  have hj' : IsClosedImmersion j'.hom.hom.left := by
    let := hj
    let : IsIso i.hom.hom.hom.left :=
      (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso i.hom
    change IsClosedImmersion (i.hom.hom.hom.left ≫ j.hom.hom.left)
    infer_instance
  have hMap (R : TestAlgebra K) (g : SL₂ R) :
      matrixMap m j' R g = matrixMap m j R (diagonalConjugate (Units.map (algebraMap K R) c) g) := by
    have h := ConcreteCategory.congr_hom (congrArg (fun a => a.app R) hi) (m.inv.app R g)
    have h₀ := ConcreteCategory.congr_hom (m.inv_hom_id_app R) g
    change (((groupPointsFunctor K).map i.hom).app R) (m.inv.app R g) =
      m.inv.app R (diagonalConjugate (Units.map (algebraMap K R) c)
        (m.hom.app R (m.inv.app R g))) at h
    rw [show m.hom.app R (m.inv.app R g) = g from h₀] at h
    exact congrArg (((groupPointsFunctor K).map j).app R) h
  have hDiag (R : TestAlgebra K) (t : Rˣ) :
      matrixMap m j' R (diagonal t) = matrixMap m j R (diagonal t) := by
    rw [hMap, diagonalConjugate_diagonal]
  have hUpper (R : TestAlgebra K) (a : R) :
      baseChangePoint F K G.val.X R (matrixMap m j' R (upper a)) =
        rootPoint (x.hom ≫ U.inclusion) ((restrictTestAlgebra F K).obj R) a := by
    rw [hMap, diagonalConjugate_upper, hx]
    exact hc R a
  let RK := CommAlgCat.of K K
  let R := (restrictTestAlgebra F K).obj RK
  let eG := baseChangePointGroupEquiv K G.val RK
  let f : SL₂ K →* GroupPoints G.val R := eG.toMonoidHom.comp (matrixMap m j' RK)
  let D := (pointHom T.inclusion R).range
  let : IsCommMonObj T.group.X :=
    torus_commutative (Specs.Unipotent.closedSubgroupAlgebraicGroup T) hT
  have hD : ∀ t : Kˣ, f (diagonal t) ∈ D := by
    obtain ⟨q, hq⟩ := hd
    intro t
    refine ⟨baseChangePoint F K T.group.X RK
      (LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint q RK t), ?_⟩
    change _ = baseChangePoint F K G.val.X RK (matrixMap m j' RK (diagonal t))
    rw [hDiag, hq]
    exact (baseChange_pointHom T.inclusion RK _).symm
  have hW : f (antiDiagonal K) ∈ Subgroup.normalizer D := by
    let DK := (pointHom (E.map T.inclusion) RK).range
    have hc' : Units.map (algebraMap K RK) c = c := by
      apply Units.ext
      exact Algebra.algebraMap_self_apply (c : K)
    have hconj := hMap RK (antiDiagonal K)
    rw [diagonalConjugate_antiDiagonal, hc', map_mul] at hconj
    have hdiagonal : matrixMap m j RK (diagonal c) ∈ DK := by
      obtain ⟨q, hq⟩ := hd
      exact ⟨LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint q RK c, (hq RK c).symm⟩
    have hnew : matrixMap m j' RK (antiDiagonal K) ∈ Subgroup.normalizer DK := by
      rw [hconj]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer (H := DK) hdiagonal) hw
    exact (normalizerOfBaseChange T.inclusion RK (matrixMap m j' RK (antiDiagonal K))).mpr hnew
  let s := c * d
  have hs (b : K) : f (lower ((s : K) * b)) =
      rootPoint (y.hom ≫ V.inclusion) R b := by
    change baseChangePoint F K G.val.X RK (matrixMap m j' RK (lower ((s : K) * b))) = _
    rw [hMap, diagonalConjugate_lower, hy, ← hd' RK b]
    congr 2
    change (algebraMap K K (↑c⁻¹ : K)) * ((c : K) * (d : K) * b) =
      algebraMap K K (d : K) * b
    simp [← mul_assoc]
  let w (b : K) : GroupPoints G.val R :=
    rootPoint (x.hom ≫ U.inclusion) R 1 *
      rootPoint (y.hom ≫ V.inclusion) R b * rootPoint (x.hom ≫ U.inclusion) R 1
  have hword (b : K) : f (upper 1 * lower ((s : K) * b) * upper 1) = w b := by
    rw [map_mul, map_mul, hs]
    change baseChangePoint F K G.val.X RK (matrixMap m j' RK (upper 1)) * _ * _ = _
    change _ * _ * baseChangePoint F K G.val.X RK (matrixMap m j' RK (upper 1)) = _
    rw [hUpper]
  have : IsSepClosed K := hK.sep_closed
  have hcriterion (b : K) (hb : b ≠ 0) :
      w b ∈ Subgroup.normalizer D ↔ (s : K) * b = -1 := by
    rw [← hword]
    exact word_normalizes_iff f (eG.injective.comp (matrixMap_injective m j' hj' RK))
      D (range_commutes T.inclusion R) hD hW (mul_ne_zero s.ne_zero hb)
  let b : K := -(↑s⁻¹ : K)
  have hb : b ≠ 0 := neg_ne_zero.mpr s⁻¹.ne_zero
  have hsb : (s : K) * b = -1 := by simp [b]
  have hwb := (hcriterion b hb).mpr hsb
  have hfixed (σ : K ≃ₐ[F] K) : σ b = b := by
    let σR := testAlgebraAutomorphism R σ.toRingEquiv (fun z => by
      change σ (algebraMap K K (algebraMap F K z)) = algebraMap K K (algebraMap F K z)
      simpa only [Algebra.algebraMap_self_apply] using σ.commutes z)
    have h := mapPoints_range_normalizer T.inclusion σR hwb
    have hmap : mapPoints σR.hom (w b) = w (σ b) := by
      let p := ((groupPointsFunctor F).obj G.val).map σR.hom
      change p.hom (w b) = _
      dsimp only [w]
      rw [map_mul, map_mul]
      change mapPoints σR.hom (rootPoint (x.hom ≫ U.inclusion) R 1) *
        mapPoints σR.hom (rootPoint (y.hom ≫ V.inclusion) R b) *
        mapPoints σR.hom (rootPoint (x.hom ≫ U.inclusion) R 1) = _
      simp only [rootPoint_natural]
      change rootPoint (x.hom ≫ U.inclusion) R (σ 1) *
        rootPoint (y.hom ≫ V.inclusion) R (σ b) *
        rootPoint (x.hom ≫ U.inclusion) R (σ 1) = _
      simp only [map_one]
    rw [hmap] at h
    have hσb : σ b ≠ 0 := fun hz => hb (σ.injective (hz.trans (map_zero σ).symm))
    exact mul_left_cancel₀ s.ne_zero (((hcriterion (σ b) hσb).mp h).trans hsb.symm)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed b).mpr hfixed
  have ha₀ : -a ≠ 0 := by
    intro h
    apply hb
    rw [← ha, neg_eq_zero.mp h, map_zero]
  let a' := Units.mk0 (-a) ha₀
  let y' := scaleIso A A a' ≪≫ y
  refine ⟨c, j', x, y', hj', hMap, hDiag, hUpper, ?_⟩
  intro Q z
  have hscalar : algebraMap F ((restrictTestAlgebra F K).obj Q) (a' : F) =
      (algebraMap K Q) (↑s⁻¹ : K) := by
    change algebraMap K Q (algebraMap F K (-a)) = _
    rw [map_neg, ha]
    simp [b]
  rw [scaledCoordinate_point y V.inclusion a', hscalar, ← hd' Q, hMap,
    diagonalConjugate_lower, hy]
  have hunit : d * s⁻¹ = c⁻¹ := by dsimp [s]; group
  have hparam : algebraMap K Q (d : K) * (algebraMap K Q (↑s⁻¹ : K) * z) =
      algebraMap K Q (↑c⁻¹ : K) * z := by
    rw [← mul_assoc, ← map_mul]
    exact congrArg (fun r : Kˣ => algebraMap K Q (r : K) * z) hunit
  exact congrArg (fun t : Q => baseChangePoint F K G.val.X Q
    (rootPoint (yK.hom ≫ E.map V.inclusion) Q t)) hparam.symm

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneNormalization
