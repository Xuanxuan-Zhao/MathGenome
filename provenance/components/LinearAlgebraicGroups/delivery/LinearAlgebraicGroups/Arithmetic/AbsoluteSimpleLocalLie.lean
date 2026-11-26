import Specs.LinearAlgebraicGroups.Arithmetic.AbsoluteSimpleLocalLie
import LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
import LinearAlgebraicGroups.Affine.Components
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.RingTheory.Ideal.IdempotentFG

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Topology TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open InfinitesimalCommutator

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

open private CommutesOver commutesOver_iff familyCentralizerIntersection
  commutesOver_of_lie_eq_zero lieZeroPoint pointConjugation pointConjugationIso
  pointConjugation_apply point_kernel_of_iso conj_commute normalOfRationalConjugation
  liftThroughOpen dualSpec_reduction_surjective groupLieRadical_eq_bot
  from LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
open private point_liftST_injective from LinearAlgebraicGroups.Affine.LieBracket
open private mono_over conjugation whisker_conjugation familyFactorizationLocus
  from LinearAlgebraicGroups.Affine.Stabilizers
open private sectionOfClosedPoint sectionOfClosedPoint_apply irreducible_of_connected_over_algClosed
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private isIso_of_schemeIso from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private tangent_coordinates from LinearAlgebraicGroups.Affine.AdjointRepresentation

variable {k : Type u} [Field k]

private theorem lie_eq_zero_of_commutesOver {G : GroupScheme k} [IsAffine G.X.left]
    (s : IdentityLieStructure G) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ x y : Lie k G, CommutesOver x.toMul.val y.toMul.val →
      ⁅x, y⁆ = @Zero.zero _ s.lieRing.toAddGroup.toZero := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro x y h
  apply Subtype.ext
  change (⁅x, y⁆ : Lie k G).toMul.val = (@Zero.zero _ s.lieRing.toAddGroup.toZero).toMul.val
  rw [lieZeroPoint s]
  apply point_liftST_injective G
  have H := s.commutator_law x y
  change (((groupPointsFunctor k).obj G).map (CommAlgCat.ofHom (liftST k))).hom
    (⁅x, y⁆ : Lie k G).toMul.val = commutator ((groupPointsFunctor k).obj G) x y at H
  rw [H, map_one]
  have hc := (commutesOver_iff _ _).mp h
    ((testSpec k).obj (op (CommAlgCat.of k (TwoVariables k))))
    ((testSpec k).map (CommAlgCat.ofHom (liftS k)).op)
    ((testSpec k).map (CommAlgCat.ofHom (liftT k)).op)
  let p : Points G.X (CommAlgCat.of k (TwoVariables k)) :=
    (testSpec k).map (CommAlgCat.ofHom (liftS k)).op ≫ x.toMul.val
  let q : Points G.X (CommAlgCat.of k (TwoVariables k)) :=
    (testSpec k).map (CommAlgCat.ofHom (liftT k)).op ≫ y.toMul.val
  change p * q * p⁻¹ * q⁻¹ = 1
  have hpq : p * q = q * p := hc.eq
  rw [hpq]
  group

/-- A transporter from one closed subgroup into another is cut out by closed equations. -/
private theorem closedTransporter (G : AffineAlgebraicGroup k)
    (C D : ClosedSubgroup G.val) :
    ∃ (Z : SchemeOver k) (j : Z ⟶ G.val.X), IsClosedImmersion j.left ∧
      ∀ (T : SchemeOver k) (p : T ⟶ G.val.X),
        (∃ a : C.group.X ⊗ T ⟶ D.group.X,
          a ≫ D.inclusion.hom.hom = conjugateFamily C.inclusion p) ↔
          ∃ y : T ⟶ Z, y ≫ j = p := by
  letI := G.property.1
  letI := C.isClosedImmersion
  letI : IsAffine C.group.X.left := isAffine_of_isAffineHom C.inclusion.hom.hom.left
  let f := conjugation C.inclusion
  let d := pullback.fst f D.inclusion.hom.hom
  have hd : IsClosedImmersion d.left :=
    MorphismProperty.of_isPullback
      (((IsPullback.of_hasPullback f D.inclusion.hom.hom).map (Over.forget _)).flip)
      D.isClosedImmersion
  obtain ⟨Z, j, hj, h⟩ := familyFactorizationLocus d hd
  refine ⟨Z, j, hj, fun T p ↦ ?_⟩
  rw [← h]
  constructor
  · rintro ⟨a, ha⟩
    have eq : (C.group.X ◁ p) ≫ f = a ≫ D.inclusion.hom.hom :=
      (whisker_conjugation C.inclusion p).trans ha.symm
    exact ⟨pullback.lift _ _ eq, pullback.lift_fst _ _ _⟩
  · rintro ⟨a, ha⟩
    refine ⟨a ≫ pullback.snd _ _, ?_⟩
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha]
    exact whisker_conjugation C.inclusion p

private theorem rationalTransporter (G : AffineAlgebraicGroup k)
    {C D : ClosedSubgroup G.val} (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    (∃ a : C.group.X ⊗ 𝟙_ (SchemeOver k) ⟶ D.group.X,
      a ≫ D.inclusion.hom.hom = conjugateFamily C.inclusion g) ↔
    ∃ a : C.group.X ⟶ D.group.X,
      a ≫ D.inclusion.hom.hom = C.inclusion.hom.hom ≫ (pointConjugation g).hom.hom := by
  let S := C.group.X
  let e := ρ_ S
  have h : conjugateFamily C.inclusion g =
      e.hom ≫ C.inclusion.hom.hom ≫ (pointConjugation g).hom.hom := by
    rw [pointConjugation_apply]
    have hfst : e.hom = fst S (𝟙_ (SchemeOver k)) := rightUnitor_hom _
    have hsnd : e.hom ≫ toUnit S = snd S (𝟙_ (SchemeOver k)) :=
      (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      hsnd, hfst]
    rfl
  rw [h]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨e.inv ≫ a, by rw [Category.assoc, ha, e.inv_hom_id_assoc]⟩
  · rintro ⟨a, ha⟩
    exact ⟨e.hom ≫ a, by rw [Category.assoc, ha]⟩

private theorem brackets_of_distinct_atoms {L : Type u} [LieRing L] [LieAlgebra k L]
    {I J : LieIdeal k L} (hI : IsAtom I) (hJ : IsAtom J) (hne : I ≠ J) :
    ∀ x ∈ I, ∀ y ∈ J, ⁅x, y⁆ = (0 : L) := by
  intro x hx y hy
  have hdis : Disjoint I J := hI.disjoint_of_ne hJ hne
  rw [disjoint_iff] at hdis
  have hm : ⁅x, y⁆ ∈ I ⊓ J :=
    ⟨lie_mem_left k L I x y hx, lie_mem_right k L J x y hy⟩
  rwa [hdis, LieSubmodule.mem_bot] at hm

private theorem exists_nonzero_bracket_in_atom {L : Type u} [LieRing L] [LieAlgebra k L]
    [LieAlgebra.IsSemisimple k L] {I : LieIdeal k L} (hI : IsAtom I) :
    ∃ x ∈ I, ∃ y ∈ I, ⁅x, y⁆ ≠ (0 : L) := by
  by_contra! h
  apply LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI
  exact ⟨fun x y ↦ Subtype.ext (h x x.property y y.property)⟩

private def idealConjugation {L : Type u} [LieRing L] [LieAlgebra k L]
    (d : L ≃ₗ⁅k⁆ L) : LieIdeal k L ≃o LieIdeal k L where
  toFun I := I.comap d.symm.toLieHom
  invFun I := I.comap d.toLieHom
  left_inv I := by ext x; change d.symm (d x) ∈ I ↔ _; rw [d.symm_apply_apply]
  right_inv I := by ext x; change d (d.symm x) ∈ I ↔ _; rw [d.apply_symm_apply]
  map_rel_iff' := by
    intro I J
    change I.comap d.symm.toLieHom ≤ J.comap d.symm.toLieHom ↔ I ≤ J
    refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ h hx⟩
    have hx' : d x ∈ I.comap d.symm.toLieHom := by
      change d.symm (d x) ∈ I
      rwa [d.symm_apply_apply]
    have hh := h hx'
    change d.symm (d x) ∈ J at hh
    rwa [d.symm_apply_apply] at hh

private theorem centralizerTransport (G : AffineAlgebraicGroup k)
    (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (I J : LieIdeal k (Lie k G.val)) (C D : ClosedSubgroup G.val),
      RepresentsSubgroup C (fun _ g ↦ ∀ x ∈ I, CommutesOver x.toMul.val g) →
      RepresentsSubgroup D (fun _ g ↦ ∀ x ∈ J, CommutesOver x.toMul.val g) →
      ∀ (g : 𝟙_ (SchemeOver k) ⟶ G.val.X)
        (d : Lie k G.val ≃ₗ⁅k⁆ Lie k G.val),
        (∀ x, d x = mapPointKernel (pointConjugationIso g⁻¹).hom x) →
        (∀ x ∈ J, d x ∈ I) →
        ∃ a : C.group.X ⟶ D.group.X,
          a ≫ D.inclusion.hom.hom = C.inclusion.hom.hom ≫ (pointConjugation g).hom.hom := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro I J C D hC hD g d hd hJI
  refine (hD _ _).mp ?_
  intro x hx
  have fix := (hC _ C.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩ (d x) (hJI x hx)
  apply (commutesOver_iff _ _).mpr
  intro U a t
  have hf := (commutesOver_iff _ _).mp fix U a t
  rw [hd] at hf
  change Commute (a ≫ x.toMul.val ≫ (pointConjugation g⁻¹).hom.hom)
    (t ≫ C.inclusion.hom.hom) at hf
  rw [← Category.assoc t C.inclusion.hom.hom]
  exact conj_commute g _ _ (by simpa only [Category.assoc] using hf)

/-- The scheme centralizer of an atomic Lie ideal is normal. The finitely
many atomic ideals give closed transporter loci covering the rational points. -/
private theorem atomCentralizerNormal [IsAlgClosed k] [CharZero k]
    (G : AffineAlgebraicGroup k) [ConnectedSpace G.val.X.left]
    (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ [FiniteDimensional k (Lie k G.val)] [LieAlgebra.IsSemisimple k (Lie k G.val)]
      (I : LieIdeal k (Lie k G.val)), IsAtom I →
      ∀ C : ClosedSubgroup G.val,
        RepresentsSubgroup C (fun _ g ↦ ∀ x ∈ I, CommutesOver x.toMul.val g) →
        IsNormalSubgroup C.inclusion := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  intro _ _ I hI C hC
  let L := Lie k G.val
  let Atom := {J : LieIdeal k L // IsAtom J}
  letI : Finite Atom :=
    (WellFoundedGT.finite_of_sSupIndep
      (LieAlgebra.IsSemisimple.sSupIndep_isAtom (R := k) (L := L))).to_subtype
  letI := Fintype.ofFinite Atom
  letI := G.property.1
  letI := G.property.2.1
  letI := G.property.2.2
  letI : JacobsonSpace G.val.X.left := LocallyOfFiniteType.jacobsonSpace G.val.X.hom
  letI : IrreducibleSpace G.val.X.left := irreducible_of_connected_over_algClosed G.val
  let D (J : Atom) := (familyCentralizerIntersection G (J.val : Set L)).choose
  have hD (J : Atom) := (familyCentralizerIntersection G (J.val : Set L)).choose_spec
  choose Z j hj hj' using fun J : Atom ↦ closedTransporter G C (D J)
  let V (J : Atom) : Set G.val.X.left := Set.range (j J).left
  have hclosed (J : Atom) : IsClosed (V J) :=
    letI := hj J
    (j J).left.isClosedEmbedding.isClosed_range
  have cover : closedPoints G.val.X.left ⊆ ⋃ J, V J := by
    intro x hx
    let g := sectionOfClosedPoint G.val.X x hx
    obtain ⟨d, hd⟩ := point_kernel_of_iso s (pointConjugationIso g⁻¹)
    let J : Atom := ⟨(idealConjugation d).symm I,
      ((idealConjugation d).symm.isAtom_iff I).mpr hI⟩
    have hJI (y : L) (hy : y ∈ J.val) : d y ∈ I := hy
    obtain ⟨a, ha⟩ := centralizerTransport G s I J.val C (D J) hC (hD J) g d hd hJI
    obtain ⟨b, hb⟩ := (hj' J _ g).mp ((rationalTransporter G g).mpr ⟨a, ha⟩)
    apply Set.mem_iUnion.mpr
    refine ⟨J, b.left (IsLocalRing.closedPoint k), ?_⟩
    change (b ≫ j J).left (IsLocalRing.closedPoint k) = x
    rw [hb, sectionOfClosedPoint_apply]
  have hfull : (Set.univ : Set G.val.X.left) ⊆ ⋃ J, V J := by
    rw [← closure_closedPoints]
    exact (isClosed_iUnion_of_finite hclosed).closure_subset_iff.mpr cover
  let vs := Finset.univ.image V
  have eq : ⋃₀ (vs : Set (Set G.val.X.left)) = ⋃ J, V J := by
    ext x
    simp [vs, V]
  obtain ⟨W, hW, hsurj⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp (IrreducibleSpace.isIrreducible_univ (X := G.val.X.left))
      vs (by simp [vs, hclosed]) (eq ▸ hfull)
  obtain ⟨J, -, rfl⟩ := Finset.mem_image.mp hW
  letI := hj J
  letI : Surjective (j J).left := ⟨fun x ↦ hsurj (Set.mem_univ x)⟩
  letI : Smooth G.val.X.hom := characteristicZeroSmoothness k G
  letI : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  letI : IsIso (j J).left := isIso_of_isClosedImmersion_of_surjective _
  letI : IsIso ((Over.forget _).map (j J)) := inferInstanceAs (IsIso (j J).left)
  letI : IsIso (j J) := isIso_of_reflects_iso (j J) (Over.forget _)
  have transport (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
      ∃ a : C.group.X ⟶ (D J).group.X,
        a ≫ (D J).inclusion.hom.hom = C.inclusion.hom.hom ≫ (pointConjugation g).hom.hom :=
    (rationalTransporter G g).mp ((hj' J _ g).mpr ⟨g ≫ inv (j J), by simp⟩)
  have same : J.val = I := by
    by_contra hne
    obtain ⟨a, ha⟩ := transport 1
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_nonzero_bracket_in_atom (k := k) J.property
    have hconj (p : C.group.X ⟶ G.val.X) :
        p ≫ (pointConjugation (1 : 𝟙_ (SchemeOver k) ⟶ G.val.X)).hom.hom = p := by
      rw [pointConjugation_apply, MonObj.comp_one, one_mul, inv_one, mul_one]
    rw [hconj] at ha
    obtain ⟨z, hz⟩ := (hC _ y.toMul.val).mp fun t ht ↦
      commutesOver_of_lie_eq_zero s t y (brackets_of_distinct_atoms hI J.property (Ne.symm hne)
        t ht y hy)
    have hc := (hD J _ y.toMul.val).mpr ⟨z ≫ a, by rw [Category.assoc, ha, hz]⟩ x hx
    exact hxy (lie_eq_zero_of_commutesOver s x y hc)
  have adapt (T : SchemeOver k) (p : T ⟶ G.val.X) :
      (∃ a : T ⟶ (D J).group.X, a ≫ (D J).inclusion.hom.hom = p) →
      ∃ b : T ⟶ C.group.X, b ≫ C.inclusion.hom.hom = p := by
    intro h
    apply (hC T p).mp
    intro x hx
    exact (hD J T p).mpr h x (same.symm ▸ hx)
  exact normalOfRationalConjugation G C (fun g ↦ adapt _ _ (transport g))

/-- Taking the identity component preserves ambient normality and the
factorization of every tangent point through the subgroup. -/
private theorem connectedNormalTangent [CharZero k]
    (G : AffineAlgebraicGroup k) [GeometricallyConnected G.val.X.hom]
    (C : ClosedSubgroup G.val)
    (hC : IsNormalSubgroup C.inclusion) :
    ∃ (N : ClosedSubgroup G.val) (i : N.group ⟶ C.group),
      i ≫ C.inclusion = N.inclusion ∧ IsSmoothConnectedNormal N ∧
      ∀ (x : Lie k G.val),
        (∃ z : (testSpec k).obj (op (CommAlgCat.of k (DualNumber k))) ⟶ C.group.X,
          z ≫ C.inclusion.hom.hom = x.toMul.val) →
        ∃ z : (testSpec k).obj (op (CommAlgCat.of k (DualNumber k))) ⟶ N.group.X,
          z ≫ N.inclusion.hom.hom = x.toMul.val := by
  let A := closedSubgroupAlgebraicGroup C
  obtain ⟨Q, D, q, i, hi, _, _, _⟩ := identityComponentAndQuotient k A
  letI := hi.openImmersion
  let D' : ClosedSubgroup A.val := ⟨D, i, hi.closedImmersion⟩
  let N := subgroupOfSubgroup C D'
  letI := mono_over C.inclusion.hom.hom C.isClosedImmersion
  letI := hi.geometricallyConnected
  letI : ConnectedSpace D.X.left := GeometricallyConnected.connectedSpace_of_subsingleton D.X.hom
  letI : Smooth G.val.X.hom := characteristicZeroSmoothness k G
  letI : Smooth D.X.hom := characteristicZeroSmoothness k (closedSubgroupAlgebraicGroup D')
  have hn : IsNormalSubgroup N.inclusion := by
    let X := G.val.X ⊗ D.X
    letI : GeometricallyConnected X.hom := by
      change GeometricallyConnected (pullback.fst G.val.X.hom D.X.hom ≫ G.val.X.hom)
      exact GeometricallyConnected.comp _ _
    letI : ConnectedSpace X.left := GeometricallyConnected.connectedSpace_of_subsingleton X.hom
    obtain ⟨f, hf⟩ := normalSubgroup_conjugate_sections hC
      (fst G.val.X D.X) (snd G.val.X D.X ≫ i.hom.hom)
    let o : 𝟙_ (SchemeOver k) ⟶ X := lift 1 1
    have ho : o ≫ f = 1 := by
      apply (cancel_mono C.inclusion.hom.hom).mp
      rw [Category.assoc, hf, MonObj.one_comp C.inclusion.hom.hom]
      simp only [o, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd,
        MonObj.one_comp, one_mul, inv_one]
    obtain ⟨v, hv⟩ := liftThroughOpen i.hom.hom f (by
      rw [hi.identityComponent]
      apply (isConnected_range f.left.continuous).subset_connectedComponent
      let p := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))
      exact ⟨o.left p, congrArg (fun a : (𝟙_ (SchemeOver k)) ⟶ A.val.X ↦ a.left p) ho⟩)
    refine ⟨v, ?_⟩
    change v ≫ i.hom.hom ≫ C.inclusion.hom.hom = _
    rw [← Category.assoc, hv, hf]
    rfl
  refine ⟨N, i, rfl, ⟨characteristicZeroSmoothness k (closedSubgroupAlgebraicGroup N),
    inferInstanceAs (ConnectedSpace D.X.left), hn⟩, ?_⟩
  rintro x ⟨z, hz⟩
  have hred : (testSpec k).map (dualReduction k).op ≫ z =
      (1 : Points C.group.X (CommAlgCat.of k k)) := by
    apply (cancel_mono C.inclusion.hom.hom).mp
    rw [Category.assoc, hz, MonObj.one_comp]
    exact x.toMul.property
  have hrange : Set.range z.left ⊆ Set.range i.hom.hom.left := by
    rintro p ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := dualSpec_reduction_surjective (k := k) t
    rw [← Scheme.Hom.comp_apply]
    change ((testSpec k).map (dualReduction k).op ≫ z).left w ∈ _
    rw [hred]
    let o : Points D.X (CommAlgCat.of k k) := 1
    exact ⟨o.left w, by
      change (o ≫ i.hom.hom).left w = _
      rw [MonObj.one_comp]
      rfl⟩
  obtain ⟨y, hy⟩ := liftThroughOpen i.hom.hom z hrange
  refine ⟨y, ?_⟩
  change y ≫ i.hom.hom ≫ C.inclusion.hom.hom = x.toMul.val
  rw [← Category.assoc, hy, hz]

/-- A connected affine algebraic group with zero identity tangent is trivial.
The augmentation is idempotent, so the identity is an open and closed point. -/
private theorem trivial_of_subsingleton_lie [CharZero k] (G : AffineAlgebraicGroup k)
    [ConnectedSpace G.val.X.left] [Subsingleton (Lie k G.val)] :
    Nonempty (G.val ≅ Grp.trivial (SchemeOver k)) := by
  obtain ⟨A, ⟨i⟩⟩ := (essImage_hopfSpec (R := CommRingCat.of k)).mpr G.property.1
  let e : Spec (CommRingCat.of A.unop) ≅ G.val.X.left :=
    ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso i
  have he : e.hom ≫ G.val.X.hom = ((hopfSpec (CommRingCat.of k)).obj A).X.hom :=
    Over.w i.hom.hom.hom
  letI := G.property.2.1
  have hf : LocallyOfFiniteType (e.hom ≫ G.val.X.hom) := inferInstance
  rw [he] at hf
  letI : Algebra.FiniteType k A.unop := (hopfSpec_locallyOfFiniteType_iff k A.unop).mp hf
  letI : IsNoetherianRing A.unop := Algebra.FiniteType.isNoetherianRing k A.unop
  obtain ⟨d, _, _⟩ := liePresentation k A.unop G.val i
  let ε := (Bialgebra.counitAlgHom k A.unop).toRingHom
  let I := RingHom.ker ε
  have hd : Subsingleton I.Cotangent :=
    (Module.subsingleton_dual_iff k).mp (d.toEquiv.injective.subsingleton)
  obtain ⟨a, ha, hI⟩ := (I.isIdempotentElem_iff_of_fg (IsNoetherian.noetherian I)).mp
    (I.cotangent_subsingleton_iff.mp hd)
  have hsurj : Function.Surjective ε := fun t ↦
    ⟨algebraMap k A.unop t, (Bialgebra.counitAlgHom k A.unop).commutes t⟩
  letI : ConnectedSpace (PrimeSpectrum A.unop) :=
    e.hom.homeomorph.symm.surjective.connectedSpace e.hom.homeomorph.symm.continuous
  have hcl : IsClopen (PrimeSpectrum.zeroLocus ({a} : Set A.unop)) :=
    PrimeSpectrum.isClopen_iff_zeroLocus.mpr ⟨a, ha, rfl⟩
  have hr : Set.range (PrimeSpectrum.comap ε) = PrimeSpectrum.zeroLocus ({a} : Set A.unop) := by
    rw [range_comap_of_surjective _ _ hsurj,
      show RingHom.ker ε = I from rfl, hI, Ideal.submodule_span_eq,
      PrimeSpectrum.zeroLocus_span]
  have heq := hcl.eq_univ (hr ▸ Set.range_nonempty _)
  letI : Subsingleton (Spec (CommRingCat.of A.unop)) :=
    (Set.range_eq_univ.mp (hr.trans heq)).subsingleton
  letI : Subsingleton G.val.X.left := e.hom.homeomorph.symm.injective.subsingleton
  let S := identitySubgroup G
  letI := S.isClosedImmersion
  letI : Surjective S.inclusion.hom.hom.left :=
    ⟨fun x ↦ ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  letI : Smooth G.val.X.hom := characteristicZeroSmoothness k G
  letI : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  letI : IsIso S.inclusion.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  letI : IsIso S.inclusion := isIso_of_schemeIso _
  exact ⟨(asIso S.inclusion).symm⟩

private theorem simple_of_geometric_normal_subgroups [CharZero k] [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) [GeometricallyConnected G.val.X.hom]
    (s : IdentityLieStructure G.val)
    (hne : ¬ Nonempty (G.val ≅ Grp.trivial (SchemeOver k)))
    (hn : ∀ N : ClosedSubgroup G.val, IsSmoothConnectedNormal N →
      IsTrivialSubgroup N ∨ IsIso N.inclusion) :
    letI := s.lieRing
    letI := s.lieAlgebra
    LieAlgebra.radical k (Lie k G.val) = ⊥ → LieAlgebra.IsSimple k (Lie k G.val) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro hrad
  letI : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  let L := Lie k G.val
  obtain ⟨_, b, _⟩ := tangent_coordinates G s
  letI : FiniteDimensional k L := Module.Finite.of_basis b
  letI : LieAlgebra.HasTrivialRadical k L := ⟨hrad⟩
  letI : LieAlgebra.IsSemisimple k L := inferInstance
  letI := G.property.1
  have single (I : LieIdeal k L) (hI : IsAtom I) : I = ⊤ := by
    by_contra hproper
    have other : ∃ J : LieIdeal k L, IsAtom J ∧ J ≠ I := by
      by_contra! hall
      apply hproper
      have hs : sSup {J : LieIdeal k L | IsAtom J} ≤ I :=
        sSup_le fun J hJ ↦ le_of_eq (hall J hJ)
      rwa [LieAlgebra.IsSemisimple.sSup_atoms_eq_top, top_le_iff] at hs
    obtain ⟨J, hJ, hJI⟩ := other
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_nonzero_bracket_in_atom (k := k) hI
    obtain ⟨z, _, w, hw, hzw⟩ := exists_nonzero_bracket_in_atom (k := k) hJ
    obtain ⟨C, hC⟩ := familyCentralizerIntersection G (I : Set L)
    have hnormal := atomCentralizerNormal G s I hI C hC
    obtain ⟨N, i, hi, hN, htan⟩ := connectedNormalTangent G C hnormal
    have hwC := (hC _ w.toMul.val).mp fun t ht ↦
      commutesOver_of_lie_eq_zero s t w (brackets_of_distinct_atoms hI hJ (Ne.symm hJI) t ht w hw)
    rcases hn N hN with htriv | hiso
    · obtain ⟨e⟩ := htriv
      obtain ⟨a, ha⟩ := htan w hwC
      have ht : IsTerminal N.group.X :=
        (isTerminalTensorUnit (C := SchemeOver k)).ofIso
          (((Grp.forget (SchemeOver k)).mapIso e).symm)
      have h1 : w.toMul.val = 1 := by
        rw [← ha, ht.hom_ext a 1, MonObj.one_comp]
      have hc : CommutesOver z.toMul.val w.toMul.val := by
        rw [h1]
        unfold CommutesOver
        rw [MonObj.comp_one]
        exact Commute.one_right _
      exact hzw (lie_eq_zero_of_commutesOver s z w hc)
    · let j := inv N.inclusion ≫ i
      have hj : j ≫ C.inclusion = 𝟙 _ := by
        rw [Category.assoc, hi, IsIso.inv_hom_id]
      have hj' := congrArg (Grp.forget (SchemeOver k)).map hj
      change j.hom.hom ≫ C.inclusion.hom.hom = 𝟙 G.val.X at hj'
      have hyC := (hC _ y.toMul.val).mpr ⟨y.toMul.val ≫ j.hom.hom, by
        rw [Category.assoc, hj', Category.comp_id]⟩
      exact hxy (lie_eq_zero_of_commutesOver s x y (hyC x hx))
  constructor
  · intro I
    rcases eq_bot_or_exists_atom_le I with h | ⟨J, hJ, hle⟩
    · exact Or.inl h
    · exact Or.inr (top_le_iff.mp (single J hJ ▸ hle))
  · intro h
    letI := h
    letI : Subsingleton L := LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian k L
    exact hne (trivial_of_subsingleton_lie G)

private theorem simple_of_baseChange {K L M : Type u}
    [Field K] [Algebra k K] [LieRing L] [LieRing M] [LieAlgebra k L] [LieAlgebra K M]
    (e : K ⊗[k] L ≃ₗ⁅K⁆ M) (h : LieAlgebra.IsSimple K M) :
    LieAlgebra.IsSimple k L := by
  refine ⟨fun I ↦ ?_, fun hab ↦ h.non_abelian ?_⟩
  · have reflect (J : LieIdeal k L) (hj : I.baseChange K = J.baseChange K) : I = J := by
      apply LieSubmodule.toSubmodule_injective
      apply Submodule.baseChange_injective (A := K)
      exact congrArg LieSubmodule.toSubmodule hj
    rcases h.eq_bot_or_eq_top (LieIdeal.map e.toLieHom (I.baseChange K)) with hbot | htop
    · exact Or.inl (reflect ⊥ (by
        rw [LieSubmodule.baseChange_bot]
        exact LieIdeal.bot_of_map_eq_bot e.injective hbot))
    · apply Or.inr (reflect ⊤ ?_)
      rw [LieSubmodule.baseChange_top, eq_top_iff]
      intro x _
      have hx : e x ∈ LieIdeal.map e.toLieHom (I.baseChange K) := htop ▸ LieSubmodule.mem_top (e x)
      obtain ⟨y, hy⟩ := LieIdeal.mem_map_of_surjective e.surjective hx
      have eq : (y : K ⊗[k] L) = x := e.injective hy
      exact eq ▸ y.property
  · constructor
    intro x y
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    change ⁅e a, e b⁆ = 0
    rw [← e.map_lie, ← e.map_zero]
    apply congrArg e
    induction a using TensorProduct.inductionOn with
    | tmul r u =>
      induction b using TensorProduct.inductionOn with
      | tmul s v => rw [LieAlgebra.ExtendScalars.bracket_tmul, hab.trivial u v, TensorProduct.tmul_zero]
      | add p q hp hq => rw [lie_add, hp, hq, add_zero]
    | add p q hp hq => rw [add_lie, hp, hq, add_zero]

theorem absoluteSimpleLocalLie : Specs.AbsoluteSimpleLocalLie.{u} := by
  intro k _ _ G hG s
  letI := s.lieRing
  letI := s.lieAlgebra
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  letI := hG.1.2.1
  letI : GeometricallyConnected H.val.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.val.X.hom (fieldSpecMap k K)))
  obtain ⟨⟨t⟩, hb⟩ := identityLieBracketBaseChange k K G
  letI := t.lieRing
  letI := t.lieAlgebra
  obtain ⟨e, _⟩ := hb s t
  have hR := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  have hr := groupLieRadical_eq_bot H _ hR hG.1.2.2 t
  exact simple_of_baseChange e (simple_of_geometric_normal_subgroups H t hG.2.1 hG.2.2 hr)

end

end LinearAlgebraicGroups.Arithmetic
