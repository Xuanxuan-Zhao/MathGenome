import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Batteries.Tactic.OpenPrivate

/-!
# Semisimplicity of the Lie algebra

Over an algebraic closure, take the last nonzero derived ideal of the Lie
radical. Its infinitesimal points lie in the centre of their scheme centralizer.
They then factor through the identity component of that centre, which is a
smooth connected commutative normal subgroup of the original group.
Scalar extension of the derived series gives the result over the base field.

The centralizer argument is adapted from Milne, *Algebraic Groups, Lie Groups,
and their Arithmetic Subgroups*, Part II, Theorem 5.23.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Topology TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Representation.SemisimplyDifferentiated

open _root_.LinearAlgebraicGroups.Specs
open _root_.LinearAlgebraicGroups.Specs.GeometricRadicals (GeometricGroup IsTrivialSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsSolvable IsSubgroupOf)
open InfinitesimalCommutator

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1500000

private theorem derivedIdeal_map_of_equiv {k L M : Type u} [Field k] [LieRing L] [LieRing M]
    [LieAlgebra k L] [LieAlgebra k M] (e : L ≃ₗ⁅k⁆ M) (I : LieIdeal k L) (n : ℕ) :
    (LieAlgebra.derivedSeriesOfIdeal k L n I).map e.toLieHom =
      LieAlgebra.derivedSeriesOfIdeal k M n (I.map e.toLieHom) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [LieAlgebra.derivedSeriesOfIdeal_succ, LieAlgebra.derivedSeriesOfIdeal_succ,
      LieIdeal.map_bracket_eq e.toLieHom e.surjective, ih]

private theorem solvableIdeal_map_of_equiv {k L M : Type u} [Field k] [LieRing L] [LieRing M]
    [LieAlgebra k L] [LieAlgebra k M] (e : L ≃ₗ⁅k⁆ M) (I : LieIdeal k L)
    (hI : LieAlgebra.IsSolvable I) : LieAlgebra.IsSolvable (I.map e.toLieHom) := by
  obtain ⟨n, hn⟩ := (LieAlgebra.isSolvable_iff k I).mp hI
  apply LieAlgebra.IsSolvable.mk (R := k)
  rw [LieIdeal.derivedSeries_eq_bot_iff, ← derivedIdeal_map_of_equiv e,
    (LieIdeal.derivedSeries_eq_bot_iff I n).mp hn]
  simp

private theorem radical_map_of_equiv {k L : Type u} [Field k] [LieRing L]
    [LieAlgebra k L] [FiniteDimensional k L] (e : L ≃ₗ⁅k⁆ L) :
    (LieAlgebra.radical k L).map e.toLieHom = LieAlgebra.radical k L := by
  let I := LieAlgebra.radical k L
  have le (d : L ≃ₗ⁅k⁆ L) : I.map d.toLieHom ≤ I :=
    (LieAlgebra.LieIdeal.solvable_iff_le_radical k L _).mp
      (solvableIdeal_map_of_equiv d I inferInstance)
  refine le_antisymm (le e) ?_
  intro x hx
  have h : e.symm x ∈ I := le e.symm (LieIdeal.mem_map (f := e.symm.toLieHom) hx)
  simpa only [LieEquiv.coe_toLieHom, e.apply_symm_apply] using
    (LieIdeal.mem_map (f := e.toLieHom) h)

/-- The last nonzero term of the radical's derived series is characteristic and abelian. -/
private theorem exists_characteristic_abelian_ideal {k L : Type u} [Field k] [LieRing L]
    [LieAlgebra k L] [FiniteDimensional k L] (h : LieAlgebra.radical k L ≠ ⊥) :
    ∃ J : LieIdeal k L, J ≠ ⊥ ∧
      (∀ x ∈ J, ∀ y ∈ J, ⁅x, y⁆ = (0 : L)) ∧
      (∀ (e : L ≃ₗ⁅k⁆ L) (x : L), x ∈ J → e x ∈ J) := by
  classical
  let I := LieAlgebra.radical k L
  let D n := LieAlgebra.derivedSeriesOfIdeal k L n I
  obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable (R := k) (L := I)
  have hex : ∃ n, D n = ⊥ := ⟨n, (LieIdeal.derivedSeries_eq_bot_iff I n).mp hn⟩
  have hn₀ : Nat.find hex ≠ 0 := by
    intro he
    exact h (by simpa [D, he] using Nat.find_spec hex)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn₀
  have hnext : D (m + 1) = ⊥ := by
    change D m.succ = ⊥
    rw [← hm]
    exact Nat.find_spec hex
  refine ⟨D m, ?_, ?_, ?_⟩
  · intro hzero
    have hle := Nat.find_min' hex hzero
    rw [hm] at hle
    exact (Nat.not_succ_le_self m) hle
  · intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ D (m + 1) := by
      change ⁅x, y⁆ ∈ LieAlgebra.derivedSeriesOfIdeal k L (m + 1) I
      rw [LieAlgebra.derivedSeriesOfIdeal_succ]
      exact LieSubmodule.lie_mem_lie hx hy
    rw [hnext, LieSubmodule.mem_bot] at hxy
    exact hxy
  · intro e x hx
    have he : (D m).map e.toLieHom = D m := by
      change (LieAlgebra.derivedSeriesOfIdeal k L m I).map e.toLieHom =
        LieAlgebra.derivedSeriesOfIdeal k L m I
      rw [derivedIdeal_map_of_equiv e, radical_map_of_equiv e]
    rw [← he]
    exact LieIdeal.mem_map hx

variable {k : Type u} [Field k]

private abbrev DualSpec (k : Type u) [Field k] : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (DualNumber k)))

private def CommutesOver {G : GroupScheme k} {A T : SchemeOver k}
    (x : A ⟶ G.X) (y : T ⟶ G.X) : Prop :=
  Commute (fst A T ≫ x) (snd A T ≫ y)

private theorem commutesOver_iff {G : GroupScheme k} {A T : SchemeOver k}
    (x : A ⟶ G.X) (y : T ⟶ G.X) :
    CommutesOver x y ↔
      ∀ (U : SchemeOver k) (a : U ⟶ A) (t : U ⟶ T), Commute (a ≫ x) (t ≫ y) := by
  constructor
  · intro h U a t
    have he := congrArg (fun q : A ⊗ T ⟶ G.X ↦ lift a t ≫ q) h.eq
    show (a ≫ x) * (t ≫ y) = (t ≫ y) * (a ≫ x)
    simpa only [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd] using he
  · intro h
    exact h _ (fst A T) (snd A T)

open private closedSubgroupOfLocus familyFactorizationLocus centralizes_iff mono_over
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

/-- The closed subgroup commuting with a fixed affine family after every base change. -/
private theorem familyCentralizer (G : AffineAlgebraicGroup k) {A : SchemeOver k}
    [IsAffine A.left] (x : A ⟶ G.val.X) :
    ∃ H : ClosedSubgroup G.val, RepresentsSubgroup H (fun _ g ↦ CommutesOver x g) := by
  letI := G.property.1
  let a := fst A G.val.X ≫ x
  let b := snd A G.val.X
  let d := equalizer.ι (a * b) (b * a)
  obtain ⟨Y, j, hj, hy⟩ := familyFactorizationLocus d (inferInstanceAs (IsClosedImmersion d.left))
  let P (T : SchemeOver k) : Subgroup (T ⟶ G.val.X) :=
    { carrier := {g | CommutesOver x g}
      one_mem' := by simp [CommutesOver, MonObj.comp_one]
      mul_mem' := fun {g h} hg hh ↦ by
        change CommutesOver x (g * h)
        unfold CommutesOver at *
        rw [MonObj.comp_mul]
        exact hg.mul_right hh
      inv_mem' := fun {g} hg ↦ by
        change CommutesOver x g⁻¹
        unfold CommutesOver at *
        rw [GrpObj.comp_inv]
        exact hg.inv_right }
  apply closedSubgroupOfLocus P j hj
  intro T g
  change CommutesOver x g ↔ _
  rw [← hy]
  have hiff : CommutesOver x g ↔ (A ◁ g) ≫ (a * b) = (A ◁ g) ≫ (b * a) := by
    change (fst A T ≫ x) * (snd A T ≫ g) = (snd A T ≫ g) * (fst A T ≫ x) ↔ _
    simp [a, b, MonObj.comp_mul]
  rw [hiff]
  refine ⟨fun h ↦ ⟨equalizer.lift _ h, equalizer.lift_ι _ _⟩, ?_⟩
  rintro ⟨t, ht⟩
  rw [← ht, Category.assoc, Category.assoc, equalizer.condition]

private theorem dualSpecProduct :
    ∃ f : DualSpec k ⊗ DualSpec k ⟶ (testSpec k).obj
        (op (CommAlgCat.of k (TwoVariables k))),
      f ≫ (testSpec k).map (CommAlgCat.ofHom (liftS k)).op = fst _ _ ∧
      f ≫ (testSpec k).map (CommAlgCat.ofHom (liftT k)).op = snd _ _ := by
  let A := DualSpec k ⊗ DualSpec k
  haveI : IsAffine (DualSpec k).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (DualNumber k))))
  have hA : IsAffine A.left := by
    change IsAffine (pullback (DualSpec k).hom (DualSpec k).hom)
    infer_instance
  obtain ⟨R, ⟨i⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hA
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a := (F.preimage (i.hom ≫ fst (DualSpec k) (DualSpec k))).unop.hom
  let b := (F.preimage (i.hom ≫ snd (DualSpec k) (DualSpec k))).unop.hom
  obtain ⟨e, he⟩ := twoVariablesUniversalProperty k R.unop
  let z : {z : R.unop × R.unop // z.1 * z.1 = 0 ∧ z.2 * z.2 = 0} :=
    ⟨(a DualNumber.eps, b DualNumber.eps), by
      constructor <;> rw [← map_mul, DualNumber.eps_mul_eps, map_zero]⟩
  let w := e.symm z
  have hw := (he w).1
  rw [e.apply_symm_apply] at hw
  have ha : w.comp (liftS k) = a := DualNumber.algHom_ext (congrArg Prod.fst hw.symm)
  have hb : w.comp (liftT k) = b := DualNumber.algHom_ext (congrArg Prod.snd hw.symm)
  refine ⟨i.inv ≫ (testSpec k).map (CommAlgCat.ofHom w).op, ?_, ?_⟩
  · rw [Category.assoc, ← Functor.map_comp]
    change i.inv ≫ (testSpec k).map (CommAlgCat.ofHom (w.comp (liftS k))).op = _
    rw [ha]
    change i.inv ≫ (testSpec k).map (F.preimage (i.hom ≫ fst _ _)) = _
    rw [F.map_preimage, i.inv_hom_id_assoc]
  · rw [Category.assoc, ← Functor.map_comp]
    change i.inv ≫ (testSpec k).map (CommAlgCat.ofHom (w.comp (liftT k))).op = _
    rw [hb]
    change i.inv ≫ (testSpec k).map (F.preimage (i.hom ≫ snd _ _)) = _
    rw [F.map_preimage, i.inv_hom_id_assoc]

private theorem lieZeroPoint {G : GroupScheme k} (s : IdentityLieStructure G) :
    (@Zero.zero (Lie k G) s.lieRing.toAddGroup.toZero).toMul.val =
      (1 : Points G.X (CommAlgCat.of k (DualNumber k))) := by
  have h := @congrArg (AddGroup (PointKernel G)) (PointKernel G)
    s.lieRing.toAddGroup Additive.addGroup (fun a ↦ @Zero.zero _ a.toZero) s.group_law
  have h₁ : (@Zero.zero (PointKernel G) Additive.addGroup.toZero).toMul.val =
      (1 : Points G.X (CommAlgCat.of k (DualNumber k))) := rfl
  exact (congrArg (fun x : PointKernel G ↦ x.toMul.val) h).trans h₁

private theorem commutesOver_of_lie_eq_zero {G : GroupScheme k} (s : IdentityLieStructure G) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (x y : Lie k G), ⁅x, y⁆ = @Zero.zero _ s.lieRing.toAddGroup.toZero →
      CommutesOver x.toMul.val y.toMul.val := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro x y hxy
  let F := (groupPointsFunctor k).obj G
  have hc := s.commutator_law x y
  change (F.map (CommAlgCat.ofHom (liftST k))).hom ⁅x, y⁆.toMul.val =
    commutator F x y at hc
  rw [hxy, lieZeroPoint s, map_one] at hc
  let p : Points G.X (CommAlgCat.of k (TwoVariables k)) := (testSpec k).map (CommAlgCat.ofHom (liftS k)).op ≫ x.toMul.val
  let q : Points G.X (CommAlgCat.of k (TwoVariables k)) := (testSpec k).map (CommAlgCat.ofHom (liftT k)).op ≫ y.toMul.val
  have h : p * q * p⁻¹ * q⁻¹ = 1 := hc.symm
  have he : Commute p q := by
    show p * q = q * p
    have hh := congrArg (fun a ↦ a * q * p) h
    simpa [mul_assoc] using hh
  obtain ⟨a, ha, hb⟩ := dualSpecProduct (k := k)
  have hp := congrArg (fun p ↦ a ≫ p) he.eq
  change (fst _ _ ≫ x.toMul.val) * (snd _ _ ≫ y.toMul.val) =
    (snd _ _ ≫ y.toMul.val) * (fst _ _ ≫ x.toMul.val)
  simp only [p, q, MonObj.comp_mul, ← Category.assoc, ha, hb] at hp
  exact hp

private theorem factorsThroughClosed_iff {X Y Z : SchemeOver k} (i : Y ⟶ Z)
    [IsClosedImmersion i.left] (f : X ⟶ Z) :
    (∃ v : X ⟶ Y, v ≫ i = f) ↔ i.left.ker ≤ f.left.ker := by
  constructor
  · rintro ⟨v, rfl⟩
    exact v.left.le_ker_comp i.left
  · intro h
    let v := IsClosedImmersion.lift i.left f.left h
    have hv : v ≫ i.left = f.left := IsClosedImmersion.lift_fac i.left f.left h
    exact ⟨Over.homMk v (by rw [← Over.w i, ← Category.assoc, hv, Over.w f]),
      Over.OverMorphism.ext hv⟩

private theorem familyCentralizerIntersection (G : AffineAlgebraicGroup k)
    (S : Set (Lie k G.val)) :
    ∃ H : ClosedSubgroup G.val, RepresentsSubgroup H
      (fun _ g ↦ ∀ x ∈ S, CommutesOver x.toMul.val g) := by
  classical
  letI : IsAffine (DualSpec k).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (DualNumber k))))
  let c (x : S) := (familyCentralizer (A := DualSpec k) G x.val.toMul.val).choose
  have hc (x : S) := (familyCentralizer (A := DualSpec k) G x.val.toMul.val).choose_spec
  let I : G.val.X.left.IdealSheafData := ⨆ x : S, (c x).inclusion.hom.hom.left.ker
  let Y : SchemeOver k := Over.mk (I.subschemeι ≫ G.val.X.hom)
  let i : Y ⟶ G.val.X := Over.homMk I.subschemeι rfl
  letI : IsClosedImmersion i.left :=
    inferInstanceAs (IsClosedImmersion I.subschemeι)
  let P (T : SchemeOver k) := ⨅ x : S, SubgroupSections (c x) T
  have factor (T : SchemeOver k) (g : T ⟶ G.val.X) :
      g ∈ P T ↔ ∃ v : T ⟶ Y, v ≫ i = g := by
    change g ∈ (⨅ x : S, SubgroupSections (c x) T) ↔ _
    rw [Subgroup.mem_iInf, factorsThroughClosed_iff]
    change (∀ x : S, ∃ v : T ⟶ (c x).group.X, v ≫ (c x).inclusion.hom.hom = g) ↔
      I.subschemeι.ker ≤ g.left.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, iSup_le_iff]
    apply forall_congr'
    intro x
    letI := (c x).isClosedImmersion
    exact factorsThroughClosed_iff (c x).inclusion.hom.hom g
  obtain ⟨H, hH⟩ := closedSubgroupOfLocus P i inferInstance factor
  refine ⟨H, fun T g ↦ ?_⟩
  rw [← hH]
  change _ ↔ g ∈ (⨅ x : S, SubgroupSections (c x) T)
  rw [Subgroup.mem_iInf]
  exact ⟨fun h x ↦ (hc x T g).mp (h x x.property),
    fun h x hx ↦ (hc ⟨x, hx⟩ T g).mpr (h ⟨x, hx⟩)⟩

private def pointConjugation {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    G ⟶ G := by
  let f := lift (toUnit G.X ≫ g) (𝟙 G.X) ≫ GrpObj.conj G.X
  have hf {T : SchemeOver k} (t : T ⟶ G.X) :
      t ≫ f = (toUnit T ≫ g) * t * (toUnit T ≫ g)⁻¹ := by
    dsimp only [f]
    rw [← Category.assoc, comp_lift, GrpObj.lift_conj_eq_mul_mul_inv, Category.comp_id,
      comp_toUnit_assoc]
  refine Grp.homMk'' f ?_ ?_
  · rw [hf]
    change (toUnit (𝟙_ (SchemeOver k)) ≫ g) * (1 : 𝟙_ (SchemeOver k) ⟶ G.X) *
      (toUnit (𝟙_ (SchemeOver k)) ≫ g)⁻¹ = 1
    simp only [mul_one, mul_inv_cancel]
  · have hμ : μ[G.X] = fst G.X G.X * snd G.X G.X := by
      rw [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp]
    have hTensor : f ⊗ₘ f = lift (fst G.X G.X ≫ f) (snd G.X G.X ≫ f) := by
      rw [← lift_map, lift_fst_snd, Category.id_comp]
    nth_rw 1 [hμ]
    rw [hf, hTensor, ← CategoryTheory.Hom.mul_def, hf, hf]
    group

private theorem pointConjugation_apply {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    {T : SchemeOver k} (t : T ⟶ G.X) :
    t ≫ (pointConjugation g).hom.hom = (toUnit T ≫ g) * t * (toUnit T ≫ g)⁻¹ := by
  change t ≫ lift (toUnit G.X ≫ g) (𝟙 G.X) ≫ GrpObj.conj G.X = _
  rw [← Category.assoc, comp_lift, GrpObj.lift_conj_eq_mul_mul_inv, Category.comp_id,
    comp_toUnit_assoc]

private def pointConjugationIso {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    G ≅ G where
  hom := pointConjugation g
  inv := pointConjugation g⁻¹
  hom_inv_id := by
    apply Grp.hom_ext
    change (pointConjugation g).hom.hom ≫ (pointConjugation g⁻¹).hom.hom = 𝟙 G.X
    rw [pointConjugation_apply]
    have h := pointConjugation_apply g (𝟙 G.X)
    rw [Category.id_comp] at h
    rw [h, GrpObj.comp_inv]
    group
  inv_hom_id := by
    apply Grp.hom_ext
    change (pointConjugation g⁻¹).hom.hom ≫ (pointConjugation g).hom.hom = 𝟙 G.X
    rw [pointConjugation_apply]
    have h := pointConjugation_apply g⁻¹ (𝟙 G.X)
    rw [Category.id_comp] at h
    rw [h, GrpObj.comp_inv]
    group

open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private sectionOfClosedPoint sectionOfClosedPoint_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

/-- Conjugation preserves a closed subgroup in characteristic zero if it does so
for every rational conjugating element over the algebraically closed field. -/
private theorem normalOfRationalConjugation [IsAlgClosed k] [CharZero k]
    (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val)
    (h : ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
      ∃ v : H.group.X ⟶ H.group.X,
        v ≫ H.inclusion.hom.hom = H.inclusion.hom.hom ≫ (pointConjugation g).hom.hom) :
    IsNormalSubgroup H.inclusion := by
  let X := G.val.X ⊗ H.group.X
  letI : Smooth G.val.X.hom := characteristicZeroSmoothness k G
  letI : Smooth H.group.X.hom := characteristicZeroSmoothness k (closedSubgroupAlgebraicGroup H)
  haveI : Smooth X.hom := by
    change Smooth (pullback.fst G.val.X.hom H.group.X.hom ≫ G.val.X.hom)
    infer_instance
  haveI : IsReduced X.left := isReduced_of_smooth_over_field X.hom
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let i := H.inclusion.hom.hom
  let f := subgroupConjugation H.inclusion
  letI : IsClosedImmersion i.left := H.isClosedImmersion
  have hpoints : closedPoints X.left ⊆ f.left ⁻¹' Set.range i.left := by
    intro x hx
    let a := sectionOfClosedPoint X x hx
    let g := a ≫ fst G.val.X H.group.X
    let b := a ≫ snd G.val.X H.group.X
    obtain ⟨v, hv⟩ := h g
    have hterminal : toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) :=
      (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
    have he : (b ≫ v) ≫ i = a ≫ f := by
      rw [Category.assoc, hv, ← Category.assoc, pointConjugation_apply, hterminal, Category.id_comp]
      simp only [f, subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc, g, b]
    refine ⟨(b ≫ v).left (IsLocalRing.closedPoint k), ?_⟩
    rw [← Scheme.Hom.comp_apply]
    change ((b ≫ v) ≫ i).left (IsLocalRing.closedPoint k) = _
    rw [he]
    change f.left (a.left (IsLocalRing.closedPoint k)) = _
    rw [sectionOfClosedPoint_apply]
  have hclosed : IsClosed (f.left ⁻¹' Set.range i.left) :=
    i.left.isClosedEmbedding.isClosed_range.preimage f.left.continuous
  have hfull := hclosed.closure_subset_iff.mpr hpoints
  rw [closure_closedPoints] at hfull
  have hrange : Set.range f.left ⊆ i.left.ker.support := by
    rintro _ ⟨x, rfl⟩
    exact i.left.range_subset_ker_support (hfull (Set.mem_univ x))
  let J {Y : Scheme.{u}} (D : Closeds Y) := Scheme.IdealSheafData.vanishingIdeal D
  have hk : f.left.ker = J (Closeds.closure (Set.range f.left)) := by
    calc
      f.left.ker = (J (⊤ : Closeds X.left)).map f.left := by
        simp [J, Scheme.nilradical_eq_bot]
      _ = _ := by
        change (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X.left)).map f.left = _
        rw [Scheme.IdealSheafData.map_vanishingIdeal]
        simp only [Closeds.coe_top, Set.image_univ, J]
        rfl
  apply (factorsThroughClosed_iff i f).mpr
  rw [hk]
  exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
    (i.left.ker.support.isClosed.closure_subset_iff.mpr hrange)

private theorem point_kernel_of_iso {G : GroupScheme k} [IsAffine G.X.left]
    (s : IdentityLieStructure G) (e : G ≅ G) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ d : Lie k G ≃ₗ⁅k⁆ Lie k G, ∀ x, d x = mapPointKernel e.hom x := by
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨d, hd⟩ := identityDifferentialLieHom k G G e.hom s s
  let F := groupPointsFunctor k
  let R := CommAlgCat.of k (DualNumber k)
  have hsection (x : Lie k G) : d (mapPointKernel e.inv x) = x := by
    rw [hd]
    apply Subtype.ext
    change (F.map e.hom).app R ((F.map e.inv).app R x.toMul.val) = x.toMul.val
    have h := congrArg (fun f ↦ (F.map f).app R) e.inv_hom_id
    rw [F.map_comp, NatTrans.comp_app, F.map_id, NatTrans.id_app] at h
    exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom h) x.toMul.val
  have hretract (x : Lie k G) : mapPointKernel e.inv (d x) = x := by
    rw [hd]
    apply Subtype.ext
    change (F.map e.inv).app R ((F.map e.hom).app R x.toMul.val) = x.toMul.val
    have h := congrArg (fun f ↦ (F.map f).app R) e.hom_inv_id
    rw [F.map_comp, NatTrans.comp_app, F.map_id, NatTrans.id_app] at h
    exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom h) x.toMul.val
  exact ⟨LieEquiv.ofBijective d ⟨Function.LeftInverse.injective hretract,
    Function.RightInverse.surjective hsection⟩, hd⟩

private theorem conj_commute {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    {U : SchemeOver k} (x y : U ⟶ G.X) :
    Commute (x ≫ (pointConjugation g⁻¹).hom.hom) y →
      Commute x (y ≫ (pointConjugation g).hom.hom) := by
  intro h
  let e := pointConjugationIso g
  let f := IsMonHom.monoidHom e.hom.hom.hom U
  have hh := congrArg f h.eq
  rw [map_mul, map_mul] at hh
  change Commute x (f y)
  have hx : f (x ≫ (pointConjugation g⁻¹).hom.hom) = x := by
    have he := congrArg (Grp.forget (SchemeOver k)).map e.inv_hom_id
    change e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 G.X at he
    change (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x
    rw [Category.assoc, he, Category.comp_id]
  rw [hx] at hh
  exact hh

private theorem characteristicCentralizerNormal [IsAlgClosed k] [CharZero k]
    (G : AffineAlgebraicGroup k) (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (J : LieIdeal k (Lie k G.val)),
      (∀ (e : Lie k G.val ≃ₗ⁅k⁆ Lie k G.val) (x : Lie k G.val), x ∈ J → e x ∈ J) →
      ∀ (H : ClosedSubgroup G.val), RepresentsSubgroup H
        (fun _ g ↦ ∀ x ∈ J, CommutesOver x.toMul.val g) →
      IsNormalSubgroup H.inclusion := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro J hJ H hH
  letI := G.property.1
  apply normalOfRationalConjugation G H
  intro g
  refine (hH _ _).mp ?_
  intro x hx
  obtain ⟨d, hd⟩ := point_kernel_of_iso s (pointConjugationIso g⁻¹)
  have fix := (hH _ H.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩ (d x) (hJ d x hx)
  apply (commutesOver_iff _ _).mpr
  intro U a t
  have hf := (commutesOver_iff _ _).mp fix U a t
  rw [hd] at hf
  change Commute (a ≫ x.toMul.val ≫ (pointConjugation g⁻¹).hom.hom)
    (t ≫ H.inclusion.hom.hom) at hf
  rw [← Category.assoc t H.inclusion.hom.hom]
  exact conj_commute g _ _ (by simpa only [Category.assoc] using hf)

/-- The scheme centre of a normal subgroup is normal in the ambient group. -/
private theorem centreInAmbientNormal [IsAlgClosed k] [CharZero k]
    (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val)
    (hH : IsNormalSubgroup H.inclusion)
    (Z : ClosedSubgroup H.group)
    (hZ : RepresentsSubgroup Z (fun _ z ↦ Centralizes (𝟙 H.group) z)) :
    IsNormalSubgroup (Z.inclusion ≫ H.inclusion) := by
  let C := Specs.GeometricBorelConjugacy.subgroupOfSubgroup H Z
  letI := mono_over H.inclusion.hom.hom H.isClosedImmersion
  change IsNormalSubgroup C.inclusion
  apply normalOfRationalConjugation G C
  intro g
  obtain ⟨f, hf⟩ := normalSubgroup_conjugate_sections hH (toUnit H.group.X ≫ g) (𝟙 H.group.X)
  obtain ⟨b, hb⟩ :=
    normalSubgroup_conjugate_sections hH (toUnit H.group.X ≫ g⁻¹) (𝟙 H.group.X)
  have heq : f ≫ H.inclusion.hom.hom =
      H.inclusion.hom.hom ≫ (pointConjugation g).hom.hom := by
    simpa only [pointConjugation_apply, Category.id_comp] using hf
  have heq' : b ≫ H.inclusion.hom.hom =
      H.inclusion.hom.hom ≫ (pointConjugation g⁻¹).hom.hom := by
    simpa only [pointConjugation_apply, Category.id_comp] using hb
  have hId : (𝟙 H.group : H.group ⟶ H.group).hom.hom = 𝟙 H.group.X := rfl
  have ht : Centralizes (𝟙 H.group) (Z.inclusion.hom.hom ≫ f) := by
    apply (centralizes_iff _ _).mpr
    intro U t v
    have hz := (hZ _ Z.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
    have hc := (centralizes_iff _ _).mp hz U t (v ≫ b)
    change Commute (t ≫ Z.inclusion.hom.hom) (v ≫ b) at hc
    have h := congrArg (IsMonHom.monoidHom H.inclusion.hom.hom U) hc.symm.eq
    rw [map_mul, map_mul] at h
    have h' : Commute ((v ≫ H.inclusion.hom.hom) ≫ (pointConjugation g⁻¹).hom.hom)
        ((t ≫ Z.inclusion.hom.hom) ≫ H.inclusion.hom.hom) := by
      show _ * _ = _ * _
      simpa only [IsMonHom.monoidHom_apply, Category.assoc, heq'] using h
    have h'' := (conj_commute g _ _ h').symm.eq
    apply (show Function.Injective (IsMonHom.monoidHom H.inclusion.hom.hom U) from
      fun _ _ h ↦ (cancel_mono H.inclusion.hom.hom).mp h)
    simpa only [map_mul, IsMonHom.monoidHom_apply, Category.assoc, heq, heq', hId, Category.id_comp] using h''
  obtain ⟨z, hz⟩ := (hZ _ _).mp ht
  refine ⟨z, ?_⟩
  change z ≫ Z.inclusion.hom.hom ≫ H.inclusion.hom.hom =
    Z.inclusion.hom.hom ≫ H.inclusion.hom.hom ≫ (pointConjugation g).hom.hom
  rw [← Category.assoc z, hz, Category.assoc, heq]

private theorem liftThroughOpen {X Y B : SchemeOver k} (i : X ⟶ Y)
    [IsOpenImmersion i.left] (f : B ⟶ Y)
    (hf : Set.range f.left ⊆ Set.range i.left) :
    ∃ g : B ⟶ X, g ≫ i = f := by
  let a := IsOpenImmersion.lift i.left f.left hf
  have ha : a ≫ i.left = f.left := IsOpenImmersion.lift_fac _ _ _
  exact ⟨Over.homMk a (by rw [← Over.w i, ← Category.assoc, ha, Over.w f]),
    Over.OverMorphism.ext ha⟩

private theorem dualSpec_reduction_surjective :
    Function.Surjective ((testSpec k).map (dualReduction k).op).left := by
  change Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom k k k).toRingHom)
  let f := (TrivSqZeroExt.fstHom k k k).toRingHom
  have hf : Function.Surjective f := fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩
  change Function.Surjective (PrimeSpectrum.comap f)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _ hf,
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  intro x hx
  change x ∈ nilradical (TrivSqZeroExt k k)
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  have h : x.fst = 0 := hx
  rw [pow_two]
  apply TrivSqZeroExt.ext <;> simp [h]

open private solvable_iff_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

/-- Every infinitesimal point of a normal commutative closed subgroup factors
through the connected solvable radical. -/
private theorem commutativeNormalTangent [IsAlgClosed k] [CharZero k]
    (G : AffineAlgebraicGroup k)
    (R C : ClosedSubgroup G.val) (hR : Specs.GeometricRadicals.IsSolvableRadical G R)
    (hRtriv : IsTrivialSubgroup R) (hC : IsNormalSubgroup C.inclusion)
    (hc : ∀ (Y : SchemeOver k) (a b : Y ⟶ C.group.X), Commute a b)
    (x : DualSpec k ⟶ C.group.X)
    (hx : (testSpec k).map (dualReduction k).op ≫ x =
      (1 : Points C.group.X (CommAlgCat.of k k))) :
    x ≫ C.inclusion.hom.hom = 1 := by
  let A := closedSubgroupAlgebraicGroup C
  obtain ⟨Q, D, q, i, hi, _, _, _⟩ := identityComponentAndQuotient k A
  letI := hi.openImmersion
  let D' : ClosedSubgroup A.val := ⟨D, i, hi.closedImmersion⟩
  have hsD := characteristicZeroSmoothness k (closedSubgroupAlgebraicGroup D')
  have hcD : ConnectedSpace D.X.left :=
    letI := hi.geometricallyConnected
    GeometricallyConnected.connectedSpace_of_subsingleton D.X.hom
  let N := Specs.GeometricBorelConjugacy.subgroupOfSubgroup C D'
  letI := mono_over C.inclusion.hom.hom C.isClosedImmersion
  have hn : IsNormalSubgroup N.inclusion := by
    apply normalOfRationalConjugation G N
    intro g
    obtain ⟨f, hf⟩ := normalSubgroup_conjugate_sections hC (toUnit D.X ≫ g) i.hom.hom
    have he : (1 : 𝟙_ (SchemeOver k) ⟶ D.X) ≫ f = 1 := by
      apply (cancel_mono C.inclusion.hom.hom).mp
      rw [Category.assoc, hf, MonObj.one_comp C.inclusion.hom.hom]
      simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
        MonObj.one_comp i.hom.hom, MonObj.one_comp C.inclusion.hom.hom, mul_one, mul_inv_cancel]
    obtain ⟨v, hv⟩ := liftThroughOpen i.hom.hom f (by
      rw [hi.identityComponent]
      apply (isConnected_range f.left.continuous).subset_connectedComponent
      let p := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))
      exact ⟨(1 : 𝟙_ (SchemeOver k) ⟶ D.X).left p,
        congrArg (fun a : (𝟙_ (SchemeOver k)) ⟶ A.val.X ↦ a.left p) he⟩)
    refine ⟨v, ?_⟩
    change v ≫ i.hom.hom ≫ C.inclusion.hom.hom =
      (i.hom.hom ≫ C.inclusion.hom.hom) ≫ (pointConjugation g).hom.hom
    rw [← Category.assoc, hv, hf, pointConjugation_apply]
  have hiMon := mono_over i.hom.hom hi.closedImmersion
  have hs : IsSolvable N.group := by
    apply (solvable_iff_sections (closedSubgroupAlgebraicGroup N) hsD hcD).mpr
    apply Group.isSolvable_of_comm
    intro a b
    apply (cancel_mono i.hom.hom).mp
    exact ((IsMonHom.monoidHom i.hom.hom _).map_mul a b).trans
      ((hc _ (a ≫ i.hom.hom) (b ≫ i.hom.hom)).eq.trans
        ((IsMonHom.monoidHom i.hom.hom _).map_mul b a).symm)
  obtain ⟨j, hj⟩ := hR.2.2 N ⟨hsD, hcD, hn⟩ hs
  obtain ⟨r⟩ := hRtriv
  have hterminal : IsTerminal R.group.X :=
    (isTerminalTensorUnit (C := SchemeOver k)).ofIso
      (((Grp.forget (SchemeOver k)).mapIso r).symm)
  have hrange : Set.range x.left ⊆ Set.range i.hom.hom.left := by
    rintro p ⟨t, rfl⟩
    obtain ⟨z, rfl⟩ := dualSpec_reduction_surjective (k := k) t
    rw [← Scheme.Hom.comp_apply]
    change ((testSpec k).map (dualReduction k).op ≫ x).left z ∈ _
    rw [hx]
    let o : Points D.X (CommAlgCat.of k k) := 1
    exact ⟨o.left z, by
      change (o ≫ i.hom.hom).left z = _
      rw [MonObj.one_comp]
      rfl⟩
  obtain ⟨y, hy⟩ := liftThroughOpen i.hom.hom x hrange
  have hi' := congrArg (Grp.forget (SchemeOver k)).map hj
  change j.hom.hom ≫ R.inclusion.hom.hom = i.hom.hom ≫ C.inclusion.hom.hom at hi'
  rw [← hy, Category.assoc, ← hi', ← Category.assoc, hterminal.hom_ext (y ≫ j.hom.hom) 1,
    MonObj.one_comp]

open private tangent_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.AdjointRepresentation

/-- The centralizer of a characteristic abelian ideal has a normal centre that
contains every tangent point of the ideal. -/
private theorem groupLieRadical_eq_bot [IsAlgClosed k] [CharZero k]
    (G : AffineAlgebraicGroup k)
    (R : ClosedSubgroup G.val) (hR : Specs.GeometricRadicals.IsSolvableRadical G R)
    (hRtriv : IsTrivialSubgroup R) (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    LieAlgebra.radical k (Lie k G.val) = ⊥ := by
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨_, v, _⟩ := tangent_coordinates G s
  letI : FiniteDimensional k (Lie k G.val) := Module.Finite.of_basis v
  by_contra h
  obtain ⟨J, hn, hab, hchar⟩ := exists_characteristic_abelian_ideal h
  obtain ⟨H, hH⟩ := familyCentralizerIntersection G (J : Set (Lie k G.val))
  have hnH := characteristicCentralizerNormal G s J hchar H hH
  let A := closedSubgroupAlgebraicGroup H
  let top : ClosedSubgroup H.group :=
    ⟨H.group, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 H.group.X.left))⟩
  obtain ⟨Z, hZ⟩ := centralizerScheme k A top
  change RepresentsSubgroup Z (fun _ z ↦ Centralizes (𝟙 H.group) z) at hZ
  have hId : (𝟙 H.group : H.group ⟶ H.group).hom.hom = 𝟙 H.group.X := rfl
  let C := Specs.GeometricBorelConjugacy.subgroupOfSubgroup H Z
  have hnC : IsNormalSubgroup C.inclusion := centreInAmbientNormal G H hnH Z hZ
  have hc (Y : SchemeOver k) (a b : Y ⟶ C.group.X) : Commute a b := by
    letI := mono_over Z.inclusion.hom.hom Z.isClosedImmersion
    let f := IsMonHom.monoidHom Z.inclusion.hom.hom Y
    apply (show Function.Injective f from fun _ _ h ↦ (cancel_mono Z.inclusion.hom.hom).mp h)
    rw [map_mul, map_mul]
    have hspec := (hZ _ Z.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
    simpa only [f, IsMonHom.monoidHom_apply, hId, Category.comp_id] using
      ((centralizes_iff _ _).mp hspec Y a (b ≫ Z.inclusion.hom.hom)).eq
  apply hn
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, hy⟩ := (hH _ x.toMul.val).mp fun a ha ↦
    commutesOver_of_lie_eq_zero s a x (hab a ha x hx)
  have hyZ : Centralizes (𝟙 H.group) y := by
    apply (centralizes_iff _ _).mpr
    intro U v w
    letI := mono_over H.inclusion.hom.hom H.isClosedImmersion
    let f := IsMonHom.monoidHom H.inclusion.hom.hom U
    apply (show Function.Injective f from fun _ _ h ↦ (cancel_mono H.inclusion.hom.hom).mp h)
    rw [map_mul, map_mul]
    have hspec := (hH _ H.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩ x hx
    simpa only [f, IsMonHom.monoidHom_apply, Category.assoc, hy, hId, Category.comp_id]
      using ((commutesOver_iff _ _).mp hspec U v w).eq
  obtain ⟨z, hz⟩ := (hZ _ y).mp hyZ
  have hzx : z ≫ C.inclusion.hom.hom = x.toMul.val := by
    change z ≫ Z.inclusion.hom.hom ≫ H.inclusion.hom.hom = x.toMul.val
    rw [← Category.assoc, hz, hy]
  letI := mono_over C.inclusion.hom.hom C.isClosedImmersion
  have hred : (testSpec k).map (dualReduction k).op ≫ z =
      (1 : Points C.group.X (CommAlgCat.of k k)) := by
    apply (cancel_mono C.inclusion.hom.hom).mp
    rw [Category.assoc, hzx, MonObj.one_comp]
    exact x.toMul.property
  have he := commutativeNormalTangent G R C hR hRtriv hnC hc z hred
  rw [hzx, ← lieZeroPoint s] at he
  rw [LieSubmodule.mem_bot]
  exact Subtype.ext he

private theorem radical_eq_bot_of_scalar_extension {K L M : Type u}
    [Field K] [Algebra k K] [LieRing L] [LieRing M] [LieAlgebra k L] [LieAlgebra K M]
    [FiniteDimensional k L] (e : K ⊗[k] L ≃ₗ⁅K⁆ M) (hK : LieAlgebra.radical K M = ⊥) :
    LieAlgebra.radical k L = ⊥ := by
  let I := LieAlgebra.radical k L
  obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable (R := k) (L := I)
  have hI : LieAlgebra.IsSolvable (I.baseChange K) := by
    apply LieAlgebra.IsSolvable.mk (R := K) (k := n)
    rw [LieIdeal.derivedSeries_eq_bot_iff, LieAlgebra.derivedSeriesOfIdeal_baseChange,
      (LieIdeal.derivedSeries_eq_bot_iff I n).mp hn, LieSubmodule.baseChange_bot]
  have hmap := solvableIdeal_map_of_equiv e (I.baseChange K) hI
  have hbot : LieIdeal.map e.toLieHom (I.baseChange K) = ⊥ := by
    have h' : LieIdeal.map e.toLieHom (I.baseChange K) ≤ LieAlgebra.radical K M := le_sSup hmap
    exact eq_bot_iff.mpr (hK ▸ h')
  have hzero := LieIdeal.bot_of_map_eq_bot e.injective hbot
  change I = ⊥
  rw [eq_bot_iff]
  intro x hx
  have hmem : 1 ⊗ₜ[k] x ∈ I.baseChange K := Submodule.tmul_mem_baseChange_of_mem 1 hx
  rw [hzero, LieSubmodule.mem_bot, Module.FaithfullyFlat.one_tmul_eq_zero_iff] at hmem
  simpa only [LieSubmodule.mem_bot] using hmem

/-- The identity tangent of a connected semisimple affine algebraic group
in characteristic zero is finite dimensional and has zero solvable radical. -/
theorem lieSemisimple : Specs.SemisimplyDifferentiated.LieSemisimple.{u} := by
  intro k _ _ G hG s
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨_, b, _⟩ := tangent_coordinates G s
  letI : FiniteDimensional k (Lie k G.val) := Module.Finite.of_basis b
  refine ⟨inferInstance, ?_⟩
  let K := AlgebraicClosure k
  let GK := GeometricGroup G
  obtain ⟨⟨sK⟩, hbase⟩ := identityLieBracketBaseChange k K G
  letI := sK.lieRing
  letI := sK.lieAlgebra
  obtain ⟨e, _⟩ := hbase s sK
  have hK := groupLieRadical_eq_bot GK _
    (GeometricRadicals.geometricSolvableRadicalLargest G) hG.2.2 sK
  exact radical_eq_bot_of_scalar_extension e hK

end

end LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
