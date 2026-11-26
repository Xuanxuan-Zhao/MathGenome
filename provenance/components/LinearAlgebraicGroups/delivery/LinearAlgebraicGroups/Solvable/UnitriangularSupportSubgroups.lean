import Specs.LinearAlgebraicGroups.Solvable.UnitriangularSupportSubgroups
import LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.Algebra.Group.TransferInstance

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.UnitriangularSupportSubgroups

open Specs.UnitriangularSupportSubgroups
open Specs.StandardGroups Specs.Unipotent

noncomputable section

section Matrices

variable {J R : Type*} [Fintype J] [LinearOrder J] [DecidableEq J] [CommRing R]
variable {q : J → J → Prop} {a b : Matrix J J R}

omit [Fintype J] [DecidableEq J] in
private theorem support_add (ha : HasSupport q a) (hb : HasSupport q b) :
    HasSupport q (a + b) := by
  intro i j h
  rw [Matrix.add_apply, ha i j h, hb i j h, add_zero]

omit [DecidableEq J] in
private theorem support_mul (hq : ∀ i j l, q i j → q j l → q i l)
    (ha : HasSupport q a) (hb : HasSupport q b) : HasSupport q (a * b) := by
  intro i j h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hil : i < l ∧ q i l
  · have hlj : ¬ (l < j ∧ q l j) :=
      fun hl ↦ h ⟨hil.1.trans hl.1, hq i l j hil.2 hl.2⟩
    rw [hb l j hlj, mul_zero]
  · rw [ha i l hil, zero_mul]

omit [LinearOrder J] in
private theorem mul_sub_one (g h : Matrix.GeneralLinearGroup J R) :
    (g * h).val - 1 = (g.val - 1) + (h.val - 1) + (g.val - 1) * (h.val - 1) := by
  change g.val * h.val - 1 = _
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  abel

-- In a forbidden position of the inverse, every contributing off-diagonal
-- term from the original matrix involves a later row of the inverse.
private theorem inverse_support (hq : ∀ i j l, q i j → q j l → q i l)
    (g : Matrix.GeneralLinearGroup J R) (hg : HasSupport q (g.val - 1)) :
    HasSupport q (g⁻¹.val - 1) := by
  let x : Matrix J J R := g.val - 1
  let y : Matrix J J R := g⁻¹.val - 1
  have hxy : x + y + x * y = 0 := by
    change (g.val - 1) + (g⁻¹.val - 1) + (g.val - 1) * (g⁻¹.val - 1) = 0
    rw [← mul_sub_one, mul_inv_cancel]
    exact sub_self _
  intro i
  induction i using (wellFounded_gt : WellFounded ((· > ·) : J → J → Prop)).induction with
  | h i ih =>
    intro j hij
    have hm : (x * y) i j = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : i < l ∧ q i l
      · have hlj : ¬ (l < j ∧ q l j) :=
          fun hl ↦ hij ⟨hil.1.trans hl.1, hq i l j hil.2 hl.2⟩
        rw [show y l j = 0 from ih l hil.1 j hlj, mul_zero]
      · rw [show x i l = 0 from hg i l hil, zero_mul]
    have he := congrArg (fun m : Matrix J J R ↦ m i j) hxy
    change x i j + y i j + (x * y) i j = 0 at he
    change y i j = 0
    rwa [show x i j = 0 from hg i j hij, hm, zero_add, add_zero] at he

private def supportSubgroup (q : J → J → Prop) (hq : ∀ i j l, q i j → q j l → q i l) :
    Subgroup (Matrix.GeneralLinearGroup J R) where
  carrier := {g | HasSupport q (g.val - 1)}
  one_mem' := by
    change HasSupport q ((1 : Matrix J J R) - 1)
    rw [sub_self]
    exact fun _ _ _ ↦ rfl
  mul_mem' {g h} hg hh := by
    change HasSupport q ((g * h).val - 1)
    rw [mul_sub_one]
    exact support_add (support_add hg hh) (support_mul hq hg hh)
  inv_mem' {g} hg := inverse_support hq g hg

end Matrices

variable {k : Type u} [Field k]

/-- A closed subscheme whose points are subgroups inherits a group scheme
structure, with the original closed immersion as its inclusion. -/
private theorem closedSubgroupOfPoints {G : GroupScheme k} {X : SchemeOver k}
    (hX : IsAffine X.left) (j : X ⟶ G.X) (hj : IsClosedImmersion j.left)
    (S : ∀ R : TestAlgebra k, Subgroup (Points G.X R))
    (hS : ∀ (R : TestAlgebra k) (x : Points G.X R),
      x ∈ S R ↔ ∃ y : Points X R, y ≫ j = x) :
    ∃ H : Specs.ClosedSubgroup G, ∀ (R : TestAlgebra k) (x : Points G.X R),
      x ∈ S R ↔ ∃ y : Points H.group.X R, y ≫ H.inclusion.hom.hom = x := by
  have : IsClosedImmersion j.left := hj
  have : Mono j := by
    apply (Over.forget _).mono_of_mono_map
    exact inferInstanceAs (Mono j.left)
  let e (R : TestAlgebra k) : Points X R ≃ S R :=
    Equiv.ofBijective (fun y ↦ ⟨y ≫ j, (hS R _).mpr ⟨y, rfl⟩⟩)
      ⟨fun _ _ h ↦ (cancel_mono j).mp (congrArg Subtype.val h), by
        intro x
        obtain ⟨y, hy⟩ := (hS R x.val).mp x.property
        exact ⟨y, Subtype.ext hy⟩⟩
  have he (R : TestAlgebra k) (y : Points X R) : (e R y).val = y ≫ j := rfl
  have he_one (R : TestAlgebra k) : (e R).group.one ≫ j = 1 := by
    change (e R).symm 1 ≫ j = 1
    rw [← he, Equiv.apply_symm_apply]
    rfl
  have he_mul (R : TestAlgebra k) (x y : Points X R) :
      (e R).group.mul x y ≫ j = (x ≫ j) * (y ≫ j) := by
    change (e R).symm (e R x * e R y) ≫ j = _
    rw [← he, Equiv.apply_symm_apply]
    rfl
  let L : NaturalGroupLaw X :=
    { group := fun R ↦ (e R).group
      map_one := by
        intro R T f
        apply (cancel_mono j).mp
        rw [show mapPoints f ((e R).group.one) ≫ j =
          mapPoints f (((e R).group.one) ≫ j) from Category.assoc .., he_one, he_one]
        exact MonObj.comp_one _
      map_mul := by
        intro R T f x y
        apply (cancel_mono j).mp
        simp only [mapPoints, Category.assoc, he_mul, MonObj.comp_mul] }
  obtain ⟨s, hs⟩ := (groupLawComparison k X hX).2 L
  let H : GroupScheme k := { X := X, grp := s }
  have hgroup (R : TestAlgebra k) :
      (inducedGroupLaw X s).group R = (e R).group :=
    congrArg (fun law : NaturalGroupLaw X ↦ law.group R) hs
  let α : (groupPointsFunctor k).obj H ⟶ (groupPointsFunctor k).obj G :=
    { app R := GrpCat.ofHom
        { toFun := (· ≫ j)
          map_one' := by
            change ((inducedGroupLaw X s).group R).one ≫ j = _
            rw [hgroup, he_one]
          map_mul' := by
            intro x y
            change ((inducedGroupLaw X s).group R).mul x y ≫ j = _
            rw [hgroup, he_mul] }
      naturality := by
        intro R T f
        apply GrpCat.ext
        intro x
        change ((testSpec k).map f.op ≫ x) ≫ j = (testSpec k).map f.op ≫ (x ≫ j)
        exact Category.assoc .. }
  obtain ⟨i, hi⟩ := (groupHomComparison k H G hX).2 α
  have hij : i.hom.hom = j := by
    obtain ⟨A, ⟨d⟩⟩ := essImage_algSpec.mpr hX
    apply (cancel_epi d.hom).mp
    exact DFunLike.congr_fun (congrArg (fun τ ↦ (τ.app A.unop).hom) hi) d.hom
  exact ⟨⟨H, i, hij.symm ▸ hj⟩, by simpa only [hij] using hS⟩

/-- The quotient by the forbidden entries of the universal matrix represents
the subgroup with the prescribed strict upper support. -/
theorem closedSubgroupOfSupport : Specs.UnitriangularSupportSubgroups.ClosedSubgroupOfSupport.{u} := by
  intro k _ U n E _ _ q hq
  let G := U.val
  obtain ⟨A, ⟨d⟩⟩ := essImage_algSpec.mpr U.property.1
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let M (R : TestAlgebra k) (x : Points G.X R) : Matrix (Index.{u} n) (Index.{u} n) R :=
    (E.app R x).val - 1
  have hM {R T : TestAlgebra k} (f : R ⟶ T) (x : Points G.X R) (i j : Index.{u} n) :
      M T (mapPoints f x) i j = f.hom (M R x i j) := by
    have hn := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (E.naturality f)) x
    have hentry := congrArg (fun g : Matrix.GeneralLinearGroup (Index.{u} n) T ↦ g.val i j) hn
    change (E.app T (mapPoints f x)).val i j = f.hom ((E.app R x).val i j) at hentry
    change (E.app T (mapPoints f x)).val i j - (1 : Matrix _ _ T) i j =
      f.hom ((E.app R x).val i j - (1 : Matrix _ _ R) i j)
    rw [hentry, map_sub]
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.one_apply_ne hij]
  let B := A.unop
  let I : Ideal B := Ideal.span
    {z | ∃ i j, ¬ (i < j ∧ q i j) ∧ M B d.hom i j = z}
  let Q : TestAlgebra k := CommAlgCat.of k (B ⧸ I)
  let p : B ⟶ Q := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)
  let X := (testSpec k).obj (op Q)
  let inclusion : X ⟶ G.X := (testSpec k).map p.op ≫ d.hom
  have hX : IsAffine X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (B ⧸ I))))
  have hclosed : IsClosedImmersion inclusion.left := by
    have : IsIso d.hom.left := (Over.forget _).map_isIso d.hom
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom p.hom.toRingHom) ≫ d.hom.left)
    exact MorphismProperty.RespectsIso.postcomp @IsClosedImmersion d.hom.left _
      (IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective)
  let ρ (R : TestAlgebra k) : Points G.X R →* Matrix.GeneralLinearGroup (Index.{u} n) R := by
    exact (E.app R).hom
  let S (R : TestAlgebra k) : Subgroup (Points G.X R) :=
    (supportSubgroup (R := R) q hq).comap (ρ R)
  have hS (R : TestAlgebra k) (x : Points G.X R) :
      x ∈ S R ↔ ∃ y : Points X R, y ≫ inclusion = x := by
    let f : B ⟶ R := (F.preimage (x ≫ d.inv)).unop
    have hf : (testSpec k).map f.op ≫ d.hom = x := by simp [f, F]
    have hvanish : x ∈ S R ↔ I ≤ RingHom.ker f.hom.toRingHom := by
      change HasSupport q (M R x) ↔ _
      rw [Ideal.span_le]
      constructor
      · rintro h _ ⟨i, j, hij, rfl⟩
        exact (hM f d.hom i j).symm.trans (by simpa only [mapPoints, hf] using h i j hij)
      · intro h i j hij
        have hz : f.hom (M B d.hom i j) = 0 := h ⟨i, j, hij, rfl⟩
        simpa only [mapPoints, hf] using (hM f d.hom i j).trans hz
    rw [hvanish]
    constructor
    · intro h
      let l : Q ⟶ R := CommAlgCat.ofHom (Ideal.Quotient.liftₐ I f.hom (fun _ hz ↦ h hz))
      have hl : p ≫ l = f := by
        apply CommAlgCat.hom_ext
        ext z
        rfl
      refine ⟨(testSpec k).map l.op, ?_⟩
      change (testSpec k).map l.op ≫ (testSpec k).map p.op ≫ d.hom = x
      rw [← Category.assoc, ← Functor.map_comp, ← op_comp, hl, hf]
    · rintro ⟨y, hy⟩
      let l : Q ⟶ R := (F.preimage y).unop
      have hl : (testSpec k).map l.op = y := F.map_preimage y
      have hlf : p ≫ l = f := by
        apply Quiver.Hom.op_inj
        apply F.map_injective
        apply (cancel_mono d.hom).mp
        rw [op_comp, Functor.map_comp, Category.assoc, hl, hf]
        exact hy
      intro z hz
      change f.hom z = 0
      rw [← hlf]
      change l.hom (Ideal.Quotient.mk I z) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
  exact closedSubgroupOfPoints hX inclusion hclosed S hS

end

end LinearAlgebraicGroups.UnitriangularSupportSubgroups
