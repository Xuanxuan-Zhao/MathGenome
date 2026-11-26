import Specs.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import Specs.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
import LinearAlgebraicGroups.Reductive.GeometricRadicals
import LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
import Mathlib.Tactic.Group
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.MaximalToriConjugate

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open Specs.GeometricBorelConjugacy (IsBorel ConjugatesSubgroups subgroupOfSubgroup)
open Specs.GeometricRadicals (IsTorus IsMaximalTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.MaximalToriConjugate

open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private definingIdeal definingIdeal_le factor_iso_of_definingIdeal_eq
  factor_closed from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private torusCoordinatesDomain from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel

noncomputable section

variable {k : Type u} [Field k] {G H : GroupScheme k}

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem torus_of_iso (e : G ≅ H) (h : IsTorus G) : IsTorus H := by
  obtain ⟨E, _, _, _, r, ⟨t⟩⟩ := h
  exact ⟨E, inferInstance, inferInstance, inferInstance, r,
    ⟨(groupBaseChange k E).mapIso e.symm ≪≫ t⟩⟩

private theorem isTorus_iff_coordinates (D : AffineAlgebraicGroup k) :
    IsTorus D.val ↔ Specs.SmoothDiagonalKernel.IsTorusGroup D := by
  constructor
  · intro h
    obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation D
    exact ⟨A, ⟨e⟩, (GeometricRadicals.torusCoordinateComparison A).mp (torus_of_iso e.symm h)⟩
  · rintro ⟨A, ⟨e⟩, h⟩
    exact torus_of_iso e ((GeometricRadicals.torusCoordinateComparison A).mpr h)

private theorem solvable_maximal_torus_iff (D : AffineAlgebraicGroup k)
    (T : ClosedSubgroup D.val) :
    Specs.GeometricTorusSplitting.IsMaximalTorus T ↔ IsMaximalTorus T := by
  have h (S : ClosedSubgroup D.val) := isTorus_iff_coordinates (closedSubgroupAlgebraicGroup S)
  constructor
  · intro ht
    exact ⟨(h T).mpr ht.1, fun S hS hTS ↦ ht.2 S ((h S).mp hS) hTS⟩
  · intro ht
    exact ⟨(h T).mp ht.1, fun S hS hTS ↦ ht.2 S ((h S).mpr hS) hTS⟩

private abbrev rationalConstant {X : SchemeOver k} (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    X ⟶ G.X :=
  toUnit X ≫ g

private def conjugate {X : SchemeOver k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (x : X ⟶ G.X) : X ⟶ G.X :=
  rationalConstant g * x * (rationalConstant g)⁻¹

private theorem comp_conjugate {X Y : SchemeOver k} (f : X ⟶ Y)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) (x : Y ⟶ G.X) :
    f ≫ conjugate g x = conjugate g (f ≫ x) := by
  simp [conjugate, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit]

private theorem conjugate_comp {X : SchemeOver k} (a : G ⟶ H)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) (x : X ⟶ G.X) :
    conjugate g x ≫ a.hom.hom = conjugate (g ≫ a.hom.hom) (x ≫ a.hom.hom) := by
  simp [conjugate, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

private theorem conjugate_mul {X : SchemeOver k} (a b : 𝟙_ (SchemeOver k) ⟶ G.X)
    (x : X ⟶ G.X) :
    conjugate (a * b) x = conjugate a (conjugate b x) := by
  simp only [conjugate, MonObj.comp_mul, mul_inv_rev]
  group

private theorem conjugate_inv_cancel {X : SchemeOver k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (x : X ⟶ G.X) :
    conjugate g⁻¹ (conjugate g x) = x := by
  simp only [conjugate, GrpObj.comp_inv, inv_inv]
  group

private def conjugationIso (g : 𝟙_ (SchemeOver k) ⟶ G.X) : G ≅ G := by
  let e : G.X ≅ G.X :=
    ⟨conjugate g (𝟙 _), conjugate g⁻¹ (𝟙 _),
      by rw [comp_conjugate, Category.comp_id, conjugate_inv_cancel],
      by
        rw [comp_conjugate, Category.comp_id]
        simpa only [inv_inv] using conjugate_inv_cancel g⁻¹ (𝟙 G.X)⟩
  refine Grp.mkIso e ?_ ?_
  · change η[G.X] ≫ conjugate g (𝟙 G.X) = η[G.X]
    rw [comp_conjugate, Category.comp_id]
    change conjugate g (1 : 𝟙_ (SchemeOver k) ⟶ G.X) = 1
    simp [conjugate]
  · change μ[G.X] ≫ conjugate g (𝟙 G.X) =
      (conjugate g (𝟙 G.X) ⊗ₘ conjugate g (𝟙 G.X)) ≫ μ[G.X]
    let a := fst G.X G.X
    let b := snd G.X G.X
    let c := conjugate g (𝟙 G.X)
    have hab : a * b = μ[G.X] := by
      change lift (fst G.X G.X) (snd G.X G.X) ≫ μ[G.X] = μ[G.X]
      rw [lift_fst_snd, Category.id_comp]
    have ha : a ≫ c = conjugate g a := by
      rw [show c = conjugate g (𝟙 G.X) from rfl, comp_conjugate, Category.comp_id]
    have hb : b ≫ c = conjugate g b := by
      rw [show c = conjugate g (𝟙 G.X) from rfl, comp_conjugate, Category.comp_id]
    calc
      μ[G.X] ≫ c = conjugate g (a * b) := by
        rw [hab, show c = conjugate g (𝟙 G.X) from rfl, comp_conjugate, Category.comp_id]
      _ = conjugate g a * conjugate g b := by
        unfold conjugate
        group
      _ = (c ⊗ₘ c) ≫ μ[G.X] := by
        rw [← ha, ← hb]
        exact congrArg (· ≫ μ[G.X]) (lift_fst_comp_snd_comp c c)

private theorem conjugates_trans {A B C : ClosedSubgroup G}
    {g h : 𝟙_ (SchemeOver k) ⟶ G.X}
    (hg : ConjugatesSubgroups g A B) (hh : ConjugatesSubgroups h B C) :
    ConjugatesSubgroups (h * g) A C := by
  obtain ⟨e, he⟩ := hg
  obtain ⟨f, hf⟩ := hh
  change (e.hom ≫ B.inclusion).hom.hom = conjugate g A.inclusion.hom.hom at he
  change (f.hom ≫ C.inclusion).hom.hom = conjugate h B.inclusion.hom.hom at hf
  refine ⟨e ≪≫ f, ?_⟩
  change e.hom.hom.hom ≫ (f.hom ≫ C.inclusion).hom.hom =
    conjugate (h * g) A.inclusion.hom.hom
  rw [hf, comp_conjugate, conjugate_mul]
  exact congrArg (conjugate h) he

private theorem inclusion_mono (B : ClosedSubgroup G) : Mono B.inclusion := by
  have := B.isClosedImmersion
  have hm : Mono B.inclusion.hom.hom := Over.mono_of_mono_left _
  exact (Grp.forget (SchemeOver k)).mono_of_mono_map (f := B.inclusion) hm

private theorem subgroupOfSubgroup_le (B : ClosedSubgroup G) (S T : ClosedSubgroup B.group) :
    IsSubgroupOf (subgroupOfSubgroup B S) (subgroupOfSubgroup B T) ↔ IsSubgroupOf S T := by
  have := inclusion_mono B
  constructor
  · rintro ⟨f, hf⟩
    change f ≫ (T.inclusion ≫ B.inclusion) = S.inclusion ≫ B.inclusion at hf
    rw [← Category.assoc] at hf
    exact ⟨f, (cancel_mono B.inclusion).mp hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, by
      change f ≫ T.inclusion ≫ B.inclusion = S.inclusion ≫ B.inclusion
      rw [← Category.assoc, hf]⟩

private theorem local_maximal_of_ambient (B : ClosedSubgroup G)
    (T : ClosedSubgroup B.group) (h : IsMaximalTorus (subgroupOfSubgroup B T)) :
    IsMaximalTorus T := by
  refine ⟨h.1, fun S hS hTS ↦ (subgroupOfSubgroup_le B S T).mp ?_⟩
  exact h.2 (subgroupOfSubgroup B S) hS ((subgroupOfSubgroup_le B T S).mpr hTS)

private def restrictSubgroup (S B : ClosedSubgroup G) (j : S.group ⟶ B.group)
    (hj : j ≫ B.inclusion = S.inclusion) : ClosedSubgroup B.group :=
  ⟨S.group, j, factor_closed hj⟩

private theorem compose_restrict (S B : ClosedSubgroup G) (j : S.group ⟶ B.group)
    (hj : j ≫ B.inclusion = S.inclusion) :
    subgroupOfSubgroup B (restrictSubgroup S B j hj) = S := by
  have equal_of_inclusion (a b : S.group ⟶ G)
      (ha : IsClosedImmersion a.hom.hom.left) (hb : IsClosedImmersion b.hom.hom.left)
      (hab : a = b) : (⟨S.group, a, ha⟩ : ClosedSubgroup G) = ⟨S.group, b, hb⟩ := by
    cases hab
    rfl
  exact equal_of_inclusion _ _ _ _ hj

private def transportSubgroup (e : G ≅ H) (S : ClosedSubgroup G) : ClosedSubgroup H := by
  have := S.isClosedImmersion
  have : IsIso e.hom.hom.hom.left := (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.hom
  exact ⟨S.group, S.inclusion ≫ e.hom, inferInstanceAs
    (IsClosedImmersion (S.inclusion.hom.hom.left ≫ e.hom.hom.hom.left))⟩

private theorem maximal_of_square (q : G ≅ H) (S : ClosedSubgroup G) (T : ClosedSubgroup H)
    (e : S.group ≅ T.group) (h : e.hom ≫ T.inclusion = S.inclusion ≫ q.hom)
    (hS : IsMaximalTorus S) : IsMaximalTorus T := by
  refine ⟨torus_of_iso e hS.1, ?_⟩
  intro U hU hTU
  obtain ⟨j, hj⟩ := hTU
  let V := transportSubgroup q.symm U
  have hSV : IsSubgroupOf S V := ⟨e.hom ≫ j, by
    change (e.hom ≫ j) ≫ U.inclusion ≫ q.inv = S.inclusion
    simp only [Category.assoc, ← Category.assoc j, hj]
    rw [← Category.assoc, h, Category.assoc, q.hom_inv_id, Category.comp_id]⟩
  obtain ⟨l, hl⟩ := hS.2 V hU hSV
  refine ⟨l ≫ e.hom, ?_⟩
  change l ≫ S.inclusion = U.inclusion ≫ q.inv at hl
  rw [Category.assoc, h, ← Category.assoc, hl, Category.assoc, q.inv_hom_id, Category.comp_id]

private theorem conjugates_maximal {S T : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} (h : ConjugatesSubgroups g S T)
    (hS : IsMaximalTorus S) : IsMaximalTorus T := by
  obtain ⟨e, he⟩ := h
  refine maximal_of_square (conjugationIso g) S T e (Grp.hom_ext _ _ ?_) hS
  change (e.hom ≫ T.inclusion).hom.hom =
    S.inclusion.hom.hom ≫ conjugate g (𝟙 G.X)
  rw [comp_conjugate, Category.comp_id]
  exact he

private theorem conjugates_transport {B C : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} (e : B.group ≅ C.group)
    (he : (e.hom ≫ C.inclusion).hom.hom = conjugate g B.inclusion.hom.hom)
    (S : ClosedSubgroup B.group) :
    ConjugatesSubgroups g (subgroupOfSubgroup B S)
      (subgroupOfSubgroup C (transportSubgroup e S)) := by
  refine ⟨Iso.refl _, ?_⟩
  change (𝟙 S.group ≫ (S.inclusion ≫ e.hom) ≫ C.inclusion).hom.hom =
    conjugate g (S.inclusion.hom.hom ≫ B.inclusion.hom.hom)
  rw [Category.id_comp, Category.assoc]
  change S.inclusion.hom.hom ≫ (e.hom ≫ C.inclusion).hom.hom = _
  rw [he, comp_conjugate]

private theorem conjugates_in_ambient (B : ClosedSubgroup G) {S T : ClosedSubgroup B.group}
    {g : 𝟙_ (SchemeOver k) ⟶ B.group.X} (h : ConjugatesSubgroups g S T) :
    ConjugatesSubgroups (g ≫ B.inclusion.hom.hom) (subgroupOfSubgroup B S)
      (subgroupOfSubgroup B T) := by
  obtain ⟨e, he⟩ := h
  change (e.hom ≫ T.inclusion).hom.hom = conjugate g S.inclusion.hom.hom at he
  refine ⟨e, ?_⟩
  change (e.hom ≫ T.inclusion ≫ B.inclusion).hom.hom =
    conjugate (g ≫ B.inclusion.hom.hom) (S.inclusion.hom.hom ≫ B.inclusion.hom.hom)
  rw [← Category.assoc]
  change (e.hom ≫ T.inclusion).hom.hom ≫ B.inclusion.hom.hom = _
  rw [he, conjugate_comp]

private theorem conjugates_preserves_borel (B : ClosedSubgroup G)
    (g : 𝟙_ (SchemeOver k) ⟶ B.group.X) :
    ConjugatesSubgroups (g ≫ B.inclusion.hom.hom) B B := by
  refine ⟨conjugationIso g, ?_⟩
  change conjugate g (𝟙 B.group.X) ≫ B.inclusion.hom.hom =
    conjugate (g ≫ B.inclusion.hom.hom) B.inclusion.hom.hom
  rw [conjugate_comp, Category.id_comp]

private theorem subgroup_trans {S T U : ClosedSubgroup G}
    (hST : IsSubgroupOf S T) (hTU : IsSubgroupOf T U) : IsSubgroupOf S U := by
  obtain ⟨a, ha⟩ := hST
  obtain ⟨b, hb⟩ := hTU
  exact ⟨a ≫ b, by rw [Category.assoc, hb, ha]⟩

private theorem definingIdeal_prime_of_torus {A : AffineAlgebraicGroup k}
    (T : ClosedSubgroup A.val) (hT : IsTorus T.group) : (definingIdeal T).IsPrime := by
  obtain ⟨R, ⟨e⟩, hR⟩ := (isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mp hT
  have : IsDomain R := torusCoordinatesDomain R hR
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
  have : IsIntegral (F.obj (specGroup R)) :=
    inferInstanceAs (IsIntegral (Spec (CommRingCat.of R)))
  have : IsIntegral T.group.X.left := IsIntegral.of_isIso (F.map e.hom)
  have : IsDomain Γ(T.group.X.left, ⊤) := inferInstance
  exact RingHom.ker_isPrime _

/-- A torus of least prime-ideal height among the tori containing the given
one is maximal. Strict inclusion of these integral closed subgroups strictly
decreases the height of the defining prime. -/
private theorem exists_maximal_torus_over (A : AffineAlgebraicGroup k)
    (S : ClosedSubgroup A.val) (hS : IsTorus S.group) :
    ∃ T : ClosedSubgroup A.val, IsMaximalTorus T ∧ IsSubgroupOf S T := by
  classical
  have hAa := A.property.1
  have hAf := A.property.2.1
  have hAn : IsLocallyNoetherian A.val.X.left := LocallyOfFiniteType.isLocallyNoetherian A.val.X.hom
  have : IsNoetherianRing Γ(A.val.X.left, ⊤) :=
    hAn.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let height (T : ClosedSubgroup A.val) := (definingIdeal T).height.toNat
  let admissible (n : ℕ) :=
    ∃ T : ClosedSubgroup A.val, IsTorus T.group ∧ IsSubgroupOf S T ∧ height T = n
  have hex : ∃ n, admissible n := ⟨_, S, hS, ⟨𝟙 _, Category.id_comp _⟩, rfl⟩
  obtain ⟨T, hT, hST, hmin⟩ := Nat.find_spec hex
  refine ⟨T, ⟨hT, ?_⟩, hST⟩
  intro U hU hTU
  obtain ⟨j, hj⟩ := hTU
  have hle := definingIdeal_le j hj
  have hpriT := definingIdeal_prime_of_torus T hT
  have hpriU := definingIdeal_prime_of_torus U hU
  have heq : definingIdeal U = definingIdeal T := by
    by_contra hne
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
    have eqU := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal U))
    have eqT := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal T))
    have hlt' : height U < height T :=
      ENat.natCast_lt_natCast.mp (eqU.symm ▸ eqT.symm ▸ hlt)
    have hleast : height T ≤ height U := by
      rw [hmin]
      exact Nat.find_min' hex ⟨U, hU, subgroup_trans hST ⟨j, hj⟩, rfl⟩
    exact (not_lt_of_ge hleast) hlt'
  have := factor_iso_of_definingIdeal_eq j hj heq.symm
  refine ⟨inv j, ?_⟩
  rw [← hj, IsIso.inv_hom_id_assoc]

private theorem solvable_tori_conjugate [IsAlgClosed k]
    (splitting : Specs.GeometricTorusSplitting.Splitting.{u})
    (conjugacy : Specs.GeometricTorusSplitting.Conjugacy.{u})
    (D : AffineAlgebraicGroup k) (hD : Smooth D.val.X.hom)
    (hc : ConnectedSpace D.val.X.left) (hd : Specs.SchemeDerivedGroup.IsSolvable D.val)
    (S T : ClosedSubgroup D.val) (hS : IsMaximalTorus S) (hT : IsMaximalTorus T) :
    ∃ g : 𝟙_ (SchemeOver k) ⟶ D.val.X, ConjugatesSubgroups g S T := by
  obtain ⟨U, _, _, hU, _⟩ := splitting D hD hc hd
  obtain ⟨g, e, he⟩ := conjugacy D hD hc hd U hU S T
    ((solvable_maximal_torus_iff D S).mpr hS) ((solvable_maximal_torus_iff D T).mpr hT)
  exact ⟨g ≫ U.inclusion.hom.hom, e, he⟩

theorem borelPairsConjugate_conditional :
    Specs.GeometricTorusSplitting.Conjugacy.{u} →
    Specs.GeometricTorusSplitting.Splitting.{u} →
    Specs.GeometricBorelConjugacy.BorelExists.{u} →
    Specs.GeometricBorelConjugacy.BorelsConjugate.{u} →
    Specs.GeometricBorelConjugacy.ClosedFlagOrbitExists.{u} →
    Specs.GeometricBorelConjugacy.ClosedFlagStabilizerIsBorel.{u} →
    Specs.GeometricBorelConjugacy.TorusContainedInBorel.{u} →
    BorelPairsConjugate.{u} := by
  intro conjugacy splitting _ borelsConjugate _ _ _ k _ _ A hA hc B C hB hC S T hS hT
  obtain ⟨g, e, he⟩ := borelsConjugate A hA hc B C hB hC
  let S' := transportSubgroup e S
  have hS' : IsMaximalTorus S' := maximal_of_square e S S' (Iso.refl _) (Category.id_comp _) hS
  obtain ⟨b, hb⟩ := solvable_tori_conjugate splitting conjugacy (closedSubgroupAlgebraicGroup C)
    hC.1.1 hC.1.2.1 hC.1.2.2 S' T hS' hT
  refine ⟨(b ≫ C.inclusion.hom.hom) * g, ?_, ?_⟩
  · exact conjugates_trans ⟨e, he⟩ (conjugates_preserves_borel C b)
  · exact conjugates_trans (conjugates_transport e he S) (conjugates_in_ambient C hb)

theorem maximalToriConjugate_conditional :
    Specs.GeometricTorusSplitting.Conjugacy.{u} →
    Specs.GeometricTorusSplitting.Splitting.{u} →
    Specs.GeometricBorelConjugacy.BorelExists.{u} →
    Specs.GeometricBorelConjugacy.BorelsConjugate.{u} →
    Specs.GeometricBorelConjugacy.ClosedFlagOrbitExists.{u} →
    Specs.GeometricBorelConjugacy.ClosedFlagStabilizerIsBorel.{u} →
    Specs.GeometricBorelConjugacy.TorusContainedInBorel.{u} →
    ToriConjugate.{u} := by
  intro conjugacy splitting borelExists borelsConjugate orbitExists stabilizerBorel torusInBorel
    k _ _ A hA hc S T hS hT
  obtain ⟨B, hB, j, hj⟩ := torusInBorel A hA hc S hS.1
  obtain ⟨C, hC, l, hl⟩ := torusInBorel A hA hc T hT.1
  have heS := compose_restrict S B j hj
  have heT := compose_restrict T C l hl
  obtain ⟨g, _, hg⟩ := borelPairsConjugate_conditional conjugacy splitting borelExists
    borelsConjugate orbitExists stabilizerBorel torusInBorel A hA hc B C hB hC
    (restrictSubgroup S B j hj) (restrictSubgroup T C l hl)
    (local_maximal_of_ambient _ _ (heS.symm ▸ hS))
    (local_maximal_of_ambient _ _ (heT.symm ▸ hT))
  exact ⟨g, by simpa only [heS, heT] using hg⟩

theorem borelMaximalTorusIff_conditional :
    Specs.GeometricTorusSplitting.Conjugacy.{u} →
    Specs.GeometricTorusSplitting.Splitting.{u} →
    Specs.GeometricBorelConjugacy.BorelExists.{u} →
    Specs.GeometricBorelConjugacy.BorelsConjugate.{u} →
    Specs.GeometricBorelConjugacy.ClosedFlagOrbitExists.{u} →
    Specs.GeometricBorelConjugacy.ClosedFlagStabilizerIsBorel.{u} →
    Specs.GeometricBorelConjugacy.TorusContainedInBorel.{u} →
    BorelMaximalTorusIff.{u} := by
  intro conjugacy splitting borelExists borelsConjugate orbitExists stabilizerBorel torusInBorel
    k _ _ A hA hc B hB T
  refine ⟨?_, local_maximal_of_ambient B T⟩
  intro hT
  obtain ⟨S, hS, _⟩ := exists_maximal_torus_over A (subgroupOfSubgroup B T) hT.1
  obtain ⟨C, hC, j, hj⟩ := torusInBorel A hA hc S hS.1
  have heS := compose_restrict S C j hj
  obtain ⟨g, _, hg⟩ := borelPairsConjugate_conditional conjugacy splitting borelExists
    borelsConjugate orbitExists stabilizerBorel torusInBorel A hA hc C B hC hB
    (restrictSubgroup S C j hj) T (local_maximal_of_ambient _ _ (heS.symm ▸ hS)) hT
  exact conjugates_maximal (by simpa only [heS] using hg) hS

private theorem normalizes_of_conjugates_self (T : ClosedSubgroup G)
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} (h : ConjugatesSubgroups g T T) :
    Normalizes T.inclusion g := by
  obtain ⟨e, he⟩ := h
  change (e.hom ≫ T.inclusion).hom.hom = conjugate g T.inclusion.hom.hom at he
  let d := (Grp.forget (SchemeOver k)).mapIso e
  refine ⟨d ⊗ᵢ Iso.refl _, ?_, ?_⟩
  · change (d.hom ⊗ₘ 𝟙 _) ≫ snd _ _ = snd _ _
    rw [tensorHom_snd, Category.comp_id]
  · change (d.hom ⊗ₘ 𝟙 _) ≫ fst _ _ ≫ T.inclusion.hom.hom =
      conjugateFamily T.inclusion g
    rw [tensorHom_fst_assoc]
    change fst _ _ ≫ (e.hom ≫ T.inclusion).hom.hom = _
    rw [he, comp_conjugate]
    have hf : toUnit (T.group.X ⊗ 𝟙_ (SchemeOver k)) =
        snd T.group.X (𝟙_ (SchemeOver k)) := Subsingleton.elim _ _
    simp only [conjugate, rationalConstant, conjugateFamily, hf]

theorem normalizerTransitiveOnBorels_conditional :
    Specs.GeometricTorusSplitting.Conjugacy.{u} →
    Specs.GeometricTorusSplitting.Splitting.{u} →
    Specs.GeometricBorelConjugacy.BorelExists.{u} →
    Specs.GeometricBorelConjugacy.BorelsConjugate.{u} →
    Specs.GeometricBorelConjugacy.ClosedFlagOrbitExists.{u} →
    Specs.GeometricBorelConjugacy.ClosedFlagStabilizerIsBorel.{u} →
    Specs.GeometricBorelConjugacy.TorusContainedInBorel.{u} →
    NormalizerTransitiveOnBorels.{u} := by
  intro conjugacy splitting borelExists borelsConjugate orbitExists stabilizerBorel torusInBorel
    k _ _ A hA hc T hT B C hB hC ⟨j, hj⟩ ⟨l, hl⟩
  have heB := compose_restrict T B j hj
  have heC := compose_restrict T C l hl
  obtain ⟨g, hg, ht⟩ := borelPairsConjugate_conditional conjugacy splitting borelExists
    borelsConjugate orbitExists stabilizerBorel torusInBorel A hA hc B C hB hC
    (restrictSubgroup T B j hj) (restrictSubgroup T C l hl)
    (local_maximal_of_ambient _ _ (heB.symm ▸ hT))
    (local_maximal_of_ambient _ _ (heC.symm ▸ hT))
  exact ⟨g, normalizes_of_conjugates_self T (by simpa only [heB, heC] using ht), hg⟩

end

end LinearAlgebraicGroups.MaximalToriConjugate

universe v8_closure_92da80f42f1f8d5a_u0
theorem _root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«borelMaximalTorusIff» : _root_.«LinearAlgebraicGroups».«Specs».«MaximalToriConjugate».«BorelMaximalTorusIff».{v8_closure_92da80f42f1f8d5a_u0} :=
  @_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«borelMaximalTorusIff_conditional».{v8_closure_92da80f42f1f8d5a_u0} (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«conjugacy».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«splitting».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel».{v8_closure_92da80f42f1f8d5a_u0})
theorem _root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«borelPairsConjugate» : _root_.«LinearAlgebraicGroups».«Specs».«MaximalToriConjugate».«BorelPairsConjugate».{v8_closure_92da80f42f1f8d5a_u0} :=
  @_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«borelPairsConjugate_conditional».{v8_closure_92da80f42f1f8d5a_u0} (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«conjugacy».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«splitting».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel».{v8_closure_92da80f42f1f8d5a_u0})
theorem _root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«maximalToriConjugate» : _root_.«LinearAlgebraicGroups».«Specs».«MaximalToriConjugate».«ToriConjugate».{v8_closure_92da80f42f1f8d5a_u0} :=
  @_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«maximalToriConjugate_conditional».{v8_closure_92da80f42f1f8d5a_u0} (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«conjugacy».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«splitting».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel».{v8_closure_92da80f42f1f8d5a_u0})
theorem _root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«normalizerTransitiveOnBorels» : _root_.«LinearAlgebraicGroups».«Specs».«MaximalToriConjugate».«NormalizerTransitiveOnBorels».{v8_closure_92da80f42f1f8d5a_u0} :=
  @_root_.«LinearAlgebraicGroups».«MaximalToriConjugate».«normalizerTransitiveOnBorels_conditional».{v8_closure_92da80f42f1f8d5a_u0} (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«conjugacy».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«splitting».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel».{v8_closure_92da80f42f1f8d5a_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel».{v8_closure_92da80f42f1f8d5a_u0})
