import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.BorelFixedPoint
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FaithfulLinearization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.BorelFixedPoint
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.GeometricBorelConjugacy

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricBorelConjugacy
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf IsSolvable DerivedSeries)

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

open private definingIdeal definingIdeal_le factor_iso_of_definingIdeal_eq
  identity_smoothConnectedNormal identity_solvable solvable_iff_sections rationalSections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

private theorem subgroupOf_trans {G : GroupScheme k} {A B C : ClosedSubgroup G}
    (hAB : IsSubgroupOf A B) (hBC : IsSubgroupOf B C) : IsSubgroupOf A C := by
  obtain ⟨f, hf⟩ := hAB
  obtain ⟨g, hg⟩ := hBC
  exact ⟨f ≫ g, by rw [Category.assoc, hg, hf]⟩

private theorem exists_borel_above [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (hT : IsSmoothConnectedSolvable T) :
    ∃ B : ClosedSubgroup G.val, IsBorel B ∧ IsSubgroupOf T B := by
  classical
  letI := G.property.1
  letI := G.property.2.1
  have hG : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  haveI : IsNoetherianRing Γ(G.val.X.left, ⊤) :=
    hG.component_noetherian ⟨⊤, isAffineOpen_top G.val.X.left⟩
  let score (H : ClosedSubgroup G.val) := (definingIdeal H).height.toNat
  have hprime (H : ClosedSubgroup G.val) (hH : IsSmoothConnectedSolvable H) :
      (definingIdeal H).IsPrime := by
    haveI : IsIntegral H.group.X.left := WordDomainGeometry.smoothConnectedGroupIntegral
      (closedSubgroupAlgebraicGroup H) hH.1 hH.2.1
    exact RingHom.ker_isPrime _
  let eligible (n : ℕ) := ∃ H : ClosedSubgroup G.val,
    IsSmoothConnectedSolvable H ∧ IsSubgroupOf T H ∧ score H = n
  have hex : ∃ n, eligible n := ⟨score T, T, hT, ⟨𝟙 _, Category.id_comp _⟩, rfl⟩
  obtain ⟨B, hB, hTB, hscore⟩ := Nat.find_spec hex
  refine ⟨B, ⟨hB, ?_⟩, hTB⟩
  intro H hH hBH
  have hmin : score B ≤ score H :=
    hscore ▸ Nat.find_min' hex ⟨H, hH, subgroupOf_trans hTB hBH, rfl⟩
  obtain ⟨j, hj⟩ := hBH
  have hle := definingIdeal_le (G := G) j hj
  have hI : definingIdeal B = definingIdeal H := by
    by_contra hne
    haveI := hprime B hB
    haveI := hprime H hH
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime
      (lt_of_le_of_ne hle (Ne.symm hne))
    have hlt' : score H < score B := by
      have eH := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal H))
      have eB := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal B))
      exact ENat.natCast_lt_natCast.mp (eH.symm ▸ eB.symm ▸ hlt)
    exact (not_lt_of_ge hmin) hlt'
  haveI : IsIso j := factor_iso_of_definingIdeal_eq (G := G) j hj hI
  exact ⟨inv j, by rw [← hj, IsIso.inv_hom_id_assoc]⟩

theorem borelExists_conditional
    (_ : Specs.BorelFixedPoint.OverAlgClosed.{u}) (_ : Specs.BorelFixedPoint.Split.{u}) :
    BorelExists.{u} := by
  intro k _ _ G _ _
  let T := Specs.GeometricRadicals.identitySubgroup G
  have h := identity_smoothConnectedNormal G
  obtain ⟨B, hB, _⟩ := exists_borel_above G T ⟨h.1, h.2.1, identity_solvable G⟩
  exact ⟨B, hB⟩

private theorem torus_smooth_connected_solvable [IsAlgClosed k] (T : AffineAlgebraicGroup k)
    (hT : Specs.GeometricRadicals.IsTorus T.val) :
    Smooth T.val.X.hom ∧ ConnectedSpace T.val.X.left ∧ IsSolvable T.val := by
  obtain ⟨E, _, _, hsep, hsplit⟩ := hT
  letI := hsep
  let e : k ≃+* E := RingEquiv.ofBijective (algebraMap k E)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  letI : IsAlgClosed E := IsAlgClosed.of_ringEquiv k E e
  haveI : IsIso (fieldSpecMap k E) :=
    (Scheme.Spec : CommRingCatᵒᵖ ⥤ Scheme).map_isIso
      ((RingEquiv.toCommRingCatIso e).hom.op)
  let U := baseChangedAlgebraicGroup E T
  have hU := EquivariantUnipotentSeries.split_torus_smooth_connected U hsplit
  let p : U.val.X.left ⟶ T.val.X.left := pullback.fst T.val.X.hom (fieldSpecMap k E)
  haveI : IsIso p := inferInstanceAs (IsIso (pullback.fst _ _))
  have hs : Smooth T.val.X.hom := by
    haveI : Smooth U.val.X.hom := hU.1
    have hh : Smooth (p ≫ T.val.X.hom) := by
      rw [pullback.condition]
      exact inferInstanceAs (Smooth (U.val.X.hom ≫ fieldSpecMap k E))
    exact (MorphismProperty.cancel_left_of_respectsIso @Smooth p _).mp hh
  have hc : ConnectedSpace T.val.X.left := p.homeomorph.connectedSpace_iff.mp hU.2
  refine ⟨hs, hc, (solvable_iff_sections T hs hc).mpr ?_⟩
  apply Group.isSolvable_of_comm
  intro a b
  let R := CommAlgCat.of E E
  let S := (testSpec k).obj (op ((restrictTestAlgebra k E).obj R))
  let d : rationalSections T.val →* (S ⟶ T.val.X) :=
    { toFun x := toUnit S ≫ x
      map_one' := MonObj.comp_one _
      map_mul' _ _ := MonObj.comp_mul _ _ _ }
  haveI : IsIso (toUnit S) := by
    have h : (toUnit S).left = fieldSpecMap k E := by
      change S.hom = fieldSpecMap k E
      rw [restrictTestAlgebra_spec_hom]
      change Spec.map (CommRingCat.ofHom (algebraMap E E)) ≫ _ = _
      rw [show CommRingCat.ofHom (algebraMap E E) = 𝟙 (CommRingCat.of E) from rfl,
        Spec.map_id, Category.id_comp]
    haveI : IsIso ((Over.forget _).map (toUnit S)) := by
      change IsIso (toUnit S).left
      rw [h]
      infer_instance
    exact isIso_of_reflects_iso _ (Over.forget _)
  obtain ⟨r, ⟨t⟩⟩ := hsplit
  let F := groupPointsFunctor E
  let eP := StandardGroups.multiplicativePowerGroupPointsIso E (ULift.{u} (Fin r))
  let q := (F.mapIso t ≪≫ eP).app R
  let m : (S ⟶ T.val.X) →* (ULift.{u} (Fin r) → Rˣ) :=
    q.hom.hom.comp (baseChangePointGroupEquiv E T.val R).symm.toMonoidHom
  have hm : Function.Injective m := (ConcreteCategory.bijective_of_isIso q.hom).1.comp
    (baseChangePointGroupEquiv E T.val R).symm.injective
  apply (cancel_epi (toUnit S)).mp
  change d (a * b) = d (b * a)
  apply hm
  simp only [map_mul]
  exact mul_comm (m (d a)) (m (d b))

theorem torusContainedInBorel_conditional
    (_ : Specs.BorelFixedPoint.OverAlgClosed.{u}) (_ : Specs.BorelFixedPoint.Split.{u}) :
    TorusContainedInBorel.{u} := by
  intro k _ _ G _ _ T hT
  exact exists_borel_above G T (torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup T) hT)

private theorem fullFlagRanks_strictMono (n : ℕ) : StrictMono (fullFlagRanks n) :=
  fun _ _ h ↦ Nat.add_lt_add_right h 1

private theorem fullFlagRanks_le (n : ℕ) (i : Fin (n - 1)) : fullFlagRanks n i ≤ n := by
  have hi := i.isLt
  unfold fullFlagRanks
  omega

open private restrictGroupAction restrictGroupAction_smul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit

/-- A faithful representation supplies a projective full flag scheme and its action. -/
private theorem exists_fullFlagAction (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) :
    ∃ (n : ℕ) (v : Module.Basis (Fin n) k (Fin n → k)) (F : FullFlagAction G v),
      Nonempty F.flags.scheme.left := by
  obtain ⟨n, L, ⟨EL⟩, ρ, hρ⟩ := faithfulLinearization k G
  let v := Pi.basisFun k (Fin n)
  let ranks := fullFlagRanks n
  have hdim : Module.finrank k (Fin n → k) = n := by
    simp [Module.finrank_eq_card_basis v]
  obtain ⟨P, D, M, E, A, _, _, _, htrans, ⟨J⟩, ⟨C⟩⟩ :=
    FlagSchemes.flagSchemeGeometry k (Fin n → k) n v (n - 1) ranks
      (fullFlagRanks_strictMono n) (fun i ↦ hdim.symm ▸ fullFlagRanks_le n i)
  have hM : IsAffine M.X.left :=
    essImage_Spec.mp ⟨op (CommRingCat.of (Specs.StandardGroups.GLCoordinates k
      (ULift.{u} (Fin n)))), ⟨(Over.forget _).mapIso C.matrixIso⟩⟩
  let f₀ : L.val ⟶ M := (groupHomEquiv L.val M L.property.1).symm (EL ≪≫ E.symm).hom
  let g₀ : M ⟶ L.val := (groupHomEquiv M L.val hM).symm (EL ≪≫ E.symm).inv
  have hf₀ : (groupPointsFunctor k).map f₀ = (EL ≪≫ E.symm).hom :=
    (groupHomEquiv L.val M L.property.1).apply_symm_apply _
  have hg₀ : (groupPointsFunctor k).map g₀ = (EL ≪≫ E.symm).inv :=
    (groupHomEquiv M L.val hM).apply_symm_apply _
  let e : L.val ≅ M := ⟨f₀, g₀, by
    apply (groupHomEquiv L.val L.val L.property.1).injective
    change (groupPointsFunctor k).map (f₀ ≫ g₀) = (groupPointsFunctor k).map (𝟙 _)
    rw [Functor.map_comp, hf₀, hg₀, Iso.hom_inv_id, CategoryTheory.Functor.map_id], by
    apply (groupHomEquiv M M hM).injective
    change (groupPointsFunctor k).map (g₀ ≫ f₀) = (groupPointsFunctor k).map (𝟙 _)
    rw [Functor.map_comp, hf₀, hg₀, Iso.inv_hom_id, CategoryTheory.Functor.map_id]⟩
  let f := ρ ≫ e.hom
  haveI : IsClosedImmersion ρ.hom.hom.left := hρ
  haveI : IsIso e.hom.hom.hom.left :=
    ((Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e).isIso_hom
  have hf : IsClosedImmersion f.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion (ρ.hom.hom.left ≫ e.hom.hom.hom.left))
  obtain ⟨a, _, ha, _, _⟩ :=
    SmoothOrbit.flagOrbit k (Fin n → k) n v (n - 1) ranks P D M E A J C G f hs htrans
  exact ⟨n, v, ⟨P, D, M, E, A, J, f, hf, a, ha⟩,
    ⟨C.point.left (IsLocalRing.closedPoint k)⟩⟩

theorem closedFlagOrbitExists_conditional
    (_ : Specs.BorelFixedPoint.OverAlgClosed.{u}) (_ : Specs.BorelFixedPoint.Split.{u}) :
    ClosedFlagOrbitExists.{u} := by
  intro k _ _ G hs _
  obtain ⟨n, v, F, hnonempty⟩ := exists_fullFlagAction G hs
  letI := F.projective.proper
  obtain ⟨x, O, hO⟩ := SmoothOrbit.closedOrbitExists k G F.flags.scheme F.action
    hs inferInstance inferInstance inferInstance hnonempty
  exact ⟨n, v, F, x, O, hO⟩

open private orbitMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private fixed_iff_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

private abbrev ReducedComponent {G : AffineAlgebraicGroup k} (H : ClosedSubgroup G.val) :=
  EquivariantUnipotentSeries.ReducedIdentityComponent (closedSubgroupAlgebraicGroup H)

open private ReducedIdentityComponent.factorHom from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries

private theorem reducedComponent_spec {G : AffineAlgebraicGroup k} [PerfectField k]
    {H : ClosedSubgroup G.val} (C : ReducedComponent H) :
    IsReducedIdentityComponent C.subgroup := by
  haveI := C.smooth
  haveI := C.connected
  haveI := C.subgroup.isClosedImmersion
  refine ⟨isReduced_of_smooth_over_field C.subgroup.group.X.hom, ?_⟩
  have hcl : IsClopen (Set.range C.subgroup.inclusion.hom.hom.left) :=
    ⟨C.subgroup.inclusion.hom.hom.left.isClosedEmbedding.isClosed_range, C.open_range⟩
  have hunit : η[H.group.X].left (IsLocalRing.closedPoint k) ∈
      Set.range C.subgroup.inclusion.hom.hom.left := by
    refine ⟨η[C.subgroup.group.X].left (IsLocalRing.closedPoint k), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]
    rfl
  exact ((isConnected_range C.subgroup.inclusion.hom.hom.left.continuous).subset_connectedComponent
    hunit).antisymm (hcl.connectedComponent_subset hunit)

private theorem factor_group_through_subgroup {G A : GroupScheme k} (H : ClosedSubgroup G)
    (f : A ⟶ G) (i : A.X ⟶ H.group.X) (hi : i ≫ H.inclusion.hom.hom = f.hom.hom) :
    ∃ j : A ⟶ H.group, j ≫ H.inclusion = f := by
  letI := H.isClosedImmersion
  letI : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  have hone : η[A.X] ≫ i = η[H.group.X] := by
    rw [← cancel_mono H.inclusion.hom.hom, Category.assoc, hi, IsMonHom.one_hom,
      IsMonHom.one_hom]
  have hmul : μ[A.X] ≫ i = (i ⊗ₘ i) ≫ μ[H.group.X] := by
    rw [← cancel_mono H.inclusion.hom.hom, Category.assoc, hi, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hi]
  exact ⟨Grp.homMk'' i hone hmul, Grp.hom_ext _ _ hi⟩

private theorem orbitProjection_factors {G : GroupScheme k} {X : SchemeOver k}
    {a : ModObj G.X X} {x : 𝟙_ (SchemeOver k) ⟶ X} (O : Specs.SmoothOrbit.Presentation a x) :
    O.projection ≫ (O.openInClosure ≫ Specs.SmoothOrbit.closureInclusion a x) =
      Specs.SmoothOrbit.orbitMap a x := by
  apply Over.OverMorphism.ext
  change O.projection.left ≫ O.openInClosure.left ≫
    (Specs.SmoothOrbit.orbitMap a x).left.imageι = _
  rw [← Category.assoc, O.factors, Scheme.Hom.toImage_imageι]

/-- The fixed point theorem gives a rational translate of the chosen point
that is fixed by the subgroup on all test schemes. -/
private theorem fixed_on_closed_orbit [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    {X : SchemeOver k} (a : ModObj G.val.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (O : Specs.SmoothOrbit.Presentation a x) (hX : IsProper X.hom)
    (hO : IsClosedImmersion (O.openInClosure ≫ Specs.SmoothOrbit.closureInclusion a x).left)
    (fixed : Specs.BorelFixedPoint.OverAlgClosed.{u}) (B : ClosedSubgroup G.val)
    (hB : IsSmoothConnectedSolvable B) :
    ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
      letI := a
      ∀ (T : SchemeOver k) (b : T ⟶ B.group.X),
        (b ≫ B.inclusion.hom.hom) • ((toUnit T ≫ g) • (toUnit T ≫ x)) =
          (toUnit T ≫ g) • (toUnit T ≫ x) := by
  letI := a
  let j := O.openInClosure ≫ Specs.SmoothOrbit.closureInclusion a x
  letI : IsClosedImmersion j.left := hO
  letI : IsProper X.hom := hX
  have hp : IsProper O.orbit.hom := by rw [← Over.w j]; infer_instance
  let y₀ := η[G.val.X] ≫ O.projection
  have hn : Nonempty O.orbit.left := ⟨y₀.left (IsLocalRing.closedPoint k)⟩
  let b := restrictGroupAction B.inclusion O.action
  obtain ⟨Z, i, _, hfix, ⟨z⟩⟩ :=
    fixed (closedSubgroupAlgebraicGroup B) O.orbit b hB.1 hB.2.1 hB.2.2 hp hn
  let y := z ≫ i
  have hy : IsFixedBy b.smul y := (hfix _ y).2 ⟨z, rfl⟩
  have hyG : (y ≫ j).left (IsLocalRing.closedPoint k) ∈ Specs.SmoothOrbit.orbitSet a x := by
    obtain ⟨p, hp⟩ := O.surjective.1 (y.left (IsLocalRing.closedPoint k))
    refine ⟨p, ?_⟩
    rw [← orbitProjection_factors O]
    change (O.projection.left ≫ j.left) p = (y.left ≫ j.left) (IsLocalRing.closedPoint k)
    simp only [Scheme.Hom.comp_apply, hp]
  obtain ⟨g, hg⟩ := (SmoothOrbit.geometricOrbitLifts k G X a x (y ≫ j)).1 hyG
  refine ⟨g, ?_⟩
  intro T t
  have hyj : toUnit T ≫ y ≫ j = (toUnit T ≫ g) • (toUnit T ≫ x) := by
    rw [← hg, ← Category.assoc, orbitMap_comp]
  rw [← hyj]
  have hfixT := @fixed_iff_sections k _ B.group _ _ b y |>.mp hy (toUnit T) t
  have h := congrArg (· ≫ j) hfixT
  change (lift t (toUnit T ≫ y) ≫ b.smul) ≫ j = (toUnit T ≫ y) ≫ j at h
  rw [Category.assoc, restrictGroupAction_smul, Category.assoc, O.actionInclusion,
    ← Category.assoc, ← Category.assoc, lift_map, lift_map] at h
  simpa only [Hom.smul_def, Category.comp_id, Category.assoc] using h

private def conjugation {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    G ⟶ G := by
  let c : G.X ⟶ G.X := toUnit G.X ≫ g
  let f := c * (𝟙 G.X) * c⁻¹
  have h {T : SchemeOver k} (t : T ⟶ G.X) :
      t ≫ f = (toUnit T ≫ g) * t * (toUnit T ≫ g)⁻¹ := by
    simp only [f, c, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, comp_toUnit_assoc]
  refine Grp.homMk'' f ?_ ?_
  · rw [h]
    change g * (1 : 𝟙_ (SchemeOver k) ⟶ G.X) * g⁻¹ = 1
    group
  · rw [h]
    have hm : (fst G.X G.X * snd G.X G.X) = μ[G.X] := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    nth_rw 1 [← hm]
    have hf : f ⊗ₘ f = lift (fst G.X G.X ≫ f) (snd G.X G.X ≫ f) := by
      rw [← lift_map, lift_fst_snd, Category.id_comp]
    rw [hf, ← Hom.mul_def, h, h]
    group

private theorem conjugation_apply {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    {T : SchemeOver k} (t : T ⟶ G.X) :
    t ≫ (conjugation g).hom.hom = (toUnit T ≫ g) * t * (toUnit T ≫ g)⁻¹ := by
  simp only [conjugation, Grp.homMk''_hom_hom, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id,
    comp_toUnit_assoc]

private def conjugationIso {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X) : G ≅ G where
  hom := conjugation g
  inv := conjugation g⁻¹
  hom_inv_id := by
    apply Grp.hom_ext
    change (conjugation g).hom.hom ≫ (conjugation g⁻¹).hom.hom = 𝟙 G.X
    rw [conjugation_apply]
    have h := conjugation_apply g (𝟙 G.X)
    rw [Category.id_comp] at h
    rw [h, GrpObj.comp_inv]
    group
  inv_hom_id := by
    apply Grp.hom_ext
    change (conjugation g⁻¹).hom.hom ≫ (conjugation g).hom.hom = 𝟙 G.X
    rw [conjugation_apply]
    have h := conjugation_apply g⁻¹ (𝟙 G.X)
    rw [Category.id_comp] at h
    rw [h, GrpObj.comp_inv]
    group

private def conjugate {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (B : ClosedSubgroup G) : ClosedSubgroup G := by
  haveI := B.isClosedImmersion
  haveI : IsIso (conjugation g).hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso (conjugationIso g).hom
  exact ⟨B.group, B.inclusion ≫ conjugation g, inferInstanceAs
    (IsClosedImmersion (B.inclusion.hom.hom.left ≫ (conjugation g).hom.hom.left))⟩

private theorem conjugate_inclusion {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (B : ClosedSubgroup G) :
    (conjugate g B).inclusion = B.inclusion ≫ conjugation g := rfl

private theorem conjugate_subgroupOf {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    {A B : ClosedSubgroup G} (h : IsSubgroupOf A B) : IsSubgroupOf (conjugate g A) (conjugate g B) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, by rw [conjugate_inclusion, conjugate_inclusion, ← Category.assoc, hf]⟩

private theorem conjugate_inv_cancel {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (B : ClosedSubgroup G) : conjugate g⁻¹ (conjugate g B) = B := by
  have h : conjugation g ≫ conjugation g⁻¹ = 𝟙 G := (conjugationIso g).hom_inv_id
  cases B
  simp only [conjugate, Category.assoc, h, Category.comp_id]

private theorem borel_conjugate {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    {B : ClosedSubgroup G} (hB : IsBorel B) : IsBorel (conjugate g B) := by
  refine ⟨hB.1, ?_⟩
  intro H hH h
  have h' := conjugate_subgroupOf g⁻¹ h
  rw [conjugate_inv_cancel] at h'
  have h'' := conjugate_subgroupOf g (hB.2 (conjugate g⁻¹ H) hH h')
  have hh := conjugate_inv_cancel g⁻¹ H
  rw [inv_inv] at hh
  rwa [hh] at h''

private theorem subgroupOf_mutual_iso {G : GroupScheme k} {A B : ClosedSubgroup G}
    (hAB : IsSubgroupOf A B) (hBA : IsSubgroupOf B A) :
    ∃ e : A.group ≅ B.group, e.hom ≫ B.inclusion = A.inclusion := by
  obtain ⟨f, hf⟩ := hAB
  obtain ⟨g, hg⟩ := hBA
  letI := A.isClosedImmersion
  letI := B.isClosedImmersion
  letI : Mono A.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono B.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono A.inclusion := (Grp.forget _).mono_of_mono_map ‹Mono A.inclusion.hom.hom›
  letI : Mono B.inclusion := (Grp.forget _).mono_of_mono_map ‹Mono B.inclusion.hom.hom›
  exact ⟨⟨f, g, (cancel_mono A.inclusion).mp (by simp [hg, hf]),
    (cancel_mono B.inclusion).mp (by simp [hf, hg])⟩, hf⟩

private theorem borel_of_containing_borel {G : GroupScheme k} {A B : ClosedSubgroup G}
    (hA : IsBorel A) (hB : IsSmoothConnectedSolvable B)
    (hAB : IsSubgroupOf A B) : IsBorel B :=
  ⟨hB, fun H hH hBH ↦ subgroupOf_trans (hA.2 H hH (subgroupOf_trans hAB hBH)) hAB⟩

/-- A smooth connected solvable subgroup has a conjugate in the reduced
identity component of the stabilizer at the chosen point. -/
private theorem conjugate_in_reduced_stabilizer [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    {X : SchemeOver k} (a : ModObj G.val.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (O : Specs.SmoothOrbit.Presentation a x) (hX : IsProper X.hom)
    (hO : IsClosedImmersion (O.openInClosure ≫ Specs.SmoothOrbit.closureInclusion a x).left)
    (fixed : Specs.BorelFixedPoint.OverAlgClosed.{u}) (B : ClosedSubgroup G.val)
    (hB : IsSmoothConnectedSolvable B) (C : ReducedComponent O.stabilizer) :
    ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
      IsSubgroupOf (conjugate g B) (subgroupOfSubgroup O.stabilizer C.subgroup) := by
  letI := a
  obtain ⟨g, hg⟩ := fixed_on_closed_orbit a x O hX hO fixed B hB
  refine ⟨g⁻¹, ?_⟩
  let j : B.group ⟶ G.val := (conjugate g⁻¹ B).inclusion
  have h : Stabilizes a.smul x j.hom.hom := by
    change j.hom.hom • (toUnit B.group.X ≫ x) = toUnit B.group.X ≫ x
    change (B.inclusion.hom.hom ≫ (conjugation g⁻¹).hom.hom) • _ = _
    have hf := hg B.group.X (𝟙 B.group.X)
    rw [Category.id_comp] at hf
    rw [conjugation_apply, GrpObj.comp_inv, inv_inv, mul_smul, mul_smul, hf, inv_smul_smul]
  obtain ⟨f, hf⟩ := (O.representsStabilizer B.group.X j.hom.hom).mp h
  obtain ⟨q, hq⟩ := factor_group_through_subgroup O.stabilizer j f hf
  obtain ⟨v, hv⟩ := ReducedIdentityComponent.factorHom C (A := closedSubgroupAlgebraicGroup B) q hB.1 hB.2.1
  exact ⟨v, by
    change v ≫ C.subgroup.inclusion ≫ O.stabilizer.inclusion = j
    rw [← Category.assoc, hv, hq]⟩

open private quotient_section_eq affineBaseTerminal from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private hom_toBase_eq coordinateFlag_fixed orbit_apply from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagSchemes
open private isIso_point_openImmersion conjugate_fixes_iff from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private flags_eq_of_planes flagAction_plane from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagIncidence

private theorem split_solvable_points {G : GroupScheme k}
    (h : Specs.SchemeDerivedGroup.IsSplitSolvable G) (R : TestAlgebra k) :
    Group.IsSolvable (Points G.X R) := by
  induction h with
  | @trivial G e =>
    obtain ⟨e⟩ := e
    letI : Subsingleton (Points G.X R) := ⟨fun a b ↦
      (cancel_mono e.hom.hom.hom).mp ((isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)⟩
    infer_instance
  | @step G D _ _ Q q hq hfactor ih =>
    let S := (testSpec k).obj (op R)
    let p := IsMonHom.monoidHom q.hom.hom S
    let j := IsMonHom.monoidHom D.inclusion.hom.hom S
    have hK : p.ker ≤ j.range := by
      intro g hg
      have he : g ≫ q.hom.hom = (1 : S ⟶ G.X) ≫ q.hom.hom := by
        change p g = p 1
        rw [map_one]
        exact hg
      obtain ⟨t, ht⟩ := quotient_section_eq D q hq 1 g he.symm
      refine ⟨t, ?_⟩
      change t ≫ D.inclusion.hom.hom = g
      simpa only [inv_one, one_mul] using ht
    letI : Group.IsSolvable (Points Q.val.X R) := by
      rcases hfactor with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · letI : Group.IsSolvable ((Specs.StandardGroups.additivePoints k).obj R) :=
          inferInstanceAs (Group.IsSolvable (Multiplicative R))
        exact Group.isSolvable_of_isSolvable_injective
          (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1
      · letI : Group.IsSolvable ((Specs.StandardGroups.multiplicativePoints k).obj R) :=
          inferInstanceAs (Group.IsSolvable Rˣ)
        exact Group.isSolvable_of_isSolvable_injective
          (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1
    exact Group.isSolvable_of_ker_le_range j p hK

private theorem upper_triangular_points_solvable (n : ℕ) (R : TestAlgebra k) :
    Group.IsSolvable (Specs.Triangularization.upperTriangular (ULift.{u} (Fin n)) R) := by
  classical
  let T := Triangularization.upperTriangularGroup k n
  let e := Triangularization.upperTriangularGroupPointsIso k n
  letI : Group.IsSolvable ((groupPointsFunctor k).obj T.val |>.obj R) :=
    split_solvable_points (Triangularization.upperTriangularSplitSolvable k n T e) R
  exact Group.isSolvable_of_isSolvable_injective
    (ConcreteCategory.bijective_of_isIso (e.inv.app R)).1

/-- In the standard matrix group, after moving the coordinate flag to the
given flag, its stabilizer admits an injective upper triangular point representation. -/
private theorem reduced_stabilizer_solvable [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n : ℕ} {v : Module.Basis (Fin n) k V} (F : FullFlagAction G v)
    (x : 𝟙_ (SchemeOver k) ⟶ F.flags.scheme)
    (O : Specs.SmoothOrbit.Presentation F.action x) (C : ReducedComponent O.stabilizer) :
    IsSolvable C.subgroup.group := by
  classical
  let B := FlagSchemes.liftedBasis v
  let ranks := fullFlagRanks n
  let charts := fun i ↦ (F.planes i).charts
  let jF := F.flags.inclusion
  let D := FlagIncidence.flagPresentation B ranks charts (fun i ↦ (F.planes i).families)
    (fun i ↦ (F.planes i).affineComparison)
  obtain ⟨w₀, hw₀⟩ :=
    (D.factor_iff_zero _ (x ≫ jF)).mpr ((F.flags.factor_iff_zero _ _).mp ⟨x, rfl⟩)
  let w : 𝟙_ (SchemeOver k) ⟶ FlagIncidence.flagScheme B ranks charts := w₀
  let jD := FlagIncidence.flagInclusion B ranks charts
  have hw : w ≫ jD = x ≫ jF := hw₀
  have hdim : Module.finrank k V = n := by simp [Module.finrank_eq_card_basis v]
  have hr (i : Fin (n - 1)) : ranks i ≤ Module.finrank k V :=
    hdim.symm ▸ fullFlagRanks_le n i
  let M := (StandardGroups.generalLinearGroup k (ULift.{u} (Fin n))).val
  let E := StandardGroups.generalLinearGroupPointsIso k (ULift.{u} (Fin n))
  let A := FlagIncidence.intrinsicFlagAction B ranks charts
  obtain ⟨z, hz, htrans⟩ := FlagIncidence.localFlagTransitivity B ranks charts
    (fullFlagRanks_strictMono n).monotone hr n v
  obtain ⟨S, a, d, ha, hs, hd⟩ := htrans _ w (IsLocalRing.closedPoint k)
  letI : IsIso a := isIso_point_openImmersion a ha hs
  let t : 𝟙_ (SchemeOver k) ⟶ M.X := inv a ≫ d
  have hwt : w = prod.lift t (FlagSchemes.toBasePoint _ ≫ z) ≫ A.onFlags := by
    have e := congrArg (inv a ≫ ·) hd
    simp only [prod.comp_lift_assoc, IsIso.inv_hom_id_assoc] at e
    change prod.lift t (inv a ≫ (testSpec k).map
      (CommAlgCat.ofHom (Algebra.ofId k S)).op ≫ z) ≫ A.onFlags = w at e
    let r := (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k S)).op
    rw [← Category.assoc (f := inv a) (g := r), hom_toBase_eq (inv a ≫ r)] at e
    exact e.symm
  let R := CommAlgCat.of k k
  let P := (testSpec k).obj (op R)
  let Z := closedSubgroupAlgebraicGroup
    (G := closedSubgroupAlgebraicGroup O.stabilizer) C.subgroup
  let K := subgroupOfSubgroup O.stabilizer C.subgroup
  let tR : Points M.X R := toUnit P ≫ t
  let q : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R := E.hom.app R tR
  let φ : Points Z.val.X R →* Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R :=
    (F.matrixPoints.hom.app R).hom.comp
      ((IsMonHom.monoidHom F.representation.hom.hom P).comp
        (IsMonHom.monoidHom K.inclusion.hom.hom P))
  have hφ (b : Points Z.val.X R) :
      q⁻¹ * φ b * q ∈ Specs.Triangularization.upperTriangular (ULift.{u} (Fin n)) R := by
    let f : Points G.val.X R := b ≫ K.inclusion.hom.hom
    let g : Points M.X R := E.inv.app R (φ b)
    have hg : (E.hom.app R).hom g = φ b := by
      exact congrArg (fun h : (Specs.StandardGroups.generalLinearPoints k _).obj R ⟶
        (Specs.StandardGroups.generalLinearPoints k _).obj R ↦ h (φ b)) (E.inv_hom_id_app R)
    have hfix : Stabilizes F.action.smul x f := by
      apply (O.representsStabilizer P f).mpr
      refine ⟨b ≫ C.subgroup.inclusion.hom.hom, ?_⟩
      change (b ≫ C.subgroup.inclusion.hom.hom) ≫ O.stabilizer.inclusion.hom.hom =
        b ≫ (C.subgroup.inclusion.hom.hom ≫ O.stabilizer.inclusion.hom.hom)
      exact Category.assoc _ _ _
    have hfix' : prod.lift (f ≫ F.representation.hom.hom) (toUnit P ≫ x) ≫
        F.flagAction.onFlags = toUnit P ≫ x := by
      change lift f (toUnit P ≫ x) ≫ F.action.smul = _ at hfix
      rw [F.action_eq] at hfix
      exact hfix
    let xP := toUnit P ≫ x
    let wP := toUnit P ≫ w
    have hwP : wP ≫ jD = xP ≫ jF := by simp only [wP, xP, Category.assoc, hw]
    have hplanes (i : Fin (n - 1)) :
        (Specs.FlagIncidence.productPlanes ranks B charts
          ((prod.lift (f ≫ F.representation.hom.hom) xP ≫ F.flagAction.onFlags) ≫ jF) i).toSubmodule =
        (Specs.FlagIncidence.productPlanes ranks B charts (xP ≫ jF) i).toSubmodule.map
          (Specs.FlagIncidence.matrixTransport B R (φ b)).toLinearMap := by
      rw [Category.assoc, F.flagAction.restricts, prod.lift_map_assoc, Category.comp_id,
        F.flagAction.transport, prod.lift_snd, prod.lift_fst]
      rfl
    have hwfix : prod.lift g wP ≫ A.onFlags = wP := by
      apply flags_eq_of_planes B ranks charts
      intro i
      change (Specs.FlagIncidence.productPlanes ranks B charts
        ((prod.lift g wP ≫ FlagIncidence.flagAction B ranks charts) ≫ jD) i).toSubmodule =
        (Specs.FlagIncidence.productPlanes ranks B charts (wP ≫ jD) i).toSubmodule
      rw [flagAction_plane]
      change (Specs.FlagIncidence.productPlanes ranks B charts (wP ≫ jD) i).toSubmodule.map
        (Specs.FlagIncidence.matrixTransport B R ((E.hom.app R).hom g)).toLinearMap = _
      rw [hg, hwP, ← hplanes i, show prod.lift (f ≫ F.representation.hom.hom) xP ≫
        F.flagAction.onFlags = xP from hfix']
    have hwtP : wP = prod.lift tR (FlagSchemes.toBasePoint P ≫ z) ≫ A.onFlags := by
      have hb : toUnit P ≫ FlagSchemes.toBasePoint (𝟙_ (SchemeOver k)) ≫ z =
          FlagSchemes.toBasePoint P ≫ z := by
        rw [← Category.assoc, hom_toBase_eq (toUnit P ≫ FlagSchemes.toBasePoint (𝟙_ (SchemeOver k)))]
      simp only [wP, hwt, prod.comp_lift_assoc, tR, hb]
    rw [hwtP] at hwfix
    have hh := (conjugate_fixes_iff A.onFlags (A.one P) (A.mul P) g tR _).mp hwfix
    have hz' := (coordinateFlag_fixed v ranks charts hr z hz R (tR⁻¹ * g * tR)).mp
      (by rw [orbit_apply]; exact hh)
    intro i j hij
    have hji : j.down.val < i.down.val := hij
    let l : Fin (n - 1) := ⟨i.down.val - 1, by have := i.down.isLt; omega⟩
    have hl : ranks l = i.down.val := by
      change i.down.val - 1 + 1 = i.down.val
      omega
    have hz'' := hz' l i j (hl.symm ▸ hji) hl.le
    change ((E.hom.app R).hom (tR⁻¹ * g * tR)).val i j = 0 at hz''
    change (q⁻¹ * φ b * q).val i j = 0
    simpa only [map_mul, map_inv, hg, q] using hz''
  let ψ : Points Z.val.X R →* Specs.Triangularization.upperTriangular (ULift.{u} (Fin n)) R :=
    ((MulAut.conj q⁻¹).toMonoidHom.comp φ).codRestrict _ (fun b ↦ by
      change q⁻¹ * φ b * (q⁻¹)⁻¹ ∈ _
      rw [inv_inv]
      exact hφ b)
  have hinj : Function.Injective ψ := by
    haveI := K.isClosedImmersion
    haveI := F.faithful
    haveI : Mono K.inclusion.hom.hom := Over.mono_of_mono_left _
    haveI : Mono F.representation.hom.hom := Over.mono_of_mono_left _
    intro p s h
    have e := congrArg Subtype.val h
    change q⁻¹ * φ p * q = q⁻¹ * φ s * q at e
    have e' : φ p = φ s := mul_left_cancel (mul_right_cancel e)
    exact (cancel_mono K.inclusion.hom.hom).mp ((cancel_mono F.representation.hom.hom).mp
      ((ConcreteCategory.bijective_of_isIso (F.matrixPoints.hom.app R)).1 e'))
  letI := upper_triangular_points_solvable n R
  let m : rationalSections Z.val →* Points Z.val.X R :=
    { toFun a := toUnit P ≫ a
      map_one' := MonObj.comp_one _
      map_mul' _ _ := MonObj.comp_mul _ _ _ }
  haveI : IsIso (toUnit P) := by
    have e := (affineBaseTerminal k).uniqueUpToIso (isTerminalTensorUnit (C := SchemeOver k))
    rw [toUnit_unique (toUnit P) e.hom]
    infer_instance
  have hsolv := Group.isSolvable_of_isSolvable_injective
    (f := ψ.comp m) (hinj.comp (fun _ _ h ↦ (cancel_epi (toUnit P)).mp h))
  exact (solvable_iff_sections Z C.smooth C.connected).mpr hsolv

theorem closedFlagStabilizerIsBorel_conditional
    (fixed : Specs.BorelFixedPoint.OverAlgClosed.{u}) (split : Specs.BorelFixedPoint.Split.{u}) :
    ClosedFlagStabilizerIsBorel.{u} := by
  intro k V _ _ _ _ _ G hs hc n v F x O hO
  obtain ⟨C⟩ := EquivariantUnipotentSeries.exists_smooth_identity_component
    (closedSubgroupAlgebraicGroup O.stabilizer)
  have hC : IsSmoothConnectedSolvable (subgroupOfSubgroup O.stabilizer C.subgroup) :=
    ⟨C.smooth, C.connected, reduced_stabilizer_solvable F x O C⟩
  obtain ⟨B, hB⟩ := borelExists_conditional fixed split G hs hc
  obtain ⟨g, hg⟩ := conjugate_in_reduced_stabilizer F.action x O F.projective.proper hO
    fixed B hB.1 C
  have hb := borel_conjugate g hB
  exact ⟨C.subgroup, reducedComponent_spec C, borel_of_containing_borel hb hC hg⟩

theorem borelsConjugate_conditional
    (fixed : Specs.BorelFixedPoint.OverAlgClosed.{u}) (split : Specs.BorelFixedPoint.Split.{u}) :
    BorelsConjugate.{u} := by
  intro k _ _ G hs hc B₁ B₂ hB₁ hB₂
  obtain ⟨n, v, F, x, O, hO⟩ := closedFlagOrbitExists_conditional fixed split G hs hc
  obtain ⟨C⟩ := EquivariantUnipotentSeries.exists_smooth_identity_component
    (closedSubgroupAlgebraicGroup O.stabilizer)
  have hC : IsSmoothConnectedSolvable (subgroupOfSubgroup O.stabilizer C.subgroup) :=
    ⟨C.smooth, C.connected, reduced_stabilizer_solvable F x O C⟩
  obtain ⟨g₁, h₁⟩ := conjugate_in_reduced_stabilizer F.action x O F.projective.proper hO
    fixed B₁ hB₁.1 C
  obtain ⟨g₂, h₂⟩ := conjugate_in_reduced_stabilizer F.action x O F.projective.proper hO
    fixed B₂ hB₂.1 C
  have i₁ := (borel_conjugate g₁ hB₁).2 _ hC h₁
  have i₂ := (borel_conjugate g₂ hB₂).2 _ hC h₂
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso (subgroupOf_trans h₁ i₂) (subgroupOf_trans h₂ i₁)
  refine ⟨g₂⁻¹ * g₁, e, ?_⟩
  have h₀ := congrArg (fun f : B₁.group ⟶ G.val ↦ f.hom.hom) he
  change e.hom.hom.hom ≫ (B₂.inclusion.hom.hom ≫ (conjugation g₂).hom.hom) =
    B₁.inclusion.hom.hom ≫ (conjugation g₁).hom.hom at h₀
  rw [← Category.assoc] at h₀
  let a : B₁.group.X ⟶ G.val.X := e.hom.hom.hom ≫ B₂.inclusion.hom.hom
  change a ≫ (conjugation g₂).hom.hom = _ at h₀
  have h := congrArg (· ≫ (conjugation g₂⁻¹).hom.hom) h₀
  have hcancel : conjugation g₂ ≫ conjugation g₂⁻¹ = 𝟙 G.val :=
    (conjugationIso g₂).hom_inv_id
  rw [Category.assoc, ← Grp.comp_hom_hom, hcancel] at h
  change a ≫ 𝟙 _ = _ at h
  rw [Category.comp_id, conjugation_apply, conjugation_apply, GrpObj.comp_inv] at h
  let c₁ : B₁.group.X ⟶ G.val.X := toUnit B₁.group.X ≫ g₁
  let c₂ : B₁.group.X ⟶ G.val.X := toUnit B₁.group.X ≫ g₂
  change a = c₂⁻¹ * (c₁ * B₁.inclusion.hom.hom * c₁⁻¹) * (c₂⁻¹)⁻¹ at h
  change a = _
  rw [MonObj.comp_mul, GrpObj.comp_inv]
  change a = (c₂⁻¹ * c₁) * B₁.inclusion.hom.hom * (c₂⁻¹ * c₁)⁻¹
  rw [h]
  group

end

end LinearAlgebraicGroups.GeometricBorelConjugacy

universe v8_closure_80d7de90c34976d9_u0
theorem _root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists» : _root_.«LinearAlgebraicGroups».«Specs».«GeometricBorelConjugacy».«BorelExists».{v8_closure_80d7de90c34976d9_u0} :=
  @_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelExists_conditional».{v8_closure_80d7de90c34976d9_u0} (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«overAlgClosed».{v8_closure_80d7de90c34976d9_u0}) (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«split».{v8_closure_80d7de90c34976d9_u0})
theorem _root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate» : _root_.«LinearAlgebraicGroups».«Specs».«GeometricBorelConjugacy».«BorelsConjugate».{v8_closure_80d7de90c34976d9_u0} :=
  @_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«borelsConjugate_conditional».{v8_closure_80d7de90c34976d9_u0} (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«overAlgClosed».{v8_closure_80d7de90c34976d9_u0}) (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«split».{v8_closure_80d7de90c34976d9_u0})
theorem _root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists» : _root_.«LinearAlgebraicGroups».«Specs».«GeometricBorelConjugacy».«ClosedFlagOrbitExists».{v8_closure_80d7de90c34976d9_u0} :=
  @_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagOrbitExists_conditional».{v8_closure_80d7de90c34976d9_u0} (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«overAlgClosed».{v8_closure_80d7de90c34976d9_u0}) (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«split».{v8_closure_80d7de90c34976d9_u0})
theorem _root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel» : _root_.«LinearAlgebraicGroups».«Specs».«GeometricBorelConjugacy».«ClosedFlagStabilizerIsBorel».{v8_closure_80d7de90c34976d9_u0} :=
  @_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«closedFlagStabilizerIsBorel_conditional».{v8_closure_80d7de90c34976d9_u0} (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«overAlgClosed».{v8_closure_80d7de90c34976d9_u0}) (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«split».{v8_closure_80d7de90c34976d9_u0})
theorem _root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel» : _root_.«LinearAlgebraicGroups».«Specs».«GeometricBorelConjugacy».«TorusContainedInBorel».{v8_closure_80d7de90c34976d9_u0} :=
  @_root_.«LinearAlgebraicGroups».«GeometricBorelConjugacy».«torusContainedInBorel_conditional».{v8_closure_80d7de90c34976d9_u0} (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«overAlgClosed».{v8_closure_80d7de90c34976d9_u0}) (@_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«split».{v8_closure_80d7de90c34976d9_u0})
