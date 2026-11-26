import Specs.LinearAlgebraicGroups.Affine.Stabilizers
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import LinearAlgebraicGroups.Affine.FixedPointSchemes
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

variable {k : Type u} [Field k] {G H : Specs.GroupScheme k} {X T : SchemeOver k}

private theorem mono_over {Y Z : SchemeOver k} (j : Y ⟶ Z) (h : IsClosedImmersion j.left) :
    Mono j :=
  (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))

/-- A closed locus whose families are subgroups inherits the group structure. -/
private theorem closedSubgroupOfLocus (P : ∀ T : SchemeOver k, Subgroup (T ⟶ G.X))
    {Z : SchemeOver k} (j : Z ⟶ G.X) (hj : IsClosedImmersion j.left)
    (hP : ∀ T g, g ∈ P T ↔ ∃ z : T ⟶ Z, z ≫ j = g) :
    ∃ S : Specs.ClosedSubgroup G, RepresentsSubgroup S (fun T g ↦ g ∈ P T) := by
  have : Mono j := mono_over j hj
  have natural {U V : SchemeOver k} (f : U ⟶ V) (g : V ⟶ G.X) (hg : g ∈ P V) :
      f ≫ g ∈ P U := by
    obtain ⟨z, rfl⟩ := (hP _ _).mp hg
    exact (hP _ _).mpr ⟨f ≫ z, Category.assoc ..⟩
  let F : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u} :=
    { obj := fun U ↦ GrpCat.of (P U.unop)
      map := fun f ↦ GrpCat.ofHom
        { toFun := fun g ↦ ⟨f.unop ≫ g.val, natural f.unop _ g.property⟩
          map_one' := Subtype.ext (MonObj.comp_one _)
          map_mul' := fun g h ↦ Subtype.ext (MonObj.comp_mul _ _ _) }
      map_id := fun U ↦ GrpCat.hom_ext <| MonoidHom.ext fun g ↦ Subtype.ext (Category.id_comp _)
      map_comp := fun f g ↦ GrpCat.hom_ext <| MonoidHom.ext fun a ↦ Subtype.ext (Category.assoc ..) }
  let e : (F ⋙ forget _).RepresentableBy Z :=
    { homEquiv := Equiv.ofBijective
        (fun z ↦ ⟨z ≫ j, (hP _ _).mpr ⟨z, rfl⟩⟩)
        ⟨fun _ _ h ↦ (cancel_mono j).mp (congrArg Subtype.val h),
          fun g ↦ by
            obtain ⟨z, hz⟩ := (hP _ _).mp g.property
            exact ⟨z, Subtype.ext hz⟩⟩
      homEquiv_comp := fun f z ↦ Subtype.ext (Category.assoc ..) }
  let := GrpObj.ofRepresentableBy Z F e
  have eq {U : SchemeOver k} (p : P U) : e.homEquiv.symm p ≫ j = p.val :=
    congrArg Subtype.val (e.homEquiv.apply_symm_apply p)
  let S : Specs.GroupScheme k := Grp.mk Z
  let inc : S ⟶ G := Grp.homMk'' j
    (show e.homEquiv.symm (1 : P _) ≫ j = η[G.X] by
      rw [eq]
      exact (MonObj.one_eq_one (M := G.X)).symm)
    (show e.homEquiv.symm (e.homEquiv (fst Z Z) * e.homEquiv (snd Z Z)) ≫ j =
        (j ⊗ₘ j) ≫ μ[G.X] by
      rw [eq]
      change ((fst Z Z ≫ j) * (snd Z Z ≫ j)) = _
      rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp])
  exact ⟨⟨S, inc, hj⟩, hP⟩

private def orbitMap {M : SchemeOver k} (a : M ⊗ X ⟶ X) (x : 𝟙_ (SchemeOver k) ⟶ X) : M ⟶ X :=
  lift (𝟙 M) (toUnit M ≫ x) ≫ a

private theorem stabilizes_iff_eq {M : SchemeOver k} (a : M ⊗ X ⟶ X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (g : T ⟶ M) : Stabilizes a x g ↔ g ≫ orbitMap a x = g ≫ toUnit M ≫ x := by
  rw [Stabilizes, orbitMap, comp_lift_assoc, Category.comp_id]
  simp only [← Category.assoc g, comp_toUnit]

theorem stabilizerScheme : Specs.StabilizerScheme.{u} := by
  intro k _ G X act x sep _ _
  let f := orbitMap act.smul x
  let g := toUnit G.X ≫ x
  let P (T : SchemeOver k) : Subgroup (T ⟶ G.X) :=
    { carrier := {p | Stabilizes act.smul x p}
      one_mem' := by
        change (1 : T ⟶ G.X) • (toUnit T ≫ x) = _
        exact one_smul _ _
      mul_mem' := fun {p q} hp hq ↦ by
        change p • (toUnit T ≫ x) = _ at hp
        change q • (toUnit T ≫ x) = _ at hq
        change (p * q) • (toUnit T ≫ x) = _
        rw [mul_smul, hq, hp]
      inv_mem' := fun {p} hp ↦ by
        change p • (toUnit T ≫ x) = _ at hp
        change p⁻¹ • (toUnit T ≫ x) = _
        exact inv_smul_eq_iff.mpr hp.symm }
  refine closedSubgroupOfLocus P (equalizer.ι f g) inferInstance fun T p ↦ ?_
  change Stabilizes act.smul x p ↔ _
  rw [stabilizes_iff_eq]
  refine ⟨fun h ↦ ⟨equalizer.lift p h, equalizer.lift_ι _ _⟩, ?_⟩
  rintro ⟨z, rfl⟩
  exact congrArg (z ≫ ·) (equalizer.condition f g)

theorem linearSubspaceStabilizer : Specs.LinearSubspaceStabilizer.{u} := by
  intro R _ p q g
  let W := Specs.firstBlock R p q
  have block (a : ((Fin p ⊕ Fin q) → R) →ₗ[R] ((Fin p ⊕ Fin q) → R)) :
      W.map a ≤ W ↔
        ∀ (i : Fin p) (j : Fin q), a (Pi.single (.inl i) 1) (.inr j) = 0 := by
    rw [Submodule.map_le_iff_le_comap]
    constructor
    · intro h i j
      have hv : Pi.single (.inl i) 1 ∈ W := fun l ↦ Pi.single_eq_of_ne (by simp) _
      exact h hv j
    · intro h v hv
      change ∀ j : Fin q, a v (.inr j) = 0
      intro j
      have v_eq : (∑ i : Fin p, v (.inl i) •
          (Pi.single (.inl i) 1 : (Fin p ⊕ Fin q) → R)) = v := by
        ext (i | i)
        · simp [Pi.single_apply]
        · simp [show v (.inr i) = 0 from hv i]
      rw [← v_eq, map_sum, Finset.sum_apply]
      simp [h]
  change W.map g.toLinearMap = W ↔
    (∀ (i : Fin p) (j : Fin q), g.toLinearMap (Pi.single (.inl i) 1) (.inr j) = 0) ∧
    (∀ (i : Fin p) (j : Fin q), g.symm.toLinearMap (Pi.single (.inl i) 1) (.inr j) = 0)
  rw [← block g.toLinearMap, ← block g.symm.toLinearMap]
  constructor
  · intro h
    refine ⟨h.le, ?_⟩
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    have : v ∈ W.map g.toLinearMap := h.symm ▸ hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp this
    simpa using hw
  · rintro ⟨hf, hr⟩
    refine le_antisymm hf fun v hv ↦ ?_
    exact Submodule.mem_map.mpr ⟨g.symm v, hr (Submodule.mem_map_of_mem hv), g.apply_symm_apply v⟩

open scoped TensorProduct in
theorem linearSubspaceStabilizerInBasis : Specs.LinearSubspaceStabilizerInBasis.{u} := by
  classical
  intro k _ V _ _ _ W
  obtain ⟨U, hU⟩ := W.exists_isCompl
  let bW := Module.finBasis k W
  let bU := Module.finBasis k U
  let b := (bW.prod bU).map (W.prodEquivOfIsCompl U hU)
  have hb (i : Fin (Module.finrank k W)) : b (.inl i) = (bW i : V) := by
    simp [b]
  have hW : Submodule.span k (Set.range (fun i : Fin (Module.finrank k W) ↦ b (.inl i))) = W := by
    simp_rw [hb]
    change Submodule.span k (Set.range (W.subtype ∘ bW)) = W
    rw [Set.range_comp W.subtype bW, ← Submodule.map_span, bW.span_eq, Submodule.map_subtype_top]
  refine ⟨_, _, b, fun R _ _ ↦ ?_⟩
  let e := (b.baseChange R).equivFun
  have hvec (i : Fin (Module.finrank k W)) :
      e (b.baseChange R (.inl i)) = Pi.single (.inl i) 1 := by
    ext j
    change (b.baseChange R).equivFun ((b.baseChange R) (.inl i)) j = _
    rw [Module.Basis.equivFun_self]
    by_cases h : j = .inl i
    · simp [h]
    · simp [h, Ne.symm h]
  have hblock : (W.baseChange R).map e.toLinearMap = Specs.firstBlock R _ _ := by
    rw [← congrArg (fun S : Submodule k V ↦ S.baseChange R) hW,
      Submodule.baseChange_span, Submodule.map_span]
    have hset : e.toLinearMap '' (TensorProduct.mk k R V 1 ''
        Set.range (fun i : Fin (Module.finrank k W) ↦ b (.inl i))) =
        Set.range (fun i : Fin (Module.finrank k W) ↦
          (Pi.single (.inl i) 1 : (Fin (Module.finrank k W) ⊕ Fin (Module.finrank k U)) → R)) := by
      simp only [← Set.range_comp]
      congr 1
      funext i
      exact (congrArg e (b.baseChange_apply R (.inl i))).symm.trans (hvec i)
    rw [hset]
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨i, rfl⟩ j
      simp
    · intro v hv
      have e_v : (∑ i : Fin (Module.finrank k W), v (.inl i) •
          (Pi.single (.inl i) 1 : (Fin (Module.finrank k W) ⊕ Fin (Module.finrank k U)) → R)) = v := by
        ext (i | j)
        · simp [Pi.single_apply]
        · simp [show v (.inr j) = 0 from hv j]
      rw [← e_v]
      exact Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨hblock, fun g ↦ ?_⟩
  let a := (e.symm.trans g).trans e
  have hm : (W.baseChange R).map g.toLinearMap = W.baseChange R ↔
      (Specs.firstBlock R _ _).map a.toLinearMap = Specs.firstBlock R _ _ := by
    rw [← hblock, ← Submodule.map_comp]
    have eq : a.toLinearMap.comp e.toLinearMap = e.toLinearMap.comp g.toLinearMap := by
      ext v
      simp [a]
    rw [eq, Submodule.map_comp]
    exact (Submodule.map_injective_of_injective e.injective).eq_iff.symm
  rw [hm]
  have hf (i : Fin (Module.finrank k W)) :
      a (Pi.single (.inl i) 1) = e (g (b.baseChange R (.inl i))) := by
    rw [← hvec]
    simp [a]
  have hr (i : Fin (Module.finrank k W)) :
      a.symm (Pi.single (.inl i) 1) = e (g.symm (b.baseChange R (.inl i))) := by
    rw [← hvec]
    simp [a]
  simpa only [hf, hr] using linearSubspaceStabilizer R _ _ a

private theorem fieldSpecMap_surjective (K : Type u) [Field K] [Algebra k K] :
    Surjective (fieldSpecMap k K) :=
  ⟨fun _ ↦ ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩

theorem geometricPointTest : Specs.GeometricPointTest.{u} := by
  intro k K _ _ _ _ X Y f g geo finiteX sep finiteY
  refine ⟨fun h p ↦ by rw [h], fun h ↦ ?_⟩
  let F := baseChange k K
  let e := fieldSpecMap k K
  have he : Surjective e := fieldSpecMap_surjective K
  have hf : Flat e := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    rw [Flat.SpecMap_iff]
    let : Algebra k K := (CommRingCat.ofHom (algebraMap k K)).hom.toAlgebra
    exact Module.Flat.of_free (R := k) (M := K)
  have : QuasiCompact e := inferInstanceAs (QuasiCompact (Spec.map _))
  have faithful : F.Faithful := inferInstanceAs ((Over.pullback e).Faithful)
  apply faithful.map_injective
  apply Over.OverMorphism.ext
  have hp (Z : SchemeOver k) := IsPullback.of_hasPullback Z.hom e
  have hr : IsReduced (F.obj X).left := GeometricallyReduced.geometrically_isReduced _ _ _ (hp X)
  have hX : LocallyOfFiniteType (F.obj X).hom :=
    MorphismProperty.of_isPullback (hp X) finiteX
  have hY : LocallyOfFiniteType (F.obj Y).hom :=
    MorphismProperty.of_isPullback (hp Y) finiteY
  have hs : IsSeparated (F.obj Y).hom := MorphismProperty.of_isPullback (hp Y) sep
  have hcomp : LocallyOfFiniteType ((F.map f).left ≫ (F.obj Y).hom) := Over.w (F.map f) ▸ hX
  refine ext_of_apply_eq (F.obj Y).hom Set.univ isOpen_univ.isLocallyClosed dense_univ (fun x _ hx ↦ ?_) ?_
  · let p : 𝟙_ (SchemeOver K) ⟶ F.obj X :=
      Over.homMk (pointOfClosedPoint (F.obj X).hom x hx) (pointOfClosedPoint_comp _ _ _)
    have heq : p.left ≫ (F.map f).left = p.left ≫ (F.map g).left :=
      congrArg (fun m ↦ m.left) (h p)
    have hx' : p.left (IsLocalRing.closedPoint K) = x := pointOfClosedPoint_apply _ _ _ _
    have e' := congrArg (fun m : Spec (.of K) ⟶ (F.obj Y).left ↦ m (IsLocalRing.closedPoint K)) heq
    change (F.map f).left (p.left (IsLocalRing.closedPoint K)) =
      (F.map g).left (p.left (IsLocalRing.closedPoint K)) at e'
    rwa [hx'] at e'
  · rw [Over.w, Over.w]

theorem geometricClosedImmersionTest : Specs.GeometricClosedImmersionTest.{u} := by
  intro k K _ _ _ _ X Y Z f i geo ft hi
  let F := baseChange k K
  constructor
  · rintro ⟨g, rfl⟩ p
    exact ⟨p ≫ F.map g, by simp [F]⟩
  · intro h
    let W := pullback f i
    let q : W ⟶ X := pullback.fst f i
    let b := fieldSpecMap k K
    have hb : Surjective b := fieldSpecMap_surjective K
    have hq := IsPullback.of_hasPullback f i
    have hq' := hq.map F
    have hiq : IsClosedImmersion q.left :=
      MorphismProperty.of_isPullback (hq.map (Over.forget _)).flip hi
    have hibc : IsClosedImmersion (F.map q).left := by
      have hb₁ : (F.map q).left ≫ pullback.fst X.hom b = pullback.fst W.hom b ≫ q.left :=
        pullback.lift_fst _ _ _
      have hb₂ : (F.map q).left ≫ pullback.snd X.hom b = pullback.snd W.hom b :=
        pullback.lift_snd _ _ _
      have outer : IsPullback ((F.map q).left ≫ pullback.snd X.hom b)
          (pullback.fst W.hom b) b (q.left ≫ X.hom) := by
        rw [hb₂, Over.w q]
        exact (IsPullback.of_hasPullback W.hom b).flip
      exact MorphismProperty.of_isPullback
        (outer.of_right hb₁ (IsPullback.of_hasPullback X.hom b).flip).flip hiq
    have hft : LocallyOfFiniteType (F.obj X).hom :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback X.hom b) ft
    have jac : JacobsonSpace ↥(F.obj X).left := LocallyOfFiniteType.jacobsonSpace (F.obj X).hom
    have hdense : Dense (closedPoints (F.obj X).left) := by
      rw [dense_iff_closure_eq]
      simpa using JacobsonSpace.closure_inter_closedPoints_eq_closure
        (X := ↥(F.obj X).left) isOpen_univ.isLocallyClosed
    have hmem : closedPoints (F.obj X).left ⊆ Set.range (F.map q).left := by
      intro x hx
      let p : 𝟙_ (SchemeOver K) ⟶ F.obj X :=
        Over.homMk (pointOfClosedPoint (F.obj X).hom x hx) (pointOfClosedPoint_comp _ _ _)
      obtain ⟨z, hz⟩ := h p
      let y := hq'.lift p z hz.symm
      have eq := hq'.lift_fst p z hz.symm
      have eq' : y.left ≫ (F.map q).left = p.left := congrArg (fun m ↦ m.left) eq
      have hx' := pointOfClosedPoint_apply (F.obj X).hom x hx (IsLocalRing.closedPoint K)
      refine ⟨y.left (IsLocalRing.closedPoint K), ?_⟩
      exact (congrArg (fun m : Spec (.of K) ⟶ (F.obj X).left ↦ m (IsLocalRing.closedPoint K)) eq').trans hx'
    have hsurj : Surjective (F.map q).left := by
      refine ⟨Set.range_eq_univ.mp ?_⟩
      have hclosed := (F.map q).left.isClosedEmbedding.isClosed_range
      exact hclosed.closure_eq.symm.trans ((hdense.mono hmem).closure_eq)
    let r := pullback.fst X.hom b
    have hr : Surjective r := inferInstanceAs (Surjective (pullback.fst _ _))
    have hs : Surjective q.left := by
      constructor
      intro x
      obtain ⟨x', hx'⟩ := hr.surj x
      obtain ⟨w, hw⟩ := hsurj.surj x'
      refine ⟨pullback.fst W.hom b w, ?_⟩
      have eq : (F.map q).left ≫ r = pullback.fst W.hom b ≫ q.left :=
        pullback.lift_fst _ _ _
      rw [← hx', ← hw]
      exact (congrArg (fun m : (F.obj W).left ⟶ X.left ↦ m w) eq).symm
    have red : IsReduced X.left :=
      GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian X.hom
    have : IsIso ((Over.forget (Spec (CommRingCat.of k))).map q) :=
      isIso_of_isClosedImmersion_of_surjective q.left
    have : IsIso q := isIso_of_reflects_iso q (Over.forget _)
    refine ⟨inv q ≫ pullback.snd f i, ?_⟩
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

private theorem comp_conjugateFamily (i : H ⟶ G) (g : T ⟶ G.X)
    {U : SchemeOver k} (f : U ⟶ H.X ⊗ T) :
    f ≫ conjugateFamily i g =
      (f ≫ snd H.X T ≫ g) * (f ≫ fst H.X T ≫ i.hom.hom) * (f ≫ snd H.X T ≫ g)⁻¹ := by
  simp [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv]

private theorem conjugateLe_iff (i : H ⟶ G) (g : T ⟶ G.X) :
    ConjugateLe i g ↔
      ∀ (U : SchemeOver k) (t : U ⟶ T) (h : U ⟶ H.X),
        ∃ a : U ⟶ H.X, a ≫ i.hom.hom =
          (t ≫ g) * (h ≫ i.hom.hom) * (t ≫ g)⁻¹ := by
  constructor
  · rintro ⟨a, ha⟩ U t h
    refine ⟨lift h t ≫ a, ?_⟩
    simp only [Category.assoc, ha, comp_conjugateFamily, lift_fst_assoc, lift_snd_assoc]
  · intro h
    simpa [ConjugateLe, conjugateFamily] using h (H.X ⊗ T) (snd H.X T) (fst H.X T)

private theorem centralizes_iff (i : H ⟶ G) (g : T ⟶ G.X) :
    Centralizes i g ↔ ∀ (U : SchemeOver k) (t : U ⟶ T) (h : U ⟶ H.X),
      Commute (t ≫ g) (h ≫ i.hom.hom) := by
  constructor
  · intro eq U t h
    have c := congrArg (fun z ↦ lift h t ≫ z) eq
    simp only [comp_conjugateFamily, lift_fst_assoc, lift_snd_assoc] at c
    exact mul_inv_eq_iff_eq_mul.mp c
  · intro h
    exact mul_inv_eq_iff_eq_mul.mpr
      (h (H.X ⊗ T) (snd H.X T) (fst H.X T)).eq

theorem normalizesIff : Specs.NormalizesIff.{u} := by
  intro k _ G H i hi T g
  have : Mono i.hom.hom := mono_over _ hi
  constructor
  · rintro ⟨e, et, eh⟩
    refine ⟨⟨e.hom ≫ fst H.X T, Category.assoc .. |>.trans eh⟩, e.inv ≫ fst H.X T, ?_⟩
    have eit : e.inv ≫ snd H.X T = snd H.X T := by
      calc
        _ = e.inv ≫ e.hom ≫ snd H.X T := congrArg (e.inv ≫ ·) et.symm
        _ = _ := e.inv_hom_id_assoc _
    have key := congrArg (fun m ↦ e.inv ≫ m) eh
    simp only [comp_conjugateFamily, ← Category.assoc e.inv, eit] at key
    simp only [Iso.inv_hom_id, Category.id_comp] at key
    change ((e.inv ≫ fst H.X T) ≫ i.hom.hom) = conjugateFamily i g⁻¹
    calc
      _ = (snd H.X T ≫ g)⁻¹ * (snd H.X T ≫ g *
            ((e.inv ≫ fst H.X T) ≫ i.hom.hom) * (snd H.X T ≫ g)⁻¹) * (snd H.X T ≫ g) := by
        group
      _ = _ := by rw [← key]; simp [conjugateFamily, GrpObj.comp_inv]
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    let f := lift a (snd H.X T)
    let r := lift b (snd H.X T)
    have fs : f ≫ snd H.X T = snd H.X T := lift_snd _ _
    have rs : r ≫ snd H.X T = snd H.X T := lift_snd _ _
    have ff : f ≫ fst H.X T ≫ i.hom.hom = conjugateFamily i g := by simpa [f] using ha
    have rf : r ≫ fst H.X T ≫ i.hom.hom = conjugateFamily i g⁻¹ := by simpa [r] using hb
    have inv (s t : H.X ⊗ T ⟶ H.X ⊗ T) (p : T ⟶ G.X)
        (hs : s ≫ snd H.X T = snd H.X T) (ht : t ≫ snd H.X T = snd H.X T)
        (hsf : s ≫ fst H.X T ≫ i.hom.hom = conjugateFamily i p)
        (htf : t ≫ fst H.X T ≫ i.hom.hom = conjugateFamily i p⁻¹) :
        s ≫ t = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext
      · apply (cancel_mono i.hom.hom).mp
        rw [Category.assoc, Category.assoc s t, htf, comp_conjugateFamily,
          ← Category.assoc s, hs, hsf, Category.id_comp]
        simp only [conjugateFamily, GrpObj.comp_inv, inv_inv]
        group
      · simp only [Category.assoc, ht, hs, Category.id_comp]
    refine ⟨⟨f, r, inv f r g fs rs ff rf, inv r f g⁻¹ rs fs rf (by simpa using ff)⟩, fs, ff⟩

open private affineSpec quotientProjection factorsThrough_affineQuotient
  closedImmersion_over_affineSpec coefficientIdeal coefficientIdeal_le_ker
  overCoverObj overCoverMap factorsThrough_iff_cover whiskerLeft_pullback
  isIso_over_product_map from LinearAlgebraicGroups.Affine.FixedPointSchemes

/-- The coefficient ideal defines the locus where a whole affine family
factors through a given closed immersion. -/
private theorem affineFactorizationLocus {A B : TestAlgebra k} {D : SchemeOver k}
    (d : D ⟶ affineSpec A ⊗ affineSpec B) (hd : IsClosedImmersion d.left) :
    ∃ (Z : SchemeOver k) (j : Z ⟶ affineSpec B), IsClosedImmersion j.left ∧
      ∀ (C : TestAlgebra k) (x : affineSpec C ⟶ affineSpec B),
        (∃ t : affineSpec A ⊗ affineSpec C ⟶ D, t ≫ d = affineSpec A ◁ x) ↔
          ∃ y : affineSpec C ⟶ Z, y ≫ j = x := by
  classical
  let F := testSpec k
  let : F.Braided := braidedAlgSpec (R := CommRingCat.of k)
  let b := asIso (Functor.OplaxMonoidal.δ F (op A) (op B))
  have hb : IsClosedImmersion (d ≫ b.inv).left := IsClosedImmersion.comp d.left b.inv.left
  obtain ⟨I, e, he⟩ := closedImmersion_over_affineSpec (d ≫ b.inv) hb
  let basis := Module.Free.chooseBasis k A
  let J := coefficientIdeal basis I
  let q := F.map (quotientProjection J).op
  refine ⟨_, q, IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  intro C x
  let c := asIso (Functor.OplaxMonoidal.δ F (op A) (op C))
  let h := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x
  have hh : F.map h = x := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hc : c.hom ≫ (affineSpec A ◁ x) = F.map (op A ◁ h) ≫ b.hom := by
    change Functor.OplaxMonoidal.δ F (op A) (op C) ≫ _ = _ ≫
      Functor.OplaxMonoidal.δ F (op A) (op B)
    rw [Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory,
      Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory, ← hh]
    exact (prodComparison_natural_whiskerLeft F (A := op A) h).symm
  have he' : d = e.hom ≫ F.map (quotientProjection I).op ≫ b.hom := by
    have eq := congrArg (fun m ↦ m ≫ b.hom) he
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using eq
  rw [factorsThrough_affineQuotient]
  refine (Iff.trans ?_ (coefficientIdeal_le_ker basis I h.unop.hom).symm)
  have criterion := factorsThrough_affineQuotient I (F.map (op A ◁ h))
  rw [Functor.FullyFaithful.preimage_map] at criterion
  refine Iff.trans ?_ criterion
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨c.hom ≫ z ≫ e.hom, (cancel_mono b.hom).mp ?_⟩
    calc
      _ = c.hom ≫ z ≫ d := by simp only [Category.assoc, he', F]
      _ = _ := by rw [hz, hc]
  · rintro ⟨z, hz⟩
    refine ⟨c.inv ≫ z ≫ e.inv, ?_⟩
    rw [he']
    calc
      _ = c.inv ≫ (z ≫ F.map (quotientProjection I).op) ≫ b.hom := by simp
      _ = _ := by rw [hz, ← hc, Iso.inv_hom_id_assoc]

private theorem factorsThrough_iso {U U' V V' D : SchemeOver k}
    (e : U' ≅ U) (s : V' ≅ V) (d : D ⟶ V) (x : U ⟶ V) :
    (∃ y, y ≫ d = x) ↔ ∃ y, y ≫ (d ≫ s.inv) = e.hom ≫ x ≫ s.inv := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.hom ≫ y, by simp⟩
  · rintro ⟨y, hy⟩
    refine ⟨e.inv ≫ y, (cancel_mono s.inv).mp ?_⟩
    calc
      _ = e.inv ≫ (y ≫ d ≫ s.inv) := Category.assoc ..
      _ = _ := by rw [hy, Iso.inv_hom_id_assoc]

private theorem familyFactorization_iff_cover {A B D T : SchemeOver k}
    (d : D ⟶ A ⊗ B) [Mono d.left] (x : T ⟶ B) (cover : T.left.OpenCover) :
    (∃ t, t ≫ d = A ◁ x) ↔
      ∀ l : cover.I₀, ∃ t, t ≫ d = A ◁ (overCoverMap cover l ≫ x) := by
  rw [factorsThrough_iff_cover (cover.pullback₁ (snd A T).left)]
  apply forall_congr'
  intro l
  change cover.I₀ at l
  let U := overCoverObj cover l
  let f := overCoverMap cover l
  let pb : IsPullback (A ◁ f).left (snd A U).left (snd A T).left (cover.f l) :=
    (whiskerLeft_pullback (H := A) f).map (Over.forget _)
  let e : A ⊗ U ≅ overCoverObj (cover.pullback₁ (snd A T).left) l :=
    Over.isoMk pb.isoPullback (by
      rw [← Over.w (overCoverMap (cover.pullback₁ (snd A T).left) l), ← Category.assoc]
      change (pb.isoPullback.hom ≫ pullback.fst (snd A T).left (cover.f l)) ≫ _ = _
      rw [pb.isoPullback_hom_fst, Over.w])
  have he : e.hom ≫ overCoverMap (cover.pullback₁ (snd A T).left) l = A ◁ f :=
    Over.OverMorphism.ext pb.isoPullback_hom_fst
  have key := factorsThrough_iso e (Iso.refl (A ⊗ B)) d
    (overCoverMap (cover.pullback₁ (snd A T).left) l ≫ (A ◁ x))
  simp only [Iso.refl_inv, Category.comp_id, ← Category.assoc e.hom, he] at key
  simpa only [whiskerLeft_comp] using key

private theorem familyFactorizationLocus {A B D : SchemeOver k}
    [IsAffine A.left] [IsAffine B.left]
    (d : D ⟶ A ⊗ B) (hd : IsClosedImmersion d.left) :
    ∃ (Z : SchemeOver k) (j : Z ⟶ B), IsClosedImmersion j.left ∧
      ∀ (T : SchemeOver k) (x : T ⟶ B),
        (∃ t : A ⊗ T ⟶ D, t ≫ d = A ◁ x) ↔ ∃ y : T ⟶ Z, y ≫ j = x := by
  obtain ⟨P, ⟨eA⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (inferInstance : IsAffine A.left)
  obtain ⟨Q, ⟨eB⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (inferInstance : IsAffine B.left)
  let s := eA ⊗ᵢ eB
  have hd' : IsClosedImmersion (d ≫ s.inv).left := IsClosedImmersion.comp d.left s.inv.left
  obtain ⟨Z, j, hj, h⟩ := affineFactorizationLocus (d ≫ s.inv) hd'
  have hj' : IsClosedImmersion (j ≫ eB.hom).left := IsClosedImmersion.comp j.left eB.hom.left
  refine ⟨Z, j ≫ eB.hom, hj', fun T x ↦ ?_⟩
  have : Mono d.left := inferInstance
  have : Mono (j ≫ eB.hom).left := inferInstance
  let cover := T.left.affineOpenCover.openCover
  rw [familyFactorization_iff_cover d x cover, factorsThrough_iff_cover cover]
  apply forall_congr'
  intro l
  let U := overCoverObj cover l
  let f := overCoverMap cover l ≫ x
  have hU : IsAffine U.left := inferInstanceAs (IsAffine (Spec (T.left.affineOpenCover.X l)))
  obtain ⟨C, ⟨eU⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hU
  have eq : (eA ⊗ᵢ eU).hom ≫ (A ◁ f) ≫ s.inv =
      affineSpec P.unop ◁ (eU.hom ≫ f ≫ eB.inv) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [s, tensorIso]
    · simp [s, tensorIso]
  change (∃ t, t ≫ d = A ◁ f) ↔ ∃ y, y ≫ (j ≫ eB.hom) = f
  rw [factorsThrough_iso (eA ⊗ᵢ eU) s, eq, h C.unop, factorsThrough_iso eU eB]
  simp

private def conjugation (i : H ⟶ G) : H.X ⊗ G.X ⟶ G.X := conjugateFamily i (𝟙 G.X)

private theorem whisker_conjugation (i : H ⟶ G) (g : T ⟶ G.X) :
    (H.X ◁ g) ≫ conjugation i = conjugateFamily i g := by
  rw [conjugation, comp_conjugateFamily]
  simp [conjugateFamily]

theorem centralizerScheme : Specs.CentralizerScheme.{u} := by
  intro k _ G H
  let i := H.inclusion
  have : IsAffine G.1.X.left := G.2.1
  have : IsClosedImmersion i.hom.hom.left := H.isClosedImmersion
  have : IsAffine H.group.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have : IsSeparated G.1.X.hom := IsSeparated.of_isAffineHom _
  let f := conjugation i
  let g := fst H.group.X G.1.X ≫ i.hom.hom
  let d := equalizer.ι f g
  obtain ⟨Z, j, hj, h⟩ := familyFactorizationLocus d (inferInstanceAs (IsClosedImmersion d.left))
  let P (T : SchemeOver k) : Subgroup (T ⟶ G.1.X) :=
    { carrier := {p | Centralizes i p}
      one_mem' := (centralizes_iff i _).mpr fun U t h ↦ by simp [MonObj.comp_one]
      mul_mem' := fun {p q} hp hq ↦ (centralizes_iff i _).mpr fun U t h ↦ by
        rw [MonObj.comp_mul]
        exact ((centralizes_iff i p).mp hp U t h).mul_left ((centralizes_iff i q).mp hq U t h)
      inv_mem' := fun {p} hp ↦ (centralizes_iff i _).mpr fun U t h ↦ by
        rw [GrpObj.comp_inv]
        exact ((centralizes_iff i p).mp hp U t h).inv_left }
  refine closedSubgroupOfLocus P j hj fun T p ↦ ?_
  change Centralizes i p ↔ _
  rw [← h]
  have eq : Centralizes i p ↔ (H.group.X ◁ p) ≫ f = (H.group.X ◁ p) ≫ g := by
    simp [f, g, Centralizes, whisker_conjugation]
  rw [eq]
  refine ⟨fun hp ↦ ⟨equalizer.lift _ hp, equalizer.lift_ι _ _⟩, ?_⟩
  rintro ⟨t, ht⟩
  rw [← ht, Category.assoc, Category.assoc, equalizer.condition]

theorem normalizerScheme : Specs.NormalizerScheme.{u} := by
  intro k _ G H
  let i := H.inclusion
  have : IsAffine G.1.X.left := G.2.1
  have hi : IsClosedImmersion i.hom.hom.left := H.isClosedImmersion
  have : IsAffine H.group.X.left := isAffine_of_isAffineHom i.hom.hom.left
  let f := conjugation i
  let d := pullback.fst f i.hom.hom
  have hd : IsClosedImmersion d.left :=
    MorphismProperty.of_isPullback
      (((IsPullback.of_hasPullback f i.hom.hom).map (Over.forget _)).flip) hi
  obtain ⟨Z, j, hj, h⟩ := familyFactorizationLocus d hd
  have loci (T : SchemeOver k) (p : T ⟶ G.1.X) :
      ConjugateLe i p ↔ ∃ y : T ⟶ Z, y ≫ j = p := by
    rw [← h]
    constructor
    · rintro ⟨a, ha⟩
      have eq : (H.group.X ◁ p) ≫ f = a ≫ i.hom.hom :=
        (whisker_conjugation i p).trans ha.symm
      exact ⟨pullback.lift _ _ eq, pullback.lift_fst _ _ _⟩
    · rintro ⟨a, ha⟩
      refine ⟨a ≫ pullback.snd _ _, ?_⟩
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha]
      exact whisker_conjugation i p
  have hinv : IsIso (ι[G.1.X]).left := by
    have h : IsIso (ι[G.1.X]) := by
      refine ⟨⟨ι, ?_, ?_⟩⟩ <;> simpa only [Hom.inv_def, Category.id_comp] using
        (inv_inv (𝟙 G.1.X))
    exact inferInstanceAs (IsIso ((Over.forget _).map (ι[G.1.X])))
  let r := pullback.fst j (j ≫ ι[G.1.X])
  have hr : IsClosedImmersion r.left :=
    MorphismProperty.of_isPullback
      (((IsPullback.of_hasPullback j (j ≫ ι[G.1.X])).map (Over.forget _)).flip)
        (IsClosedImmersion.comp _ _)
  let P (T : SchemeOver k) : Subgroup (T ⟶ G.1.X) :=
    { carrier := {p | Normalizes i p}
      one_mem' := (normalizesIff k i hi _ _).mpr (by simp only [inv_one]; exact ⟨
        (conjugateLe_iff i _).mpr (fun U t h ↦ ⟨h, by simp [MonObj.comp_one]⟩),
        (conjugateLe_iff i _).mpr (fun U t h ↦ ⟨h, by simp [MonObj.comp_one]⟩)⟩)
      mul_mem' := fun {p q} hp hq ↦ by
        have mul {p q : T ⟶ G.1.X} (hp : ConjugateLe i p) (hq : ConjugateLe i q) :
            ConjugateLe i (p * q) := (conjugateLe_iff i _).mpr fun U t h ↦ by
          obtain ⟨a, ha⟩ := (conjugateLe_iff i q).mp hq U t h
          obtain ⟨b, hb⟩ := (conjugateLe_iff i p).mp hp U t a
          refine ⟨b, ?_⟩
          rw [hb, ha, MonObj.comp_mul]
          group
        obtain ⟨hp, hp'⟩ := (normalizesIff k i hi _ _).mp hp
        obtain ⟨hq, hq'⟩ := (normalizesIff k i hi _ _).mp hq
        exact (normalizesIff k i hi _ _).mpr ⟨mul hp hq, by simpa using mul hq' hp'⟩
      inv_mem' := fun {p} hp ↦ by
        obtain ⟨h₁, h₂⟩ := (normalizesIff k i hi _ _).mp hp
        exact (normalizesIff k i hi _ _).mpr ⟨h₂, by simpa using h₁⟩ }
  refine closedSubgroupOfLocus P (r ≫ j) (IsClosedImmersion.comp r.left j.left) fun T p ↦ ?_
  change Normalizes i p ↔ _
  rw [normalizesIff k i hi, loci, loci]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have eq : a ≫ j = b ≫ (j ≫ ι[G.1.X]) := by
      rw [ha, ← Category.assoc, hb, ← Hom.inv_def, inv_inv]
    exact ⟨pullback.lift a b eq, by rw [← Category.assoc, pullback.lift_fst, ha]⟩
  · rintro ⟨a, ha⟩
    refine ⟨⟨a ≫ r, ha⟩, a ≫ pullback.snd _ _, ?_⟩
    rw [Hom.inv_def, ← ha, Category.assoc, Category.assoc]
    have eq := pullback.condition (f := j) (g := j ≫ ι[G.1.X])
    have hh' : pullback.snd j (j ≫ ι[G.1.X]) ≫ j = r ≫ j ≫ ι[G.1.X] := by
      change pullback.snd j (j ≫ ι[G.1.X]) ≫ j = (r ≫ j)⁻¹
      change r ≫ j = (pullback.snd j (j ≫ ι[G.1.X]) ≫ j)⁻¹ at eq
      rw [eq, inv_inv]
    exact congrArg (a ≫ ·) hh'

section BaseChange

variable (K : Type u) [Field K] [Algebra k K]

private abbrev extensionAdj := Over.mapPullbackAdj (fieldSpecMap k K)

private theorem adjoint_factorization {A B : SchemeOver k} (j : A ⟶ B)
    {U : SchemeOver K} (x : U ⟶ (baseChange k K).obj B) :
    (∃ z, z ≫ (baseChange k K).map j = x) ↔
      ∃ z, z ≫ j = ((extensionAdj (k := k) K).homEquiv U B).symm x := by
  let adj := extensionAdj (k := k) K
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(adj.homEquiv U A).symm z, (adj.homEquiv_naturality_right_symm z j).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨adj.homEquiv U A z, (adj.homEquiv U B).symm.injective ?_⟩
    rw [adj.homEquiv_naturality_right_symm, Equiv.symm_apply_apply, hz]

private theorem prodComparison_inv_fst (A B : SchemeOver k) :
    (prodComparisonIso (baseChange k K) A B).inv ≫ (baseChange k K).map (fst A B) =
      fst ((baseChange k K).obj A) ((baseChange k K).obj B) := by
  rw [← CartesianMonoidalCategory.prodComparison_fst, ← prodComparisonIso_hom,
    Iso.inv_hom_id_assoc]

private theorem prodComparison_inv_snd (A B : SchemeOver k) :
    (prodComparisonIso (baseChange k K) A B).inv ≫ (baseChange k K).map (snd A B) =
      snd ((baseChange k K).obj A) ((baseChange k K).obj B) := by
  rw [← CartesianMonoidalCategory.prodComparison_snd, ← prodComparisonIso_hom,
    Iso.inv_hom_id_assoc]

private theorem adjoint_family {A B Y : SchemeOver k} (f : A ⊗ B ⟶ Y)
    {U : SchemeOver K} (x : U ⟶ (baseChange k K).obj B) :
    let F := baseChange k K
    let L := Over.map (fieldSpecMap k K)
    let adj := extensionAdj (k := k) K
    let b := lift (L.map (fst (F.obj A) U) ≫ adj.counit.app A) (L.map (snd (F.obj A) U))
    (adj.homEquiv (F.obj A ⊗ U) Y).symm
      ((F.obj A ◁ x) ≫ (prodComparisonIso F A B).inv ≫ F.map f) =
      b ≫ (A ◁ (adj.homEquiv U B).symm x) ≫ f := by
  dsimp only
  let F := baseChange k K
  let L := Over.map (fieldSpecMap k K)
  let adj := extensionAdj (k := k) K
  let w := (F.obj A ◁ x) ≫ (prodComparisonIso F A B).inv
  let b := lift (L.map (fst (F.obj A) U) ≫ adj.counit.app A) (L.map (snd (F.obj A) U))
  have hw : (adj.homEquiv (F.obj A ⊗ U) (A ⊗ B)).symm w =
      b ≫ (A ◁ (adj.homEquiv U B).symm x) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, ← adj.homEquiv_naturality_right_symm]
      have hwf : w ≫ F.map (fst A B) = fst (F.obj A) U := by
        dsimp only [w]
        rw [Category.assoc, prodComparison_inv_fst K, whiskerLeft_fst]
      rw [hwf, adj.homEquiv_counit]
      exact (lift_fst _ _).symm
    · rw [Category.assoc, whiskerLeft_snd, ← adj.homEquiv_naturality_right_symm]
      have hws : w ≫ F.map (snd A B) = snd (F.obj A) U ≫ x := by
        dsimp only [w]
        rw [Category.assoc, prodComparison_inv_snd K, whiskerLeft_snd]
      rw [hws, adj.homEquiv_naturality_left_symm]
      exact (lift_snd_assoc _ _ _).symm
  change (adj.homEquiv _ _).symm (w ≫ F.map f) = _
  rw [adj.homEquiv_naturality_right_symm, hw, Category.assoc]

private theorem conjugation_baseChange (i : H ⟶ G) :
    (prodComparisonIso (baseChange k K) H.X G.X).inv ≫
      (baseChange k K).map (conjugation i) =
    conjugation ((groupBaseChange k K).map i) := by
  let F := baseChange k K
  let : GrpObj (F.obj G.X) := ((groupBaseChange k K).obj G).grp
  change (prodComparisonIso F H.X G.X).inv ≫ F.map (conjugation i) = _
  unfold conjugation conjugateFamily
  simp only [Category.comp_id, F.map_mul, F.map_inv', F.map_comp, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc]
  rw [prodComparison_inv_fst K H.X G.X, prodComparison_inv_snd K H.X G.X]
  rfl

private theorem centralizes_baseChange (i : H ⟶ G) {U : SchemeOver K}
    (p : U ⟶ ((groupBaseChange k K).obj G).X) :
    Centralizes ((groupBaseChange k K).map i) p ↔
      Centralizes i (((extensionAdj (k := k) K).homEquiv U G.X).symm p) := by
  let F := baseChange k K
  let L := Over.map (fieldSpecMap k K)
  let adj := extensionAdj (k := k) K
  let b := lift (L.map (fst (F.obj H.X) U) ≫ adj.counit.app H.X) (L.map (snd (F.obj H.X) U))
  have : IsIso b := isIso_over_product_map (fieldSpecMap k K) H.X U
  let p' : U ⟶ F.obj G.X := p
  let q : H.X ⊗ G.X ⟶ G.X := fst H.X G.X ≫ i.hom.hom
  have eq : (prodComparisonIso F H.X G.X).inv ≫ F.map q =
      fst (F.obj H.X) (F.obj G.X) ≫ F.map i.hom.hom := by
    rw [Functor.map_comp, ← Category.assoc, prodComparison_inv_fst]
  change conjugateFamily ((groupBaseChange k K).map i) p =
    fst (F.obj H.X) U ≫ F.map i.hom.hom ↔ _
  have ep : conjugateFamily ((groupBaseChange k K).map i) p =
      (F.obj H.X ◁ p') ≫ (prodComparisonIso F H.X G.X).inv ≫ F.map (conjugation i) := by
    rw [conjugation_baseChange K i]
    exact (whisker_conjugation ((groupBaseChange k K).map i) p).symm
  change _ = fst (F.obj H.X) U ≫ F.map i.hom.hom ↔
    Centralizes i ((adj.homEquiv U G.X).symm p')
  rw [ep, ← whiskerLeft_fst_assoc (F.obj H.X) p',
    ← eq, ← (adj.homEquiv (F.obj H.X ⊗ U) G.X).symm.injective.eq_iff]
  erw [adjoint_family K (conjugation i) p', adjoint_family K q p']
  change b ≫ _ = b ≫ _ ↔ _
  rw [cancel_epi, whisker_conjugation]
  simp only [Centralizes, q, whiskerLeft_fst_assoc]
  rfl

private theorem conjugateLe_baseChange (i : H ⟶ G) {U : SchemeOver K}
    (p : U ⟶ ((groupBaseChange k K).obj G).X) :
    ConjugateLe ((groupBaseChange k K).map i) p ↔
      ConjugateLe i (((extensionAdj (k := k) K).homEquiv U G.X).symm p) := by
  let F := baseChange k K
  let L := Over.map (fieldSpecMap k K)
  let adj := extensionAdj (k := k) K
  let b := lift (L.map (fst (F.obj H.X) U) ≫ adj.counit.app H.X) (L.map (snd (F.obj H.X) U))
  have : IsIso b := isIso_over_product_map (fieldSpecMap k K) H.X U
  let p' : U ⟶ F.obj G.X := p
  change (∃ t : F.obj H.X ⊗ U ⟶ F.obj H.X,
    t ≫ F.map i.hom.hom = conjugateFamily ((groupBaseChange k K).map i) p) ↔ _
  have ep : conjugateFamily ((groupBaseChange k K).map i) p =
      (F.obj H.X ◁ p') ≫ (prodComparisonIso F H.X G.X).inv ≫ F.map (conjugation i) := by
    rw [conjugation_baseChange K i]
    exact (whisker_conjugation ((groupBaseChange k K).map i) p).symm
  rw [ep]
  erw [adjoint_factorization K (U := F.obj H.X ⊗ U) i.hom.hom,
    adjoint_family K (conjugation i) p']
  simp only [whisker_conjugation, ConjugateLe]
  let c := conjugateFamily i ((adj.homEquiv U G.X).symm p')
  change (∃ t, t ≫ i.hom.hom = b ≫ c) ↔ ∃ t, t ≫ i.hom.hom = c
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨inv b ≫ t, by rw [Category.assoc, ht, IsIso.inv_hom_id_assoc]⟩
  · rintro ⟨t, ht⟩
    exact ⟨b ≫ t, by rw [Category.assoc, ht]⟩

private theorem stabilizes_baseChange (a : G.X ⊗ X ⟶ X)
    (x : 𝟙_ (SchemeOver k) ⟶ X) {U : SchemeOver K}
    (p : U ⟶ ((groupBaseChange k K).obj G).X) :
    Stabilizes (baseChangeAction K a) (scalarExtendedRationalPoint K x) p ↔
      Stabilizes a x (((extensionAdj (k := k) K).homEquiv U G.X).symm p) := by
  let F := baseChange k K
  let adj := extensionAdj (k := k) K
  have const (V : SchemeOver k) :
      F.map (toUnit V ≫ x) = toUnit (F.obj V) ≫ scalarExtendedRationalPoint K x := by
    rw [Functor.map_comp, scalarExtendedRationalPoint, ← Category.assoc]
    congr 1
    exact (Functor.Monoidal.toUnit_ε F V).symm
  have orb : F.map (orbitMap a x) =
      orbitMap (baseChangeAction K a)
        (scalarExtendedRationalPoint K x) := by
    rw [orbitMap, orbitMap, baseChangeAction, Functor.map_comp, ← Category.assoc]
    congr 1
    rw [Iso.eq_comp_inv]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_fst,
        lift_fst]
      change F.map (lift (𝟙 G.X) (toUnit G.X ≫ x)) ≫ F.map (fst G.X X) = 𝟙 _
      rw [← F.map_comp, lift_fst, F.map_id]
    · simp only [Category.assoc, prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd,
        lift_snd]
      change F.map (lift (𝟙 G.X) (toUnit G.X ≫ x)) ≫ F.map (snd G.X X) =
        toUnit (F.obj G.X) ≫ scalarExtendedRationalPoint K x
      rw [← F.map_comp, lift_snd, const]
  rw [stabilizes_iff_eq, stabilizes_iff_eq, ← orb, ← const,
    ← (adj.homEquiv U X).symm.injective.eq_iff,
    adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_right_symm]

theorem stabilizerSchemeBaseChange : Specs.StabilizerSchemeBaseChange.{u} := by
  intro k K _ _ _ G X a x S hS
  refine ⟨baseChangeClosedSubgroup k K S.inclusion S.isClosedImmersion, fun U p ↦ ?_⟩
  exact (stabilizes_baseChange K a x p).trans
    ((hS _ _).trans (adjoint_factorization K S.inclusion.hom.hom p).symm)

theorem centralizerSchemeBaseChange : Specs.CentralizerSchemeBaseChange.{u} := by
  intro k K _ _ _ G H i C hC
  refine ⟨baseChangeClosedSubgroup k K C.inclusion C.isClosedImmersion, fun U p ↦ ?_⟩
  exact (centralizes_baseChange K i p).trans
    ((hC _ _).trans (adjoint_factorization K C.inclusion.hom.hom p).symm)

theorem normalizerSchemeBaseChange : Specs.NormalizerSchemeBaseChange.{u} := by
  intro k K _ _ _ G H i N hi hN
  refine ⟨baseChangeClosedSubgroup k K N.inclusion N.isClosedImmersion, fun U p ↦ ?_⟩
  let F := baseChange k K
  let adj := extensionAdj (k := k) K
  let j := (groupBaseChange k K).map i
  have hinv : (adj.homEquiv U G.X).symm (p⁻¹ : U ⟶ ((groupBaseChange k K).obj G).X) =
      ((adj.homEquiv U G.X).symm p)⁻¹ := by
    change (adj.homEquiv U G.X).symm (p ≫ F.map (ι[G.X])) =
      (adj.homEquiv U G.X).symm p ≫ ι[G.X]
    exact adj.homEquiv_naturality_right_symm p _
  change Normalizes j p ↔ ∃ z, z ≫ F.map N.inclusion.hom.hom = p
  rw [normalizesIff K j (baseChangeClosedSubgroup k K i hi), conjugateLe_baseChange K,
    conjugateLe_baseChange K, hinv, ← normalizesIff k i hi]
  exact (hN _ _).trans (adjoint_factorization K N.inclusion.hom.hom p).symm

end BaseChange

end
end LinearAlgebraicGroups
