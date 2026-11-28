import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.ModularBlocks
import MathGenome.Internal.AlgebraCore.P103.Ch03.ArtinianProduct
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.RingTheory.LocalRing.RingHom.Basic

open scoped MonoidAlgebra

universe u v w

namespace RepTheorySurvey.Modular

abbrev IsPrimitiveIdempotent := @Specs.primitiveIdempotent
noncomputable abbrev augmentation := @Specs.augmentation
noncomputable abbrev principalIdempotent := @Specs.principal

private theorem primitive_map {C D : Type*} [CommRing C] [CommRing D]
    (f : C ≃+* D) (x : C) (h : IsPrimitiveIdempotent x) :
    IsPrimitiveIdempotent (f x) := by
  refine ⟨h.1.map f, fun he => h.2.1 (f.injective (he.trans (map_zero f).symm)), ?_⟩
  intro y z hy hz hyz hsum
  have hmul : f.symm y * f.symm z = 0 := by rw [← map_mul, hyz, map_zero]
  have hadd : f.symm y + f.symm z = x := by rw [← map_add, hsum, RingEquiv.symm_apply_apply]
  rcases h.2.2 _ _ (hy.map f.symm) (hz.map f.symm) hmul hadd with hzero | hzero
  · left
    simpa using congrArg f hzero
  · right
    simpa using congrArg f hzero

private theorem local_idempotent {C : Type*} [CommRing C] [IsLocalRing C]
    {b : C} (hb : IsIdempotentElem b) : b = 0 ∨ b = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self b with hu | hu
  · exact Or.inr (hu.mul_left_cancel (show b * b = b * 1 by simpa using hb.eq))
  · exact Or.inl (hu.mul_left_cancel (show (1 - b) * b = (1 - b) * 0 by
      simp [sub_mul, hb.eq]))

section Product

variable {I : Type*} {C : I → Type*} [∀ i, CommRing (C i)] [∀ i, IsLocalRing (C i)]
  [DecidableEq I]

private theorem primitive_single (i : I) : IsPrimitiveIdempotent (Pi.single i (1 : C i)) := by
  have hi : IsIdempotentElem (Pi.single i (1 : C i)) := by
    change Pi.single i (1 : C i) * Pi.single i (1 : C i) = _
    rw [← Pi.single_mul, one_mul]
  refine ⟨hi, ?_, ?_⟩
  · intro he
    exact (one_ne_zero : (1 : C i) ≠ 0) (by simpa using congrFun he i)
  · intro x y hx _ hxy hsum
    have hx' (j : I) : x j * x j = x j := congrFun hx.eq j
    have hxy' (j : I) : x j * y j = 0 := congrFun hxy j
    have hsum' (j : I) : x j + y j = Pi.single i (1 : C i) j := congrFun hsum j
    have hoff (j : I) (hj : j ≠ i) : x j = 0 ∧ y j = 0 := by
      have hzero : x j + y j = 0 := by simpa [Pi.single_eq_of_ne hj] using hsum' j
      have hxj : x j = 0 := by
        calc
          x j = x j * x j := (hx' j).symm
          _ = x j * (x j + y j) := by rw [mul_add, hxy' j, add_zero]
          _ = 0 := by rw [hzero, mul_zero]
      exact ⟨hxj, by simpa [hxj] using hzero⟩
    rcases local_idempotent (show IsIdempotentElem (x i) from hx' i) with hzero | hone
    · left
      funext j
      by_cases hj : j = i
      · subst j
        exact hzero
      · exact (hoff j hj).1
    · right
      funext j
      by_cases hj : j = i
      · subst j
        simpa [hone] using hxy' i
      · exact (hoff j hj).2

private theorem primitive_exists_single {b : ∀ i, C i} (hb : IsPrimitiveIdempotent b) :
    ∃ i, b = Pi.single i (1 : C i) := by
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra! h
    exact hb.2.1 (funext h)
  have hbi : b i = 1 :=
    (local_idempotent (show IsIdempotentElem (b i) from congrFun hb.1.eq i)).resolve_left hi
  let x : ∀ i, C i := Pi.single i (1 : C i)
  let y := b - x
  have hy : IsIdempotentElem y := by
    change y * y = y
    funext j
    change (b j - x j) * (b j - x j) = b j - x j
    by_cases hj : j = i
    · subst j
      simp [x, hbi]
    · have hbj : b j * b j = b j := congrFun hb.1.eq j
      simpa [x, Pi.single_eq_of_ne hj] using hbj
  have hxy : x * y = 0 := by
    funext j
    change x j * (b j - x j) = 0
    by_cases hj : j = i
    · subst j
      simp [x, hbi]
    · simp [x, Pi.single_eq_of_ne hj]
  have hsum : x + y = b := by
    change x + (b - x) = b
    rw [add_comm, sub_add_cancel]
  have hzero := (hb.2.2 x y (primitive_single i).1 hy hxy hsum).resolve_left (primitive_single i).2.1
  exact ⟨i, by simpa [hzero] using hsum.symm⟩

private theorem single_one_injective :
    Function.Injective (fun i : I => Pi.single i (1 : C i)) := by
  intro i j hij
  by_contra h
  exact (one_ne_zero : (1 : C i) ≠ 0)
    (by simpa [Pi.single_eq_of_ne h] using congrFun hij i)

omit [∀ i, IsLocalRing (C i)] in
private theorem single_one_orthogonal {i j : I} (hij : i ≠ j) :
    Pi.single i (1 : C i) * Pi.single j (1 : C j) = 0 := by
  funext l
  change Pi.single i (1 : C i) l * Pi.single j (1 : C j) l = 0
  by_cases hl : l = i
  · subst l
    simp [Pi.single_eq_of_ne hij]
  · simp [Pi.single_eq_of_ne hl]

private theorem single_one_sum [Fintype I] :
    (∑ i : I, Pi.single i (1 : C i)) = 1 := by
  funext j
  rw [Finset.sum_apply]
  change (∑ i : I, Pi.single i (1 : C i) j) = 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi.symm]
  · simp

private noncomputable def cornerFactor {Z : Type*} [CommRing Z] (e : Z ≃+* (∀ i, C i))
    {b : Z} (hb : IsIdempotentElem b) {i : I} (hi : e b = Pi.single i (1 : C i)) :
    hb.Corner ≃+* C i := by
  have he : e b i = 1 := by simp [hi]
  have hzero (j : I) (hj : j ≠ i) (x : hb.Corner) : e x.1 j = 0 := by
    have hfix : b * x.1 = x.1 := ((Subsemigroup.mem_corner_iff hb).mp x.2).1
    have hcoord : e b j * e x.1 j = e x.1 j := by
      simpa only [map_mul, Pi.mul_apply] using congrArg (fun z => e z j) hfix
    simpa [hi, Pi.single_eq_of_ne hj] using hcoord.symm
  let f : hb.Corner →+* C i :=
    { toFun x := e x.1 i
      map_zero' := congrFun (map_zero e) i
      map_one' := he
      map_add' x y := congrFun (map_add e x.1 y.1) i
      map_mul' x y := congrFun (map_mul e x.1 y.1) i }
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply e.injective
    funext j
    by_cases hj : j = i
    · subst j
      exact hxy
    · exact (hzero j hj x).trans (hzero j hj y).symm
  · intro z
    let x := e.symm (Pi.single i z)
    have hfix : b * x = x := by
      apply e.injective
      simp only [map_mul, hi, x, RingEquiv.apply_symm_apply, ← Pi.single_mul, one_mul]
    refine ⟨⟨x, (Subsemigroup.mem_corner_iff hb).mpr ⟨hfix, (mul_comm x b).trans hfix⟩⟩, ?_⟩
    change e x i = z
    simp [x]

end Product

section Blocks

variable {R : Type u} {G : Type v} [CommRing R] [Group G]

theorem BlockIdempotent.mem_algebra_iff (b : BlockIdempotent R G) (a : R[G]) :
    a ∈ Subsemigroup.corner b.element ↔ ∃ x : R[G], x * b.element = a :=
  Subsemigroup.mem_corner_iff_mem_range_mul_right b.idempotent b.central

theorem BlockIdempotent.mem_algebra_iff_mem_ideal (b : BlockIdempotent R G) (a : R[G]) :
    a ∈ Subsemigroup.corner b.element ↔ a ∈ Ideal.span {b.element} :=
  (b.mem_algebra_iff a).trans Ideal.mem_span_singleton'.symm

theorem BlockIdempotent.projection_surjective (b : BlockIdempotent R G) :
    Function.Surjective b.projection := by
  intro x
  refine ⟨x.1, Subtype.ext ?_⟩
  exact ((Subsemigroup.mem_corner_iff b.idempotent).mp x.2).2

@[simp] theorem BlockIdempotent.algebra_smul (b : BlockIdempotent R G) (a : R[G])
    (x : b.Algebra) : (a • x).1 = a * x.1 := by
  change (a * b.element) * x.1 = a * x.1
  exact (mul_assoc ..).trans (congrArg (a * ·) ((Subsemigroup.mem_corner_iff b.idempotent).mp x.2).1)

@[simp] theorem BlockIdempotent.algebra_one (b : BlockIdempotent R G) :
    (1 : b.Algebra).1 = b.element := rfl

theorem BlockIdempotent.element_ne_zero (b : BlockIdempotent R G) : b.element ≠ 0 :=
  fun he => b.2.2.1 (Subtype.ext he)

theorem BlockIdempotent.element_injective :
    Function.Injective (BlockIdempotent.element (R := R) (G := G)) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

end Blocks

section Field

variable (k : Type u) (G : Type v) [Field k] [Group G] [Finite G]

private theorem artinian_center : IsArtinianRing (Subalgebra.center k k[G]) := by
  let := Fintype.ofFinite G
  have : IsArtinian k k[G] :=
    isArtinian_of_linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm
  exact isArtinian_of_tower k
    (isArtinian_of_injective (Subalgebra.center k k[G]).val.toLinearMap Subtype.val_injective)

private theorem blocks_and_local_centers :
    (∃ s : Finset (BlockIdempotent k G), (∀ b, b ∈ s) ∧
      (∑ b ∈ s, b.element) = 1 ∧
      Pairwise (fun b c : BlockIdempotent k G => b.element * c.element = 0)) ∧
    ∀ b : BlockIdempotent k G, IsLocalRing b.Center := by
  classical
  let Z := Subalgebra.center k k[G]
  let : IsArtinianRing Z := artinian_center k G
  obtain ⟨hfin, n, _, _, hfactors, e, _⟩ := P103.Ch03.ArtinianProduct.decomposition Z
  let := hfin
  let := Fintype.ofFinite (MaximalSpectrum Z)
  let (i : MaximalSpectrum Z) : IsLocalRing (Z ⧸ i.asIdeal ^ n) := (hfactors i).1
  let b (i : MaximalSpectrum Z) : BlockIdempotent k G :=
    ⟨e.symm (Pi.single i 1), primitive_map e.symm _ (primitive_single i)⟩
  have he (i : MaximalSpectrum Z) : e (b i).1 = Pi.single i 1 := e.apply_symm_apply _
  have hinj : Function.Injective b := by
    intro i j hij
    apply single_one_injective (C := fun l : MaximalSpectrum Z => Z ⧸ l.asIdeal ^ n)
    simpa only [he] using congrArg (fun c : BlockIdempotent k G => e c.1) hij
  have hsurj : Function.Surjective b := by
    intro c
    obtain ⟨i, hi⟩ := primitive_exists_single (primitive_map e c.1 c.2)
    exact ⟨i, Subtype.ext (e.injective ((he i).trans hi.symm))⟩
  constructor
  · refine ⟨Finset.univ.image b, ?_, ?_, ?_⟩
    · intro c
      obtain ⟨i, rfl⟩ := hsurj c
      exact Finset.mem_image_of_mem b (Finset.mem_univ i)
    · rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      have hsum : (∑ i, (b i).1) = (1 : Z) := by
        apply e.injective
        simpa only [map_sum, map_one, he] using
          (single_one_sum (C := fun l : MaximalSpectrum Z => Z ⧸ l.asIdeal ^ n))
      change (∑ i, (Subalgebra.center k k[G]).val (b i).1) = 1
      rw [← map_sum, hsum, map_one]
    · intro c d hcd
      obtain ⟨i, rfl⟩ := hsurj c
      obtain ⟨j, rfl⟩ := hsurj d
      have hij : i ≠ j := fun h => hcd (congrArg b h)
      have hzero : (b i).1 * (b j).1 = (0 : Z) := by
        apply e.injective
        simpa only [map_mul, map_zero, he] using
          (single_one_orthogonal (C := fun l : MaximalSpectrum Z => Z ⧸ l.asIdeal ^ n) hij)
      exact congrArg (fun z : Z => (z : k[G])) hzero
  · intro c
    obtain ⟨i, rfl⟩ := hsurj c
    exact (cornerFactor e (b i).center_idempotent (he i)).symm.isLocalRing

/-- All block idempotents form a finite orthogonal family with sum one. -/
theorem block_decomposition : Specs.blocks_type.{u, v} :=
  fun k G _ _ _ => (blocks_and_local_centers k G).1

/-- A finite group algebra has finitely many block idempotents. -/
instance blockIdempotent_finite (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] :
    Finite (BlockIdempotent k G) := by
  obtain ⟨s, hs, _, _⟩ := block_decomposition k G
  exact Finite.of_surjective (fun b : ↥s => b.val) (fun b => ⟨⟨b, hs b⟩, rfl⟩)

theorem BlockIdempotent.center_isLocal {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
    (b : BlockIdempotent k G) : IsLocalRing b.Center :=
  (blocks_and_local_centers k G).2 b

end Field

section Modules

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
variable {M : Type w} [AddCommGroup M] [Module k[G] M]

omit [Finite G] in
private theorem simple_block_action [IsSimpleModule k[G] M] (b : BlockIdempotent k G) :
    b.BelongsTo M ∨ ∀ m : M, b.element • m = 0 := by
  let f : M →ₗ[k[G]] M :=
    { toFun m := b.element • m
      map_add' := smul_add _
      map_smul' r m := by
        change b.element • (r • m) = r • (b.element • m)
        rw [← mul_smul, ← mul_smul, (b.central.comm r).eq] }
  rcases eq_bot_or_eq_top (LinearMap.range f) with hzero | htop
  · right
    intro m
    exact LinearMap.congr_fun (LinearMap.range_eq_bot.mp hzero) m
  · left
    intro m
    obtain ⟨x, rfl⟩ := LinearMap.range_eq_top.mp htop m
    change b.element • (b.element • x) = b.element • x
    rw [← mul_smul, b.idempotent.eq]

theorem simple_has_unique_block (M : Type w) [AddCommGroup M] [Module k[G] M]
    [IsSimpleModule k[G] M] : ∃! b : BlockIdempotent k G, b.BelongsTo M := by
  have := IsSimpleModule.nontrivial k[G] M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨s, _, hsum, horth⟩ := block_decomposition k G
  have hex : ∃ b : BlockIdempotent k G, b.BelongsTo M := by
    by_contra! h
    apply hm
    calc
      m = (1 : k[G]) • m := (one_smul _ _).symm
      _ = ∑ b ∈ s, b.element • m := by rw [← hsum, Finset.sum_smul]
      _ = 0 := Finset.sum_eq_zero fun b _ => ((simple_block_action b).resolve_left (h b)) m
  obtain ⟨b, hb⟩ := hex
  refine ⟨b, hb, fun c hc => ?_⟩
  by_contra hne
  exact hm (calc
    m = c.element • (b.element • m) := by rw [hb m, hc m]
    _ = 0 := by rw [← mul_smul, horth hne, zero_smul])

omit [Finite G] in
theorem BlockIdempotent.exists_simple_quotient (b : BlockIdempotent k G) :
    ∃ N : Submodule k[G] b.Algebra,
      IsSimpleModule k[G] (b.Algebra ⧸ N) ∧ b.BelongsTo (b.Algebra ⧸ N) := by
  have hspan : Function.Surjective (LinearMap.toSpanSingleton k[G] b.Algebra 1) := by
    intro x
    obtain ⟨a, ha⟩ := b.projection_surjective x
    refine ⟨a, ?_⟩
    change b.projection a * 1 = x
    simpa using ha
  let : Module.Finite k[G] b.Algebra := Module.Finite.of_surjective _ hspan
  have : Nontrivial b.Algebra := nontrivial_of_ne 1 0
    (fun h => b.element_ne_zero (congrArg Subtype.val h))
  obtain ⟨N, hN, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule k[G] b.Algebra)).resolve_left
    bot_ne_top
  refine ⟨N, isSimpleModule_iff_isCoatom.mpr hN, ?_⟩
  have hproj : b.projection b.element = 1 := Subtype.ext b.idempotent.eq
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
  rw [← Submodule.Quotient.mk_smul]
  exact congrArg (Submodule.Quotient.mk (p := N)) (show b.projection b.element * y = y by simp [hproj])

end Modules

section Principal

variable {R : Type u} {G : Type v} [CommRing R] [Group G]

theorem augmentation_eq_sum [Fintype G] (x : R[G]) :
    augmentation R G x = ∑ g : G, x.coeff g := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    simp [Specs.augmentation, MonoidAlgebra.lift_single]
  | add x y hx hy =>
    simp [hx, hy, Finset.sum_add_distrib]
  | smul r x hx =>
    simp [hx, Finset.mul_sum, smul_eq_mul]

private theorem trivial_action {k : Type u} [Field k] {G : Type v} [Group G] (x : k[G])
    (m : (Representation.trivial k G k).asModule) :
    (Representation.trivial k G k).asModuleEquiv (x • m) =
      augmentation k G x * (Representation.trivial k G k).asModuleEquiv m := by
  rw [Representation.asModuleEquiv_map_smul]
  generalize (Representation.trivial k G k).asModuleEquiv m = y
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    rw [Representation.asAlgebraHom_of, Representation.trivial_apply]
    simp [Specs.augmentation, MonoidAlgebra.of_apply, MonoidAlgebra.lift_single]
  | add x z hx hz =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hz, add_mul]
  | smul r x hx =>
    rw [map_smul, map_smul, LinearMap.smul_apply, hx]
    simp only [smul_eq_mul, mul_assoc]

theorem BlockIdempotent.belongsTo_trivial_iff {k : Type u} {H : Type v} [Field k] [Group H]
    (b : BlockIdempotent k H) :
    b.BelongsTo (Representation.trivial k H k).asModule ↔ augmentation k H b.element = 1 := by
  let e := (Representation.trivial k H k).asModuleEquiv
  constructor
  · intro h
    have hval := congrArg e (h (e.symm 1))
    rw [trivial_action, LinearEquiv.apply_symm_apply, mul_one] at hval
    exact hval
  · intro h m
    apply e.injective
    rw [trivial_action, h, one_mul]

private theorem trivial_isSimple (k : Type u) (G : Type v) [Field k] [Group G] :
    IsSimpleModule k[G] (Representation.trivial k G k).asModule := by
  let e := (Representation.trivial k G k).asModuleEquiv
  have : Nontrivial (Representation.trivial k G k).asModule := e.toEquiv.nontrivial
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, ?_⟩
  intro m hm y
  have hm' : e m ≠ 0 := fun h => hm (e.injective (h.trans (map_zero e).symm))
  refine ⟨algebraMap k k[G] (e y / e m), e.injective ?_⟩
  change e (algebraMap k k[G] (e y / e m) • m) = e y
  rw [trivial_action, AlgHom.commutes, Algebra.algebraMap_self_apply, div_mul_cancel₀ _ hm']

theorem principal_block_unique (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] :
    ∃! b : BlockIdempotent k G, b.BelongsTo (Representation.trivial k G k).asModule := by
  let := trivial_isSimple k G
  exact simple_has_unique_block _

theorem principal_idempotent_spec (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] :
    ∃ b : BlockIdempotent k G,
      b.1 = principalIdempotent k G ∧ b.BelongsTo (Representation.trivial k G k).asModule := by
  classical
  obtain ⟨b, hb, _⟩ := principal_block_unique k G
  have hex : ∃ c : BlockIdempotent k G, augmentation k G c.element = 1 :=
    ⟨b, b.belongsTo_trivial_iff.mp hb⟩
  refine ⟨hex.choose, ?_, hex.choose.belongsTo_trivial_iff.mpr hex.choose_spec⟩
  simp [Specs.principal, hex]

/-- The block of the trivial one-dimensional representation. -/
noncomputable def principalBlock (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] :
    BlockIdempotent k G :=
  ⟨principalIdempotent k G, by
    obtain ⟨b, hb, _⟩ := principal_idempotent_spec k G
    exact hb ▸ b.2⟩

theorem principalBlock_belongs (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] :
    (principalBlock k G).BelongsTo (Representation.trivial k G k).asModule := by
  obtain ⟨b, hb, hbel⟩ := principal_idempotent_spec k G
  have h : b = principalBlock k G := Subtype.ext hb
  exact h ▸ hbel

theorem principalBlock_augmentation (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] :
    augmentation k G (principalBlock k G).element = 1 :=
  (principalBlock k G).belongsTo_trivial_iff.mp (principalBlock_belongs k G)

end Principal

end RepTheorySurvey.Modular
