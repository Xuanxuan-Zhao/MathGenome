import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechCochains
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Full unnormalized Čech cochains (HA-H02), including their augmentation. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped Simplicial
open AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.Cech

universe u r v w

namespace AdvancedHomologicalAlgebra.CechCochains

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (F : PresheafOfModules.{w} R.obj)
  {U : Opens X} {I : Type v} (c : Cover U I)

abbrev cochains := Cochains R F c
abbrev differential := Cech.differential R F c
abbrev augmentation := Cech.augmentation R F c

lemma reindex_id (p : ℕ) : reindex R F c (id : Fin (p + 1) → _) = LinearMap.id := by
  ext s t
  change F.map (𝟙 (op (tupleOpen c t))) (s t) = s t
  exact congr($(F.presheaf.map_id (op (tupleOpen c t))) (s t))

lemma reindex_comp {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1))
    (g : Fin (q + 1) → Fin (r + 1)) :
    reindex R F c (g ∘ f) = (reindex R F c g).comp (reindex R F c f) := by
  ext s t
  exact F.map_comp_apply _ _ _

/-- All tuple reindexings, including repeated positions, form a cosimplicial module. -/
def cosimplicial : CosimplicialObject (ModuleCat.{max v w} (sectionRing R U)) where
  obj n := ModuleCat.of _ (Cochains R F c n.len)
  map f := ModuleCat.ofHom (reindex R F c f.toOrderHom)
  map_id n := by
    apply ModuleCat.hom_ext
    exact reindex_id R F c n.len
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact reindex_comp R F c f.toOrderHom g.toOrderHom

lemma differential_eq_alternating (p : ℕ) :
    ModuleCat.ofHom (differential R F c p) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimplicial R F c) p := by
  simp only [differential, Cech.differential,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  rfl

theorem differential_squared :
    Specs.AdvancedHomologicalAlgebra.CechCochains.differentialSquared R F c := by
  intro p
  have h := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
    (cosimplicial R F c) p
  rw [← differential_eq_alternating, ← differential_eq_alternating] at h
  exact congrArg ModuleCat.Hom.hom h

/-- The cochain complex with exactly these full product terms and differentials. -/
def complex : CochainComplex (ModuleCat.{max v w} (sectionRing R U)) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (cosimplicial R F c)

@[simp]
lemma complex_X (p : ℕ) :
    (complex R F c).X p = ModuleCat.of (sectionRing R U) (Cochains R F c p) := rfl

@[simp]
lemma complex_d (p : ℕ) :
    (complex R F c).d p (p + 1) = ModuleCat.ofHom (differential R F c p) := by
  exact (CochainComplex.of_d (fun n ↦ (cosimplicial R F c).obj ⦋n⦌)
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimplicial R F c)) p).trans
    (differential_eq_alternating R F c p).symm

/-- In degree zero, the prescribed signs give `res(s_j) - res(s_i)`. -/
lemma differential_zero_apply (s : Cochains R F c 0) (t : Fin 2 → I) :
    differential R F c 0 s t =
      (F.presheaf.map (homOfLE (show tupleOpen c t ≤ c.opens (t 1) from inf_le_right)).op
        (s (fun _ ↦ t 1)) : F.obj (op (tupleOpen c t))) -
      (F.presheaf.map (homOfLE (show tupleOpen c t ≤ c.opens (t 0) from inf_le_left)).op
        (s (fun _ ↦ t 0)) : F.obj (op (tupleOpen c t))) := by
  have h0 : t ∘ (0 : Fin 2).succAbove = fun _ : Fin 1 ↦ t 1 := by
    funext a; exact congrArg t (congrArg Fin.succ (Subsingleton.elim a 0))
  have h1 : t ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 ↦ t 0 := by
    funext a; rw [Subsingleton.elim a 0]; rfl
  change ((∑ a : Fin 2, (-1 : ℤ) ^ a.val • reindex R F c a.succAbove) s t) = _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_zsmul,
    LinearMap.add_apply, LinearMap.neg_apply, Pi.add_apply, Pi.neg_apply]
  change F.presheaf.map
      (homOfLE (tupleOpen_reindex_le c (0 : Fin 2).succAbove t)).op
      (s (t ∘ (0 : Fin 2).succAbove)) +
    -(F.presheaf.map (homOfLE (tupleOpen_reindex_le c (1 : Fin 2).succAbove t)).op
      (s (t ∘ (1 : Fin 2).succAbove))) = _
  have hs0 : HEq (s (t ∘ (0 : Fin 2).succAbove)) (s (fun _ ↦ t 1)) := by rw [h0]
  have hs1 : HEq (s (t ∘ (1 : Fin 2).succAbove)) (s (fun _ ↦ t 0)) := by rw [h1]
  rw [eq_of_heq hs0, eq_of_heq hs1]
  exact (sub_eq_add_neg _ _).symm

theorem augmentation_closed :
    Specs.AdvancedHomologicalAlgebra.CechCochains.augmentationClosed R F c := by
  ext s t
  change differential R F c 0 (augmentation R F c s) t = 0
  rw [differential_zero_apply]
  change F.presheaf.map _ (F.presheaf.map _ s) -
    F.presheaf.map _ (F.presheaf.map _ s) = 0
  rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp,
    ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  exact sub_self _

lemma closed_iff_compatible (s : Cochains R F c 0) :
    differential R F c 0 s = 0 ↔
      TopCat.Presheaf.IsCompatible F.presheaf c.opens (fun i ↦ s (fun _ ↦ i)) := by
  constructor
  · intro hs i j
    have h := congrArg (fun z ↦ z ![i, j]) hs
    rw [differential_zero_apply] at h
    exact (sub_eq_zero.mp h).symm
  · intro hs
    funext t
    rw [differential_zero_apply]
    exact sub_eq_zero.mpr (hs (t 0) (t 1)).symm

/-- The canonical augmentation with its codomain restricted to cocycles. -/
def augmentationToKernel : F.obj (op U) →ₗ[sectionRing R U] zeroCocycles R F c :=
  (augmentation R F c).codRestrict _ (fun s ↦ by
    change differential R F c 0 (augmentation R F c s) = 0
    exact LinearMap.congr_fun (augmentation_closed R F c) s)

variable (M : SheafOfModules.{w} R)

lemma augmentationToKernel_bijective :
    Function.Bijective (augmentationToKernel R M.val c) := by
  obtain ⟨opens, le, covers⟩ := c
  subst U
  let c : Cover (iSup opens) I := ⟨opens, le, rfl⟩
  change Function.Bijective (augmentationToKernel R M.val c)
  let A : TopCat.Presheaf (Type w) X := M.val.presheaf ⋙ forget AddCommGrpCat.{w}
  -- The free rank-one abelian group corepresents the underlying-set functor.
  have hA : A.IsSheaf := by
    change CategoryTheory.Presheaf.IsSheaf _ (_ ⋙ forget AddCommGrpCat.{w})
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso _ (Functor.isoWhiskerLeft _
      AddCommGrpCat.coyonedaObjIsoForget) (M.isSheaf (AddCommGrpCat.of (ULift.{w} ℤ)))
  apply (Function.bijective_iff_existsUnique _).mpr
  intro z
  let sf : ∀ i, A.obj (op (opens i)) := fun i ↦ z.val (fun _ ↦ i)
  have hc : TopCat.Presheaf.IsCompatible A opens sf :=
    (closed_iff_compatible R M.val c z.val).mp z.property
  obtain ⟨s, hs, huniq⟩ := hA.isSheafUniqueGluing_types sf hc
  refine ⟨s, ?_, ?_⟩
  · apply Subtype.ext
    funext t
    have ht : (fun _ : Fin 1 ↦ t 0) = t := by
      funext a
      rw [Subsingleton.elim a 0]
    have h := hs (t 0)
    change M.val.map (homOfLE (tupleOpen_le c t)).op s = z.val t
    change M.val.map (homOfLE (c.le (t 0))).op s = z.val (fun _ ↦ t 0) at h
    have hz : HEq (z.val (fun _ ↦ t 0)) (z.val t) := by rw [ht]
    exact h.trans (eq_of_heq hz)
  · intro t ht
    apply huniq
    intro i
    exact congrArg (fun z : zeroCocycles R M.val c ↦ z.val (fun _ ↦ i)) ht

/-- The linear identification uses precisely the restriction augmentation. -/
def sectionsKernelEquiv :
    M.val.obj (op U) ≃ₗ[sectionRing R U] zeroCocycles R M.val c :=
  LinearEquiv.ofBijective (augmentationToKernel R M.val c)
    (augmentationToKernel_bijective R c M)

@[simp]
lemma sectionsKernelEquiv_apply (s : M.val.obj (op U)) :
    (sectionsKernelEquiv R c M s).val = augmentation R M.val c s := rfl

theorem sections_kernel :
    Specs.AdvancedHomologicalAlgebra.CechCochains.sectionsKernel R c M :=
  ⟨sectionsKernelEquiv R c M, fun _ ↦ rfl⟩

end AdvancedHomologicalAlgebra.CechCochains
