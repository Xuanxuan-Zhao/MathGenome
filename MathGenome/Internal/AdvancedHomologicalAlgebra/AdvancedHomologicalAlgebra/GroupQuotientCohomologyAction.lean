import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupBarResolution
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCochainComparison
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# The quotient action on subgroup cohomology

Conjugation on the homogeneous bar complex induces the action of the quotient.
The projective resolution induced from that bar complex and any injective
resolution of the coefficients compute the same Ext group. The comparison is
equivariant because the two actions come from the same map in the first Ext
argument.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
universe u v w
namespace AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
open Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction

section BarResolution

variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private lemma barAugmentation_exact :
    (ShortComplex.mk _ _ (GroupBar.Large.boundary_augmentation.{u,v,w} k G)).Exact := by
  let F : Rep.{max u v w} k G ⥤ ModuleCat.{max u v w} k := forget₂ _ _
  apply (ShortComplex.exact_map_iff_of_faithful _ F).mp
  apply ModuleCat.shortComplex_exact
  intro x
  change (ULift.up (GroupBar.Large.ε.{u,v,w} k G x) : ULift.{max v w} k) =
    ULift.up (0 : k) ↔ ∃ y, GroupBar.Large.d.{u,v,w} k G 0 y = x
  simpa only [ULift.up_inj] using GroupBar.Large.exact_zero.{u,v,w} k G x

private lemma barAugmentation_epi : Epi (GroupBar.Large.augmentation.{u,v,w} k G) := by
  apply (Rep.epi_iff_surjective _).mpr
  intro x
  obtain ⟨y, hy⟩ := GroupBar.Large.augmentation_surjective.{u,v,w} k G x.down
  exact ⟨y, ULift.ext hy⟩

private def barAugmentationChainMap :
    GroupBar.Large.complex.{u,v,w} k G ⟶ (ChainComplex.single₀ _).obj
      (GroupBar.Large.trivial.{u,v,w} k G) :=
  ((GroupBar.Large.complex.{u,v,w} k G).toSingle₀Equiv _).symm
    ⟨GroupBar.Large.augmentation.{u,v,w} k G, GroupBar.Large.boundary_augmentation.{u,v,w} k G⟩

private lemma barAugmentation_quasiIso : QuasiIso (barAugmentationChainMap.{u,v,w} k G) := by
  constructor
  intro n
  cases n with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      simp only [barAugmentationChainMap, HomologicalComplex.shortComplexFunctor'_map_τ₂,
        ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
      exact ⟨barAugmentation_exact.{u,v,w} k G, barAugmentation_epi.{u,v,w} k G⟩
  | succ n =>
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
      let F : Rep.{max u v w} k G ⥤ ModuleCat.{max u v w} k := forget₂ _ _
      apply (ShortComplex.exact_map_iff_of_faithful _ F).mp
      apply ModuleCat.shortComplex_exact
      exact GroupBar.Large.exact_succ.{u,v,w} k G n

/-- The augmented homogeneous bar complex in the representation category. -/
def barResolution : ProjectiveResolution (GroupBar.Large.trivial.{u,v,w} k G) where
  complex := GroupBar.Large.complex.{u,v,w} k G
  projective n := by
    let E : Rep.{max u v w} k G ≌ ModuleCat.{max u v w} k[G] :=
      Rep.equivalenceModuleMonoidAlgebra
    let := GroupBar.Large.degree_free.{u,v,w} k G n
    let : Module.Projective k[G] (GroupBar.Large.B.{u,v,w} k G n).ρ.asModule :=
      Module.Projective.of_free
    let X := GroupBar.Large.B.{u,v,w} k G n
    have h : Projective (E.functor.obj X) :=
      ModuleCat.projective_of_categoryTheory_projective
        (ModuleCat.of k[G] (GroupBar.Large.B.{u,v,w} k G n).ρ.asModule)
    exact Projective.of_iso (E.unitIso.app X).symm (E.inverse.projective_obj_of_projective h)
  π := barAugmentationChainMap.{u,v,w} k G
  quasiIso := barAugmentation_quasiIso.{u,v,w} k G

@[simp] lemma barResolution_π_f_zero :
    (barResolution.{u,v,w} k G).π.f 0 = GroupBar.Large.augmentation.{u,v,w} k G :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

@[simp] lemma barAugmentation_single (c : Fin 1 → G) (r : k) :
    (GroupBar.Large.augmentation.{u,v,w} k G).hom
      (GroupBar.Large.single.{u,v,w} k G c r) = (ULift.up r : ULift.{max v w} k) :=
  congrArg ULift.up (GroupBar.Large.augmentation_single.{u,v,w} k G c r)

end BarResolution

variable (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]

/-- The usual factorization of a map from an inflated module through M^N. -/
def invariantsHomEquiv (X : Rep.{max u v w} k (G ⧸ N)) (M : Rep.{max u v w} k G) :
    ((inflation.{u,v,w} k G N).obj X ⟶ M) ≃ (X ⟶ (normalInvariants.{u,v,w} k G N).obj M) where
  toFun f := Rep.ofHom
    ⟨f.hom.toLinearMap.codRestrict _ (by
      intro x b
      change M.ρ (b : G) (f.hom x) = f.hom x
      have h := (Rep.hom_comm_apply f (b : G) x).symm
      have hb : QuotientGroup.mk' N (b : G) = 1 :=
        (QuotientGroup.eq_one_iff (N := N) (b : G)).mpr b.property
      change M.ρ (b : G) (f.hom x) = f.hom (X.ρ (QuotientGroup.mk' N b) x) at h
      simpa only [hb, map_one, Module.End.one_apply] using h), fun q => by
        induction q using QuotientGroup.induction_on with | H g =>
          ext x
          exact Rep.hom_comm_apply f g x⟩
  invFun f := Rep.ofHom
    ⟨(Submodule.subtype _).comp f.hom.toLinearMap, fun g => by
      ext x
      exact congrArg Subtype.val (Rep.hom_comm_apply f (QuotientGroup.mk' N g) x)⟩
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl

/-- Inflation is left adjoint to normal-subgroup invariants. -/
def inflationInvariantsAdjunction : inflation.{u,v,w} k G N ⊣ normalInvariants.{u,v,w} k G N :=
  Adjunction.mkOfHomEquiv {
    homEquiv := invariantsHomEquiv.{u,v,w} k G N
    homEquiv_naturality_left_symm := by intros; ext x; rfl
    homEquiv_naturality_right := by intros; ext x; rfl }

instance normalInvariants_preservesInjectives :
    (normalInvariants.{u,v,w} k G N).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (inflationInvariantsAdjunction.{u,v,w} k G N)

theorem invariantsAdjunctionFor : InvariantsAdjunction.{u,v,w} k G N :=
  ⟨⟨inflationInvariantsAdjunction.{u,v,w} k G N⟩, inferInstance, inferInstance, inferInstance⟩


/-- Pullback of homogeneous tuples by inverse conjugation. -/
def conjugateBar (g : G) (j : ℕ) : GroupBar.Large.B.{u,v,w} k N j →ₗ[k] GroupBar.Large.B.{u,v,w} k N j :=
  MonoidAlgebra.mapDomainLinearMap k k
    (fun c : ULift.{w} (Fin (j+1) → N) => ULift.up (fun i => MulAut.conjNormal g⁻¹ (c.down i)))

@[simp] lemma conjugateBar_single (g : G) (j : ℕ) (c : Fin (j+1) → N) (r : k) :
    conjugateBar.{u,v,w} k G N g j (GroupBar.Large.single.{u,v,w} k N c r) =
      GroupBar.Large.single.{u,v,w} k N (fun i => MulAut.conjNormal g⁻¹ (c i)) r := by
  simp [conjugateBar, GroupBar.Large.single]

/-- Coefficient action after inverse conjugation of homogeneous vertices. -/
def conjugateCochain (M : Rep.{max u v w} k G) (g : G) (j : ℕ)
    (φ : GroupBar.Large.B.{u,v,w} k N j ⟶ Rep.res N.subtype M) :
    GroupBar.Large.B.{u,v,w} k N j ⟶ Rep.res N.subtype M :=
  Rep.ofHom ⟨M.ρ g ∘ₗ φ.hom.toLinearMap ∘ₗ conjugateBar.{u,v,w} k G N g j, fun b => by
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change M.ρ g (φ.hom (conjugateBar.{u,v,w} k G N g j
        ((GroupBar.Large.B.{u,v,w} k N j).ρ b (GroupBar.Large.single.{u,v,w} k N c 1)))) =
      M.ρ (b : G) (M.ρ g (φ.hom (conjugateBar.{u,v,w} k G N g j (GroupBar.Large.single.{u,v,w} k N c 1))))
    rw [GroupBar.Large.diagonal_action, conjugateBar_single, conjugateBar_single]
    have ht : (fun i => MulAut.conjNormal g⁻¹ (b * c i)) =
        (fun i => MulAut.conjNormal g⁻¹ b * MulAut.conjNormal g⁻¹ (c i)) := by
      funext i; exact map_mul _ _ _
    rw [ht, ← GroupBar.Large.diagonal_action.{u,v,w} k N j]
    rw [Rep.hom_comm_apply φ]
    change M.ρ g (M.ρ (↑(MulAut.conjNormal g⁻¹ b) : G) _) = _
    simp only [MulAut.conjNormal_apply, inv_inv]
    simp [← Module.End.mul_apply, ← map_mul, mul_assoc]⟩

@[simp] lemma conjugateCochain_single (M : Rep.{max u v w} k G) (g : G) (j : ℕ)
    (φ : GroupBar.Large.B.{u,v,w} k N j ⟶ Rep.res N.subtype M) (c : Fin (j+1) → N) (r : k) :
    (conjugateCochain.{u,v,w} k G N M g j φ).hom (GroupBar.Large.single.{u,v,w} k N c r) =
      M.ρ g (φ.hom (GroupBar.Large.single.{u,v,w} k N
        (fun i => MulAut.conjNormal g⁻¹ (c i)) r)) := by
  change M.ρ g (φ.hom (conjugateBar.{u,v,w} k G N g j (GroupBar.Large.single.{u,v,w} k N c r))) = _
  rw [conjugateBar_single]

/-- Each group element acts k-linearly on the homogeneous cochains. -/
def conjugateCochainLinear (M : Rep.{max u v w} k G) (g : G) (j : ℕ) :
    (homogeneousComplex.{u,v,w} k G N M).X j →ₗ[k] (homogeneousComplex.{u,v,w} k G N M).X j where
  toFun := conjugateCochain.{u,v,w} k G N M g j
  map_add' φ ψ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    ext x
    exact map_add (M.ρ g) _ _
  map_smul' r φ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    ext x
    exact (M.ρ g).map_smul r _


/-- Inverse conjugation of vertices commutes with alternating deletion. -/
lemma conjugateBar_boundary (g : G) (j : ℕ) :
    conjugateBar.{u,v,w} k G N g j ∘ₗ GroupBar.Large.d.{u,v,w} k N j =
      GroupBar.Large.d.{u,v,w} k N j ∘ₗ conjugateBar.{u,v,w} k G N g (j+1) := by
  apply MonoidAlgebra.lhom_ext'
  rintro ⟨c⟩
  apply LinearMap.ext_ring
  change conjugateBar.{u,v,w} k G N g j (GroupBar.Large.d.{u,v,w} k N j (GroupBar.Large.single.{u,v,w} k N c 1)) =
    GroupBar.Large.d.{u,v,w} k N j (conjugateBar.{u,v,w} k G N g (j+1) (GroupBar.Large.single.{u,v,w} k N c 1))
  rw [GroupBar.Large.boundary_single, map_sum, conjugateBar_single, GroupBar.Large.boundary_single]
  apply Finset.sum_congr rfl
  intro i hi
  exact conjugateBar_single.{u,v,w} k G N g j (c ∘ i.succAbove) _

/-- The action is a cochain map, not just a degreewise linear operation. -/
def conjugateCochainMap (M : Rep.{max u v w} k G) (g : G) :
    homogeneousComplex.{u,v,w} k G N M ⟶ homogeneousComplex.{u,v,w} k G N M where
  f j := ModuleCat.ofHom (conjugateCochainLinear.{u,v,w} k G N M g j)
  comm' i j hij := by
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change (GroupBar.Large.B.{u,v,w} k N i ⟶ Rep.res N.subtype M) at φ
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    ext x
    change M.ρ g (φ.hom (conjugateBar.{u,v,w} k G N g i (GroupBar.Large.d.{u,v,w} k N i x))) =
      M.ρ g (φ.hom (GroupBar.Large.d.{u,v,w} k N i (conjugateBar.{u,v,w} k G N g (i+1) x)))
    exact congrArg (fun y => M.ρ g (φ.hom y))
      (LinearMap.congr_fun (conjugateBar_boundary.{u,v,w} k G N g i) x)

/-- Conjugation and the coefficient action give an actual group action on
homogeneous cochains. Endomorphism multiplication is function composition. -/
def homogeneousAction (M : Rep.{max u v w} k G) : G →* End (homogeneousComplex.{u,v,w} k G N M) where
  toFun g := End.of (conjugateCochainMap.{u,v,w} k G N M g)
  map_one' := by
    apply End.ext
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change (GroupBar.Large.B.{u,v,w} k N j ⟶ Rep.res N.subtype M) at φ
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change (conjugateCochain.{u,v,w} k G N M 1 j φ).hom (GroupBar.Large.single.{u,v,w} k N c 1) =
      φ.hom (GroupBar.Large.single.{u,v,w} k N c 1)
    rw [conjugateCochain_single.{u,v,w} k G N M 1 j φ c 1]
    simp
  map_mul' g h := by
    apply End.ext
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change (GroupBar.Large.B.{u,v,w} k N j ⟶ Rep.res N.subtype M) at φ
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change (conjugateCochain.{u,v,w} k G N M (g*h) j φ).hom (GroupBar.Large.single.{u,v,w} k N c 1) =
      (conjugateCochain.{u,v,w} k G N M g j (conjugateCochain.{u,v,w} k G N M h j φ)).hom
        (GroupBar.Large.single.{u,v,w} k N c 1)
    rw [conjugateCochain_single.{u,v,w} k G N M (g*h) j φ c 1,
      conjugateCochain_single.{u,v,w} k G N M g j (conjugateCochain.{u,v,w} k G N M h j φ) c 1,
      conjugateCochain_single.{u,v,w} k G N M h j φ (fun i => MulAut.conjNormal g⁻¹ (c i)) 1]
    simp only [mul_inv_rev, map_mul, MulAut.mul_apply,
      Module.End.mul_apply]

lemma homogeneousAction_formula (M : Rep.{max u v w} k G) :
    ActionFormula.{u,v,w} k G N M (homogeneousAction.{u,v,w} k G N M) := by
  intro g j φ c
  exact conjugateCochain_single.{u,v,w} k G N M g j φ c 1

theorem cochainAction : CochainAction.{u,v,w} k G N := by
  intro M
  exact ⟨homogeneousAction.{u,v,w} k G N M, homogeneousAction_formula.{u,v,w} k G N M⟩


/-- Simultaneous right translation is N-linear for the diagonal left action. -/
def rightTranslateDegree (b : N) (j : ℕ) : GroupBar.Large.B.{u,v,w} k N j ⟶ GroupBar.Large.B.{u,v,w} k N j :=
  Rep.ofHom ⟨MonoidAlgebra.mapDomainLinearMap k k
    (fun c : ULift.{w} (Fin (j+1) → N) => ULift.up (fun i => c.down i * b)), fun a => by
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change MonoidAlgebra.mapDomainLinearMap k k (fun c : ULift.{w} (Fin (j+1) → N) => ULift.up (fun i => c.down i * b))
        ((GroupBar.Large.B.{u,v,w} k N j).ρ a (GroupBar.Large.single.{u,v,w} k N c 1)) =
      (GroupBar.Large.B.{u,v,w} k N j).ρ a
        (MonoidAlgebra.mapDomainLinearMap k k (fun c : ULift.{w} (Fin (j+1) → N) => ULift.up (fun i => c.down i * b))
          (GroupBar.Large.single.{u,v,w} k N c 1))
    rw [GroupBar.Large.diagonal_action]
    simp only [GroupBar.Large.single, MonoidAlgebra.mapDomainLinearMap_single]
    change GroupBar.Large.single.{u,v,w} k N (fun i => (a * c i) * b) 1 =
      (GroupBar.Large.B.{u,v,w} k N j).ρ a (GroupBar.Large.single.{u,v,w} k N (fun i => c i * b) 1)
    rw [GroupBar.Large.diagonal_action]
    simp only [mul_assoc]⟩

omit [N.Normal] in
@[simp] lemma rightTranslateDegree_single (b : N) (j : ℕ) (c : Fin (j+1) → N) (r : k) :
    (rightTranslateDegree.{u,v,w} k G N b j).hom (GroupBar.Large.single.{u,v,w} k N c r) =
      GroupBar.Large.single.{u,v,w} k N (fun i => c i * b) r := by
  simp [rightTranslateDegree, GroupBar.Large.single]

/-- Right translation of all vertices is a chain map on the homogeneous bar resolution. -/
def rightTranslate (b : N) : GroupBar.Large.complex.{u,v,w} k N ⟶ GroupBar.Large.complex.{u,v,w} k N where
  f j := rightTranslateDegree.{u,v,w} k G N b j
  comm' i j hij := by
    subst i
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    symm
    change (rightTranslateDegree.{u,v,w} k G N b j).hom (GroupBar.Large.d.{u,v,w} k N j (GroupBar.Large.single.{u,v,w} k N c 1)) =
      GroupBar.Large.d.{u,v,w} k N j ((rightTranslateDegree.{u,v,w} k G N b (j+1)).hom (GroupBar.Large.single.{u,v,w} k N c 1))
    rw [GroupBar.Large.boundary_single, map_sum,
      rightTranslateDegree_single.{u,v,w} k G N b (j+1), GroupBar.Large.boundary_single]
    apply Finset.sum_congr rfl
    intro i hi
    exact rightTranslateDegree_single.{u,v,w} k G N b j (c ∘ i.succAbove) _

/-- Both right translation and the identity lift the identity of the trivial
module. Projective-resolution comparison therefore supplies an N-linear
homotopy. This avoids any choice of coset representatives or coefficients. -/
def rightTranslateHomotopy (b : N) :
    Homotopy (rightTranslate.{u,v,w} k G N b) (𝟙 (GroupBar.Large.complex.{u,v,w} k N)) := by
  let π : GroupBar.Large.complex.{u,v,w} k N ⟶
      (ChainComplex.single₀ _).obj (GroupBar.Large.trivial.{u,v,w} k N) :=
    (barResolution.{u,v,w} k N).π
  apply ProjectiveResolution.liftHomotopy (𝟙 (GroupBar.Large.trivial.{u,v,w} k N))
    (P := barResolution.{u,v,w} k N) (Q := barResolution.{u,v,w} k N)
  · change rightTranslate.{u,v,w} k G N b ≫ π = π ≫ (ChainComplex.single₀ _).map (𝟙 _)
    apply HomologicalComplex.to_single_hom_ext
    have hπ : π.f 0 = GroupBar.Large.augmentation.{u,v,w} k N :=
      barResolution_π_f_zero.{u,v,w} k N
    simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero, hπ]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change (GroupBar.Large.augmentation.{u,v,w} k N).hom
        ((rightTranslateDegree.{u,v,w} k G N b 0).hom (GroupBar.Large.single.{u,v,w} k N c 1)) =
      (GroupBar.Large.augmentation.{u,v,w} k N).hom (GroupBar.Large.single.{u,v,w} k N c 1)
    rw [rightTranslateDegree_single, barAugmentation_single, barAugmentation_single]
  · change 𝟙 _ ≫ π = π ≫ (ChainComplex.single₀ _).map (𝟙 _)
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero, Category.id_comp]
    exact (Category.comp_id (π.f 0)).symm

/-- Pullback along any map of homogeneous bar complexes. -/
def barPullback (M : Rep.{max u v w} k G) (t : GroupBar.Large.complex.{u,v,w} k N ⟶ GroupBar.Large.complex.{u,v,w} k N) :
    homogeneousComplex.{u,v,w} k G N M ⟶ homogeneousComplex.{u,v,w} k G N M :=
  (HomologicalComplex.unopFunctor (ModuleCat k) (ComplexShape.down ℕ)).map
    (((((linearYoneda k (Rep k N)).obj (Rep.res N.subtype M)).rightOp.mapHomologicalComplex _).map t).op)

/-- An N-linear homotopy on the resolution induces a cochain homotopy by
precomposition. Opposite categories reverse the homological grading. -/
def barPullbackHomotopy (M : Rep.{max u v w} k G)
    {t s : GroupBar.Large.complex.{u,v,w} k N ⟶ GroupBar.Large.complex.{u,v,w} k N} (h : Homotopy t s) :
    Homotopy (barPullback.{u,v,w} k G N M t) (barPullback.{u,v,w} k G N M s) :=
  ((((linearYoneda k (Rep k N)).obj (Rep.res N.subtype M)).rightOp).mapHomotopy h).unop

lemma conjugateCochainMap_subgroup (M : Rep.{max u v w} k G) (b : N) :
    conjugateCochainMap.{u,v,w} k G N M b = barPullback.{u,v,w} k G N M (rightTranslate.{u,v,w} k G N b) := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (GroupBar.Large.B.{u,v,w} k N j ⟶ Rep.res N.subtype M) at φ
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  rintro ⟨c⟩
  apply LinearMap.ext_ring
  change (conjugateCochain.{u,v,w} k G N M b j φ).hom (GroupBar.Large.single.{u,v,w} k N c 1) =
    φ.hom ((rightTranslateDegree.{u,v,w} k G N b j).hom (GroupBar.Large.single.{u,v,w} k N c 1))
  rw [conjugateCochain_single.{u,v,w} k G N M b j φ c 1, rightTranslateDegree_single.{u,v,w} k G N b j c 1]
  have ht : (fun i => c i * b) =
      (fun i => b * MulAut.conjNormal (↑b : G)⁻¹ (c i)) := by
    funext i
    apply Subtype.ext
    simp [mul_assoc]
  rw [ht, ← GroupBar.Large.diagonal_action.{u,v,w} k N j, Rep.hom_comm_apply φ]
  rfl

/-- Every element of N acts cochain-homotopically as the identity. -/
def subgroupActionHomotopy (M : Rep.{max u v w} k G) (b : N) :
    Homotopy (homogeneousAction.{u,v,w} k G N M b).asHom (𝟙 _) := by
  change Homotopy (conjugateCochainMap.{u,v,w} k G N M b) (𝟙 _)
  rw [conjugateCochainMap_subgroup]
  exact (barPullbackHomotopy.{u,v,w} k G N M (rightTranslateHomotopy.{u,v,w} k G N b)).trans
    (Homotopy.ofEq (by ext j φ; rfl))

lemma subgroupAction_trivial (M : Rep.{max u v w} k G) :
    Triviality.{u,v,w} k G N M (homogeneousAction.{u,v,w} k G N M) := by
  refine ⟨fun b => ⟨subgroupActionHomotopy.{u,v,w} k G N M b⟩, ?_⟩
  intro b j
  simpa using (subgroupActionHomotopy.{u,v,w} k G N M b).homologyMap_eq j


/-- The induced representation on the actual homogeneous cohomology module. -/
def cohomologyRepresentation (M : Rep.{max u v w} k G) (j : ℕ) :
    Representation k G ((homogeneousComplex.{u,v,w} k G N M).homology j) where
  toFun g := (HomologicalComplex.homologyMap (homogeneousAction.{u,v,w} k G N M g).asHom j).hom
  map_one' := by
    rw [map_one]
    change (HomologicalComplex.homologyMap (𝟙 (homogeneousComplex.{u,v,w} k G N M)) j).hom = _
    rw [HomologicalComplex.homologyMap_id]
    rfl
  map_mul' g h := by
    rw [map_mul]
    change (HomologicalComplex.homologyMap
      ((homogeneousAction.{u,v,w} k G N M h).asHom ≫ (homogeneousAction.{u,v,w} k G N M g).asHom) j).hom = _
    rw [HomologicalComplex.homologyMap_comp]
    rfl

instance cohomologyRepresentation_trivial (M : Rep.{max u v w} k G) (j : ℕ) :
    Representation.IsTrivial ((cohomologyRepresentation.{u,v,w} k G N M j).comp N.subtype) where
  out b := by
    change (HomologicalComplex.homologyMap (homogeneousAction.{u,v,w} k G N M b).asHom j).hom = _
    rw [(subgroupAction_trivial.{u,v,w} k G N M).2 b j]
    rfl

/-- The N-trivial action descends to G/N without choosing representatives. -/
def quotientCohomologyRepresentation (M : Rep.{max u v w} k G) (j : ℕ) :
    Representation k (G ⧸ N) ((homogeneousComplex.{u,v,w} k G N M).homology j) :=
  (cohomologyRepresentation.{u,v,w} k G N M j).ofQuotient N

lemma quotientAction (M : Rep.{max u v w} k G) :
    QuotientAction.{u,v,w} k G N M (homogeneousAction.{u,v,w} k G N M) := by
  intro j
  refine ⟨quotientCohomologyRepresentation.{u,v,w} k G N M j, ?_⟩
  intro g
  rfl


/-- The conjugation action, its N-linear bar homotopy, and its descent to Q. -/
theorem actionAndDescentFor : ActionAndDescent.{u,v,w} k G N := by
  intro M
  exact ⟨homogeneousAction.{u,v,w} k G N M, homogeneousAction_formula.{u,v,w} k G N M,
    subgroupAction_trivial.{u,v,w} k G N M, quotientAction.{u,v,w} k G N M⟩

def quotientSection (q : G ⧸ N) : G := Function.surjInv (QuotientGroup.mk'_surjective N) q

@[simp] lemma quotientSection_mk (q : G ⧸ N) :
    QuotientGroup.mk' N (quotientSection G N q) = q :=
  Function.surjInv_eq (QuotientGroup.mk'_surjective N) q

/-- The N-part of an element relative to a right coset representative. -/
def quotientComponent (g : G) : N :=
  ⟨g * (quotientSection G N (QuotientGroup.mk' N g))⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N _ = 1
    rw [map_mul, map_inv, quotientSection_mk, mul_inv_cancel]⟩

lemma quotientComponent_mul (b : N) (g : G) :
    quotientComponent G N ((b : G) * g) = b * quotientComponent G N g := by
  apply Subtype.ext
  have hb : QuotientGroup.mk' N (b : G) = 1 := (QuotientGroup.eq_one_iff _).mpr b.property
  simp [quotientComponent, map_mul, hb, mul_assoc]

/-- The direct-sum coordinates of an induced module on right cosets. -/
def inductionCoordinates (A : Rep.{max u v w} k N) :
    Rep.ind N.subtype A →ₗ[k] ((G ⧸ N) →₀ A) :=
  Representation.Coinvariants.lift _
    (TensorProduct.lift <|
      (Finsupp.linearCombination k fun g : G =>
        (Finsupp.lsingle (QuotientGroup.mk' N g)).comp (A.ρ (quotientComponent G N g)⁻¹)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
    (fun b => by
      ext g a
      have hb : QuotientGroup.mk' N (b : G) = 1 := (QuotientGroup.eq_one_iff _).mpr b.property
      have hq : QuotientGroup.mk' N ((b : G)*g) = QuotientGroup.mk' N g := by rw [map_mul, hb, one_mul]
      have hq' : (((b : G) * g : G) : G ⧸ N) = (g : G ⧸ N) := hq
      simp [quotientComponent_mul, ← Module.End.mul_apply, ← map_mul, hq'])

@[simp] lemma inductionCoordinates_mk (A : Rep.{max u v w} k N) (g : G) (a : A) :
    inductionCoordinates.{u,v,w} k G N A (Representation.IndV.mk N.subtype A.ρ g a) =
      Finsupp.single (QuotientGroup.mk' N g) (A.ρ (quotientComponent G N g)⁻¹ a) := by
  simp [inductionCoordinates]

/-- Rebuild from the finitely supported coordinates, valid at arbitrary index. -/
def fromInductionCoordinates (A : Rep.{max u v w} k N) :
    ((G ⧸ N) →₀ A) →ₗ[k] Rep.ind N.subtype A :=
  Finsupp.lsum k fun q => Representation.IndV.mk N.subtype A.ρ (quotientSection G N q)

lemma from_inductionCoordinates (A : Rep.{max u v w} k N) :
    fromInductionCoordinates.{u,v,w} k G N A ∘ₗ inductionCoordinates.{u,v,w} k G N A = LinearMap.id := by
  apply Representation.IndV.hom_ext N.subtype A.ρ
  intro g
  ext a
  change fromInductionCoordinates.{u,v,w} k G N A
      (inductionCoordinates.{u,v,w} k G N A (Representation.IndV.mk N.subtype A.ρ g a)) =
    Representation.IndV.mk N.subtype A.ρ g a
  rw [inductionCoordinates_mk]
  simp only [fromInductionCoordinates, Finsupp.lsum_single]
  change Representation.IndV.mk N.subtype A.ρ (quotientSection G N (QuotientGroup.mk' N g))
      (A.ρ (quotientComponent G N g)⁻¹ a) = Representation.IndV.mk N.subtype A.ρ g a
  change Representation.Coinvariants.mk _
      (MonoidAlgebra.single (quotientSection G N (QuotientGroup.mk' N g)) (1 : k) ⊗ₜ[k]
        A.ρ (quotientComponent G N g)⁻¹ a) = _
  rw [Representation.Coinvariants.mk_tmul_inv]
  simp [quotientComponent, Representation.ofMulAction_single]

lemma inductionCoordinates_injective (A : Rep.{max u v w} k N) :
    Function.Injective (inductionCoordinates.{u,v,w} k G N A) := by
  apply Function.LeftInverse.injective (g := fromInductionCoordinates.{u,v,w} k G N A)
  intro x
  exact LinearMap.congr_fun (from_inductionCoordinates.{u,v,w} k G N A) x


lemma inductionCoordinates_natural {A B : Rep.{max u v w} k N} (f : A ⟶ B) :
    inductionCoordinates.{u,v,w} k G N B ∘ₗ (Rep.indMap N.subtype f).hom.toLinearMap =
      Finsupp.mapRange.linearMap f.hom.toLinearMap ∘ₗ inductionCoordinates.{u,v,w} k G N A := by
  apply Representation.IndV.hom_ext N.subtype A.ρ
  intro g
  ext a
  simp [inductionCoordinates, Rep.indMap, Rep.hom_comm_apply]

instance induction_additive : (Rep.indFunctor.{max u v w} k N.subtype).Additive where
  map_add := by
    intros A B f g
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Representation.IndV.hom_ext N.subtype A.ρ
    intro t
    ext a
    simp [Rep.indFunctor, Rep.indMap, Rep.add_hom]

instance induction_preservesMonos : (Rep.indFunctor.{max u v w} k N.subtype).PreservesMonomorphisms where
  preserves {A B} f hf := by
    apply (Rep.mono_iff_injective _).mpr
    intro x y hxy
    apply inductionCoordinates_injective.{u,v,w} k G N A
    apply Finsupp.mapRange_injective f.hom.toLinearMap (map_zero _) ((Rep.mono_iff_injective f).mp hf)
    change (Finsupp.mapRange.linearMap f.hom.toLinearMap) (inductionCoordinates.{u,v,w} k G N A x) =
      (Finsupp.mapRange.linearMap f.hom.toLinearMap) (inductionCoordinates.{u,v,w} k G N A y)
    have hn := LinearMap.congr_fun (inductionCoordinates_natural.{u,v,w} k G N f)
    exact (hn x).symm.trans ((congrArg (inductionCoordinates.{u,v,w} k G N B) hxy).trans (hn y))

instance induction_preservesFiniteLimits : PreservesFiniteLimits (Rep.indFunctor.{max u v w} k N.subtype) := by
  have := Functor.preservesHomology_of_preservesMonos_and_cokernels (Rep.indFunctor.{max u v w} k N.subtype)
  exact Functor.preservesFiniteLimits_of_preservesHomology _

instance restriction_preservesInjectives :
    (Rep.resFunctor.{max u v w} (k := k) N.subtype).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Rep.indResAdjunction.{max u v w} k N.subtype)

open Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction in
theorem restrictionInjectivesFor : RestrictionInjectives.{u,v,w} k G N :=
  ⟨⟨Rep.indResAdjunction.{max u v w} k N.subtype⟩, inferInstance, inferInstance, inferInstance⟩


/-- The cochain action is natural in every k[G]-linear coefficient map. -/
lemma homogeneousAction_natural {M L : Rep.{max u v w} k G} (f : M ⟶ L) (g : G) :
    (homogeneousAction.{u,v,w} k G N M g).asHom ≫ coefficientCochainMap.{u,v,w} k G N f =
      coefficientCochainMap.{u,v,w} k G N f ≫ (homogeneousAction.{u,v,w} k G N L g).asHom := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (GroupBar.Large.B.{u,v,w} k N j ⟶ Rep.res N.subtype M) at φ
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  rintro ⟨c⟩
  apply LinearMap.ext_ring
  change f.hom ((conjugateCochain.{u,v,w} k G N M g j φ).hom (GroupBar.Large.single.{u,v,w} k N c 1)) =
    (conjugateCochain.{u,v,w} k G N L g j (φ ≫ Rep.resMap N.subtype f)).hom (GroupBar.Large.single.{u,v,w} k N c 1)
  rw [conjugateCochain_single.{u,v,w} k G N M g j φ c 1,
    conjugateCochain_single.{u,v,w} k G N L g j (φ ≫ Rep.resMap N.subtype f) c 1]
  exact Rep.hom_comm_apply f g _


theorem actionAndDescent : actionAndDescentExpected.{u,v,w} :=
  fun k G _ _ N _ => actionAndDescentFor.{u,v,w} k G N

theorem invariantsAdjunction : invariantsAdjunctionExpected.{u,v,w} :=
  fun k G _ _ N _ => invariantsAdjunctionFor.{u,v,w} k G N

theorem restrictionInjectives : restrictionInjectivesExpected.{u,v,w} :=
  fun k G _ _ N _ => restrictionInjectivesFor.{u,v,w} k G N

end AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction



universe uC vC uR
namespace InjectiveBridge
open CochainComplex HomComplex
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{vC} C]
  (k : Type uR) [CommRing k] [Linear k C] {X Y : C} (R : InjectiveResolution Y)

def homComplex (X : C) : CochainComplex (ModuleCat.{vC} k) ℕ :=
  (((linearCoyoneda k C).obj (Opposite.op X)).mapHomologicalComplex (.up ℕ)).obj R.cocomplex

def homShortComplex (X : C) (n : ℕ) : ShortComplex (ModuleCat.{vC} k) :=
  (homComplex k R X).sc' (n-1) n (n+1)

def cyclesExtMap (X : C) (n : ℕ) :
    (homShortComplex k R X n).moduleCatLeftHomologyData.K →ₗ[k] Abelian.Ext X Y n where
  toFun f := R.extMk f.1 (n+1) rfl (by exact f.2)
  map_add' f g := (R.add_extMk _ _ _ _ _ _).symm
  map_smul' r f := by
    change R.extMk (r • f.1) (n+1) rfl _ = r • R.extMk f.1 (n+1) rfl _
    exact (R.smul_extMk r f.1 (n+1) rfl _).symm

lemma cyclesExtMap_surjective (X : C) (n : ℕ) :
    Function.Surjective (cyclesExtMap k R X n) := by
  intro x
  obtain ⟨f, hf, hx⟩ := R.extMk_surjective x (n+1) rfl
  exact ⟨⟨f, hf⟩, hx⟩

lemma extMk_zero_iff (f : X ⟶ R.cocomplex.X 0) (hf : f ≫ R.cocomplex.d 0 1 = 0) :
    R.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  rw [← R.extEquivCohomologyClass.apply_eq_iff_eq]
  simp only [InjectiveResolution.extEquivCohomologyClass_extMk,
    InjectiveResolution.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1) (by simp)]
  constructor
  · rintro ⟨g, hg⟩
    have hgzero : g = 0 :=
      (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 (-1)).eq_of_tgt _ _
    apply (cancel_mono (R.cochainComplexXIso 0 0 rfl).inv).mp
    simpa [hgzero] using hg.symm
  · intro hfzero
    subst f
    exact ⟨0, by simp⟩

lemma cyclesExtMap_exact (X : C) (n : ℕ) :
    Function.Exact (homShortComplex k R X n).moduleCatToCycles (cyclesExtMap k R X n) := by
  intro f
  cases n with
  | zero =>
      dsimp only [cyclesExtMap, LinearMap.coe_mk, AddHom.coe_mk]
      rw [extMk_zero_iff]
      constructor
      · intro hf
        refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa using hf.symm
      · rintro ⟨g, hg⟩
        have hg' := congrArg Subtype.val hg
        change ((homComplex k R X).d 0 0).hom g = f.1 at hg'
        rw [HomologicalComplex.shape _ _ _ (by simp)] at hg'
        change f.1 = 0
        exact hg'.symm.trans rfl
  | succ n =>
      dsimp only [cyclesExtMap, LinearMap.coe_mk, AddHom.coe_mk]
      rw [R.extMk_eq_zero_iff _ _ _ _ n rfl]
      simp only [homShortComplex, Nat.succ_sub_one]
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g, Subtype.ext hg⟩
      · rintro ⟨g, hg⟩
        exact ⟨g, congrArg Subtype.val hg⟩

def extLeftHomologyData (X : C) (n : ℕ) : (homShortComplex k R X n).LeftHomologyData where
  K := (homShortComplex k R X n).moduleCatLeftHomologyData.K
  H := ModuleCat.of k (Abelian.Ext X Y n)
  i := (homShortComplex k R X n).moduleCatLeftHomologyData.i
  π := ModuleCat.ofHom (cyclesExtMap k R X n)
  wi := (homShortComplex k R X n).moduleCatLeftHomologyData.wi
  hi := (homShortComplex k R X n).moduleCatLeftHomologyData.hi
  wπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (cyclesExtMap_exact k R X n _).mpr ⟨f, rfl⟩
  hπ := ModuleCat.isColimitCokernelCofork _ _ (cyclesExtMap_exact k R X n)
    (cyclesExtMap_surjective k R X n)

def homologyExtIso (X : C) (n : ℕ) :
    (homComplex k R X).homology n ≅ ModuleCat.of k (Abelian.Ext X Y n) :=
  (ShortComplex.homologyFunctor (ModuleCat k)).mapIso
    ((homComplex k R X).isoSc' (n-1) n (n+1)
      (AdvancedHomologicalAlgebra.GroupCochainComparison.ResolutionBridge.prev_up_nat n)
      ((ComplexShape.up ℕ).next_eq' rfl)) ≪≫
    (extLeftHomologyData k R X n).homologyIso

def homPostcomp {Y Z : C} (R : InjectiveResolution Y) (S : InjectiveResolution Z)
    (g : R.cocomplex ⟶ S.cocomplex) (X : C) :
    homComplex k R X ⟶ homComplex k S X :=
  (((linearCoyoneda k C).obj (Opposite.op X)).mapHomologicalComplex (.up ℕ)).map g

def cyclesPostcomp {Y Z : C} (R : InjectiveResolution Y) (S : InjectiveResolution Z)
    (g : R.cocomplex ⟶ S.cocomplex) (X : C) (n : ℕ) :
    (homShortComplex k R X n).moduleCatLeftHomologyData.K →ₗ[k]
      (homShortComplex k S X n).moduleCatLeftHomologyData.K where
  toFun f := ⟨f.1 ≫ g.f n, by
    change (f.1 ≫ g.f n) ≫ S.cocomplex.d n (n+1) = 0
    have hf := f.2
    change f.1 ≫ R.cocomplex.d n (n+1) = 0 at hf
    rw [Category.assoc, g.comm, ← Category.assoc, hf, zero_comp]⟩
  map_add' f g := by
    apply Subtype.ext
    exact Preadditive.add_comp _ _ _ f.1 g.1 _
  map_smul' r f := by
    apply Subtype.ext
    exact Linear.smul_comp _ _ _ r f.1 _

def homologyMapData {Y Z : C} (R : InjectiveResolution Y) (S : InjectiveResolution Z)
    (b : Y ⟶ Z) (φ : InjectiveResolution.Hom R S b) (X : C) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat k) (.up ℕ) (n-1) n (n+1)).map
        (homPostcomp k R S φ.hom X)) (extLeftHomologyData k R X n)
        (extLeftHomologyData k S X n) where
  φK := ModuleCat.ofHom (cyclesPostcomp k R S φ.hom X n)
  φH := (Abelian.linearExtFunctorObj k X n).map b
  commi := by ext f; rfl
  commf' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change (f ≫ R.cocomplex.d (n-1) n) ≫ φ.hom.f n =
      (f ≫ φ.hom.f (n-1)) ≫ S.cocomplex.d (n-1) n
    simp only [Category.assoc, ← φ.hom.comm]
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact R.extMk_comp_mk₀ f.1 (n+1) rfl f.2 φ

lemma homologyExtIso_natural {Y Z : C} (R : InjectiveResolution Y) (S : InjectiveResolution Z)
    (b : Y ⟶ Z) (φ : InjectiveResolution.Hom R S b) (X : C) (n : ℕ) :
    HomologicalComplex.homologyMap (homPostcomp k R S φ.hom X) n ≫
      (homologyExtIso k S X n).hom =
      (homologyExtIso k R X n).hom ≫ (Abelian.linearExtFunctorObj k X n).map b := by
  have hnat := (HomologicalComplex.natIsoSc' (ModuleCat k) (.up ℕ) (n-1) n (n+1)
    (AdvancedHomologicalAlgebra.GroupCochainComparison.ResolutionBridge.prev_up_nat n)
      ((ComplexShape.up ℕ).next_eq' rfl)).hom.naturality (homPostcomp k R S φ.hom X)
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat k)).map hnat
  simp only [Functor.map_comp] at h
  dsimp only [homologyExtIso, Iso.trans_hom, Functor.mapIso_hom]
  change HomologicalComplex.homologyMap (homPostcomp k R S φ.hom X) n ≫
      (ShortComplex.homologyFunctor (ModuleCat k)).map
        ((homComplex k S X).isoSc' (n-1) n (n+1) _ _).hom = _ at h
  erw [← Category.assoc, h, Category.assoc]
  erw [(homologyMapData k R S b φ X n).homologyMap_comm]
  simp only [Category.assoc]
  rfl

def homPrecomp {X X' : C} (b : X' ⟶ X) : homComplex k R X ⟶ homComplex k R X' where
  f n := ModuleCat.ofHom (Linear.leftComp k (R.cocomplex.X n) b)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change (b ≫ f) ≫ R.cocomplex.d i j = b ≫ (f ≫ R.cocomplex.d i j)
    exact Category.assoc _ _ _

def cyclesPrecomp {X X' : C} (b : X' ⟶ X) (n : ℕ) :
    (homShortComplex k R X n).moduleCatLeftHomologyData.K →ₗ[k]
      (homShortComplex k R X' n).moduleCatLeftHomologyData.K where
  toFun f := ⟨b ≫ f.1, by
    change (b ≫ f.1) ≫ R.cocomplex.d n (n+1) = 0
    have hf := f.2
    change f.1 ≫ R.cocomplex.d n (n+1) = 0 at hf
    simp [Category.assoc, hf]⟩
  map_add' f g := by
    apply Subtype.ext
    exact Preadditive.comp_add _ _ _ b f.1 g.1
  map_smul' r f := by
    apply Subtype.ext
    exact Linear.comp_smul _ _ _ b r f.1

def homologyMapDataPrecomp {X X' : C} (b : X' ⟶ X) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat k) (.up ℕ) (n-1) n (n+1)).map
        (homPrecomp k R b)) (extLeftHomologyData k R X n)
        (extLeftHomologyData k R X' n) where
  φK := ModuleCat.ofHom (cyclesPrecomp k R b n)
  φH := ((Abelian.linearExtFunctor k C n).map b.op).app Y
  commi := by ext f; rfl
  commf' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact R.mk₀_comp_extMk f.1 (n+1) rfl f.2 b

lemma homologyExtIso_precomp {X X' : C} (b : X' ⟶ X) (n : ℕ) :
    HomologicalComplex.homologyMap (homPrecomp k R b) n ≫
      (homologyExtIso k R X' n).hom =
      (homologyExtIso k R X n).hom ≫ ((Abelian.linearExtFunctor k C n).map b.op).app Y := by
  have hnat := (HomologicalComplex.natIsoSc' (ModuleCat k) (.up ℕ) (n-1) n (n+1)
    (AdvancedHomologicalAlgebra.GroupCochainComparison.ResolutionBridge.prev_up_nat n)
      ((ComplexShape.up ℕ).next_eq' rfl)).hom.naturality (homPrecomp k R b)
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat k)).map hnat
  simp only [Functor.map_comp] at h
  dsimp only [homologyExtIso, Iso.trans_hom, Functor.mapIso_hom]
  change HomologicalComplex.homologyMap (homPrecomp k R b) n ≫
      (ShortComplex.homologyFunctor (ModuleCat k)).map
        ((homComplex k R X').isoSc' (n-1) n (n+1) _ _).hom = _ at h
  erw [← Category.assoc, h, Category.assoc]
  erw [(homologyMapDataPrecomp k R b n).homologyMap_comm]
  simp only [Category.assoc]
  rfl

end InjectiveBridge


namespace AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.ProjectiveBridge
open AdvancedHomologicalAlgebra.GroupCochainComparison.ResolutionBridge
open AdvancedHomologicalAlgebra.ExtShiftedHom.LiftedP103 (resolutionSign)
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{vC} C]
  (k : Type uR) [CommRing k] [Linear k C]
  {X X' Y : C} (R : ProjectiveResolution X) (R' : ProjectiveResolution X')

def homPrecomp (t : R'.complex ⟶ R.complex) :
    R.complex.linearYonedaObj k Y ⟶ R'.complex.linearYonedaObj k Y where
  f n := ModuleCat.ofHom
    { toFun f := t.f n ≫ f
      map_add' f g := Preadditive.comp_add _ _ _ _ _ _
      map_smul' r f := Linear.comp_smul _ _ _ _ _ _ }
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change R'.complex.d j i ≫ (t.f i ≫ f) = t.f j ≫ (R.complex.d j i ≫ f)
    rw [← Category.assoc, ← t.comm]
    exact Category.assoc _ _ _

def cyclesPrecomp (t : R'.complex ⟶ R.complex) (n : ℕ) :
    (homShortComplex k (Y := Y) R n).moduleCatLeftHomologyData.K →ₗ[k]
      (homShortComplex k (Y := Y) R' n).moduleCatLeftHomologyData.K where
  toFun f := ⟨t.f n ≫ f.1, by
    change R'.complex.d (n+1) n ≫ (t.f n ≫ f.1) = 0
    have hf := f.2
    change R.complex.d (n+1) n ≫ f.1 = 0 at hf
    rw [← Category.assoc, ← t.comm, Category.assoc, hf, comp_zero]⟩
  map_add' f g := by
    apply Subtype.ext
    exact Preadditive.comp_add _ _ _ _ _ _
  map_smul' r f := by
    apply Subtype.ext
    exact Linear.comp_smul _ _ _ _ _ _

def homologyPrecompData {g : X' ⟶ X} (φ : ProjectiveResolution.Hom R' R g) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat k) (.up ℕ) (n-1) n (n+1)).map
        (homPrecomp k R R' (Y := Y) φ.hom))
      (extLeftHomologyData k R n) (extLeftHomologyData k R' n) where
  φK := ModuleCat.ofHom (cyclesPrecomp k R R' φ.hom n)
  φH := ((Abelian.linearExtFunctor k C n).map g.op).app Y
  commi := by ext f; rfl
  commf' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change φ.hom.f n ≫ (R.complex.d n (n-1) ≫ f) =
      R'.complex.d n (n-1) ≫ (φ.hom.f (n-1) ≫ f)
    rw [← Category.assoc, φ.hom.comm, Category.assoc]
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change (((Abelian.linearExtFunctor k C n).map g.op).app Y).hom (cyclesExtMap k R n f) =
      cyclesExtMap k R' n (cyclesPrecomp k R R' φ.hom n f)
    rw [cyclesExtMap_apply, cyclesExtMap_apply, map_zsmul]
    exact congrArg (resolutionSign n • ·) (ProjectiveResolution.mk₀_comp_extMk f.1 (n+1) rfl f.2 φ)

lemma homologyExtIso_precomp {g : X' ⟶ X}
    (φ : ProjectiveResolution.Hom R' R g) (n : ℕ) :
    HomologicalComplex.homologyMap (homPrecomp k R R' (Y := Y) φ.hom) n ≫
      (homologyExtIso k R' Y n).hom =
      (homologyExtIso k R Y n).hom ≫ ((Abelian.linearExtFunctor k C n).map g.op).app Y := by
  have hnat := (HomologicalComplex.natIsoSc' (ModuleCat k) (.up ℕ) (n-1) n (n+1)
    (prev_up_nat n) ((ComplexShape.up ℕ).next_eq' rfl)).hom.naturality
      (homPrecomp k R R' (Y := Y) φ.hom)
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat k)).map hnat
  simp only [Functor.map_comp] at h
  dsimp only [homologyExtIso, Iso.trans_hom, Functor.mapIso_hom]
  change HomologicalComplex.homologyMap (homPrecomp k R R' (Y := Y) φ.hom) n ≫
    (ShortComplex.homologyFunctor (ModuleCat k)).map
      ((R'.complex.linearYonedaObj k Y).isoSc' (n-1) n (n+1) _ _).hom = _ at h
  erw [← Category.assoc, h, Category.assoc]
  erw [(homologyPrecompData k R R' φ n).homologyMap_comm]
  simp only [Category.assoc]
  rfl

end AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.ProjectiveBridge


namespace AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
open Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
variable (k : Type u) (G : Type v) [CommRing k] [Group G] (N : Subgroup G) [N.Normal]

/-- The actual HA-A02 homogeneous-cochain comparison, on representations. -/
def homogeneousDerivedCohomologyIso (j : ℕ) :
    Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.repHomogeneousCohomology.{u,v,w}
      k N j ≅
    Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.repDerivedCohomology.{u,v,w}
      k N j := by
  let E : Rep.{max u v w} k N ≌
      Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.GroupModule.{u,v,w} k N :=
    Rep.equivalenceModuleMonoidAlgebra
  let F := Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.repHomogeneousCohomology.{u,v,w}
    k N j
  exact (Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight E.unitIso F ≪≫
    Functor.isoWhiskerLeft E.functor
      (AdvancedHomologicalAlgebra.GroupCochainComparison.Large.cohomologyIso.{u,v,w} k N j).symm

private def homogeneousCohomologyIso (M : Rep.{max u v w} k G) (j : ℕ) :
    (homogeneousComplex.{u,v,w} k G N M).homology j ≅
      ((Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.repDerivedCohomology.{u,v,w}
        k N j).obj (Rep.res N.subtype M)) :=
  (homogeneousDerivedCohomologyIso.{u,v,w} k G N j).app (Rep.res N.subtype M)

/-- The homogeneous quotient action transported to the HA-A01 derived invariants. -/
def ordinaryCohomologyRepresentation (M : Rep.{max u v w} k G) (j : ℕ) :
    Representation k (G ⧸ N)
      ((Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large.repDerivedCohomology.{u,v,w}
        k N j).obj (Rep.res N.subtype M)) where
  toFun q :=
    (homogeneousCohomologyIso.{u,v,w} k G N M j).hom.hom ∘ₗ
      quotientCohomologyRepresentation.{u,v,w} k G N M j q ∘ₗ
        (homogeneousCohomologyIso.{u,v,w} k G N M j).inv.hom
  map_one' := by
    rw [map_one]
    ext x
    exact congrArg (fun f => f.hom x) (homogeneousCohomologyIso.{u,v,w} k G N M j).inv_hom_id
  map_mul' q r := by
    rw [map_mul]
    ext x
    simp only [LinearMap.comp_apply, Module.End.mul_apply]
    have hi (y : (homogeneousComplex.{u,v,w} k G N M).homology j) :
        (homogeneousCohomologyIso.{u,v,w} k G N M j).inv.hom
          ((homogeneousCohomologyIso.{u,v,w} k G N M j).hom.hom y) = y :=
      congrArg (fun f => f.hom y) (homogeneousCohomologyIso.{u,v,w} k G N M j).hom_inv_id
    rw [hi]

set_option maxRecDepth 4096 in
theorem ordinaryCohomologyActionFor : OrdinaryCohomologyAction.{u,v,w} k G N := by
  refine ⟨homogeneousDerivedCohomologyIso.{u,v,w} k G N, ?_⟩
  intro M
  refine ⟨homogeneousAction.{u,v,w} k G N M, homogeneousAction_formula.{u,v,w} k G N M, ?_⟩
  intro j
  refine ⟨ordinaryCohomologyRepresentation.{u,v,w} k G N M j, ?_⟩
  intro g x
  change (homogeneousCohomologyIso.{u,v,w} k G N M j).hom.hom
    (quotientCohomologyRepresentation.{u,v,w} k G N M j (QuotientGroup.mk' N g)
      ((homogeneousCohomologyIso.{u,v,w} k G N M j).inv.hom
        ((homogeneousCohomologyIso.{u,v,w} k G N M j).hom.hom x))) = _
  have hi : (homogeneousCohomologyIso.{u,v,w} k G N M j).inv.hom
      ((homogeneousCohomologyIso.{u,v,w} k G N M j).hom.hom x) = x :=
    congrArg (fun f => f.hom x) (homogeneousCohomologyIso.{u,v,w} k G N M j).hom_inv_id
  rw [hi]
  rfl


instance induction_preservesProjectives : (induction.{u,v,w} k G N).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (Rep.indResAdjunction k N.subtype)

abbrev inducedTrivial : Rep.{max u v w} k G := Rep.ind N.subtype (GroupBar.Large.trivial.{u,v,w} k N)

def inducedBarResolution : ProjectiveResolution (inducedTrivial.{u,v,w} k G N) :=
  (induction.{u,v,w} k G N).mapProjectiveResolution (barResolution.{u,v,w} k N)

/-- Frobenius reciprocity in each degree of the bar cochain complex. -/
def inducedBarHomIso (M : Rep.{max u v w} k G) :
    (inducedBarResolution.{u,v,w} k G N).complex.linearYonedaObj k M ≅ homogeneousComplex.{u,v,w} k G N M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (Rep.indResHomEquiv N.subtype (GroupBar.Large.B.{u,v,w} k N j) M).toModuleIso) (by
      intro i j hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      change (Rep.indResHomEquiv N.subtype (GroupBar.Large.B.{u,v,w} k N (i+1)) M)
          (Rep.indMap N.subtype (GroupBar.Large.boundary.{u,v,w} k N i) ≫ φ) =
        GroupBar.Large.boundary.{u,v,w} k N i ≫ ((Rep.indResHomEquiv N.subtype (GroupBar.Large.B.{u,v,w} k N i) M) φ)
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      simp [Rep.indResHomEquiv, Rep.indMap])

abbrev inducedUnit (A : Rep.{max u v w} k N) : A ⟶ Rep.res N.subtype (Rep.ind N.subtype A) :=
  (Rep.indResHomEquiv N.subtype A (Rep.ind N.subtype A)) (𝟙 _)

lemma conjugateCochain_natural_degree {M L : Rep.{max u v w} k G} (f : M ⟶ L)
    (g : G) (j : ℕ) (φ : GroupBar.Large.B.{u,v,w} k N j ⟶ Rep.res N.subtype M) :
    conjugateCochain.{u,v,w} k G N M g j φ ≫ Rep.resMap N.subtype f =
      conjugateCochain.{u,v,w} k G N L g j (φ ≫ Rep.resMap N.subtype f) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext x
  exact Rep.hom_comm_apply f g _

/-- The G-linear morphism representing conjugation on homogeneous cochains. -/
def inducedConjugationDegree (g : G) (j : ℕ) :
    Rep.ind N.subtype (GroupBar.Large.B.{u,v,w} k N j) ⟶ Rep.ind N.subtype (GroupBar.Large.B.{u,v,w} k N j) :=
  (Rep.indResHomEquiv N.subtype _ _).symm
    (conjugateCochain.{u,v,w} k G N (Rep.ind N.subtype (GroupBar.Large.B.{u,v,w} k N j)) g j
      (inducedUnit.{u,v,w} k G N (GroupBar.Large.B.{u,v,w} k N j)))

lemma inducedConjugationDegree_represents (g : G) (j : ℕ) (M : Rep.{max u v w} k G)
    (f : Rep.ind N.subtype (GroupBar.Large.B.{u,v,w} k N j) ⟶ M) :
    (Rep.indResHomEquiv N.subtype _ M) (inducedConjugationDegree.{u,v,w} k G N g j ≫ f) =
      conjugateCochain.{u,v,w} k G N M g j ((Rep.indResHomEquiv N.subtype _ M) f) := by
  change (Rep.indResAdjunction.{max u v w} k N.subtype).homEquiv _ _
      (inducedConjugationDegree.{u,v,w} k G N g j ≫ f) = _
  rw [(Rep.indResAdjunction.{max u v w} k N.subtype).homEquiv_naturality_right]
  change (Rep.indResHomEquiv N.subtype _ _) (inducedConjugationDegree.{u,v,w} k G N g j) ≫
    Rep.resMap N.subtype f = _
  rw [inducedConjugationDegree, LinearEquiv.apply_symm_apply]
  exact conjugateCochain_natural_degree.{u,v,w} k G N f g j _

lemma conjugateCochain_boundary (M : Rep.{max u v w} k G) (g : G) (j : ℕ)
    (φ : GroupBar.Large.B.{u,v,w} k N j ⟶ Rep.res N.subtype M) :
    conjugateCochain.{u,v,w} k G N M g (j+1) (GroupBar.Large.boundary.{u,v,w} k N j ≫ φ) =
      GroupBar.Large.boundary.{u,v,w} k N j ≫ conjugateCochain.{u,v,w} k G N M g j φ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun y => M.ρ g (φ.hom y))
    (LinearMap.congr_fun (conjugateBar_boundary.{u,v,w} k G N g j).symm x)

/-- The representing G-linear endomorphisms commute with the bar differential. -/
lemma inducedConjugationDegree_boundary (g : G) (j : ℕ) :
    inducedConjugationDegree.{u,v,w} k G N g (j+1) ≫ Rep.indMap N.subtype (GroupBar.Large.boundary.{u,v,w} k N j) =
      Rep.indMap N.subtype (GroupBar.Large.boundary.{u,v,w} k N j) ≫ inducedConjugationDegree.{u,v,w} k G N g j := by
  apply (Rep.indResHomEquiv N.subtype _ _).injective
  rw [inducedConjugationDegree_represents]
  have hnat := (Rep.indResAdjunction.{max u v w} k N.subtype).homEquiv_naturality_left
    (GroupBar.Large.boundary.{u,v,w} k N j) (inducedConjugationDegree.{u,v,w} k G N g j)
  change (Rep.indResHomEquiv N.subtype _ _)
      (Rep.indMap N.subtype (GroupBar.Large.boundary.{u,v,w} k N j) ≫ inducedConjugationDegree.{u,v,w} k G N g j) = _ at hnat
  rw [hnat]
  change conjugateCochain.{u,v,w} k G N _ g (j+1)
      ((Rep.indResHomEquiv N.subtype _ _) (Rep.indMap N.subtype (GroupBar.Large.boundary.{u,v,w} k N j))) =
    GroupBar.Large.boundary.{u,v,w} k N j ≫
      (Rep.indResHomEquiv N.subtype _ _) (inducedConjugationDegree.{u,v,w} k G N g j)
  rw [inducedConjugationDegree, LinearEquiv.apply_symm_apply]
  have hunit : (Rep.indResHomEquiv N.subtype _ _) (Rep.indMap N.subtype (GroupBar.Large.boundary.{u,v,w} k N j)) =
      GroupBar.Large.boundary.{u,v,w} k N j ≫ inducedUnit.{u,v,w} k G N (GroupBar.Large.B.{u,v,w} k N j) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    simp [Rep.indResHomEquiv, Rep.indMap, inducedUnit]
  rw [hunit]
  exact conjugateCochain_boundary.{u,v,w} k G N _ g j _

def inducedConjugation (g : G) :
    ((induction.{u,v,w} k G N).mapHomologicalComplex (.down ℕ)).obj (GroupBar.Large.complex.{u,v,w} k N) ⟶
      ((induction.{u,v,w} k G N).mapHomologicalComplex (.down ℕ)).obj (GroupBar.Large.complex.{u,v,w} k N) where
  f j := inducedConjugationDegree.{u,v,w} k G N g j
  comm' i j hij := by
    subst i
    exact inducedConjugationDegree_boundary.{u,v,w} k G N g j

/-- On degree-zero invariants, conjugation is the coefficient action. -/
def conjugateInvariant (M : Rep.{max u v w} k G) (g : G)
    (φ : GroupBar.Large.trivial.{u,v,w} k N ⟶ Rep.res N.subtype M) :
    GroupBar.Large.trivial.{u,v,w} k N ⟶ Rep.res N.subtype M :=
  Rep.ofHom ⟨M.ρ g ∘ₗ φ.hom.toLinearMap, fun b => by
    apply LinearMap.ext
    intro r
    let b' : N := MulAut.conjNormal g⁻¹ b
    have hb : (b : G) * g = g * (b' : G) := by
      simp [b', mul_assoc]
    have hφ := Rep.hom_comm_apply φ b' r
    change φ.hom r = M.ρ (b' : G) (φ.hom r) at hφ
    change M.ρ g (φ.hom r) = M.ρ (b : G) (M.ρ g (φ.hom r))
    rw [← Module.End.mul_apply, ← map_mul, hb, map_mul, Module.End.mul_apply, ← hφ]⟩

lemma conjugateInvariant_natural {M L : Rep.{max u v w} k G} (f : M ⟶ L) (g : G)
    (φ : GroupBar.Large.trivial.{u,v,w} k N ⟶ Rep.res N.subtype M) :
    conjugateInvariant.{u,v,w} k G N M g φ ≫ Rep.resMap N.subtype f =
      conjugateInvariant.{u,v,w} k G N L g (φ ≫ Rep.resMap N.subtype f) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro r
  exact Rep.hom_comm_apply f g _

/-- The G-linear map of the induced trivial module representing coefficient action. -/
def inducedInvariantAction (g : G) :
    Rep.ind N.subtype (GroupBar.Large.trivial.{u,v,w} k N) ⟶ Rep.ind N.subtype (GroupBar.Large.trivial.{u,v,w} k N) :=
  (Rep.indResHomEquiv N.subtype _ _).symm
    (conjugateInvariant.{u,v,w} k G N (Rep.ind N.subtype (GroupBar.Large.trivial.{u,v,w} k N)) g
      (inducedUnit.{u,v,w} k G N (GroupBar.Large.trivial.{u,v,w} k N)))

lemma inducedInvariantAction_represents (g : G) (M : Rep.{max u v w} k G)
    (f : Rep.ind N.subtype (GroupBar.Large.trivial.{u,v,w} k N) ⟶ M) :
    (Rep.indResHomEquiv N.subtype _ M) (inducedInvariantAction.{u,v,w} k G N g ≫ f) =
      conjugateInvariant.{u,v,w} k G N M g ((Rep.indResHomEquiv N.subtype _ M) f) := by
  change (Rep.indResAdjunction.{max u v w} k N.subtype).homEquiv _ _
      (inducedInvariantAction.{u,v,w} k G N g ≫ f) = _
  rw [(Rep.indResAdjunction.{max u v w} k N.subtype).homEquiv_naturality_right]
  change (Rep.indResHomEquiv N.subtype _ _) (inducedInvariantAction.{u,v,w} k G N g) ≫
    Rep.resMap N.subtype f = _
  rw [inducedInvariantAction, LinearEquiv.apply_symm_apply]
  exact conjugateInvariant_natural.{u,v,w} k G N f g _

lemma conjugateCochain_augmentation (M : Rep.{max u v w} k G) (g : G)
    (φ : GroupBar.Large.trivial.{u,v,w} k N ⟶ Rep.res N.subtype M) :
    conjugateCochain.{u,v,w} k G N M g 0 (GroupBar.Large.augmentation.{u,v,w} k N ≫ φ) =
      GroupBar.Large.augmentation.{u,v,w} k N ≫ conjugateInvariant.{u,v,w} k G N M g φ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change (conjugateCochain.{u,v,w} k G N M g 0 (GroupBar.Large.augmentation.{u,v,w} k N ≫ φ)).hom
      (GroupBar.Large.single.{u,v,w} k N c.down 1) = _
  rw [conjugateCochain_single.{u,v,w} k G N M g 0 _ c.down 1]
  change M.ρ g (φ.hom (ULift.up (GroupBar.Large.ε.{u,v,w} k N (GroupBar.Large.single.{u,v,w} k N
      (fun i => MulAut.conjNormal g⁻¹ (c.down i)) 1)))) =
    M.ρ g (φ.hom (ULift.up (GroupBar.Large.ε.{u,v,w} k N (GroupBar.Large.single.{u,v,w} k N c.down 1))))
  rw [GroupBar.Large.augmentation_single, GroupBar.Large.augmentation_single]

/-- The induced chain action lifts its representing action on Ind_N^G(k). -/
lemma inducedConjugation_augmentation (g : G) :
    inducedConjugationDegree.{u,v,w} k G N g 0 ≫ Rep.indMap N.subtype (GroupBar.Large.augmentation.{u,v,w} k N) =
      Rep.indMap N.subtype (GroupBar.Large.augmentation.{u,v,w} k N) ≫ inducedInvariantAction.{u,v,w} k G N g := by
  apply (Rep.indResHomEquiv N.subtype _ _).injective
  rw [inducedConjugationDegree_represents]
  have hnat := (Rep.indResAdjunction.{max u v w} k N.subtype).homEquiv_naturality_left
    (GroupBar.Large.augmentation.{u,v,w} k N) (inducedInvariantAction.{u,v,w} k G N g)
  change (Rep.indResHomEquiv N.subtype _ _)
      (Rep.indMap N.subtype (GroupBar.Large.augmentation.{u,v,w} k N) ≫ inducedInvariantAction.{u,v,w} k G N g) = _ at hnat
  rw [hnat]
  change conjugateCochain.{u,v,w} k G N _ g 0
      ((Rep.indResHomEquiv N.subtype _ _) (Rep.indMap N.subtype (GroupBar.Large.augmentation.{u,v,w} k N))) =
    GroupBar.Large.augmentation.{u,v,w} k N ≫
      (Rep.indResHomEquiv N.subtype _ _) (inducedInvariantAction.{u,v,w} k G N g)
  rw [inducedInvariantAction, LinearEquiv.apply_symm_apply]
  have hunit : (Rep.indResHomEquiv N.subtype _ _)
      (Rep.indMap N.subtype (GroupBar.Large.augmentation.{u,v,w} k N)) =
      GroupBar.Large.augmentation.{u,v,w} k N ≫ inducedUnit.{u,v,w} k G N (GroupBar.Large.trivial.{u,v,w} k N) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    simp [Rep.indResHomEquiv, Rep.indMap, inducedUnit]
  rw [hunit]
  exact conjugateCochain_augmentation.{u,v,w} k G N _ g _


/-- Pullback on Hom_G(P,-) along the induced bar chain action. -/
def inducedHomAction (M : Rep.{max u v w} k G) (g : G) :
    (inducedBarResolution.{u,v,w} k G N).complex.linearYonedaObj k M ⟶
      (inducedBarResolution.{u,v,w} k G N).complex.linearYonedaObj k M :=
  (HomologicalComplex.unopFunctor (ModuleCat k) (ComplexShape.down ℕ)).map
    (((((linearYoneda k (Rep k G)).obj M).rightOp.mapHomologicalComplex _).map
      (inducedConjugation.{u,v,w} k G N g)).op)

lemma inducedBarHomIso_action (M : Rep.{max u v w} k G) (g : G) :
    inducedHomAction.{u,v,w} k G N M g ≫ (inducedBarHomIso.{u,v,w} k G N M).hom =
      (inducedBarHomIso.{u,v,w} k G N M).hom ≫ (homogeneousAction.{u,v,w} k G N M g).asHom := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact inducedConjugationDegree_represents.{u,v,w} k G N g j M f

/-- The explicit bar chain action lifts the induced trivial-module action. -/
def inducedConjugationHom (g : G) :
    ProjectiveResolution.Hom (inducedBarResolution.{u,v,w} k G N)
      (inducedBarResolution.{u,v,w} k G N) (inducedInvariantAction.{u,v,w} k G N g) where
  hom := inducedConjugation.{u,v,w} k G N g
  hom_f_zero_comp_π_f_zero := by
    change inducedConjugationDegree.{u,v,w} k G N g 0 ≫ Rep.indMap N.subtype (GroupBar.Large.augmentation.{u,v,w} k N) =
      Rep.indMap N.subtype (GroupBar.Large.augmentation.{u,v,w} k N) ≫ inducedInvariantAction.{u,v,w} k G N g
    exact inducedConjugation_augmentation.{u,v,w} k G N g


abbrev quotientForget : Rep.{max u v w} k (G ⧸ N) ⥤ ModuleCat.{max u v w} k := forget₂ _ _

/-- Evaluation at 1 identifies maps from the trivial representation with invariants. -/
def trivialHomInvariantEquiv (M : Rep.{max u v w} k G) :
    (GroupBar.Large.trivial.{u,v,w} k N ⟶ Rep.res N.subtype M) ≃ₗ[k]
      (quotientForget.{u,v,w} k G N).obj ((normalInvariants.{u,v,w} k G N).obj M) where
  toFun φ := ⟨φ.hom (ULift.up (1 : k)), fun b => by
    have h := Rep.hom_comm_apply φ b (ULift.up (1 : k))
    exact h.symm⟩
  invFun m := Rep.ofHom ⟨(ULift.moduleEquiv : ULift.{max v w} k ≃ₗ[k] k).toLinearMap.smulRight m.val, fun b => by
    apply LinearMap.ext
    intro r
    change r.down • m.val = M.ρ (b : G) (r.down • m.val)
    have hm := m.property b
    change M.ρ (b : G) m.val = m.val at hm
    rw [map_smul, hm]⟩
  left_inv φ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro r
    change r.down • φ.hom (ULift.up (1 : k)) = φ.hom r
    rw [← map_smul]
    congr 1
    exact ULift.ext (mul_one r.down)
  right_inv m := by apply Subtype.ext; exact one_smul k m.val
  map_add' φ ψ := by apply Subtype.ext; rfl
  map_smul' r φ := by apply Subtype.ext; rfl

/-- Frobenius reciprocity followed by evaluation at 1. -/
def inducedInvariantEquiv (M : Rep.{max u v w} k G) :
    (inducedTrivial.{u,v,w} k G N ⟶ M) ≃ₗ[k]
      (quotientForget.{u,v,w} k G N).obj ((normalInvariants.{u,v,w} k G N).obj M) :=
  (Rep.indResHomEquiv N.subtype _ M).trans (trivialHomInvariantEquiv.{u,v,w} k G N M)

lemma inducedInvariantEquiv_natural {M L : Rep.{max u v w} k G} (f : M ⟶ L)
    (φ : inducedTrivial.{u,v,w} k G N ⟶ M) :
    inducedInvariantEquiv.{u,v,w} k G N L (φ ≫ f) =
      ((normalInvariants.{u,v,w} k G N).map f).hom (inducedInvariantEquiv.{u,v,w} k G N M φ) := by
  apply Subtype.ext
  rfl

lemma inducedInvariantEquiv_action (M : Rep.{max u v w} k G) (g : G)
    (φ : inducedTrivial.{u,v,w} k G N ⟶ M) :
    inducedInvariantEquiv.{u,v,w} k G N M (inducedInvariantAction.{u,v,w} k G N g ≫ φ) =
      ((normalInvariants.{u,v,w} k G N).obj M).ρ (QuotientGroup.mk' N g)
        (inducedInvariantEquiv.{u,v,w} k G N M φ) := by
  dsimp only [inducedInvariantEquiv, LinearEquiv.trans_apply]
  rw [inducedInvariantAction_represents]
  apply Subtype.ext
  rfl

abbrev inducedInvariantHomFunctor : Rep.{max u v w} k G ⥤ ModuleCat.{max u v w} k :=
  (linearCoyoneda k (Rep.{max u v w} k G)).obj (Opposite.op (inducedTrivial.{u,v,w} k G N))

abbrev inducedInvariantHomComplex (K : CochainComplex (Rep.{max u v w} k G) ℕ) :=
  ((inducedInvariantHomFunctor.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).obj K

abbrev underlyingInvariantComplex (K : CochainComplex (Rep.{max u v w} k G) ℕ) :=
  ((quotientForget.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).obj
    (((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).obj K)

/-- The two ordinary cochain models agree by Frobenius reciprocity. -/
def inducedInvariantHomIso (K : CochainComplex (Rep.{max u v w} k G) ℕ) :
    inducedInvariantHomComplex.{u,v,w} k G N K ≅ underlyingInvariantComplex.{u,v,w} k G N K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (inducedInvariantEquiv.{u,v,w} k G N (K.X j)).toModuleIso) (by
      intro i j hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      exact inducedInvariantEquiv_natural.{u,v,w} k G N (K.d i j) φ)

lemma inducedInvariantHomIso_natural {K L : CochainComplex (Rep.{max u v w} k G) ℕ} (f : K ⟶ L) :
    ((inducedInvariantHomFunctor.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).map f ≫
      (inducedInvariantHomIso.{u,v,w} k G N L).hom =
    (inducedInvariantHomIso.{u,v,w} k G N K).hom ≫
      ((quotientForget.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).map
        (((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).map f) := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact inducedInvariantEquiv_natural.{u,v,w} k G N (f.f j) φ

/-- Every group element acts as a natural endomorphism of the forgetful functor. -/
def quotientForgetAction (q : G ⧸ N) : quotientForget.{u,v,w} k G N ⟶ quotientForget.{u,v,w} k G N where
  app M := ModuleCat.ofHom (M.ρ q)
  naturality {M L} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Rep.hom_comm_apply f q x).symm

/-- Precomposition by the representing endomorphism on Ind_N^G(k). -/
def inducedInvariantHomAction (K : CochainComplex (Rep.{max u v w} k G) ℕ) (g : G) :
    inducedInvariantHomComplex.{u,v,w} k G N K ⟶ inducedInvariantHomComplex.{u,v,w} k G N K :=
  (((linearCoyoneda k (Rep.{max u v w} k G)).map
      (inducedInvariantAction.{u,v,w} k G N g).op).mapHomologicalComplex (.up ℕ)).app K

lemma inducedInvariantHomIso_action (K : CochainComplex (Rep.{max u v w} k G) ℕ) (g : G) :
    inducedInvariantHomAction.{u,v,w} k G N K g ≫ (inducedInvariantHomIso.{u,v,w} k G N K).hom =
      (inducedInvariantHomIso.{u,v,w} k G N K).hom ≫
        ((quotientForgetAction.{u,v,w} k G N (QuotientGroup.mk' N g)).mapHomologicalComplex (.up ℕ)).app
          (((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact inducedInvariantEquiv_action.{u,v,w} k G N (K.X j) g φ

/-- Exact forgetting commutes canonically with homology. -/
def quotientForgetHomologyIso (K : CochainComplex (Rep.{max u v w} k (G ⧸ N)) ℕ) (j : ℕ) :
    (((quotientForget.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).obj K).homology j ≅
      (quotientForget.{u,v,w} k G N).obj (K.homology j) :=
  (K.sc j).mapHomologyIso (quotientForget.{u,v,w} k G N)

lemma quotientForgetHomologyIso_natural {K L : CochainComplex (Rep.{max u v w} k (G ⧸ N)) ℕ}
    (f : K ⟶ L) (j : ℕ) :
    HomologicalComplex.homologyMap
        (((quotientForget.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).map f) j ≫
      (quotientForgetHomologyIso.{u,v,w} k G N L j).hom =
    (quotientForgetHomologyIso.{u,v,w} k G N K j).hom ≫
      (quotientForget.{u,v,w} k G N).map (HomologicalComplex.homologyMap f j) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) j).map f) (quotientForget.{u,v,w} k G N)

lemma quotientForgetHomologyIso_action (K : CochainComplex (Rep.{max u v w} k (G ⧸ N)) ℕ)
    (q : G ⧸ N) (j : ℕ) :
    HomologicalComplex.homologyMap
        (((quotientForgetAction.{u,v,w} k G N q).mapHomologicalComplex (.up ℕ)).app K) j ≫
      (quotientForgetHomologyIso.{u,v,w} k G N K j).hom =
    (quotientForgetHomologyIso.{u,v,w} k G N K j).hom ≫ ModuleCat.ofHom ((K.homology j).ρ q) := by
  have h := NatTrans.app_homology (quotientForgetAction.{u,v,w} k G N q) (K.sc j)
  change ModuleCat.ofHom ((K.homology j).ρ q) =
    (quotientForgetHomologyIso.{u,v,w} k G N K j).inv ≫
      HomologicalComplex.homologyMap
        (((quotientForgetAction.{u,v,w} k G N q).mapHomologicalComplex (.up ℕ)).app K) j ≫
      (quotientForgetHomologyIso.{u,v,w} k G N K j).hom at h
  rw [h]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Hom(T,I) computes the actual homology object of the Q-invariants complex. -/
def inducedInvariantHomologyIso (K : CochainComplex (Rep.{max u v w} k G) ℕ) (j : ℕ) :
    (inducedInvariantHomComplex.{u,v,w} k G N K).homology j ≅
      (quotientForget.{u,v,w} k G N).obj
        ((((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).obj K).homology j) :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) j).mapIso
      (inducedInvariantHomIso.{u,v,w} k G N K) ≪≫
    quotientForgetHomologyIso.{u,v,w} k G N
      (((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).obj K) j

lemma inducedInvariantHomologyIso_natural {K L : CochainComplex (Rep.{max u v w} k G) ℕ}
    (f : K ⟶ L) (j : ℕ) :
    HomologicalComplex.homologyMap
        (((inducedInvariantHomFunctor.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).map f) j ≫
      (inducedInvariantHomologyIso.{u,v,w} k G N L j).hom =
    (inducedInvariantHomologyIso.{u,v,w} k G N K j).hom ≫
      (quotientForget.{u,v,w} k G N).map (HomologicalComplex.homologyMap
        (((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).map f) j) := by
  have h := congrArg (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) j).map
    (inducedInvariantHomIso_natural.{u,v,w} k G N f)
  simp only [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp] at h
  dsimp only [inducedInvariantHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [HomologicalComplex.homologyFunctor_map]
  erw [← Category.assoc, h, Category.assoc,
    quotientForgetHomologyIso_natural]
  rfl

lemma inducedInvariantHomologyIso_action (K : CochainComplex (Rep.{max u v w} k G) ℕ)
    (g : G) (j : ℕ) :
    HomologicalComplex.homologyMap (inducedInvariantHomAction.{u,v,w} k G N K g) j ≫
      (inducedInvariantHomologyIso.{u,v,w} k G N K j).hom =
    (inducedInvariantHomologyIso.{u,v,w} k G N K j).hom ≫ ModuleCat.ofHom
      (((((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).obj K).homology j).ρ
        (QuotientGroup.mk' N g)) := by
  have h := congrArg (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) j).map
    (inducedInvariantHomIso_action.{u,v,w} k G N K g)
  simp only [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp] at h
  dsimp only [inducedInvariantHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [HomologicalComplex.homologyFunctor_map]
  erw [← Category.assoc, h, Category.assoc, quotientForgetHomologyIso_action]
  rfl


local instance groupHasExt : HasExt.{max u v w} (Rep.{max u v w} k G) := by
  let E : Rep.{max u v w} k G ≌ ModuleCat.{max u v w} k[G] :=
    Rep.equivalenceModuleMonoidAlgebra
  let : EnoughProjectives (Rep.{max u v w} k G) :=
    E.enoughProjectives_iff.mpr ModuleCat.enoughProjectives
  exact CategoryTheory.hasExt_of_enoughProjectives.{max u v w} (Rep.{max u v w} k G)

open AdvancedHomologicalAlgebra.GroupCochainComparison.ResolutionBridge

lemma inducedBarHomIso_postcomp {M L : Rep.{max u v w} k G} (f : M ⟶ L) :
    homPostcomp k (inducedBarResolution.{u,v,w} k G N) f ≫ (inducedBarHomIso.{u,v,w} k G N L).hom =
      (inducedBarHomIso.{u,v,w} k G N M).hom ≫ coefficientCochainMap.{u,v,w} k G N f := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (Rep.indResHomEquiv N.subtype (GroupBar.Large.B.{u,v,w} k N j) L) (φ ≫ f) =
    ((Rep.indResHomEquiv N.subtype (GroupBar.Large.B.{u,v,w} k N j) M) φ) ≫ Rep.resMap N.subtype f
  rfl

/-- Homogeneous bar cohomology as Ext_G(Ind_N^G k,M). -/
def homogeneousExtIso (M : Rep.{max u v w} k G) (j : ℕ) :
    (homogeneousComplex.{u,v,w} k G N M).homology j ≅
      ModuleCat.of k (Abelian.Ext (inducedTrivial.{u,v,w} k G N) M j) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) j).mapIso
      (inducedBarHomIso.{u,v,w} k G N M)).symm ≪≫
    homologyExtIso k (inducedBarResolution.{u,v,w} k G N) M j

lemma homogeneousExtIso_action (M : Rep.{max u v w} k G) (g : G) (j : ℕ) :
    HomologicalComplex.homologyMap (homogeneousAction.{u,v,w} k G N M g).asHom j ≫
      (homogeneousExtIso.{u,v,w} k G N M j).hom =
    (homogeneousExtIso.{u,v,w} k G N M j).hom ≫
      ((Abelian.linearExtFunctor k (Rep.{max u v w} k G) j).map (inducedInvariantAction.{u,v,w} k G N g).op).app M := by
  let e := (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) j).mapIso
    (inducedBarHomIso.{u,v,w} k G N M)
  have ha := congrArg (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) j).map
    (inducedBarHomIso_action.{u,v,w} k G N M g)
  simp only [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp] at ha
  change HomologicalComplex.homologyMap (inducedHomAction.{u,v,w} k G N M g) j ≫ e.hom =
    e.hom ≫ HomologicalComplex.homologyMap (homogeneousAction.{u,v,w} k G N M g).asHom j at ha
  have hp := ProjectiveBridge.homologyExtIso_precomp k (inducedBarResolution.{u,v,w} k G N)
    (inducedBarResolution.{u,v,w} k G N) (Y := M) (inducedConjugationHom.{u,v,w} k G N g) j
  change HomologicalComplex.homologyMap (inducedHomAction.{u,v,w} k G N M g) j ≫ _ = _ at hp
  change _ ≫ (e.inv ≫ _) = (e.inv ≫ _) ≫ _
  apply (cancel_epi e.hom).mp
  simp only [Category.assoc]
  rw [← reassoc_of% ha]
  simp only [Iso.hom_inv_id_assoc]
  exact hp

lemma homogeneousExtIso_natural {M L : Rep.{max u v w} k G} (f : M ⟶ L) (j : ℕ) :
    HomologicalComplex.homologyMap (coefficientCochainMap.{u,v,w} k G N f) j ≫
      (homogeneousExtIso.{u,v,w} k G N L j).hom =
    (homogeneousExtIso.{u,v,w} k G N M j).hom ≫
      (Abelian.linearExtFunctorObj k (inducedTrivial.{u,v,w} k G N) j).map f := by
  let eM := (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) j).mapIso
    (inducedBarHomIso.{u,v,w} k G N M)
  let eL := (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) j).mapIso
    (inducedBarHomIso.{u,v,w} k G N L)
  have ha := congrArg (HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) j).map
    (inducedBarHomIso_postcomp.{u,v,w} k G N f)
  simp only [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp] at ha
  change HomologicalComplex.homologyMap (homPostcomp k (inducedBarResolution.{u,v,w} k G N) f) j ≫ eL.hom =
    eM.hom ≫ HomologicalComplex.homologyMap (coefficientCochainMap.{u,v,w} k G N f) j at ha
  have hp := homologyExtIso_natural k (inducedBarResolution.{u,v,w} k G N) f j
  change _ ≫ (eL.inv ≫ _) = (eM.inv ≫ _) ≫ _
  apply (cancel_epi eM.hom).mp
  simp only [Category.assoc]
  rw [← reassoc_of% ha]
  simp only [Iso.hom_inv_id_assoc]
  exact hp

/-- The natural underlying-module comparison for every G-injective resolution. -/
def comparisonModuleIso (M : Rep.{max u v w} k G) (j : ℕ) (I : InjectiveResolution M) :
    (homogeneousComplex.{u,v,w} k G N M).homology j ≅
      (quotientForget.{u,v,w} k G N).obj ((invariantResolutionComplex.{u,v,w} k G N M I).homology j) :=
  homogeneousExtIso.{u,v,w} k G N M j ≪≫
    (InjectiveBridge.homologyExtIso k I (inducedTrivial.{u,v,w} k G N) j).symm ≪≫
    inducedInvariantHomologyIso.{u,v,w} k G N I.cocomplex j

lemma comparisonModuleIso_action (M : Rep.{max u v w} k G) (j : ℕ) (I : InjectiveResolution M) (g : G) :
    HomologicalComplex.homologyMap (homogeneousAction.{u,v,w} k G N M g).asHom j ≫
      (comparisonModuleIso.{u,v,w} k G N M j I).hom =
    (comparisonModuleIso.{u,v,w} k G N M j I).hom ≫
      ModuleCat.ofHom (((invariantResolutionComplex.{u,v,w} k G N M I).homology j).ρ (QuotientGroup.mk' N g)) := by
  let ei := InjectiveBridge.homologyExtIso k I (inducedTrivial.{u,v,w} k G N) j
  let α := ((Abelian.linearExtFunctor k (Rep.{max u v w} k G) j).map (inducedInvariantAction.{u,v,w} k G N g).op).app M
  let aI := HomologicalComplex.homologyMap (inducedInvariantHomAction.{u,v,w} k G N I.cocomplex g) j
  have hi := InjectiveBridge.homologyExtIso_precomp k I (inducedInvariantAction.{u,v,w} k G N g) j
  change aI ≫ ei.hom = ei.hom ≫ α at hi
  have hinv : α ≫ ei.inv = ei.inv ≫ aI := by
    apply (Iso.comp_inv_eq ei).mpr
    rw [Category.assoc, hi, Iso.inv_hom_id_assoc]
  dsimp only [comparisonModuleIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [← Category.assoc, homogeneousExtIso_action]
  simp only [Category.assoc]
  rw [reassoc_of% hinv, inducedInvariantHomologyIso_action]

lemma comparisonModuleIso_natural {M L : Rep.{max u v w} k G} (f : M ⟶ L) (j : ℕ)
    (I : InjectiveResolution M) (J : InjectiveResolution L) (φ : InjectiveResolution.Hom I J f) :
    HomologicalComplex.homologyMap (coefficientCochainMap.{u,v,w} k G N f) j ≫
      (comparisonModuleIso.{u,v,w} k G N L j J).hom =
    (comparisonModuleIso.{u,v,w} k G N M j I).hom ≫
      (quotientForget.{u,v,w} k G N).map (HomologicalComplex.homologyMap
        (((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).map φ.hom) j) := by
  let ei := InjectiveBridge.homologyExtIso k I (inducedTrivial.{u,v,w} k G N) j
  let ej := InjectiveBridge.homologyExtIso k J (inducedTrivial.{u,v,w} k G N) j
  let β := (Abelian.linearExtFunctorObj k (inducedTrivial.{u,v,w} k G N) j).map f
  let hφ := HomologicalComplex.homologyMap
    (InjectiveBridge.homPostcomp k I J φ.hom (inducedTrivial.{u,v,w} k G N)) j
  have hi := InjectiveBridge.homologyExtIso_natural k I J f φ (inducedTrivial.{u,v,w} k G N) j
  change hφ ≫ ej.hom = ei.hom ≫ β at hi
  have hinv : β ≫ ej.inv = ei.inv ≫ hφ := by
    apply (Iso.comp_inv_eq ej).mpr
    rw [Category.assoc, hi, Iso.inv_hom_id_assoc]
  dsimp only [comparisonModuleIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [← Category.assoc, homogeneousExtIso_natural]
  simp only [Category.assoc]
  rw [reassoc_of% hinv]
  have hv : hφ ≫ (inducedInvariantHomologyIso.{u,v,w} k G N J.cocomplex j).hom =
      (inducedInvariantHomologyIso.{u,v,w} k G N I.cocomplex j).hom ≫
        (quotientForget.{u,v,w} k G N).map (HomologicalComplex.homologyMap
          (((normalInvariants.{u,v,w} k G N).mapHomologicalComplex (.up ℕ)).map φ.hom) j) :=
    inducedInvariantHomologyIso_natural.{u,v,w} k G N φ.hom j
  erw [hv]

/-- The comparison is Q-linear for the actual descended cochain action. -/
def comparisonRepIso (M : Rep.{max u v w} k G) (j : ℕ) (I : InjectiveResolution M) :
    Rep.of (quotientCohomologyRepresentation.{u,v,w} k G N M j) ≅
      (invariantResolutionComplex.{u,v,w} k G N M I).homology j :=
  Rep.mkIso (.mk (comparisonModuleIso.{u,v,w} k G N M j I).toLinearEquiv (fun q => by
    induction q using QuotientGroup.induction_on with
    | H g =>
      apply LinearMap.ext
      intro x
      exact congrArg (fun t => t.hom x) (comparisonModuleIso_action.{u,v,w} k G N M j I g)))

/-- The comparison is natural in every coefficient map and every compatible map of resolutions. -/
theorem injectiveComparisonFor : InjectiveComparison.{u,v,w} k G N := by
  refine ⟨homogeneousAction.{u,v,w} k G N, quotientCohomologyRepresentation.{u,v,w} k G N, ?_, ?_,
    comparisonRepIso.{u,v,w} k G N, ?_⟩
  · intro M
    exact ⟨homogeneousAction_formula.{u,v,w} k G N M, subgroupAction_trivial.{u,v,w} k G N M⟩
  · intros M j g
    rfl
  · intros M L f j I J φ x
    exact congrArg (fun t => t.hom x) (comparisonModuleIso_natural.{u,v,w} k G N f j I J φ)


/-- All parts of HA-A05-Action, for arbitrary coefficient ring, group and normal subgroup. -/
theorem fullStatementFor : FullStatement.{u,v,w} k G N :=
  ⟨actionAndDescentFor.{u,v,w} k G N, ordinaryCohomologyActionFor.{u,v,w} k G N, invariantsAdjunctionFor.{u,v,w} k G N,
    restrictionInjectivesFor.{u,v,w} k G N, injectiveComparisonFor.{u,v,w} k G N⟩


theorem ordinaryCohomologyAction : ordinaryCohomologyActionExpected.{u,v,w} :=
  fun k G _ _ N _ => ordinaryCohomologyActionFor.{u,v,w} k G N

theorem injectiveComparison : injectiveComparisonExpected.{u,v,w} :=
  fun k G _ _ N _ => injectiveComparisonFor.{u,v,w} k G N

theorem fullStatement : fullStatementExpected.{u,v,w} :=
  fun k G _ _ N _ => fullStatementFor.{u,v,w} k G N

end AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction
