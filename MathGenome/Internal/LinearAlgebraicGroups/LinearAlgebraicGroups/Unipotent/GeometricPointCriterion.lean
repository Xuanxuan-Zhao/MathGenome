import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.GeometricPointCriterion
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Data.ZMod.QuotientGroup
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct MonoidAlgebra

universe u v
noncomputable section

namespace LinearAlgebraicGroups.Unipotent

open Specs.Unipotent

section PointFlags

variable {K : Type u} [Field K] [IsAlgClosed K] {Γ : Type v} [Group Γ]
  {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem irreducible_action_surjective (ρ : _root_.Representation K Γ V)
    [ρ.IsIrreducible] : Function.Surjective ρ.asAlgebraHom := by
  classical
  intro T
  let e := ρ.asModuleEquiv
  let T' : Module.End K ρ.asModule := e.symm.toLinearMap.comp (T.comp e.toLinearMap)
  -- Schur's lemma makes every linear map commute with the module endomorphisms.
  let S : Module.End (Module.End K[Γ] ρ.asModule) ρ.asModule :=
    { T'.toAddHom with
      map_smul' := fun a x ↦ by
        obtain ⟨t, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
          (A := K[Γ]) (V := ρ.asModule) K).surjective a
        change T' (t • x) = t • T' x
        exact T'.map_smul t x }
  let b := Module.finBasis K ρ.asModule
  obtain ⟨r, hr⟩ := jacobson_density S (Finset.univ.image b)
  refine ⟨r, b.ext ?_⟩
  intro i
  have h := hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))
  exact h.symm

private theorem irreducible_unipotent_action_trivial (ρ : _root_.Representation K Γ V)
    [ρ.IsIrreducible] (h : ∀ g, IsNilpotent (ρ g - 1)) (g : Γ) :
    ρ g = 1 := by
  let tr := LinearMap.trace K V
  have ht (a : Γ) : tr (ρ a - 1) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent (h a)).eq_zero
  have hz (a : Γ) : tr (ρ a * (ρ g - 1)) = 0 := by
    rw [mul_sub, mul_one, ← map_mul]
    have h₁ := ht (a * g)
    have h₂ := ht a
    simp only [map_sub, sub_eq_zero] at h₁ h₂ ⊢
    exact h₁.trans h₂.symm
  -- Every group element has the same trace as the identity. The difference is
  -- orthogonal to the span of the group under the trace pairing.
  have htrace (T : Module.End K V) : tr (T * (ρ g - 1)) = 0 := by
    obtain ⟨r, rfl⟩ := irreducible_action_surjective ρ T
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [add_mul, hx, hy]
    | single a c => simp [ρ.asAlgebraHom_single, hz]
  apply sub_eq_zero.mp
  ext x
  by_contra hn
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K hn
  have he : l.smulRight x * (ρ g - 1) = (l.comp (ρ g - 1)).smulRight x := by
    ext y
    rfl
  have h₀ := htrace (l.smulRight x)
  rw [he, LinearMap.trace_smulRight, LinearMap.comp_apply, hl] at h₀
  exact one_ne_zero h₀

private theorem exists_fixed_vector [Nontrivial V] (ρ : _root_.Representation K Γ V)
    (h : ∀ g, IsNilpotent (ρ g - 1)) :
    ∃ x : V, x ≠ 0 ∧ ∀ g, ρ g x = x := by
  let : IsArtinian K[Γ] ρ.asModule := isArtinian_of_tower K inferInstance
  have : Nontrivial ρ.asModule := ρ.asModuleEquiv.symm.injective.nontrivial
  obtain ⟨W, hW⟩ := IsAtomic.exists_atom (α := Submodule K[Γ] ρ.asModule)
  let S := Subrepresentation.ofSubmodule' W
  let σ := S.toRepresentation
  have eW : σ.asModule ≃ₗ[K[Γ]] W :=
    { AddEquiv.refl _ with
      map_smul' := fun a x ↦ by
        change (show W from a • x) = a • (show W from x)
        induction a using MonoidAlgebra.induction_linear with
        | zero =>
          rw [zero_smul, zero_smul]
          rfl
        | add a b ha hb =>
          rw [add_smul, add_smul]
          exact congrArg₂ (fun y z : W ↦ y + z) ha hb
        | single g c =>
          apply Subtype.ext
          change ((σ.asModuleEquiv (MonoidAlgebra.single g c • x)).val : V) =
            ρ.asModuleEquiv ((MonoidAlgebra.single g c : K[Γ]) • (show W from x).val)
          simp only [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single,
            LinearMap.smul_apply]
          rfl }
  have : IsSimpleModule K[Γ] W := isSimpleModule_iff_isAtom.mpr hW
  have : IsSimpleModule K[Γ] σ.asModule := IsSimpleModule.congr eW
  have : σ.IsIrreducible := (σ.irreducible_iff_isSimpleModule_asModule).mpr inferInstance
  have hσ (g : Γ) : IsNilpotent (σ g - 1) := by
    have hstab : Set.MapsTo (⇑(ρ g - 1 : Module.End K V)) S.toSubmodule S.toSubmodule := by
      intro x hx
      exact S.toSubmodule.sub_mem (S.apply_mem_toSubmodule g hx) hx
    have he : (ρ g - 1).restrict hstab = σ g - 1 := by ext x; rfl
    rw [← he]
    exact Module.End.isNilpotent.restrict hstab (h g)
  have : Nontrivial S.toSubmodule := IsSimpleModule.nontrivial K[Γ] σ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : S.toSubmodule)
  refine ⟨x, fun hx' ↦ hx (Subtype.ext hx'), fun g ↦ ?_⟩
  exact congrArg Subtype.val (DFunLike.congr_fun (irreducible_unipotent_action_trivial σ hσ g) x)

private theorem triangular_basis (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (ρ : _root_.Representation K Γ V), Module.finrank K V = n →
      (∀ g, IsNilpotent (ρ g - 1)) →
      ∃ b : Module.Basis (Fin n) K V,
        ∀ g i j, j ≤ i → LinearMap.toMatrix b b (ρ g - 1) i j = 0 := by
  induction n with
  | zero =>
    intro V _ _ _ ρ hn _
    exact ⟨(Module.finBasis K V).reindex (finCongr hn), fun _ i ↦ Fin.elim0 i⟩
  | succ n ih =>
    intro V _ _ _ ρ hn h
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
    obtain ⟨x, hx, hfix⟩ := exists_fixed_vector ρ h
    let P : Subrepresentation ρ :=
      ⟨K ∙ x, fun g v hv ↦ by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
        rw [map_smul, hfix g]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)⟩
    let p := P.toSubmodule
    have hp : Module.finrank K p = 1 := finrank_span_singleton hx
    have hq : Module.finrank K (V ⧸ p) = n := by
      have hd := p.finrank_quotient_add_finrank
      omega
    have hnil (g : Γ) : IsNilpotent (P.quotient g - 1) := by
      have hg : p ≤ p.comap (ρ g - 1) := fun v hv ↦ p.sub_mem (P.apply_mem_toSubmodule g hv) hv
      have he : p.mapQ p (ρ g - 1) hg = P.quotient g - 1 := by
        apply LinearMap.ext
        intro z
        obtain ⟨v, rfl⟩ := p.mkQ_surjective z
        change p.mkQ (ρ g v - v) = p.mkQ (ρ g v) - p.mkQ v
        exact map_sub p.mkQ _ _
      rw [← he]
      exact Module.End.IsNilpotent.mapQ hg (h g)
    obtain ⟨c, hc⟩ := ih (V ⧸ p) P.quotient hq hnil
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl p
    let e := p.quotientEquivOfIsCompl W hW
    have hxP : x ∈ p := Submodule.mem_span_singleton_self x
    have hli (a : K) (y : V) (hy : y ∈ W) (heq : a • x + y = 0) : a = 0 := by
      have hm : a • x ∈ W := by
        rw [show a • x = -y from eq_neg_iff_add_eq_zero.mpr heq]
        exact W.neg_mem hy
      have hzero : a • x = 0 := Submodule.disjoint_def.mp hW.disjoint _ (p.smul_mem a hxP) hm
      exact (smul_eq_zero.mp hzero).resolve_right hx
    have hsp (y : V) : ∃ a : K, y + a • x ∈ W := by
      have hy : y ∈ p ⊔ W := by rw [hW.sup_eq_top]; trivial
      obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      exact ⟨-a, by simpa [add_comm, add_left_comm, neg_smul] using hw⟩
    let b := Module.Basis.mkFinCons x (c.map e) hli hsp
    have hb : (b : Fin (n + 1) → V) = Fin.cons x ((↑) ∘ c.map e) :=
      Module.Basis.coe_mkFinCons x (c.map e) hli hsp
    have hb0 : b 0 = x := by simp [hb]
    have hbq (j : Fin n) : p.mkQ (b j.succ) = c j := by
      rw [hb, Fin.cons_succ]
      simp [e, Submodule.mk_quotientEquivOfIsCompl_apply]
    have hcoord (i : Fin n) : b.coord i.succ = (c.coord i).comp p.mkQ := by
      apply b.ext
      intro j
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · rw [b.coord_apply, b.repr_self, LinearMap.comp_apply, hb0]
        have hz : p.mkQ x = 0 := LinearMap.mem_ker.mp (p.ker_mkQ.symm ▸ hxP)
        rw [hz]
        simp
      · simp [LinearMap.comp_apply, hbq, Module.Basis.coord_apply, Finsupp.single_apply]
    refine ⟨b, fun g i j hij ↦ ?_⟩
    rw [LinearMap.toMatrix_apply, ← b.coord_apply]
    cases j using Fin.cases with
    | zero => simp [hb0, hfix g]
    | succ j =>
      cases i using Fin.cases with
      | zero => exact ((Fin.succ_pos j).not_ge hij).elim
      | succ i =>
        rw [hcoord, LinearMap.comp_apply]
        have hmap : p.mkQ ((ρ g - 1) (b j.succ)) = (P.quotient g - 1) (c j) := by
          rw [← hbq j]
          change p.mkQ (ρ g (b j.succ) - b j.succ) =
            p.mkQ (ρ g (b j.succ)) - p.mkQ (b j.succ)
          exact map_sub p.mkQ _ _
        rw [hmap]
        simpa only [LinearMap.toMatrix_apply, Module.Basis.coord_apply] using
          hc g i j (Fin.succ_le_succ_iff.mp hij)

/-- A common full flag for any group acting by unipotent transformations. -/
theorem geometricPointFlag : GeometricPointFlag.{u, v} := by
  intro K _ _ Γ _ V _ _ _ ρ h
  obtain ⟨b, hb⟩ := triangular_basis (Module.finrank K V) V ρ rfl h
  have he (g : Γ) (i j : Fin (Module.finrank K V)) (hij : j ≤ i) :
      LinearMap.toMatrix b b (ρ g) i j = (1 : Matrix _ _ K) i j := by
    have hh := hb g i j hij
    rwa [map_sub, LinearMap.toMatrix_one, Matrix.sub_apply, sub_eq_zero] at hh
  exact ⟨b, fun g ↦ ⟨fun {_ _} hij ↦ (he g _ _ hij.le).trans (Matrix.one_apply_ne hij.ne'),
    fun i ↦ (he g i i le_rfl).trans (Matrix.one_apply_eq i)⟩⟩

end PointFlags
section SchemeCriterion

open RationalRepresentations Algebra.TensorProduct
open private unitriangular_det groupIsoOfPoints hopfMapOfUnitriangularMatrix
  matrix_eq_coordinateMatrix_of_unitriangular filtration_of_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
open private pointMatrix pointMatrix_evaluation coordinateReduced eq_zero_of_algHom_eq_zero
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

private theorem nilpotent_sub_one_of_unitriangular {F ι : Type*} [Field F] [Fintype ι]
    [LinearOrder ι] [DecidableEq ι] {M : Matrix ι ι F} (h : IsUpperUnitriangular M) :
    IsNilpotent (M - 1) := by
  let N := M - 1
  have hn : N.IsUpperTriangular := by
    intro i j hij
    change M i j - (1 : Matrix ι ι F) i j = 0
    change j < i at hij
    rw [h.1 hij, Matrix.one_apply_ne (ne_of_gt hij), sub_zero]
  have hd (i : ι) : N i i = 0 := by
    change M i i - (1 : Matrix ι ι F) i i = 0
    rw [h.2, Matrix.one_apply_eq, sub_self]
  have hp : N.charpoly = Polynomial.X ^ Fintype.card ι := by
    rw [Matrix.charpoly_of_isUpperTriangular N hn]
    simp [hd]
  exact ⟨Fintype.card ι, by simpa [hp] using N.aeval_self_charpoly⟩

variable {F : Type u} [Field F] {V ι : Type u} [AddCommGroup V] [Module F V]
  [Fintype ι] [DecidableEq ι] (A : HopfAlgebraCategory F)

private abbrev fieldPoints := (convolutionPoints A).obj (CommAlgCat.of F F)

private def pointAction (b : Module.Basis ι F V) (ρ : RightComodule F A V) :
    _root_.Representation F (fieldPoints A) V :=
  (Matrix.toLinAlgEquiv b).toMonoidHom.comp
    ((Units.coeHom (Matrix ι ι F)).comp
      ((matrixPointHom A (coefficients A b ρ) (coefficients_isCoactionMatrix A b ρ)).app
        (CommAlgCat.of F F)).hom)

private theorem pointAction_apply (b : Module.Basis ι F V) (ρ : RightComodule F A V)
    (g : fieldPoints A) :
    pointAction A b ρ g = (TensorProduct.rid F V).toLinearMap.comp (evaluate A ρ g.ofConv) := by
  apply b.ext
  intro j
  rw [LinearMap.comp_apply]
  change Matrix.toLinAlgEquiv b (g.ofConv.mapMatrix (coefficients A b ρ)) (b j) = _
  rw [Matrix.toLinAlgEquiv_self]
  unfold evaluate
  rw [LinearMap.comp_apply, coaction_apply_basis A b ρ, map_sum, map_sum]
  simp [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

private theorem pointAction_toMatrix {J : Type u} [Fintype J] [DecidableEq J]
    (b : Module.Basis ι F V) (c : Module.Basis J F V) (ρ : RightComodule F A V)
    (g : fieldPoints A) :
    LinearMap.toMatrix c c (pointAction A b ρ g) = g.ofConv.mapMatrix (coefficients A c ρ) := by
  rw [pointAction_apply A b]
  rw [← pointAction_apply A c]
  change LinearMap.toMatrixAlgEquiv c
      (Matrix.toLinAlgEquiv c (g.ofConv.mapMatrix (coefficients A c ρ))) = _
  exact LinearMap.toMatrixAlgEquiv_toLinAlgEquiv _ _

omit [Fintype ι] [DecidableEq ι] in
private theorem coeff_mem_of_basis {J : Type u} [Fintype J]
    (b : Module.Basis ι F V) (c : Module.Basis J F V) (ρ : RightComodule F A V)
    (S : Subalgebra F A) (h : ∀ i j, coefficients A c ρ i j ∈ S) (i j : ι) :
    coefficients A b ρ i j ∈ S := by
  change tensorCoordinate b i (ρ.coaction (b j)) ∈ S
  rw [← c.sum_repr (b j), map_sum, map_sum]
  apply S.toSubmodule.sum_mem
  intro x _
  rw [map_smul, map_smul, coaction_apply_basis A c ρ, map_sum]
  apply S.toSubmodule.smul_mem
  apply S.toSubmodule.sum_mem
  intro y _
  change b.coord i (c y) • coefficients A c ρ y x ∈ S
  exact S.toSubmodule.smul_mem _ (h _ _)

private def coordinatePointsIso {k : Type u} [Field k] (A : HopfAlgebraCategory k)
    (G : Specs.AffineAlgebraicGroup k)
    (s : ((affineHopfSpec k).obj (op A)).val ≅ G.val) :
    convolutionPoints A ≅ (groupPointsFunctor k).obj G.val :=
  hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso s

open Specs.StandardGroups in
private theorem faithful_coefficients {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    (G L : Specs.AffineAlgebraicGroup k) (A : HopfAlgebraCategory k)
    (s : ((affineHopfSpec k).obj (op A)).val ≅ G.val)
    (l : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k ι)
    (f : G.val ⟶ L.val) (hf : IsClosedImmersion f.hom.hom.left) :
    ∃ q : GLCoordinates k ι →ₐ[k] A, Function.Surjective q ∧
      q.mapMatrix (Specs.StandardGroups.universalMatrix k ι) =
        RationalRepresentations.universalMatrix A ⟨G.val, G.property.1⟩ L.val
          (coordinatePointsIso A G s) l f := by
  obtain ⟨h, _, _, _, _, _, _, hL⟩ := StandardGroups.generalLinearGroupSpecification k ι
  let := h.hopf
  let D := GLCoordinates k ι
  let L' := spectrum k D
  obtain ⟨d, hd, l', hl'⟩ := hL
  let t := l ≪≫ l'.symm
  let a : L.val ≅ L'.val := groupIsoOfPoints t
  have ha : (groupPointsFunctor k).map a.hom = t.hom :=
    Classical.choose_spec ((groupHomComparison k L.val L'.val L.property.1).2 t.hom)
  let F := groupPointsFunctor k
  let R := CommAlgCat.of k A
  let p := (coordinatePointsIso A G s).hom.app R (toConv (AlgHom.id k A))
  let y := (F.map f).app R p
  let q : D →ₐ[k] A := (d.inv.app R ((F.map a.hom).app R y)).ofConv
  have hy : d.hom.app R (toConv q) = (F.map a.hom).app R y := by
    change d.hom.app R (d.inv.app R ((F.map a.hom).app R y)) = _
    rw [← GrpCat.comp_apply, d.inv_hom_id_app]
    rfl
  let sf : Spec (CommRingCat.of A) ⟶ G.val.X.left := s.hom.hom.hom.left
  let ff : G.val.X.left ⟶ L.val.X.left := f.hom.hom.left
  let af : L.val.X.left ⟶ Spec (CommRingCat.of D) := a.hom.hom.hom.left
  have hp : (p : Points G.val.X R).left = sf := by
    change Spec.map (𝟙 (CommRingCat.of A)) ≫ sf = sf
    rw [Spec.map_id, Category.id_comp]
  let r := CommRingCat.ofHom q.toRingHom
  have he : Spec.map r = (sf ≫ ff) ≫ af := by
    have h' := congrArg (fun z : Points L'.val.X R ↦ z.left) hy
    rw [hd R q] at h'
    change Spec.map r = ((p : Points G.val.X R).left ≫ ff) ≫ af at h'
    rwa [hp] at h'
  have hs : IsIso sf := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map s.hom)
    infer_instance
  have haa : IsIso af := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map a.hom)
    infer_instance
  have hff : IsClosedImmersion ff := hf
  have : IsClosedImmersion (Spec.map r) := by rw [he]; infer_instance
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map r)).2
  have hr : (Scheme.ΓSpecIso _).inv ≫ (Spec.map r).appTop ≫ (Scheme.ΓSpecIso _).hom = r := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hsurj : Function.Surjective r := by
    rw [← hr]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp
      (hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2)
  refine ⟨q, hsurj, ?_⟩
  have hh := hl' R q
  rw [hy, ha] at hh
  have ht : l'.hom.app R (t.hom.app R y) = l.hom.app R y := by
    change l'.hom.app R (l'.inv.app R (l.hom.app R y)) = _
    rw [← GrpCat.comp_apply, l'.inv_hom_id_app]
    rfl
  rw [ht] at hh
  exact hh.symm

private theorem invariantVectors_descend {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (h : HasInvariantVectors (scalarExtension A K)) :
    HasInvariantVectors A := by
  classical
  intro V _ _ _ _ ρ
  let b : Module.Basis (Index.{u} (Module.finrank k V)) k V :=
    (Module.finBasis k V).reindex Equiv.ulift.symm
  obtain ⟨σ, _, hinv, _⟩ := fieldExtensionComparison (K := K) A b ρ
  have : Nontrivial (K ⊗[k] V) :=
    Module.nontrivial_of_finrank_pos (R := K) (M := K ⊗[k] V) (by
      rw [Module.finrank_eq_card_basis (b.baseChange K), Fintype.card_ulift, Fintype.card_fin]
      exact Module.finrank_pos)
  obtain ⟨x, hx, hmem⟩ := h _ σ
  have hn : invariants A ρ ≠ ⊥ := by
    intro he
    rw [hinv, he, Submodule.baseChange_bot, Submodule.mem_bot] at hmem
    exact hx hmem
  rw [ne_eq, Submodule.eq_bot_iff, not_forall] at hn
  obtain ⟨v, hv⟩ := hn
  exact ⟨v, fun h₀ ↦ hv (fun _ ↦ h₀), of_not_not (fun h₀ ↦ hv (fun hm ↦ (h₀ hm).elim))⟩

open Specs.StandardGroups in
private theorem hasInvariantVectors_of_geometric_matrices
    {k K ι V : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {A : HopfAlgebraCategory k} [Algebra.FiniteType k A] [IsReduced (K ⊗[k] A)]
    (b : Module.Basis ι K V) (σ : RightComodule K (scalarExtension A K) V)
    (q : GLCoordinates k ι →ₐ[k] A) (hq : Function.Surjective q)
    (hcoeff : coefficients (scalarExtension A K) b σ =
      ((Algebra.TensorProduct.includeRight (A := K)).comp q).mapMatrix
        (Specs.StandardGroups.universalMatrix k ι))
    (hpoint : ∀ g : fieldPoints (scalarExtension A K),
      IsNilpotent (g.ofConv.mapMatrix (coefficients (scalarExtension A K) b σ) - 1)) :
    HasInvariantVectors (scalarExtension A K) := by
  classical
  let B := scalarExtension A K
  let τ := pointAction B b σ
  have hτ (g : fieldPoints B) : IsNilpotent (τ g - 1) := by
    have hg := hpoint g
    rw [← pointAction_toMatrix B b b σ g] at hg
    change IsNilpotent (LinearMap.toMatrixAlgEquiv b (τ g) - 1) at hg
    rw [← map_one (LinearMap.toMatrixAlgEquiv b), ← map_sub] at hg
    exact (IsNilpotent.map_iff (LinearMap.toMatrixAlgEquiv b).injective).mp hg
  obtain ⟨c₀, hc₀⟩ := geometricPointFlag τ hτ
  let c : Module.Basis (Index.{u} (Module.finrank K V)) K V := c₀.reindex Equiv.ulift.symm
  have hc (g : fieldPoints B) : IsUpperUnitriangular (g.ofConv.mapMatrix (coefficients B c σ)) := by
    rw [← pointAction_toMatrix B b c σ g]
    have he (i j : Index.{u} (Module.finrank K V)) :
        LinearMap.toMatrix c c (τ g) i j = LinearMap.toMatrix c₀ c₀ (τ g) i.down j.down := by
      simp [LinearMap.toMatrix_apply, c, Module.Basis.reindex_apply]
    exact ⟨fun {i j} hij ↦ (he i j).trans ((hc₀ g).1 hij),
      fun i ↦ (he i i).trans ((hc₀ g).2 i.down)⟩
  -- The extended coordinate ring is reduced, so the flag equations on field
  -- points hold for the universal coaction matrix.
  have ht : IsUpperUnitriangular (coefficients B c σ) := by
    constructor
    · intro i j hij
      apply eq_zero_of_algHom_eq_zero (F := K)
      intro g
      exact (hc (toConv g)).1 hij
    · intro i
      apply sub_eq_zero.mp
      apply eq_zero_of_algHom_eq_zero (F := K)
      intro g
      rw [map_sub, map_one]
      exact sub_eq_zero.mpr ((hc (toConv g)).2 i)
  let p := hopfMapOfUnitriangularMatrix ht (coefficients_isCoactionMatrix B c σ)
  let S := p.hom.toAlgHom.range
  have hcS (i j) : coefficients B c σ i j ∈ S :=
    ⟨coordinateMatrix K (Module.finrank K V) i j,
      congrArg (fun M ↦ M i j) (matrix_eq_coordinateMatrix_of_unitriangular ht)⟩
  have hbS := coeff_mem_of_basis B b c σ S hcS
  have hdet : (coefficients B b σ).det = 1 := by
    apply sub_eq_zero.mp
    apply eq_zero_of_algHom_eq_zero (F := K)
    intro g
    rw [map_sub, map_one, g.map_det, ← pointAction_toMatrix B b b σ (toConv g),
      LinearMap.det_toMatrix_eq_det_toMatrix b c, pointAction_toMatrix B b c σ (toConv g)]
    exact sub_eq_zero.mpr (unitriangular_det (hc (toConv g)))
  let Q : GLCoordinates k ι →ₐ[k] B := Algebra.TensorProduct.includeRight.comp q
  let P := MvPolynomial (ι × ι) k
  let d := genericDeterminant k ι
  let D := GLCoordinates k ι
  let q₀ : P →ₐ[k] B := Q.comp (IsScalarTower.toAlgHom k P D)
  have hd : Q (algebraMap P D d) = 1 := by
    have hh := hdet
    rw [hcoeff] at hh
    change (Q.mapMatrix ((algebraMap P D).mapMatrix (genericMatrix k ι))).det = 1 at hh
    rwa [← Q.map_det, ← RingHom.map_det] at hh
  have hpoly (x : P) : q₀ x ∈ S := by
    induction x using MvPolynomial.induction_on with
    | C x =>
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      exact (S.restrictScalars k).algebraMap_mem x
    | add x y hx hy => exact (map_add q₀ x y).symm ▸ S.add_mem hx hy
    | mul_X x ij hx =>
      have hX : q₀ (MvPolynomial.X ij) ∈ S := by
        have hh := hbS ij.1 ij.2
        rw [hcoeff] at hh
        exact hh
      exact (map_mul q₀ x _).symm ▸ S.mul_mem hx hX
  -- The original faithful coordinates generate after inverting the determinant.
  -- Its image is one, so the rebased entries already generate.
  have hloc (x : D) : Q x ∈ S := by
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj d x
    have hh := congrArg Q ha
    rw [map_mul, map_pow, hd, one_pow, mul_one] at hh
    exact hh ▸ hpoly a
  have hS (x : B) : x ∈ S := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => exact S.add_mem hx hy
    | tmul r a =>
      obtain ⟨z, rfl⟩ := hq a
      have hz : (1 : K) ⊗ₜ[k] q z ∈ S := hloc z
      have hh : r • ((1 : K) ⊗ₜ[k] q z) = r ⊗ₜ[k] q z := by
        change (r * 1) ⊗ₜ[k] q z = _
        rw [mul_one]
      exact hh ▸ S.toSubmodule.smul_mem r hz
  have hsurj : Function.Surjective p.hom :=
    (AlgHom.range_eq_top p.hom.toAlgHom).mp (top_unique (fun x _ ↦ hS x))
  exact hasInvariantVectors_of_filtration (filtration_of_surjective p hsurj)

open private triangularBasis_of_invariants triangularBasis_isUnitriangular
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria

private theorem extended_coaction_eq {k K V ι : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [Fintype ι]
    (A : HopfAlgebraCategory k) (b : Module.Basis ι k V) (ρ : RightComodule k A V)
    (σ : RightComodule K (scalarExtension A K) (K ⊗[k] V))
    (h : ∀ i j, coefficients (scalarExtension A K) (b.baseChange K) σ i j =
      (1 : K) ⊗ₜ[k] coefficients A b ρ i j) :
    σ.coaction =
      (TensorProduct.AlgebraTensorModule.distribBaseChange k K V A).toLinearMap.comp
        (ρ.coaction.baseChange K) := by
  apply (b.baseChange K).ext
  intro j
  rw [coaction_apply_basis (scalarExtension A K) (b.baseChange K) σ, LinearMap.comp_apply]
  simp only [h, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
  rw [coaction_apply_basis A b ρ]
  simp only [TensorProduct.tmul_sum, map_sum, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

/-- A smooth affine algebraic group is unipotent exactly when its geometric points
act by unipotent matrices in the given faithful representation. -/
theorem geometricPointCriterion : GeometricPointCriterion.{u} := by
  classical
  intro k _ G hG n L l f hf
  let K := AlgebraicClosure k
  let R := CommAlgCat.of k K
  let H : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  let A := coordinateHopf H
  let s : ((affineHopfSpec k).obj (op A)).val ≅ G.val :=
    (affineGroupInclusion k).mapIso (coordinateHopfSpecIso H)
  let e := coordinatePointsIso A G s
  let B := scalarExtension A K
  let ι := Index.{u} n
  let V := ι → k
  let b : Module.Basis ι k V := Pi.basisFun k ι
  obtain ⟨E, hE⟩ := representationCoactionComparison A b H L.val e l
  let ρ := E f
  let α := e.hom ≫ (groupPointsFunctor k).map f ≫ l.hom
  have hm : coefficients A b ρ = pointMatrix A α := hE f
  have hge (g : (convolutionPoints A).obj R) :
      (l.hom.app R (((groupPointsFunctor k).map f).app R (e.hom.app R g))).val =
        g.ofConv.mapMatrix (coefficients A b ρ) := by
    rw [hm]
    exact pointMatrix_evaluation A α R g
  obtain ⟨σ, hσ, _, _⟩ := fieldExtensionComparison (K := K) A b ρ
  let bK := b.baseChange K
  let eK : (A →ₐ[k] K) ≃ (B →ₐ[K] K) := liftEquivRight k K A K
  have hgK (g : B →ₐ[K] K) :
      g.mapMatrix (coefficients B bK σ) = (eK.symm g).mapMatrix (coefficients A b ρ) := by
    ext i j
    change g (coefficients B bK σ i j) = _
    rw [hσ]
    rfl
  have hInv := (unipotenceCriteria G A s).1
  constructor
  · intro h p
    let g := (e.inv.app R p)
    have hg : e.hom.app R g = p := by
      change e.hom.app R (e.inv.app R p) = _
      rw [← GrpCat.comp_apply, e.inv_hom_id_app]
      rfl
    rw [← hg, hge g, ← eK.symm_apply_apply g.ofConv, ← hgK]
    obtain ⟨c₀, hc₀⟩ := triangularBasis_of_invariants A (hInv.mp h) (Module.finrank k V) V rfl ρ
    let c : Module.Basis (Index.{u} (Module.finrank k V)) k V := c₀.reindex Equiv.ulift.symm
    have hc := triangularBasis_isUnitriangular A ρ c₀ hc₀
    obtain ⟨σ', hσ', _, _⟩ := fieldExtensionComparison (K := K) A c ρ
    have hsame : σ = σ' := by
      cases σ
      cases σ'
      congr
      exact (extended_coaction_eq A b ρ _ hσ).trans (extended_coaction_eq A c ρ _ hσ').symm
    let cK := c.baseChange K
    have hcK : IsUpperUnitriangular (coefficients B cK σ) := by
      rw [hsame]
      exact ⟨fun {i j} hij ↦ by rw [hσ', hc.1 hij, TensorProduct.tmul_zero],
        fun i ↦ by rw [hσ', hc.2 i]; rfl⟩
    let g' : fieldPoints B := toConv (eK g.ofConv)
    let T := pointAction B bK σ g'
    have htri : IsUpperUnitriangular (LinearMap.toMatrix cK cK T) := by
      rw [pointAction_toMatrix B bK cK σ g']
      exact ⟨hcK.1.map g'.ofConv, fun i ↦ by
        change g'.ofConv (coefficients B cK σ i i) = _
        rw [hcK.2, map_one]⟩
    have hnil := nilpotent_sub_one_of_unitriangular htri
    change IsNilpotent (LinearMap.toMatrixAlgEquiv cK T - 1) at hnil
    rw [← map_one (LinearMap.toMatrixAlgEquiv cK), ← map_sub] at hnil
    have hn := (IsNilpotent.map_iff (LinearMap.toMatrixAlgEquiv cK).injective).mp hnil
    have hn' := hn.map (LinearMap.toMatrixAlgEquiv bK)
    rw [map_sub, map_one] at hn'
    change IsNilpotent (LinearMap.toMatrix bK bK T - 1) at hn'
    rwa [pointAction_toMatrix B bK bK σ g'] at hn'
  · intro h
    obtain ⟨hft, hred⟩ := coordinateReduced G A s hG
    obtain ⟨q, hq, hqM⟩ := faithful_coefficients G L A s l f hf
    have hcoeff : coefficients B bK σ =
        ((Algebra.TensorProduct.includeRight (A := K)).comp q).mapMatrix
          (Specs.StandardGroups.universalMatrix k ι) := by
      ext i j
      rw [hσ]
      have he := congrArg (fun M : Matrix ι ι A ↦ M i j) (hqM.trans (hE f).symm)
      change (1 : K) ⊗ₜ[k] coefficients A b ρ i j = (1 : K) ⊗ₜ[k] (q.mapMatrix _) i j
      rw [he]
    have hpoint (g : fieldPoints B) :
        IsNilpotent (g.ofConv.mapMatrix (coefficients B bK σ) - 1) := by
      rw [hgK, ← hge (toConv (eK.symm g.ofConv))]
      exact h _
    exact hInv.mpr (invariantVectors_descend A
      (hasInvariantVectors_of_geometric_matrices bK σ q hq hcoeff hpoint))

end SchemeCriterion

section RootsOfUnity

open RationalRepresentations

variable {k : Type u} [Field k] {p : ℕ}

private abbrev CyclicCharacterGroup (p : ℕ) := Multiplicative (ZMod p)

private def cyclicGenerator (p : ℕ) : CyclicCharacterGroup p := Multiplicative.ofAdd 1

private theorem cyclicGenerator_pow : cyclicGenerator p ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  change p • (1 : ZMod p) = 0
  simp [nsmul_eq_mul]

private theorem cyclicGenerator_pow_val [NeZero p] (a : CyclicCharacterGroup p) :
    cyclicGenerator p ^ a.toAdd.val = a := by
  apply Multiplicative.toAdd.injective
  change a.toAdd.val • (1 : ZMod p) = a.toAdd
  rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

private abbrev rootCoordinates (k : Type u) [Field k] (p : ℕ) : HopfAlgebraCategory k :=
  CommHopfAlgCat.of k (k[CyclicCharacterGroup p])

private def rootGenerator (k : Type u) [Field k] (p : ℕ) : rootCoordinates k p :=
  MonoidAlgebra.of k (CyclicCharacterGroup p) (cyclicGenerator p)

private theorem rootGenerator_groupLike :
    IsGroupLikeElem k (rootGenerator k p) :=
  MonoidAlgebra.isGroupLikeElem_single_one (cyclicGenerator p)

private def rootEvaluation (R : TestAlgebra k) :
    (convolutionPoints (rootCoordinates k p)).obj R →* primeRoots p R where
  toFun f :=
    let g := ((MonoidAlgebra.lift k R (CyclicCharacterGroup p)).symm f.ofConv).toHomUnits
    ⟨g (cyclicGenerator p), by
      change g (cyclicGenerator p) ^ p = 1
      rw [← map_pow, cyclicGenerator_pow, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change (1 : WithConv (rootCoordinates k p →ₐ[k] R)) (rootGenerator k p) = 1
    rw [AlgHom.convOne_apply, rootGenerator_groupLike.counit_eq_one, map_one]
  map_mul' f g := by
    apply Subtype.ext
    apply Units.ext
    let f' : WithConv (rootCoordinates k p →ₐ[k] R) := f
    let g' : WithConv (rootCoordinates k p →ₐ[k] R) := g
    change (f' * g') (rootGenerator k p) =
      f'.ofConv (rootGenerator k p) * g'.ofConv (rootGenerator k p)
    rw [AlgHom.convMul_apply, rootGenerator_groupLike.comul_eq_tmul_self]
    simp

private theorem rootEvaluation_bijective [NeZero p] (R : TestAlgebra k) :
    Function.Bijective (rootEvaluation (p := p) R) := by
  constructor
  · intro f g h
    have ht := congrArg (fun z : primeRoots p R ↦ (z.val : R)) h
    change f.ofConv (rootGenerator k p) = g.ofConv (rootGenerator k p) at ht
    apply WithConv.ofConv_injective
    apply (MonoidAlgebra.lift k R (CyclicCharacterGroup p)).symm.injective
    apply MonoidHom.ext
    intro a
    change f.ofConv (MonoidAlgebra.of k (CyclicCharacterGroup p) a) =
      g.ofConv (MonoidAlgebra.of k (CyclicCharacterGroup p) a)
    have he := cyclicGenerator_pow_val a
    conv_lhs => rw [← he]
    conv_rhs => rw [← he]
    simp only [map_pow]
    exact congrArg (· ^ a.toAdd.val) ht
  · intro a
    let f : ℤ →+ Additive Rˣ :=
      { toFun := fun z ↦ Additive.ofMul (a.val ^ z)
        map_zero' := by simp
        map_add' := fun x y ↦ by simp [zpow_add] }
    have hf : f p = 0 := by
      change Additive.ofMul (a.val ^ (p : ℤ)) = Additive.ofMul 1
      rw [zpow_natCast, show a.val ^ p = 1 from a.property]
    let g : CyclicCharacterGroup p →* Rˣ := AddMonoidHom.toMultiplicativeLeft (ZMod.lift p ⟨f, hf⟩)
    have hg : g (cyclicGenerator p) = a.val := by
      change (ZMod.lift p ⟨f, hf⟩ (1 : ZMod p)).toMul = a.val
      rw [show (1 : ZMod p) = ((1 : ℤ) : ZMod p) from Int.cast_one.symm, ZMod.lift_coe]
      change a.val ^ (1 : ℤ) = a.val
      exact zpow_one a.val
    let q := MonoidAlgebra.lift k R (CyclicCharacterGroup p) ((Units.coeHom R).comp g)
    refine ⟨toConv q, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change q (MonoidAlgebra.of k (CyclicCharacterGroup p) (cyclicGenerator p)) = (a.val : R)
    rw [MonoidAlgebra.lift_of]
    exact congrArg Units.val hg

private def rootPointsIso (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] :
    (groupPointsFunctor k).obj (muPrime k p).val ≅ primeRootsPoints k p :=
  (hopfSpecPointIso (rootCoordinates k p)).symm ≪≫
    NatIso.ofComponents
      (fun R ↦ (MulEquiv.ofBijective (rootEvaluation R) (rootEvaluation_bijective R)).toGrpIso)
      (by
        intro R S f
        apply GrpCat.ext
        intro g
        apply Subtype.ext
        apply Units.ext
        rfl)

private theorem rootGenerator_ne_one [Fact p.Prime] : rootGenerator k p ≠ 1 := by
  classical
  intro h
  have ht : cyclicGenerator p ≠ (1 : CyclicCharacterGroup p) := by
    intro he
    exact one_ne_zero (congrArg Multiplicative.toAdd he : (1 : ZMod p) = 0)
  have hh := congrArg (fun a : k[CyclicCharacterGroup p] ↦ a.coeff 1) h
  change (MonoidAlgebra.single (cyclicGenerator p) (1 : k)).coeff 1 = _ at hh
  simp [ht] at hh

private theorem muPrime_not_unipotent [Fact p.Prime] : ¬ IsUnipotent (muPrime k p) := by
  let A := rootCoordinates k p
  intro h
  have hInv := ((unipotenceCriteria (muPrime k p) A (Iso.refl _)).1).mp h
  let t : A := rootGenerator k p
  have ht : IsGroupLikeElem k t := rootGenerator_groupLike
  let ρ : RightComodule k A k :=
    { coaction := (TensorProduct.mk k k A).flip t
      coassoc := fun x ↦ by
        change TensorProduct.assoc k k A A (((TensorProduct.mk k k A).flip t).rTensor A
          (x ⊗ₜ[k] t)) = (Coalgebra.comul (R := k) (A := A)).lTensor k (x ⊗ₜ[k] t)
        rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, ht.comul_eq_tmul_self]
        rfl
      counit := fun x ↦ by
        change TensorProduct.rid k k ((Coalgebra.counit (R := k) (A := A)).lTensor k
          (x ⊗ₜ[k] t)) = x
        rw [LinearMap.lTensor_tmul, ht.counit_eq_one, TensorProduct.rid_tmul, one_smul] }
  obtain ⟨x, hx, hfix⟩ := hInv k ρ
  have h' := (invariantKernel A ρ x).mpr hfix (CommAlgCat.of k A) (AlgHom.id k A)
  change (AlgHom.id k A).toLinearMap.lTensor k (x ⊗ₜ[k] t) = x ⊗ₜ[k] (1 : A) at h'
  rw [LinearMap.lTensor_tmul] at h'
  have hx' : x • t = x • (1 : A) := congrArg (TensorProduct.lid k A) h'
  exact rootGenerator_ne_one ((smul_right_injective (M := A) hx) hx')

/-- The group scheme of p-th roots of unity is a counterexample without smoothness. -/
theorem geometricPointCounterexample : GeometricPointCounterexample.{u} := by
  intro k _ p _ _
  let e := rootPointsIso k p
  let K := AlgebraicClosure k
  let R := CommAlgCat.of k K
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hu (a : primeRoots p K) : a = 1 := by
    apply Subtype.ext
    apply Units.ext
    have ha : (a.val : K) ^ p = 1 := by
      change ((a.val ^ p : Kˣ) : K) = 1
      rw [show a.val ^ p = 1 from a.property]
      rfl
    have hzero : ((a.val : K) - 1) ^ p = 0 := by rw [sub_pow_char, ha, one_pow, sub_self]
    exact sub_eq_zero.mp ((show IsNilpotent ((a.val : K) - 1) from ⟨p, hzero⟩).eq_zero)
  have htrivial : Subsingleton (((groupPointsFunctor k).obj (muPrime k p).val).obj R) := by
    refine ⟨fun x y ↦ ?_⟩
    have hxy : e.hom.app R x = e.hom.app R y := (hu _).trans (hu _).symm
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1 hxy
  refine ⟨⟨e⟩, htrivial, muPrime_not_unipotent, fun hs ↦ ?_⟩
  obtain ⟨n, L, ⟨l⟩, f, hf⟩ := faithfulLinearization k (muPrime k p)
  apply muPrime_not_unipotent (k := k) (p := p)
  apply (geometricPointCriterion (muPrime k p) hs n L l f hf).mpr
  intro g
  rw [htrivial.elim g 1]
  simp only [map_one]
  change IsNilpotent ((1 : Matrix (Index.{u} n) (Index.{u} n) K) - 1)
  rw [sub_self]
  exact ⟨1, pow_one _⟩

end RootsOfUnity

end LinearAlgebraicGroups.Unipotent
