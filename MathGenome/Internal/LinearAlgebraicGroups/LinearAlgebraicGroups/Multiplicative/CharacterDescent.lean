import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.CategoryTheory.Whiskering
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite Coalgebra HopfAlgebra
open scoped TensorProduct MonoidAlgebra Topology

namespace LinearAlgebraicGroups.CharacterDescent

open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.Specs.CharacterDescent
  LinearAlgebraicGroups.Specs.DiagonalizableGroups Descent

universe u

noncomputable section

abbrev isDiagonalizable : IsDiagonalizableType.{u} := @Specs.CharacterDescent.IsDiagonalizable
abbrev isMultiplicativeType : IsMultiplicativeTypeType.{u} :=
  @Specs.CharacterDescent.IsMultiplicativeType
abbrev isTorus : IsTorusType.{u} := @Specs.CharacterDescent.IsTorus
abbrev character : CharacterType.{u} := @Specs.CharacterDescent.Character
abbrev cocharacter : CocharacterType.{u} := @Specs.CharacterDescent.Cocharacter
abbrev compositionPairing : CompositionPairingType.{u} := @Specs.CharacterDescent.compositionPairing
abbrev groupAlgebraOperator : GroupAlgebraOperatorType.{u} :=
  @Specs.CharacterDescent.groupAlgebraOperator

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem operator_single {M : Type u} [CommGroup M] (σ : Gal(K/k))
    (e : M ≃* M) (m : M) (a : K) :
    groupAlgebraOperator σ e (MonoidAlgebra.single m a) = MonoidAlgebra.single (e m) (σ a) := by
  simp [groupAlgebraOperator, Specs.CharacterDescent.groupAlgebraOperator]

private def groupAlgebraSemilinearAction {M : Type u} [CommGroup M] (ρ : Gal(K/k) →* MulAut M) :
    SemilinearAction k K (MonoidAlgebra K M) where
  act σ := (groupAlgebraOperator σ (ρ σ)).toAddEquiv
  one_act x := by
    change groupAlgebraOperator 1 (ρ 1) x = x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single m a => simp [operator_single]
  mul_act σ τ x := by
    change groupAlgebraOperator (σ * τ) (ρ (σ * τ)) x =
      groupAlgebraOperator σ (ρ σ) (groupAlgebraOperator τ (ρ τ) x)
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single m a =>
      rw [operator_single, operator_single, operator_single, map_mul]
      rfl
  map_smul σ a x := by
    change groupAlgebraOperator σ (ρ σ) (a • x) = σ a • groupAlgebraOperator σ (ρ σ) x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    change groupAlgebraOperator σ (ρ σ) (MonoidAlgebra.single 1 a) =
      MonoidAlgebra.single 1 (σ a)
    rw [operator_single, map_one]

@[simp] private theorem groupAlgebraSemilinearAction_single {M : Type u} [CommGroup M]
    (ρ : Gal(K/k) →* MulAut M) (σ : Gal(K/k)) (m : M) (a : K) :
    (groupAlgebraSemilinearAction ρ).act σ (MonoidAlgebra.single m a) =
      MonoidAlgebra.single (ρ σ m) (σ a) :=
  operator_single σ (ρ σ) m a

/-- The semilinear action on the group algebra respects its Hopf operations. -/
def groupAlgebraDescentDatum {M : Type u} [CommGroup M] (ρ : Gal(K/k) →* MulAut M) :
    HopfDescentDatum k (groupAlgebra K M) where
  action := groupAlgebraSemilinearAction ρ
  map_one σ := (groupAlgebraOperator σ (ρ σ)).map_one
  map_mul σ := (groupAlgebraOperator σ (ρ σ)).map_mul
  comul_equivariant σ x := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single m a =>
      simp only [MonoidAlgebra.comul_single,
        CommSemiring.comul_apply, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
        groupAlgebraSemilinearAction_single, SemilinearAction.tensor_act_tmul, map_one]
  counit_equivariant σ x := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single m a =>
      simp [SemilinearAction.unit]
  antipode_equivariant σ x := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single m a => simp

open private comparison_equivariant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

/-- The finite Galois descent of the group algebra has its fixed algebra as coordinates. -/
def descendedGroup {M : Type u} [CommGroup M] [FiniteDimensional k K] [IsGalois k K]
    (ρ : Gal(K/k) →* MulAut M) : GroupScheme k :=
  specGroup (Descent.descendHopf (groupAlgebraDescentDatum ρ)).algebra

theorem finiteGroupAlgebraDescent : FiniteGroupAlgebraDescent.{u} := by
  intro k K _ _ _ _ _ M _ _ ρ
  let H := Descent.descendHopf (groupAlgebraDescentDatum ρ)
  refine ⟨groupAlgebraDescentDatum ρ, H, fun _ => rfl, ?_,
    comparison_equivariant H, ?_, ⟨(Descent.groupDescentComparison H).symm⟩⟩
  · exact (Descent.affineDescentProperties H).1
      (inferInstanceAs (Algebra.FiniteType K (MonoidAlgebra K M)))
  · exact ⟨K, inferInstance, inferInstance, inferInstance,
      ⟨⟨CommGrpCat.of M, inferInstance⟩, ⟨H.iso.symm⟩⟩⟩

private def actionAutomorphisms {Γ : Type u} [Group Γ] (M : Action CommGrpCat.{u} Γ) :
    Γ →* MulAut M.V where
  toFun σ := (Aut.isoEquiv (M.ρAut σ)).commGroupIsoToMulEquiv
  map_one' := by
    apply MulEquiv.ext
    intro m
    change (M.ρ 1).asHom m = m
    simp
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro m
    change (M.ρ (σ * τ)).asHom m = (M.ρ σ).asHom ((M.ρ τ).asHom m)
    rw [map_mul]
    rfl

theorem factorsThroughFiniteGalois : FactorsThroughFiniteGalois.{u} := by
  intro k K _ _ _ _ M
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.mp M.property.1
  let U : Set Gal(K/k) := ⋂ m ∈ s, {g | (M.obj.ρ g).asHom m = m}
  have hU : IsOpen U := hfin.isOpen_biInter (fun m _ => M.property.2 m)
  have h1 : (1 : Gal(K/k)) ∈ U := by simp [U]
  obtain ⟨E, hE, hN, hfix⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k K U).mp (hU.mem_nhds h1)
  let _ := hN
  let π : Gal(K/k) →* Gal(E/k) := AlgEquiv.restrictNormalHom E
  let ρ := actionAutomorphisms M.obj
  have hk : π.ker ≤ ρ.ker := by
    intro σ hσ
    have hσ' : σ ∈ U := hfix (by simpa [π, E.restrictNormalHom_ker] using hσ)
    have hgens : ∀ m ∈ s, (M.obj.ρ σ).asHom m = m := by simpa [U] using hσ'
    change ρ σ = 1
    apply MulEquiv.ext
    intro m
    change (M.obj.ρ σ).asHom m = m
    have hm : m ∈ Subgroup.closure s := by simp [hs]
    induction hm using Subgroup.closure_induction with
    | mem m hm => exact hgens m hm
    | one => simp
    | mul x y _ _ hx hy => simp [map_mul, hx, hy]
    | inv x _ hx => simp [map_inv, hx]
  have hπ : Function.Surjective π :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := E) K
  let lift := π.liftOfSurjective hπ ⟨ρ, hk⟩
  refine ⟨E, hE, hN, lift, fun σ m => ?_⟩
  have h := π.liftOfRightInverse_comp_apply (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨ρ, hk⟩ σ
  exact congrArg (fun e : MulAut M.obj.V => e m) h.symm

section ScalarExtension

variable (K) (A : HopfAlgebraCategory k)

/-- The action on an extended Hopf algebra acts on the field factor. -/
def scalarExtensionDatum : HopfDescentDatum k (extendedHopf K A) where
  action := SemilinearAction.scalarExtension (K := K) A
  map_one σ := by
    change (σ 1 : K) ⊗ₜ[k] (1 : A) = 1 ⊗ₜ[k] 1
    rw [map_one]
  map_mul σ x y := by
    let f := Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)
    have hf (z : K ⊗[k] A) : (SemilinearAction.scalarExtension (K := K) A).act σ z = f z := by
      induction z using TensorProduct.inductionOn with
      | tmul r a => rfl
      | add z w hz hw => simp only [map_add, hz, hw]
    rw [hf, hf, hf, map_mul]
  comul_equivariant σ x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a =>
      change comul (R := K) (σ r ⊗ₜ[k] a) =
        ((SemilinearAction.scalarExtension (K := K) A).tensor
          (SemilinearAction.scalarExtension (K := K) A)).act σ
          (comul (R := K) (r ⊗ₜ[k] a))
      simp only [TensorProduct.comul_tmul, CommSemiring.comul_apply]
      generalize comul (R := k) a = t
      induction t using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul x y =>
        simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          SemilinearAction.tensor_act_tmul]
        change (1 ⊗ₜ[k] x) ⊗ₜ[K] (σ r ⊗ₜ[k] y) =
          (σ 1 ⊗ₜ[k] x) ⊗ₜ[K] (σ r ⊗ₜ[k] y)
        rw [map_one]
  counit_equivariant σ x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a =>
      change counit (R := K) (σ r ⊗ₜ[k] a) = σ (counit (R := K) (r ⊗ₜ[k] a))
      simp [TensorProduct.counit_tmul, Algebra.smul_def, mul_comm]
  antipode_equivariant σ x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a => rfl

/-- The Galois action on geometric characters is the restriction of its action on
the coordinate algebra. -/
def geometricAction : Gal(K/k) →* End (CommGrpCat.of (GeometricCharacters K A)) where
  toFun σ := End.of (CommGrpCat.ofHom
    { toFun := fun x =>
        ⟨(scalarExtensionDatum K A).action.act σ x.val, by
          constructor
          · rw [(scalarExtensionDatum K A).counit_equivariant, x.2.counit_eq_one]
            exact map_one σ
          · rw [(scalarExtensionDatum K A).comul_equivariant, x.2.comul_eq_tmul_self,
              SemilinearAction.tensor_act_tmul]⟩
      map_one' := GroupLike.val_injective ((scalarExtensionDatum K A).map_one σ)
      map_mul' := fun x y =>
        GroupLike.val_injective ((scalarExtensionDatum K A).map_mul σ x.val y.val) })
  map_one' := by
    apply End.ext
    apply CommGrpCat.ext
    intro x
    exact GroupLike.val_injective ((scalarExtensionDatum K A).action.one_act x.val)
  map_mul' σ τ := by
    apply End.ext
    apply CommGrpCat.ext
    intro x
    exact GroupLike.val_injective ((scalarExtensionDatum K A).action.mul_act σ τ x.val)

/-- An element of a scalar extension has an open stabilizer, since the scalars
of any finite tensor expression have open stabilizers. -/
private theorem openSubgroupFixingTensor [Algebra.IsIntegral k K] (x : K ⊗[k] A) :
    ∃ U : Subgroup Gal(K/k), IsOpen (U : Set Gal(K/k)) ∧
      ∀ σ ∈ U, (scalarExtensionDatum K A).action.act σ x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    refine ⟨MulAction.stabilizer Gal(K/k) a, stabilizer_isOpen_of_isIntegral a, ?_⟩
    intro σ hσ
    change σ a = a at hσ
    change σ a ⊗ₜ[k] b = a ⊗ₜ[k] b
    rw [hσ]
  | add a b ha hb =>
    obtain ⟨U, hU, ha⟩ := ha
    obtain ⟨V, hV, hb⟩ := hb
    exact ⟨U ⊓ V, hU.inter hV, fun σ hσ => by
      rw [map_add, ha σ hσ.1, hb σ hσ.2]⟩

end ScalarExtension


section ChangeOfField

variable (k K) (M : Type u) [CommGroup M]

set_option maxHeartbeats 600000 in
/-- Scalar extension of a split group algebra preserves every basis exponent. -/
def groupAlgebraBaseChange :
    (K ⊗[k] MonoidAlgebra k M) ≃ₐc[K] MonoidAlgebra K M := by
  let f := MonoidAlgebra.scalarTensorEquiv k K (M := M)
  have hf (a : K) (m : M) :
      f (a ⊗ₜ[k] MonoidAlgebra.single m (1 : k)) = MonoidAlgebra.single m a :=
    (f.toEquiv.eq_symm_apply).mp
      (MonoidAlgebra.scalarTensorEquiv_symm_single (R := k) (A := K) m a).symm
  refine BialgEquiv.ofAlgEquiv f ?_ ?_
  · apply Algebra.TensorProduct.ext_ring
    apply MonoidAlgebra.algHom_ext
    · intro m
      change counit (R := K) (f ((1 : K) ⊗ₜ[k] MonoidAlgebra.single m (1 : k))) =
        counit (R := K) ((1 : K) ⊗ₜ[k] MonoidAlgebra.single m (1 : k))
      rw [hf]
      simp [TensorProduct.counit_tmul]
    · ext
  · apply Algebra.TensorProduct.ext_ring
    apply MonoidAlgebra.algHom_ext
    · intro m
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Bialgebra.comulAlgHom_apply,
        TensorProduct.comul_tmul, CommSemiring.comul_apply, MonoidAlgebra.comul_single,
        TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        Algebra.TensorProduct.map_tmul, AlgEquiv.toAlgHom_apply, hf]
    · ext

end ChangeOfField


section BaseChangeCharacters

open private tensorAlong tensorAlong_tmul tensorAlong_injective comparison_comul_base comparison_counit_base
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

variable (K) (A : HopfAlgebraCategory k)

private abbrev includeScalarExtension : A →ₐ[k] (K ⊗[k] A) :=
  Algebra.TensorProduct.includeRight

private theorem includeScalarExtension_injective :
    Function.Injective (includeScalarExtension K A) :=
  Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective

private theorem includeTensor_injective :
    Function.Injective (tensorAlong (K := K) (includeScalarExtension K A)
      (includeScalarExtension K A)) := by
  have h : (includeScalarExtension K A).toLinearMap.liftBaseChange K =
      LinearMap.id (R := K) (M := K ⊗[k] A) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    simp [includeScalarExtension, TensorProduct.smul_tmul']
  exact tensorAlong_injective _ _ (h ▸ Function.injective_id) (h ▸ Function.injective_id)

private theorem comul_include (a : A) :
    comul (R := K) ((1 : K) ⊗ₜ[k] a) =
      tensorAlong (K := K) (includeScalarExtension K A)
        (includeScalarExtension K A) (comul (R := k) a) := by
  rw [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
  generalize comul (R := k) a = t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, tensorAlong_tmul]
    rfl
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- Extension and reflection of the two group-like identities under scalar extension. -/
theorem isGroupLikeElem_tmul_one_iff (a : A) :
    IsGroupLikeElem K ((1 : K) ⊗ₜ[k] a) ↔ IsGroupLikeElem k a := by
  change IsGroupLikeElem K (includeScalarExtension K A a) ↔ _
  have hc : counit (R := K) (includeScalarExtension K A a) =
      algebraMap k K (counit (R := k) a) :=
    comparison_counit_base (K := K) a
  have hd : comul (R := K) (includeScalarExtension K A a) =
      tensorAlong (K := K) (includeScalarExtension K A)
        (includeScalarExtension K A) (comul (R := k) a) :=
    comul_include K A a
  constructor
  · intro h
    constructor
    · apply (algebraMap k K).injective
      rw [← hc, h.counit_eq_one, map_one]
    · apply includeTensor_injective K A
      rw [← hd, tensorAlong_tmul, h.comul_eq_tmul_self]
  · intro h
    constructor
    · rw [hc, h.counit_eq_one, map_one]
    · rw [hd, h.comul_eq_tmul_self, tensorAlong_tmul]

/-- The natural map on group-like elements induced by field extension. -/
def baseChangeCharacterMap : GroupLike k A →* GeometricCharacters K A where
  toFun x := ⟨includeScalarExtension K A x.val, (isGroupLikeElem_tmul_one_iff K A x.val).2 x.2⟩
  map_one' := GroupLike.val_injective (map_one (includeScalarExtension K A))
  map_mul' x y := GroupLike.val_injective (map_mul (includeScalarExtension K A) x.val y.val)

theorem baseChangeCharacterMap_injective :
    Function.Injective (baseChangeCharacterMap K A) :=
  fun _ _ h => GroupLike.val_injective
    (includeScalarExtension_injective K A (congrArg GroupLike.val h))

variable {M : Type u} [CommGroup M]

private def monomialCharacter (k : Type u) [Field k] :
    M →* GroupLike k (groupAlgebra k M) where
  toFun m := ⟨MonoidAlgebra.of k M m, MonoidAlgebra.isGroupLikeElem_of m⟩
  map_one' := GroupLike.val_injective (map_one (MonoidAlgebra.of k M))
  map_mul' x y := GroupLike.val_injective (map_mul (MonoidAlgebra.of k M) x y)

/-- A homomorphism between Hopf algebras pulls back characters between their spectra. -/
def mapGroupLike {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    GroupLike k A →* GroupLike k B where
  toFun x := ⟨f.hom x.val, x.2.map f.hom⟩
  map_one' := GroupLike.val_injective (map_one f.hom)
  map_mul' x y := GroupLike.val_injective (map_mul f.hom x.val y.val)

private theorem mapGroupLike_id (A : HopfAlgebraCategory k) :
    mapGroupLike (𝟙 A) = MonoidHom.id _ := by
  ext x
  rfl

private theorem mapGroupLike_comp {A B C : HopfAlgebraCategory k} (f : A ⟶ B) (g : B ⟶ C) :
    mapGroupLike (f ≫ g) = (mapGroupLike g).comp (mapGroupLike f) := by
  ext x
  rfl

/-- Over a split group algebra, all characters are uniquely its basis exponents. -/
def monomialCharacterEquiv (k : Type u) [Field k] :
    M ≃* GroupLike k (groupAlgebra k M) :=
  MulEquiv.ofBijective (monomialCharacter k) ⟨
    fun _ _ h => MonoidAlgebra.of_injective (congrArg GroupLike.val h),
    fun x => by
      obtain ⟨m, hm⟩ := MonoidAlgebra.isGroupLikeElem_iff_mem_range_of.mp x.2
      exact ⟨m, GroupLike.val_injective hm⟩⟩

private def groupLikeIso {A B : HopfAlgebraCategory k} (e : A ≅ B) :
    GroupLike k A ≃* GroupLike k B :=
  MonoidHom.toMulEquiv (mapGroupLike e.hom) (mapGroupLike e.inv)
    (by rw [← mapGroupLike_comp, e.hom_inv_id, mapGroupLike_id])
    (by rw [← mapGroupLike_comp, e.inv_hom_id, mapGroupLike_id])

/-- Extension of scalars as a functor on coordinate Hopf algebras. -/
def extendedHopfFunctor : HopfAlgebraCategory k ⥤ HopfAlgebraCategory K where
  obj A := extendedHopf K A
  map f := extendedHopfMap K f
  map_id A := by
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.coe_toAlgHom_injective
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro a
    rfl
  map_comp f g := by
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.coe_toAlgHom_injective
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro a
    rfl

theorem baseChangeCharacterMap_bijective (h : IsDiagonalizable A) :
    Function.Bijective (baseChangeCharacterMap K A) := by
  refine ⟨baseChangeCharacterMap_injective K A, ?_⟩
  obtain ⟨M, ⟨e⟩⟩ := h
  let E := (extendedHopfFunctor K).mapIso e
  let d : groupAlgebra K M.obj ≅ extendedHopf K (groupAlgebra k M.obj) :=
    CommHopfAlgCat.isoMk (groupAlgebraBaseChange k K M.obj).symm
  intro y
  obtain ⟨m, hm⟩ := ((monomialCharacterEquiv K).trans (groupLikeIso (d ≪≫ E))).surjective y
  refine ⟨mapGroupLike e.hom (monomialCharacter k m), GroupLike.val_injective ?_⟩
  rw [← hm]
  change (1 : K) ⊗ₜ[k] e.hom.hom (MonoidAlgebra.single m (1 : k)) =
    (extendedHopfMap K e.hom).hom
      ((groupAlgebraBaseChange k K M.obj).symm (MonoidAlgebra.single m (1 : K)))
  have hd : (groupAlgebraBaseChange k K M.obj).symm (MonoidAlgebra.single m (1 : K)) =
      (1 : K) ⊗ₜ[k] MonoidAlgebra.single m (1 : k) :=
    MonoidAlgebra.scalarTensorEquiv_symm_single m 1
  rw [hd]
  rfl

end BaseChangeCharacters


section FieldTower

variable {L : Type u} [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
variable (L) (A : HopfAlgebraCategory k)

set_option maxHeartbeats 700000 in
/-- The canonical comparison for extending scalars twice, remembering the Hopf structure. -/
def extendedHopfTower :
    extendedHopf L (extendedHopf K A) ≅ extendedHopf L A := by
  let f := Algebra.TensorProduct.cancelBaseChange k K L L A
  have hf (r : L) (s : K) (a : A) :
      f (r ⊗ₜ[K] (s ⊗ₜ[k] a)) = (s • r) ⊗ₜ[k] a :=
    Algebra.TensorProduct.cancelBaseChange_tmul k K L L A r s a
  refine CommHopfAlgCat.isoMk (BialgEquiv.ofAlgEquiv f ?_ ?_)
  · apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      change counit (R := L) (f ((1 : L) ⊗ₜ[K] (s ⊗ₜ[k] a))) =
        counit (R := L) ((1 : L) ⊗ₜ[K] (s ⊗ₜ[k] a))
      rw [hf]
      simp [TensorProduct.counit_tmul, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply k K L, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  · apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Bialgebra.comulAlgHom_apply,
        AlgEquiv.toAlgHom_apply, hf, TensorProduct.comul_tmul, CommSemiring.comul_apply]
      generalize comul (R := k) a = t
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          Algebra.TensorProduct.map_tmul, AlgEquiv.toAlgHom_apply, hf, one_smul]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]

private theorem extendedHopfTower_symm_apply (r : L) (a : A) :
    (extendedHopfTower (K := K) L A).inv.hom (r ⊗ₜ[k] a) =
      r ⊗ₜ[K] ((1 : K) ⊗ₜ[k] a) :=
  Algebra.TensorProduct.cancelBaseChange_symm_tmul k K L L A r a

private theorem extendedHopfTower_apply (r : L) (s : K) (a : A) :
    (extendedHopfTower (K := K) L A).hom.hom (r ⊗ₜ[K] (s ⊗ₜ[k] a)) =
      (s • r) ⊗ₜ[k] a :=
  Algebra.TensorProduct.cancelBaseChange_tmul k K L L A r s a

end FieldTower

private theorem splitBaseChange (A : HopfAlgebraCategory k) (h : IsDiagonalizable A) :
    IsDiagonalizable (extendedHopf K A) := by
  obtain ⟨M, ⟨e⟩⟩ := h
  exact ⟨M, ⟨(CommHopfAlgCat.isoMk (groupAlgebraBaseChange k K M.obj)).symm ≪≫
    (extendedHopfFunctor K).mapIso e⟩⟩

theorem splitsOverSeparableClosure : SplitsOverSeparableClosure.{u} := by
  intro k K _ _ _ _ A
  constructor
  · rintro ⟨E, _, _, _, hE⟩
    let _ := IsSepClosure.sep_closed k (K := K)
    let embedding : E →ₐ[k] K := IsSepClosed.lift
    let _ : Algebra E K := embedding.toRingHom.toAlgebra
    let _ : IsScalarTower k E K := IsScalarTower.of_algebraMap_eq' embedding.comp_algebraMap.symm
    obtain ⟨M, ⟨e⟩⟩ := splitBaseChange (K := K) (extendedHopf E A) hE
    exact ⟨M, ⟨e ≪≫ extendedHopfTower K A⟩⟩
  · exact fun h => ⟨K, inferInstance, inferInstance, inferInstance, h⟩

open private liftCharacters liftCharacters_single liftCharacters_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private theorem groupLikeSpanOfSplit (A : HopfAlgebraCategory k) (h : IsDiagonalizable A) :
    Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤ := by
  obtain ⟨M, ⟨e⟩⟩ := h
  have : Group.FG M.obj := M.property
  have : Algebra.FiniteType k A :=
    Algebra.FiniteType.equiv (inferInstanceAs (Algebra.FiniteType k (MonoidAlgebra k M.obj)))
      (CommHopfAlgCat.ofIso e).toAlgEquiv
  exact (DiagonalizableGroups.groupLikeSpanning k A).2
    ⟨M.obj, inferInstance, M.property, ⟨CommHopfAlgCat.ofIso e⟩⟩

private def groupAlgebraOfCharacters (A : HopfAlgebraCategory k)
    (h : Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤) :
    groupAlgebra k (GroupLike k A) ≅ A := by
  let f := liftCharacters (MonoidHom.id (GroupLike k A))
  have hf : Function.Surjective f := by
    change Function.Surjective f.toAlgHom.toLinearMap
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← h]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact ⟨MonoidAlgebra.single x 1, liftCharacters_single _ x⟩
  exact CommHopfAlgCat.isoMk <|
    BialgEquiv.ofBijective f ⟨liftCharacters_injective _ Function.injective_id, hf⟩

private theorem charactersFG (A : HopfAlgebraCategory k) (h : IsDiagonalizable A) :
    Group.FG (GroupLike k A) := by
  obtain ⟨M, ⟨e⟩⟩ := h
  have : Group.FG M.obj := M.property
  let i := (monomialCharacterEquiv k).trans (groupLikeIso e)
  exact Group.fg_of_surjective (f := i.toMonoidHom) i.surjective

open private tensorAlong tensorAlong_tmul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

theorem multiplicativeTypeProperties : MultiplicativeTypeProperties.{u} := by
  intro k _ A
  rintro ⟨E, _, _, _, M, ⟨e⟩⟩
  have hsplit : IsDiagonalizable (extendedHopf E A) := ⟨M, ⟨e⟩⟩
  have : Group.FG M.obj := M.property
  have : Algebra.FiniteType E (E ⊗[k] A) :=
    Algebra.FiniteType.equiv (inferInstanceAs (Algebra.FiniteType E (MonoidAlgebra E M.obj)))
      (CommHopfAlgCat.ofIso e).toAlgEquiv
  refine ⟨Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat E,
    (hopfSpecCommutativity k A).mpr ?_⟩
  have : IsCocomm E (extendedHopf E A) := by
    constructor
    apply LinearMap.ext_on_range (groupLikeSpanOfSplit _ hsplit)
    intro x
    change TensorProduct.comm E _ _ (comul (R := E) x.val) = comul (R := E) x.val
    rw [x.2.comul_eq_tmul_self, TensorProduct.comm_tmul]
  let j := includeScalarExtension E A
  let t := tensorAlong (K := E) j j
  have ht (x : A ⊗[k] A) :
      t (TensorProduct.comm k A A x) = TensorProduct.comm E _ _ (t x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp only [t, TensorProduct.comm_tmul, tensorAlong_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  refine LinearMap.ext fun a => includeTensor_injective E A ?_
  change t (TensorProduct.comm k A A (comul (R := k) a)) = t (comul (R := k) a)
  rw [ht, show t (comul (R := k) a) = comul (R := E) (j a) from (comul_include E A a).symm]
  exact comm_comul (R := E) (A := extendedHopf E A) (j a)

theorem torusIsMultiplicativeType : TorusIsMultiplicativeType.{u} := by
  intro k _ A
  rintro ⟨E, _, _, _, r, ⟨e⟩⟩
  let i : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
  have h : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective (f := i.toMonoidHom) i.surjective
  have hfg : Group.FG (StandardLattice.{u} r) := by
    apply Group.fg_def.mpr
    simpa only [Subgroup.pi_top] using
      (Subgroup.FG.pi (P := fun (_ : Fin r) => (⊤ : Subgroup IntegerCharacters)) fun _ =>
        Group.fg_def.mp h)
  exact ⟨E, inferInstance, inferInstance, inferInstance,
    ⟨⟨CommGrpCat.of _, hfg⟩, ⟨e⟩⟩⟩


section FixedElements

open private repr_act from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
open private tensorAlong tensorAlong_tmul comparison_counit_base
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

variable (K) [IsGalois k K]

private theorem scalarExtension_fixed_surjective (V : Type u) [AddCommGroup V] [Module k V] :
    Function.Surjective (SemilinearAction.scalarExtensionComparison (k := k) (K := K) V) := by
  classical
  let b := Module.Free.chooseBasis k V
  let s := SemilinearAction.scalarExtension (k := k) (K := K) V
  have hb (i : _) : b.baseChange K i ∈ s.fixed := by
    intro σ
    simp [s]
  intro x
  have h (i : _) : ∃ a : k, algebraMap k K a = (b.baseChange K).repr x.val i := by
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := k) _).2
    intro σ
    rw [← repr_act s (b.baseChange K) hb σ, x.property σ]
  choose a ha using h
  refine ⟨∑ i ∈ ((b.baseChange K).repr x.val).support, a i • b i, Subtype.ext ?_⟩
  change (1 : K) ⊗ₜ[k] (∑ i ∈ ((b.baseChange K).repr x.val).support, a i • b i) = x.val
  rw [TensorProduct.tmul_sum]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans ((b.baseChange K).linearCombination_repr x.val)
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ha]
  change _ = ((b.baseChange K).repr x.val i) • (b.baseChange K i)
  rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable (A : HopfAlgebraCategory k)

private theorem fixedElements (x : K ⊗[k] A)
    (h : ∀ σ, (scalarExtensionDatum K A).action.act σ x = x) :
    ∃ a : A, (1 : K) ⊗ₜ[k] a = x := by
  obtain ⟨a, ha⟩ := scalarExtension_fixed_surjective K A ⟨x, h⟩
  exact ⟨a, congrArg Subtype.val ha⟩

variable {A} {B : HopfAlgebraCategory k}

private def descendEquivariantAlg (f : extendedHopf K A ⟶ extendedHopf K B)
    (hf : (scalarExtensionDatum K A).Equivariant (scalarExtensionDatum K B) f) :
    A →ₐ[k] B :=
  (AlgEquiv.ofInjective (includeScalarExtension K B) (includeScalarExtension_injective K B)).symm.toAlgHom.comp <|
    (((f.hom.toAlgHom.restrictScalars k).comp (includeScalarExtension K A)).codRestrict
      (includeScalarExtension K B).range fun x => by
      change ∃ y, includeScalarExtension K B y = f.hom (includeScalarExtension K A x)
      apply fixedElements K B
      intro σ
      have hx : (scalarExtensionDatum K A).action.act σ (includeScalarExtension K A x) =
          includeScalarExtension K A x := by
        change σ 1 ⊗ₜ[k] x = (1 : K) ⊗ₜ[k] x
        rw [map_one]
      exact (hf σ (includeScalarExtension K A x)).symm.trans (congrArg f.hom hx))

private theorem descendEquivariantAlg_spec (f : extendedHopf K A ⟶ extendedHopf K B)
    (hf : (scalarExtensionDatum K A).Equivariant (scalarExtensionDatum K B) f) (x : A) :
    includeScalarExtension K B (descendEquivariantAlg K f hf x) =
      f.hom (includeScalarExtension K A x) := by
  let e := AlgEquiv.ofInjective (includeScalarExtension K B) (includeScalarExtension_injective K B)
  change (e (e.symm ⟨f.hom (includeScalarExtension K A x), _⟩)).val = _
  rw [e.apply_symm_apply]

/-- Equivariant maps between scalar extensions descend along any Galois extension. -/
private theorem descendEquivariantHopfMap
    (f : extendedHopf K A ⟶ extendedHopf K B)
    (hf : (scalarExtensionDatum K A).Equivariant (scalarExtensionDatum K B) f) :
    ∃ g : A ⟶ B, extendedHopfMap K g = f := by
  let g := descendEquivariantAlg K f hf
  have hg (x : A) : includeScalarExtension K B (g x) = f.hom (includeScalarExtension K A x) :=
    descendEquivariantAlg_spec K f hf x
  let gb := BialgHom.ofAlgHom g (by
    apply AlgHom.ext
    intro x
    apply (algebraMap k K).injective
    change algebraMap k K (counit (R := k) (g x)) = algebraMap k K (counit (R := k) x)
    rw [← comparison_counit_base (K := K) (g x), ← comparison_counit_base (K := K) x]
    change counit (R := K) (includeScalarExtension K B (g x)) =
      counit (R := K) (includeScalarExtension K A x)
    rw [hg, CoalgHomClass.counit_comp_apply]) (by
    apply AlgHom.ext
    intro x
    apply includeTensor_injective K B
    have ht (t : A ⊗[k] A) :
        tensorAlong (K := K) (includeScalarExtension K B) (includeScalarExtension K B)
          (Algebra.TensorProduct.map g g t) =
        Algebra.TensorProduct.map f.hom.toAlgHom f.hom.toAlgHom
          (tensorAlong (K := K) (includeScalarExtension K A) (includeScalarExtension K A) t) := by
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, tensorAlong_tmul, hg]
        rfl
      | add a b ha hb => simp only [map_add, ha, hb]
    change tensorAlong (K := K) (includeScalarExtension K B) (includeScalarExtension K B)
        (Algebra.TensorProduct.map g g (comul (R := k) x)) =
      tensorAlong (K := K) (includeScalarExtension K B) (includeScalarExtension K B) (comul (R := k) (g x))
    rw [ht, ← comul_include K A, ← comul_include K B]
    change Algebra.TensorProduct.map f.hom.toAlgHom f.hom.toAlgHom
      (comul (R := K) (includeScalarExtension K A x)) =
        comul (R := K) (includeScalarExtension K B (g x))
    rw [hg]
    exact CoalgHomClass.map_comp_comul_apply f.hom _)
  refine ⟨CommHopfAlgCat.ofHom gb, ?_⟩
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  exact hg

end FixedElements


section GeometricFunctor

variable (K) [IsSepClosure k K]

private theorem geometricActionContinuous (A : HopfAlgebraCategory k) :
    HasContinuousAction
      (⟨CommGrpCat.of (GeometricCharacters K A), geometricAction K A⟩ :
        Action CommGrpCat Gal(K/k)) := by
  intro x
  let ρ := actionAutomorphisms
    (⟨CommGrpCat.of (GeometricCharacters K A), geometricAction K A⟩ :
      Action CommGrpCat Gal(K/k))
  let _ : MulAction Gal(K/k) (GeometricCharacters K A) :=
    MulAction.compHom _ ρ
  obtain ⟨U, hU, hf⟩ := openSubgroupFixingTensor K A x.val
  have h : U ≤ MulAction.stabilizer Gal(K/k) x := by
    intro σ hσ
    exact GroupLike.val_injective (hf σ hσ)
  exact Subgroup.isOpen_mono h hU

omit [IsSepClosure k K] in
private theorem extendedHopfMap_equivariant {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    (scalarExtensionDatum K A).Equivariant (scalarExtensionDatum K B) (extendedHopfMap K f) := by
  intro σ x
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem geometricHopfMaps_ext {A B : HopfAlgebraCategory K}
    (hA : IsDiagonalizable A) {f g : A ⟶ B}
    (h : ∀ x : GroupLike K A, (mapGroupLike f) x = (mapGroupLike g) x) : f = g := by
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  apply AlgHom.toLinearMap_injective
  apply LinearMap.ext_on_range (groupLikeSpanOfSplit A hA)
  exact fun x => congrArg GroupLike.val (h x)

/-- The geometric character functor in the covariant coordinate-Hopf-algebra convention. -/
def geometricCharacterFunctor : MultiplicativeTypeHopf k ⥤ CharacterModule k K where
  obj A := ⟨⟨CommGrpCat.of (GeometricCharacters K A.obj.val), geometricAction K A.obj.val⟩,
    charactersFG (extendedHopf K A.obj.val) ((splitsOverSeparableClosure A.obj.val).mp A.property),
    geometricActionContinuous K A.obj.val⟩
  map f := ObjectProperty.homMk
    { hom := CommGrpCat.ofHom (mapGroupLike (extendedHopfMap K f.hom.hom))
      comm := fun σ => by
        apply CommGrpCat.ext
        intro x
        exact GroupLike.val_injective (extendedHopfMap_equivariant K f.hom.hom σ x.val) }
  map_id A := by
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply CommGrpCat.ext
    intro x
    change (mapGroupLike ((extendedHopfFunctor K).map (𝟙 A.obj.val))) x = x
    rw [(extendedHopfFunctor K).map_id A.obj.val, mapGroupLike_id]
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply CommGrpCat.ext
    intro x
    change (mapGroupLike ((extendedHopfFunctor K).map (f.hom.hom ≫ g.hom.hom))) x =
      (mapGroupLike (extendedHopfMap K g.hom.hom)) ((mapGroupLike (extendedHopfMap K f.hom.hom)) x)
    rw [Functor.map_comp, mapGroupLike_comp]
    rfl

private theorem geometricCharacterFunctor_faithful : (geometricCharacterFunctor (k := k) K).Faithful := by
  constructor
  intro A B f g h
  have heq : extendedHopfMap K f.hom.hom = extendedHopfMap K g.hom.hom :=
    geometricHopfMaps_ext K ((splitsOverSeparableClosure A.obj.val).mp A.property) <| fun x =>
      DFunLike.congr_fun (congrArg (fun p => p.hom.hom.hom) h) x
  apply ObjectProperty.hom_ext
  apply InducedCategory.hom_ext
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro a
  apply includeScalarExtension_injective K B.obj.val
  exact congrArg (fun e => e.hom ((1 : K) ⊗ₜ[k] a)) heq

private theorem groupAlgebraOfCharacters_hom_single {A : HopfAlgebraCategory K}
    (h : Submodule.span K (Set.range (GroupLike.val (R := K) (A := A))) = ⊤)
    (x : GroupLike K A) :
    (groupAlgebraOfCharacters A h).hom.hom (MonoidAlgebra.single x (1 : K)) = x.val :=
  liftCharacters_single (MonoidHom.id _) x

private theorem geometricCharacterFunctor_full : (geometricCharacterFunctor (k := k) K).Full := by
  constructor
  intro A B g
  let C := extendedHopf K A.obj.val
  let T := extendedHopf K B.obj.val
  have hC := groupLikeSpanOfSplit C ((splitsOverSeparableClosure A.obj.val).mp A.property)
  let e := groupAlgebraOfCharacters C hC
  let g₀ : GroupLike K C →* GroupLike K T := g.hom.hom.hom
  let f : C ⟶ T := e.inv ≫ CommHopfAlgCat.ofHom (liftCharacters g₀)
  have hf (x : GroupLike K C) : f.hom x.val = (g₀ x).val := by
    rw [← groupAlgebraOfCharacters_hom_single K hC x]
    change (e.hom ≫ f).hom (MonoidAlgebra.single x 1) = _
    simp only [f, Iso.hom_inv_id_assoc]
    exact liftCharacters_single g₀ x
  have heq : (scalarExtensionDatum K A.obj.val).Equivariant (scalarExtensionDatum K B.obj.val) f := by
    intro σ a
    obtain ⟨x, rfl⟩ := (CommHopfAlgCat.ofIso e).surjective a
    change f.hom ((scalarExtensionDatum K A.obj.val).action.act σ (e.hom.hom x)) =
      (scalarExtensionDatum K B.obj.val).action.act σ (f.hom (e.hom.hom x))
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single x r =>
      have hr : MonoidAlgebra.single x r = r • MonoidAlgebra.single x (1 : K) := by
        simp
      rw [hr, map_smul, groupAlgebraOfCharacters_hom_single,
        (scalarExtensionDatum K A.obj.val).action.map_smul, map_smul,
        map_smul, hf, (scalarExtensionDatum K B.obj.val).action.map_smul]
      have hcomm := DFunLike.congr_fun (congrArg CommGrpCat.Hom.hom (g.hom.comm σ)) x
      change g₀ ((geometricAction K A.obj.val σ).asHom x) =
        (geometricAction K B.obj.val σ).asHom (g₀ x) at hcomm
      congr 1
      change f.hom (((geometricAction K A.obj.val σ).asHom x).val) = _
      rw [hf]
      exact congrArg GroupLike.val hcomm
  obtain ⟨g₁, hg₁⟩ := descendEquivariantHopfMap K f heq
  refine ⟨ObjectProperty.homMk (InducedCategory.homMk g₁), ?_⟩
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  apply CommGrpCat.ext
  intro x
  apply GroupLike.val_injective
  change (extendedHopfMap K g₁).hom x.val = (g₀ x).val
  rw [hg₁]
  exact hf x

end GeometricFunctor


section ScalarExtensionOfDescent

variable {L M : Type u} [Field L] [CommGroup M]
variable [Algebra k L] [Algebra K L] [IsScalarTower k K L] [Normal k K]

private theorem operator_mapCoefficients (σ : Gal(L/k)) (e : M ≃* M) (x : MonoidAlgebra K M) :
    groupAlgebraOperator σ e (MonoidAlgebra.mapAlgHom M (Algebra.ofId K L) x) =
      MonoidAlgebra.mapAlgHom M (Algebra.ofId K L) (groupAlgebraOperator (σ.restrictNormal K) e x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m a =>
    simp only [MonoidAlgebra.mapAlgHom_single, operator_single, Algebra.ofId_apply]
    rw [σ.restrictNormal_commutes]

private def extendDescentComparison {D : HopfDescentDatum k (groupAlgebra K M)}
    (H : HopfDescent D) : extendedHopf L H.algebra ≅ groupAlgebra L M :=
  (extendedHopfTower (K := K) L H.algebra).symm ≪≫ (extendedHopfFunctor L).mapIso H.iso ≪≫
    CommHopfAlgCat.isoMk (groupAlgebraBaseChange K L M)

omit [Normal k K] in
private theorem extendDescentComparison_tmul {D : HopfDescentDatum k (groupAlgebra K M)}
    (H : HopfDescent D) (r : L) (x : D.fixed) :
    (extendDescentComparison (L := L) H).hom.hom (r ⊗ₜ[k] x) =
      r • MonoidAlgebra.mapAlgHom M (Algebra.ofId K L) x.val := by
  change (groupAlgebraBaseChange K L M)
    ((extendedHopfMap L H.iso.hom).hom ((extendedHopfTower (K := K) L H.algebra).inv.hom
      (r ⊗ₜ[k] x))) = _
  rw [extendedHopfTower_symm_apply]
  change (groupAlgebraBaseChange K L M) (r ⊗ₜ[K] H.comparison ((1 : K) ⊗ₜ[k] x)) = _
  rw [H.comparison_tmul, one_smul]
  exact MonoidAlgebra.scalarTensorEquiv_tmul (R := K) (A := L) r x.val

private theorem extendDescentComparison_equivariant
    {D : HopfDescentDatum k (groupAlgebra K M)} (H : HopfDescent D)
    (ρ : Gal(K/k) →* MulAut M)
    (hD : ∀ g, D.action.act g = (groupAlgebraOperator g (ρ g)).toAddEquiv)
    (σ : Gal(L/k)) (a : L ⊗[k] H.algebra) :
    (extendDescentComparison (L := L) H).hom.hom
        ((scalarExtensionDatum L H.algebra).action.act σ a) =
      groupAlgebraOperator σ (ρ (σ.restrictNormal K)) ((extendDescentComparison (L := L) H).hom.hom a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r x =>
    change (extendDescentComparison (L := L) H).hom.hom (σ r ⊗ₜ[k] x) = _
    rw [extendDescentComparison_tmul, extendDescentComparison_tmul]
    have h := (groupAlgebraSemilinearAction (ρ.comp (AlgEquiv.restrictNormalHom K))).map_smul σ r
      (MonoidAlgebra.mapAlgHom M (Algebra.ofId K L) x.val)
    change groupAlgebraOperator σ (ρ (σ.restrictNormal K))
      (r • MonoidAlgebra.mapAlgHom M (Algebra.ofId K L) x.val) =
      σ r • groupAlgebraOperator σ (ρ (σ.restrictNormal K))
        (MonoidAlgebra.mapAlgHom M (Algebra.ofId K L) x.val) at h
    rw [h, operator_mapCoefficients]
    have hx := x.property (σ.restrictNormal K)
    rw [hD] at hx
    change groupAlgebraOperator (σ.restrictNormal K) (ρ (σ.restrictNormal K)) x.val = x.val at hx
    rw [hx]
  | add a b ha hb => simp only [map_add, ha, hb]

end ScalarExtensionOfDescent

theorem finiteDescentCharacters : FiniteDescentCharacters.{u} := by
  intro k K S _ _ _ _ _ _ _ _ _ _ M _ ρ D H hD
  let j := extendDescentComparison (L := S) H
  let e := (monomialCharacterEquiv S).trans (groupLikeIso j.symm)
  have he (m : M) : j.hom.hom (e m).val = MonoidAlgebra.single m (1 : S) :=
    CommHopfAlgCat.hom_inv_apply j (MonoidAlgebra.single m 1)
  refine ⟨e, j, extendDescentComparison_tmul H, he, ?_⟩
  intro σ m
  apply (CommHopfAlgCat.ofIso j).injective
  change j.hom.hom ((scalarExtensionDatum S H.algebra).action.act σ (e m).val) =
    j.hom.hom (e (ρ (σ.restrictNormal K) m)).val
  rw [extendDescentComparison_equivariant H ρ hD, he, he, operator_single, map_one]

section EssentialSurjectivity

variable (K) [IsSepClosure k K]

private theorem finiteModelOfCharacters (M : CharacterModule k K) :
    ∃ (A : MultiplicativeTypeHopf k) (E : IntermediateField k K)
      (_ : FiniteDimensional k E) (_ : IsGalois k E),
      IsDiagonalizable (extendedHopf E A.obj.val) ∧
      Nonempty ((geometricCharacterFunctor K).obj A ≅ M) := by
  obtain ⟨E, hE, hN, ρ, hρ⟩ := factorsThroughFiniteGalois M
  let _ := hE
  let _ := hN
  let _ : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E K
  let _ : IsGalois k E := ⟨⟩
  have : Group.FG M.obj.V := M.property.1
  obtain ⟨D, H, hD, hft, _, hH, _⟩ := finiteGroupAlgebraDescent ρ
  let A : MultiplicativeTypeHopf k := ⟨⟨H.algebra, hft⟩, hH⟩
  obtain ⟨i, _, _, _, hi⟩ := finiteDescentCharacters (S := K) ρ D H hD
  refine ⟨A, E, hE, inferInstance,
    ⟨⟨M.obj.V, M.property.1⟩, ⟨H.iso.symm⟩⟩,
    ⟨(ObjectProperty.isoMk _ (Action.mkIso
    (M := M.obj) (N := ((geometricCharacterFunctor K).obj A).obj) i.toCommGrpIso ?_)).symm⟩⟩
  intro σ
  apply CommGrpCat.ext
  intro x
  apply GroupLike.val_injective
  change (i ((M.obj.ρ σ).asHom x)).val =
    (SemilinearAction.scalarExtension (K := K) H.algebra).act σ (i x).val
  rw [hρ, hi]
  rfl

private theorem geometricCharacterFunctor_essSurj :
    (geometricCharacterFunctor (k := k) K).EssSurj := by
  constructor
  intro M
  obtain ⟨A, _, _, _, _, h⟩ := finiteModelOfCharacters K M
  exact ⟨A, h⟩

theorem geometricCharacterAntiequivalence : GeometricCharacterAntiequivalence.{u} := by
  intro k K _ _ _ _
  refine ⟨geometricCharacterFunctor K, ?_, fun _ => MulEquiv.refl _, ?_, ?_⟩
  · exact ⟨geometricCharacterFunctor_faithful K, geometricCharacterFunctor_full K,
      geometricCharacterFunctor_essSurj K⟩
  · intros
    rfl
  · intros
    rfl

end EssentialSurjectivity


theorem torusAndSplitCriteria : TorusAndSplitCriteria.{u} := by
  intro k K _ _ _ _ A hA
  have hs : IsDiagonalizable (extendedHopf K A) := (splitsOverSeparableClosure A).mp hA
  constructor
  · constructor
    · rintro ⟨E, _, _, _, r, ⟨e⟩⟩
      let _ := IsSepClosure.sep_closed k (K := K)
      let embedding : E →ₐ[k] K := IsSepClosed.lift
      let _ : Algebra E K := embedding.toRingHom.toAlgebra
      let _ : IsScalarTower k E K := IsScalarTower.of_algebraMap_eq' embedding.comp_algebraMap.symm
      let f : groupAlgebra K (StandardLattice.{u} r) ≅ extendedHopf K A :=
        (CommHopfAlgCat.isoMk (groupAlgebraBaseChange E K _)).symm ≪≫
          (extendedHopfFunctor K).mapIso e ≪≫ extendedHopfTower K A
      exact ⟨r, ⟨((monomialCharacterEquiv K).trans (groupLikeIso f)).symm⟩⟩
    · rintro ⟨r, ⟨i⟩⟩
      let f := CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv K K i.symm) ≪≫
        groupAlgebraOfCharacters (extendedHopf K A) (groupLikeSpanOfSplit _ hs)
      exact ⟨K, inferInstance, inferInstance, inferInstance, r, ⟨f⟩⟩
  · constructor
    · intro h σ x
      obtain ⟨a, rfl⟩ := (baseChangeCharacterMap_bijective K A h).2 x
      change σ 1 ⊗ₜ[k] a.val = (1 : K) ⊗ₜ[k] a.val
      rw [map_one]
    · intro h
      have hsur : Function.Surjective (baseChangeCharacterMap K A) := by
        intro x
        obtain ⟨a, ha⟩ := fixedElements K A x.val (fun σ => h σ x)
        have hg : IsGroupLikeElem k a :=
          (isGroupLikeElem_tmul_one_iff K A a).mp (by rw [ha]; exact x.2)
        exact ⟨⟨a, hg⟩, GroupLike.val_injective ha⟩
      let f := liftCharacters (MonoidHom.id (GroupLike k A))
      let l := f.toAlgHom.toLinearMap
      have hf : Function.Surjective l := by
        apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective k K l).mp
        change Function.Surjective (l.baseChange K)
        apply LinearMap.range_eq_top.mp
        rw [← top_le_iff, ← groupLikeSpanOfSplit _ hs]
        apply Submodule.span_le.mpr
        rintro _ ⟨x, rfl⟩
        obtain ⟨a, rfl⟩ := hsur x
        refine ⟨(1 : K) ⊗ₜ[k] MonoidAlgebra.single a 1, ?_⟩
        rw [LinearMap.baseChange_tmul]
        change (1 : K) ⊗ₜ[k] f (MonoidAlgebra.single a 1) = (1 : K) ⊗ₜ[k] a.val
        rw [liftCharacters_single]
        rfl
      let i := MulEquiv.ofBijective (baseChangeCharacterMap K A)
        ⟨baseChangeCharacterMap_injective K A, hsur⟩
      have : Group.FG (GeometricCharacters K A) := charactersFG _ hs
      have hi : Group.FG (GroupLike k A) := Group.fg_of_surjective (f := i.symm.toMonoidHom) i.symm.surjective
      exact ⟨⟨CommGrpCat.of (GroupLike k A), hi⟩, ⟨CommHopfAlgCat.isoMk
        (BialgEquiv.ofBijective f ⟨liftCharacters_injective _ Function.injective_id, hf⟩)⟩⟩


section BaseChangeOfAction

variable {L S : Type u} [Field L] [Field S]
variable [Algebra k L] [Algebra k S] [Algebra K S] [Algebra L S]
variable [IsScalarTower k K S] [IsScalarTower k L S]
variable (S) (A : HopfAlgebraCategory k)

private abbrev mapTensorCoefficients : K ⊗[k] A →ₐ[k] S ⊗[k] A :=
  Algebra.TensorProduct.map ((Algebra.ofId K S).restrictScalars k) (AlgHom.id k A)

private theorem mapTensorCoefficients_eq (x : K ⊗[k] A) :
    (extendedHopfTower (K := K) S A).hom.hom ((1 : S) ⊗ₜ[K] x) =
      mapTensorCoefficients S A x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [extendedHopfTower_apply]
    simp [mapTensorCoefficients, Algebra.smul_def]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

variable [IsSepClosure k K]

private theorem mapTensorCoefficients_equivariant (σ : Gal(S/L)) (x : K ⊗[k] A) :
    mapTensorCoefficients S A
        ((SemilinearAction.scalarExtension (K := K) A).act
          ((σ.restrictScalars k).restrictNormal K) x) =
      (SemilinearAction.scalarExtension (k := k) (K := S) A).act
        (σ.restrictScalars k) (mapTensorCoefficients S A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [SemilinearAction.scalarExtension_act_tmul, mapTensorCoefficients,
      Algebra.TensorProduct.map_tmul, AlgHom.restrictScalars_apply, Algebra.ofId_apply,
      AlgHom.id_apply]
    rw [(σ.restrictScalars k).restrictNormal_commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem towerEquivariant (σ : Gal(S/L)) (x : S ⊗[k] A) :
    (extendedHopfTower (K := L) S A).inv.hom
        ((SemilinearAction.scalarExtension (k := k) (K := S) A).act
          (σ.restrictScalars k) x) =
      (SemilinearAction.scalarExtension (K := S) (extendedHopf L A)).act σ
        ((extendedHopfTower (K := L) S A).inv.hom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [SemilinearAction.scalarExtension_act_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem baseChangeRestrictsAction : BaseChangeRestrictsAction.{u} := by
  intro k K L S _ _ _ _ _ _ _ _ _ _ _ _ _ A hA
  have h : IsDiagonalizable (extendedHopf K A) := (splitsOverSeparableClosure A).mp hA
  let i := MulEquiv.ofBijective (baseChangeCharacterMap S (extendedHopf K A))
    (baseChangeCharacterMap_bijective S _ h)
  let f := extendedHopfTower (K := K) S A
  let g := extendedHopfTower (K := L) S A
  let e := (i.trans (groupLikeIso f)).trans (groupLikeIso g.symm)
  have hsplit : IsDiagonalizable (extendedHopf S (extendedHopf L A)) := by
    obtain ⟨M, ⟨d⟩⟩ := splitBaseChange (K := S) _ h
    exact ⟨M, ⟨d ≪≫ f ≪≫ g.symm⟩⟩
  have he (x : GeometricCharacters K A) : (e x).val = g.inv.hom (mapTensorCoefficients S A x.val) := by
    change g.inv.hom (f.hom.hom ((1 : S) ⊗ₜ[K] x.val)) = _
    rw [mapTensorCoefficients_eq S A]
  refine ⟨⟨S, inferInstance, inferInstance, inferInstance, hsplit⟩, e, ?_, ?_⟩
  · intro x
    change g.hom.hom (e x).val = _
    rw [he]
    exact CommHopfAlgCat.hom_inv_apply g _
  · intro σ x y hxy
    rw [he, he, ← towerEquivariant, ← mapTensorCoefficients_equivariant, hxy]

end BaseChangeOfAction


private theorem extendedHopfFunctor_faithful (K : Type u) [Field K] [Algebra k K] :
    (extendedHopfFunctor (k := k) K).Faithful := by
  constructor
  intro A B f g h
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro a
  apply includeScalarExtension_injective K B
  exact congrArg (fun e => e.hom ((1 : K) ⊗ₜ[k] a)) h

private theorem isoHomEquivariant_symm {A B : HopfAlgebraCategory K}
    (e : A ≅ B) (D : SemilinearAction k K A) (E : SemilinearAction k K B)
    (h : D.Equivariant E e.hom.hom.toLinearMap) :
    E.Equivariant D e.inv.hom.toLinearMap := by
  intro σ x
  apply (CommHopfAlgCat.ofIso e).injective
  change e.hom.hom (e.inv.hom (E.act σ x)) = e.hom.hom (D.act σ (e.inv.hom x))
  rw [CommHopfAlgCat.hom_inv_apply]
  exact ((h σ (e.inv.hom x)).trans (congrArg (E.act σ) (CommHopfAlgCat.hom_inv_apply e x))).symm

private theorem descendEquivariantComparison [IsGalois k K]
    {A B : HopfAlgebraCategory k} {T : HopfAlgebraCategory K} (D : SemilinearAction k K T)
    (e : extendedHopf K A ≅ T) (e' : extendedHopf K B ≅ T)
    (he : (scalarExtensionDatum K A).action.Equivariant D e.hom.hom.toLinearMap)
    (he' : (scalarExtensionDatum K B).action.Equivariant D e'.hom.hom.toLinearMap) :
    ∃ i : A ≅ B, extendedHopfMap K i.hom = e.hom ≫ e'.inv := by
  have fwd : (scalarExtensionDatum K A).Equivariant (scalarExtensionDatum K B) (e.hom ≫ e'.inv) := by
    intro σ x
    exact (congrArg e'.inv.hom (he σ x)).trans
      (isoHomEquivariant_symm e' _ _ he' σ (e.hom.hom x))
  have rev : (scalarExtensionDatum K B).Equivariant (scalarExtensionDatum K A) (e'.hom ≫ e.inv) := by
    intro σ x
    exact (congrArg e.inv.hom (he' σ x)).trans
      (isoHomEquivariant_symm e _ _ he σ (e'.hom.hom x))
  obtain ⟨f, hf⟩ := descendEquivariantHopfMap K _ fwd
  obtain ⟨g, hg⟩ := descendEquivariantHopfMap K _ rev
  let F := extendedHopfFunctor (k := k) K
  let _ : F.Faithful := extendedHopfFunctor_faithful K
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply F.map_injective
    rw [F.map_comp, F.map_id]
    change extendedHopfMap K f ≫ extendedHopfMap K g = _
    rw [hf, hg]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
    rfl
  · apply F.map_injective
    rw [F.map_comp, F.map_id]
    change extendedHopfMap K g ≫ extendedHopfMap K f = _
    rw [hg, hf]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
    rfl

theorem descentIndependentOfField : DescentIndependentOfField.{u} := by
  intro k K L _ _ _ _ _ _ _ _ _ _ _ M _ _ ρ D D' H H' hD hD'
  let e := extendDescentComparison (L := L) H
  have he : (scalarExtensionDatum L H.algebra).action.Equivariant D'.action e.hom.hom.toLinearMap := by
    intro σ x
    rw [hD']
    exact extendDescentComparison_equivariant H ρ hD σ x
  have he' : (scalarExtensionDatum L H'.algebra).action.Equivariant
      D'.action H'.iso.hom.hom.toLinearMap := comparison_equivariant H'
  obtain ⟨i, hi⟩ := descendEquivariantComparison D'.action e H'.iso he he'
  have hi' (x : D.fixed) :
      (i.hom.hom x).val = MonoidAlgebra.mapAlgHom M (Algebra.ofId K L) x.val := by
    have h := congrArg (fun (u : extendedHopf L H.algebra ⟶ extendedHopf L H'.algebra) =>
      H'.iso.hom.hom (u.hom ((1 : L) ⊗ₜ[k] x))) hi
    change H'.comparison ((1 : L) ⊗ₜ[k] i.hom.hom x) =
      H'.iso.hom.hom (H'.iso.inv.hom (e.hom.hom ((1 : L) ⊗ₜ[k] x))) at h
    rw [H'.comparison_tmul, one_smul, CommHopfAlgCat.hom_inv_apply,
      extendDescentComparison_tmul, one_smul] at h
    exact h
  refine ⟨i, hi', fun j hj => ?_⟩
  apply Iso.ext
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro x
  apply Subtype.ext
  exact (hj x).trans (hi' x).symm


section SchemeCharacters

open WithConv
open scoped MonObj

open private integerHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private def integerHopfHomEquiv (A : HopfAlgebraCategory k) :
    GroupLike k A ≃ (groupAlgebra k IntegerCharacters ⟶ A) where
  toFun x := CommHopfAlgCat.ofHom (liftCharacters (integerHomEquiv _ x))
  invFun f := mapGroupLike f (monomialCharacter k integerGenerator)
  left_inv x := by
    apply GroupLike.val_injective
    change liftCharacters (integerHomEquiv _ x) (MonoidAlgebra.single integerGenerator 1) = x.val
    rw [liftCharacters_single]
    exact congrArg GroupLike.val ((integerHomEquiv _).left_inv x)
  right_inv f := by
    let a := (mapGroupLike f).comp (monomialCharacter k (M := IntegerCharacters))
    have h : integerHomEquiv _ (a integerGenerator) = a :=
      (integerHomEquiv _).apply_symm_apply a
    apply CommHopfAlgCat.hom_ext
    change liftCharacters (integerHomEquiv _ (a integerGenerator)) = f.hom
    rw [h]
    apply MonoidAlgebra.bialgHom_ext
    · intro m
      rw [liftCharacters_single]
      rfl
    · ext

private theorem integerHopfHomEquiv_generator (A : HopfAlgebraCategory k) (x : GroupLike k A) :
    (integerHopfHomEquiv A x).hom (MonoidAlgebra.of k _ integerGenerator) = x.val :=
  congrArg GroupLike.val ((integerHopfHomEquiv A).left_inv x)

private def schemeHopfHomEquiv (A B : HopfAlgebraCategory k) :
    (A ⟶ B) ≃ (specGroup B ⟶ specGroup A) :=
  (CategoryTheory.opEquiv (op B) (op A)).symm.trans
    (hopfSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv

private theorem specGroupMap_convMul {A B : HopfAlgebraCategory k}
    [IsCocomm k A] [IsCommMonObj (specGroup A).X] (f g : A ⟶ B) :
    specGroupMap (CommHopfAlgCat.ofHom (toConv f.hom * toConv g.hom).ofConv) =
      specGroupMap f * specGroupMap g := by
  apply Grp.hom_ext
  exact (Spec.mapMulEquiv (R := k) (S := A) (T := B)).map_mul
    (toConv f.hom.toAlgHom) (toConv g.hom.toAlgHom)

private theorem convMul_apply_groupLike {A B : HopfAlgebraCategory k} [IsCocomm k A]
    (f g : A ⟶ B) (x : GroupLike k A) :
    (toConv f.hom * toConv g.hom).ofConv x.val = f.hom x.val * g.hom x.val := by
  change (toConv f.hom.toAlgHom * toConv g.hom.toAlgHom).ofConv x.val = _
  rw [AlgHom.convMul_apply, x.2.comul_eq_tmul_self, Algebra.TensorProduct.lift_tmul]
  rfl

/-- A character pulls the standard coordinate on Gm back to its group-like element. -/
def groupLikeCharacterEquiv (A : HopfAlgebraCategory k) :
    GroupLike k A ≃* Character (specGroup A) where
  toEquiv := (integerHopfHomEquiv A).trans (schemeHopfHomEquiv _ _)
  map_mul' x y := by
    let f := integerHopfHomEquiv A x
    let g := integerHopfHomEquiv A y
    change specGroupMap (integerHopfHomEquiv A (x * y)) = specGroupMap f * specGroupMap g
    rw [← specGroupMap_convMul]
    congr 1
    apply (integerHopfHomEquiv A).symm.injective
    rw [Equiv.symm_apply_apply]
    apply GroupLike.val_injective
    let t := monomialCharacter (M := IntegerCharacters) k integerGenerator
    change x.val * y.val = (toConv f.hom * toConv g.hom).ofConv t.val
    rw [convMul_apply_groupLike f g t]
    exact (congrArg₂ (· * ·) (integerHopfHomEquiv_generator A x)
      (integerHopfHomEquiv_generator A y)).symm

theorem characterInterpretation : CharacterInterpretation.{u} := by
  intro k _
  refine ⟨groupLikeCharacterEquiv, ?_, ?_⟩
  · intro A B f x
    change specGroupMap ((integerHopfHomEquiv B) (mapGroupLike f x)) =
      specGroupMap f ≫ specGroupMap ((integerHopfHomEquiv A) x)
    rw [← specGroupMap_comp]
    congr 1
    apply (integerHopfHomEquiv B).symm.injective
    rw [Equiv.symm_apply_apply]
    change _ = mapGroupLike ((integerHopfHomEquiv A) x ≫ f) (monomialCharacter k integerGenerator)
    rw [mapGroupLike_comp]
    change _ = mapGroupLike f ((integerHopfHomEquiv A).symm ((integerHopfHomEquiv A) x))
    rw [Equiv.symm_apply_apply]
  · intro A x
    exact ⟨integerHopfHomEquiv A x, integerHopfHomEquiv_generator A x, rfl⟩

theorem standardSplitTorus : StandardSplitTorus.{u} := by
  intro k _ r
  let i : Multiplicative (ULift.{u} (Fin r) → ℤ) ≃* StandardLattice.{u} r :=
    { toFun := fun v j => ⟨Multiplicative.ofAdd (v.toAdd ⟨j⟩)⟩
      invFun := fun w => Multiplicative.ofAdd (fun j => (w j.down).down.toAdd)
      left_inv := by intro v; rfl
      right_inv := by intro w; rfl
      map_mul' := by intros; rfl }
  let e := (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k (ULift.{u} (Fin r) → ℤ)).trans
    (MonoidAlgebra.domCongrBialgEquiv k k i)
  exact ⟨(hopfSpec (CommRingCat.of k)).mapIso (CommHopfAlgCat.isoMk e).op⟩

private def splitGroupHomEquiv (M N : Type u) [CommGroup M] [CommGroup N] :
    (M →* N) ≃* (specGroup (groupAlgebra k N) ⟶ specGroup (groupAlgebra k M)) where
  toEquiv :=
    ((MonoidAlgebra.mapDomainBialgHomEquiv (R := k)).trans
      { toFun := CommHopfAlgCat.ofHom
        invFun := CommHopfAlgCat.Hom.hom
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }).trans (schemeHopfHomEquiv _ _)
  map_mul' f g := by
    change specGroupMap (groupAlgebraMap k (f * g)) =
      specGroupMap (groupAlgebraMap k f) * specGroupMap (groupAlgebraMap k g)
    rw [← specGroupMap_convMul]
    congr 1
    apply CommHopfAlgCat.hom_ext
    apply MonoidAlgebra.bialgHom_ext
    · intro m
      let x := monomialCharacter (M := M) k m
      change (groupAlgebraMap k (f * g)).hom x.val =
        (toConv (groupAlgebraMap k f).hom * toConv (groupAlgebraMap k g).hom).ofConv x.val
      rw [convMul_apply_groupLike]
      change MonoidAlgebra.mapDomainBialgHom k (f * g) (MonoidAlgebra.single m 1) =
        MonoidAlgebra.mapDomainBialgHom k f (MonoidAlgebra.single m 1) *
          MonoidAlgebra.mapDomainBialgHom k g (MonoidAlgebra.single m 1)
      simp only [MonoidAlgebra.mapDomainBialgHom_single, MonoidAlgebra.single_mul_single,
        MonoidHom.mul_apply, mul_one]
    · ext

theorem splitCompositionPairing : SplitCompositionPairing.{u} := by
  intro k _ r
  let M := StandardLattice.{u} r
  let e := (monomialCharacterEquiv (M := M) k).trans (groupLikeCharacterEquiv (groupAlgebra k M))
  let f := splitGroupHomEquiv (k := k) M IntegerCharacters
  have he (m : M) : e m = specGroupMap (groupAlgebraMap k ((zpowersHom M m).comp
      MulEquiv.ulift.toMonoidHom)) := by
    change specGroupMap (integerHopfHomEquiv (groupAlgebra k M) (monomialCharacter k m)) = _
    congr 1
    apply (integerHopfHomEquiv (groupAlgebra k M)).symm.injective
    rw [Equiv.symm_apply_apply]
    apply GroupLike.val_injective
    change MonoidAlgebra.single m (1 : k) =
      MonoidAlgebra.mapDomainBialgHom k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)
        (MonoidAlgebra.single integerGenerator 1)
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    change MonoidAlgebra.single m (1 : k) = MonoidAlgebra.single (m ^ (1 : ℤ)) (1 : k)
    rw [zpow_one]
  refine ⟨e, f, he, fun _ => rfl, ?_⟩
  intro m v
  change f v ≫ e m = _
  rw [he]
  change specGroupMap (groupAlgebraMap k v) ≫ _ = _
  rw [← specGroupMap_comp]
  congr 1
  apply CommHopfAlgCat.hom_ext
  change (MonoidAlgebra.mapDomainBialgHom k v).comp
      (MonoidAlgebra.mapDomainBialgHom k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)) = _
  rw [← MonoidAlgebra.mapDomainBialgHom_comp]
  congr 1
  apply MonoidHom.ext
  intro a
  exact map_zpow v m a.down.toAdd

end SchemeCharacters

theorem descentIndependentOfTwoFields : DescentIndependentOfTwoFields.{u} := by
  intro k K L S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ ρ τ D D' H H' hρ hD hD'
  let e := extendDescentComparison (L := S) H
  let e' := extendDescentComparison (L := S) H'
  let action : SemilinearAction k S (MonoidAlgebra S M) :=
    groupAlgebraSemilinearAction (ρ.comp (AlgEquiv.restrictNormalHom K))
  have he : (scalarExtensionDatum S H.algebra).action.Equivariant action e.hom.hom.toLinearMap :=
    extendDescentComparison_equivariant H ρ hD
  have he' : (scalarExtensionDatum S H'.algebra).action.Equivariant action e'.hom.hom.toLinearMap := by
    intro σ x
    change e'.hom.hom ((scalarExtensionDatum S H'.algebra).action.act σ x) =
      groupAlgebraOperator σ (ρ (σ.restrictNormal K)) (e'.hom.hom x)
    rw [hρ]
    exact extendDescentComparison_equivariant H' τ hD' σ x
  obtain ⟨i, hi⟩ := descendEquivariantComparison action e e' he he'
  let f := MonoidAlgebra.mapAlgHom M (Algebra.ofId L S)
  let g := MonoidAlgebra.mapAlgHom M (Algebra.ofId K S)
  have hi' (x : D.fixed) : f (i.hom.hom x).val = g x.val := by
    have h := congrArg (fun (u : extendedHopf S H.algebra ⟶ extendedHopf S H'.algebra) =>
      e'.hom.hom (u.hom ((1 : S) ⊗ₜ[k] x))) hi
    change e'.hom.hom ((1 : S) ⊗ₜ[k] i.hom.hom x) =
      e'.hom.hom (e'.inv.hom (e.hom.hom ((1 : S) ⊗ₜ[k] x))) at h
    rw [CommHopfAlgCat.hom_inv_apply, extendDescentComparison_tmul,
      extendDescentComparison_tmul, one_smul, one_smul] at h
    exact h
  refine ⟨i, hi', fun j hj => ?_⟩
  apply Iso.ext
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro x
  apply Subtype.ext
  have hinj : Function.Injective f := by
    intro a b h
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro m
    apply (algebraMap L S).injective
    simpa only [f, MonoidAlgebra.coeff_mapAlgHom, Algebra.ofId_apply] using
      congrArg (fun z : MonoidAlgebra S M => z.coeff m) h
  exact hinj ((hj x).trans (hi' x).symm)

theorem compatibleSeparableClosures : CompatibleSeparableClosures.{u} := by
  intro k L _ _ _
  let K := separableClosure k (AlgebraicClosure L)
  let S := SeparableClosure L
  let f : K →ₐ[k] S :=
    IntermediateField.inclusion (separableClosure.le_restrictScalars k L (AlgebraicClosure L))
  let a : Algebra K S := f.toRingHom.toAlgebra
  let _ := a
  exact ⟨a, IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm⟩

open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

theorem multiplicativeTypeOnSchemes : MultiplicativeTypeOnSchemes.{u} := by
  intro k _ A
  constructor
  · rintro ⟨E, _, _, _, M, ⟨e⟩⟩
    exact ⟨E, inferInstance, inferInstance, inferInstance, M,
      ⟨(extendedGroupIso E A).symm ≪≫ (hopfSpec (CommRingCat.of E)).mapIso e.op⟩⟩
  · rintro ⟨E, _, _, _, M, ⟨e⟩⟩
    let f := (hopfSpec.fullyFaithful (R := CommRingCat.of E)).preimageIso
      (extendedGroupIso E A ≪≫ e)
    exact ⟨E, inferInstance, inferInstance, inferInstance, M, ⟨f.unop⟩⟩

theorem multiplicativeTypeGroupCriterion : MultiplicativeTypeGroupCriterion.{u} := by
  intro k _ G
  let U : AffineAlgebraicGroupCategory k ⥤ GroupScheme k := inducedFunctor Subtype.val
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    obtain ⟨E, _, _, _, M, ⟨d⟩⟩ :=
      (multiplicativeTypeOnSchemes X.unop.obj.val).mp X.unop.property
    exact ⟨E, inferInstance, inferInstance, inferInstance, M,
      ⟨(groupBaseChange k E).mapIso (U.mapIso e).symm ≪≫ d⟩⟩
  · rintro ⟨E, _, _, _, M, ⟨d⟩⟩
    let _ := finiteTypeHopfSpecEquivalence k
    let X := (finiteTypeHopfSpec k).objPreimage G
    let e := (finiteTypeHopfSpec k).objObjPreimageIso G
    have hX : IsMultiplicativeType X.unop.val :=
      (multiplicativeTypeOnSchemes X.unop.val).mpr
        ⟨E, inferInstance, inferInstance, inferInstance, M,
          ⟨(groupBaseChange k E).mapIso (U.mapIso e) ≪≫ d⟩⟩
    exact ⟨op ⟨X.unop, hX⟩, ⟨e⟩⟩

theorem torusOnSchemes : TorusOnSchemes.{u} := by
  intro k _ A
  constructor
  · rintro ⟨E, _, _, _, r, ⟨e⟩⟩
    obtain ⟨i⟩ := standardSplitTorus (k := E) r
    exact ⟨E, inferInstance, inferInstance, inferInstance, r, ⟨
      (extendedGroupIso E A).symm ≪≫ (hopfSpec (CommRingCat.of E)).mapIso e.op ≪≫ i⟩⟩
  · rintro ⟨E, _, _, _, r, ⟨e⟩⟩
    obtain ⟨i⟩ := standardSplitTorus (k := E) r
    let f := (hopfSpec.fullyFaithful (R := CommRingCat.of E)).preimageIso
      (extendedGroupIso E A ≪≫ e ≪≫ i.symm)
    exact ⟨E, inferInstance, inferInstance, inferInstance, r, ⟨f.unop⟩⟩

theorem geometricCharacterSchemeAntiequivalence : GeometricCharacterSchemeAntiequivalence.{u} := by
  intro k K _ _ _ _
  have hSpec : (multiplicativeTypeSpecFunctor k).toEssImage.IsEquivalence := by
    let _ := finiteTypeHopfSpecEquivalence k
    unfold multiplicativeTypeSpecFunctor
    infer_instance
  obtain ⟨F, hF, i, ha, hm⟩ := geometricCharacterAntiequivalence (k := k) (K := K)
  let d := (multiplicativeTypeSpecFunctor k).toEssImage.asEquivalence.rightOp
  refine ⟨d.symm.trans F.asEquivalence, F, hF, ⟨?_⟩, i, ha, hm⟩
  change d.functor ⋙ (d.inverse ⋙ F) ≅ F
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight d.unitIso.symm F ≪≫ Functor.leftUnitor F


theorem finiteGaloisSplitting : FiniteGaloisSplitting.{u} := by
  intro k K _ _ _ _ A hA
  let X : MultiplicativeTypeHopf k := ⟨⟨A, (multiplicativeTypeProperties A hA).1⟩, hA⟩
  let F := geometricCharacterFunctor (k := k) K
  let _ : F.IsEquivalence := ⟨geometricCharacterFunctor_faithful K,
    geometricCharacterFunctor_full K, geometricCharacterFunctor_essSurj K⟩
  obtain ⟨B, E, hE, hG, ⟨M, ⟨j⟩⟩, ⟨i⟩⟩ := finiteModelOfCharacters K (F.obj X)
  let U : MultiplicativeTypeHopf k ⥤ HopfAlgebraCategory k :=
    ObjectProperty.ι _ ⋙ inducedFunctor Subtype.val
  exact ⟨E, hE, hG, M, ⟨j ≪≫ (U ⋙ extendedHopfFunctor E).mapIso (F.preimageIso i)⟩⟩

end

end LinearAlgebraicGroups.CharacterDescent
