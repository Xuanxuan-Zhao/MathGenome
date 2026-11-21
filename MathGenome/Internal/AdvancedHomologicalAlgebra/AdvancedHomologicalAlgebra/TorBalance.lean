import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TorBalance
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions
import Mathlib.Algebra.Category.ModuleCat.Ulift

noncomputable section
open CategoryTheory CategoryTheory.Limits
open P103.BalancedTensor
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Specs.Ch02.FlatnessTests
universe u v w x
namespace AdvancedHomologicalAlgebra.TorBalance

theorem balance : Specs.Balance.{u,v,w} := P103.Ch11.TorBalance.balance

theorem augmentation_naturality : Specs.AugmentationNaturality.{u,v,w} :=
  P103.Ch11.TorBalance.augmentation_natural

theorem balance_naturality : Specs.BalanceNaturality.{u,v,w} :=
  P103.Ch11.TorBalance.balanceEquiv_natural

theorem lift_independence : Specs.LiftIndependence.{u,v,w} :=
  P103.Ch11.TorBalance.lift_independent

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Exactness preserves the kernel and cokernel defining each homology object. -/
def exactHomologyComparison
    {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] : HomologyComparison F where
  equivalence S := (S.mapHomologyIso F).symm
  cyclesEquivalence S := (S.mapCyclesIso F).symm
  inclusion S := by
    rw [← cancel_epi (S.mapCyclesIso F).hom]
    simp only [Iso.symm_hom, Iso.hom_inv_id_assoc, ShortComplex.mapCyclesIso_hom_iCycles]
  projection S := by
    rw [← cancel_epi (S.mapCyclesIso F).hom, ← cancel_mono (S.mapHomologyIso F).hom]
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
    symm
    rw [S.leftHomologyData.mapHomologyIso_eq F, S.leftHomologyData.mapCyclesIso_eq F]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
      Category.assoc]
    change (S.leftHomologyData.map F).cyclesIso.hom ≫
      F.map S.leftHomologyData.π ≫ F.map S.leftHomologyData.homologyIso.inv = _
    rw [← F.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
    rw [F.map_comp]
  naturality f := ShortComplex.mapHomologyIso_inv_naturality f F

/-- Universe enlargement in P103 flatness can test terms in any smaller universe. -/
theorem flat_tensor_injective {R : Type u} [Ring R] {M : Type w}
    [AddCommGroup M] [Module R M] (hM : Flat.{u,w,v} R M)
    {A B : Type v} [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B]
    (f : A →ₗ[Rᵐᵒᵖ] B) (hf : Function.Injective f) :
    Function.Injective (tensorMap f (LinearMap.id : M →ₗ[R] M)) := by
  let eA : ULift.{max u v w} A ≃ₗ[Rᵐᵒᵖ] A := ULift.moduleEquiv
  let eB : ULift.{max u v w} B ≃ₗ[Rᵐᵒᵖ] B := ULift.moduleEquiv
  let f' := eB.symm.toLinearMap.comp (f.comp eA.toLinearMap)
  have hinj := hM _ _ f' (eB.symm.injective.comp (hf.comp eA.injective))
    (tensorMap f' (LinearMap.id : M →ₗ[R] M)).toAddMonoidHom (by intros; rfl)
  have hrect : (tensorMap f' (LinearMap.id : M →ₗ[R] M)).comp
      (tensorMap eA.symm.toLinearMap LinearMap.id) =
      (tensorMap eB.symm.toLinearMap LinearMap.id).comp (tensorMap f LinearMap.id) := by
    apply tensor_hom_ext
    intro a m
    rfl
  have hback : (tensorMap eA.toLinearMap (LinearMap.id : M →ₗ[R] M)).comp
      (tensorMap eA.symm.toLinearMap LinearMap.id) = LinearMap.id := by
    apply tensor_hom_ext
    intro a m
    rfl
  intro a b hab
  have h' : tensorMap eA.symm.toLinearMap LinearMap.id a =
      tensorMap eA.symm.toLinearMap LinearMap.id b := by
    apply hinj
    change ((tensorMap f' (LinearMap.id : M →ₗ[R] M)).comp
      (tensorMap eA.symm.toLinearMap LinearMap.id)) a =
        ((tensorMap f' (LinearMap.id : M →ₗ[R] M)).comp
          (tensorMap eA.symm.toLinearMap LinearMap.id)) b
    rw [hrect]
    exact congrArg (tensorMap eB.symm.toLinearMap LinearMap.id) hab
  have hh := congrArg (tensorMap eA.toLinearMap (LinearMap.id : M →ₗ[R] M)) h'
  change ((tensorMap eA.toLinearMap (LinearMap.id : M →ₗ[R] M)).comp
    (tensorMap eA.symm.toLinearMap LinearMap.id)) a =
      ((tensorMap eA.toLinearMap (LinearMap.id : M →ₗ[R] M)).comp
        (tensorMap eA.symm.toLinearMap LinearMap.id)) b at hh
  simpa only [hback, LinearMap.id_apply] using hh

theorem flat_tensor_exact {R : Type u} [Ring R] {M : Type w}
    [AddCommGroup M] [Module R M] (hM : Flat.{u,w,v} R M)
    {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] [Module Rᵐᵒᵖ C]
    (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C) (he : Function.Exact f g) :
    Function.Exact (tensorMap f (LinearMap.id : M →ₗ[R] M))
      (tensorMap g (LinearMap.id : M →ₗ[R] M)) := by
  have he' : Function.Exact f g.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    simpa only [LinearMap.ker_rangeRestrict] using LinearMap.exact_iff.mp he
  have hr := (P103.HomTensorExactness.tensor_first_rightExact f g.rangeRestrict he'
    (LinearMap.surjective_rangeRestrict g)
    (tensorMap f (LinearMap.id : M →ₗ[R] M)).toAddMonoidHom (by intros; rfl)
    (tensorMap g.rangeRestrict LinearMap.id).toAddMonoidHom (by intros; rfl)).1
  have hi := flat_tensor_injective hM (LinearMap.range g).subtype Subtype.val_injective
  have hc : (tensorMap (LinearMap.range g).subtype (LinearMap.id : M →ₗ[R] M)).comp
      (tensorMap g.rangeRestrict LinearMap.id) = tensorMap g LinearMap.id := by
    apply tensor_hom_ext
    intro a m
    rfl
  intro z
  rw [← hc]
  change tensorMap (LinearMap.range g).subtype LinearMap.id
    (tensorMap g.rangeRestrict (LinearMap.id : M →ₗ[R] M) z) = 0 ↔ _
  rw [← map_zero (tensorMap (LinearMap.range g).subtype (LinearMap.id : M →ₗ[R] M)),
    hi.eq_iff]
  exact hr z

theorem flat_tensor_preservesHomology {R : Type u} [Ring R] {M : Type w}
    [AddCommGroup M] [Module R M] (hM : Flat.{u,w,v} R M) :
    (tensorFunctor M : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  apply ModuleCat.shortComplex_exact
  exact flat_tensor_exact hM S.f.hom S.g.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS)

theorem flat_left_comparison : Specs.FlatLeftComparison.{u,v,w} := by
  intro R _ M _ _ hM
  have := flat_tensor_preservesHomology hM
  exact ⟨exactHomologyComparison (tensorFunctor M)⟩

theorem right_flat_tensor_injective {R : Type u} [Ring R] {M : Type w}
    [AddCommGroup M] [Module Rᵐᵒᵖ M] (hM : RightFlat.{u,w,v} R M)
    {A B : Type v} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Injective f) :
    Function.Injective (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f) := by
  let eA : ULift.{max u v w} A ≃ₗ[R] A := ULift.moduleEquiv
  let eB : ULift.{max u v w} B ≃ₗ[R] B := ULift.moduleEquiv
  let f' := eB.symm.toLinearMap.comp (f.comp eA.toLinearMap)
  have hinj := hM _ _ f' (eB.symm.injective.comp (hf.comp eA.injective))
    (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f').toAddMonoidHom (by intros; rfl)
  have hrect : (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f').comp
      (tensorMap LinearMap.id eA.symm.toLinearMap) =
      (tensorMap LinearMap.id eB.symm.toLinearMap).comp (tensorMap LinearMap.id f) := by
    apply tensor_hom_ext
    intro m a
    rfl
  have hback : (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) eA.toLinearMap).comp
      (tensorMap LinearMap.id eA.symm.toLinearMap) = LinearMap.id := by
    apply tensor_hom_ext
    intro m a
    rfl
  intro a b hab
  have h' : tensorMap LinearMap.id eA.symm.toLinearMap a =
      tensorMap LinearMap.id eA.symm.toLinearMap b := by
    apply hinj
    change ((tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f').comp
      (tensorMap LinearMap.id eA.symm.toLinearMap)) a =
        ((tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f').comp
          (tensorMap LinearMap.id eA.symm.toLinearMap)) b
    rw [hrect]
    exact congrArg (tensorMap LinearMap.id eB.symm.toLinearMap) hab
  have hh := congrArg (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) eA.toLinearMap) h'
  change ((tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) eA.toLinearMap).comp
    (tensorMap LinearMap.id eA.symm.toLinearMap)) a =
      ((tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) eA.toLinearMap).comp
        (tensorMap LinearMap.id eA.symm.toLinearMap)) b at hh
  simpa only [hback, LinearMap.id_apply] using hh

theorem right_flat_tensor_exact {R : Type u} [Ring R] {M : Type w}
    [AddCommGroup M] [Module Rᵐᵒᵖ M] (hM : RightFlat.{u,w,v} R M)
    {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (he : Function.Exact f g) :
    Function.Exact (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f)
      (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) g) := by
  have he' : Function.Exact f g.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    simpa only [LinearMap.ker_rangeRestrict] using LinearMap.exact_iff.mp he
  have hr := (P103.HomTensorExactness.tensorSecond_rightExact f g.rangeRestrict he'
    (LinearMap.surjective_rangeRestrict g)
    (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f).toAddMonoidHom
    (tensorMap LinearMap.id g.rangeRestrict).toAddMonoidHom (by intros; rfl) (by intros; rfl)).1
  have hi := right_flat_tensor_injective hM (LinearMap.range g).subtype Subtype.val_injective
  have hc : (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) (LinearMap.range g).subtype).comp
      (tensorMap LinearMap.id g.rangeRestrict) = tensorMap LinearMap.id g := by
    apply tensor_hom_ext
    intro m a
    rfl
  intro z
  rw [← hc]
  change tensorMap LinearMap.id (LinearMap.range g).subtype
    (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) g.rangeRestrict z) = 0 ↔ _
  rw [← map_zero (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) (LinearMap.range g).subtype),
    hi.eq_iff]
  exact hr z

theorem right_flat_tensor_preservesHomology {R : Type u} [Ring R] {M : Type w}
    [AddCommGroup M] [Module Rᵐᵒᵖ M] (hM : RightFlat.{u,w,v} R M) :
    (leftTensorFunctor M : ModuleCat.{v} R ⥤ ModuleCat.{max v w} ℤ).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  apply ModuleCat.shortComplex_exact
  exact right_flat_tensor_exact hM S.f.hom S.g.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS)

theorem flat_right_comparison : Specs.FlatRightComparison.{u,v,w} := by
  intro R _ M _ _ hM
  have := right_flat_tensor_preservesHomology hM
  exact ⟨exactHomologyComparison (leftTensorFunctor M)⟩

theorem balanced_identification : Specs.BalancedIdentification.{u,v,w} := by
  intro R _ A M _ _ _ _ P Q hP hQ
  obtain ⟨α, hL, hR⟩ := balance R A M P Q hP hQ
  exact ⟨α, hL, hR, fun n => ⟨balanceEquiv α hL hR n, rfl,
    P103.Ch11.TorBalance.balanceEquiv_apply_left α hL hR n⟩⟩

theorem resolution_independence : Specs.ResolutionIndependence.{u,v,w} :=
  P103.Ch11.ExtTorDefinitions.tor_coherent

theorem exactHomologyComparison_compatible
    {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [F.PreservesHomology] [G.PreservesHomology] (τ : F ⟶ G) :
    ComparisonCompatible (exactHomologyComparison F) (exactHomologyComparison G) τ := by
  intro S
  change τ.app S.homology ≫ (S.mapHomologyIso G).inv =
    (S.mapHomologyIso F).inv ≫ ShortComplex.homologyMap (S.mapNatTrans τ)
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Iso.inv_hom_id_assoc]

theorem flat_left_naturality : Specs.FlatLeftNaturality.{u,v,w} := by
  intro R _ M N _ _ _ _ hM hN g
  have := flat_tensor_preservesHomology hM
  have := flat_tensor_preservesHomology hN
  exact ⟨exactHomologyComparison _, exactHomologyComparison _,
    exactHomologyComparison_compatible (tensorCoefficientMap g)⟩

theorem flat_right_naturality : Specs.FlatRightNaturality.{u,v,w} := by
  intro R _ A B _ _ _ _ hA hB f
  have := right_flat_tensor_preservesHomology hA
  have := right_flat_tensor_preservesHomology hB
  exact ⟨exactHomologyComparison _, exactHomologyComparison _,
    exactHomologyComparison_compatible (leftTensorCoefficientMap f)⟩

theorem flat_left_chain_comparison : Specs.FlatLeftChainComparison.{u,v,w} := by
  intro R _ M _ _ hM C n
  obtain ⟨c⟩ := flat_left_comparison R M hM
  exact ⟨c.equivalence (C.sc n), c.cyclesEquivalence (C.sc n),
    c.inclusion (C.sc n), c.projection (C.sc n)⟩

theorem flat_right_chain_comparison : Specs.FlatRightChainComparison.{u,v,w} := by
  intro R _ A _ _ hA C n
  obtain ⟨c⟩ := flat_right_comparison R A hA
  exact ⟨c.equivalence (C.sc n), c.cyclesEquivalence (C.sc n),
    c.inclusion (C.sc n), c.projection (C.sc n)⟩

theorem left_resolution_independence : Specs.LeftResolutionIndependence.{u,v,w} := by
  intro R _ A _ _ n
  exact P103.Ch10.Comparison.chain_homology_functorial R ℤ (leftTensorFunctor A) n

theorem tor_identification : Specs.TorIdentification.{u,v,w} := by
  intro R _ T A M P Q hP hQ
  obtain ⟨α, hL, hR⟩ := balance R A M P Q hP hQ
  refine ⟨α, hL, hR, ?_⟩
  intro n
  obtain ⟨c⟩ := resolution_independence R M n
  let e : TorWith P M n ≃ₗ[ℤ] T.Tor A M n :=
    (c.comparison ⟨P,hP⟩ (T.rightResolutions A)).toLinearEquiv
  refine ⟨e, (balanceEquiv α hL hR n).symm.trans e, ?_⟩
  apply LinearEquiv.ext
  intro z
  change e z = e ((balanceEquiv α hL hR n).symm ((balanceEquiv α hL hR n) z))
  exact (congrArg e ((balanceEquiv α hL hR n).symm_apply_apply z)).symm

namespace LinearChainMap

open P103.Specs.Ch10.Complexes
universe a b d e
variable {S : Type u} [Ring S] {ι : Type x} {c : ComplexShape ι}
  {K : HomologicalComplex (ModuleCat.{a} S) c}
  {L : HomologicalComplex (ModuleCat.{b} S) c}

protected def id (K : HomologicalComplex (ModuleCat.{a} S) c) : LinearChainMap K K where
  app _ := LinearMap.id
  comm _ _ := by simp

protected def comp {N : HomologicalComplex (ModuleCat.{d} S) c}
    (g : LinearChainMap L N) (f : LinearChainMap K L) : LinearChainMap K N where
  app n := (g.app n).comp (f.app n)
  comm i j := by rw [← LinearMap.comp_assoc, g.comm, LinearMap.comp_assoc, f.comm,
    ← LinearMap.comp_assoc]

@[simp] theorem id_app (n : ι) : (LinearChainMap.id K).app n = LinearMap.id := rfl

@[simp] theorem comp_app {N : HomologicalComplex (ModuleCat.{d} S) c}
    (g : LinearChainMap L N) (f : LinearChainMap K L) (n : ι) :
    (g.comp f).app n = (g.app n).comp (f.app n) := rfl

theorem eq_of_app_eq {f g : LinearChainMap K L} (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

theorem comm_apply (f : LinearChainMap K L) (i j : ι) (z : K.X i) :
    (L.d i j).hom (f.app i z) = f.app j ((K.d i j).hom z) :=
  LinearMap.congr_fun (f.comm i j) z

@[simp] theorem homologyMap_id (n : ι) : (LinearChainMap.id K).homologyMap n = LinearMap.id := by
  apply (cycleBoundaries K n).quot_hom_ext
  intro z
  rfl

@[simp] theorem homologyMap_comp {N : HomologicalComplex (ModuleCat.{d} S) c}
    (g : LinearChainMap L N) (f : LinearChainMap K L) (n : ι) :
    (g.comp f).homologyMap n = (g.homologyMap n).comp (f.homologyMap n) := by
  apply (cycleBoundaries K n).quot_hom_ext
  intro z
  rfl

theorem isQuasiIso_ofHom {L : HomologicalComplex (ModuleCat.{a} S) c}
    {f : K ⟶ L} (h : QuasiIsomorphism f) : (LinearChainMap.ofHom f).IsQuasiIso := h

theorem IsQuasiIso.comp {N : HomologicalComplex (ModuleCat.{d} S) c}
    {g : LinearChainMap L N} {f : LinearChainMap K L}
    (hg : g.IsQuasiIso) (hf : f.IsQuasiIso) : (g.comp f).IsQuasiIso := by
  intro n
  rw [homologyMap_comp]
  exact (hg n).comp (hf n)

theorem isQuasiIso_of_homology_inverse (f : LinearChainMap K L) (g : LinearChainMap L K)
    (h₁ : ∀ n, (g.comp f).homologyMap n = LinearMap.id)
    (h₂ : ∀ n, (f.comp g).homologyMap n = LinearMap.id) : f.IsQuasiIso := by
  intro n
  simp only [homologyMap_comp] at h₁ h₂
  have hleft : Function.LeftInverse (g.homologyMap n) (f.homologyMap n) :=
    LinearMap.congr_fun (h₁ n)
  have hright : Function.RightInverse (g.homologyMap n) (f.homologyMap n) :=
    LinearMap.congr_fun (h₂ n)
  exact ⟨hleft.injective, hright.surjective⟩

theorem isQuasiIso_of_inverse (f : LinearChainMap K L) (g : LinearChainMap L K)
    (h₁ : g.comp f = LinearChainMap.id K) (h₂ : f.comp g = LinearChainMap.id L) :
    f.IsQuasiIso :=
  f.isQuasiIso_of_homology_inverse g (by simp [h₁]) (by simp [h₂])

theorem homologyMap_square
    {K' : HomologicalComplex (ModuleCat.{d} S) c}
    {L' : HomologicalComplex (ModuleCat.{e} S) c}
    (f : LinearChainMap K L) (g : LinearChainMap K' L')
    (α : LinearChainMap K K') (β : LinearChainMap L L')
    (h : ∀ n, (β.app n).comp (f.app n) = (g.app n).comp (α.app n)) (n : ι) :
    (β.homologyMap n).comp (f.homologyMap n) =
      (g.homologyMap n).comp (α.homologyMap n) := by
  rw [← homologyMap_comp, ← homologyMap_comp,
    eq_of_app_eq (f := β.comp f) (g := g.comp α) (funext h)]

private def extendApp {K : ChainComplex (ModuleCat.{a} S) ℕ}
    {L : ChainComplex (ModuleCat.{b} S) ℕ} (f : LinearChainMap K L) (i : ℤ) :
    (extendNonnegativeChain K).X i →ₗ[S] (extendNonnegativeChain L).X i :=
  if h : 0 ≤ i then
    let hi : nonnegativeChainEmbedding.f i.toNat = i := Int.toNat_of_nonneg h
    (L.extendXIso nonnegativeChainEmbedding hi).inv.hom.comp
      ((f.app i.toNat).comp (K.extendXIso nonnegativeChainEmbedding hi).hom.hom)
  else 0

private theorem extendApp_cast {K : ChainComplex (ModuleCat.{a} S) ℕ}
    {L : ChainComplex (ModuleCat.{b} S) ℕ} (f : LinearChainMap K L) (i : ℕ) :
    extendApp f (i : ℤ) =
      (L.extendXIso nonnegativeChainEmbedding (i := i) rfl).inv.hom.comp
        ((f.app i).comp (K.extendXIso nonnegativeChainEmbedding (i := i) rfl).hom.hom) := by
  simp [extendApp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero across independent module universes. -/
def extendNonnegative {K : ChainComplex (ModuleCat.{a} S) ℕ}
    {L : ChainComplex (ModuleCat.{b} S) ℕ} (f : LinearChainMap K L) :
    LinearChainMap (extendNonnegativeChain K) (extendNonnegativeChain L) where
  app := extendApp f
  comm i j := by
    by_cases hi : 0 ≤ i
    · by_cases hj : 0 ≤ j
      · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hi
        obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hj
        rw [extendApp_cast, extendApp_cast]
        change LinearMap.comp
            ((L.extend nonnegativeChainEmbedding).d (nonnegativeChainEmbedding.f i)
              (nonnegativeChainEmbedding.f j)).hom _ =
          LinearMap.comp _ ((K.extend nonnegativeChainEmbedding).d (nonnegativeChainEmbedding.f i)
            (nonnegativeChainEmbedding.f j)).hom
        rw [L.extend_d_eq nonnegativeChainEmbedding (i := i) (j := j) rfl rfl,
          K.extend_d_eq nonnegativeChainEmbedding (i := i) (j := j) rfl rfl]
        ext z
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
          ModuleCat.hom_inv_apply]
        rw [f.comm_apply]
      · have := P103.Ch10.Complexes.extendNonnegativeChain_supported L j (by simpa using hj)
        ext z
        exact Subsingleton.elim _ _
    · have := P103.Ch10.Complexes.extendNonnegativeChain_supported K i (by simpa using hi)
      ext z
      simp [Subsingleton.elim z (0 : (extendNonnegativeChain K).X i)]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem extendNonnegative_app_inv {K : ChainComplex (ModuleCat.{a} S) ℕ}
    {L : ChainComplex (ModuleCat.{b} S) ℕ} (f : LinearChainMap K L) (i : ℕ) (z : K.X i) :
    f.extendNonnegative.app (i : ℤ)
        ((K.extendXIso nonnegativeChainEmbedding (i := i) rfl).inv.hom z) =
      (L.extendXIso nonnegativeChainEmbedding (i := i) rfl).inv.hom (f.app i z) := by
  change extendApp f (i : ℤ) _ = _
  rw [extendApp_cast]
  let e := K.extendXIso nonnegativeChainEmbedding (i := i) rfl
  let e' := L.extendXIso nonnegativeChainEmbedding (i := i) rfl
  change e'.inv (f.app i (e.hom (e.inv z))) = e'.inv (f.app i z)
  rw [ModuleCat.hom_inv_apply]

end LinearChainMap

section Total
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.TotalComplexAssembly
open P103.Ch10.TotalComplexAssembly (chain_totalInclusion_d totalTermEquiv_inclusion)
universe v' w' v'' w''
variable {R : Type u} [Ring R]

/-- Linear maps out of a total term are determined on its original summands. -/
private theorem totalLinear_ext
    {S : Type u} [Ring S] (K : ChainBicomplex.{u,v} S) (n : ℤ)
    {W : Type w} [AddCommGroup W] [Module S W] {f g : (total K).X n →ₗ[S] W}
    (h : ∀ p q (hpq : p + q = n) (z : (K.X p).X q),
      f ((totalInclusion K p q n hpq).hom z) = g ((totalInclusion K p q n hpq).hom z)) :
    f = g := by
  have he : f.comp (totalTermEquiv K n).symm.toLinearMap =
      g.comp (totalTermEquiv K n).symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p, q⟩, hpq⟩
    ext z
    simp only [LinearMap.comp_apply]
    rw [← totalTermEquiv_inclusion K p q n hpq z]
    change f ((totalTermEquiv K n).symm (totalTermEquiv K n _)) =
      g ((totalTermEquiv K n).symm (totalTermEquiv K n _))
    rw [LinearEquiv.symm_apply_apply]
    exact h p q hpq z
  ext z
  have hz := LinearMap.congr_fun he (totalTermEquiv K n z)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hz

private def totalLinear
    {S : Type u} [Ring S] (K : ChainBicomplex.{u,v} S) (L : ChainBicomplex.{u,w} S)
    (f : ∀ p q, (K.X p).X q →ₗ[S] (L.X p).X q) (n : ℤ) :
    (total K).X n →ₗ[S] (total L).X n :=
  (DirectSum.toModule S _ ((total L).X n)
    (fun i => (totalInclusion L i.val.1 i.val.2 n i.property).hom.comp
      (f i.val.1 i.val.2))).comp (totalTermEquiv K n).toLinearMap

private theorem totalLinear_inclusion
    {S : Type u} [Ring S] (K : ChainBicomplex.{u,v} S) (L : ChainBicomplex.{u,w} S)
    (f : ∀ p q, (K.X p).X q →ₗ[S] (L.X p).X q)
    (p q n : ℤ) (h : p + q = n) (z : (K.X p).X q) :
    totalLinear K L f n ((totalInclusion K p q n h).hom z) =
      (totalInclusion L p q n h).hom (f p q z) := by
  simp only [totalLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, totalTermEquiv_inclusion]
  exact DirectSum.toModule_lof S (M := fun i => diagonalFamily K n i) ⟨(p, q), h⟩ z

private theorem total_d_on_inclusion (K : ChainBicomplex.{0,v} ℤ)
    (p q n : ℤ) (h : p + q = n) (z : (K.X p).X q) :
    ((total K).d n (n - 1)).hom ((totalInclusion K p q n h).hom z) =
      (totalInclusion K (p - 1) q (n - 1) (by omega)).hom (((K.d p (p - 1)).f q).hom z) +
      p.negOnePow •
        (totalInclusion K p (q - 1) (n - 1) (by omega)).hom (((K.X p).d q (q - 1)).hom z) := by
  have hd := chain_totalInclusion_d K p q n (n - 1) h
  rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (show (p - 1) + q = n - 1 by omega),
    HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (show p + (q - 1) = n - 1 by omega)] at hd
  exact congrArg (fun k => k.hom z) hd

/-- The map of the signed total obtained from degreewise maps commuting with each differential. -/
private def totalChainMap
    (K : ChainBicomplex.{0,v} ℤ) (L : ChainBicomplex.{0,w} ℤ)
    (f : ∀ p q, (K.X p).X q →ₗ[ℤ] (L.X p).X q)
    (hh : ∀ p q z, ((L.d p (p - 1)).f q).hom (f p q z) =
      f (p - 1) q (((K.d p (p - 1)).f q).hom z))
    (hv : ∀ p q z, ((L.X p).d q (q - 1)).hom (f p q z) =
      f p (q - 1) (((K.X p).d q (q - 1)).hom z)) :
    LinearChainMap (total K) (total L) where
  app := totalLinear K L f
  comm n m := by
    by_cases hnm : (ComplexShape.down ℤ).Rel n m
    · have hm : m = n - 1 := by change m + 1 = n at hnm; omega
      subst m
      apply totalLinear_ext K n
      intro p q h z
      simp only [LinearMap.comp_apply, totalLinear_inclusion, total_d_on_inclusion _ p q n h,
        hh, hv, map_add, Units.smul_def, map_zsmul, totalLinear_inclusion]
    · simp only [(total L).shape _ _ hnm, (total K).shape _ _ hnm, ModuleCat.hom_zero,
        LinearMap.zero_comp, LinearMap.comp_zero]

private def tensorTotalChainMap
    {C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {C' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
    {D : ChainComplex (ModuleCat.{w} R) ℤ} {D' : ChainComplex (ModuleCat.{w'} R) ℤ}
    (f : LinearChainMap C C') (g : LinearChainMap D D') :
    LinearChainMap (tensorTotal C D) (tensorTotal C' D') :=
  totalChainMap (tensorBicomplex C D) (tensorBicomplex C' D')
    (fun p q => tensorMap (f.app p) (g.app q))
    (by
      intro p q
      suffices ((tensorMap (C'.d p (p - 1)).hom LinearMap.id).comp
          (tensorMap (f.app p) (g.app q)) : Tensor R (C.X p) (D.X q) →ₗ[ℤ] _) =
        (tensorMap (f.app (p - 1)) (g.app q)).comp
          (tensorMap (C.d p (p - 1)).hom LinearMap.id) by
        exact LinearMap.congr_fun this
      apply tensor_hom_ext
      intro a b
      simp only [LinearMap.comp_apply, tensorMap_tmul, LinearMap.id_apply, f.comm_apply])
    (by
      intro p q
      suffices ((tensorMap LinearMap.id (D'.d q (q - 1)).hom).comp
          (tensorMap (f.app p) (g.app q)) : Tensor R (C.X p) (D.X q) →ₗ[ℤ] _) =
        (tensorMap (f.app p) (g.app (q - 1))).comp
          (tensorMap LinearMap.id (D.d q (q - 1)).hom) by
        exact LinearMap.congr_fun this
      apply tensor_hom_ext
      intro a b
      simp only [LinearMap.comp_apply, tensorMap_tmul, LinearMap.id_apply, g.comm_apply])

private def ordinaryTotalChainMap
    {C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ} {C' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℕ}
    {D : ChainComplex (ModuleCat.{w} R) ℕ} {D' : ChainComplex (ModuleCat.{w'} R) ℕ}
    (f : LinearChainMap C C') (g : LinearChainMap D D') :
    LinearChainMap (ordinaryTotal C D) (ordinaryTotal C' D') where
  app n := (tensorTotalChainMap f.extendNonnegative g.extendNonnegative).app (n : ℤ)
  comm i j := (tensorTotalChainMap f.extendNonnegative g.extendNonnegative).comm (i : ℤ) (j : ℤ)

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryTotalChainMap_inclusion
    {C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ} {C' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℕ}
    {D : ChainComplex (ModuleCat.{w} R) ℕ} {D' : ChainComplex (ModuleCat.{w'} R) ℕ}
    (f : LinearChainMap C C') (g : LinearChainMap D D') (i j n : ℕ) (h : i + j = n)
    (a : C.X i) (b : D.X j) :
    (ordinaryTotalChainMap f g).app n (ordinaryInclusion C D i j n h (tmul R a b)) =
      ordinaryInclusion C' D' i j n h (tmul R (f.app i a) (g.app j b)) := by
  rw [P103.Ch11.TorBalance.ordinaryInclusion_tmul, P103.Ch11.TorBalance.ordinaryInclusion_tmul]
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  let L := tensorBicomplex (extendNonnegativeChain C') (extendNonnegativeChain D')
  change totalLinear K L (fun p q => tensorMap (f.extendNonnegative.app p)
    (g.extendNonnegative.app q)) n ((totalInclusion K i j n _).hom (tmul R _ _)) =
      (totalInclusion L i j n _).hom (tmul R _ _)
  rw [totalLinear_inclusion]
  apply congrArg ((totalInclusion L i j n _).hom)
  change tmul R (f.extendNonnegative.app (i : ℤ) _) (g.extendNonnegative.app (j : ℤ) _) = _
  rw [f.extendNonnegative_app_inv, g.extendNonnegative_app_inv]


set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryTotalLinear_ext
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ) (D : ChainComplex (ModuleCat.{w} R) ℕ)
    (n : ℕ) {W : Type x} [AddCommGroup W] [Module ℤ W]
    {f g : (ordinaryTotal C D).X n →ₗ[ℤ] W}
    (h : ∀ p q (hpq : p + q = n) (a : C.X p) (b : D.X q),
      f (ordinaryInclusion C D p q n hpq (tmul R a b)) =
        g (ordinaryInclusion C D p q n hpq (tmul R a b))) : f = g := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  refine totalLinear_ext K (n : ℤ) ?_
  intro p q hpq
  suffices f.comp (totalInclusion K p q n hpq).hom =
      g.comp (totalInclusion K p q n hpq).hom by
    exact LinearMap.congr_fun this
  change (f.comp (totalInclusion K p q n hpq).hom :
    Tensor R ((extendNonnegativeChain C).X p) ((extendNonnegativeChain D).X q) →ₗ[ℤ] W) = _
  apply LinearMap.toAddMonoidHom_injective
  apply P103.BalancedTensor.hom_ext
  intro a b
  by_cases hp : 0 ≤ p
  · by_cases hq : 0 ≤ q
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      let e := C.extendXIso nonnegativeChainEmbedding (i := p) rfl
      let e' := D.extendXIso nonnegativeChainEmbedding (i := q) rfl
      replace hpq : p + q = n := by exact_mod_cast hpq
      have ht := h p q hpq (e.hom a) (e'.hom b)
      change f ((totalInclusion K p q n _).hom (tmul R (e.inv (e.hom a)) (e'.inv (e'.hom b)))) =
        g ((totalInclusion K p q n _).hom (tmul R (e.inv (e.hom a)) (e'.inv (e'.hom b)))) at ht
      change f ((totalInclusion K p q n _).hom (tmul R a b)) =
        g ((totalInclusion K p q n _).hom (tmul R a b))
      simpa only [ModuleCat.inv_hom_apply] using ht
    · have := P103.Ch10.Complexes.extendNonnegativeChain_supported D q (by simpa using hq)
      simp only [Subsingleton.elim b 0, tmul_zero, map_zero]
  · have := P103.Ch10.Complexes.extendNonnegativeChain_supported C p (by simpa using hp)
    simp only [Subsingleton.elim a 0, zero_tmul, map_zero]

private theorem ordinaryTotalChainMap_id
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ) (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    ordinaryTotalChainMap (LinearChainMap.id C) (LinearChainMap.id D) =
      LinearChainMap.id (ordinaryTotal C D) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply ordinaryTotalLinear_ext C D n
  intro p q h a b
  simp only [ordinaryTotalChainMap_inclusion, LinearChainMap.id_app, LinearMap.id_apply]

private theorem ordinaryTotalChainMap_comp
    {C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ} {C' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℕ}
    {C'' : ChainComplex (ModuleCat.{v''} Rᵐᵒᵖ) ℕ}
    {D : ChainComplex (ModuleCat.{w} R) ℕ} {D' : ChainComplex (ModuleCat.{w'} R) ℕ}
    {D'' : ChainComplex (ModuleCat.{w''} R) ℕ}
    (f : LinearChainMap C C') (f' : LinearChainMap C' C'')
    (g : LinearChainMap D D') (g' : LinearChainMap D' D'') :
    (ordinaryTotalChainMap f' g').comp (ordinaryTotalChainMap f g) =
      ordinaryTotalChainMap (f'.comp f) (g'.comp g) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply ordinaryTotalLinear_ext C D n
  intro p q h a b
  simp only [LinearChainMap.comp_app, LinearMap.comp_apply, ordinaryTotalChainMap_inclusion]

end Total

section TensorMaps
open P103.Specs.Ch10.Complexes
universe v' w' v'' w'' a a' b b'
variable {R : Type u} [Ring R]

/-- Tensor the right-complex map and the left-coefficient map on the original terms. -/
def tensorLinearChainMap
    {C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ} {C' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℕ}
    {M : Type w} {M' : Type w'} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M']
    (l : LinearChainMap C C') (g : M →ₗ[R] M') :
    LinearChainMap (tensorComplex C M) (tensorComplex C' M') where
  app n := tensorMap (l.app n) g
  comm i j := by
    apply tensor_hom_ext
    intro a b
    change tmul R ((C'.d i j).hom (l.app i a)) (g b) =
      tmul R (l.app j ((C.d i j).hom a)) (g b)
    rw [l.comm_apply]

/-- Tensor the right-coefficient map and the left-complex map on the original terms. -/
def leftTensorLinearChainMap
    {D : ChainComplex (ModuleCat.{w} R) ℕ} {D' : ChainComplex (ModuleCat.{w'} R) ℕ}
    {A : Type v} {A' : Type v'} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    (f : A →ₗ[Rᵐᵒᵖ] A') (m : LinearChainMap D D') :
    LinearChainMap (leftOrdinaryTensorComplex A D) (leftOrdinaryTensorComplex A' D') where
  app n := tensorMap f (m.app n)
  comm i j := by
    apply tensor_hom_ext
    intro a b
    change tmul R (f a) ((D'.d i j).hom (m.app i b)) =
      tmul R (f a) (m.app j ((D.d i j).hom b))
    rw [m.comm_apply]

@[simp] theorem tensorLinearChainMap_id
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (M : Type w) [AddCommGroup M] [Module R M] :
    tensorLinearChainMap (LinearChainMap.id C) (LinearMap.id : M →ₗ[R] M) =
      LinearChainMap.id (tensorComplex C M) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply tensor_hom_ext
  intros
  rfl

theorem tensorLinearChainMap_comp
    {C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ} {C' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℕ}
    {C'' : ChainComplex (ModuleCat.{v''} Rᵐᵒᵖ) ℕ}
    {M : Type w} {M' : Type w'} {M'' : Type w''} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    (l : LinearChainMap C C') (l' : LinearChainMap C' C'')
    (g : M →ₗ[R] M') (g' : M' →ₗ[R] M'') :
    (tensorLinearChainMap l' g').comp (tensorLinearChainMap l g) =
      tensorLinearChainMap (l'.comp l) (g'.comp g) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply tensor_hom_ext
  intros
  rfl

@[simp] theorem leftTensorLinearChainMap_id
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    leftTensorLinearChainMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) (LinearChainMap.id D) =
      LinearChainMap.id (leftOrdinaryTensorComplex A D) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply tensor_hom_ext
  intros
  rfl

theorem leftTensorLinearChainMap_comp
    {D : ChainComplex (ModuleCat.{w} R) ℕ} {D' : ChainComplex (ModuleCat.{w'} R) ℕ}
    {D'' : ChainComplex (ModuleCat.{w''} R) ℕ}
    {A : Type v} {A' : Type v'} {A'' : Type v''} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A'] [AddCommGroup A''] [Module Rᵐᵒᵖ A'']
    (f : A →ₗ[Rᵐᵒᵖ] A') (f' : A' →ₗ[Rᵐᵒᵖ] A'')
    (m : LinearChainMap D D') (m' : LinearChainMap D' D'') :
    (leftTensorLinearChainMap f' m').comp (leftTensorLinearChainMap f m) =
      leftTensorLinearChainMap (f'.comp f) (m'.comp m) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply tensor_hom_ext
  intros
  rfl

variable {A : ModuleCat.{v} Rᵐᵒᵖ} {A' : ModuleCat.{v'} Rᵐᵒᵖ}
  {M : ModuleCat.{w} R} {M' : ModuleCat.{w'} R}
  {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {P' : AugmentedResolution.{u,v',a'} Rᵐᵒᵖ A'}
  {Q : AugmentedResolution.{u,w,b} R M} {Q' : AugmentedResolution.{u,w',b'} R M'}

set_option backward.isDefEq.respectTransparency false in
/-- The two squares use the same map on the signed total and the original
augmentations. Each identity is determined by the axis summands. -/
def balanceMaps (f : A →ₗ[Rᵐᵒᵖ] A') (g : M →ₗ[R] M')
    (l : LinearChainMap P.complex P'.complex) (m : LinearChainMap Q.complex Q'.complex)
    (hl : P.Lifts P' f l) (hm : Q.Lifts Q' g m)
    (α : OriginalAugmentations P Q) (β : OriginalAugmentations P' Q') :
    BalanceMaps f g l m α β where
  total := ordinaryTotalChainMap l m
  left := tensorLinearChainMap l g
  right := leftTensorLinearChainMap f m
  total_formula i j n h := by
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    exact ordinaryTotalChainMap_inclusion l m i j n h
  left_formula _ := rfl
  right_formula _ := rfl
  left_square n := by
    apply ordinaryTotalLinear_ext P.complex Q.complex n
    intro i j h a b
    simp only [LinearMap.comp_apply, ordinaryTotalChainMap_inclusion]
    by_cases hj : j = 0
    · subst j
      obtain rfl : i = n := by omega
      rw [β.left_zero, α.left_zero]
      change tmul R (l.app i a) (Q'.ε (m.app 0 b)) = tmul R (l.app i a) (g (Q.ε b))
      rw [hm b]
    · have hα := LinearMap.congr_fun (α.left_positive i j n h hj) (tmul R a b)
      have hβ := LinearMap.congr_fun (β.left_positive i j n h hj) (tmul R (l.app i a) (m.app j b))
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hα hβ
      rw [hα, hβ, map_zero]
  right_square n := by
    apply ordinaryTotalLinear_ext P.complex Q.complex n
    intro i j h a b
    simp only [LinearMap.comp_apply, ordinaryTotalChainMap_inclusion]
    by_cases hi : i = 0
    · subst i
      obtain rfl : j = n := by omega
      rw [β.right_zero, α.right_zero]
      change tmul R (P'.ε (l.app 0 a)) (m.app j b) = tmul R (f (P.ε a)) (m.app j b)
      rw [hl a]
    · have hα := LinearMap.congr_fun (α.right_positive i j n h hi) (tmul R a b)
      have hβ := LinearMap.congr_fun (β.right_positive i j n h hi) (tmul R (l.app i a) (m.app j b))
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hα hβ
      rw [hα, hβ, map_zero]

@[simp] theorem OriginalAugmentations.balanceEquiv_apply_left
    (α : OriginalAugmentations P Q) (hL : α.left.IsQuasiIso) (hR : α.right.IsQuasiIso)
    (n : ℕ) (z : Homology (ordinaryTotal P.complex Q.complex) n) :
    α.balanceEquiv hL hR n (α.left.homologyMap n z) = α.right.homologyMap n z :=
  congrArg (α.right.homologyEquiv hR n) ((α.left.homologyEquiv hL n).symm_apply_apply z)

theorem BalanceMaps.left_eq {f : A →ₗ[Rᵐᵒᵖ] A'} {g : M →ₗ[R] M'}
    {l : LinearChainMap P.complex P'.complex} {m : LinearChainMap Q.complex Q'.complex}
    {α : OriginalAugmentations P Q} {β : OriginalAugmentations P' Q'}
    (F : BalanceMaps f g l m α β) : F.left = tensorLinearChainMap l g :=
  LinearChainMap.eq_of_app_eq (funext F.left_formula)

theorem BalanceMaps.right_eq {f : A →ₗ[Rᵐᵒᵖ] A'} {g : M →ₗ[R] M'}
    {l : LinearChainMap P.complex P'.complex} {m : LinearChainMap Q.complex Q'.complex}
    {α : OriginalAugmentations P Q} {β : OriginalAugmentations P' Q'}
    (F : BalanceMaps f g l m α β) : F.right = leftTensorLinearChainMap f m :=
  LinearChainMap.eq_of_app_eq (funext F.right_formula)

theorem heterogeneous_balance_naturality :
    Specs.HeterogeneousBalanceNaturality.{u,v,w,v',w'} := by
  intro R _ A A' M M' P P' Q Q' f g l m hl hm α β hαL hαR hβL hβR
  let F := balanceMaps f g l m hl hm α β
  refine ⟨F, fun n => ?_⟩
  have hL := F.total.homologyMap_square F.left α.left β.left F.left_square n
  have hR := F.total.homologyMap_square F.right α.right β.right F.right_square n
  refine ⟨hL, hR, ?_⟩
  apply LinearMap.ext
  intro z
  obtain ⟨t, rfl⟩ := (hαL n).surjective z
  change β.balanceEquiv hβL hβR n (F.left.homologyMap n (α.left.homologyMap n t)) =
    F.right.homologyMap n (α.balanceEquiv hαL hαR n (α.left.homologyMap n t))
  have hLt := DFunLike.congr_fun hL t
  have hRt := DFunLike.congr_fun hR t
  simp only [LinearMap.comp_apply] at hLt hRt
  rw [← hLt, β.balanceEquiv_apply_left, α.balanceEquiv_apply_left, hRt]

end TensorMaps


namespace LinearChainMap

open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
universe a b d
variable {S : Type u} [Ring S]

private def liftComplex (K : ChainComplex (ModuleCat.{a} S) ℕ) :
    ChainComplex (ModuleCat.{max a d} S) ℕ :=
  ((ModuleCat.uliftFunctor.{d} S).mapHomologicalComplex (ComplexShape.down ℕ)).obj K

private def liftComplexUp (K : ChainComplex (ModuleCat.{a} S) ℕ) :
    LinearChainMap K (liftComplex.{u,a,d} K) where
  app _ := ULift.moduleEquiv.symm.toLinearMap
  comm _ _ := rfl

private def liftComplexDown (K : ChainComplex (ModuleCat.{a} S) ℕ) :
    LinearChainMap (liftComplex.{u,a,d} K) K where
  app _ := ULift.moduleEquiv.toLinearMap
  comm _ _ := rfl

private theorem liftComplexDown_comp_up (K : ChainComplex (ModuleCat.{a} S) ℕ) :
    (liftComplexDown.{u,a,d} K).comp (liftComplexUp.{u,a,d} K) = LinearChainMap.id K :=
  eq_of_app_eq (funext fun _ => rfl)

private theorem liftComplexUp_comp_down (K : ChainComplex (ModuleCat.{a} S) ℕ) :
    (liftComplexUp.{u,a,d} K).comp (liftComplexDown.{u,a,d} K) =
      LinearChainMap.id (liftComplex.{u,a,d} K) :=
  eq_of_app_eq (funext fun _ => rfl)

private def liftLinear
    {X : Type a} {Y : Type b} [AddCommGroup X] [Module S X]
    [AddCommGroup Y] [Module S Y] (f : X →ₗ[S] Y) :
    ULift.{d} X →ₗ[S] ULift.{d} Y :=
  ULift.moduleEquiv.symm.toLinearMap.comp (f.comp ULift.moduleEquiv.toLinearMap)

private theorem liftLinear_exact
    {X : Type a} {Y : Type b} {Z : Type*} [AddCommGroup X] [Module S X]
    [AddCommGroup Y] [Module S Y] [AddCommGroup Z] [Module S Z]
    (f : X →ₗ[S] Y) (g : Y →ₗ[S] Z)
    (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range (liftLinear.{u,a,b,d} f) = LinearMap.ker (liftLinear.{u,b,_,d} g) := by
  have he : Function.Exact f g := LinearMap.exact_iff.mpr h.symm
  symm
  apply LinearMap.exact_iff.mp
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (he y.down).mp (congrArg ULift.down hy)
    exact ⟨ULift.up x, ULift.ext hx⟩
  · rintro ⟨x, hx⟩
    exact ULift.ext ((he y.down).mpr ⟨x.down, congrArg ULift.down hx⟩)

private def liftResolution
    {A : Type v} [AddCommGroup A] [Module S A] (P : AugmentedResolution.{u,v,a} S A) :
    LeftResolution S (ULift.{max u v a d} A) where
  complex := liftComplex.{u,a,max u v a d} P.complex
  ε := liftLinear P.ε
  surjective y := by
    obtain ⟨x, hx⟩ := P.surjective y.down
    exact ⟨ULift.up x, ULift.ext hx⟩
  exact_zero := liftLinear_exact _ _ P.exact_zero
  exact_succ n := liftLinear_exact _ _ (P.exact_succ n)

private theorem liftResolution_projective
    {A : Type v} [AddCommGroup A] [Module S A] (P : AugmentedResolution.{u,v,a} S A) :
    (liftResolution.{u,v,a,d} P).IsProjective := by
  intro n
  change Module.Projective S (ULift.{max u v a d} (P.complex.X n))
  let := P.projective n
  infer_instance

/-- Put both chain complexes in a common module category, keeping the
degreewise carrier equivalences explicit. -/
private def liftMap {K : ChainComplex (ModuleCat.{a} S) ℕ}
    {L : ChainComplex (ModuleCat.{b} S) ℕ} (f : LinearChainMap K L) :
    liftComplex.{u,a,max a b d} K ⟶ liftComplex.{u,b,max a b d} L where
  f n := ModuleCat.ofHom (liftLinear (f.app n))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext z
    exact ULift.ext (f.comm_apply i j z.down)

private def lowerMap {K : ChainComplex (ModuleCat.{a} S) ℕ}
    {L : ChainComplex (ModuleCat.{b} S) ℕ}
    (f : liftComplex.{u,a,max a b d} K ⟶ liftComplex.{u,b,max a b d} L) :
    LinearChainMap K L where
  app n := ULift.moduleEquiv.toLinearMap.comp ((f.f n).hom.comp ULift.moduleEquiv.symm.toLinearMap)
  comm i j := by
    ext z
    exact congrArg (fun k => ((k.hom (ULift.up z)) : ULift.{max a b d} (L.X j)).down)
      (f.comm i j)

/-- Coefficient maps lift to chain maps on the given augmented resolutions. -/
theorem exists_augmentedLift
    {A : Type v} {B : Type w} [AddCommGroup A] [Module S A]
    [AddCommGroup B] [Module S B] (P : AugmentedResolution.{u,v,a} S A)
    (Q : AugmentedResolution.{u,w,b} S B) (f : A →ₗ[S] B) :
    ∃ l : LinearChainMap P.complex Q.complex, P.Lifts Q f l := by
  let P₁ := liftResolution.{u,v,a,max w b} P
  let Q₁ := liftResolution.{u,w,b,max v a} Q
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists S _ _ P₁ Q₁
    (liftResolution_projective P) (liftLinear f)
  refine ⟨lowerMap.{u,a,b,max u v w} l, fun z => ?_⟩
  exact congrArg ULift.down (LinearMap.congr_fun hl (ULift.up z))

variable {ι : Type x} {c : ComplexShape ι}
  {K : HomologicalComplex (ModuleCat.{a} S) c} {L : HomologicalComplex (ModuleCat.{b} S) c}

/-- A degreewise homotopy identity for maps of complexes in different universes. -/
def Homotopic (f g : LinearChainMap K L) : Prop :=
  ∃ h : ∀ i j, K.X i →ₗ[S] L.X j, ∀ n,
    f.app n = (h (c.next n) n).comp (K.d n (c.next n)).hom +
      (L.d (c.prev n) n).hom.comp (h n (c.prev n)) + g.app n

/-- Homotopic maps agree on the cycle quotient. -/
theorem homologyMap_eq_of_homotopic {f g : LinearChainMap K L} (h : f.Homotopic g) :
    f.homologyMap = g.homologyMap := by
  obtain ⟨s, hs⟩ := h
  funext n
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (cycleBoundaries K n).mkQ_surjective z
  change homologyClass L n (f.cyclesMap n z) = homologyClass L n (g.cyclesMap n z)
  apply (P103.Ch10.Complexes.homologyClass_eq_iff L n _ _).mpr
  refine ⟨s n (c.prev n) z.val, ?_⟩
  change (L.d (c.prev n) n).hom (s n (c.prev n) z.val) = f.app n z.val - g.app n z.val
  have hz : (K.d n (c.next n)).hom z.val = 0 := z.property
  have hval := LinearMap.congr_fun (hs n) z.val
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero, zero_add] at hval
  rw [hval, add_sub_cancel_right]

/-- Comparison homotopies are transported from the common module category
through the degreewise carrier equivalences. -/
theorem augmentedLifts_homotopic
    {A : Type v} {B : Type w} [AddCommGroup A] [Module S A]
    [AddCommGroup B] [Module S B] (P : AugmentedResolution.{u,v,a} S A)
    (Q : AugmentedResolution.{u,w,b} S B) (f : A →ₗ[S] B)
    (l l' : LinearChainMap P.complex Q.complex)
    (hl : P.Lifts Q f l) (hl' : P.Lifts Q f l') :
    l.Homotopic l' := by
  let P₁ := liftResolution.{u,v,a,max w b} P
  let Q₁ := liftResolution.{u,w,b,max v a} Q
  let l₁ := liftMap.{u,a,b,max u v w} l
  let l₁' := liftMap.{u,a,b,max u v w} l'
  have hl₁ : ChainLift P₁ Q₁ (liftLinear f) l₁ := by
    apply LinearMap.ext
    intro z
    exact ULift.ext (hl z.down)
  have hl₁' : ChainLift P₁ Q₁ (liftLinear f) l₁' := by
    apply LinearMap.ext
    intro z
    exact ULift.ext (hl' z.down)
  obtain ⟨h⟩ := P103.Ch10.Comparison.chain_unique S _ _ P₁ Q₁
    (liftResolution_projective P) (liftLinear f) l₁ l₁' hl₁ hl₁'
  refine ⟨fun i j => ULift.moduleEquiv.toLinearMap.comp
    ((h.hom i j).hom.comp ULift.moduleEquiv.symm.toLinearMap), ?_⟩
  intro n
  apply LinearMap.ext
  intro z
  exact congrArg (fun k => ((k.hom (ULift.up z)) : ULift.{max u v w a b} (Q.complex.X n)).down)
    (h.comm n)

/-- Opposite lifts of the identity compose to the identity up to homotopy. -/
theorem augmentedLifts_comp_homotopic_id
    {A : Type v} [AddCommGroup A] [Module S A]
    {P : AugmentedResolution.{u,v,a} S A} {Q : AugmentedResolution.{u,v,b} S A}
    {l : LinearChainMap P.complex Q.complex} {k : LinearChainMap Q.complex P.complex}
    (hl : P.Lifts Q LinearMap.id l) (hk : Q.Lifts P LinearMap.id k) :
    (k.comp l).Homotopic (LinearChainMap.id P.complex) := by
  refine augmentedLifts_homotopic P P LinearMap.id _ _ (fun z => ?_) (fun _ => rfl)
  exact (hk (l.app 0 z)).trans (hl z)

end LinearChainMap

section OriginalBalance
open P103.Specs.Ch10.Complexes
open LinearChainMap (liftResolution liftResolution_projective liftComplexUp liftComplexDown
  liftComplexDown_comp_up liftComplexUp_comp_down)
universe a b

set_option backward.isDefEq.respectTransparency false in
theorem original_balance : Specs.OriginalBalance.{u,v,w,a,b} := by
  intro R _ A M P Q
  let P₁ := liftResolution.{u,v,a,0} P
  let Q₁ := liftResolution.{u,w,b,0} Q
  obtain ⟨α, hαL, hαR⟩ := balance R (ULift.{max u v a} A) (ULift.{max u w b} M) P₁ Q₁
    (liftResolution_projective P) (liftResolution_projective Q)
  let upP : LinearChainMap P.complex P₁.complex := liftComplexUp P.complex
  let upQ : LinearChainMap Q.complex Q₁.complex := liftComplexUp Q.complex
  let downP : LinearChainMap P₁.complex P.complex := liftComplexDown P.complex
  let downQ : LinearChainMap Q₁.complex Q.complex := liftComplexDown Q.complex
  let eA : ULift.{max u v a} A ≃ₗ[Rᵐᵒᵖ] A := ULift.moduleEquiv
  let eM : ULift.{max u w b} M ≃ₗ[R] M := ULift.moduleEquiv
  let totalUp := ordinaryTotalChainMap upP upQ
  let leftDown := tensorLinearChainMap downP eM.toLinearMap
  let rightDown := leftTensorLinearChainMap eA.toLinearMap downQ
  have htotal : totalUp.IsQuasiIso := by
    apply totalUp.isQuasiIso_of_inverse (ordinaryTotalChainMap downP downQ)
    · simp only [totalUp, ordinaryTotalChainMap_comp, downP, upP, downQ, upQ,
        liftComplexDown_comp_up, ordinaryTotalChainMap_id]
    · simp only [totalUp, ordinaryTotalChainMap_comp, upP, downP, upQ, downQ,
        liftComplexUp_comp_down]
      exact ordinaryTotalChainMap_id _ _
  have hleft : leftDown.IsQuasiIso := by
    apply leftDown.isQuasiIso_of_inverse (tensorLinearChainMap upP eM.symm.toLinearMap)
    · simp only [leftDown, tensorLinearChainMap_comp, downP, upP, liftComplexUp_comp_down,
        LinearEquiv.symm_comp]
      exact tensorLinearChainMap_id _ _
    · simp only [leftDown, tensorLinearChainMap_comp, downP, upP, liftComplexDown_comp_up,
        LinearEquiv.comp_symm, tensorLinearChainMap_id]
  have hright : rightDown.IsQuasiIso := by
    apply rightDown.isQuasiIso_of_inverse (leftTensorLinearChainMap eA.symm.toLinearMap upQ)
    · simp only [rightDown, leftTensorLinearChainMap_comp, downQ, upQ, liftComplexUp_comp_down,
        LinearEquiv.symm_comp]
      exact leftTensorLinearChainMap_id _ _
    · simp only [rightDown, leftTensorLinearChainMap_comp, downQ, upQ, liftComplexDown_comp_up,
        LinearEquiv.comp_symm, leftTensorLinearChainMap_id]
  let left := leftDown.comp ((LinearChainMap.ofHom α.left).comp totalUp)
  let right := rightDown.comp ((LinearChainMap.ofHom α.right).comp totalUp)
  refine ⟨⟨left, right, ?_, ?_, ?_, ?_⟩,
    hleft.comp ((LinearChainMap.isQuasiIso_ofHom hαL).comp htotal),
    hright.comp ((LinearChainMap.isQuasiIso_ofHom hαR).comp htotal)⟩
  · intro p x y
    change leftDown.app p ((α.left.f p).hom
      ((ordinaryTotalChainMap upP upQ).app p
        (ordinaryInclusion P.complex Q.complex p 0 p _ (tmul R x y)))) = _
    rw [ordinaryTotalChainMap_inclusion, α.left_zero]
    rfl
  · intro p q n h hq
    apply tensor_hom_ext
    intro x y
    change leftDown.app n ((α.left.f n).hom
      ((ordinaryTotalChainMap upP upQ).app n
        (ordinaryInclusion P.complex Q.complex p q n h (tmul R x y)))) = 0
    rw [ordinaryTotalChainMap_inclusion]
    have hz := DFunLike.congr_fun (α.left_positive p q n h hq)
      (tmul R (upP.app p x) (upQ.app q y))
    change (α.left.f n).hom (ordinaryInclusion P₁.complex Q₁.complex p q n h
      (tmul R (upP.app p x) (upQ.app q y))) = 0 at hz
    rw [hz, map_zero]
  · intro q x y
    change rightDown.app q ((α.right.f q).hom
      ((ordinaryTotalChainMap upP upQ).app q
        (ordinaryInclusion P.complex Q.complex 0 q q _ (tmul R x y)))) = _
    rw [ordinaryTotalChainMap_inclusion, α.right_zero]
    rfl
  · intro p q n h hp
    apply tensor_hom_ext
    intro x y
    change rightDown.app n ((α.right.f n).hom
      ((ordinaryTotalChainMap upP upQ).app n
        (ordinaryInclusion P.complex Q.complex p q n h (tmul R x y)))) = 0
    rw [ordinaryTotalChainMap_inclusion]
    have hz := DFunLike.congr_fun (α.right_positive p q n h hp)
      (tmul R (upP.app p x) (upQ.app q y))
    change (α.right.f n).hom (ordinaryInclusion P₁.complex Q₁.complex p q n h
      (tmul R (upP.app p x) (upQ.app q y))) = 0 at hz
    rw [hz, map_zero]

end OriginalBalance


section Homotopies
open P103.Specs.Ch10.Complexes
universe v' w' a a' b b'
variable {R : Type u} [Ring R]

private theorem tensorLinearChainMap_homotopic
    {C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ} {C' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℕ}
    {M : Type w} {M' : Type w'} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M']
    {l l' : LinearChainMap C C'} (h : l.Homotopic l') (g : M →ₗ[R] M') :
    (tensorLinearChainMap l g).Homotopic (tensorLinearChainMap l' g) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨fun i j => tensorMap (s i j) g, ?_⟩
  intro n
  apply tensor_hom_ext
  intro a b
  let c := ComplexShape.down ℕ
  change tmul R (l.app n a) (g b) =
    tmul R (s (c.next n) n ((C.d n (c.next n)).hom a)) (g b) +
    tmul R ((C'.d (c.prev n) n).hom (s n (c.prev n) a)) (g b) +
    tmul R (l'.app n a) (g b)
  rw [LinearMap.congr_fun (hs n) a]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, add_tmul, c]

private theorem leftTensorLinearChainMap_homotopic
    {D : ChainComplex (ModuleCat.{w} R) ℕ} {D' : ChainComplex (ModuleCat.{w'} R) ℕ}
    {A : Type v} {A' : Type v'} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    (f : A →ₗ[Rᵐᵒᵖ] A') {m m' : LinearChainMap D D'} (h : m.Homotopic m') :
    (leftTensorLinearChainMap f m).Homotopic (leftTensorLinearChainMap f m') := by
  obtain ⟨s, hs⟩ := h
  refine ⟨fun i j => tensorMap f (s i j), ?_⟩
  intro n
  apply tensor_hom_ext
  intro a b
  let c := ComplexShape.down ℕ
  change tmul R (f a) (m.app n b) =
    tmul R (f a) (s (c.next n) n ((D.d n (c.next n)).hom b)) +
    tmul R (f a) ((D'.d (c.prev n) n).hom (s n (c.prev n) b)) +
    tmul R (f a) (m'.app n b)
  rw [LinearMap.congr_fun (hs n) b]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, tmul_add, c]

open LinearChainMap (augmentedLifts_comp_homotopic_id homologyMap_eq_of_homotopic)

/-- Opposite lifts of the identity induce inverse comparisons in the right
resolution formula. -/
theorem tensor_comparison_homology_inverse
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {P' : AugmentedResolution.{u,v,a'} Rᵐᵒᵖ A}
    {l : LinearChainMap P.complex P'.complex} {k : LinearChainMap P'.complex P.complex}
    (hl : P.Lifts P' LinearMap.id l) (hk : P'.Lifts P LinearMap.id k)
    (M : Type w) [AddCommGroup M] [Module R M] (n : ℕ) :
    ((tensorLinearChainMap k (LinearMap.id : M →ₗ[R] M)).homologyMap n).comp
      ((tensorLinearChainMap l (LinearMap.id : M →ₗ[R] M)).homologyMap n) = LinearMap.id := by
  have h := tensorLinearChainMap_homotopic (augmentedLifts_comp_homotopic_id hl hk)
    (LinearMap.id : M →ₗ[R] M)
  rw [← LinearChainMap.homologyMap_comp, tensorLinearChainMap_comp, LinearMap.id_comp,
    homologyMap_eq_of_homotopic h, tensorLinearChainMap_id, LinearChainMap.homologyMap_id]

/-- The same inverse identities hold in the left resolution formula. -/
theorem left_tensor_comparison_homology_inverse
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {M : Type w} [AddCommGroup M] [Module R M]
    {Q : AugmentedResolution.{u,w,b} R M} {Q' : AugmentedResolution.{u,w,b'} R M}
    {m : LinearChainMap Q.complex Q'.complex} {k : LinearChainMap Q'.complex Q.complex}
    (hm : Q.Lifts Q' LinearMap.id m) (hk : Q'.Lifts Q LinearMap.id k) (n : ℕ) :
    ((leftTensorLinearChainMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) k).homologyMap n).comp
      ((leftTensorLinearChainMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) m).homologyMap n) = LinearMap.id := by
  have h := leftTensorLinearChainMap_homotopic (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A)
    (augmentedLifts_comp_homotopic_id hm hk)
  rw [← LinearChainMap.homologyMap_comp, leftTensorLinearChainMap_comp, LinearMap.id_comp,
    homologyMap_eq_of_homotopic h, leftTensorLinearChainMap_id, LinearChainMap.homologyMap_id]

theorem tensor_comparison_quasiIso
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {P' : AugmentedResolution.{u,v,a'} Rᵐᵒᵖ A}
    {l : LinearChainMap P.complex P'.complex} (hl : P.Lifts P' LinearMap.id l)
    (M : Type w) [AddCommGroup M] [Module R M] :
    (tensorLinearChainMap l (LinearMap.id : M →ₗ[R] M)).IsQuasiIso := by
  obtain ⟨k, hk⟩ := LinearChainMap.exists_augmentedLift P' P LinearMap.id
  apply LinearChainMap.isQuasiIso_of_homology_inverse _
    (tensorLinearChainMap k (LinearMap.id : M →ₗ[R] M))
  · intro n
    rw [LinearChainMap.homologyMap_comp]
    exact tensor_comparison_homology_inverse hl hk M n
  · intro n
    rw [LinearChainMap.homologyMap_comp]
    exact tensor_comparison_homology_inverse hk hl M n

theorem original_tor_identification : Specs.OriginalTorIdentification.{u,v,w,a,b} := by
  intro R _ T A M P Q P₀ P₀' l hl α hL hR
  let t := tensorLinearChainMap l (LinearMap.id : M →ₗ[R] M)
  have ht : t.IsQuasiIso := tensor_comparison_quasiIso hl M
  refine ⟨t, fun _ => rfl, ht, fun n => ?_⟩
  let e := α.balanceEquiv hL hR n
  refine ⟨e.symm.trans (t.homologyEquiv ht n), ?_⟩
  exact DFunLike.ext _ _ fun z => congrArg (t.homologyEquiv ht n) (e.symm_apply_apply z)

/-- The comparison with a second choice of right resolution commutes with
the maps of the original module pairs on tensor homology. -/
theorem tensor_resolution_comparison_natural
    {A : Type v} {A' : Type v'} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    {M : Type w} {M' : Type w'} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M']
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {P' : AugmentedResolution.{u,v',a'} Rᵐᵒᵖ A'}
    {P₀ : AugmentedResolution.{u,v,b} Rᵐᵒᵖ A} {P₀' : AugmentedResolution.{u,v',b'} Rᵐᵒᵖ A'}
    {f : A →ₗ[Rᵐᵒᵖ] A'} (g : M →ₗ[R] M')
    {l : LinearChainMap P.complex P'.complex} {l₀ : LinearChainMap P₀.complex P₀'.complex}
    {k : LinearChainMap P.complex P₀.complex} {k' : LinearChainMap P'.complex P₀'.complex}
    (hl : P.Lifts P' f l) (hl₀ : P₀.Lifts P₀' f l₀)
    (hk : P.Lifts P₀ LinearMap.id k) (hk' : P'.Lifts P₀' LinearMap.id k') (n : ℕ) :
    ((tensorLinearChainMap l₀ g).homologyMap n).comp
        ((tensorLinearChainMap k (LinearMap.id : M →ₗ[R] M)).homologyMap n) =
      ((tensorLinearChainMap k' (LinearMap.id : M' →ₗ[R] M')).homologyMap n).comp
        ((tensorLinearChainMap l g).homologyMap n) := by
  have h₁ : P.Lifts P₀' f (l₀.comp k) := fun z => (hl₀ (k.app 0 z)).trans (congrArg f (hk z))
  have h₂ : P.Lifts P₀' f (k'.comp l) := fun z => (hk' (l.app 0 z)).trans (hl z)
  have h := LinearChainMap.augmentedLifts_homotopic P P₀' f _ _ h₁ h₂
  rw [← LinearChainMap.homologyMap_comp, ← LinearChainMap.homologyMap_comp,
    tensorLinearChainMap_comp, tensorLinearChainMap_comp, LinearMap.comp_id, LinearMap.id_comp]
  exact congrFun (homologyMap_eq_of_homotopic (tensorLinearChainMap_homotopic h g)) n

private theorem tensor_homologyMap_ofHom
    {C C' : ChainComplex (ModuleCat.{a} Rᵐᵒᵖ) ℕ} {M M' : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (l : C ⟶ C') (g : M →ₗ[R] M') (n : ℕ) :
    (tensorLinearChainMap (LinearChainMap.ofHom l) g).homologyMap n =
      homologyMap (tensorFirstMap l M ≫ tensorSecondMap C' g) n := by
  have h : tensorLinearChainMap (LinearChainMap.ofHom l) g =
      LinearChainMap.ofHom (tensorFirstMap l M ≫ tensorSecondMap C' g) := by
    apply LinearChainMap.eq_of_app_eq
    funext n
    apply tensor_hom_ext
    intros
    rfl
  rw [h]
  rfl

/-- Naturality of the comparison with the actual maps of the chosen P103
Tor theory. The heterogeneous square uses the same maps on its quotients. -/
theorem original_tor_naturality (T : CanonicalTheory.{u,v,w} R)
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} {M M' : ModuleCat.{w} R}
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {P' : AugmentedResolution.{u,v,a'} Rᵐᵒᵖ A'}
    (f : A ⟶ A') (g : M ⟶ M') {l : LinearChainMap P.complex P'.complex}
    (hl : P.Lifts P' f.hom l)
    {k : LinearChainMap P.complex (T.rightResolutions A).val.complex}
    {k' : LinearChainMap P'.complex (T.rightResolutions A').val.complex}
    (hk : P.Lifts (AugmentedResolution.ofP103 _ (T.rightResolutions A).property) LinearMap.id k)
    (hk' : P'.Lifts (AugmentedResolution.ofP103 _ (T.rightResolutions A').property) LinearMap.id k')
    (n : ℕ) :
    ∀ z : Homology (tensorComplex P.complex M) n,
      T.torMap n f g ((tensorLinearChainMap k (LinearMap.id : M →ₗ[R] M)).homologyMap n z) =
        (tensorLinearChainMap k' (LinearMap.id : M' →ₗ[R] M')).homologyMap n
          ((tensorLinearChainMap l g.hom).homologyMap n z) := by
  let P₀ := T.rightResolutions A
  let P₀' := T.rightResolutions A'
  obtain ⟨l₀, hl₀⟩ := P103.Ch10.Comparison.chain_exists Rᵐᵒᵖ A A' P₀.val P₀'.val P₀.property f.hom
  have hmap := (T.torMaps n).formula P₀ P₀' f g l₀ hl₀
  have hl₀' : (AugmentedResolution.ofP103 P₀.val P₀.property).Lifts
      (AugmentedResolution.ofP103 P₀'.val P₀'.property) f.hom (LinearChainMap.ofHom l₀) :=
    DFunLike.congr_fun hl₀
  have h := tensor_resolution_comparison_natural g.hom hl hl₀' hk hk' n
  intro z
  let t := (tensorLinearChainMap k (LinearMap.id : M →ₗ[R] M)).homologyMap n z
  have h₁ := DFunLike.congr_fun hmap t
  have h₂ := DFunLike.congr_fun (tensor_homologyMap_ofHom l₀ g.hom n).symm t
  have h₃ := DFunLike.congr_fun h z
  exact h₁.trans (h₂.trans h₃)

theorem heterogeneous_lift_independence :
    Specs.HeterogeneousLiftIndependence.{u,v,w,v',w'} := by
  intro R _ A A' M M' P P' Q Q' f g
  constructor
  · obtain ⟨l, hl⟩ := LinearChainMap.exists_augmentedLift P P' f
    obtain ⟨m, hm⟩ := LinearChainMap.exists_augmentedLift Q Q' g
    exact ⟨l, m, hl, hm⟩
  · intro l l' m m' hl hl' hm hm' α β F G n
    constructor
    · rw [F.left_eq, G.left_eq, homologyMap_eq_of_homotopic
        (tensorLinearChainMap_homotopic (LinearChainMap.augmentedLifts_homotopic P P' f l l' hl hl') g)]
    · rw [F.right_eq, G.right_eq, homologyMap_eq_of_homotopic
        (leftTensorLinearChainMap_homotopic f (LinearChainMap.augmentedLifts_homotopic Q Q' g m m' hm hm'))]


set_option backward.isDefEq.respectTransparency false in
/-- Lift independence on the signed total follows from its left augmentation
square and injectivity of the target augmentation on homology. -/
theorem BalanceMaps.total_homology_independent
    {A : ModuleCat.{v} Rᵐᵒᵖ} {A' : ModuleCat.{v'} Rᵐᵒᵖ}
    {M : ModuleCat.{w} R} {M' : ModuleCat.{w'} R}
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {P' : AugmentedResolution.{u,v',a'} Rᵐᵒᵖ A'}
    {Q : AugmentedResolution.{u,w,b} R M} {Q' : AugmentedResolution.{u,w',b'} R M'}
    {f : A →ₗ[Rᵐᵒᵖ] A'} {g : M →ₗ[R] M'}
    {l l' : LinearChainMap P.complex P'.complex} {m m' : LinearChainMap Q.complex Q'.complex}
    (hl : P.Lifts P' f l) (hl' : P.Lifts P' f l')
    (hm : Q.Lifts Q' g m) (hm' : Q.Lifts Q' g m')
    {α : OriginalAugmentations P Q} {β : OriginalAugmentations P' Q'} (hβ : β.left.IsQuasiIso)
    (F : BalanceMaps f g l m α β) (G : BalanceMaps f g l' m' α β) :
    F.total.homologyMap = G.total.homologyMap := by
  funext n
  have h := (heterogeneous_lift_independence R A A' M M' P P' Q Q' f g).2
    l l' m m' hl hl' hm hm' α β F G n
  refine DFunLike.ext _ _ fun z => ?_
  apply (hβ n).injective
  have hF := F.total.homologyMap_square F.left α.left β.left F.left_square n
  have hG := G.total.homologyMap_square G.left α.left β.left G.left_square n
  rw [h.1] at hF
  exact DFunLike.congr_fun (hF.trans hG.symm) z

/-- Lifts of the identity compare any two choices of resolutions by inverse
maps on the outer homologies and on the signed total homology. -/
theorem BalanceMaps.resolution_change_homology
    {A : ModuleCat.{v} Rᵐᵒᵖ} {M : ModuleCat.{w} R}
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {P' : AugmentedResolution.{u,v,a'} Rᵐᵒᵖ A}
    {Q : AugmentedResolution.{u,w,b} R M} {Q' : AugmentedResolution.{u,w,b'} R M}
    {l : LinearChainMap P.complex P'.complex} {k : LinearChainMap P'.complex P.complex}
    {m : LinearChainMap Q.complex Q'.complex} {j : LinearChainMap Q'.complex Q.complex}
    (hl : P.Lifts P' LinearMap.id l) (hk : P'.Lifts P LinearMap.id k)
    (hm : Q.Lifts Q' LinearMap.id m) (hj : Q'.Lifts Q LinearMap.id j)
    {α : OriginalAugmentations P Q} {β : OriginalAugmentations P' Q'} (hα : α.left.IsQuasiIso)
    (F : BalanceMaps LinearMap.id LinearMap.id l m α β)
    (G : BalanceMaps LinearMap.id LinearMap.id k j β α) (n : ℕ) :
    (G.left.homologyMap n).comp (F.left.homologyMap n) = LinearMap.id ∧
    (G.right.homologyMap n).comp (F.right.homologyMap n) = LinearMap.id ∧
    (G.total.homologyMap n).comp (F.total.homologyMap n) =
      (LinearChainMap.id (ordinaryTotal P.complex Q.complex)).homologyMap n := by
  have hleft : (G.left.homologyMap n).comp (F.left.homologyMap n) = LinearMap.id := by
    rw [G.left_eq, F.left_eq]
    exact tensor_comparison_homology_inverse hl hk M n
  have hright : (G.right.homologyMap n).comp (F.right.homologyMap n) = LinearMap.id := by
    rw [G.right_eq, F.right_eq]
    exact left_tensor_comparison_homology_inverse A hm hj n
  refine ⟨hleft, hright, DFunLike.ext _ _ fun z => ?_⟩
  apply (hα n).injective
  have hF := DFunLike.congr_fun
    (F.total.homologyMap_square F.left α.left β.left F.left_square n) z
  have hG := DFunLike.congr_fun
    (G.total.homologyMap_square G.left β.left α.left G.left_square n) (F.total.homologyMap n z)
  have hi := DFunLike.congr_fun hleft (α.left.homologyMap n z)
  simp only [LinearChainMap.homologyMap_id, LinearMap.comp_apply, LinearMap.id_apply] at hF hG hi ⊢
  rw [hG, hF, hi]

end Homotopies

end AdvancedHomologicalAlgebra.TorBalance
