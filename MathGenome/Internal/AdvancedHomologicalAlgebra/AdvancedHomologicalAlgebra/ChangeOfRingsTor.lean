import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChangeOfRingsTor
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import Mathlib.Algebra.Module.TransferInstance
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TorBalance
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleComplexConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import MathGenome.Internal.AlgebraCore.P103.Ch10.ProjectiveResolutions

noncomputable section
universe u v w x a b
namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open CategoryTheory
open P103.BalancedTensor
variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable (f : R →+* S) (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A]

/-- The R–S bimodule S induces a right S action on extension of scalars. -/
def extensionAction : ExtensionAction f A where
  module := rightModule
  formula _ _ _ := rfl

local instance extensionModule : Module Sᵐᵒᵖ (Tensor R A (Restricted f S)) :=
  (extensionAction f A).module

/-- Functoriality in the right module is S-linear. -/
def extensionMap {B : Type x} [AddCommGroup B] [Module Rᵐᵒᵖ B]
    (g : A →ₗ[Rᵐᵒᵖ] B) :
    Tensor R A (Restricted f S) →ₗ[Sᵐᵒᵖ] Tensor R B (Restricted f S) :=
  mapRightLinear g LinearMap.id (by intros; rfl)

/-- Extension of scalars, retaining the unused right S-action. -/
def scalarExtension : ModuleCat.{w} Rᵐᵒᵖ ⥤ ModuleCat.{max w v} Sᵐᵒᵖ where
  obj X := ModuleCat.of Sᵐᵒᵖ (Tensor R X (Restricted f S))
  map g := ModuleCat.ofHom (extensionMap f _ g.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using induction_on with
    | h0 => simp
    | ht a s => rfl
    | ha x y hx hy => simp only [map_add, hx, hy]
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change extensionMap f _ (h.hom.comp g.hom) z =
      extensionMap f _ h.hom (extensionMap f _ g.hom z)
    induction z using induction_on with
    | h0 => simp
    | ht a s => rfl
    | ha x y hx hy => simp only [map_add, hx, hy]

instance scalarExtension_additive : (scalarExtension f :
    ModuleCat.{w} Rᵐᵒᵖ ⥤ ModuleCat.{max w v} Sᵐᵒᵖ).Additive where
  map_add := by
    intro X Y g h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change extensionMap f _ (g.hom + h.hom) z =
      extensionMap f _ g.hom z + extensionMap f _ h.hom z
    induction z using induction_on with
    | h0 => simp
    | ht a s => exact add_tmul _ _ _
    | ha x y hx hy => simp only [map_add, hx, hy]; abel

/-- The S-linear extension map is the existing P103 tensor map on groups. -/
theorem extensionMap_eq {B : Type x} [AddCommGroup B] [Module Rᵐᵒᵖ B]
    (g : A →ₗ[Rᵐᵒᵖ] B) (z : Tensor R A (Restricted f S)) :
    extensionMap f A g z =
      P103.Specs.Ch11.ExtTorDefinitions.tensorMap g LinearMap.id z := by
  induction z using induction_on with
  | h0 => simp
  | ht a s => rfl
  | ha x y hx hy => simp only [map_add, hx, hy]

def extensionComplexData (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) :
    ExtensionComplexData f C where
  action n := extensionAction f (C.X n)
  complex := ((scalarExtension f).mapHomologicalComplex (ComplexShape.down ℕ)).obj C
  termEquiv _ := AddEquiv.refl _
  linear _ _ _ := rfl
  differential m n z := extensionMap_eq f _ (C.d m n).hom z

theorem extension_complex : Specs.ExtensionComplex.{u,v,w} := by
  intro R S _ _ f C
  exact ⟨extensionComplexData f C⟩

open P103.Specs.Ch10.Complexes P103.Specs.Ch11.ExtTorDefinitions

/-- The underlying cycles are unchanged on forgetting the right S-action. -/
def extensionCyclesEquiv (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) (n : ℕ) :
    cycles (extensionComplexData f C).complex n ≃ₗ[ℤ]
      cycles (tensorComplex C (Restricted f S)) n where
  toFun z := ⟨z.val, by
    change tensorMap (C.d n _).hom LinearMap.id z.val = 0
    exact (extensionMap_eq f _ _
      (show Tensor R (C.X n) (Restricted f S) from z.val)).symm.trans z.property⟩
  invFun z := ⟨z.val, by
    change extensionMap f _ (C.d n _).hom z.val = 0
    exact (extensionMap_eq f _ _
      (show Tensor R (C.X n) (Restricted f S) from z.val)).trans z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extension_boundaries (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) (n : ℕ) :
    ((cycleBoundaries (extensionComplexData f C).complex n).restrictScalars ℤ).map
      (extensionCyclesEquiv f C n).toLinearMap =
      cycleBoundaries (tensorComplex C (Restricted f S)) n := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    change tensorMap (C.d _ n).hom LinearMap.id x = y.val
    exact (extensionMap_eq f _ _
      (show Tensor R (C.X _) (Restricted f S) from x)).symm.trans hx
  · rintro ⟨x, hx⟩
    refine ⟨(extensionCyclesEquiv f C n).symm z, ?_, by simp⟩
    refine ⟨x, ?_⟩
    change extensionMap f _ (C.d _ n).hom x = z.val
    exact (extensionMap_eq f _ _
      (show Tensor R (C.X _) (Restricted f S) from x)).trans hx

/-- Forgetting the right S-action recovers exactly the P103 Tor homology. -/
def innerHomologyData (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) :
    InnerHomologyData f C where
  toExtensionComplexData := extensionComplexData f C
  homologyEquiv n :=
    (Submodule.Quotient.restrictScalarsEquiv ℤ _).symm.trans
      (Submodule.Quotient.equiv _ _ (extensionCyclesEquiv f C n)
        (extension_boundaries f C n))
  representative n z := ⟨extensionCyclesEquiv f C n z, rfl, rfl⟩

theorem inner_homology : Specs.InnerHomology.{u,v,w} := by
  intro R S _ _ f C
  exact ⟨innerHomologyData f C⟩

/-- The unused right action transported to the actual P103 Tor quotient. -/
@[instance_reducible] def innerTorModule (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) (n : ℕ) :
    Module Sᵐᵒᵖ (Homology (tensorComplex C (Restricted f S)) n) :=
  ((innerHomologyData f C).homologyEquiv n).symm.toAddEquiv.module Sᵐᵒᵖ

theorem inner_tor_action : Specs.InnerTorAction.{u,v,w} := by
  intro R S _ _ f C n
  refine ⟨innerHomologyData f C, innerTorModule f C n, ?_⟩
  intro s z
  exact ((((innerHomologyData f C).homologyEquiv n).symm.toAddEquiv.linearEquiv
    Sᵐᵒᵖ).symm.map_smul s z)

section Reassociation
variable (M : Type x) [AddCommGroup M] [Module S M]

private def contraction (y : M) :
    Tensor R A (Restricted f S) →+ Tensor R A (Restricted f M) :=
  lift <| Pairing.ofFun
    (fun a s => tmul R a (Restricted.of f M ((Restricted.val f S s) • y)))
    (by intros; exact add_tmul _ _ _)
    (by
      intro a s t
      change tmul R a (Restricted.of f M ((Restricted.val f S s + Restricted.val f S t) • y)) = _
      rw [add_smul, Restricted.of_add, tmul_add])
    (by
      intro r a s
      rw [balance]
      change tmul R a (Restricted.of f M (f r • (Restricted.val f S s • y))) =
        tmul R a (Restricted.of f M ((f r * Restricted.val f S s) • y))
      rw [mul_smul])

private def forward :
    Tensor S (Tensor R A (Restricted f S)) M →+ Tensor R A (Restricted f M) :=
  lift <| Pairing.ofFun (fun z y => contraction f A M y z)
    (by intros; exact map_add _ _ _)
    (by
      intro z y y'
      induction z using induction_on with
      | h0 => simp
      | ht a s =>
        change tmul R a (Restricted.of f M (Restricted.val f S s • (y+y'))) = _
        simp only [smul_add, Restricted.of_add, tmul_add]
        rfl
      | ha a b ha hb => simp [map_add, ha, hb, add_add_add_comm])
    (by
      intro s z y
      induction z using induction_on with
      | h0 => simp
      | ht a t =>
        change tmul R a (Restricted.of f M ((Restricted.val f S t * s) • y)) =
          tmul R a (Restricted.of f M (Restricted.val f S t • s • y))
        rw [mul_smul]
      | ha a b ha hb => simp [smul_add, map_add, ha, hb])

private def backward :
    Tensor R A (Restricted f M) →+ Tensor S (Tensor R A (Restricted f S)) M :=
  lift <| Pairing.ofFun
    (fun a y => tmul S (tmul R a (Restricted.of f S 1)) (Restricted.val f M y))
    (by intros; simp only [add_tmul])
    (by intros; exact tmul_add _ _ _)
    (by
      intro r a y
      rw [balance (R := R)]
      change tmul S (tmul R a (Restricted.of f S (f r * 1))) (Restricted.val f M y) =
        tmul S (tmul R a (Restricted.of f S 1)) (f r • Restricted.val f M y)
      rw [mul_one, ← balance, (extensionAction f A).formula, one_mul])

/-- (A ⊗_R S) ⊗_S M ≃ A ⊗_R M, for the actual balanced tensor model. -/
def reassociation :
    Tensor S (Tensor R A (Restricted f S)) M ≃+ Tensor R A (Restricted f M) :=
  { forward f A M with
    invFun := backward f A M
    left_inv := by
      intro z
      change backward f A M (forward f A M z) = z
      induction z using induction_on with
      | h0 => simp
      | ht t y =>
        induction t using induction_on with
        | h0 => simp
        | ht a s =>
          change tmul S (tmul R a (Restricted.of f S 1)) (Restricted.val f S s • y) =
            tmul S (tmul R a s) y
          rw [← balance, (extensionAction f A).formula, one_mul]
          rfl
        | ha a b ha hb =>
          simp only [add_tmul, map_add] at *
          exact congrArg₂ (· + ·) ha hb
      | ha a b ha hb => simp [map_add, ha, hb]
    right_inv := by
      intro z
      change forward f A M (backward f A M z) = z
      induction z using induction_on with
      | h0 => simp
      | ht a y =>
        change tmul R a (Restricted.of f M ((1 : S) • Restricted.val f M y)) = tmul R a y
        rw [one_smul]
        rfl
      | ha a b ha hb => simp [map_add, ha, hb] }

@[simp] theorem reassociation_tmul (a : A) (s : S) (y : M) :
    reassociation f A M (tmul S (tmul R a (Restricted.of f S s)) y) =
      tmul R a (Restricted.of f M (s • y)) := rfl

@[simp] theorem reassociation_symm_tmul (a : A) (y : M) :
    (reassociation f A M).symm (tmul R a (Restricted.of f M y)) =
      tmul S (tmul R a (Restricted.of f S 1)) y := rfl
end Reassociation

theorem tensor_algebra : Specs.TensorAlgebra.{u,v,w,x} := by
  intro R S _ _ f A _ _
  refine ⟨extensionAction f A, ?_, ?_⟩
  · intro B _ _ g
    exact ⟨extensionAction f B, extensionMap f A g, fun _ _ => rfl⟩
  · intro M _ _
    exact ⟨reassociation f A M, reassociation_tmul f A M, reassociation_symm_tmul f A M⟩
/-- Tensor reassociation commutes with both inputs, hence both differentials. -/
theorem reassociation_naturality : Specs.ReassociationNaturality.{u,v,w,x} := by
  intro R S _ _ f A B _ _ _ _ M N _ _ _ _ a b
  let := a.module
  let := b.module
  intro g h k hk e e' he he' z
  suffices H : e'.toAddMonoidHom.comp (P103.BalancedTensor.map k h) =
      (P103.BalancedTensor.map g (Restricted.map f h)).comp e.toAddMonoidHom by
    exact DFunLike.congr_fun H z
  apply hom_ext
  intro t y
  induction t using induction_on with
  | h0 => simp
  | ht x s =>
    change e' (tmul S (k (tmul R x (Restricted.of f S (Restricted.val f S s)))) (h y)) =
      P103.BalancedTensor.map g (Restricted.map f h)
        (e (tmul S (tmul R x (Restricted.of f S (Restricted.val f S s))) y))
    rw [hk x (Restricted.val f S s), he', he]
    change tmul R (g x) (Restricted.of f N (Restricted.val f S s • h y)) =
      tmul R (g x) (Restricted.of f N (h (Restricted.val f S s • y)))
    rw [h.map_smul]
  | ha x y hx hy =>
    simp only [add_tmul, map_add] at *
    exact congrArg₂ (· + ·) hx hy
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reassociation as a natural isomorphism of the actual tensor functors.
It applies to complexes in any degree shape, so includes every differential. -/
def reassociationNatIso (M : Type (max v x)) [AddCommGroup M] [Module S M] :
    (scalarExtension f : ModuleCat.{w} Rᵐᵒᵖ ⥤ ModuleCat.{max w v} Sᵐᵒᵖ) ⋙
      tensorFunctor M ≅ tensorFunctor (Restricted f M) :=
  NatIso.ofComponents (fun A =>
    (reassociation f A M).toIntLinearEquiv.toModuleIso) (by
      intro A B g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change reassociation f B M (tensorMap (extensionMap f A g.hom) LinearMap.id z) =
        tensorMap g.hom LinearMap.id (reassociation f A M z)
      induction z using induction_on with
      | h0 => simp
      | ht t y =>
        induction t using induction_on with
        | h0 => simp
        | ht x s => rfl
        | ha a b ha hb =>
          simp only [P103.Specs.Ch11.TorBalance.tensorMap_tmul, add_tmul, map_add] at *
          exact congrArg₂ (· + ·) ha hb
      | ha a b ha hb => simp [map_add, ha, hb])

/-- Reassociation in the right-complex direction, including the differentials. -/
def reassociationComplexIso (M : Type (max v x)) [AddCommGroup M] [Module S M]
    {ι : Type*} (c : ComplexShape ι) (C : HomologicalComplex (ModuleCat.{w} Rᵐᵒᵖ) c) :
    ((tensorFunctor M).mapHomologicalComplex c).obj
      (((scalarExtension f).mapHomologicalComplex c).obj C) ≅
      ((tensorFunctor (Restricted f M)).mapHomologicalComplex c).obj C :=
  (Functor.mapHomologicalComplexCompIso (reassociationNatIso f M) c).app C

section QuotientComparison
variable {T : Type*} [Ring T] {ι : Type*} {c : ComplexShape ι}

/-- The boundary submodule used in P103 is the range in Mathlib's concrete
left homology data; only the presentation of membership differs. -/
theorem cycleBoundaries_eq_range (C : HomologicalComplex (ModuleCat.{w} T) c) (n : ι) :
    cycleBoundaries C n = (C.sc n).moduleCatToCycles.range := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-- The explicit upstream quotient and categorical homology are canonically
isomorphic for all shapes, without exactness or boundedness assumptions. -/
def explicitToCategoricalHomologyIso (C : HomologicalComplex (ModuleCat.{w} T) c) (n : ι) :
    ModuleCat.of T (Homology C n) ≅ C.homology n :=
  (Submodule.quotEquivOfEq _ _ (cycleBoundaries_eq_range C n)).toModuleIso ≪≫
    (C.sc n).moduleCatHomologyIso.symm

/-- The isomorphism sends a cycle class to that same categorical homology class. -/
theorem explicitToCategoricalHomologyIso_class (C : HomologicalComplex (ModuleCat.{w} T) c) (n : ι) :
    ModuleCat.ofHom (homologyClass C n) ≫ (explicitToCategoricalHomologyIso C n).hom =
      (C.sc n).moduleCatCyclesIso.inv ≫ C.homologyπ n := by
  erw [ShortComplex.moduleCatCyclesIso_inv_π]
  change ModuleCat.ofHom (homologyClass C n) ≫
    (Submodule.quotEquivOfEq _ _ (cycleBoundaries_eq_range C n)).toModuleIso.hom ≫
    (C.sc n).moduleCatHomologyIso.inv = _
  have h : ModuleCat.ofHom (homologyClass C n) ≫
      (Submodule.quotEquivOfEq _ _ (cycleBoundaries_eq_range C n)).toModuleIso.hom =
        (C.sc n).moduleCatLeftHomologyData.π := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  erw [← Category.assoc, h]

/-- The explicit-to-categorical comparison commutes with every complex map. -/
theorem explicitToCategoricalHomologyIso_naturality
    {C D : HomologicalComplex (ModuleCat.{w} T) c} (g : C ⟶ D) (n : ι) :
    ModuleCat.ofHom (homologyMap g n) ≫ (explicitToCategoricalHomologyIso D n).hom =
      (explicitToCategoricalHomologyIso C n).hom ≫ HomologicalComplex.homologyMap g n := by
  let q := ModuleCat.ofHom (homologyClass C n)
  have : Epi q := (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  have hm : q ≫ ModuleCat.ofHom (homologyMap g n) =
      ModuleCat.ofHom (cyclesMap g n) ≫ ModuleCat.ofHom (homologyClass D n) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  have hk : ModuleCat.ofHom (cyclesMap g n) ≫ (D.sc n).moduleCatCyclesIso.inv =
      (C.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap g n := by
    apply (cancel_mono (D.iCycles n)).mp
    erw [Category.assoc, ShortComplex.moduleCatCyclesIso_inv_iCycles,
      Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
      ShortComplex.moduleCatCyclesIso_inv_iCycles]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  apply (cancel_epi q).mp
  erw [← Category.assoc, hm, Category.assoc, explicitToCategoricalHomologyIso_class,
    ← Category.assoc, hk, Category.assoc, ← HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, ← explicitToCategoricalHomologyIso_class]

/-- Thus the bridge is an isomorphism of homology functors. -/
def quotientHomologyNatIso (c : ComplexShape ι) (n : ι) :
    (P103.Specs.Ch10.Comparison.quotientHomology c n :
      HomologicalComplex (ModuleCat.{w} T) c ⥤ ModuleCat.{w} T) ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{w} T) c n :=
  NatIso.ofComponents (fun C => explicitToCategoricalHomologyIso C n)
    (fun {_ _} g => explicitToCategoricalHomologyIso_naturality g n)

end QuotientComparison

/-- Flat tensoring commutes with the actual P103 quotient homology, in any
complex shape. This bridges the homology API used for filtered pages. -/
def flatQuotientHomologyIso
    {T : Type*} [Ring T] (N : Type x) [AddCommGroup N] [Module T N]
    (hN : P103.Specs.Ch02.FlatnessTests.Flat.{_,x,w} T N)
    {ι : Type*} (c : ComplexShape ι) (C : HomologicalComplex (ModuleCat.{w} Tᵐᵒᵖ) c)
    (n : ι) :
    ModuleCat.of ℤ (Tensor T (Homology C n) N) ≅
      ModuleCat.of ℤ (Homology (((tensorFunctor N).mapHomologicalComplex c).obj C) n) := by
  letI := TorBalance.flat_tensor_preservesHomology hN
  exact (tensorFunctor N).mapIso (explicitToCategoricalHomologyIso C n) ≪≫
    (TorBalance.exactHomologyComparison (tensorFunctor N)).equivalence (C.sc n) ≪≫
    (explicitToCategoricalHomologyIso (((tensorFunctor N).mapHomologicalComplex c).obj C) n).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient comparison is natural in a flat left coefficient. Thus it
also intertwines the differentials in a complex of flat coefficients. -/
theorem flatQuotientHomologyIso_naturality
    {T : Type*} [Ring T] {N N' : Type x}
    [AddCommGroup N] [Module T N] [AddCommGroup N'] [Module T N']
    (hN : P103.Specs.Ch02.FlatnessTests.Flat.{_,x,w} T N)
    (hN' : P103.Specs.Ch02.FlatnessTests.Flat.{_,x,w} T N') (g : N →ₗ[T] N')
    {ι : Type*} (c : ComplexShape ι) (C : HomologicalComplex (ModuleCat.{w} Tᵐᵒᵖ) c)
    (n : ι) :
    ModuleCat.ofHom (tensorMap (LinearMap.id : Homology C n →ₗ[Tᵐᵒᵖ] _) g) ≫
      (flatQuotientHomologyIso N' hN' c C n).hom =
    (flatQuotientHomologyIso N hN c C n).hom ≫ ModuleCat.ofHom
      (homologyMap ((TorBalance.tensorCoefficientMap g).mapHomologicalComplex c |>.app C) n) := by
  have := TorBalance.flat_tensor_preservesHomology hN
  have := TorBalance.flat_tensor_preservesHomology hN'
  let F := (tensorFunctor N : ModuleCat.{w} Tᵐᵒᵖ ⥤ ModuleCat.{max w x} ℤ)
  let G := (tensorFunctor N' : ModuleCat.{w} Tᵐᵒᵖ ⥤ ModuleCat.{max w x} ℤ)
  let τ : F ⟶ G := TorBalance.tensorCoefficientMap g
  let d := (τ.mapHomologicalComplex c).app C
  let X := (F.mapHomologicalComplex c).obj C
  let Y := (G.mapHomologicalComplex c).obj C
  have hq : HomologicalComplex.homologyMap d n ≫ (explicitToCategoricalHomologyIso Y n).inv =
      (explicitToCategoricalHomologyIso X n).inv ≫ ModuleCat.ofHom (homologyMap d n) := by
    apply (cancel_mono (explicitToCategoricalHomologyIso Y n).hom).mp
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, explicitToCategoricalHomologyIso_naturality, Iso.inv_hom_id_assoc]
  have hc := TorBalance.exactHomologyComparison_compatible τ (C.sc n)
  change τ.app (ModuleCat.of Tᵐᵒᵖ (Homology C n)) ≫
    G.map (explicitToCategoricalHomologyIso C n).hom ≫
      ((TorBalance.exactHomologyComparison G).equivalence (C.sc n)).hom ≫
        (explicitToCategoricalHomologyIso Y n).inv =
    F.map (explicitToCategoricalHomologyIso C n).hom ≫
      ((TorBalance.exactHomologyComparison F).equivalence (C.sc n)).hom ≫
        (explicitToCategoricalHomologyIso X n).inv ≫ ModuleCat.ofHom (homologyMap d n)
  rw [← τ.naturality_assoc]
  erw [← Category.assoc (τ.app (C.homology n)) _ _, hc, Category.assoc]
  change F.map (explicitToCategoricalHomologyIso C n).hom ≫
      ((TorBalance.exactHomologyComparison F).equivalence (C.sc n)).hom ≫
        HomologicalComplex.homologyMap d n ≫ (explicitToCategoricalHomologyIso Y n).inv = _
  erw [hq]

/-- The homology action comparison is linear over S, for the transported
module structure on the original Tor quotient. -/
def innerTorEquiv (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) (n : ℕ) :
    letI := innerTorModule f C n
    Homology (extensionComplexData f C).complex n ≃ₗ[Sᵐᵒᵖ]
      Homology (tensorComplex C (Restricted f S)) n :=
  (((innerHomologyData f C).homologyEquiv n).symm.toAddEquiv.linearEquiv Sᵐᵒᵖ).symm

/-- Horizontal homology of P⊗R Q is the tensor of the inner Tor with Q.
Only the flatness of the coefficient over S is used here. -/
def horizontalHomologyIso
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (N : Type (max v x)) [AddCommGroup N] [Module S N]
    (hN : P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S N) (n : ℕ) :
    letI := innerTorModule f C n
    Tensor S (Homology (tensorComplex C (Restricted f S)) n) N ≃ₗ[ℤ]
      Homology (tensorComplex C (Restricted f N)) n := by
  letI := innerTorModule f C n
  let E := (extensionComplexData f C).complex
  let a := (tensorFunctor N).mapIso (innerTorEquiv f C n).symm.toModuleIso
  let b := flatQuotientHomologyIso N hN (ComplexShape.down ℕ) E n
  let d := (P103.Specs.Ch10.Comparison.quotientHomology (ComplexShape.down ℕ) n).mapIso
    (reassociationComplexIso f N (ComplexShape.down ℕ) C)
  exact (a ≪≫ b ≪≫ d).toLinearEquiv

theorem horizontal_homology : Specs.HorizontalHomology.{u,v,w,x} := by
  intro R S _ _ f C M _ _ hM n
  exact ⟨⟨innerHomologyData f C, innerTorModule f C n,
    (innerTorEquiv f C n).map_smul, horizontalHomologyIso f C M hM n⟩⟩

/-- The right S-linear maps on inner homology are independent of the chosen
lift of a right-module map between projective resolutions. -/
theorem inner_lift_independent
    (A B : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup B] [Module Rᵐᵒᵖ B]
    (P : P103.Specs.Ch10.Comparison.LeftResolution Rᵐᵒᵖ A)
    (Q : P103.Specs.Ch10.Comparison.LeftResolution Rᵐᵒᵖ B) (hP : P.IsProjective)
    (g : A →ₗ[Rᵐᵒᵖ] B) (l l' : P.complex ⟶ Q.complex)
    (hl : P103.Specs.Ch10.Comparison.ChainLift P Q g l)
    (hl' : P103.Specs.Ch10.Comparison.ChainLift P Q g l') (n : ℕ) :
    homologyMap (((scalarExtension f).mapHomologicalComplex (ComplexShape.down ℕ)).map l) n =
      homologyMap (((scalarExtension f).mapHomologicalComplex (ComplexShape.down ℕ)).map l') n := by
  exact congrArg ModuleCat.Hom.hom
    (P103.Ch10.Comparison.chain_homology_independent Rᵐᵒᵖ Sᵐᵒᵖ (scalarExtension f)
      A B P Q hP g l l' n hl hl')

section Target
open CategoryTheory.Limits
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch11.TorBalance
open P103.Ch11.TorBalance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Only the right resolution needs to be projective for the vertical
augmentation. The left input is any exact augmented resolution. -/
theorem tensor_target_comparison
    {A : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type x} [AddCommGroup B] [Module R B]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B) (hP : P.IsProjective) :
    ∃ a : ordinaryTotal P.complex Q.complex ⟶ tensorComplex P.complex B,
      QuasiIsomorphism a ∧
      (∀ p (x : P.complex.X p) (y : Q.complex.X 0),
        (a.f p).hom (ordinaryInclusion P.complex Q.complex p 0 p (by omega)
          (tmul R x y)) = tmul R x (Q.ε y)) ∧
      (∀ (p q n : ℕ) (h : p+q=n), q ≠ 0 →
        (a.f n).hom.comp (ordinaryInclusion P.complex Q.complex p q n h) = 0) := by
  let K := P103.Specs.Ch11.TorBalance.tensorBicomplex
    (extendNonnegativeChain P.complex) (extendNonnegativeChain Q.complex)
  let L := ((tensorFunctor B).mapHomologicalComplex (ComplexShape.down ℤ)).obj
    (extendNonnegativeChain P.complex)
  have hK := ordinary_tensor_supported P.complex Q.complex
  have hKt : SupportedQuadrant K.flip 0 0 := by
    intro p q h
    exact hK q p (h.elim Or.inr Or.inl)
  have hL : SupportedIn L (Set.Ici 0) := by
    intro n hn
    exact ModuleCat.isZero_iff_subsingleton.mp ((tensorFunctor B).map_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr
        (P103.Ch10.Complexes.extendNonnegativeChain_supported P.complex n hn)))
  have hT : SupportedIn (total K) (Set.Ici 0) := by
    intro n hn
    exact P103.Ch10.TotalComplexAssembly.total_supportedBelow K 0 0 hK n (by simpa using hn)
  obtain ⟨l, hl, hl0, hlp⟩ := totalRowAugmentation_quasi K L
    (tensorRowAugmentation Q (extendNonnegativeChain P.complex))
    (tensorRowAugmentation_square Q (extendNonnegativeChain P.complex))
    (column_isZero_of_supported K.flip hKt) 0 hKt hL
    (tensorRowAugmentation_rows_acyclic P Q hP)
  let e := restrictExtendMapIso P.complex (tensorFunctor B)
  let a := HomologicalComplex.restrictionMap l nonnegativeChainEmbedding ≫ e.hom
  refine ⟨a, quasiIsomorphism_comp_any
    (quasiIsomorphism_restriction_nonnegative hT hL l hl)
    (quasiIsomorphism_of_iso_any e), ?_, ?_⟩
  · intro p x y
    rw [ordinaryInclusion_tmul]
    have hx := congrArg (fun k => k.hom (tmul R
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom x)
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom y))) (hl0 (p : ℤ))
    change (l.f (p : ℤ)).hom
      ((totalInclusion K p 0 p (by omega)).hom (tmul R
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom x)
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom y))) =
      tmul R ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom x)
        (Q.ε ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
          ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom y))) at hx
    change (e.hom.f p).hom ((l.f (p : ℤ)).hom _) = _
    erw [hx]
    change tmul R
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom.hom
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom x))
      (Q.ε ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom y))) = _
    simp only [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  · intro p q n h hq
    apply tensor_hom_ext
    intro x y
    change (a.f n).hom (ordinaryInclusion P.complex Q.complex p q n h (tmul R x y)) = 0
    rw [ordinaryInclusion_tmul]
    have hx := congrArg (fun k => k.hom (tmul R
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom x)
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom y)))
      (hlp p q n (by exact_mod_cast h) (by exact_mod_cast hq))
    change (l.f (n : ℤ)).hom
      ((totalInclusion K p q n (by exact_mod_cast h)).hom (tmul R
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom x)
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom y))) = 0 at hx
    change (e.hom.f n).hom ((l.f (n : ℤ)).hom _) = 0
    erw [hx, map_zero]

/-- In particular restriction of an S-resolution is sufficient. No
projectivity over R, and no flatness of S over R, is assumed. -/
theorem target_comparison : Specs.TargetComparison.{u,v,w,x} := by
  intro R S _ _ f A _ _ M _ _ P Q hP
  obtain ⟨a, h, hz, hp⟩ := tensor_target_comparison P (restrictionResolution f M Q) hP
  exact ⟨⟨a, h, hz, hp⟩⟩

end Target


section Horizontal
set_option maxHeartbeats 1200000

open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch11.ExtTorDefinitions
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem reassociationComplexIso_coefficient_naturality
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    {N N' : Type (max v x)} [AddCommGroup N] [Module S N]
    [AddCommGroup N'] [Module S N'] (g : N →ₗ[S] N') :
    ((TorBalance.tensorCoefficientMap g).mapHomologicalComplex (ComplexShape.down ℕ)).app
      (extensionComplexData f C).complex ≫
      (reassociationComplexIso f N' (ComplexShape.down ℕ) C).hom =
    (reassociationComplexIso f N (ComplexShape.down ℕ) C).hom ≫
      tensorSecondMap C (Restricted.map f g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro t y
  letI := (extensionAction f (C.X n)).module
  change reassociation f (C.X n) N' (tensorMap LinearMap.id g (tmul S t y)) =
    tensorMap LinearMap.id (Restricted.map f g) (reassociation f (C.X n) N (tmul S t y))
  induction t using induction_on with
  | h0 => simp
  | ht a s =>
    change tmul R a (Restricted.of f N' (Restricted.val f S s • g y)) =
      tmul R a (Restricted.of f N' (g (Restricted.val f S s • y)))
    rw [g.map_smul]
  | ha a b ha hb =>
    simp only [add_tmul, map_add] at *
    exact congrArg₂ (· + ·) ha hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem horizontalHomologyIso_naturality
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    {N N' : Type (max v x)} [AddCommGroup N] [Module S N]
    [AddCommGroup N'] [Module S N']
    (hN : P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S N)
    (hN' : P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S N')
    (g : N →ₗ[S] N') (n : ℕ) :
    letI := innerTorModule f C n
    ModuleCat.ofHom (tensorMap (LinearMap.id :
      Homology (tensorComplex C (Restricted f S)) n →ₗ[Sᵐᵒᵖ] _) g) ≫
      (horizontalHomologyIso f C N' hN' n).toModuleIso.hom =
    (horizontalHomologyIso f C N hN n).toModuleIso.hom ≫ ModuleCat.ofHom
      (homologyMap (tensorSecondMap C (Restricted.map f g)) n) := by
  letI := innerTorModule f C n
  let E := (extensionComplexData f C).complex
  let H := P103.Specs.Ch10.Comparison.quotientHomology (S := ℤ) (ComplexShape.down ℕ) n
  let a := (tensorFunctor N).mapIso (innerTorEquiv f C n).symm.toModuleIso
  let a' := (tensorFunctor N').mapIso (innerTorEquiv f C n).symm.toModuleIso
  let b := flatQuotientHomologyIso N hN (ComplexShape.down ℕ) E n
  let b' := flatQuotientHomologyIso N' hN' (ComplexShape.down ℕ) E n
  let d := H.mapIso (reassociationComplexIso f N (ComplexShape.down ℕ) C)
  let d' := H.mapIso (reassociationComplexIso f N' (ComplexShape.down ℕ) C)
  let m := ModuleCat.ofHom (tensorMap (LinearMap.id :
    Homology (tensorComplex C (Restricted f S)) n →ₗ[Sᵐᵒᵖ] _) g)
  let k := ModuleCat.ofHom (tensorMap (LinearMap.id : Homology E n →ₗ[Sᵐᵒᵖ] _) g)
  let l := ((TorBalance.tensorCoefficientMap g).mapHomologicalComplex (ComplexShape.down ℕ)).app E
  let l' := tensorSecondMap C (Restricted.map f g)
  have ha : m ≫ a'.hom = a.hom ≫ k := by
    exact ((TorBalance.tensorCoefficientMap g).naturality (innerTorEquiv f C n).symm.toModuleIso.hom).symm
  have hb : k ≫ b'.hom = b.hom ≫ H.map l :=
    flatQuotientHomologyIso_naturality hN hN' g (ComplexShape.down ℕ) E n
  have hd : H.map l ≫ d'.hom = d.hom ≫ H.map l' := by
    change H.map l ≫ H.map (reassociationComplexIso f N' (ComplexShape.down ℕ) C).hom =
      H.map (reassociationComplexIso f N (ComplexShape.down ℕ) C).hom ≫ H.map l'
    rw [← H.map_comp, ← H.map_comp, reassociationComplexIso_coefficient_naturality]
  change m ≫ a'.hom ≫ b'.hom ≫ d'.hom = a.hom ≫ b.hom ≫ d.hom ≫ H.map l'
  rw [← Category.assoc m a'.hom, ha, Category.assoc, ← Category.assoc k b'.hom,
    hb, Category.assoc, hd]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def rowHomologyComplexIso
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (Q : ChainComplex (ModuleCat.{max v x} S) ℕ)
    (hQ : ∀ p, P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S (Q.X p)) (n : ℕ) :
    letI := innerTorModule f C n
    P103.Specs.Ch11.TorBalance.leftOrdinaryTensorComplex
      (Homology (tensorComplex C (Restricted f S)) n) Q ≅ rowHomologyComplex f C Q n := by
  letI := innerTorModule f C n
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => (horizontalHomologyIso f C (Q.X p) (hQ p) n).toModuleIso) ?_
  intro p p' h
  exact (horizontalHomologyIso_naturality f C (hQ p) (hQ p') (Q.d p p').hom n).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def rowHomologyTorEquiv
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (M : Type (max v x)) [AddCommGroup M] [Module S M]
    (Q : P103.Specs.Ch10.Comparison.LeftResolution S M) (hQ : Q.IsProjective) (n : ℕ) :
    letI := innerTorModule f C n
    ∀ (U : P103.Specs.Ch10.Comparison.LeftResolution Sᵐᵒᵖ
      (Homology (tensorComplex C (Restricted f S)) n)), U.IsProjective → ∀ p : ℕ,
      Homology (rowHomologyComplex f C Q.complex n) p ≃ₗ[ℤ] TorWith U M p := by
  letI := innerTorModule f C n
  intro U hU p
  have hQflat (j : ℕ) :
      P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S (Q.complex.X j) :=
    P103.Ch02.FlatnessTests.projective_flat S (Q.complex.X j) (hQ j)
  let e := rowHomologyComplexIso f C Q.complex hQflat n
  let a := (P103.Specs.Ch10.Comparison.quotientHomology (ComplexShape.down ℕ) p).mapIso e.symm
  let hb := TorBalance.balance S
    (Homology (tensorComplex C (Restricted f S)) n) M U Q hU hQ
  exact a.toLinearEquiv.trans (P103.Specs.Ch11.TorBalance.balanceEquiv
    hb.choose hb.choose_spec.1 hb.choose_spec.2 p).symm


end Horizontal

section HorizontalQLifts

open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch11.ExtTorDefinitions
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)

/-- A homotopic choice of lift in the left resolution gives exactly the same
map on the homology of the horizontal homology complex. -/
theorem row_lift_independent
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (M N : Type (max v x)) [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N]
    (Q : P103.Specs.Ch10.Comparison.LeftResolution S M)
    (Q' : P103.Specs.Ch10.Comparison.LeftResolution S N) (hQ : Q.IsProjective)
    (g : M →ₗ[S] N) (l l' : Q.complex ⟶ Q'.complex) (q p : ℕ)
    (hl : P103.Specs.Ch10.Comparison.ChainLift Q Q' g l)
    (hl' : P103.Specs.Ch10.Comparison.ChainLift Q Q' g l') :
    homologyMap ((((restrictionFunctor f ⋙ tensorCoefficientComplex C) ⋙
      P103.Specs.Ch10.Comparison.quotientHomology (ComplexShape.down ℕ) q).mapHomologicalComplex
        (ComplexShape.down ℕ)).map l) p =
    homologyMap ((((restrictionFunctor f ⋙ tensorCoefficientComplex C) ⋙
      P103.Specs.Ch10.Comparison.quotientHomology (ComplexShape.down ℕ) q).mapHomologicalComplex
        (ComplexShape.down ℕ)).map l') p := by
  exact congrArg ModuleCat.Hom.hom
    (P103.Ch10.Comparison.chain_homology_independent S ℤ
      ((restrictionFunctor f ⋙ tensorCoefficientComplex C) ⋙
        P103.Specs.Ch10.Comparison.quotientHomology (ComplexShape.down ℕ) q)
      M N Q Q' hQ g l l' p hl hl')

end HorizontalQLifts

section InnerNaturality

open CategoryTheory P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch11.ExtTorDefinitions
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem innerHomologyData_naturality
    {C D : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ} (l : C ⟶ D) (n : ℕ)
    (z : Homology (extensionComplexData f C).complex n) :
    (innerHomologyData f D).homologyEquiv n
      (homologyMap (((scalarExtension f).mapHomologicalComplex (ComplexShape.down ℕ)).map l) n z) =
    homologyMap (tensorFirstMap l (Restricted f S)) n
      ((innerHomologyData f C).homologyEquiv n z) := by
  refine Quotient.inductionOn z ?_
  intro x
  change homologyClass (tensorComplex D (Restricted f S)) n
      (extensionCyclesEquiv f D n
        (cyclesMap (((scalarExtension f).mapHomologicalComplex (ComplexShape.down ℕ)).map l) n x)) =
    homologyClass (tensorComplex D (Restricted f S)) n
      (cyclesMap (tensorFirstMap l (Restricted f S)) n (extensionCyclesEquiv f C n x))
  congr 1
  apply Subtype.ext
  exact extensionMap_eq f _ (l.f n).hom x.val

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def innerTorMap
    {C D : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ} (l : C ⟶ D) (n : ℕ) :
    letI := innerTorModule f C n
    letI := innerTorModule f D n
    Homology (tensorComplex C (Restricted f S)) n →ₗ[Sᵐᵒᵖ]
      Homology (tensorComplex D (Restricted f S)) n := by
  letI := innerTorModule f C n
  letI := innerTorModule f D n
  exact (innerTorEquiv f D n).toLinearMap.comp
    ((homologyMap (((scalarExtension f).mapHomologicalComplex (ComplexShape.down ℕ)).map l) n).comp
      (innerTorEquiv f C n).symm.toLinearMap)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem innerTorMap_eq
    {C D : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ} (l : C ⟶ D) (n : ℕ)
    (z : Homology (tensorComplex C (Restricted f S)) n) :
    innerTorMap f l n z = homologyMap (tensorFirstMap l (Restricted f S)) n z := by
  change (innerHomologyData f D).homologyEquiv n
      (homologyMap (((scalarExtension f).mapHomologicalComplex (ComplexShape.down ℕ)).map l) n
        (((innerHomologyData f C).homologyEquiv n).symm z)) = _
  rw [innerHomologyData_naturality]
  simp


end InnerNaturality

section TargetExtras
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Ch11.TorBalance

variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}

namespace TargetComparisonData
variable {A : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  {M : Type (max u v x)} [AddCommGroup M] [Module S M]
  {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution S M}

/-- The target identification is the map induced by the actual total augmentation. -/
def homologyEquiv (T : TargetComparisonData f A M P Q) (n : ℕ) :=
  LinearEquiv.ofBijective (homologyMap T.augmentation n) (T.quasi n)

@[simp] theorem homologyEquiv_apply (T : TargetComparisonData f A M P Q) (n : ℕ) (z) :
    T.homologyEquiv n z = homologyMap T.augmentation n z := rfl

@[simp] theorem homologyEquiv_class (T : TargetComparisonData f A M P Q) (n : ℕ)
    (z : cycles (ordinaryTotal P.complex (restrictionResolution f M Q).complex) n) :
    T.homologyEquiv n (homologyClass _ n z) =
      homologyClass (tensorComplex P.complex (Restricted f M)) n
        ⟨(T.augmentation.f n).hom z.val,
          P103.Ch10.Complexes.map_cycles T.augmentation n z.property⟩ := by
  exact P103.Ch10.Complexes.homologyMap_apply T.augmentation n z

end TargetComparisonData

/-- Restriction on a chosen resolution map, with the source and target fixed explicitly. -/
def restrictionResolutionMap
    {M M' : Type (max u v x)} [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M']
    {Q : LeftResolution S M} {Q' : LeftResolution S M'}
    (m : Q.complex ⟶ Q'.complex) :
    (restrictionResolution f M Q).complex ⟶ (restrictionResolution f M' Q').complex :=
  ((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the total augmentation uses only the degree-zero coefficient lift. -/
theorem target_augmentation_natural
    {A A' : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    {M M' : Type (max u v x)} [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M']
    {P : LeftResolution Rᵐᵒᵖ A} {P' : LeftResolution Rᵐᵒᵖ A'}
    {Q : LeftResolution S M} {Q' : LeftResolution S M'}
    (g : M →ₗ[S] M') (l : P.complex ⟶ P'.complex) (m : Q.complex ⟶ Q'.complex)
    (hm : ChainLift Q Q' g m)
    (α : TargetComparisonData f A M P Q) (β : TargetComparisonData f A' M' P' Q') :
    ordinaryTotalMap l (restrictionResolutionMap (f := f) m) ≫
      β.augmentation = α.augmentation ≫ tensorFirstMap l (Restricted f M) ≫
        tensorSecondMap P'.complex (Restricted.map f g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ordinaryTotal_hom_ext P.complex (restrictionResolution f M Q).complex n
  intro p q h a b
  change (β.augmentation.f n).hom
      (((ordinaryTotalMap l (restrictionResolutionMap (f := f) m)).f n).hom
        (ordinaryInclusion P.complex (restrictionResolution f M Q).complex p q n h (tmul R a b))) =
    ((tensorSecondMap P'.complex (Restricted.map f g)).f n).hom
      (((tensorFirstMap l (Restricted f M)).f n).hom
        ((α.augmentation.f n).hom
          (ordinaryInclusion P.complex (restrictionResolution f M Q).complex p q n h (tmul R a b))))
  rw [ordinaryTotalMap_inclusion (D := (restrictionResolution f M Q).complex)
    (D' := (restrictionResolution f M' Q').complex) l
    (restrictionResolutionMap (f := f) m)]
  by_cases hq : q = 0
  · subst q
    simp only [Nat.add_zero] at h
    subst n
    rw [β.zero, α.zero]
    exact congrArg (fun z : M' => tmul R ((l.f p).hom a) (Restricted.of f M' z))
      (LinearMap.congr_fun hm (Restricted.val f (Q.complex.X 0) b))
  · have ha := LinearMap.congr_fun (α.positive p q n h hq) (tmul R a b)
    have hb := LinearMap.congr_fun (β.positive p q n h hq)
      (tmul R ((l.f p).hom a)
        (((restrictionResolutionMap (f := f) m).f q).hom b))
    change (α.augmentation.f n).hom
      (ordinaryInclusion P.complex (restrictionResolution f M Q).complex p q n h (tmul R a b)) = 0 at ha
    change (β.augmentation.f n).hom
      (ordinaryInclusion P'.complex (restrictionResolution f M' Q').complex p q n h
        (tmul R ((l.f p).hom a)
          (((restrictionResolutionMap (f := f) m).f q).hom b))) = 0 at hb
    rw [ha, hb, map_zero, map_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient target identification commutes with simultaneous resolution maps. -/
theorem target_homologyEquiv_natural
    {A A' : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    {M M' : Type (max u v x)} [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M']
    {P : LeftResolution Rᵐᵒᵖ A} {P' : LeftResolution Rᵐᵒᵖ A'}
    {Q : LeftResolution S M} {Q' : LeftResolution S M'}
    (g : M →ₗ[S] M') (l : P.complex ⟶ P'.complex) (m : Q.complex ⟶ Q'.complex)
    (hm : ChainLift Q Q' g m)
    (α : TargetComparisonData f A M P Q) (β : TargetComparisonData f A' M' P' Q') (n : ℕ) :
    ∀ z,
      β.homologyEquiv n
        (homologyMap (ordinaryTotalMap l (restrictionResolutionMap (f := f) m)) n z) =
      homologyMap (tensorFirstMap l (Restricted f M) ≫
        tensorSecondMap P'.complex (Restricted.map f g)) n (α.homologyEquiv n z) := by
  intro z
  have hh := target_augmentation_natural g l m hm α β
  have hc := congrArg (fun k => homologyMap k n z) hh
  simp only [P103.Ch10.Complexes.homologyMap_comp, LinearMap.comp_apply,
    P103.Ch10.Complexes.homologyMap] at hc
  convert hc using 1
  · exact β.homologyEquiv_apply n _
  · rw [α.homologyEquiv_apply]
    exact LinearMap.congr_fun (P103.Ch10.Complexes.homologyMap_comp
      (tensorFirstMap l (Restricted f M))
      (tensorSecondMap P'.complex (Restricted.map f g)) n) _


end TargetExtras

section TargetInteger
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Ch11.TorBalance
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
namespace TargetComparisonData
variable {A : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  {M : Type (max u v x)} [AddCommGroup M] [Module S M]
  {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution S M}

theorem totalSupported (T : TargetComparisonData f A M P Q) :
    SupportedIn (ordinaryTensorTotal P.complex (restrictionResolution f M Q).complex) (Set.Ici 0) := by
  intro n hn
  exact P103.Ch10.TotalComplexAssembly.total_supportedBelow _ 0 0
    (ordinary_tensor_supported P.complex (restrictionResolution f M Q).complex) n (by simpa using hn)

/-- The target comparison also applies directly to the integer totalization. -/
def integerHomologyEquiv (T : TargetComparisonData f A M P Q) (n : ℕ) :=
  (restrictionHomologyEquiv
    (ordinaryTensorTotal P.complex (restrictionResolution f M Q).complex) T.totalSupported n).symm.trans
      (LinearEquiv.ofBijective (homologyMap T.augmentation n) (T.quasi n))

/-- Categorical homology of the integer totalization computes the original Tor quotient. -/
def categoricalIntegerHomologyIso (T : TargetComparisonData f A M P Q) (n : ℕ) :=
  (explicitToCategoricalHomologyIso (ordinaryTensorTotal P.complex (restrictionResolution f M Q).complex)
    (n : ℤ)).symm ≪≫ (T.integerHomologyEquiv n).toModuleIso

end TargetComparisonData

end TargetInteger

section TargetIndependent
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Ch11.TorBalance
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}

/-- Target maps induced by any lifts of the same pair of module maps agree.
The left resolution is only required to be exact, since its augmentation is used. -/
theorem target_lift_independent
    {A A' : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    {M M' : Type (max u v x)} [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M']
    {P : LeftResolution Rᵐᵒᵖ A} {P' : LeftResolution Rᵐᵒᵖ A'}
    {Q : LeftResolution S M} {Q' : LeftResolution S M'}
    (hP : P.IsProjective) (a : A →ₗ[Rᵐᵒᵖ] A') (g : M →ₗ[S] M')
    (l l' : P.complex ⟶ P'.complex) (m m' : Q.complex ⟶ Q'.complex)
    (hl : ChainLift P P' a l) (hl' : ChainLift P P' a l')
    (hm : ChainLift Q Q' g m) (hm' : ChainLift Q Q' g m')
    (α : TargetComparisonData f A M P Q) (β : TargetComparisonData f A' M' P' Q') (n : ℕ) :
    ∀ z,
      homologyMap (ordinaryTotalMap l (restrictionResolutionMap (f := f) m)) n z =
        homologyMap (ordinaryTotalMap l' (restrictionResolutionMap (f := f) m')) n z := by
  intro z
  apply (β.homologyEquiv n).injective
  rw [target_homologyEquiv_natural g l m hm α β n,
    target_homologyEquiv_natural g l' m' hm' α β n]
  have he := P103.Ch10.Comparison.chain_homology_independent Rᵐᵒᵖ ℤ
    (tensorFunctor (Restricted f M)) A A' P P' hP a l l' n hl hl'
  have he' : homologyMap (tensorFirstMap l (Restricted f M)) n =
      homologyMap (tensorFirstMap l' (Restricted f M)) n :=
    congrArg ModuleCat.Hom.hom he
  simp only [P103.Ch10.Complexes.homologyMap_comp, LinearMap.comp_apply]
  exact congrArg (homologyMap (tensorSecondMap P'.complex (Restricted.map f g)) n)
    (LinearMap.congr_fun he' (α.homologyEquiv n z))


end TargetIndependent


section SpectralAssembly
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Limits
open FiniteDiagonalFiltrations DoubleTotalization DoubleComplexFirstPages
open P103.Specs.Ch11.TorBalance
/-- Finite diagonals also hold for a translated upper quadrant. -/
theorem finiteDiagonals_of_upperQuadrant {A : Type u} [Category.{v} A] [Abelian A]
    (K : Bicomplex A) (p₀ q₀ : ℤ)
    (h : ∀ p q : ℤ, ¬ (p ≤ p₀ ∧ q ≤ q₀) → IsZero ((K.X p).X q)) :
    FiniteDiagonals K := by
  intro n
  let s : Set (Diagonal n) := {i | ¬ IsZero (diagonalFamily K n i)}
  have hp : ∀ i ∈ s, n-q₀ ≤ i.val.1 ∧ i.val.1 ≤ p₀ := by
    intro i hi
    have hb : i.val.1 ≤ p₀ ∧ i.val.2 ≤ q₀ := by
      by_contra hb
      exact hi (h i.val.1 i.val.2 hb)
    have he := i.property
    exact ⟨by omega, hb.1⟩
  have ht : Set.Finite ((fun i : Diagonal n => i.val.1) '' s) :=
    (Set.finite_Icc (n-q₀) p₀).subset (by
      rintro _ ⟨i, hi, rfl⟩
      exact hp i hi)
  apply Set.Finite.of_finite_image ht
  intro i hi j hj hij
  apply Subtype.ext
  apply Prod.ext hij
  have hi' : i.val.1 + i.val.2 = n := i.property
  have hj' : j.val.1 + j.val.2 = n := j.property
  dsimp at hij
  omega

theorem tensorCochainBicomplex_finite
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    FiniteDiagonals (tensorCochainBicomplex C D) := by
  apply finiteDiagonals_of_upperQuadrant _ 0 0
  intro p q hpq
  have hpq' : -p < 0 ∨ -q < 0 := by omega
  change IsZero (((tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)).X (-p)).X (-q))
  letI := P103.Ch11.TorBalance.ordinary_tensor_supported C D (-p) (-q) hpq'
  exact ModuleCat.isZero_of_subsingleton _


section RegradingReuse

open DoubleTotalization FiniteDiagonalFiltrations

abbrev negChainEmbedding := AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.negEmbedding

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ))

theorem chainToCochainBicomplex_eq : chainToCochainBicomplex K = AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.cochainBicomplex K := rfl

variable [K.HasTotal (ComplexShape.down ℤ)]
variable [(chainToCochainBicomplex K).HasTotal (ComplexShape.up ℤ)]

abbrev reverseTotalMap :
    (chainToCochainBicomplex K).total (ComplexShape.up ℤ) ⟶
      (K.total (ComplexShape.down ℤ)).restriction negChainEmbedding :=
  by
  letI : (AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.cochainBicomplex K).HasTotal (ComplexShape.up ℤ) := inferInstanceAs ((chainToCochainBicomplex K).HasTotal (ComplexShape.up ℤ))
  exact AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.regradeTotalMap K

abbrev reverseTotalTermMap (n : ℤ) :
    ((chainToCochainBicomplex K).total (ComplexShape.up ℤ)).X n ⟶
      (K.total (ComplexShape.down ℤ)).X (-n) :=
  (reverseTotalMap K).f n

@[reassoc (attr := simp)]
theorem reverseTotalTermMap_ι (p q n : ℤ) (h : p+q=n) :
    (chainToCochainBicomplex K).ιTotal (ComplexShape.up ℤ) p q n h ≫ reverseTotalTermMap K n =
      K.ιTotal (ComplexShape.down ℤ) (-p) (-q) (-n) (by change -p + -q = -n; omega) :=
  by
  letI : (AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.cochainBicomplex K).HasTotal (ComplexShape.up ℤ) := inferInstanceAs ((chainToCochainBicomplex K).HasTotal (ComplexShape.up ℤ))
  exact AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.injection_regradeTotalComponent K p q n h

abbrev reverseTotalIso :
    (chainToCochainBicomplex K).total (ComplexShape.up ℤ) ≅
      (K.total (ComplexShape.down ℤ)).restriction negChainEmbedding :=
  by
  letI : (AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.cochainBicomplex K).HasTotal (ComplexShape.up ℤ) := inferInstanceAs ((chainToCochainBicomplex K).HasTotal (ComplexShape.up ℤ))
  exact asIso (AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.regradeTotalMap K)

abbrev reverseTotalTermIso (n : ℤ) :
    ((chainToCochainBicomplex K).total (ComplexShape.up ℤ)).X n ≅
      (K.total (ComplexShape.down ℤ)).X (-n) :=
  HomologicalComplex.Hom.isoApp (reverseTotalIso K) n

abbrev negScNatIsoE2 (n : ℤ) :
    negChainEmbedding.restrictionFunctor A ⋙
      HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n ≅
    HomologicalComplex.shortComplexFunctor A (ComplexShape.down ℤ) (-n) :=
  AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.negScNatIso n

variable {K}
variable {L : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ)}


variable [L.HasTotal (ComplexShape.down ℤ)]
variable [(chainToCochainBicomplex L).HasTotal (ComplexShape.up ℤ)]

/-- Upstream theorem has the other orientation. -/
theorem reverseTotalIso_natural (f : K ⟶ L) :
    HomologicalComplex₂.total.map (chainToCochainBicomplexMap f) (ComplexShape.up ℤ) ≫
      (reverseTotalIso L).hom =
      (reverseTotalIso K).hom ≫ HomologicalComplex.restrictionMap
        (HomologicalComplex₂.total.map f (ComplexShape.down ℤ)) negChainEmbedding :=
  by
  letI : (AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.cochainBicomplex K).HasTotal (ComplexShape.up ℤ) := inferInstanceAs ((chainToCochainBicomplex K).HasTotal (ComplexShape.up ℤ))
  letI : (AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.cochainBicomplex L).HasTotal (ComplexShape.up ℤ) := inferInstanceAs ((chainToCochainBicomplex L).HasTotal (ComplexShape.up ℤ))
  exact (AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison.regradeTotalMap_naturality K L f).symm


/-- The accepted short-complex regrading gives canonical homology regrading. -/
abbrev negativeRestrictionHomologyNatIso (n : ℤ) :
    negChainEmbedding.restrictionFunctor A ⋙
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n ≅
    HomologicalComplex.homologyFunctor A (ComplexShape.down ℤ) (-n) :=
  Functor.isoWhiskerRight (negScNatIsoE2 (A := A) n) (ShortComplex.homologyFunctor A)

abbrev negativeRestrictionHomologyIso (C : ChainComplex A ℤ) (n : ℤ) :
    (C.restriction negChainEmbedding).homology n ≅ C.homology (-n) :=
  (negativeRestrictionHomologyNatIso n).app C

theorem negativeRestrictionHomologyIso_natural (C D : ChainComplex A ℤ) (f : C ⟶ D) (n : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f negChainEmbedding) n ≫
      (negativeRestrictionHomologyIso D n).hom =
      (negativeRestrictionHomologyIso C n).hom ≫ HomologicalComplex.homologyMap f (-n) :=
  (negativeRestrictionHomologyNatIso (A := A) n).hom.naturality f

/-- Reuse total regrading and short-complex regrading together. -/
abbrev reverseTotalHomologyIso (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ))
    [K.HasTotal (ComplexShape.down ℤ)]
    [(chainToCochainBicomplex K).HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    ((chainToCochainBicomplex K).total (ComplexShape.up ℤ)).homology n ≅
      (K.total (ComplexShape.down ℤ)).homology (-n) :=
  (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).mapIso (reverseTotalIso K) ≪≫
    negativeRestrictionHomologyIso (K.total (ComplexShape.down ℤ)) n


end RegradingReuse


theorem tensor_total_exists : Specs.TensorTotalExists.{u,w,x} := by
  intro R _ C Q
  exact (FiniteDiagonalFiltrations.totalizationsExist _
    (tensorCochainBicomplex_finite C Q)).1

/-- Actual quotient pages, their next-page homology isomorphisms, and finite
convergence for the prescribed row filtration of the original double complex. -/
theorem tensor_pages : Specs.TensorPages.{u,w,x} := by
  intro R _ C Q _
  let K := tensorCochainBicomplex C Q
  have hK := tensorCochainBicomplex_finite C Q
  obtain ⟨Fc,Fr,hc,hr,_,_⟩ := FiniteDiagonalFiltrations.filtrations K hK
  let D := FilteredPage.pageData Fr
  exact ⟨⟨Fr,hr,D,PageCohomology.data Fr D,
    (DoubleComplexFirstPages.system _).row K hK Fr hr D,
    (DoubleComplexConvergence.double_complex_convergence K hK Fc Fr hc hr).2⟩⟩

end SpectralAssembly

section HomologicalIndexingLaws
open CategoryTheory.Limits
variable {V : Type a} [Category.{b} V] [Abelian V]
variable {T : CochainComplex V ℤ} (F : Filtration T) (D : F03Specs.PageData F)
theorem chainDifferential_eq (r : ℤ) (hr : 0 ≤ r) (p n p' n' : ℤ)
    (hp : p-r=p') (hn : n-1=n') :
    chainDifferential F D r hr p n ≫ eqToHom (by rw [hp,hn]) =
      D.differential r hr (-p) (-n) ≫ eqToHom (by congr 1 <;> omega) := by
  simp [chainDifferential]

theorem chainDifferential_square_zero (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    chainDifferential F D r hr p n ≫
      chainDifferential F D r hr (p-r) (n-1) = 0 := by
  have he : ((-p+r, -n+1) : ℤ × ℤ) = (-(p-r), -(n-1)) := by
    apply Prod.ext <;> dsimp <;> omega
  have hd := eqToHom_naturality (fun k : ℤ × ℤ => D.differential r hr k.1 k.2) he
  dsimp only at hd
  dsimp only [chainDifferential]
  simp only [Category.assoc]
  erw [← Category.assoc (eqToHom _) (D.differential r hr (-(p-r)) (-(n-1))) (eqToHom _),
    ← hd]
  simp only [← Category.assoc]
  erw [D.square_zero, zero_comp, zero_comp]


/-- Negating total and filtration degrees gives the page-homology law in
homological indexing. -/
def chainPageNextIso (H : PageCohomology.Data F D)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    chainPage F D (r+1) p n ≅ (chainPageShortComplex F D r hr p n).homology :=
  eqToIso (congrArg₂ (PageCohomology.object F D (r+1))
    (by omega : -p = -p-r+r) (by omega : -n = -n-1+1)) ≪≫
      H.nextIso r hr (-p-r) (-n-1)

theorem chainTargetPiece_increasing (p n : ℤ) :
    chainTargetPiece F (p-1) n ≤ chainTargetPiece F p n := by
  have hp : -(p-1) = -p+1 := by omega
  change FiniteFiltrationConvergence.cohomologyPiece F (-(p-1)) (-n) ≤ _
  rw [hp]
  exact FiniteFiltrationConvergence.cohomologyPiece_decreasing F (-p) (-n)

/-- Finite lower and upper effective indices are retained on homology. -/
theorem chainTargetPiece_finite
    (h : DoubleComplexConvergence.Converges F) (n : ℤ) :
    ∃ a b : ℤ,
      (∀ p, p ≤ a → chainTargetPiece F p n = ⊥) ∧
      (∀ p, b ≤ p → chainTargetPiece F p n = ⊤) := by
  obtain ⟨a,b,ha,hb⟩ := h.target.finite (-n)
  exact ⟨-b,-a,fun p hp => hb (-p) (by omega),fun p hp => ha (-p) (by omega)⟩

/-- Each stable chain page is the corresponding target filtration quotient. -/
def chainPageLimitIso (h : DoubleComplexConvergence.Converges F)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (hs : FiniteFiltrationConvergence.Stabilized F r (-p) (-n)) :
    chainPage F D r p n ≅ FiniteFiltrationConvergence.gradedCohomology F (-p) (-n) :=
  (h.limit D r (-p) (-n) hr hs).some.iso


end HomologicalIndexingLaws

section PageSupport
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Category CategoryTheory.Limits
open DoubleTotalization FiniteDiagonalFiltrations DoubleComplexFirstPages
/-- Every filtered page is a subquotient of its graded term. -/
theorem page_isZero_of_graded {A : Type u} [Category.{v} A] [Abelian A]
    {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)
    (r p n : ℤ) (h : IsZero ((F.graded p).X n)) :
    IsZero (PageCohomology.object F D r p n) := by
  have hz : IsZero (FilteredPage.cycles F r p n : A) :=
    IsZero.of_mono (FilteredPage.cycles F r p n).arrow h
  exact IsZero.of_epi (cokernel.π (Subobject.ofLE _ _ (D.containment r p n))) hz

/-- A formula filtration is all of a total term when its threshold contains
all nonzero diagonal summands. -/
theorem formula_piece_eq_top {A : Type u} [Category.{v} A] [Abelian A]
    (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
    (axis : ℤ × ℤ → ℤ) (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K axis F) (a n : ℤ)
    (ha : ∀ p q (h : p+q=n), ¬ IsZero ((K.X p).X q) → a ≤ axis (p,q)) :
    F.piece a n = ⊤ := by
  classical
  let r : (sumTotal K).X n ⟶ (F.piece a n : A) := K.totalDesc (fun p q h =>
    if hpa : a ≤ axis (p,q) then summandToStep K axis F hF a p q n h hpa else 0)
  have hr : r ≫ (F.piece a n).arrow = 𝟙 _ := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc, Category.comp_id]
    by_cases hpa : a ≤ axis (p,q)
    · rw [dite_eq_left hpa, summandToStep_arrow]
    · rw [dite_eq_right hpa, zero_comp]
      apply (show IsZero ((K.X p).X q) from by by_contra hz; exact hpa (ha p q hpq hz)).eq_of_src
  have : Epi (F.piece a n).arrow := epi_of_epi_fac hr
  have : IsIso (F.piece a n).arrow := isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow _

/-- A formula filtration vanishes when all its selected summands vanish. -/
theorem formula_piece_eq_bot {A : Type u} [Category.{v} A] [Abelian A]
    (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
    (axis : ℤ × ℤ → ℤ) (F : Filtration (sumTotal K))
    (hF : HasFiltrationFormula K axis F) (a n : ℤ)
    (ha : ∀ p q (h : p+q=n), a ≤ axis (p,q) → IsZero ((K.X p).X q)) :
    F.piece a n = ⊥ := by
  obtain ⟨b,hb,ι,hι,eι,hbi⟩ := hF a n
  rw [← eι]
  apply Subobject.mk_eq_bot_iff_zero.mpr
  apply hb.isColimit.hom_ext
  rintro ⟨i⟩
  exact (ha i.val.val.1 i.val.val.2 i.val.property i.property).eq_of_src _ _

variable {R : Type u} [Ring R]
open P103.Specs.Ch10.Complexes P103.Specs.Ch11.TorBalance

/-- Reversed ordinary tensor bicomplexes vanish in either positive cochain index. -/
theorem tensorCochainBicomplex_upper
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (Q : ChainComplex (ModuleCat.{x} R) ℕ) (p q : ℤ) (h : 0 < p ∨ 0 < q) :
    IsZero (((tensorCochainBicomplex C Q).X p).X q) := by
  change IsZero (((tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain Q)).X (-p)).X (-q))
  have hs := P103.Ch11.TorBalance.ordinary_tensor_supported C Q (-p) (-q) (by omega)
  letI := hs
  exact ModuleCat.isZero_of_subsingleton _

namespace TensorPagesData
variable {C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ}
    {Q : ChainComplex (ModuleCat.{x} R) ℕ}
    [(tensorCochainBicomplex C Q).HasTotal (ComplexShape.up ℤ)]
    (T : TensorPagesData C Q)

/-- Every page vanishes outside the first chain quadrant, including E0. -/
theorem firstQuadrant (r p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero (DoubleComplexFirstPages.page T.filtration T.pages r (-p) (-q)) := by
  apply page_isZero_of_graded
  apply (T.firstPages.gradedIso (-p) (-q)).isZero_iff.mpr
  exact tensorCochainBicomplex_upper C Q (-q) (-p) (by omega)

/-- The same vanishing statement in filtration/total chain coordinates. -/
theorem chainFirstQuadrant (r p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero (PageCohomology.object T.filtration T.pages r (-p) (-(p+q))) := by
  let e : PageCohomology.object T.filtration T.pages r (-p) (-(p+q)) ≅
      DoubleComplexFirstPages.page T.filtration T.pages r (-p) (-q) :=
    eqToIso (by congr 1; omega)
  exact e.isZero_iff.mpr (T.firstQuadrant r p q h)

/-- The row filtration in chain degree n contains all terms at p=n. -/
theorem piece_top (n : ℤ) : T.filtration.piece n n = ⊤ := by
  apply formula_piece_eq_top _ Prod.snd _ T.formula
  intro p q hpq hz
  have hp : p ≤ 0 := by
    by_contra hp
    exact hz (tensorCochainBicomplex_upper C Q p q (Or.inl (by omega)))
  dsimp
  omega

/-- The row filtration has no terms at positive cochain filtration index. -/
theorem piece_bot (a n : ℤ) (ha : 0 < a) : T.filtration.piece a n = ⊥ := by
  apply formula_piece_eq_bot _ Prod.snd _ T.formula
  intro p q hpq haq
  exact tensorCochainBicomplex_upper C Q p q (Or.inr (by dsimp at haq; omega))

/-- The induced finite filtration of the target has F_n=H_n. -/
theorem target_top (n : ℤ) :
    FiniteFiltrationConvergence.cohomologyPiece T.filtration n n = ⊤ :=
  FiniteFiltrationConvergence.cohomologyPiece_eq_top T.filtration n n (T.piece_top n)

/-- The induced finite filtration of the target has F_{-1}=0 after reversal. -/
theorem target_bot (n : ℤ) :
    FiniteFiltrationConvergence.cohomologyPiece T.filtration 1 n = ⊥ :=
  FiniteFiltrationConvergence.cohomologyPiece_eq_bot T.filtration 1 n (T.piece_bot 1 n (by omega))
end TensorPagesData

end PageSupport
section E2Bridge
set_option maxHeartbeats 1500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch11.TorBalance P103.Ch11.TorBalance
open FiniteDiagonalFiltrations DoubleComplexFirstPages
@[simp] theorem negChainEmbedding_f (n : ℤ) : negChainEmbedding.f n = -n := rfl
section Generic
variable {T : Type u} [Ring T] {U : Type x} [Ring U]
variable (C : ChainComplex (ModuleCat.{v} T) ℕ)
variable (F : ModuleCat.{v} T ⥤ ModuleCat.{w} U) [F.Additive]

theorem mappedExtend_support : SupportedIn
    ((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj (extendNonnegativeChain C)) (Set.Ici 0) := by
  intro n hn
  exact ModuleCat.isZero_iff_subsingleton.mp (F.map_isZero
    (ModuleCat.isZero_iff_subsingleton.mpr
      (P103.Ch10.Complexes.extendNonnegativeChain_supported C n hn)))

def mappedExtendHomologyIso (p : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj
      (extendNonnegativeChain C)).homology (p : ℤ) ≅
    ModuleCat.of U (Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) p) :=
  (explicitToCategoricalHomologyIso _ (p : ℤ)).symm ≪≫
    (restrictionHomologyEquiv _ (mappedExtend_support C F) p).symm.toModuleIso ≪≫
    (P103.Specs.Ch10.Comparison.quotientHomology (ComplexShape.down ℕ) p).mapIso
      (restrictExtendMapIso C F)

variable {F} {G : ModuleCat.{v} T ⥤ ModuleCat.{w} U} [G.Additive] (τ : F ⟶ G)

theorem restrictExtendMapIso_naturality :
    HomologicalComplex.restrictionMap
      ((τ.mapHomologicalComplex (ComplexShape.down ℤ)).app (extendNonnegativeChain C))
      nonnegativeChainEmbedding ≫ (restrictExtendMapIso C G).hom =
    (restrictExtendMapIso C F).hom ≫ (τ.mapHomologicalComplex (ComplexShape.down ℕ)).app C := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (τ.naturality (C.extendXIso nonnegativeChainEmbedding (i := n) rfl).hom).symm

theorem mappedExtendHomologyIso_naturality (p : ℕ) :
    HomologicalComplex.homologyMap
      ((τ.mapHomologicalComplex (ComplexShape.down ℤ)).app (extendNonnegativeChain C)) (p : ℤ) ≫
      (mappedExtendHomologyIso C G p).hom =
    (mappedExtendHomologyIso C F p).hom ≫ ModuleCat.ofHom
      (homologyMap ((τ.mapHomologicalComplex (ComplexShape.down ℕ)).app C) p) := by
  let E := (F.mapHomologicalComplex (ComplexShape.down ℤ)).obj (extendNonnegativeChain C)
  let E' := (G.mapHomologicalComplex (ComplexShape.down ℤ)).obj (extendNonnegativeChain C)
  let l := (τ.mapHomologicalComplex (ComplexShape.down ℤ)).app (extendNonnegativeChain C)
  let lN := HomologicalComplex.restrictionMap l nonnegativeChainEmbedding
  let HZ := P103.Specs.Ch10.Comparison.quotientHomology (S := U) (ComplexShape.down ℤ) (p : ℤ)
  let HN := P103.Specs.Ch10.Comparison.quotientHomology (S := U) (ComplexShape.down ℕ) p
  let a := explicitToCategoricalHomologyIso E (p : ℤ)
  let a' := explicitToCategoricalHomologyIso E' (p : ℤ)
  let b := (restrictionHomologyEquiv E (mappedExtend_support C F) p).toModuleIso
  let b' := (restrictionHomologyEquiv E' (mappedExtend_support C G) p).toModuleIso
  let d := HN.mapIso (restrictExtendMapIso C F)
  let d' := HN.mapIso (restrictExtendMapIso C G)
  have ha : HomologicalComplex.homologyMap l (p : ℤ) ≫ a'.inv = a.inv ≫ HZ.map l := by
    apply (cancel_mono a'.hom).mp
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      explicitToCategoricalHomologyIso_naturality, Iso.inv_hom_id_assoc]
  have hbb : HN.map lN ≫ b'.hom = b.hom ≫ HZ.map l := by
    exact congrArg ModuleCat.ofHom
      (restrictionHomologyEquiv_natural (mappedExtend_support C F) (mappedExtend_support C G) l p)
  have hb : HZ.map l ≫ b'.inv = b.inv ≫ HN.map lN := by
    apply (cancel_mono b'.hom).mp
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hbb,
      Iso.inv_hom_id_assoc]
  have hd : HN.map lN ≫ d'.hom = d.hom ≫
      HN.map ((τ.mapHomologicalComplex (ComplexShape.down ℕ)).app C) := by
    change HN.map lN ≫ HN.map _ = HN.map _ ≫ HN.map _
    rw [← HN.map_comp, ← HN.map_comp, restrictExtendMapIso_naturality]
  change HomologicalComplex.homologyMap l (p : ℤ) ≫ a'.inv ≫ b'.inv ≫ d'.hom =
    a.inv ≫ b.inv ≫ d.hom ≫ HN.map ((τ.mapHomologicalComplex (ComplexShape.down ℕ)).app C)
  rw [← Category.assoc _ a'.inv, ha, Category.assoc, ← Category.assoc _ b'.inv,
    hb, Category.assoc, hd]
end Generic


section TensorComparison
variable {R : Type u} [Ring R]

def tensorCoefficientComplexInt (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) :
    ModuleCat.{w} R ⥤ ChainComplex (ModuleCat.{max v w} ℤ) ℤ where
  obj N := ((tensorFunctor N).mapHomologicalComplex (ComplexShape.down ℤ)).obj C
  map g := ((TorBalance.tensorCoefficientMap g.hom).mapHomologicalComplex (ComplexShape.down ℤ)).app C
  map_id _ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  map_comp _ _ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl

instance tensorCoefficientComplexInt_additive
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) :
    (tensorCoefficientComplexInt C : ModuleCat.{w} R ⥤ _).Additive where
  map_add := by
    intro M N g h
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    exact P103.BalancedTensor.tmul_add _ _ _

abbrev ordinaryHorizontalHomologyFunctor (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ) (q : ℕ) :=
  (tensorCoefficientComplex C : ModuleCat.{w} R ⥤ _) ⋙
    P103.Specs.Ch10.Comparison.quotientHomology (ComplexShape.down ℕ) q

abbrev extendedHorizontalHomologyFunctor (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ) (q : ℕ) :=
  (tensorCoefficientComplexInt (extendNonnegativeChain C) : ModuleCat.{w} R ⥤ _) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q : ℤ)

def extendedHorizontalHomologyNatIso
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ) (q : ℕ) :
    (extendedHorizontalHomologyFunctor C q : ModuleCat.{w} R ⥤ _) ≅ ordinaryHorizontalHomologyFunctor C q :=
  NatIso.ofComponents (fun N => mappedExtendHomologyIso C (tensorFunctor N) q)
    (fun {_ _} g => mappedExtendHomologyIso_naturality C (TorBalance.tensorCoefficientMap g.hom) q)

def extendedHorizontalHomologyComplexIso
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) :
    ((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q : ℤ)).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj
        (P103.Specs.Ch11.TorBalance.tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)).flip ≅
    ((ordinaryHorizontalHomologyFunctor C q).mapHomologicalComplex (ComplexShape.down ℤ)).obj
      (extendNonnegativeChain D) :=
  (Functor.mapHomologicalComplexCompIso (extendedHorizontalHomologyNatIso C q) (ComplexShape.down ℤ)).app
    (extendNonnegativeChain D)
end TensorComparison

section Reverse
variable {A : Type u} [Category.{v} A] [Abelian A]

def reverseHomologyNatIsoE2 (q : ℤ) :
    negChainEmbedding.restrictionFunctor A ⋙
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (-q) ≅
    HomologicalComplex.homologyFunctor A (ComplexShape.down ℤ) q :=
  Functor.isoWhiskerRight (negScNatIsoE2 (-q)) (ShortComplex.homologyFunctor A) ≪≫
    eqToIso (by simp only [neg_neg]; rfl)
end Reverse

section E2
variable {R : Type u} [Ring R]

def reversedHorizontalHomologyIso
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) :
    verticalHomology (chainToCochainBicomplex
      (P103.Specs.Ch11.TorBalance.tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D))).flip (-(q : ℤ)) ≅
    (((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q : ℤ)).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj
        (P103.Specs.Ch11.TorBalance.tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)).flip).restriction
          negChainEmbedding :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (reverseHomologyNatIsoE2 (q : ℤ)).app
      ((P103.Specs.Ch11.TorBalance.tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)).flip.X (-i))) (by
      intro i j hij
      exact ((reverseHomologyNatIsoE2 (q : ℤ)).hom.naturality
        ((P103.Specs.Ch11.TorBalance.tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)).flip.d (-i) (-j))).symm)

def tensorCochainE2Iso
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q : ℕ) :
    (verticalHomology (chainToCochainBicomplex
      (P103.Specs.Ch11.TorBalance.tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D))).flip (-(q : ℤ))).homology (-(p : ℤ)) ≅
    ModuleCat.of ℤ (Homology
      (((ordinaryHorizontalHomologyFunctor C q).mapHomologicalComplex (ComplexShape.down ℕ)).obj D) p) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso
    (reversedHorizontalHomologyIso C D q) ≪≫
  (reverseHomologyNatIsoE2 (p : ℤ)).app _ ≪≫
  (HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (p : ℤ)).mapIso
    (extendedHorizontalHomologyComplexIso C D q) ≪≫
  mappedExtendHomologyIso D (ordinaryHorizontalHomologyFunctor C q) p

end E2


end E2Bridge
section ReverseMaps
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Category CategoryTheory.Limits
section ReverseNaturality
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L M : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ)}

/-- Simultaneous integer reversal applied to a map of commuting bicomplexes. -/
@[simp]
theorem chainToCochainBicomplexMap_id (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ)) :
    chainToCochainBicomplexMap (𝟙 K) = 𝟙 _ := by
  ext p q
  rfl

@[simp]
theorem chainToCochainBicomplexMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    chainToCochainBicomplexMap (f ≫ g) = chainToCochainBicomplexMap f ≫ chainToCochainBicomplexMap g := by
  ext p q
  rfl

variable [K.HasTotal (ComplexShape.down ℤ)] [L.HasTotal (ComplexShape.down ℤ)]
variable [(chainToCochainBicomplex K).HasTotal (ComplexShape.up ℤ)]
variable [(chainToCochainBicomplex L).HasTotal (ComplexShape.up ℤ)]

end ReverseNaturality

end ReverseMaps


section TotalNaturality
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Category CategoryTheory.Limits


section TotalHomologyNaturality
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ)}
variable [K.HasTotal (ComplexShape.down ℤ)] [L.HasTotal (ComplexShape.down ℤ)]
variable [(chainToCochainBicomplex K).HasTotal (ComplexShape.up ℤ)]
variable [(chainToCochainBicomplex L).HasTotal (ComplexShape.up ℤ)]

/-- The canonical total homology comparison is natural, with both gradings explicit. -/
theorem reverseTotalHomologyIso_natural (f : K ⟶ L) (n : ℤ) :
    HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (chainToCochainBicomplexMap f) (ComplexShape.up ℤ)) n ≫
        (reverseTotalHomologyIso L n).hom =
      (reverseTotalHomologyIso K n).hom ≫
        HomologicalComplex.homologyMap (HomologicalComplex₂.total.map f (ComplexShape.down ℤ)) (-n) := by
  have he := congrArg (fun z => HomologicalComplex.homologyMap z n) (reverseTotalIso_natural f)
  simp only [HomologicalComplex.homologyMap_comp] at he
  change _ ≫ (HomologicalComplex.homologyMap (reverseTotalIso L).hom n ≫
    (negativeRestrictionHomologyIso (L.total (ComplexShape.down ℤ)) n).hom) =
    (HomologicalComplex.homologyMap (reverseTotalIso K).hom n ≫
      (negativeRestrictionHomologyIso (K.total (ComplexShape.down ℤ)) n).hom) ≫ _
  rw [← Category.assoc, he, Category.assoc,
    negativeRestrictionHomologyIso_natural (K.total (ComplexShape.down ℤ))
      (L.total (ComplexShape.down ℤ)) (HomologicalComplex₂.total.map f (ComplexShape.down ℤ)) n,
    ← Category.assoc]
end TotalHomologyNaturality

end TotalNaturality

section TensorLiftMaps
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Category CategoryTheory.Limits
section TensorMaps
open P103.Specs.Ch10.Complexes P103.Specs.Ch11.TorBalance
variable {R : Type u} [Ring R]
variable {C C' C'' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
variable {Q Q' Q'' : ChainComplex (ModuleCat.{w} R) ℕ}


@[simp]
theorem tensorCochainBicomplexMap_id :
    tensorCochainBicomplexMap (𝟙 C) (𝟙 Q) = 𝟙 _ := by
  dsimp only [tensorCochainBicomplexMap]
  simp only [HomologicalComplex.extendMap_id]
  erw [P103.Ch11.TorBalance.tensorBicomplexMap_id, chainToCochainBicomplexMap_id]

@[simp]
theorem tensorCochainBicomplexMap_comp (l : C ⟶ C') (l' : C' ⟶ C'')
    (m : Q ⟶ Q') (m' : Q' ⟶ Q'') :
    tensorCochainBicomplexMap (l ≫ l') (m ≫ m') =
      tensorCochainBicomplexMap l m ≫ tensorCochainBicomplexMap l' m' := by
  simp [tensorCochainBicomplexMap, P103.Ch11.TorBalance.tensorBicomplexMap_comp]

/-- Every pair of lifted chain maps induces an actual filtered map of totals. -/
theorem tensorCochainBicomplex_filteredMap
    [(tensorCochainBicomplex C Q).HasTotal (ComplexShape.up ℤ)]
    [(tensorCochainBicomplex C' Q').HasTotal (ComplexShape.up ℤ)]
    (F : Filtration (DoubleTotalization.sumTotal (tensorCochainBicomplex C Q)))
    (G : Filtration (DoubleTotalization.sumTotal (tensorCochainBicomplex C' Q')))
    (hF : FiniteDiagonalFiltrations.HasFiltrationFormula (tensorCochainBicomplex C Q) Prod.snd F)
    (hG : FiniteDiagonalFiltrations.HasFiltrationFormula (tensorCochainBicomplex C' Q') Prod.snd G)
    (l : C ⟶ C') (m : Q ⟶ Q') :
    ∃ g : FilteredMap ⟨_,F⟩ ⟨_,G⟩,
      g.hom = HomologicalComplex₂.total.map (tensorCochainBicomplexMap l m) (ComplexShape.up ℤ) :=
  FiniteDiagonalFiltrations.formula_filteredMap _ _ Prod.snd F G hF hG (tensorCochainBicomplexMap l m)
end TensorMaps

end TensorLiftMaps

section PageMapEquality
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Category CategoryTheory.Limits

open FilteredPageFunctoriality
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {X Y : FilteredComplex A} {f g : FilteredMap X Y}
variable {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
variable (M : MapData f D E) (N : MapData g D E)
variable (C : PageCohomology.Data X.filtration D) (C' : PageCohomology.Data Y.filtration E)

include C C'

/-- Equality of all maps on one page propagates through its page homology. -/
theorem pageMap_eq_succ_center (r : ℤ) (hr : 0 ≤ r)
    (h : ∀ p n, M.map r p n = N.map r p n) (p n : ℤ) :
    M.map (r+1) (p+r) (n+1) = N.map (r+1) (p+r) (n+1) := by
  have hs : shortComplexMap M r hr p n = shortComplexMap N r hr p n := by
    ext <;> apply h
  apply (cancel_mono (C'.nextIso r hr p n).hom).1
  rw [next_naturality M C C', next_naturality N C C', hs]

/-- In particular, independence on E2 suffices for independence on every later page. -/
theorem pageMap_eq_of_page (r : ℤ) (hr : 0 ≤ r)
    (h : ∀ p n, M.map r p n = N.map r p n) (s : ℤ) (hs : r ≤ s) :
    ∀ p n, M.map s p n = N.map s p n := by
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hs
  clear hs
  induction k with
  | zero =>
    rw [Int.natCast_zero, add_zero]
    exact h
  | succ k ih =>
    intro p n
    have hk : 0 ≤ r + (k : ℤ) := by omega
    have hh := pageMap_eq_succ_center M N C C' (r+(k:ℤ)) hk ih (p-(r+(k:ℤ))) (n-1)
    rw [sub_add_cancel, sub_add_cancel] at hh
    rw [show r + (↑(k+1) : ℤ) = r + (k : ℤ) + 1 by omega]
    exact hh

end PageMapEquality

section HorizontalRightMaps
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Category CategoryTheory.Limits

open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)

/-- Maps in the two tensor variables commute as chain maps. -/
theorem tensorFirstMap_tensorSecondMap
    {C D : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ} (l : C ⟶ D)
    {N N' : Type x} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') :
    tensorFirstMap l N ≫ tensorSecondMap D g =
      tensorSecondMap C g ≫ tensorFirstMap l N' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

/-- The map in the right-resolution variable on the entire horizontal
homology complex, with the original coefficient differentials. -/
def rowHomologyMap
    {C D : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ} (l : C ⟶ D)
    (Q : ChainComplex (ModuleCat.{max v x} S) ℕ) (q : ℕ) :
    rowHomologyComplex f C Q q ⟶ rowHomologyComplex f D Q q where
  f p := ModuleCat.ofHom (homologyMap (tensorFirstMap l (Restricted f (Q.X p))) q)
  comm' p p' _ := by
    let H := P103.Specs.Ch10.Comparison.quotientHomology (S := ℤ) (ComplexShape.down ℕ) q
    change H.map (tensorFirstMap l (Restricted f (Q.X p))) ≫
      H.map (tensorSecondMap D (Restricted.map f (Q.d p p').hom)) =
      H.map (tensorSecondMap C (Restricted.map f (Q.d p p').hom)) ≫
        H.map (tensorFirstMap l (Restricted f (Q.X p')))
    rw [← H.map_comp, ← H.map_comp, tensorFirstMap_tensorSecondMap]

/-- In the right variable, any two lifts of the same module map already
induce exactly the same map on the horizontal homology complex. -/
theorem rowHomologyMap_lift_independent
    (A B : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup B] [Module Rᵐᵒᵖ B]
    (P : LeftResolution Rᵐᵒᵖ A) (P' : LeftResolution Rᵐᵒᵖ B) (hP : P.IsProjective)
    (a : A →ₗ[Rᵐᵒᵖ] B) (l l' : P.complex ⟶ P'.complex)
    (hl : ChainLift P P' a l) (hl' : ChainLift P P' a l')
    (Q : ChainComplex (ModuleCat.{max v x} S) ℕ) (q : ℕ) :
    rowHomologyMap.{u,v,max u w,x} f (C := P.complex) (D := P'.complex) l Q q =
      rowHomologyMap.{u,v,max u w,x} f (C := P.complex) (D := P'.complex) l' Q q := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  exact congrArg ModuleCat.Hom.hom
    (P103.Ch10.Comparison.chain_homology_independent Rᵐᵒᵖ ℤ
      (tensorFunctor (Restricted f (Q.X p))) A B P P' hP a l l' q hl hl')



end HorizontalRightMaps

section TargetGraded
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Category CategoryTheory.Limits

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

section SubobjectQuotients
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : C}

/-- The mapped subobject has the original underlying object transported along the ambient iso. -/
def mappedSubobjectIso (e : X ≅ Y) (S : Subobject X) :
    (S : C) ≅ (Subobject.mapIsoToOrderIso e S : C) := by
  apply Subobject.isoOfMkEq (S.arrow ≫ e.hom) (Subobject.mapIsoToOrderIso e S)
  change Subobject.mk (S.arrow ≫ e.hom) = (Subobject.map e.hom).obj S
  conv_rhs => rw [← Subobject.mk_arrow S]
  rfl

@[reassoc (attr := simp)]
theorem mappedSubobjectIso_hom_arrow (e : X ≅ Y) (S : Subobject X) :
    (mappedSubobjectIso e S).hom ≫ (Subobject.mapIsoToOrderIso e S).arrow = S.arrow ≫ e.hom := by
  apply Subobject.ofMkLE_arrow

/-- Inclusions of nested subobjects commute with ambient isomorphism transport. -/
theorem mappedSubobjectIso_ofLE (e : X ≅ Y) (S T : Subobject X) (h : S ≤ T) :
    Subobject.ofLE S T h ≫ (mappedSubobjectIso e T).hom =
      (mappedSubobjectIso e S).hom ≫
        Subobject.ofLE (Subobject.mapIsoToOrderIso e S) (Subobject.mapIsoToOrderIso e T)
          ((Subobject.mapIsoToOrderIso e).monotone h) := by
  apply (cancel_mono (Subobject.mapIsoToOrderIso e T).arrow).mp
  simp only [Category.assoc, mappedSubobjectIso_hom_arrow,
    Subobject.ofLE_arrow, Subobject.ofLE_arrow_assoc]

/-- An ambient isomorphism canonically transports each successive subobject quotient. -/
def mappedSubobjectCokernelIso (e : X ≅ Y) (S T : Subobject X) (h : S ≤ T) :
    cokernel (Subobject.ofLE S T h) ≅
      cokernel (Subobject.ofLE (Subobject.mapIsoToOrderIso e S) (Subobject.mapIsoToOrderIso e T)
        ((Subobject.mapIsoToOrderIso e).monotone h)) :=
  cokernel.mapIso _ _ (mappedSubobjectIso e S) (mappedSubobjectIso e T)
    (mappedSubobjectIso_ofLE e S T h)

end SubobjectQuotients
section TransportedLimit
open FiniteFiltrationConvergence
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ} (F : Filtration K) (D : F03Specs.PageData F)

/-- The stable pages identify the successive quotients of the filtration
transported along any specified target isomorphism. -/
def mappedChainPageLimitIso {H : C} (n : ℤ) (e : K.homology (-n) ≅ H)
    (h : DoubleComplexConvergence.Converges F)
    (r : ℤ) (hr : 0 ≤ r) (p : ℤ) (hs : Stabilized F r (-p) (-n)) :
    chainPage F D r p n ≅
      cokernel (Subobject.ofLE
        (Subobject.mapIsoToOrderIso e (chainTargetPiece F (p-1) n))
        (Subobject.mapIsoToOrderIso e (chainTargetPiece F p n))
        ((Subobject.mapIsoToOrderIso e).monotone (chainTargetPiece_increasing F p n))) := by
  refine chainPageLimitIso F D h r hr p n hs ≪≫ ?_ ≪≫
    mappedSubobjectCokernelIso e (chainTargetPiece F (p-1) n) (chainTargetPiece F p n)
      (chainTargetPiece_increasing F p n)
  let sIso : (cohomologyPiece F (-p+1) (-n) : C) ≅ (chainTargetPiece F (p-1) n : C) :=
    Subobject.isoOfEq _ _ (by dsimp only [chainTargetPiece]; congr 1 <;> omega)
  refine cokernel.mapIso _ _ sIso (Iso.refl _) ?_
  apply (cancel_mono (chainTargetPiece F p n).arrow).mp
  simp only [Iso.refl_hom, Category.comp_id, Category.assoc,
    sIso, Subobject.isoOfEq_hom, Subobject.ofLE_arrow]

end TransportedLimit


end TargetGraded


section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

instance negativeChainEmbedding_relIff : negativeChainEmbedding.IsRelIff where
  rel' i j h := by
    change -(i : ℤ) + 1 = -(j : ℤ) at h
    change j + 1 = i
    omega

theorem negativeChainEmbedding_outside (i : ℤ)
    (h : ∀ n, negativeChainEmbedding.f n ≠ i) : 0 < i := by
  by_contra! hi
  exact h (-i).toNat (by change -(((-i).toNat : ℕ) : ℤ) = i; omega)

section NegativeExtension
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Type u} [Category.{v} V] [Abelian V]
variable {K K' : CochainComplex V ℤ} {L L' : ChainComplex V ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- A map out of a cochain complex extends the map on the nonpositive degrees.
No differential enters these degrees from outside the image. -/
def negativeExtensionMap (a : K.restriction negativeChainEmbedding ⟶ L) :
    K ⟶ L.extend negativeChainEmbedding :=
  negativeChainEmbedding.liftExtend a (by
    intro j hj i hi
    exact False.elim (negativeChainEmbedding.not_boundaryGE_next
      (j := j + 1) (k := j) (by rfl) hj))

theorem negativeExtensionMap_f
    (a : K.restriction negativeChainEmbedding ⟶ L) (n : ℕ) :
    (negativeExtensionMap a).f (negativeChainEmbedding.f n) =
      a.f n ≫ (L.extendXIso negativeChainEmbedding (i := n) rfl).inv := by
  exact (negativeChainEmbedding.liftExtend_f a _ (i := n) rfl).trans (id_comp _)

/-- An isomorphism on the nonpositive degrees identifies a supported cochain
complex with the zero extension of its chain version. -/
def negativeExtensionIso (a : K.restriction negativeChainEmbedding ≅ L)
    (hK : ∀ n : ℤ, 0 < n → IsZero (K.X n)) :
    K ≅ L.extend negativeChainEmbedding := by
  let f := negativeExtensionMap a.hom
  haveI : ∀ n, IsIso (f.f n) := by
    intro n
    by_cases hn : ∃ i, negativeChainEmbedding.f i = n
    · obtain ⟨i, rfl⟩ := hn
      change IsIso (f.f (negativeChainEmbedding.f i))
      dsimp only [f]
      rw [negativeExtensionMap_f]
      haveI : IsIso (a.hom.f i) := (Hom.isoApp a i).isIso_hom
      infer_instance
    · have ho : ∀ i, negativeChainEmbedding.f i ≠ n := fun i hi => hn ⟨i, hi⟩
      exact ⟨⟨0, (hK _ (negativeChainEmbedding_outside n ho)).eq_of_src _ _,
        (L.isZero_extend_X negativeChainEmbedding n ho).eq_of_src _ _⟩⟩
  haveI := Hom.isIso_of_components f
  exact asIso f

theorem negativeExtensionIso_hom_f
    (a : K.restriction negativeChainEmbedding ≅ L)
    (hK : ∀ n : ℤ, 0 < n → IsZero (K.X n)) (n : ℕ) :
    (negativeExtensionIso a hK).hom.f (negativeChainEmbedding.f n) =
      a.hom.f n ≫ (L.extendXIso negativeChainEmbedding (i := n) rfl).inv :=
  negativeExtensionMap_f a.hom n

theorem negativeExtensionIso_inv_f
    (a : K.restriction negativeChainEmbedding ≅ L)
    (hK : ∀ n : ℤ, 0 < n → IsZero (K.X n)) (n : ℕ) :
    (negativeExtensionIso a hK).inv.f (negativeChainEmbedding.f n) =
      (L.extendXIso negativeChainEmbedding (i := n) rfl).hom ≫ a.inv.f n := by
  let e := Hom.isoApp (negativeExtensionIso a hK) (negativeChainEmbedding.f n)
  apply (cancel_mono e.hom).mp
  change e.inv ≫ e.hom = _
  rw [Iso.inv_hom_id]
  change _ = _ ≫ (negativeExtensionIso a hK).hom.f (negativeChainEmbedding.f n)
  rw [negativeExtensionIso_hom_f]
  have hi := (Hom.isoApp a n).inv_hom_id
  change a.inv.f n ≫ a.hom.f n = 𝟙 _ at hi
  simp only [Category.assoc, ← Category.assoc (a.inv.f n), hi, Category.id_comp, Iso.hom_inv_id]

theorem negativeExtensionIso_natural
    (a : K.restriction negativeChainEmbedding ≅ L)
    (a' : K'.restriction negativeChainEmbedding ≅ L')
    (hK : ∀ n : ℤ, 0 < n → IsZero (K.X n))
    (hK' : ∀ n : ℤ, 0 < n → IsZero (K'.X n))
    (g : K ⟶ K') (l : L ⟶ L')
    (hg : restrictionMap g negativeChainEmbedding ≫ a'.hom = a.hom ≫ l) :
    g ≫ (negativeExtensionIso a' hK').hom =
      (negativeExtensionIso a hK).hom ≫ extendMap l negativeChainEmbedding := by
  apply Hom.ext
  funext n
  by_cases hn : ∃ i, negativeChainEmbedding.f i = n
  · obtain ⟨i, rfl⟩ := hn
    change g.f (negativeChainEmbedding.f i) ≫ (negativeExtensionIso a' hK').hom.f (negativeChainEmbedding.f i) =
      (negativeExtensionIso a hK).hom.f (negativeChainEmbedding.f i) ≫
        (extendMap l negativeChainEmbedding).f (negativeChainEmbedding.f i)
    rw [negativeExtensionIso_hom_f, negativeExtensionIso_hom_f,
      extendMap_f l negativeChainEmbedding (i := i) rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun k : K.restriction negativeChainEmbedding ⟶ L' =>
      k.f i ≫ (L'.extendXIso negativeChainEmbedding (i := i) rfl).inv) hg
  · apply (hK _ (negativeChainEmbedding_outside n (fun i hi => hn ⟨i, hi⟩))).eq_of_src

end NegativeExtension

end

section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

section Representatives
set_option maxHeartbeats 600000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {B : Type u} [Ring B] {ι : Type x} {c : ComplexShape ι}
variable (K : HomologicalComplex (ModuleCat.{w} B) c) (n : ι)

private theorem quotientEquivOfEq_toModuleIso {X : ModuleCat.{w} B}
    (P Q : Submodule B X) (h : P = Q) :
    (Submodule.quotEquivOfEq P Q h).toModuleIso =
      eqToIso (congrArg (fun T : Submodule B X => ModuleCat.of B (X ⧸ T)) h) := by
  subst Q
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P z
  exact Submodule.quotEquivOfEq_mk P P rfl x

theorem quotientHomologyIso_eq_explicitToCategoricalHomologyIso_symm :
    quotientHomologyIso K n = (explicitToCategoricalHomologyIso K n).symm := by
  simp only [quotientHomologyIso, explicitToCategoricalHomologyIso, Iso.trans_symm,
    Iso.symm_symm_eq]
  have h := quotientEquivOfEq_toModuleIso (X := ModuleCat.of B (cycles K n))
    (cycleBoundaries K n) (K.sc n).moduleCatToCycles.range (cycleBoundaries_eq_range K n)
  erw [h]
  apply congrArg ((K.sc n).moduleCatHomologyIso ≪≫ ·)
  apply Iso.ext
  rfl

theorem explicitToCategoricalHomologyIso_apply_class (z : cycles K n) :
    (explicitToCategoricalHomologyIso K n).hom.hom (homologyClass K n z) =
      explicitClass K n z :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (explicitToCategoricalHomologyIso_class K n)) z

theorem quotientHomologyIso_apply_class (z : cycles K n) :
    (quotientHomologyIso K n).hom.hom (explicitClass K n z) = homologyClass K n z := by
  rw [quotientHomologyIso_eq_explicitToCategoricalHomologyIso_symm,
    ← explicitToCategoricalHomologyIso_apply_class]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (explicitToCategoricalHomologyIso K n).hom_inv_id) (homologyClass K n z)

theorem explicitCycle_iCycles (z : cycles K n) :
    (K.iCycles n).hom ((K.sc n).moduleCatCyclesIso.inv.hom z) = z.val :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (K.sc n).moduleCatCyclesIso_inv_iCycles) z

theorem explicitClass_eq_of_iCycles (a : K.cycles n) (z : cycles K n)
    (h : (K.iCycles n).hom a = z.val) :
    (K.homologyπ n).hom a = explicitClass K n z := by
  have ha : a = (K.sc n).moduleCatCyclesIso.inv.hom z :=
    (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
      (h.trans (explicitCycle_iCycles K n z).symm)
  rw [ha]
  rfl

theorem explicitClass_map {K' : HomologicalComplex (ModuleCat.{w} B) c}
    (g : K ⟶ K') (z : cycles K n) :
    (HomologicalComplex.homologyMap g n).hom (explicitClass K n z) =
      explicitClass K' n (P103.Specs.Ch10.Complexes.cyclesMap g n z) := by
  rw [← explicitToCategoricalHomologyIso_apply_class,
    ← explicitToCategoricalHomologyIso_apply_class]
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (explicitToCategoricalHomologyIso_naturality g n)) (homologyClass K n z)).symm

theorem quotientHomologyIso_natural {K' : HomologicalComplex (ModuleCat.{w} B) c}
    (g : K ⟶ K') :
    HomologicalComplex.homologyMap g n ≫ (quotientHomologyIso K' n).hom =
      (quotientHomologyIso K n).hom ≫ ModuleCat.ofHom (P103.Specs.Ch10.Complexes.homologyMap g n) := by
  rw [quotientHomologyIso_eq_explicitToCategoricalHomologyIso_symm,
    quotientHomologyIso_eq_explicitToCategoricalHomologyIso_symm]
  apply (cancel_mono (explicitToCategoricalHomologyIso K' n).hom).mp
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    explicitToCategoricalHomologyIso_naturality, Iso.inv_hom_id_assoc]

variable {ι' : Type*} {c' : ComplexShape ι'} (e : c.Embedding c') {n' : ι'} (hn : e.f n = n')

/-- A cycle in a zero extension represents the class of the corresponding
cycle in the original degree. -/
theorem explicitClass_extend_inv (z : cycles K n) :
    ∃ t : cycles (K.extend e) n',
      t.val = (K.extendXIso e hn).inv.hom z.val ∧
      (K.extendHomologyIso e hn).inv.hom (explicitClass K n z) =
        explicitClass (K.extend e) n' t := by
  let a := (K.sc n).moduleCatCyclesIso.inv.hom z
  let b := (K.extendCyclesIso e hn).inv.hom a
  let t : cycles (K.extend e) n' := ((K.extend e).sc n').moduleCatCyclesIso.hom.hom b
  have hb := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((K.extend e).sc n').moduleCatCyclesIso_hom_i) b
  change t.val = ((K.extend e).iCycles n').hom b at hb
  have hz' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (K.extendCyclesIso_inv_iCycles e hn)) a
  change ((K.extend e).iCycles n').hom b = (K.extendXIso e hn).inv.hom ((K.iCycles n).hom a) at hz'
  have hz : (K.iCycles n).hom a = z.val := explicitCycle_iCycles K n z
  refine ⟨t, hb.trans (hz'.trans (congrArg _ hz)), ?_⟩
  have hπ := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (K.homologyπ_extendHomologyIso_inv e hn)) a
  change (K.extendHomologyIso e hn).inv.hom (explicitClass K n z) =
    ((K.extend e).homologyπ n').hom b at hπ
  exact hπ.trans (explicitClass_eq_of_iCycles (K.extend e) n' b t hb.symm)

end Representatives

section FlatRepresentatives

set_option maxHeartbeats 600000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : Type u} [Ring T] {N : Type x} [AddCommGroup N] [Module T N]
variable {ι : Type v} (c : ComplexShape ι) (C : HomologicalComplex (ModuleCat.{w} Tᵐᵒᵖ) c)
variable (hN : P103.Specs.Ch02.FlatnessTests.Flat.{u,x,w} T N)

theorem flatQuotientHomologyIso_class (n : ι) (z : cycles C n) (b : N) :
    let F := tensorFunctor N
    let L := (F.mapHomologicalComplex c).obj C
    ∃ t : cycles L n, t.val = tmul T z.val b ∧
      (flatQuotientHomologyIso N hN c C n).hom.hom
        (tmul T (homologyClass C n z) b) = homologyClass L n t := by
  let F : ModuleCat.{w} Tᵐᵒᵖ ⥤ ModuleCat.{max w x} ℤ := tensorFunctor N
  let L := (F.mapHomologicalComplex c).obj C
  letI := TorBalance.flat_tensor_preservesHomology hN
  let H := TorBalance.exactHomologyComparison F
  let a := (C.sc n).moduleCatCyclesIso.inv.hom z
  let y : L.cycles n := ((H.cyclesEquivalence (C.sc n)).hom).hom (tmul T a b)
  let t : cycles L n := (L.sc n).moduleCatCyclesIso.hom.hom y
  have ht := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (L.sc n).moduleCatCyclesIso_hom_i) y
  change t.val = (L.iCycles n).hom y at ht
  have hi := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (H.inclusion (C.sc n))) (tmul T a b)
  change (L.iCycles n).hom y = tmul T ((C.iCycles n).hom a) b at hi
  have ha : (C.iCycles n).hom a = z.val := explicitCycle_iCycles C n z
  refine ⟨t, ht.trans (hi.trans (congrArg (fun t => tmul T t b) ha)), ?_⟩
  have hp := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (H.projection (C.sc n))) (tmul T a b)
  change (H.equivalence (C.sc n)).hom.hom (tmul T (explicitClass C n z) b) =
    (L.homologyπ n).hom y at hp
  change (explicitToCategoricalHomologyIso L n).inv.hom
    ((H.equivalence (C.sc n)).hom.hom
      (tmul T ((explicitToCategoricalHomologyIso C n).hom.hom (homologyClass C n z)) b)) = _
  rw [explicitToCategoricalHomologyIso_apply_class, hp,
    explicitClass_eq_of_iCycles L n y t ht.symm]
  have h := quotientHomologyIso_apply_class L n t
  rw [quotientHomologyIso_eq_explicitToCategoricalHomologyIso_symm] at h
  exact h

end FlatRepresentatives

end

section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open P103.BalancedTensor P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open DoubleComplexFirstPages

section NaturalSquares

variable {V : Type*} [Category* V]
variable {I I' J J' K K' : V}

theorem composeIso_natural
    (a : I ≅ J) (a' : I' ≅ J') (b : J ≅ K) (b' : J' ≅ K')
    (f : I ⟶ I') (g : J ⟶ J') (h : K ⟶ K')
    (ha : f ≫ a'.hom = a.hom ≫ g) (hb : g ≫ b'.hom = b.hom ≫ h) :
    f ≫ (a' ≪≫ b').hom = (a ≪≫ b).hom ≫ h := by
  simp only [Iso.trans_hom]
  rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]

theorem inverseIso_natural (a : I ≅ J) (b : I' ≅ J') (f : I ⟶ I') (g : J ⟶ J')
    (h : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  apply (cancel_mono b.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, h, Iso.inv_hom_id_assoc]

end NaturalSquares

section ExtensionQuotient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {B : Type u} [Ring B]
variable {K K' : CochainComplex (ModuleCat.{w} B) ℤ}
variable {L L' : ChainComplex (ModuleCat.{w} B) ℕ}

/-- The quotient comparison for a nonnegative chain complex presented as
a cochain complex supported in nonpositive degrees. -/
def negativeExtensionQuotientIso (a : K ≅ L.extend negativeChainEmbedding) (n : ℕ) :
    K.homology (negativeChainEmbedding.f n) ≅ ModuleCat.of B (Homology L n) :=
  homologyMapIso a (negativeChainEmbedding.f n) ≪≫
    L.extendHomologyIso negativeChainEmbedding (j := n) rfl ≪≫ quotientHomologyIso L n

theorem negativeExtensionQuotientIso_natural
    (a : K ≅ L.extend negativeChainEmbedding) (a' : K' ≅ L'.extend negativeChainEmbedding)
    (g : K ⟶ K') (l : L ⟶ L')
    (h : g ≫ a'.hom = a.hom ≫ extendMap l negativeChainEmbedding) (n : ℕ) :
    HomologicalComplex.homologyMap g (negativeChainEmbedding.f n) ≫
      (negativeExtensionQuotientIso a' n).hom =
    (negativeExtensionQuotientIso a n).hom ≫
      ModuleCat.ofHom (P103.Specs.Ch10.Complexes.homologyMap l n) := by
  let j := negativeChainEmbedding.f n
  let H := homologyFunctor (ModuleCat.{w} B) (ComplexShape.up ℤ) j
  have ha : H.map g ≫ (H.mapIso a').hom =
      (H.mapIso a).hom ≫ H.map (extendMap l negativeChainEmbedding) := by
    rw [Functor.mapIso_hom, Functor.mapIso_hom, ← H.map_comp, ← H.map_comp, h]
  have hb := extendHomologyIso_hom_naturality l negativeChainEmbedding (j := n) rfl
  have hc := quotientHomologyIso_natural L n l
  exact composeIso_natural _ _ _ _ _ _ _ ha (composeIso_natural _ _ _ _ _ _ _ hb hc)

theorem negativeExtensionQuotientIso_inv_class
    (a : K ≅ L.extend negativeChainEmbedding) (n : ℕ) (z : cycles L n) :
    ∃ t : cycles K (negativeChainEmbedding.f n),
      t.val = (a.inv.f (negativeChainEmbedding.f n)).hom
        ((L.extendXIso negativeChainEmbedding (i := n) rfl).inv.hom z.val) ∧
      (negativeExtensionQuotientIso a n).inv.hom (homologyClass L n z) =
        explicitClass K (negativeChainEmbedding.f n) t := by
  let j := negativeChainEmbedding.f n
  obtain ⟨y, hy, hclass⟩ := explicitClass_extend_inv L n negativeChainEmbedding
    (n' := j) rfl z
  let t := P103.Specs.Ch10.Complexes.cyclesMap a.inv j y
  refine ⟨t, ?_, ?_⟩
  · change (a.inv.f j).hom y.val = _
    rw [hy]
  · change (HomologicalComplex.homologyMap a.inv j).hom
      ((L.extendHomologyIso negativeChainEmbedding (j := n) rfl).inv.hom
        ((quotientHomologyIso L n).inv.hom (homologyClass L n z))) = _
    have hz : (quotientHomologyIso L n).inv.hom (homologyClass L n z) = explicitClass L n z := by
      rw [quotientHomologyIso_eq_explicitToCategoricalHomologyIso_symm]
      exact explicitToCategoricalHomologyIso_apply_class L n z
    rw [hz, hclass]
    exact explicitClass_map _ _ a.inv y

end ExtensionQuotient

section TensorRowTerms

set_option maxHeartbeats 700000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : Type u} [Ring T]

/-- The term of the integer extension corresponding to a nonnegative degree,
written using the sign convention of the cochain bicomplex. -/
def reversedExtendXIso {V : Type*} [Category* V] [Abelian V]
    (C : ChainComplex V ℕ) (n : ℕ) :
    C.X n ≅ (C.extend nonnegativeChainEmbedding).X (-negativeChainEmbedding.f n) :=
  (C.extendXIso nonnegativeChainEmbedding (i := n)
    (by change (n : ℤ) = -(-(n : ℤ)); omega)).symm

theorem reversedExtendXIso_d {V : Type*} [Category* V] [Abelian V]
    (C : ChainComplex V ℕ) (i j : ℕ) :
    C.d i j ≫ (reversedExtendXIso C j).hom =
      (reversedExtendXIso C i).hom ≫
        (C.extend nonnegativeChainEmbedding).d (-negativeChainEmbedding.f i) (-negativeChainEmbedding.f j) := by
  let hi : nonnegativeChainEmbedding.f i = -negativeChainEmbedding.f i := (Int.neg_neg (i : ℤ)).symm
  let hj : nonnegativeChainEmbedding.f j = -negativeChainEmbedding.f j := (Int.neg_neg (j : ℤ)).symm
  change C.d i j ≫ (C.extendXIso nonnegativeChainEmbedding hj).inv =
    (C.extendXIso nonnegativeChainEmbedding hi).inv ≫ (C.extend nonnegativeChainEmbedding).d _ _
  rw [C.extend_d_eq nonnegativeChainEmbedding hi hj, Iso.inv_hom_id_assoc]

theorem reversedExtendXIso_map {V : Type*} [Category* V] [Abelian V]
    {C C' : ChainComplex V ℕ} (a : C ⟶ C') (i : ℕ) :
    a.f i ≫ (reversedExtendXIso C' i).hom =
      (reversedExtendXIso C i).hom ≫ (extendMap a nonnegativeChainEmbedding).f (-negativeChainEmbedding.f i) := by
  let hi : nonnegativeChainEmbedding.f i = -negativeChainEmbedding.f i := (Int.neg_neg (i : ℤ)).symm
  change a.f i ≫ (C'.extendXIso nonnegativeChainEmbedding hi).inv =
    (C.extendXIso nonnegativeChainEmbedding hi).inv ≫ (extendMap a nonnegativeChainEmbedding).f _
  rw [extendMap_f a nonnegativeChainEmbedding hi, Iso.inv_hom_id_assoc]

/-- The tensor of two termwise isomorphisms. -/
def tensorTermIso {A A' : ModuleCat.{v} Tᵐᵒᵖ} {B B' : ModuleCat.{w} T}
    (a : A ≅ A') (b : B ≅ B') :
    ModuleCat.of ℤ (Tensor T A B) ≅ ModuleCat.of ℤ (Tensor T A' B') :=
  (tensorFunctor B).mapIso a ≪≫ (leftTensorFunctor A').mapIso b

theorem tensorTermIso_hom {A A' : ModuleCat.{v} Tᵐᵒᵖ} {B B' : ModuleCat.{w} T}
    (a : A ≅ A') (b : B ≅ B') :
    (tensorTermIso a b).hom = ModuleCat.ofHom (tensorMap a.hom.hom b.hom.hom) := by
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro p q
  rfl

theorem tensorTermIso_natural {A A' U U' : ModuleCat.{v} Tᵐᵒᵖ}
    {B B' V V' : ModuleCat.{w} T}
    (a : A ≅ U) (a' : A' ≅ U') (b : B ≅ V) (b' : B' ≅ V')
    (l : A ⟶ A') (l' : U ⟶ U') (m : B ⟶ B') (m' : V ⟶ V')
    (hl : l ≫ a'.hom = a.hom ≫ l') (hm : m ≫ b'.hom = b.hom ≫ m') :
    ModuleCat.ofHom (tensorMap l.hom m.hom) ≫ (tensorTermIso a' b').hom =
      (tensorTermIso a b).hom ≫ ModuleCat.ofHom (tensorMap l'.hom m'.hom) := by
  rw [tensorTermIso_hom, tensorTermIso_hom]
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro z y
  have hz := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hl) z
  have hy := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hm) y
  exact congrArg₂ (tmul T) hz hy

variable (C : ChainComplex (ModuleCat.{v} Tᵐᵒᵖ) ℕ)
variable (D : ChainComplex (ModuleCat.{w} T) ℕ)

abbrev cochainTensorRow (p : ℕ) :=
  (tensorCochainBicomplex C D).flip.X (negativeChainEmbedding.f p)

def tensorRowRestrictionIso (p : ℕ) :
    tensorComplex C (D.X p) ≅ (cochainTensorRow C D p).restriction negativeChainEmbedding :=
  Hom.isoOfComponents
    (fun i => tensorTermIso (reversedExtendXIso C i) (reversedExtendXIso D p)) (by
      intro i j hij
      exact (tensorTermIso_natural _ _ _ _ (C.d i j)
        ((extendNonnegativeChain C).d (-negativeChainEmbedding.f i) (-negativeChainEmbedding.f j))
        (𝟙 _) (𝟙 _) (reversedExtendXIso_d C i j) (by simp)).symm)

theorem cochainTensorRow_zero (p : ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((cochainTensorRow C D p).X i) :=
  tensorCochainBicomplex_upper C D i (negativeChainEmbedding.f p) (Or.inl hi)

def tensorRowExtensionIso (p : ℕ) :
    (tensorComplex C (D.X p)).extend negativeChainEmbedding ≅ cochainTensorRow C D p :=
  (negativeExtensionIso (tensorRowRestrictionIso C D p).symm (cochainTensorRow_zero C D p)).symm

theorem tensorRowExtensionIso_f (p i : ℕ) :
    (tensorRowExtensionIso C D p).hom.f (negativeChainEmbedding.f i) =
      ((tensorComplex C (D.X p)).extendXIso negativeChainEmbedding (i := i) rfl).hom ≫
        (tensorTermIso (reversedExtendXIso C i) (reversedExtendXIso D p)).hom :=
  negativeExtensionIso_inv_f (tensorRowRestrictionIso C D p).symm (cochainTensorRow_zero C D p) i

theorem tensorRowExtensionIso_natural
    {C' : ChainComplex (ModuleCat.{v} Tᵐᵒᵖ) ℕ}
    {D' : ChainComplex (ModuleCat.{w} T) ℕ} {p p' : ℕ}
    (g : tensorComplex C (D.X p) ⟶ tensorComplex C' (D'.X p'))
    (g' : cochainTensorRow C D p ⟶ cochainTensorRow C' D' p')
    (h : ∀ i, g.f i ≫ (tensorTermIso (reversedExtendXIso C' i) (reversedExtendXIso D' p')).hom =
      (tensorTermIso (reversedExtendXIso C i) (reversedExtendXIso D p)).hom ≫
        g'.f (negativeChainEmbedding.f i)) :
    extendMap g negativeChainEmbedding ≫ (tensorRowExtensionIso C' D' p').hom =
      (tensorRowExtensionIso C D p).hom ≫ g' := by
  have ha : g ≫ (tensorRowRestrictionIso C' D' p').hom =
      (tensorRowRestrictionIso C D p).hom ≫ restrictionMap g' negativeChainEmbedding := by
    apply Hom.ext
    funext i
    exact h i
  have hb := negativeExtensionIso_natural (tensorRowRestrictionIso C D p).symm
    (tensorRowRestrictionIso C' D' p').symm (cochainTensorRow_zero C D p)
    (cochainTensorRow_zero C' D' p') g' g (inverseIso_natural _ _ _ _ ha)
  exact inverseIso_natural _ _ _ _ hb

end TensorRowTerms

end

section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open P103.BalancedTensor P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open DoubleTotalization

section TotalRegrading
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Type u} [Category.{v} V] [Abelian V]

/-- Restricting to the nonpositive cochain degrees after reversal gives precisely
the nonnegative chain degrees of the original complex. -/
def reversedRestrictionIso (K : ChainComplex V ℤ) :
    (K.restriction negChainEmbedding).restriction negativeChainEmbedding ≅
      K.restriction nonnegativeChainEmbedding :=
  Hom.isoOfComponents (fun i => K.XIsoOfEq
    (show -(-(i : ℤ)) = (i : ℤ) from Int.neg_neg _)) (by
      intro i j hij
      exact (K.XIsoOfEq_hom_comp_d (Int.neg_neg (i : ℤ)) (j : ℤ)).trans
        (K.d_comp_XIsoOfEq_hom (Int.neg_neg (j : ℤ)) (-(-(i : ℤ)))).symm)

theorem reversedRestrictionIso_natural {K L : ChainComplex V ℤ} (g : K ⟶ L) :
    restrictionMap (restrictionMap g negChainEmbedding) negativeChainEmbedding ≫
        (reversedRestrictionIso L).hom =
      (reversedRestrictionIso K).hom ≫ restrictionMap g nonnegativeChainEmbedding := by
  apply Hom.ext
  funext i
  exact XIsoOfEq_hom_naturality g (Int.neg_neg (i : ℤ))

variable {R : Type u} [Ring R]
variable (C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
variable (D D' : ChainComplex (ModuleCat.{w} R) ℕ)
variable [(tensorCochainBicomplex C D).HasTotal (ComplexShape.up ℤ)]
variable [(tensorCochainBicomplex C' D').HasTotal (ComplexShape.up ℤ)]

theorem reversedTensorTotal_zero (n : ℤ) (hn : 0 < n) :
    IsZero (((ordinaryTensorTotal C D).restriction negChainEmbedding).X n) := by
  change IsZero ((ordinaryTensorTotal C D).X (-n))
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  letI : Subsingleton ((ordinaryTensorTotal C D).X (-n)) :=
    P103.Ch10.TotalComplexAssembly.total_supportedBelow K 0 0
      (P103.Ch11.TorBalance.ordinary_tensor_supported C D) (-n) (by omega)
  exact ModuleCat.isZero_of_subsingleton _

/-- The signed cochain total is identified by its summand inclusions
with the zero extension of the ordinary signed tensor total. -/
def ordinaryTotalRegrading : TotalRegrading C D := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  let e := negativeExtensionIso (reversedRestrictionIso (ordinaryTensorTotal C D))
    (reversedTensorTotal_zero C D)
  refine ⟨reverseTotalIso K ≪≫ e, ?_⟩
  intro i j n h z
  have hι := reverseTotalTermMap_ι K (-(i : ℤ)) (-(j : ℤ)) (-(n : ℤ)) (by omega)
  have hh := negativeExtensionIso_hom_f (reversedRestrictionIso (ordinaryTensorTotal C D))
    (reversedTensorTotal_zero C D) n
  change (e.hom.f (negativeChainEmbedding.f n)) = _ at hh
  have hv := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hι)
    (tensorSummand C D i j z)
  let ι := sumInjection (tensorCochainBicomplex C D) (-(i : ℤ)) (-(j : ℤ)) (-(n : ℤ))
    (by omega)
  change (reverseTotalTermMap K (-(n : ℤ))).hom (ι.hom (tensorSummand C D i j z)) = _ at hv
  change (e.hom.f (negativeChainEmbedding.f n)).hom
    ((reverseTotalTermMap K (-(n : ℤ))).hom (ι.hom (tensorSummand C D i j z))) = _
  rw [hv, hh]
  subst n
  cases i <;> cases j <;> rfl

variable {C D C' D'}
theorem ordinaryTotalRegrading_natural (l : C ⟶ C') (m : D ⟶ D') :
    HomologicalComplex₂.total.map (tensorCochainBicomplexMap l m) (ComplexShape.up ℤ) ≫
        (ordinaryTotalRegrading C' D').iso.hom =
      (ordinaryTotalRegrading C D).iso.hom ≫
        extendMap (ordinaryTotalMap l m) negativeChainEmbedding := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  let L := tensorBicomplex (extendNonnegativeChain C') (extendNonnegativeChain D')
  let f := tensorBicomplexMap (extendMap l nonnegativeChainEmbedding)
    (extendMap m nonnegativeChainEmbedding)
  let g := HomologicalComplex₂.total.map f (ComplexShape.down ℤ)
  let e := negativeExtensionIso (reversedRestrictionIso (ordinaryTensorTotal C D))
    (reversedTensorTotal_zero C D)
  let e' := negativeExtensionIso (reversedRestrictionIso (ordinaryTensorTotal C' D'))
    (reversedTensorTotal_zero C' D')
  have h := reverseTotalIso_natural f
  have he := negativeExtensionIso_natural _ _ (reversedTensorTotal_zero C D)
    (reversedTensorTotal_zero C' D') (restrictionMap g negChainEmbedding)
    (ordinaryTotalMap l m) (reversedRestrictionIso_natural g)
  change HomologicalComplex₂.total.map (chainToCochainBicomplexMap f) (ComplexShape.up ℤ) ≫
      (reverseTotalIso L).hom ≫ e'.hom =
    ((reverseTotalIso K).hom ≫ e.hom) ≫ extendMap (ordinaryTotalMap l m) negativeChainEmbedding
  erw [← Category.assoc, h, Category.assoc, he, Category.assoc]
  rfl

end TotalRegrading

end

section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open P103.BalancedTensor P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open DoubleComplexFirstPages

section Rows
set_option maxHeartbeats 900000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [Ring R]
variable (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ) (D : ChainComplex (ModuleCat.{w} R) ℕ)

abbrev ordinaryRows (q : ℕ) :=
  ((ordinaryHorizontalHomologyFunctor C q).mapHomologicalComplex (ComplexShape.down ℕ)).obj D

abbrev cochainRows (q : ℕ) :=
  verticalHomology (tensorCochainBicomplex C D).flip (negativeChainEmbedding.f q)

def ordinaryRowTermIso (p q : ℕ) :
    (cochainRows C D q).X (negativeChainEmbedding.f p) ≅ (ordinaryRows C D q).X p :=
  negativeExtensionQuotientIso (tensorRowExtensionIso C D p).symm q

theorem ordinaryRowTermIso_natural
    {C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    {D' : ChainComplex (ModuleCat.{w} R) ℕ} {p p' : ℕ}
    (g : tensorComplex C (D.X p) ⟶ tensorComplex C' (D'.X p'))
    (g' : cochainTensorRow C D p ⟶ cochainTensorRow C' D' p')
    (h : ∀ i, g.f i ≫ (tensorTermIso (reversedExtendXIso C' i) (reversedExtendXIso D' p')).hom =
      (tensorTermIso (reversedExtendXIso C i) (reversedExtendXIso D p)).hom ≫
        g'.f (negativeChainEmbedding.f i)) (q : ℕ) :
    HomologicalComplex.homologyMap g' (negativeChainEmbedding.f q) ≫ (ordinaryRowTermIso C' D' p' q).hom =
      (ordinaryRowTermIso C D p q).hom ≫ ModuleCat.ofHom (P103.Specs.Ch10.Complexes.homologyMap g q) :=
  negativeExtensionQuotientIso_natural _ _ g' g
    (inverseIso_natural (tensorRowExtensionIso C D p) (tensorRowExtensionIso C' D' p') _ _
      (tensorRowExtensionIso_natural C D g g' h)) q

def ordinaryRowsRestrictionIso (q : ℕ) :
    (cochainRows C D q).restriction negativeChainEmbedding ≅ ordinaryRows C D q :=
  Hom.isoOfComponents (fun p => ordinaryRowTermIso C D p q) (by
    intro p p' hp
    let g := tensorSecondMap C (D.d p p').hom
    let g' := (tensorCochainBicomplex C D).flip.d (negativeChainEmbedding.f p) (negativeChainEmbedding.f p')
    refine (ordinaryRowTermIso_natural C D g g' (fun i => ?_) q).symm
    exact tensorTermIso_natural _ _ _ _ (𝟙 _) (𝟙 _) (D.d p p')
      ((extendNonnegativeChain D).d (-negativeChainEmbedding.f p) (-negativeChainEmbedding.f p'))
      (by simp) (reversedExtendXIso_d D p p'))

theorem cochainRows_zero (q : ℕ) (p : ℤ) (hp : 0 < p) :
    IsZero ((cochainRows C D q).X p) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (tensorCochainBicomplex_upper C D (negativeChainEmbedding.f q) p (Or.inr hp))

/-- The unsigned horizontal homology complex regrades to the zero extension
of the complex of ordinary horizontal cycle quotients. -/
def ordinaryRowsExtensionIso (q : ℕ) :
    cochainRows C D q ≅ (ordinaryRows C D q).extend negativeChainEmbedding :=
  negativeExtensionIso (ordinaryRowsRestrictionIso C D q) (cochainRows_zero C D q)

theorem ordinaryRowsExtensionIso_inv_class (p q : ℕ) (z : cycles (tensorComplex C (D.X p)) q) :
    ∃ t : cycles (cochainTensorRow C D p) (negativeChainEmbedding.f q),
      t.val = tensorSummand C D q p z.val ∧
      ((ordinaryRowsExtensionIso C D q).inv.f (negativeChainEmbedding.f p)).hom
        (((ordinaryRows C D q).extendXIso negativeChainEmbedding (i := p) rfl).inv.hom
          (homologyClass (tensorComplex C (D.X p)) q z)) =
        explicitClass (cochainTensorRow C D p) (negativeChainEmbedding.f q) t := by
  obtain ⟨t, ht, he⟩ := negativeExtensionQuotientIso_inv_class
    (tensorRowExtensionIso C D p).symm q z
  refine ⟨t, ?_, ?_⟩
  · rw [ht]
    change ((tensorRowExtensionIso C D p).hom.f (negativeChainEmbedding.f q)).hom _ = _
    rw [tensorRowExtensionIso_f, tensorTermIso_hom]
    let e := (tensorComplex C (D.X p)).extendXIso negativeChainEmbedding (i := q) rfl
    have hz : e.hom.hom (e.inv.hom z.val) = z.val :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id) z.val
    change tensorMap (reversedExtendXIso C q).hom.hom (reversedExtendXIso D p).hom.hom
      (e.hom.hom (e.inv.hom z.val)) = _
    rw [hz]
    rfl
  · erw [negativeExtensionIso_inv_f (ordinaryRowsRestrictionIso C D q) (cochainRows_zero C D q) p]
    let e := (ordinaryRows C D q).extendXIso negativeChainEmbedding (i := p) rfl
    have hz : e.hom.hom (e.inv.hom (homologyClass (tensorComplex C (D.X p)) q z)) =
        homologyClass (tensorComplex C (D.X p)) q z :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id)
        (homologyClass (tensorComplex C (D.X p)) q z)
    change (ordinaryRowTermIso C D p q).inv.hom
      (e.hom.hom (e.inv.hom (homologyClass (tensorComplex C (D.X p)) q z))) = _
    rw [hz]
    exact he

end Rows

section ChangeOfRingsRows

set_option maxHeartbeats 900000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)

theorem horizontalHomologyIso_class (N : Type (max v x)) [AddCommGroup N] [Module S N]
    (hN : P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S N)
    (q : ℕ) (z : cycles (tensorComplex C (Restricted f S)) q) (b : N) :
    letI := innerTorModule f C q
    letI := (extensionAction f (C.X q)).module
    let L := tensorComplex C (Restricted f N)
    ∃ t : cycles L q, t.val = reassociation f (C.X q) N (tmul S z.val b) ∧
      horizontalHomologyIso f C N hN q (tmul S (homologyClass (tensorComplex C (Restricted f S)) q z) b) =
        homologyClass L q t := by
  letI := innerTorModule f C q
  letI := (extensionAction f (C.X q)).module
  let E := (extensionComplexData f C).complex
  let zE := (extensionCyclesEquiv f C q).symm z
  let L := tensorComplex C (Restricted f N)
  let e := reassociationComplexIso f N (ComplexShape.down ℕ) C
  obtain ⟨y, hy, hc⟩ := flatQuotientHomologyIso_class (c := ComplexShape.down ℕ) E hN q zE b
  let t : cycles L q := P103.Specs.Ch10.Complexes.cyclesMap e.hom q y
  have hz : zE.val = z.val := rfl
  refine ⟨t, ?_, ?_⟩
  · change (e.hom.f q).hom y.val = _
    rw [hy]
    change reassociation f (C.X q) N (tmul S zE.val b) = _
    rw [hz]
  · have hI : (innerTorEquiv f C q).symm (homologyClass (tensorComplex C (Restricted f S)) q z) =
        homologyClass E q zE := by
      apply (innerTorEquiv f C q).injective
      rw [LinearEquiv.apply_symm_apply]
      change _ = homologyClass (tensorComplex C (Restricted f S)) q (extensionCyclesEquiv f C q zE)
      rw [LinearEquiv.apply_symm_apply]
    change P103.Specs.Ch10.Complexes.homologyMap e.hom q
      ((flatQuotientHomologyIso N hN (ComplexShape.down ℕ) E q).hom.hom
        (tmul S ((innerTorEquiv f C q).symm (homologyClass (tensorComplex C (Restricted f S)) q z)) b)) = _
    rw [hI, hc]
    rfl

def rowTensorComparison
    (C₁ : ChainComplex (ModuleCat.{max u w} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{max u v x} S) ℕ)
    (hD : ∀ p, P103.Specs.Ch02.FlatnessTests.Flat.{v,max u v x,max u w v} S (D.X p))
    (q : ℕ) :
    letI := innerTorModule f C₁ q
    RowTensorComparison.{u,v,w,x} f C₁ D (innerHomologyData f C₁) q := by
  letI := innerTorModule f C₁ q
  let E := negativeChainEmbedding.extendFunctor (ModuleCat.{max u v w x} ℤ)
  let D' := restrictionComplex f (ComplexShape.down ℕ) D
  let L := leftOrdinaryTensorComplex (Homology (tensorComplex C₁ (Restricted f S)) q) D
  let a := rowHomologyComplexIso.{u,v,max u w,max u x} f C₁ D hD q
  let b := ordinaryRowsExtensionIso C₁ D' q
  refine {
    reassociate := fun p => reassociation f (C₁.X q) (D.X p)
    on_tensors := fun p => reassociation_tmul f (C₁.X q) (D.X p)
    iso := E.mapIso a ≪≫ b.symm
    on_classes := ?_ }
  intro p z y
  obtain ⟨s, hs, he⟩ := horizontalHomologyIso_class.{u,v,max u w,max u x} f C₁ (D.X p) (hD p) q z y
  obtain ⟨t, ht, hπ⟩ := ordinaryRowsExtensionIso_inv_class C₁ D' p q s
  refine ⟨t, ht.trans (congrArg (tensorSummand C₁ D' q p) hs), ?_⟩
  let c := L.extendXIso negativeChainEmbedding (i := p) rfl
  let c' := (ordinaryRows C₁ D' q).extendXIso negativeChainEmbedding (i := p) rfl
  let z' := tmul S (homologyClass (tensorComplex C₁ (Restricted f S)) q z) y
  change (b.inv.f (negativeChainEmbedding.f p)).hom
      (((extendMap a.hom negativeChainEmbedding).f (negativeChainEmbedding.f p)).hom (c.inv.hom z')) = _
  have h := extendMap_f a.hom negativeChainEmbedding (i := p) rfl
  change (extendMap a.hom negativeChainEmbedding).f (negativeChainEmbedding.f p) =
    c.hom ≫ a.hom.f p ≫ c'.inv at h
  rw [h]
  have hz : c.hom.hom (c.inv.hom z') = z' :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom c.inv_hom_id) z'
  change (b.inv.f (negativeChainEmbedding.f p)).hom (c'.inv.hom
    (horizontalHomologyIso.{u,v,max u w,max u x} f C₁ (D.X p) (hD p) q (c.hom.hom (c.inv.hom z')))) = _
  rw [hz]
  change (b.inv.f (negativeChainEmbedding.f p)).hom (c'.inv.hom (horizontalHomologyIso.{u,v,max u w,max u x} f C₁ (D.X p) (hD p) q
    (tmul S (homologyClass (tensorComplex C₁ (Restricted f S)) q z) y))) = _
  rw [he]
  exact hπ

end ChangeOfRingsRows

end

section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open DoubleTotalization HomologicalComplex

section Targets

set_option maxHeartbeats 600000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
variable {A A' : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  [AddCommGroup A'] [Module Rᵐᵒᵖ A']
variable {M M' : Type (max u v x)} [AddCommGroup M] [Module S M]
  [AddCommGroup M'] [Module S M']
variable {P : LeftResolution Rᵐᵒᵖ A} {P' : LeftResolution Rᵐᵒᵖ A'}
  {Q : LeftResolution S M} {Q' : LeftResolution S M'}
variable [(tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex).HasTotal
    (ComplexShape.up ℤ)]
variable [(tensorCochainBicomplex P'.complex (restrictionResolution f M' Q').complex).HasTotal
    (ComplexShape.up ℤ)]

namespace TargetComparisonData

/-- The abutment is the homology of the summand-preserving regrading
followed by the actual total augmentation on the ordinary quotient. -/
def cochainHomologyIso (T : TargetComparisonData f A M P Q) (n : ℕ) :
    (sumTotal (tensorCochainBicomplex P.complex
      (restrictionResolution f M Q).complex)).homology (-(n : ℤ)) ≅
      ModuleCat.of ℤ (TorWith P (Restricted f M) n) :=
  negativeExtensionQuotientIso
      (ordinaryTotalRegrading P.complex (restrictionResolution f M Q).complex).iso n ≪≫
    (T.homologyEquiv n).toModuleIso

end TargetComparisonData

theorem target_cochainHomologyIso_natural
    (g : M →ₗ[S] M') (l : P.complex ⟶ P'.complex) (m : Q.complex ⟶ Q'.complex)
    (hm : ChainLift Q Q' g m)
    (α : TargetComparisonData f A M P Q) (β : TargetComparisonData f A' M' P' Q') (n : ℕ) :
    HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map
        (tensorCochainBicomplexMap l (restrictionResolutionMap (f := f) m)) (ComplexShape.up ℤ))
      (-(n : ℤ)) ≫ (β.cochainHomologyIso n).hom =
    (α.cochainHomologyIso n).hom ≫
      ModuleCat.ofHom (P103.Specs.Ch10.Complexes.homologyMap
        (tensorFirstMap l (Restricted f M) ≫ tensorSecondMap P'.complex (Restricted.map f g)) n) := by
  let m' := restrictionResolutionMap (f := f) m
  let s := HomologicalComplex₂.total.map (tensorCochainBicomplexMap l m') (ComplexShape.up ℤ)
  let t := ordinaryTotalMap l m'
  let a := (ordinaryTotalRegrading P.complex (restrictionResolution f M Q).complex).iso
  let b := (ordinaryTotalRegrading P'.complex (restrictionResolution f M' Q').complex).iso
  have h₁ := negativeExtensionQuotientIso_natural a b s t
    (ordinaryTotalRegrading_natural l m') n
  let k := tensorFirstMap l (Restricted f M) ≫ tensorSecondMap P'.complex (Restricted.map f g)
  let H := quotientHomology (S := ℤ) (ComplexShape.down ℕ) n
  have h₂ : H.map t ≫ (β.homologyEquiv n).toModuleIso.hom =
      (α.homologyEquiv n).toModuleIso.hom ≫ H.map k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact target_homologyEquiv_natural g l m hm α β n
  exact composeIso_natural _ _ _ _ _ _ _ h₁ h₂

end Targets

section ExtensionQuotientComposition

set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {B : Type u} [Ring B]
variable {K : CochainComplex (ModuleCat.{w} B) ℤ}
variable {L L' : ChainComplex (ModuleCat.{w} B) ℕ}

theorem negativeExtensionQuotientIso_comp
    (a : K ≅ L.extend negativeChainEmbedding) (b : L ≅ L') (n : ℕ) :
    negativeExtensionQuotientIso
      (a ≪≫ (negativeChainEmbedding.extendFunctor (ModuleCat.{w} B)).mapIso b) n =
    negativeExtensionQuotientIso a n ≪≫ (quotientHomology (S := B) (ComplexShape.down ℕ) n).mapIso b := by
  apply Iso.ext
  let j := negativeChainEmbedding.f n
  let E := extendMap b.hom negativeChainEmbedding
  let H := homologyFunctor (ModuleCat.{w} B) (ComplexShape.up ℤ) j
  let e := L.extendHomologyIso negativeChainEmbedding (j := n) rfl
  let e' := L'.extendHomologyIso negativeChainEmbedding (j := n) rfl
  let q := quotientHomologyIso L n
  let q' := quotientHomologyIso L' n
  let f := (quotientHomology (S := B) (ComplexShape.down ℕ) n).map b.hom
  change H.map (a.hom ≫ E) ≫ e'.hom ≫ q'.hom =
    (H.map a.hom ≫ e.hom ≫ q.hom) ≫ f
  have h := extendHomologyIso_hom_naturality b.hom negativeChainEmbedding (j := n) rfl
  have hq := quotientHomologyIso_natural L n b.hom
  rw [H.map_comp]
  simp only [Category.assoc]
  erw [← Category.assoc (H.map E) e'.hom, h, Category.assoc, hq, Category.assoc]

end ExtensionQuotientComposition

end

section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.TorBalance P103.Specs.Ch11.ExtTorDefinitions

section ResolvedAssembly

set_option maxHeartbeats 650000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
variable {A : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  {M : Type (max u v x)} [AddCommGroup M] [Module S M]
  {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution S M}
  [(tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex).HasTotal
    (ComplexShape.up ℤ)]

/-- Assemble the quotient pages with the actual augmentation and the
unsigned calculation used after the signed first-page identification. -/
def resolvedSequenceFromPages
    (B : TensorPagesData P.complex (restrictionResolution f M Q).complex)
    (T : TargetComparisonData f A M P Q) (hQ : Q.IsProjective) :
    ResolvedSequenceData f A M P Q where
  toTensorPagesData := B
  inner := innerHomologyData f P.complex
  innerModule := innerTorModule f P.complex
  innerLinear := fun q => (innerTorEquiv f P.complex q).map_smul
  totalRegrading := ordinaryTotalRegrading P.complex (restrictionResolution f M Q).complex
  augmentation := T
  rowTensor := fun q => rowTensorComparison.{u,v,w,x} f P.complex Q.complex
    (fun p => P103.Ch02.FlatnessTests.projective_flat S (Q.complex.X p) (hQ p)) q
  balance := by
    intro q
    letI := innerTorModule f P.complex q
    intro U hU
    exact TorBalance.balance S (TorWith P (Restricted f S) q) M U Q hU hQ
  firstQuadrant := fun r p q _ h => B.chainFirstQuadrant r p q h

theorem resolved_sequence : Specs.ResolvedSequence.{u,v,w,x} := by
  intro R S _ _ f A _ _ M _ _ P Q hP hQ _
  obtain ⟨B⟩ := tensor_pages R P.complex (restrictionResolution f M Q).complex
  obtain ⟨T⟩ := target_comparison R S f A M P Q hP
  exact ⟨resolvedSequenceFromPages B T hQ⟩

end ResolvedAssembly

end

section ResolvedAssembly
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.TorBalance
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
namespace ResolvedSequenceData
open CategoryTheory.Limits
variable {A : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  {M : Type (max u v x)} [AddCommGroup M] [Module S M]
  {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution S M}
  [(tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex).HasTotal
    (ComplexShape.up ℤ)]
  (E : ResolvedSequenceData f A M P Q)

/-- The target filtration transported to the original Tor quotient. -/
def targetPiece (p : ℤ) (n : ℕ) : Subobject (ModuleCat.of ℤ (TorWith P (Restricted f M) n)) :=
  Subobject.mapIsoToOrderIso (E.targetIso n) (chainTargetPiece E.filtration p (n : ℤ))

theorem targetPiece_increasing (p : ℤ) (n : ℕ) :
    E.targetPiece (p-1) n ≤ E.targetPiece p n :=
  (Subobject.mapIsoToOrderIso (E.targetIso n)).monotone
    (chainTargetPiece_increasing E.filtration p (n : ℤ))

@[simp] theorem targetPiece_bot (n : ℕ) : E.targetPiece (-1) n = ⊥ := by
  change Subobject.mapIsoToOrderIso (E.targetIso n)
    (FiniteFiltrationConvergence.cohomologyPiece E.filtration 1 (-(n : ℤ))) = ⊥
  rw [E.toTensorPagesData.target_bot]
  exact (Subobject.mapIsoToOrderIso (E.targetIso n)).map_bot

@[simp] theorem targetPiece_top (n : ℕ) : E.targetPiece n n = ⊤ := by
  change Subobject.mapIsoToOrderIso (E.targetIso n)
    (FiniteFiltrationConvergence.cohomologyPiece E.filtration (-(n : ℤ)) (-(n : ℤ))) = ⊤
  rw [E.toTensorPagesData.target_top]
  exact (Subobject.mapIsoToOrderIso (E.targetIso n)).map_top

theorem targetPiece_finite (n : ℕ) : ∃ a b : ℤ,
    (∀ p, p ≤ a → E.targetPiece p n = ⊥) ∧
    (∀ p, b ≤ p → E.targetPiece p n = ⊤) := by
  obtain ⟨a,b,ha,hb⟩ := chainTargetPiece_finite E.filtration E.convergence (n : ℤ)
  refine ⟨a,b,?_,?_⟩
  · intro p hp
    change Subobject.mapIsoToOrderIso (E.targetIso n) (chainTargetPiece E.filtration p (n : ℤ)) = ⊥
    rw [ha p hp]
    exact (Subobject.mapIsoToOrderIso (E.targetIso n)).map_bot
  · intro p hp
    change Subobject.mapIsoToOrderIso (E.targetIso n) (chainTargetPiece E.filtration p (n : ℤ)) = ⊤
    rw [hb p hp]
    exact (Subobject.mapIsoToOrderIso (E.targetIso n)).map_top
/-- The stabilized page is the actual successive quotient of the Tor target filtration. -/
def targetLimitIso (n : ℕ) (r : ℤ) (hr : 0 ≤ r) (p : ℤ)
    (hs : FiniteFiltrationConvergence.Stabilized E.filtration r (-p) (-(n : ℤ))) :
    chainPage E.filtration E.pages r p (n : ℤ) ≅
      cokernel (Subobject.ofLE (E.targetPiece (p-1) n) (E.targetPiece p n)
        (E.targetPiece_increasing p n)) :=
  mappedChainPageLimitIso E.filtration E.pages (n : ℤ) (E.targetIso n)
    E.convergence r hr p hs

end ResolvedSequenceData


end ResolvedAssembly


section CanonicalPages

open FiniteDiagonalFiltrations DoubleTotalization
variable {R : Type u} [Ring R]
variable {C C' C'' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
variable {Q Q' Q'' : ChainComplex (ModuleCat.{w} R) ℕ}
variable [(tensorCochainBicomplex C Q).HasTotal (ComplexShape.up ℤ)]
variable [(tensorCochainBicomplex C' Q').HasTotal (ComplexShape.up ℤ)]
variable [(tensorCochainBicomplex C'' Q'').HasTotal (ComplexShape.up ℤ)]

/-- Canonical row identifications on a chosen actual row filtration. -/
def canonicalTensorPagesData (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (Q : ChainComplex (ModuleCat.{w} R) ℕ)
    [(tensorCochainBicomplex C Q).HasTotal (ComplexShape.up ℤ)] : TensorPagesData C Q :=
  let B := Classical.choice (tensor_pages R C Q)
  { B with firstPages := ((DoubleComplexFirstPages.system _).row
      (tensorCochainBicomplex C Q) (tensorCochainBicomplex_finite C Q)
      B.filtration B.formula B.pages) }

@[simp] theorem canonicalTensorPagesData_firstPages :
    (canonicalTensorPagesData C Q).firstPages =
      (DoubleComplexFirstPages.system _).row
        (tensorCochainBicomplex C Q) (tensorCochainBicomplex_finite C Q)
        (canonicalTensorPagesData C Q).filtration
        (canonicalTensorPagesData C Q).formula
        (canonicalTensorPagesData C Q).pages := rfl

namespace TensorPagesData
variable (B : TensorPagesData C Q) (B' : TensorPagesData C' Q') (B'' : TensorPagesData C'' Q'')

/-- The filtered map determined by a pair of maps of the tensor factors. -/
def filteredMap (l : C ⟶ C') (m : Q ⟶ Q') :
    FilteredMap ⟨_, B.filtration⟩ ⟨_, B'.filtration⟩ :=
  (tensorCochainBicomplex_filteredMap B.filtration B'.filtration B.formula B'.formula l m).choose

@[simp] theorem filteredMap_hom (l : C ⟶ C') (m : Q ⟶ Q') :
    (B.filteredMap B' l m).hom =
      HomologicalComplex₂.total.map (tensorCochainBicomplexMap l m) (ComplexShape.up ℤ) :=
  (tensorCochainBicomplex_filteredMap B.filtration B'.filtration B.formula B'.formula l m).choose_spec

@[simp] theorem filteredMap_id : B.filteredMap B (𝟙 C) (𝟙 Q) = FilteredMap.id _ := by
  apply FilteredMap.ext
  simp only [filteredMap_hom, tensorCochainBicomplexMap_id,
    HomologicalComplex₂.total.map_id, FilteredMap.id]

@[simp] theorem filteredMap_comp (l : C ⟶ C') (l' : C' ⟶ C'')
    (m : Q ⟶ Q') (m' : Q' ⟶ Q'') :
    B.filteredMap B'' (l ≫ l') (m ≫ m') =
      (B.filteredMap B' l m).comp (B'.filteredMap B'' l' m') := by
  apply FilteredMap.ext
  simp only [filteredMap_hom, FilteredMap.comp,
    tensorCochainBicomplexMap_comp, HomologicalComplex₂.total.map_comp]

/-- The induced maps of the actual quotient pages. -/
abbrev mapData (l : C ⟶ C') (m : Q ⟶ Q') :=
  FilteredPageFunctoriality.mapData (B.filteredMap B' l m) B.pages B'.pages

@[simp] theorem mapData_id (r p n : ℤ) :
    (B.mapData B (𝟙 C) (𝟙 Q)).map r p n = 𝟙 _ := by
  dsimp only [mapData, FilteredPageFunctoriality.mapData]
  rw [filteredMap_id, FilteredPageFunctoriality.pageMap_id]

@[simp] theorem mapData_comp (l : C ⟶ C') (l' : C' ⟶ C'')
    (m : Q ⟶ Q') (m' : Q' ⟶ Q'') (r p n : ℤ) :
    (B.mapData B'' (l ≫ l') (m ≫ m')).map r p n =
      (B.mapData B' l m).map r p n ≫ (B'.mapData B'' l' m').map r p n := by
  dsimp only [mapData, FilteredPageFunctoriality.mapData]
  rw [filteredMap_comp B B' B'', FilteredPageFunctoriality.pageMap_comp]
end TensorPagesData

end CanonicalPages


section HorizontalMapCompatibility

open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Flat homology comparison is natural also in its complex. -/
theorem flatQuotientHomologyIso_complex_naturality
    {T : Type u} [Ring T] (N : Type x) [AddCommGroup N] [Module T N]
    (hN : P103.Specs.Ch02.FlatnessTests.Flat.{u,x,w} T N)
    {ι : Type*} (c : ComplexShape ι)
    {C D : HomologicalComplex (ModuleCat.{w} Tᵐᵒᵖ) c} (l : C ⟶ D) (n : ι) :
    (tensorFunctor N).map (ModuleCat.ofHom (homologyMap l n)) ≫
      (flatQuotientHomologyIso N hN c D n).hom =
    (flatQuotientHomologyIso N hN c C n).hom ≫
      ModuleCat.ofHom (homologyMap (((tensorFunctor N).mapHomologicalComplex c).map l) n) := by
  letI := TorBalance.flat_tensor_preservesHomology hN
  let F := (tensorFunctor N : ModuleCat.{w} Tᵐᵒᵖ ⥤ ModuleCat.{max w x} ℤ)
  let l' := (F.mapHomologicalComplex c).map l
  let C' := (F.mapHomologicalComplex c).obj C
  let D' := (F.mapHomologicalComplex c).obj D
  have hq : HomologicalComplex.homologyMap l' n ≫ (explicitToCategoricalHomologyIso D' n).inv =
      (explicitToCategoricalHomologyIso C' n).inv ≫ ModuleCat.ofHom (homologyMap l' n) := by
    apply (cancel_mono (explicitToCategoricalHomologyIso D' n).hom).mp
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, explicitToCategoricalHomologyIso_naturality, Iso.inv_hom_id_assoc]
  have ha := congrArg F.map (explicitToCategoricalHomologyIso_naturality l n)
  simp only [F.map_comp] at ha
  have hb := (TorBalance.exactHomologyComparison F).naturality (HomologicalComplex.shortComplexFunctor _ _ n |>.map l)
  change F.map (ModuleCat.ofHom (homologyMap l n)) ≫ F.map (explicitToCategoricalHomologyIso D n).hom ≫
    ((TorBalance.exactHomologyComparison F).equivalence (D.sc n)).hom ≫
      (explicitToCategoricalHomologyIso D' n).inv =
    F.map (explicitToCategoricalHomologyIso C n).hom ≫
      ((TorBalance.exactHomologyComparison F).equivalence (C.sc n)).hom ≫
        (explicitToCategoricalHomologyIso C' n).inv ≫ ModuleCat.ofHom (homologyMap l' n)
  rw [← Category.assoc _ (F.map (explicitToCategoricalHomologyIso D n).hom), ha, Category.assoc]
  erw [← Category.assoc _ ((TorBalance.exactHomologyComparison F).equivalence (D.sc n)).hom, hb,
    Category.assoc]
  erw [hq]

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
/-- The horizontal computation intertwines maps of right complexes. -/
theorem horizontalHomologyIso_complex_naturality
    {C D : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ} (l : C ⟶ D)
    (N : Type (max v x)) [AddCommGroup N] [Module S N]
    (hN : P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S N) (n : ℕ) :
    letI := innerTorModule f C n
    letI := innerTorModule f D n
    ModuleCat.ofHom (tensorMap (innerTorMap f l n) (LinearMap.id : N →ₗ[S] N)) ≫
      (horizontalHomologyIso f D N hN n).toModuleIso.hom =
    (horizontalHomologyIso f C N hN n).toModuleIso.hom ≫
      ModuleCat.ofHom (homologyMap (tensorFirstMap l (Restricted f N)) n) := by
  letI := innerTorModule f C n
  letI := innerTorModule f D n
  let E := (extensionComplexData f C).complex
  let E' := (extensionComplexData f D).complex
  let k := ((scalarExtension f).mapHomologicalComplex (ComplexShape.down ℕ)).map l
  let F := (tensorFunctor N : ModuleCat.{max w v} Sᵐᵒᵖ ⥤ ModuleCat.{max w v x} ℤ)
  let H := P103.Specs.Ch10.Comparison.quotientHomology (S := ℤ) (ComplexShape.down ℕ) n
  let a := F.mapIso (innerTorEquiv f C n).symm.toModuleIso
  let a' := F.mapIso (innerTorEquiv f D n).symm.toModuleIso
  let b := flatQuotientHomologyIso N hN (ComplexShape.down ℕ) E n
  let b' := flatQuotientHomologyIso N hN (ComplexShape.down ℕ) E' n
  let d := H.mapIso (reassociationComplexIso f N (ComplexShape.down ℕ) C)
  let d' := H.mapIso (reassociationComplexIso f N (ComplexShape.down ℕ) D)
  let m := ModuleCat.ofHom (tensorMap (innerTorMap f l n) (LinearMap.id : N →ₗ[S] N))
  have ha : m ≫ a'.hom = a.hom ≫ F.map (ModuleCat.ofHom (homologyMap k n)) := by
    change F.map (ModuleCat.ofHom (innerTorMap f l n)) ≫
        F.map (innerTorEquiv f D n).toModuleIso.inv =
      F.map (innerTorEquiv f C n).toModuleIso.inv ≫ F.map (ModuleCat.ofHom (homologyMap k n))
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (innerTorEquiv f D n).symm (innerTorMap f l n z) =
      homologyMap k n ((innerTorEquiv f C n).symm z)
    simp only [innerTorMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rfl
  have hb := flatQuotientHomologyIso_complex_naturality N hN (ComplexShape.down ℕ) k n
  have hd : H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map k) ≫ d'.hom =
      d.hom ≫ H.map (tensorFirstMap l (Restricted f N)) := by
    change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    exact ((Functor.mapHomologicalComplexCompIso (reassociationNatIso f N)
      (ComplexShape.down ℕ)).hom.naturality l)
  change m ≫ a'.hom ≫ b'.hom ≫ d'.hom =
    a.hom ≫ b.hom ≫ d.hom ≫ H.map (tensorFirstMap l (Restricted f N))
  rw [← Category.assoc m a'.hom, ha, Category.assoc,
    ← Category.assoc _ b'.hom]
  erw [hb, Category.assoc, hd]
  rfl


end HorizontalMapCompatibility


section HorizontalComplexCompatibility

open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
/-- On first-page complexes the right-complex map is the inner Tor map. -/
theorem rowHomologyComplexIso_complex_naturality
    {C D : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ} (l : C ⟶ D)
    (Q : ChainComplex (ModuleCat.{max v x} S) ℕ)
    (hQ : ∀ p, P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S (Q.X p)) (q : ℕ) :
    letI := innerTorModule f C q
    letI := innerTorModule f D q
    leftTensorFirstMap (innerTorMap f l q) Q ≫
      (rowHomologyComplexIso.{u,v,w,x} f D Q hQ q).hom =
    (rowHomologyComplexIso.{u,v,w,x} f C Q hQ q).hom ≫ rowHomologyMap.{u,v,w,x} f l Q q := by
  apply HomologicalComplex.Hom.ext
  funext p
  exact horizontalHomologyIso_complex_naturality.{u,v,w,x} f l (Q.X p) (hQ p) q

/-- The row-complex identification is natural in every map of flat coefficient complexes. -/
theorem rowHomologyComplexIso_coefficient_naturality
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    {Q Q' : ChainComplex (ModuleCat.{max v x} S) ℕ} (m : Q ⟶ Q')
    (hQ : ∀ p, P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S (Q.X p))
    (hQ' : ∀ p, P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S (Q'.X p)) (q : ℕ) :
    letI := innerTorModule f C q
    ((leftTensorFunctor (Homology (tensorComplex C (Restricted f S)) q)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map m ≫ (rowHomologyComplexIso.{u,v,w,x} f C Q' hQ' q).hom =
    (rowHomologyComplexIso.{u,v,w,x} f C Q hQ q).hom ≫
      ((((restrictionFunctor f ⋙ tensorCoefficientComplex C) ⋙
        quotientHomology (ComplexShape.down ℕ) q).mapHomologicalComplex
          (ComplexShape.down ℕ)).map m) := by
  apply HomologicalComplex.Hom.ext
  funext p
  exact horizontalHomologyIso_naturality.{u,v,w,x} f C (hQ p) (hQ' p) (m.f p).hom q

/-- Simultaneous naturality of the first-page complex calculation. -/
theorem rowHomologyComplexIso_naturality
    {C D : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ} (l : C ⟶ D)
    {Q Q' : ChainComplex (ModuleCat.{max v x} S) ℕ} (m : Q ⟶ Q')
    (hQ : ∀ p, P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S (Q.X p))
    (hQ' : ∀ p, P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S (Q'.X p)) (q : ℕ) :
    letI := innerTorModule f C q
    letI := innerTorModule f D q
    leftTensorMap (innerTorMap f l q) m ≫
      (rowHomologyComplexIso.{u,v,w,x} f D Q' hQ' q).hom =
    (rowHomologyComplexIso.{u,v,w,x} f C Q hQ q).hom ≫ rowHomologyMap.{u,v,w,x} f l Q q ≫
      ((((restrictionFunctor f ⋙ tensorCoefficientComplex D) ⋙
        quotientHomology (ComplexShape.down ℕ) q).mapHomologicalComplex
          (ComplexShape.down ℕ)).map m) := by
  dsimp only [leftTensorMap]
  rw [Category.assoc, rowHomologyComplexIso_coefficient_naturality,
    ← Category.assoc, rowHomologyComplexIso_complex_naturality, Category.assoc]

end HorizontalComplexCompatibility


section OuterTorCompatibility

open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
/-- The outer Tor identification intertwines its ordinary maps in both variables. -/
theorem rowHomologyTorEquiv_naturality
    {C D : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ} (l : C ⟶ D)
    {M N : Type (max v x)} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N]
    (Q : LeftResolution S M) (Q' : LeftResolution S N)
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (g : M →ₗ[S] N) (m : Q.complex ⟶ Q'.complex) (hm : ChainLift Q Q' g m) (q : ℕ) :
    letI := innerTorModule f C q
    letI := innerTorModule f D q
    ∀ (U : LeftResolution Sᵐᵒᵖ (Homology (tensorComplex C (Restricted f S)) q))
      (U' : LeftResolution Sᵐᵒᵖ (Homology (tensorComplex D (Restricted f S)) q))
      (hU : U.IsProjective) (hU' : U'.IsProjective)
      (u : U.complex ⟶ U'.complex) (hu : ChainLift U U' (innerTorMap f l q) u) (p : ℕ),
    ModuleCat.ofHom (homologyMap (rowHomologyMap.{u,v,w,max v x} f l Q.complex q ≫
      ((((restrictionFunctor f ⋙ tensorCoefficientComplex D) ⋙ quotientHomology (ComplexShape.down ℕ) q).mapHomologicalComplex (ComplexShape.down ℕ)).map m)) p) ≫
      (rowHomologyTorEquiv.{u,v,w,x} f D N Q' hQ' q U' hU' p).toModuleIso.hom =
    (rowHomologyTorEquiv.{u,v,w,x} f C M Q hQ q U hU p).toModuleIso.hom ≫
      ModuleCat.ofHom (homologyMap (tensorFirstMap u M ≫ tensorSecondMap U'.complex g) p) := by
  letI := innerTorModule f C q
  letI := innerTorModule f D q
  intro U U' hU hU' u hu p
  let hQflat := fun j => P103.Ch02.FlatnessTests.projective_flat S (Q.complex.X j) (hQ j)
  let hQflat' := fun j => P103.Ch02.FlatnessTests.projective_flat S (Q'.complex.X j) (hQ' j)
  let e := rowHomologyComplexIso.{u,v,w,x} f C Q.complex hQflat q
  let e' := rowHomologyComplexIso.{u,v,w,x} f D Q'.complex hQflat' q
  let k := rowHomologyMap.{u,v,w,max v x} f l Q.complex q ≫
    ((((restrictionFunctor f ⋙ tensorCoefficientComplex D) ⋙ quotientHomology (ComplexShape.down ℕ) q).mapHomologicalComplex (ComplexShape.down ℕ)).map m)
  let a := leftTensorMap (innerTorMap f l q) m
  let H := quotientHomology (S := ℤ) (ComplexShape.down ℕ) p
  have he : H.map k ≫ H.map e'.inv = H.map e.inv ≫ H.map a := by
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id_assoc]
    have h := rowHomologyComplexIso_naturality.{u,v,w,x} f l m hQflat hQflat' q
    change a ≫ e'.hom = e.hom ≫ k at h
    change (e.hom ≫ k) ≫ e'.inv = a
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let HB := TorBalance.balance S (Homology (tensorComplex C (Restricted f S)) q) M U Q hU hQ
  let HB' := TorBalance.balance S (Homology (tensorComplex D (Restricted f S)) q) N U' Q' hU' hQ'
  let b := (balanceEquiv HB.choose HB.choose_spec.1 HB.choose_spec.2 p).toModuleIso
  let b' := (balanceEquiv HB'.choose HB'.choose_spec.1 HB'.choose_spec.2 p).toModuleIso
  let t := ModuleCat.ofHom (homologyMap (tensorFirstMap u M ≫ tensorSecondMap U'.complex g) p)
  have hb : t ≫ b'.hom = b.hom ≫ H.map a := by
    apply ModuleCat.hom_ext
    exact TorBalance.balance_naturality S _ _ M N U U' Q Q'
      (innerTorMap f l q) g u m hu hm HB.choose HB'.choose
      HB.choose_spec.1 HB.choose_spec.2 HB'.choose_spec.1 HB'.choose_spec.2 p
  have hb' : H.map a ≫ b'.inv = b.inv ≫ t := by
    apply (cancel_epi b.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id_assoc]
    erw [← hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change H.map k ≫ (H.map e'.inv ≫ b'.inv) = (H.map e.inv ≫ b.inv) ≫ t
  rw [← Category.assoc, he, Category.assoc, hb', Category.assoc]

end OuterTorCompatibility

end AdvancedHomologicalAlgebra.ChangeOfRingsTor

noncomputable section
namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Ch11.TorBalance

theorem homologyMap_index_natural {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
    (t : K ⟶ L) {i j : ι} (h : i = j) :
    HomologicalComplex.homologyMap t i ≫ eqToHom (congrArg (fun j => L.homology j) h) =
      eqToHom (congrArg (fun j => K.homology j) h) ≫ HomologicalComplex.homologyMap t j := by
  subst j
  simp

section
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
variable {A A' : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A']
variable {M M' : Type (max u v x)} [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M']
variable {P : LeftResolution Rᵐᵒᵖ A} {P' : LeftResolution Rᵐᵒᵖ A'}
    {Q : LeftResolution S M} {Q' : LeftResolution S M'}
variable (g : M →ₗ[S] M') (l : P.complex ⟶ P'.complex) (m : Q.complex ⟶ Q'.complex)
    (hm : ChainLift Q Q' g m)
    (α : TargetComparisonData f A M P Q) (β : TargetComparisonData f A' M' P' Q')

include hm

/-- The integer-total comparison commutes with simultaneous lifted maps. -/
theorem target_integerHomologyEquiv_natural (n : ℕ) (z) :
    β.integerHomologyEquiv n
      (homologyMap (tensorTotalMap
        (HomologicalComplex.extendMap l nonnegativeChainEmbedding)
        (HomologicalComplex.extendMap (restrictionResolutionMap (f := f) m)
          nonnegativeChainEmbedding)) (n : ℤ) z) =
    homologyMap (tensorFirstMap l (Restricted f M) ≫
      tensorSecondMap P'.complex (Restricted.map f g)) n (α.integerHomologyEquiv n z) := by
  let t := tensorTotalMap
    (HomologicalComplex.extendMap l nonnegativeChainEmbedding)
    (HomologicalComplex.extendMap (restrictionResolutionMap (f := f) m)
      nonnegativeChainEmbedding)
  let e := restrictionHomologyEquiv
    (ordinaryTensorTotal P.complex (restrictionResolution f M Q).complex) α.totalSupported n
  let e' := restrictionHomologyEquiv
    (ordinaryTensorTotal P'.complex (restrictionResolution f M' Q').complex) β.totalSupported n
  have h := restrictionHomologyEquiv_natural α.totalSupported β.totalSupported t n
  have he : e'.symm (homologyMap t (n : ℤ) z) =
      homologyMap (ordinaryTotalMap l (restrictionResolutionMap (f := f) m)) n (e.symm z) := by
    apply e'.injective
    have hh := congrArg (fun k => k (e.symm z)) h
    change e' (homologyMap (ordinaryTotalMap l (restrictionResolutionMap (f := f) m)) n
      (e.symm z)) = homologyMap t (n : ℤ) (e (e.symm z)) at hh
    rw [e.apply_symm_apply] at hh
    rw [e'.apply_symm_apply]
    exact hh.symm
  change β.homologyEquiv n (e'.symm (homologyMap t (n : ℤ) z)) =
    homologyMap (tensorFirstMap l (Restricted f M) ≫
      tensorSecondMap P'.complex (Restricted.map f g)) n (α.homologyEquiv n (e.symm z))
  rw [he]
  exact target_homologyEquiv_natural g l m hm α β n (e.symm z)

/-- The categorical integer-total comparison commutes with lifted maps. -/
theorem target_categoricalIntegerHomologyIso_natural (n : ℕ) :
    HomologicalComplex.homologyMap (tensorTotalMap
        (HomologicalComplex.extendMap l nonnegativeChainEmbedding)
        (HomologicalComplex.extendMap (restrictionResolutionMap (f := f) m)
          nonnegativeChainEmbedding)) (n : ℤ) ≫
      (β.categoricalIntegerHomologyIso n).hom =
    (α.categoricalIntegerHomologyIso n).hom ≫
      ModuleCat.ofHom (homologyMap (tensorFirstMap l (Restricted f M) ≫
        tensorSecondMap P'.complex (Restricted.map f g)) n) := by
  let t := tensorTotalMap
    (HomologicalComplex.extendMap l nonnegativeChainEmbedding)
    (HomologicalComplex.extendMap (restrictionResolutionMap (f := f) m)
      nonnegativeChainEmbedding)
  let HZ := P103.Specs.Ch10.Comparison.quotientHomology (S := ℤ) (ComplexShape.down ℤ) (n : ℤ)
  let a := explicitToCategoricalHomologyIso
    (ordinaryTensorTotal P.complex (restrictionResolution f M Q).complex) (n : ℤ)
  let a' := explicitToCategoricalHomologyIso
    (ordinaryTensorTotal P'.complex (restrictionResolution f M' Q').complex) (n : ℤ)
  have ha : HomologicalComplex.homologyMap t (n : ℤ) ≫ a'.inv =
      a.inv ≫ HZ.map t := by
    apply (cancel_mono a'.hom).mp
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      explicitToCategoricalHomologyIso_naturality, Iso.inv_hom_id_assoc]
  have hb : HZ.map t ≫
      (β.integerHomologyEquiv n).toModuleIso.hom =
      (α.integerHomologyEquiv n).toModuleIso.hom ≫
        ModuleCat.ofHom (homologyMap (tensorFirstMap l (Restricted f M) ≫
          tensorSecondMap P'.complex (Restricted.map f g)) n) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact target_integerHomologyEquiv_natural g l m hm α β n
  change HomologicalComplex.homologyMap t (n : ℤ) ≫
      (a'.inv ≫ (β.integerHomologyEquiv n).toModuleIso.hom) =
    (a.inv ≫ (α.integerHomologyEquiv n).toModuleIso.hom) ≫ _
  rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]

variable [(tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex).HasTotal
    (ComplexShape.up ℤ)]
    [(tensorCochainBicomplex P'.complex (restrictionResolution f M' Q').complex).HasTotal
    (ComplexShape.up ℤ)]

end
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

noncomputable section
namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open FiniteFiltrationConvergence

section TransportedNaturality
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : FilteredComplex C} (f : FilteredMap X Y)
variable {H H' : C} (n : ℤ) (e : X.complex.homology n ≅ H)
    (e' : Y.complex.homology n ≅ H')

/-- The map of image filtration steps transported along the specified target identifications. -/
def transportedCohomologyStepMap (p : ℤ) :
    (Subobject.mapIsoToOrderIso e (cohomologyPiece X.filtration p n) : C) ⟶
      (Subobject.mapIsoToOrderIso e' (cohomologyPiece Y.filtration p n) : C) :=
  (mappedSubobjectIso e (cohomologyPiece X.filtration p n)).inv ≫
    cohomologyStepMap f p n ≫
      (mappedSubobjectIso e' (cohomologyPiece Y.filtration p n)).hom

/-- A natural target comparison makes the transported step map a restriction of the target map. -/
@[reassoc (attr := simp)]
theorem transportedCohomologyStepMap_arrow (k : H ⟶ H')
    (h : HomologicalComplex.homologyMap f.hom n ≫ e'.hom = e.hom ≫ k) (p : ℤ) :
    transportedCohomologyStepMap f n e e' p ≫
      (Subobject.mapIsoToOrderIso e' (cohomologyPiece Y.filtration p n)).arrow =
    (Subobject.mapIsoToOrderIso e (cohomologyPiece X.filtration p n)).arrow ≫ k := by
  dsimp only [transportedCohomologyStepMap]
  simp only [Category.assoc, mappedSubobjectIso_hom_arrow,
    cohomologyStepMap_arrow_assoc]
  rw [h, ← mappedSubobjectIso_hom_arrow_assoc,
    Iso.inv_hom_id_assoc]
end TransportedNaturality
end AdvancedHomologicalAlgebra.ChangeOfRingsTor
namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open FiniteFiltrationConvergence
section
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
variable {A A' : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A']
variable {M M' : Type (max u v x)} [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M']
variable {P : LeftResolution Rᵐᵒᵖ A} {P' : LeftResolution Rᵐᵒᵖ A'}
    {Q : LeftResolution S M} {Q' : LeftResolution S M'}
variable [(tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex).HasTotal
    (ComplexShape.up ℤ)]
    [(tensorCochainBicomplex P'.complex (restrictionResolution f M' Q').complex).HasTotal
    (ComplexShape.up ℤ)]
variable (g : M →ₗ[S] M') (l : P.complex ⟶ P'.complex) (m : Q.complex ⟶ Q'.complex)
    (hm : ChainLift Q Q' g m)
    (α : TargetComparisonData f A M P Q) (β : TargetComparisonData f A' M' P' Q')
variable (F : Filtration (DoubleTotalization.sumTotal
    (tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex)))
    (G : Filtration (DoubleTotalization.sumTotal
    (tensorCochainBicomplex P'.complex (restrictionResolution f M' Q').complex)))
    (hF : FiniteDiagonalFiltrations.HasFiltrationFormula
      (tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex) Prod.snd F)
    (hG : FiniteDiagonalFiltrations.HasFiltrationFormula
      (tensorCochainBicomplex P'.complex (restrictionResolution f M' Q').complex) Prod.snd G)

include hm hF hG

/-- The induced ordinary Tor map preserves the actual target filtration. -/
theorem target_filtration_map_exists (p : ℤ) (n : ℕ) :
    ∃ k :
      (Subobject.mapIsoToOrderIso (α.cochainHomologyIso n) (chainTargetPiece F p n) : ModuleCat ℤ) ⟶
        (Subobject.mapIsoToOrderIso (β.cochainHomologyIso n) (chainTargetPiece G p n) : ModuleCat ℤ),
      k ≫ (Subobject.mapIsoToOrderIso (β.cochainHomologyIso n) (chainTargetPiece G p n)).arrow =
      (Subobject.mapIsoToOrderIso (α.cochainHomologyIso n) (chainTargetPiece F p n)).arrow ≫
        ModuleCat.ofHom (homologyMap (tensorFirstMap l (Restricted f M) ≫
          tensorSecondMap P'.complex (Restricted.map f g)) n) := by
  obtain ⟨φ,hφ⟩ := tensorCochainBicomplex_filteredMap F G hF hG l
    (restrictionResolutionMap (f := f) m)
  refine ⟨transportedCohomologyStepMap φ (-(n : ℤ))
    (α.cochainHomologyIso n) (β.cochainHomologyIso n) (-p), ?_⟩
  apply transportedCohomologyStepMap_arrow
  rw [hφ]
  exact target_cochainHomologyIso_natural g l m hm α β n
/-- The direct image of every target filtration step lies in the corresponding target step. -/
theorem target_filtration_preserved (p : ℤ) (n : ℕ) :
    (Subobject.«exists» (ModuleCat.ofHom (homologyMap
      (tensorFirstMap l (Restricted f M) ≫
        tensorSecondMap P'.complex (Restricted.map f g)) n))).obj
      (Subobject.mapIsoToOrderIso (α.cochainHomologyIso n) (chainTargetPiece F p n)) ≤
    Subobject.mapIsoToOrderIso (β.cochainHomologyIso n) (chainTargetPiece G p n) := by
  obtain ⟨k,hk⟩ := target_filtration_map_exists g l m hm α β F G hF hG p n
  exact Subobject.exists_le_of_comm _ k hk

end
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
section ExtendedHomologyNaturality

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance P103.Ch11.TorBalance
open DoubleComplexFirstPages
set_option maxHeartbeats 1500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace E2Bridge
variable {T : Type u} [Ring T] {U : Type x} [Ring U]
variable {C C' : ChainComplex (ModuleCat.{v} T) ℕ}
variable (F : ModuleCat.{v} T ⥤ ModuleCat.{w} U) [F.Additive]
theorem restrictExtendMapIso_chain_naturality (l : C ⟶ C') :
    HomologicalComplex.restrictionMap
      ((F.mapHomologicalComplex (ComplexShape.down ℤ)).map (HomologicalComplex.extendMap l nonnegativeChainEmbedding))
      nonnegativeChainEmbedding ≫ (restrictExtendMapIso C' F).hom =
    (restrictExtendMapIso C F).hom ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map l := by
  apply HomologicalComplex.Hom.ext
  funext n
  change F.map ((HomologicalComplex.extendMap l nonnegativeChainEmbedding).f (n:ℤ)) ≫
      F.map _ = F.map _ ≫ F.map (l.f n)
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  erw [HomologicalComplex.extendMap_f l nonnegativeChainEmbedding (i := n) rfl]
  simp

theorem mappedExtendHomologyIso_chain_naturality (l : C ⟶ C') (p : ℕ) :
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.down ℤ)).map
        (HomologicalComplex.extendMap l nonnegativeChainEmbedding)) (p : ℤ) ≫
      (mappedExtendHomologyIso C' F p).hom =
    (mappedExtendHomologyIso C F p).hom ≫ ModuleCat.ofHom
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map l) p) := by
  let E := (F.mapHomologicalComplex (ComplexShape.down ℤ)).obj (extendNonnegativeChain C)
  let E' := (F.mapHomologicalComplex (ComplexShape.down ℤ)).obj (extendNonnegativeChain C')
  let lZ := (F.mapHomologicalComplex (ComplexShape.down ℤ)).map (HomologicalComplex.extendMap l nonnegativeChainEmbedding)
  let lN := HomologicalComplex.restrictionMap lZ nonnegativeChainEmbedding
  let HZ := P103.Specs.Ch10.Comparison.quotientHomology (S := U) (ComplexShape.down ℤ) (p : ℤ)
  let HN := P103.Specs.Ch10.Comparison.quotientHomology (S := U) (ComplexShape.down ℕ) p
  let a := explicitToCategoricalHomologyIso E (p : ℤ)
  let a' := explicitToCategoricalHomologyIso E' (p : ℤ)
  let b := (restrictionHomologyEquiv E (mappedExtend_support C F) p).toModuleIso
  let b' := (restrictionHomologyEquiv E' (mappedExtend_support C' F) p).toModuleIso
  let d := HN.mapIso (restrictExtendMapIso C F)
  let d' := HN.mapIso (restrictExtendMapIso C' F)
  have ha : HomologicalComplex.homologyMap lZ (p : ℤ) ≫ a'.inv = a.inv ≫ HZ.map lZ := by
    apply (cancel_mono a'.hom).mp
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      explicitToCategoricalHomologyIso_naturality, Iso.inv_hom_id_assoc]
  have hbb : HN.map lN ≫ b'.hom = b.hom ≫ HZ.map lZ := by
    exact congrArg ModuleCat.ofHom
      (restrictionHomologyEquiv_natural (mappedExtend_support C F) (mappedExtend_support C' F) lZ p)
  have hb : HZ.map lZ ≫ b'.inv = b.inv ≫ HN.map lN := by
    apply (cancel_mono b'.hom).mp
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hbb,
      Iso.inv_hom_id_assoc]
  have hd : HN.map lN ≫ d'.hom = d.hom ≫
      HN.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map l) := by
    change HN.map lN ≫ HN.map _ = HN.map _ ≫ HN.map _
    rw [← HN.map_comp, ← HN.map_comp, restrictExtendMapIso_chain_naturality]
  change HomologicalComplex.homologyMap lZ (p : ℤ) ≫ a'.inv ≫ b'.inv ≫ d'.hom =
    a.inv ≫ b.inv ≫ d.hom ≫ HN.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map l)
  rw [← Category.assoc _ a'.inv, ha, Category.assoc, ← Category.assoc _ b'.inv,
    hb, Category.assoc, hd]
end E2Bridge

end ExtendedHomologyNaturality
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
section RawE2Naturality

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance P103.Ch11.TorBalance
open DoubleComplexFirstPages
set_option maxHeartbeats 1500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [Ring R]
variable {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
variable {D D' : ChainComplex (ModuleCat.{w} R) ℕ}

def integerTensorMap (l : C ⟶ C') (m : D ⟶ D') :=
  tensorBicomplexMap (HomologicalComplex.extendMap l nonnegativeChainEmbedding)
    (HomologicalComplex.extendMap m nonnegativeChainEmbedding)

abbrev flippedIntegerTensorMap (l : C ⟶ C') (m : D ⟶ D') :=
  (HomologicalComplex₂.flipFunctor _ (ComplexShape.down ℤ) (ComplexShape.down ℤ)).map (integerTensorMap l m)

abbrev flippedCochainTensorMap (l : C ⟶ C') (m : D ⟶ D') :=
  (HomologicalComplex₂.flipFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map (tensorCochainBicomplexMap l m)

theorem reversedHorizontalHomologyIso_naturality (l : C ⟶ C') (m : D ⟶ D') (q : ℕ) :
    verticalHomologyMap _ (flippedCochainTensorMap l m) (-(q:ℤ)) ≫
      (reversedHorizontalHomologyIso C' D' q).hom =
    (reversedHorizontalHomologyIso C D q).hom ≫ HomologicalComplex.restrictionMap
      (((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q:ℤ)).mapHomologicalComplex
        (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l m)) negChainEmbedding := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact (reverseHomologyNatIsoE2 (A := ModuleCat.{max v w} ℤ) (q:ℤ)).hom.naturality
    ((flippedIntegerTensorMap l m).f (-i))

-- For homotopy in first variable the inner categorical homology map agrees.
theorem integer_horizontal_homology_eq_first
    (l l' : C ⟶ C') (h : Homotopy l l') (m : D ⟶ D') (q : ℤ) :
    ((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) q).mapHomologicalComplex
        (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l m) =
    ((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) q).mapHomologicalComplex
        (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l' m) := by
  apply HomologicalComplex.Hom.ext
  funext i
  let F := tensorFunctor (R := R) ((extendNonnegativeChain D).X i)
  let mZ := HomologicalComplex.extendMap m nonnegativeChainEmbedding
  let τ := TorBalance.tensorCoefficientMap (mZ.f i).hom
  have hh := (F.mapHomotopy (h.extend nonnegativeChainEmbedding)).homologyMap_eq q
  have he (k : C ⟶ C') : (flippedIntegerTensorMap k m).f i =
      (F.mapHomologicalComplex (ComplexShape.down ℤ)).map
        (HomologicalComplex.extendMap k nonnegativeChainEmbedding) ≫
      (τ.mapHomologicalComplex (ComplexShape.down ℤ)).app (extendNonnegativeChain C') := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  change HomologicalComplex.homologyMap ((flippedIntegerTensorMap l m).f i) q =
    HomologicalComplex.homologyMap ((flippedIntegerTensorMap l' m).f i) q
  rw [he l, he l', HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, hh]


def tensorCochainE2IntegerIso
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q : ℕ) :
    (verticalHomology (tensorCochainBicomplex C D).flip (-(q:ℤ))).homology (-(p:ℤ)) ≅
    (((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q:ℤ)).mapHomologicalComplex
        (ComplexShape.down ℤ)).obj
      (P103.Specs.Ch11.TorBalance.tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)).flip).homology (p:ℤ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.up ℤ) (-(p:ℤ))).mapIso
    (reversedHorizontalHomologyIso C D q) ≪≫
      (reverseHomologyNatIsoE2 (p:ℤ)).app _

theorem tensorCochainE2IntegerIso_naturality (l : C ⟶ C') (m : D ⟶ D') (p q : ℕ) :
    HomologicalComplex.homologyMap
      (verticalHomologyMap _ (flippedCochainTensorMap l m) (-(q:ℤ))) (-(p:ℤ)) ≫
      (tensorCochainE2IntegerIso C' D' p q).hom =
    (tensorCochainE2IntegerIso C D p q).hom ≫ HomologicalComplex.homologyMap
      (((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q:ℤ)).mapHomologicalComplex
        (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l m)) (p:ℤ) := by
  have he := congrArg (fun z => HomologicalComplex.homologyMap z (-(p:ℤ)))
    (reversedHorizontalHomologyIso_naturality l m q)
  simp only [HomologicalComplex.homologyMap_comp] at he
  change _ ≫ (HomologicalComplex.homologyMap (reversedHorizontalHomologyIso C' D' q).hom (-(p:ℤ)) ≫
      ((reverseHomologyNatIsoE2 (p:ℤ)).app _).hom) =
    (HomologicalComplex.homologyMap (reversedHorizontalHomologyIso C D q).hom (-(p:ℤ)) ≫
      ((reverseHomologyNatIsoE2 (p:ℤ)).app _).hom) ≫ _
  rw [← Category.assoc, he, Category.assoc]
  have hn := (reverseHomologyNatIsoE2 (A := ModuleCat.{max v w} ℤ) (p:ℤ)).hom.naturality
    (((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q:ℤ)).mapHomologicalComplex
        (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l m))
  change HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap _ negChainEmbedding) (-(p:ℤ)) ≫ _ =
    _ ≫ HomologicalComplex.homologyMap _ (p:ℤ) at hn
  rw [Category.assoc]
  congr 1

theorem tensorCochainE2Map_eq_first
    (l l' : C ⟶ C') (h : Homotopy l l') (m : D ⟶ D') (p q : ℕ) :
    HomologicalComplex.homologyMap
      (verticalHomologyMap _ (flippedCochainTensorMap l m) (-(q:ℤ))) (-(p:ℤ)) =
    HomologicalComplex.homologyMap
      (verticalHomologyMap _ (flippedCochainTensorMap l' m) (-(q:ℤ))) (-(p:ℤ)) := by
  apply (cancel_mono (tensorCochainE2IntegerIso C' D' p q).hom).mp
  rw [tensorCochainE2IntegerIso_naturality, tensorCochainE2IntegerIso_naturality,
    integer_horizontal_homology_eq_first l l' h m]


end RawE2Naturality
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
section CoefficientE2Independence

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance P103.Ch11.TorBalance
open DoubleComplexFirstPages
set_option maxHeartbeats 1500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [Ring R]
variable {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
variable {D D' : ChainComplex (ModuleCat.{w} R) ℕ}

theorem integer_horizontal_outer_homology_eq_second
    (l : C ⟶ C') (m m' : D ⟶ D') (h : Homotopy m m') (p q : ℕ) :
    HomologicalComplex.homologyMap
      (((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q:ℤ)).mapHomologicalComplex
        (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l m)) (p:ℤ) =
    HomologicalComplex.homologyMap
      (((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q:ℤ)).mapHomologicalComplex
        (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l m')) (p:ℤ) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q:ℤ)
  let F := (extendedHorizontalHomologyFunctor C' q : ModuleCat.{w} R ⥤ ModuleCat.{max v w} ℤ)
  let B := (H.mapHomologicalComplex (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l (𝟙 D))
  have hf (k : D ⟶ D') :
      (H.mapHomologicalComplex (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l k) =
      B ≫ (F.mapHomologicalComplex (ComplexShape.down ℤ)).map (HomologicalComplex.extendMap k nonnegativeChainEmbedding) := by
    apply HomologicalComplex.Hom.ext
    funext i
    let eC := HomologicalComplex.extendMap l nonnegativeChainEmbedding
    let eD := HomologicalComplex.extendMap k nonnegativeChainEmbedding
    let τ := TorBalance.tensorCoefficientMap (eD.f i).hom
    have he : (flippedIntegerTensorMap l k).f i =
        (flippedIntegerTensorMap l (𝟙 D)).f i ≫
          (τ.mapHomologicalComplex (ComplexShape.down ℤ)).app (extendNonnegativeChain C') := by
      apply HomologicalComplex.Hom.ext
      funext j
      apply ModuleCat.hom_ext
      apply tensor_hom_ext
      intro a b
      simp only [flippedIntegerTensorMap, integerTensorMap, HomologicalComplex.extendMap_id]
      rfl
    change HomologicalComplex.homologyMap _ (q:ℤ) = HomologicalComplex.homologyMap _ (q:ℤ) ≫
      HomologicalComplex.homologyMap _ (q:ℤ)
    rw [he, HomologicalComplex.homologyMap_comp]
    rfl
  have hh := (F.mapHomotopy (h.extend nonnegativeChainEmbedding)).homologyMap_eq (p:ℤ)
  change HomologicalComplex.homologyMap ((H.mapHomologicalComplex (ComplexShape.down ℤ)).map
      (flippedIntegerTensorMap l m)) (p:ℤ) =
    HomologicalComplex.homologyMap ((H.mapHomologicalComplex (ComplexShape.down ℤ)).map
      (flippedIntegerTensorMap l m')) (p:ℤ)
  rw [hf m, hf m', HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, hh]

theorem tensorCochainE2Map_eq_second
    (l : C ⟶ C') (m m' : D ⟶ D') (h : Homotopy m m') (p q : ℕ) :
    HomologicalComplex.homologyMap
      (verticalHomologyMap _ (flippedCochainTensorMap l m) (-(q:ℤ))) (-(p:ℤ)) =
    HomologicalComplex.homologyMap
      (verticalHomologyMap _ (flippedCochainTensorMap l m') (-(q:ℤ))) (-(p:ℤ)) := by
  apply (cancel_mono (tensorCochainE2IntegerIso C' D' p q).hom).mp
  rw [tensorCochainE2IntegerIso_naturality, tensorCochainE2IntegerIso_naturality,
    integer_horizontal_outer_homology_eq_second l m m' h]

end CoefficientE2Independence
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
section E2PairCompatibility

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance P103.Ch11.TorBalance
open DoubleComplexFirstPages
set_option maxHeartbeats 1500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [Ring R]
variable {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
variable {D D' : ChainComplex (ModuleCat.{w} R) ℕ}

def ordinaryHorizontalHomologyNatMap (l : C ⟶ C') (q : ℕ) :
    (ordinaryHorizontalHomologyFunctor C q : ModuleCat.{w} R ⥤ _) ⟶ ordinaryHorizontalHomologyFunctor C' q where
  app N := ModuleCat.ofHom (homologyMap (tensorFirstMap l N) q)
  naturality {N N'} g := by
    let H := P103.Specs.Ch10.Comparison.quotientHomology (S := ℤ) (ComplexShape.down ℕ) q
    change H.map (tensorSecondMap C g.hom) ≫ H.map (tensorFirstMap l N') =
      H.map (tensorFirstMap l N) ≫ H.map (tensorSecondMap C' g.hom)
    rw [← H.map_comp, ← H.map_comp, tensorFirstMap_tensorSecondMap]

def ordinaryHorizontalPairMap (l : C ⟶ C') (m : D ⟶ D') (q : ℕ) :=
  ((ordinaryHorizontalHomologyNatMap l q).mapHomologicalComplex (ComplexShape.down ℕ)).app D ≫
    ((ordinaryHorizontalHomologyFunctor C' q).mapHomologicalComplex (ComplexShape.down ℕ)).map m

def extendedOrdinaryHorizontalPairMap (l : C ⟶ C') (m : D ⟶ D') (q : ℕ) :=
  ((ordinaryHorizontalHomologyNatMap l q).mapHomologicalComplex (ComplexShape.down ℤ)).app (extendNonnegativeChain D) ≫
    ((ordinaryHorizontalHomologyFunctor C' q).mapHomologicalComplex (ComplexShape.down ℤ)).map
      (HomologicalComplex.extendMap m nonnegativeChainEmbedding)

theorem extendedHorizontalHomologyComplexIso_naturality
    (l : C ⟶ C') (m : D ⟶ D') (q : ℕ) :
    ((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q:ℤ)).mapHomologicalComplex
        (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l m) ≫
        (extendedHorizontalHomologyComplexIso C' D' q).hom =
    (extendedHorizontalHomologyComplexIso C D q).hom ≫ extendedOrdinaryHorizontalPairMap l m q := by
  apply HomologicalComplex.Hom.ext
  funext i
  let N := (extendNonnegativeChain D).X i
  let N' := (extendNonnegativeChain D').X i
  let lZ := HomologicalComplex.extendMap l nonnegativeChainEmbedding
  let mZ := HomologicalComplex.extendMap m nonnegativeChainEmbedding
  let τ := TorBalance.tensorCoefficientMap (mZ.f i).hom
  let F := tensorFunctor (R := R) N
  let G := tensorFunctor (R := R) N'
  have hf : (flippedIntegerTensorMap l m).f i =
      (F.mapHomologicalComplex (ComplexShape.down ℤ)).map lZ ≫
      (τ.mapHomologicalComplex (ComplexShape.down ℤ)).app (extendNonnegativeChain C') := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  change HomologicalComplex.homologyMap ((flippedIntegerTensorMap l m).f i) (q:ℤ) ≫
      (mappedExtendHomologyIso C' G q).hom =
    (mappedExtendHomologyIso C F q).hom ≫
      ModuleCat.ofHom (homologyMap (tensorFirstMap l N) q) ≫
        ModuleCat.ofHom (homologyMap (tensorSecondMap C' (mZ.f i).hom) q)
  erw [hf, HomologicalComplex.homologyMap_comp, Category.assoc,
    mappedExtendHomologyIso_naturality C' τ q, ← Category.assoc,
    E2Bridge.mappedExtendHomologyIso_chain_naturality F l q]
  rw [Category.assoc]
  rfl

section PairGeneric
variable {T : Type u} [Ring T] {U : Type x} [Ring U]
variable {E E' : ChainComplex (ModuleCat.{v} T) ℕ}
variable {F G : ModuleCat.{v} T ⥤ ModuleCat.{w} U} [F.Additive] [G.Additive]

theorem mappedExtendHomologyIso_pair_naturality (τ : F ⟶ G) (l : E ⟶ E') (p : ℕ) :
    HomologicalComplex.homologyMap
      (((τ.mapHomologicalComplex (ComplexShape.down ℤ)).app (extendNonnegativeChain E)) ≫
        (G.mapHomologicalComplex (ComplexShape.down ℤ)).map (HomologicalComplex.extendMap l nonnegativeChainEmbedding)) (p:ℤ) ≫
      (mappedExtendHomologyIso E' G p).hom =
    (mappedExtendHomologyIso E F p).hom ≫ ModuleCat.ofHom
      (homologyMap (((τ.mapHomologicalComplex (ComplexShape.down ℕ)).app E) ≫
        (G.mapHomologicalComplex (ComplexShape.down ℕ)).map l) p) := by
  let HN := P103.Specs.Ch10.Comparison.quotientHomology (S := U) (ComplexShape.down ℕ) p
  change _ = (mappedExtendHomologyIso E F p).hom ≫ HN.map (_ ≫ _)
  rw [HomologicalComplex.homologyMap_comp, HN.map_comp, Category.assoc,
    E2Bridge.mappedExtendHomologyIso_chain_naturality G l p, ← Category.assoc,
    mappedExtendHomologyIso_naturality E τ p, Category.assoc]
  rfl
end PairGeneric


end E2PairCompatibility
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
section FullE2Compatibility

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance P103.Ch11.TorBalance
open DoubleComplexFirstPages
set_option maxHeartbeats 1500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [Ring R]
variable {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
variable {D D' : ChainComplex (ModuleCat.{w} R) ℕ}

theorem tensorCochainE2Iso_naturality
    (l : C ⟶ C') (m : D ⟶ D') (p q : ℕ) :
    HomologicalComplex.homologyMap
      (verticalHomologyMap _ (flippedCochainTensorMap l m) (-(q:ℤ))) (-(p:ℤ)) ≫
      (tensorCochainE2Iso C' D' p q).hom =
    (tensorCochainE2Iso C D p q).hom ≫
      ModuleCat.ofHom (homologyMap (ordinaryHorizontalPairMap l m q) p) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (p:ℤ)
  let a := tensorCochainE2IntegerIso C D p q
  let a' := tensorCochainE2IntegerIso C' D' p q
  let b := H.mapIso (extendedHorizontalHomologyComplexIso C D q)
  let b' := H.mapIso (extendedHorizontalHomologyComplexIso C' D' q)
  let c := mappedExtendHomologyIso D (ordinaryHorizontalHomologyFunctor C q) p
  let c' := mappedExtendHomologyIso D' (ordinaryHorizontalHomologyFunctor C' q) p
  let v := ((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} ℤ) (ComplexShape.down ℤ) (q:ℤ)).mapHomologicalComplex
        (ComplexShape.down ℤ)).map (flippedIntegerTensorMap l m)
  have ha := tensorCochainE2IntegerIso_naturality l m p q
  have hb : HomologicalComplex.homologyMap v (p:ℤ) ≫ b'.hom = b.hom ≫
      HomologicalComplex.homologyMap (extendedOrdinaryHorizontalPairMap l m q) (p:ℤ) := by
    have he := congrArg (fun z => HomologicalComplex.homologyMap z (p:ℤ))
      (extendedHorizontalHomologyComplexIso_naturality l m q)
    change HomologicalComplex.homologyMap v (p:ℤ) ≫
      HomologicalComplex.homologyMap (extendedHorizontalHomologyComplexIso C' D' q).hom (p:ℤ) =
      HomologicalComplex.homologyMap (extendedHorizontalHomologyComplexIso C D q).hom (p:ℤ) ≫
        HomologicalComplex.homologyMap (extendedOrdinaryHorizontalPairMap l m q) (p:ℤ)
    simpa only [HomologicalComplex.homologyMap_comp] using he
  have hc : HomologicalComplex.homologyMap (extendedOrdinaryHorizontalPairMap l m q) (p:ℤ) ≫ c'.hom =
      c.hom ≫ ModuleCat.ofHom (homologyMap (ordinaryHorizontalPairMap l m q) p) :=
    mappedExtendHomologyIso_pair_naturality (ordinaryHorizontalHomologyNatMap l q) m p
  change _ ≫ (a'.hom ≫ b'.hom ≫ c'.hom) = (a.hom ≫ b.hom ≫ c.hom) ≫ _
  rw [← Category.assoc _ a'.hom, ha, Category.assoc, ← Category.assoc _ b'.hom, hb,
    Category.assoc, hc, ← Category.assoc, ← Category.assoc]
  simp only [Category.assoc]
  rfl


end FullE2Compatibility
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
section CanonicalResolved

open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
set_option maxHeartbeats 300000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}

def canonicalTargetComparison (P : ResolutionPair f A M) :
    TargetComparisonData f A M P.right P.left :=
  (target_comparison.{u,v,w,x} R S f A M P.right P.left P.right_projective).some

/-- The canonical row system and canonical total augmentation are chosen together. -/
def canonicalResolvedSequenceData (P : ResolutionPair f A M) : Resolved f A M P :=
  resolvedSequenceFromPages
    (canonicalTensorPagesData.{u,max u w,max u v x} P.right.complex
      (restrictionResolution f M P.left).complex)
    (canonicalTargetComparison.{u,v,w,x} f P) P.left_projective

@[simp] theorem canonicalResolvedSequenceData_firstPages (P : ResolutionPair f A M) :
    (canonicalResolvedSequenceData f P).firstPages =
      (DoubleComplexFirstPages.system _).row _
        (tensorCochainBicomplex_finite P.right.complex (restrictionResolution f M P.left).complex)
        (canonicalResolvedSequenceData f P).filtration
        (canonicalResolvedSequenceData f P).formula (canonicalResolvedSequenceData f P).pages := rfl

end CanonicalResolved
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
section FirstQuadrantMaps
open CategoryTheory

open P103.Specs.Ch10.Comparison
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
variable {A B : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  [AddCommGroup B] [Module Rᵐᵒᵖ B]
variable {M N : Type (max u v x)} [AddCommGroup M] [Module S M]
  [AddCommGroup N] [Module S N]
variable {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution S M}
  {P' : LeftResolution Rᵐᵒᵖ B} {Q' : LeftResolution S N}
variable [(tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex).HasTotal
      (ComplexShape.up ℤ)]
  [(tensorCochainBicomplex P'.complex (restrictionResolution f N Q').complex).HasTotal
      (ComplexShape.up ℤ)]
variable (E : ResolvedSequenceData f A M P Q) (E' : ResolvedSequenceData f B N P' Q')

/-- First-quadrant support extends equality on ordinary bidegrees to every
integer filtration/total degree; this is useful before page propagation. -/
theorem pageMap_eq_of_firstQuadrant
    (r : ℤ) (hr : 0 ≤ r)
    (α β : ∀ p n : ℤ, chainPage E.filtration E.pages r p n ⟶
      chainPage E'.filtration E'.pages r p n)
    (h : ∀ p q : ℕ, α p (p+q) = β p (p+q)) :
    ∀ p n : ℤ, α p n = β p n := by
  intro p n
  by_cases hp : 0 ≤ p
  · by_cases hq : 0 ≤ n-p
    · let q := (n-p).toNat
      let p' := p.toNat
      have heqp : (p' : ℤ) = p := Int.toNat_of_nonneg hp
      have heqq : (q : ℤ) = n-p := Int.toNat_of_nonneg hq
      have heqn : (p' : ℤ) + q = n := by omega
      have hh := h p' q
      rw [heqn, heqp] at hh
      exact hh
    · have hz := E.firstQuadrant r p (n-p) hr (Or.inr (by omega))
      have hz' : Limits.IsZero (chainPage E.filtration E.pages r p n) := by
        convert hz using 1 <;> congr 1 <;> omega
      exact hz'.eq_of_src _ _
  · have hz := E.firstQuadrant r p (n-p) hr (Or.inl (by omega))
    have hz' : Limits.IsZero (chainPage E.filtration E.pages r p n) := by
      convert hz using 1 <;> congr 1 <;> omega
    exact hz'.eq_of_src _ _

end FirstQuadrantMaps
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open FiniteFiltrationConvergence
section TransportedStableNaturality
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : FilteredComplex C} (f : FilteredMap X Y)
variable {H H' : C} (n : ℤ) (e : X.complex.homology (-n) ≅ H)
    (e' : Y.complex.homology (-n) ≅ H')

/-- Reindexing and target transport on the actual cohomology filtration quotient. -/
def chainTargetQuotientIso (F : Filtration X.complex) (e : X.complex.homology (-n) ≅ H) (p : ℤ) :
    gradedCohomology F (-p) (-n) ≅
      cokernel (Subobject.ofLE
        (Subobject.mapIsoToOrderIso e (chainTargetPiece F (p-1) n))
        (Subobject.mapIsoToOrderIso e (chainTargetPiece F p n))
        ((Subobject.mapIsoToOrderIso e).monotone (chainTargetPiece_increasing F p n))) := by
  let sIso : (cohomologyPiece F (-p+1) (-n) : C) ≅ (chainTargetPiece F (p-1) n : C) :=
    Subobject.isoOfEq _ _ (by dsimp only [chainTargetPiece]; congr 1 <;> omega)
  refine cokernel.mapIso _ _ sIso (Iso.refl _) ?_ ≪≫
    mappedSubobjectCokernelIso e (chainTargetPiece F (p-1) n) (chainTargetPiece F p n)
      (chainTargetPiece_increasing F p n)
  apply (cancel_mono (chainTargetPiece F p n).arrow).mp
  simp only [Iso.refl_hom, Category.comp_id, Category.assoc,
    sIso, Subobject.isoOfEq_hom, Subobject.ofLE_arrow]

/-- The quotient transport acts on representatives by the transported step inclusion. -/
@[reassoc (attr := simp)]
theorem chainTargetQuotientIso_π (p : ℤ) :
    cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing X.filtration (-p) (-n))) ≫
      (chainTargetQuotientIso n X.filtration e p).hom =
    (mappedSubobjectIso e (chainTargetPiece X.filtration p n)).hom ≫
      cokernel.π (Subobject.ofLE
        (Subobject.mapIsoToOrderIso e (chainTargetPiece X.filtration (p-1) n))
        (Subobject.mapIsoToOrderIso e (chainTargetPiece X.filtration p n))
        ((Subobject.mapIsoToOrderIso e).monotone (chainTargetPiece_increasing X.filtration p n))) := by
  simp only [chainTargetQuotientIso, Iso.trans_hom, mappedSubobjectCokernelIso,
    cokernel.mapIso_hom, cokernel.map, cokernel.π_desc_assoc, cokernel.π_desc,
    Iso.refl_hom, Category.id_comp]

/-- The map of transported target quotients induced by a filtered cochain map. -/
def transportedChainGradedMap (p : ℤ) :=
  (chainTargetQuotientIso n X.filtration e p).inv ≫
    gradedCohomologyMap f (-p) (-n) ≫
      (chainTargetQuotientIso n Y.filtration e' p).hom

/-- This quotient map is induced by the actual map of the target filtration steps. -/
@[reassoc (attr := simp)]
theorem transportedChainGradedMap_π (p : ℤ) :
    cokernel.π (Subobject.ofLE
        (Subobject.mapIsoToOrderIso e (chainTargetPiece X.filtration (p-1) n))
        (Subobject.mapIsoToOrderIso e (chainTargetPiece X.filtration p n))
        ((Subobject.mapIsoToOrderIso e).monotone (chainTargetPiece_increasing X.filtration p n))) ≫
      transportedChainGradedMap f n e e' p =
    transportedCohomologyStepMap f (-n) e e' (-p) ≫
      cokernel.π (Subobject.ofLE
        (Subobject.mapIsoToOrderIso e' (chainTargetPiece Y.filtration (p-1) n))
        (Subobject.mapIsoToOrderIso e' (chainTargetPiece Y.filtration p n))
        ((Subobject.mapIsoToOrderIso e').monotone (chainTargetPiece_increasing Y.filtration p n))) := by
  apply (cancel_epi (mappedSubobjectIso e (chainTargetPiece X.filtration p n)).hom).1
  rw [← chainTargetQuotientIso_π_assoc]
  dsimp only [transportedChainGradedMap, transportedCohomologyStepMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [gradedCohomologyMap]
  rw [cokernel.π_desc_assoc, Category.assoc, chainTargetQuotientIso_π]

/-- The existing limiting comparison factors through the canonical target quotient transport. -/
theorem mappedChainPageLimitIso_factor
    (D : F03Specs.PageData X.filtration) (h : DoubleComplexConvergence.Converges X.filtration)
    (r : ℤ) (hr : 0 ≤ r) (p : ℤ) (hs : Stabilized X.filtration r (-p) (-n)) :
    mappedChainPageLimitIso X.filtration D n e h r hr p hs =
      chainPageLimitIso X.filtration D h r hr p n hs ≪≫
        chainTargetQuotientIso n X.filtration e p := by
  apply Iso.ext
  simp only [mappedChainPageLimitIso, chainTargetQuotientIso, Iso.trans_hom, Category.assoc]

/-- Stable pages commute with the actual quotient map on the transported target filtration. -/
theorem mappedChainPageLimitIso_natural
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D E)
    (hX : DoubleComplexConvergence.Converges X.filtration)
    (hY : DoubleComplexConvergence.Converges Y.filtration)
    (r : ℤ) (hr : 0 ≤ r) (p : ℤ)
    (hsX : Stabilized X.filtration r (-p) (-n))
    (hsY : Stabilized Y.filtration r (-p) (-n)) :
    M.map r (-p) (-n) ≫
      (mappedChainPageLimitIso Y.filtration E n e' hY r hr p hsY).hom =
    (mappedChainPageLimitIso X.filtration D n e hX r hr p hsX).hom ≫
      transportedChainGradedMap f n e e' p := by
  have hn : M.map r (-p) (-n) ≫ (chainPageLimitIso Y.filtration E hY r hr p n hsY).hom =
      (chainPageLimitIso X.filtration D hX r hr p n hsX).hom ≫
        gradedCohomologyMap f (-p) (-n) :=
    limitIso_naturality f D E M r (-p) (-n)
      (hX.limit D r (-p) (-n) hr hsX).some
      (hY.limit E r (-p) (-n) hr hsY).some hsX
  rw [mappedChainPageLimitIso_factor, mappedChainPageLimitIso_factor]
  dsimp only [transportedChainGradedMap, Iso.trans_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
end TransportedStableNaturality
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open CategoryTheory
section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison P103.BalancedTensor
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open DoubleComplexFirstPages

section RowComparisonNaturality

set_option maxHeartbeats 1200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} {S : Type x} [Ring R] [Ring S]
variable {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
variable {Q Q' : ChainComplex (ModuleCat.{max x w} S) ℕ}

def rowHomologyCoefficientMap (f : R →+* S)
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ) (m : Q ⟶ Q') (q : ℕ) :
    rowHomologyComplex.{u,x,v,w} f C Q q ⟶ rowHomologyComplex.{u,x,v,w} f C Q' q :=
  ((((restrictionFunctor f ⋙ tensorCoefficientComplex C) ⋙
    P103.Specs.Ch10.Comparison.quotientHomology (ComplexShape.down ℕ) q).mapHomologicalComplex
      (ComplexShape.down ℕ)).map m)

private theorem changeOfRingsRowsExtensionIso_natural (f : R →+* S)
    (l : C ⟶ C') (m : Q ⟶ Q') (q : ℕ) :
    verticalHomologyMap _ (flippedCochainTensorMap l
        (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m)) (negativeChainEmbedding.f q) ≫
      (ordinaryRowsExtensionIso C' (restrictionComplex f (ComplexShape.down ℕ) Q') q).hom =
    (ordinaryRowsExtensionIso C (restrictionComplex f (ComplexShape.down ℕ) Q) q).hom ≫
      HomologicalComplex.extendMap
        (rowHomologyMap.{u,x,v,w} f l Q q ≫ rowHomologyCoefficientMap.{u,v,w,x} f C' m q)
        negativeChainEmbedding := by
  let D := restrictionComplex f (ComplexShape.down ℕ) Q
  let D' := restrictionComplex f (ComplexShape.down ℕ) Q'
  let mR := ((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m
  let φ := flippedCochainTensorMap l mR
  let F := verticalHomologyMap _ φ (negativeChainEmbedding.f q)
  let r := rowHomologyMap.{u,x,v,w} f l Q q ≫ rowHomologyCoefficientMap.{u,v,w,x} f C' m q
  apply negativeExtensionIso_natural (ordinaryRowsRestrictionIso C D q)
    (ordinaryRowsRestrictionIso C' D' q) (cochainRows_zero C D q) (cochainRows_zero C' D' q) F r
  apply HomologicalComplex.Hom.ext
  funext j
  let g := tensorFirstMap l (D.X j)
  let h := tensorSecondMap C' (mR.f j).hom
  let g' := φ.f (negativeChainEmbedding.f j)
  have hr (i : ℕ) : (g ≫ h).f i = ModuleCat.ofHom (tensorMap (l.f i).hom (mR.f j).hom) := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  have hg := ordinaryRowTermIso_natural C D (C' := C') (D' := D') (p := j) (p' := j)
    (g ≫ h) g' (fun i => by
    rw [hr]
    exact tensorTermIso_natural _ _ _ _
      (l.f i) ((HomologicalComplex.extendMap l nonnegativeChainEmbedding).f (-negativeChainEmbedding.f i))
      (mR.f j) ((HomologicalComplex.extendMap mR nonnegativeChainEmbedding).f (-negativeChainEmbedding.f j))
      (reversedExtendXIso_map l i) (reversedExtendXIso_map mR j)) q
  let H := quotientHomology (S := ℤ) (ComplexShape.down ℕ) q
  change HomologicalComplex.homologyMap g' (negativeChainEmbedding.f q) ≫ (ordinaryRowTermIso C' D' j q).hom =
    (ordinaryRowTermIso C D j q).hom ≫ (H.map g ≫ H.map h)
  rw [← H.map_comp]
  exact hg

/-- Horizontal homology followed by regrading gives the ordinary complex of
row quotients used to compute the second page. -/
def changeOfRingsE2Iso (f : R →+* S)
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (Q : ChainComplex (ModuleCat.{max x w} S) ℕ) (p q : ℕ) :
    (cochainRows C (restrictionComplex f (ComplexShape.down ℕ) Q) q).homology
      (negativeChainEmbedding.f p) ≅
    ModuleCat.of ℤ (Homology (rowHomologyComplex.{u,x,v,w} f C Q q) p) :=
  negativeExtensionQuotientIso (ordinaryRowsExtensionIso C (restrictionComplex f (ComplexShape.down ℕ) Q) q) p

theorem changeOfRingsE2Iso_naturality (f : R →+* S)
    (l : C ⟶ C') (m : Q ⟶ Q') (p q : ℕ) :
    @Eq ((cochainRows C (restrictionComplex f (ComplexShape.down ℕ) Q) q).homology
        (negativeChainEmbedding.f p) ⟶ ModuleCat.of ℤ (Homology (rowHomologyComplex.{u,x,v,w} f C' Q' q) p))
      (HomologicalComplex.homologyMap
        (verticalHomologyMap _ (flippedCochainTensorMap l
          (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m)) (negativeChainEmbedding.f q))
        (negativeChainEmbedding.f p) ≫ (changeOfRingsE2Iso.{u,v,w,x} f C' Q' p q).hom)
      ((changeOfRingsE2Iso.{u,v,w,x} f C Q p q).hom ≫ ModuleCat.ofHom
        (homologyMap (rowHomologyMap.{u,x,v,w} f l Q q ≫ rowHomologyCoefficientMap.{u,v,w,x} f C' m q) p)) := by
  let mR := ((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m
  let g := verticalHomologyMap _ (flippedCochainTensorMap l mR) (negativeChainEmbedding.f q)
  let h := rowHomologyMap.{u,x,v,w} f l Q q ≫ rowHomologyCoefficientMap.{u,v,w,x} f C' m q
  let a := ordinaryRowsExtensionIso C (restrictionComplex f (ComplexShape.down ℕ) Q) q
  let a' := ordinaryRowsExtensionIso C' (restrictionComplex f (ComplexShape.down ℕ) Q') q
  have hn : g ≫ a'.hom = a.hom ≫ HomologicalComplex.extendMap h negativeChainEmbedding :=
    changeOfRingsRowsExtensionIso_natural.{u,v,w,x} f l m q
  exact negativeExtensionQuotientIso_natural a a' g h hn p

end RowComparisonNaturality

end

end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open CategoryTheory
section PageHomotopyIndependence

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance P103.Ch11.TorBalance
open DoubleComplexFirstPages DoubleTotalization FiniteDiagonalFiltrations
set_option maxHeartbeats 1500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [Ring R]
variable {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
variable {Q Q' : ChainComplex (ModuleCat.{w} R) ℕ}
variable [(tensorCochainBicomplex C Q).HasTotal (ComplexShape.up ℤ)]
variable [(tensorCochainBicomplex C' Q').HasTotal (ComplexShape.up ℤ)]
namespace TensorPagesData
variable (B : TensorPagesData C Q) (B' : TensorPagesData C' Q')

theorem mapData_eq_secondPage (l l' : C ⟶ C') (hl : Homotopy l l')
    (m m' : Q ⟶ Q') (hm : Homotopy m m') (p n : ℤ) :
    (B.mapData B' l m).map 2 p n = (B.mapData B' l' m').map 2 p n := by
  by_cases hs : 0 < p ∨ 0 < n-p
  · have hz : IsZero (PageCohomology.object B.filtration B.pages 2 p n) := by
      have hz := B.chainFirstQuadrant 2 (-p) (p-n) (by omega)
      convert hz using 1 <;> congr 1 <;> omega
    exact hz.eq_of_src _ _
  · let a := (-p).toNat
    let b := (p-n).toNat
    have ha : -(a:ℤ) = p := by dsimp [a]; omega
    have hb : -(b:ℤ) = n-p := by dsimp [b]; omega
    clear_value a b
    have hn : n = -(a:ℤ) + -(b:ℤ) := by omega
    subst p
    subst n
    let S := DoubleComplexFirstPages.system (ModuleCat.{max v w} ℤ)
    have hM := (S.row_naturality (tensorCochainBicomplex C Q) (tensorCochainBicomplex C' Q')
      (tensorCochainBicomplex_finite C Q) (tensorCochainBicomplex_finite C' Q')
      B.filtration B'.filtration B.formula B'.formula B.pages B'.pages
      (tensorCochainBicomplexMap l m) (B.filteredMap B' l m) (B.filteredMap_hom B' l m)
      (B.mapData B' l m) (-(a:ℤ)) (-(b:ℤ))).2.2
    have hN := (S.row_naturality (tensorCochainBicomplex C Q) (tensorCochainBicomplex C' Q')
      (tensorCochainBicomplex_finite C Q) (tensorCochainBicomplex_finite C' Q')
      B.filtration B'.filtration B.formula B'.formula B.pages B'.pages
      (tensorCochainBicomplexMap l' m') (B.filteredMap B' l' m') (B.filteredMap_hom B' l' m')
      (B.mapData B' l' m') (-(a:ℤ)) (-(b:ℤ))).2.2
    have he := (tensorCochainE2Map_eq_first l l' hl m a b).trans
      (tensorCochainE2Map_eq_second l' m m' hm a b)
    apply (cancel_mono ((S.row (tensorCochainBicomplex C' Q') (tensorCochainBicomplex_finite C' Q')
        B'.filtration B'.formula B'.pages).secondIso (-(a:ℤ)) (-(b:ℤ))).hom).mp
    rw [hM, hN]
    congr 1

theorem mapData_eq_of_homotopy (l l' : C ⟶ C') (hl : Homotopy l l')
    (m m' : Q ⟶ Q') (hm : Homotopy m m') (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    (B.mapData B' l m).map r p n = (B.mapData B' l' m').map r p n := by
  exact pageMap_eq_of_page (B.mapData B' l m) (B.mapData B' l' m') B.cohomology B'.cohomology
    2 (by omega) (mapData_eq_secondPage B B' l l' hl m m' hm) r hr p n
end TensorPagesData

end PageHomotopyIndependence
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open CategoryTheory
section PageMapConstruction

namespace PageMapAssembly
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}

/-- All original modules admit the projective choices used by the system. -/
theorem choices (A : ModuleCat.{w} Rᵐᵒᵖ) (M : ModuleCat.{max u v x} S) :
    Nonempty (ResolutionPair f A M) := by
  obtain ⟨P,hP⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution Rᵐᵒᵖ A
  obtain ⟨Q,hQ⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution S M
  exact ⟨⟨P,Q,hP,hQ,tensor_total_exists R P.complex (restrictionResolution f M Q).complex⟩⟩

variable (E : ∀ {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
  (P : ResolutionPair f A M), Resolved f A M P)

abbrev lifted {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (l : P.right.complex ⟶ Q.right.complex) (m : P.left.complex ⟶ Q.left.complex) :=
  (E P).toTensorPagesData.filteredMap (E Q).toTensorPagesData l
    (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m)

abbrev liftedPages {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (l : P.right.complex ⟶ Q.right.complex) (m : P.left.complex ⟶ Q.left.complex) :=
  (E P).toTensorPagesData.mapData (E Q).toTensorPagesData l
    (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m)

@[simp] theorem liftedPages_id
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (r p n : ℤ) :
    (liftedPages E P P (𝟙 _) (𝟙 _)).map r p n = 𝟙 _ := by
  dsimp only [liftedPages]
  erw [CategoryTheory.Functor.map_id, TensorPagesData.mapData_id]

@[simp] theorem liftedPages_comp
    {A B C : ModuleCat.{w} Rᵐᵒᵖ} {M N O : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (T : ResolutionPair f C O)
    (l : P.right.complex ⟶ Q.right.complex) (l' : Q.right.complex ⟶ T.right.complex)
    (m : P.left.complex ⟶ Q.left.complex) (m' : Q.left.complex ⟶ T.left.complex)
    (r p n : ℤ) :
    (liftedPages E P T (l ≫ l') (m ≫ m')).map r p n =
      (liftedPages E P Q l m).map r p n ≫ (liftedPages E Q T l' m').map r p n := by
  dsimp only [liftedPages]
  erw [CategoryTheory.Functor.map_comp, TensorPagesData.mapData_comp]

abbrev rightLift {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) :=
  P103.Ch10.Comparison.chainMap P.right Q.right P.right_projective a.hom
abbrev leftLift {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (b : M ⟶ N) :=
  P103.Ch10.Comparison.chainMap P.left Q.left P.left_projective b.hom

@[simp] theorem rightLift_lifts
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) :
    ChainLift P.right Q.right a.hom (rightLift P Q a) :=
  P103.Ch10.Comparison.chainMap_lifts P.right Q.right P.right_projective a.hom
@[simp] theorem leftLift_lifts
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (b : M ⟶ N) :
    ChainLift P.left Q.left b.hom (leftLift P Q b) :=
  P103.Ch10.Comparison.chainMap_lifts P.left Q.left P.left_projective b.hom

def map {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N)
    (r p n : ℤ) :
    chainPage (E P).filtration (E P).pages r p n ⟶
      chainPage (E Q).filtration (E Q).pages r p n :=
  (liftedPages E P Q (rightLift P Q a) (leftLift P Q b)).map r (-p) (-n)

/-- The single substantive page premise, to be discharged by the E2 computation
and the accepted next-page law before final assembly. -/
def LiftIndependent : Prop :=
  ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N)
    (l l' : P.right.complex ⟶ Q.right.complex) (m m' : P.left.complex ⟶ Q.left.complex),
    ChainLift P.right Q.right a.hom l → ChainLift P.right Q.right a.hom l' →
    ChainLift P.left Q.left b.hom m → ChainLift P.left Q.left b.hom m' →
    ∀ r p n, 2 ≤ r → (liftedPages E P Q l m).map r p n = (liftedPages E P Q l' m').map r p n

variable (hInd : LiftIndependent E)
include hInd

 theorem map_eq
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N)
    (l : P.right.complex ⟶ Q.right.complex) (m : P.left.complex ⟶ Q.left.complex)
    (hl : ChainLift P.right Q.right a.hom l) (hm : ChainLift P.left Q.left b.hom m)
    (r p n : ℤ) (hr : 2 ≤ r) :
    map E P Q a b r p n = (liftedPages E P Q l m).map r (-p) (-n) :=
  hInd P Q a b (rightLift P Q a) l (leftLift P Q b) m
    (rightLift_lifts P Q a) hl (leftLift_lifts P Q b) hm r (-p) (-n) hr

theorem map_id
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (r p n : ℤ) (hr : 2 ≤ r) :
    map E P P (𝟙 A) (𝟙 M) r p n = 𝟙 _ := by
  rw [map_eq E hInd P P (𝟙 A) (𝟙 M) (𝟙 _) (𝟙 _)
    (P103.Ch10.Comparison.chainLift_id P.right)
    (P103.Ch10.Comparison.chainLift_id P.left) r p n hr,
    liftedPages_id]

theorem map_comp
    {A B C : ModuleCat.{w} Rᵐᵒᵖ} {M N O : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (T : ResolutionPair f C O)
    (a : A ⟶ B) (a' : B ⟶ C) (b : M ⟶ N) (b' : N ⟶ O)
    (r p n : ℤ) (hr : 2 ≤ r) :
    map E P T (a ≫ a') (b ≫ b') r p n = map E P Q a b r p n ≫ map E Q T a' b' r p n := by
  rw [map_eq E hInd P T (a ≫ a') (b ≫ b')
    (rightLift P Q a ≫ rightLift Q T a') (leftLift P Q b ≫ leftLift Q T b')
    (P103.Ch10.Comparison.chainLift_comp (rightLift_lifts P Q a) (rightLift_lifts Q T a'))
    (P103.Ch10.Comparison.chainLift_comp (leftLift_lifts P Q b) (leftLift_lifts Q T b')) r p n hr,
    liftedPages_comp]
  rfl

omit hInd in
theorem map_differential
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    map E P Q a b r p n ≫ chainDifferential (E Q).filtration (E Q).pages r hr p n =
      chainDifferential (E P).filtration (E P).pages r hr p n ≫
        map E P Q a b r (p-r) (n-1) := by
  let F := liftedPages E P Q (rightLift P Q a) (leftLift P Q b)
  have he : ((-p+r,-n+1) : ℤ × ℤ) = (-(p-r),-(n-1)) := by
    apply Prod.ext <;> dsimp <;> omega
  have htransport := eqToHom_naturality (fun k : ℤ × ℤ => F.map r k.1 k.2) he
  change F.map r (-p) (-n) ≫ _ = _ ≫ F.map r (-(p-r)) (-(n-1))
  dsimp only [chainDifferential]
  rw [← Category.assoc, F.differential_comm, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun z => (E P).pages.differential r hr (-p) (-n) ≫ z) htransport
end PageMapAssembly

end PageMapConstruction
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open CategoryTheory
section InnerMapConstruction

namespace PageMapAssembly
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}

def innerMap {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (q : ℕ) :
    letI := innerTorModule f P.right.complex q
    letI := innerTorModule f Q.right.complex q
    TorWith P.right (Restricted f S) q →ₗ[Sᵐᵒᵖ] TorWith Q.right (Restricted f S) q :=
  innerTorMap f (rightLift P Q a) q

theorem innerMap_eq {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (q : ℕ)
    (l : P.right.complex ⟶ Q.right.complex) (hl : ChainLift P.right Q.right a.hom l)
    (z : TorWith P.right (Restricted f S) q) :
    innerMap P Q a q z = homologyMap (tensorFirstMap l (Restricted f S)) q z := by
  rw [innerMap, innerTorMap_eq]
  have hh := P103.Ch10.Comparison.chain_homology_independent Rᵐᵒᵖ ℤ
    (tensorFunctor (Restricted f S)) A B P.right Q.right P.right_projective a.hom
    (rightLift P Q a) l q (rightLift_lifts P Q a) hl
  exact congrArg (fun k => k.hom z) hh
end PageMapAssembly

end InnerMapConstruction
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open CategoryTheory
section PageLiftIndependence

namespace PageMapAssembly
open P103.Specs.Ch10.Comparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
variable (E : ∀ {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
  (P : ResolutionPair f A M), Resolved f A M P)

/-- The selected page maps are independent of both comparison lifts. -/
theorem liftIndependent : LiftIndependent E := by
  intro A B M N P Q a b l l' m m' hl hl' hm hm' r p n hr
  let hP := (P103.Ch10.Comparison.chain_unique Rᵐᵒᵖ A B P.right Q.right
    P.right_projective a.hom l l' hl hl').some
  let hQ := (P103.Ch10.Comparison.chain_unique S M N P.left Q.left
    P.left_projective b.hom m m' hm hm').some
  exact TensorPagesData.mapData_eq_of_homotopy (E P).toTensorPagesData (E Q).toTensorPagesData
    l l' hP _ _ ((restrictionFunctor f).mapHomotopy hQ) r hr p n
end PageMapAssembly

end PageLiftIndependence
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

noncomputable section
namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

section JointTensor
variable {R : Type u} [Ring R]
variable {C D E : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ}
variable {M N O : Type x} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup O] [Module R O]

/-- Simultaneous tensor maps respect composition in both variables. -/
theorem tensorPairMap_comp (l : C ⟶ D) (l' : D ⟶ E)
    (b : M →ₗ[R] N) (b' : N →ₗ[R] O) :
    tensorFirstMap (l ≫ l') M ≫ tensorSecondMap E (b'.comp b) =
      (tensorFirstMap l M ≫ tensorSecondMap D b) ≫
        (tensorFirstMap l' N ≫ tensorSecondMap E b') := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a m
  rfl

/-- The joint tensor map of identities is the identity chain map. -/
theorem tensorPairMap_id :
    tensorFirstMap (𝟙 C) M ≫ tensorSecondMap C (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a m
  rfl
end JointTensor

namespace NaturalSystem
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
variable (T : NaturalSystem.{u,v,w,x} f)

/-- The target maps form the ordinary Tor functor, beginning with identities. -/
@[simp] theorem targetMap_id
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (n : ℕ) :
    T.targetMap P P (𝟙 A) (𝟙 M) n = 𝟙 _ := by
  rw [T.targetMap_eq P P (𝟙 A) (𝟙 M) n (𝟙 P.right.complex)
    (P103.Ch10.Comparison.chainLift_id P.right)]
  change ModuleCat.ofHom (homologyMap
    (tensorFirstMap (𝟙 P.right.complex) (Restricted f M) ≫
      tensorSecondMap P.right.complex LinearMap.id) n) = 𝟙 _
  rw [tensorPairMap_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z => rfl

/-- The target maps respect composition in both original module variables. -/
theorem targetMap_comp
    {A B C : ModuleCat.{w} Rᵐᵒᵖ} {M N O : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (U : ResolutionPair f C O)
    (a : A ⟶ B) (a' : B ⟶ C) (b : M ⟶ N) (b' : N ⟶ O) (n : ℕ) :
    T.targetMap P U (a ≫ a') (b ≫ b') n =
      T.targetMap P Q a b n ≫ T.targetMap Q U a' b' n := by
  let l := P103.Ch10.Comparison.chainMap P.right Q.right P.right_projective a.hom
  let l' := P103.Ch10.Comparison.chainMap Q.right U.right Q.right_projective a'.hom
  have hl := P103.Ch10.Comparison.chainMap_lifts P.right Q.right P.right_projective a.hom
  have hl' := P103.Ch10.Comparison.chainMap_lifts Q.right U.right Q.right_projective a'.hom
  rw [T.targetMap_eq P U (a ≫ a') (b ≫ b') n (l ≫ l')
      (P103.Ch10.Comparison.chainLift_comp hl hl'),
    T.targetMap_eq P Q a b n l hl, T.targetMap_eq Q U a' b' n l' hl']
  change ModuleCat.ofHom (homologyMap
    (tensorFirstMap (l ≫ l') (Restricted f M) ≫
      tensorSecondMap U.right.complex
        ((Restricted.map f b'.hom).comp (Restricted.map f b.hom))) n) = _
  rw [tensorPairMap_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z => rfl

/-- Changes of resolution identify the targets by the ordinary identity-induced Tor map. -/
def targetComparison
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P Q : ResolutionPair f A M) (n : ℕ) :
    ModuleCat.of ℤ (TorWith P.right (Restricted f M) n) ≅
      ModuleCat.of ℤ (TorWith Q.right (Restricted f M) n) where
  hom := T.targetMap P Q (𝟙 A) (𝟙 M) n
  inv := T.targetMap Q P (𝟙 A) (𝟙 M) n
  hom_inv_id := by
    rw [← T.targetMap_comp P Q P _ _ _ _ n]
    simpa only [Category.id_comp] using T.targetMap_id P n
  inv_hom_id := by
    rw [← T.targetMap_comp Q P Q _ _ _ _ n]
    simpa only [Category.id_comp] using T.targetMap_id Q n

@[simp] theorem targetComparison_refl
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (n : ℕ) : T.targetComparison P P n = Iso.refl _ := by
  apply Iso.ext
  exact T.targetMap_id P n

theorem targetComparison_trans
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P Q U : ResolutionPair f A M) (n : ℕ) :
    T.targetComparison P Q n ≪≫ T.targetComparison Q U n = T.targetComparison P U n := by
  apply Iso.ext
  change T.targetMap P Q (𝟙 A) (𝟙 M) n ≫ T.targetMap Q U (𝟙 A) (𝟙 M) n = _
  rw [← T.targetMap_comp P Q U _ _ _ _ n]
  simp only [Category.id_comp]
  rfl

theorem targetComparison_naturality
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P P' : ResolutionPair f A M) (Q Q' : ResolutionPair f B N)
    (a : A ⟶ B) (b : M ⟶ N) (n : ℕ) :
    T.targetMap P Q a b n ≫ (T.targetComparison Q Q' n).hom =
      (T.targetComparison P P' n).hom ≫ T.targetMap P' Q' a b n := by
  change T.targetMap P Q a b n ≫ T.targetMap Q Q' (𝟙 B) (𝟙 N) n =
    T.targetMap P P' (𝟙 A) (𝟙 M) n ≫ T.targetMap P' Q' a b n
  rw [← T.targetMap_comp P Q Q' _ _ _ _ n,
    ← T.targetMap_comp P P' Q' _ _ _ _ n]
  simp only [Category.comp_id, Category.id_comp]
end NaturalSystem
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

noncomputable section
namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
set_option maxHeartbeats 2000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
namespace PageMapAssembly
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}

/-- The target map is the ordinary chosen-resolution Tor map in the original modules. -/
def targetMap
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (a : A ⟶ B) (b : M ⟶ N) (n : ℕ) :
    ModuleCat.of ℤ (TorWith P.right (Restricted f M) n) ⟶
      ModuleCat.of ℤ (TorWith Q.right (Restricted f N) n) :=
  (P103.Specs.Ch10.Comparison.quotientHomology (S := ℤ) (ComplexShape.down ℕ) n).map
    (tensorFirstMap (rightLift P Q a) (Restricted f M) ≫
      tensorSecondMap Q.right.complex (Restricted.map f b.hom))

/-- Every right-resolution lift gives this same target map. -/
theorem targetMap_eq
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (a : A ⟶ B) (b : M ⟶ N) (n : ℕ)
    (l : P.right.complex ⟶ Q.right.complex) (hl : ChainLift P.right Q.right a.hom l) :
    targetMap (f := f) P Q a b n = ModuleCat.ofHom
      (homologyMap (tensorFirstMap l (Restricted f M) ≫
        tensorSecondMap Q.right.complex (Restricted.map f b.hom)) n) := by
  have he := P103.Ch10.Comparison.chain_homology_independent Rᵐᵒᵖ ℤ
    (tensorFunctor (Restricted f M)) A B P.right Q.right P.right_projective a.hom
    (rightLift P Q a) l n (rightLift_lifts P Q a) hl
  let H := P103.Specs.Ch10.Comparison.quotientHomology (S := ℤ) (ComplexShape.down ℕ) n
  change H.map (tensorFirstMap (rightLift P Q a) (Restricted f M) ≫
      tensorSecondMap Q.right.complex (Restricted.map f b.hom)) =
    H.map (tensorFirstMap l (Restricted f M) ≫
      tensorSecondMap Q.right.complex (Restricted.map f b.hom))
  rw [H.map_comp, H.map_comp]
  exact congrArg (fun z => z ≫ H.map (tensorSecondMap Q.right.complex (Restricted.map f b.hom))) he
end PageMapAssembly
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

noncomputable section
namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
namespace NaturalSystem
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
variable (T : NaturalSystem.{u,v,w,x} f)
/-- Resolution comparison identifies the actual finite filtration on each ordinary Tor target. -/
theorem targetComparison_piece
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P Q : ResolutionPair f A M) (p : ℤ) (n : ℕ) :
    Subobject.mapIsoToOrderIso (T.targetComparison P Q n)
      (resolvedTargetPiece f (T.sequence P) p n) =
    resolvedTargetPiece f (T.sequence Q) p n := by
  let e := T.targetComparison P Q n
  obtain ⟨u,hu⟩ := T.target_preserves P Q (𝟙 A) (𝟙 M) p n
  obtain ⟨v,hv⟩ := T.target_preserves Q P (𝟙 A) (𝟙 M) p n
  have h : (Subobject.map e.hom).obj (resolvedTargetPiece f (T.sequence P) p n) ≤
      resolvedTargetPiece f (T.sequence Q) p n := by
    rw [← Subobject.exists_iso_map]
    exact Subobject.exists_le_of_comm _ u hu
  have h' : (Subobject.map e.inv).obj (resolvedTargetPiece f (T.sequence Q) p n) ≤
      resolvedTargetPiece f (T.sequence P) p n := by
    rw [← Subobject.exists_iso_map]
    exact Subobject.exists_le_of_comm _ v hv
  apply le_antisymm h
  change resolvedTargetPiece f (T.sequence Q) p n ≤
    (Subobject.mapIsoToOrderIso e) (resolvedTargetPiece f (T.sequence P) p n)
  apply (Subobject.mapIsoToOrderIso e).symm_apply_le.mp
  change (Subobject.map e.inv).obj (resolvedTargetPiece f (T.sequence Q) p n) ≤
    resolvedTargetPiece f (T.sequence P) p n
  exact h' 

end NaturalSystem
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

noncomputable section
namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open FiniteFiltrationConvergence
section
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : FilteredComplex C} (f g : FilteredMap X Y)
variable {H H' : C} (n : ℤ) (e : X.complex.homology (-n) ≅ H)
    (e' : Y.complex.homology (-n) ≅ H')

/-- The map on a transported target step depends only on the actual target map. -/
theorem transportedCohomologyStepMap_eq_of_target
    (k : H ⟶ H')
    (hf : HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom = e.hom ≫ k)
    (hg : HomologicalComplex.homologyMap g.hom (-n) ≫ e'.hom = e.hom ≫ k) (p : ℤ) :
    transportedCohomologyStepMap f (-n) e e' (-p) =
      transportedCohomologyStepMap g (-n) e e' (-p) := by
  apply (cancel_mono (Subobject.mapIsoToOrderIso e'
    (cohomologyPiece Y.filtration (-p) (-n))).arrow).1
  rw [transportedCohomologyStepMap_arrow f (-n) e e' k hf,
    transportedCohomologyStepMap_arrow g (-n) e e' k hg]

/-- The map on each transported target quotient also depends only on the target map. -/
theorem transportedChainGradedMap_eq_of_target
    (k : H ⟶ H')
    (hf : HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom = e.hom ≫ k)
    (hg : HomologicalComplex.homologyMap g.hom (-n) ≫ e'.hom = e.hom ≫ k) (p : ℤ) :
    transportedChainGradedMap f n e e' p = transportedChainGradedMap g n e e' p := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE
    (Subobject.mapIsoToOrderIso e (chainTargetPiece X.filtration (p-1) n))
    (Subobject.mapIsoToOrderIso e (chainTargetPiece X.filtration p n))
    ((Subobject.mapIsoToOrderIso e).monotone (chainTargetPiece_increasing X.filtration p n))))).1
  rw [transportedChainGradedMap_π, transportedChainGradedMap_π,
    transportedCohomologyStepMap_eq_of_target f g n e e' k hf hg]
end
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open CategoryTheory
section FullSystemAssembly

namespace PageMapAssembly
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions
set_option maxHeartbeats 2000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)

/-- The E2 square proved by the concrete horizontal comparison and Tor balance. -/
def CanonicalSecondNaturality : Prop :=
  ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N)
    (p q : ℕ), letI := (canonicalResolvedSequenceData.{u,v,w,x} f P).innerModule q
    letI := (canonicalResolvedSequenceData.{u,v,w,x} f Q).innerModule q
    ∀ (U : LeftResolution Sᵐᵒᵖ (TorWith P.right (Restricted f S) q))
      (V : LeftResolution Sᵐᵒᵖ (TorWith Q.right (Restricted f S) q))
      (hU : U.IsProjective) (hV : V.IsProjective) (k : U.complex ⟶ V.complex),
    ChainLift U V (innerMap P Q a q) k →
    @Eq (chainPage (canonicalResolvedSequenceData.{u,v,w,x} f P).filtration
        (canonicalResolvedSequenceData.{u,v,w,x} f P).pages 2 p (p+q) ⟶
      ModuleCat.of ℤ (TorWith V N p))
      (map.{u,v,w,x} (canonicalResolvedSequenceData.{u,v,w,x} f) P Q a b 2 p (p+q) ≫
        ((canonicalResolvedSequenceData.{u,v,w,x} f Q).secondIso p q V hV).hom)
      (((canonicalResolvedSequenceData.{u,v,w,x} f P).secondIso p q U hU).hom ≫
        ModuleCat.ofHom (homologyMap (tensorFirstMap k M ≫ tensorSecondMap V.complex b.hom) p))

/-- Assemble the natural sequence from the already proved E2 comparison. -/
def naturalSystem (hE2 : CanonicalSecondNaturality.{u,v,w,x} f) : NaturalSystem.{u,v,w,x} f where
  choices := choices
  rowSystem := DoubleComplexFirstPages.system _
  sequence := canonicalResolvedSequenceData.{u,v,w,x} f
  canonical_row := by
    intro A M P hK
    exact canonicalResolvedSequenceData_firstPages f P
  lifted := lifted (canonicalResolvedSequenceData.{u,v,w,x} f)
  lifted_hom := by
    intro A B M N P Q l m
    exact TensorPagesData.filteredMap_hom _ _ l _
  liftedPages := liftedPages (canonicalResolvedSequenceData.{u,v,w,x} f)
  map := map.{u,v,w,x} (canonicalResolvedSequenceData.{u,v,w,x} f)
  map_eq := map_eq (canonicalResolvedSequenceData.{u,v,w,x} f) (liftIndependent (canonicalResolvedSequenceData.{u,v,w,x} f))
  map_id := map_id (canonicalResolvedSequenceData.{u,v,w,x} f) (liftIndependent (canonicalResolvedSequenceData.{u,v,w,x} f))
  map_comp := map_comp (canonicalResolvedSequenceData.{u,v,w,x} f) (liftIndependent (canonicalResolvedSequenceData.{u,v,w,x} f))
  differential_naturality := by
    intro A B M N P Q a b r hr p n _
    exact map_differential (canonicalResolvedSequenceData.{u,v,w,x} f) P Q a b r hr p n
  innerMap := innerMap
  innerMap_eq := innerMap_eq
  second_naturality := hE2
  targetMap := targetMap
  targetMap_eq := targetMap_eq
  target_naturality := by
    intro A B M N P Q a b l m hl hm n
    rw [targetMap_eq P Q a b n l hl]
    change HomologicalComplex.homologyMap
      (lifted (canonicalResolvedSequenceData.{u,v,w,x} f) P Q l m).hom (-(n:ℤ)) ≫
        ((canonicalTargetComparison f Q).cochainHomologyIso n).hom =
      ((canonicalTargetComparison f P).cochainHomologyIso n).hom ≫ _
    rw [TensorPagesData.filteredMap_hom]
    exact target_cochainHomologyIso_natural b.hom l m hm
      (canonicalTargetComparison f P) (canonicalTargetComparison f Q) n
  target_preserves := by
    intro A B M N P Q a b p n
    rw [targetMap_eq P Q a b n (rightLift P Q a) (rightLift_lifts P Q a)]
    exact target_filtration_map_exists b.hom (rightLift P Q a) (leftLift P Q b)
      (leftLift_lifts P Q b) (canonicalTargetComparison f P) (canonicalTargetComparison f Q)
      (canonicalResolvedSequenceData.{u,v,w,x} f P).filtration (canonicalResolvedSequenceData.{u,v,w,x} f Q).filtration
      (canonicalResolvedSequenceData.{u,v,w,x} f P).formula (canonicalResolvedSequenceData.{u,v,w,x} f Q).formula p n
end PageMapAssembly

end FullSystemAssembly
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

noncomputable section
namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
set_option maxHeartbeats 500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open FiniteFiltrationConvergence
namespace NaturalSystem
variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R →+* S}
variable (T : NaturalSystem.{u,v,w,x} f)

/-- The map induced on actual successive quotients of the ordinary Tor target filtration. -/
def gradedTargetMap
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (a : A ⟶ B) (b : M ⟶ N) (p : ℤ) (n : ℕ) :=
  transportedChainGradedMap
    (T.lifted P Q (PageMapAssembly.rightLift P Q a) (PageMapAssembly.leftLift P Q b))
    (n : ℤ) ((T.sequence P).targetIso n) ((T.sequence Q).targetIso n) p

/-- The quotient map is induced by a filtration-step map restricting the ordinary Tor map. -/
theorem gradedTargetMap_induced
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (a : A ⟶ B) (b : M ⟶ N) (p : ℤ) (n : ℕ) :
    ∃ h : (resolvedTargetPiece f (T.sequence P) p n : ModuleCat ℤ) ⟶
        (resolvedTargetPiece f (T.sequence Q) p n : ModuleCat ℤ),
      (h ≫ (resolvedTargetPiece f (T.sequence Q) p n).arrow =
        (resolvedTargetPiece f (T.sequence P) p n).arrow ≫ T.targetMap P Q a b n) ∧
      (cokernel.π (Subobject.ofLE ((T.sequence P).targetPiece (p-1) n)
          ((T.sequence P).targetPiece p n) ((T.sequence P).targetPiece_increasing p n)) ≫
        T.gradedTargetMap P Q a b p n =
      h ≫ cokernel.π (Subobject.ofLE ((T.sequence Q).targetPiece (p-1) n)
          ((T.sequence Q).targetPiece p n) ((T.sequence Q).targetPiece_increasing p n))) := by
  let g := T.lifted P Q (PageMapAssembly.rightLift P Q a) (PageMapAssembly.leftLift P Q b)
  refine ⟨transportedCohomologyStepMap g (-(n : ℤ))
    ((T.sequence P).targetIso n) ((T.sequence Q).targetIso n) (-p), ?_, ?_⟩
  · exact transportedCohomologyStepMap_arrow g (-(n : ℤ))
      ((T.sequence P).targetIso n) ((T.sequence Q).targetIso n) (T.targetMap P Q a b n)
      (T.target_naturality P Q a b (PageMapAssembly.rightLift P Q a)
        (PageMapAssembly.leftLift P Q b) (PageMapAssembly.rightLift_lifts P Q a)
        (PageMapAssembly.leftLift_lifts P Q b) n) (-p)
  · exact transportedChainGradedMap_π g (n : ℤ)
      ((T.sequence P).targetIso n) ((T.sequence Q).targetIso n) p

/-- The system maps agree at stable pages with the maps induced on its finite target quotients. -/
theorem limit_naturality
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (a : A ⟶ B) (b : M ⟶ N) (r : ℤ) (hr : 2 ≤ r) (p : ℤ) (n : ℕ)
    (hsP : Stabilized (T.sequence P).filtration r (-p) (-(n : ℤ)))
    (hsQ : Stabilized (T.sequence Q).filtration r (-p) (-(n : ℤ))) :
    T.map P Q a b r p (n : ℤ) ≫ ((T.sequence Q).targetLimitIso n r (by omega) p hsQ).hom =
      ((T.sequence P).targetLimitIso n r (by omega) p hsP).hom ≫
        T.gradedTargetMap P Q a b p n := by
  rw [T.map_eq P Q a b (PageMapAssembly.rightLift P Q a) (PageMapAssembly.leftLift P Q b)
    (PageMapAssembly.rightLift_lifts P Q a) (PageMapAssembly.leftLift_lifts P Q b)
    r p (n : ℤ) hr]
  exact mappedChainPageLimitIso_natural
    (T.lifted P Q (PageMapAssembly.rightLift P Q a) (PageMapAssembly.leftLift P Q b))
    (n : ℤ) ((T.sequence P).targetIso n) ((T.sequence Q).targetIso n)
    (T.sequence P).pages (T.sequence Q).pages
    (T.liftedPages P Q (PageMapAssembly.rightLift P Q a) (PageMapAssembly.leftLift P Q b))
    (T.sequence P).convergence (T.sequence Q).convergence r (by omega) p hsP hsQ
end NaturalSystem
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open CategoryTheory
section CanonicalSecondPage

open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open DoubleComplexFirstPages FiniteDiagonalFiltrations
set_option maxHeartbeats 1500000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable {C C' : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ}
variable {Q Q' : ChainComplex (ModuleCat.{max v x} S) ℕ}
variable [(tensorCochainBicomplex C (restrictionComplex f (ComplexShape.down ℕ) Q)).HasTotal (ComplexShape.up ℤ)]
variable [(tensorCochainBicomplex C' (restrictionComplex f (ComplexShape.down ℕ) Q')).HasTotal (ComplexShape.up ℤ)]
variable (B : TensorPagesData C (restrictionComplex f (ComplexShape.down ℕ) Q))
variable (B' : TensorPagesData C' (restrictionComplex f (ComplexShape.down ℕ) Q'))

def tensorE2RowIso (p q : ℕ) :
    chainPage B.filtration B.pages 2 p (p+q) ≅
      ModuleCat.of ℤ (Homology (rowHomologyComplex.{u,v,w,x} f C Q q) p) :=
  eqToIso (congrArg (PageCohomology.object B.filtration B.pages 2 (-(p : ℤ)))
      (by omega : -((p : ℤ)+q) = -(p : ℤ) + -(q : ℤ))) ≪≫
    ((DoubleComplexFirstPages.system _).row _ (tensorCochainBicomplex_finite C
      (restrictionComplex f (ComplexShape.down ℕ) Q)) B.filtration B.formula B.pages).secondIso
      (-(p : ℤ)) (-(q : ℤ)) ≪≫
    changeOfRingsE2Iso.{u,w,x,v} f C Q p q

theorem tensorE2RowIso_naturality
    (l : C ⟶ C') (m : Q ⟶ Q') (p q : ℕ) :
    @Eq (chainPage B.filtration B.pages 2 p (p+q) ⟶
      ModuleCat.of ℤ (Homology (rowHomologyComplex.{u,v,w,x} f C' Q' q) p))
    ((TensorPagesData.mapData.{u,w,max v x} B B' l
      (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m)).map
      2 (-(p : ℤ)) (-((p : ℤ)+q)) ≫ (tensorE2RowIso.{u,v,w,x} (C := C') (Q := Q') f B' p q).hom)
    ((tensorE2RowIso.{u,v,w,x} (C := C) (Q := Q) f B p q).hom ≫ (P103.Specs.Ch10.Comparison.quotientHomology (S := ℤ) (ComplexShape.down ℕ) p).map
      (rowHomologyMap.{u,v,w,x} f l Q q ≫ rowHomologyCoefficientMap.{u,w,x,v} f C' m q)) := by
  let F := TensorPagesData.mapData.{u,w,max v x} B B' l
    (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m)
  let S := DoubleComplexFirstPages.system (ModuleCat.{max v w x} ℤ)
  let K := tensorCochainBicomplex C (restrictionComplex f (ComplexShape.down ℕ) Q)
  let L := tensorCochainBicomplex C' (restrictionComplex f (ComplexShape.down ℕ) Q')
  let hK := tensorCochainBicomplex_finite C (restrictionComplex f (ComplexShape.down ℕ) Q)
  let hL := tensorCochainBicomplex_finite C' (restrictionComplex f (ComplexShape.down ℕ) Q')
  let row := S.row K hK B.filtration B.formula B.pages
  let row' := S.row L hL B'.filtration B'.formula B'.pages
  have hrow := (S.row_naturality K L hK hL B.filtration B'.filtration B.formula B'.formula B.pages B'.pages
    (tensorCochainBicomplexMap l (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m))
    (B.filteredMap B' l (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m))
    (B.filteredMap_hom B' l (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m))
    F (-(p : ℤ)) (-(q : ℤ))).2.2
  have hcast := eqToHom_naturality (fun n : ℤ => F.map 2 (-(p : ℤ)) n)
    (by omega : -((p : ℤ)+q) = -(p : ℤ) + -(q : ℤ))
  have hbridge := changeOfRingsE2Iso_naturality.{u,w,x,v} f l m p q
  dsimp only [tensorE2RowIso, Iso.trans_hom, eqToIso]
  rw [← Category.assoc, hcast, Category.assoc, ← Category.assoc _
    ((S.row L hL B'.filtration B'.formula B'.pages).secondIso (-(p:ℤ)) (-(q:ℤ))).hom,
    hrow, Category.assoc]
  erw [hbridge]
  simp only [Category.assoc]
  rfl

end CanonicalSecondPage
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open CategoryTheory
section SecondPageNaturality

open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open PageMapAssembly
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compose_natural_squares
    {C : Type*} [Category C] {X X' Y Y' Z Z' : C}
    {f : X ⟶ X'} {g : Y ⟶ Y'} {h : Z ⟶ Z'}
    {i : X ⟶ Y} {i' : X' ⟶ Y'} {j : Y ⟶ Z} {j' : Y' ⟶ Z'}
    (hi : f ≫ i' = i ≫ g) (hj : g ≫ j' = j ≫ h) :
    f ≫ (i' ≫ j') = (i ≫ j) ≫ h := by
  rw [← Category.assoc, hi, Category.assoc, hj, ← Category.assoc]

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
private theorem canonicalSecondIso_hom_aux
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (p q : ℕ) :
    letI := innerTorModule f P.right.complex q
    ∀ (U : LeftResolution Sᵐᵒᵖ (TorWith P.right (Restricted f S) q)) (hU : U.IsProjective),
    @Eq (chainPage (canonicalResolvedSequenceData.{u,v,w,x} f P).filtration
      (canonicalResolvedSequenceData.{u,v,w,x} f P).pages 2 p (p+q) ⟶ ModuleCat.of ℤ (TorWith U M p))
    (((canonicalResolvedSequenceData.{u,v,w,x} f P).secondIso p q U hU).hom)
    ((tensorE2RowIso.{u,v,max u w,max u x} (C := P.right.complex) (Q := P.left.complex) f
        (canonicalResolvedSequenceData.{u,v,w,x} f P).toTensorPagesData p q).hom ≫
      (rowHomologyTorEquiv.{u,v,max u w,max u x} f P.right.complex M P.left P.left_projective q U hU p).toModuleIso.hom) := by
  intro U hU
  letI := innerTorModule f P.right.complex q
  let E := canonicalResolvedSequenceData.{u,v,w,x} f P
  let hFlat (j : ℕ) := P103.Ch02.FlatnessTests.projective_flat.{v,max u v x,max u v w}
    S (P.left.complex.X j) (P.left_projective j)
  let a := rowHomologyComplexIso.{u,v,max u w,max u x} f P.right.complex P.left.complex hFlat q
  let b := ordinaryRowsExtensionIso P.right.complex
    (restrictionComplex f (ComplexShape.down ℕ) P.left.complex) q
  let H := quotientHomology (S := ℤ) (ComplexShape.down ℕ) p
  let c := H.mapIso a.symm
  let e := changeOfRingsE2Iso.{u,max u w,max u x,v} f P.right.complex P.left.complex p q
  have hf : negativeExtensionQuotientIso (E.rowTensor q).iso.symm p = e ≪≫ c :=
    negativeExtensionQuotientIso_comp b a.symm p
  let hBalance := E.balance q U hU
  let t := (balanceEquiv hBalance.choose hBalance.choose_spec.1 hBalance.choose_spec.2 p).symm.toModuleIso
  let s := E.firstPages.secondIso (-(p : ℤ)) (-(q : ℤ))
  let i := eqToIso (congrArg (PageCohomology.object E.filtration E.pages 2 (-(p : ℤ)))
    (by omega : -((p : ℤ)+q) = -(p : ℤ) + -(q : ℤ)))
  change (i ≪≫ s ≪≫ negativeExtensionQuotientIso (E.rowTensor q).iso.symm p ≪≫ t).hom =
    (i ≪≫ s ≪≫ e).hom ≫ (c ≪≫ t).hom
  rw [hf]
  simp only [Iso.trans_hom, Category.assoc]

theorem canonical_second_naturality : CanonicalSecondNaturality.{u,v,w,x} f := by
  intro A B M N P Q a b p q
  letI := innerTorModule f P.right.complex q
  letI := innerTorModule f Q.right.complex q
  intro U V hU hV k hk
  let E := canonicalResolvedSequenceData.{u,v,w,x} f P
  let E' := canonicalResolvedSequenceData.{u,v,w,x} f Q
  let l := rightLift P Q a
  let m := leftLift P Q b
  have hr := tensorE2RowIso_naturality.{u,v,max u w,max u x}
    (C := P.right.complex) (C' := Q.right.complex) (Q := P.left.complex) (Q' := Q.left.complex) f
    E.toTensorPagesData E'.toTensorPagesData l m p q
  have ht := rowHomologyTorEquiv_naturality.{u,v,max u w,max u x} f l P.left Q.left
    P.left_projective Q.left_projective b.hom m (leftLift_lifts P Q b) q U V hU hV k hk p
  rw [canonicalSecondIso_hom_aux f Q p q V hV, canonicalSecondIso_hom_aux f P p q U hU]
  exact compose_natural_squares hr ht

end SecondPageNaturality
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor

/-- The natural change-of-rings sequence, simultaneously for every projective choice. -/
def changeOfRingsSystem {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) :
    NaturalSystem.{u,v,w,x} f :=
  PageMapAssembly.naturalSystem.{u,v,w,x} f (canonical_second_naturality.{u,v,w,x} f)

/-- HA-B07: existence, naturality and coherent resolution independence, with no flatness of S over R. -/
theorem natural_sequence : Specs.NaturalSequence.{u,v,w,x} := by
  intro R S _ _ f
  exact ⟨changeOfRingsSystem.{u,v,w,x} f⟩

end AdvancedHomologicalAlgebra.ChangeOfRingsTor
