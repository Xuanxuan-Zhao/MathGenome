import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.P103.Ch10.Comparison
import MathGenome.Internal.AlgebraCore.P103.Ch10.TotalComplexConstruction
import MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.AlgebraCore.P103.Ch10.AugmentedAssembly
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace P103.Ch11.TorBalance
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
noncomputable section
universe u v w x y
variable {R : Type u} [Ring R]

section Restriction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem restriction_cycles (C : ChainComplex (ModuleCat.{v} R) ℤ)
    (hC : SupportedIn C (Set.Ici 0)) (n : ℕ) :
    cycles (C.restriction nonnegativeChainEmbedding) n = cycles C (n : ℤ) := by
  unfold cycles
  rw [ChainComplex.next]
  cases n with
  | zero =>
    rw [ChainComplex.next_nat_zero]
    change LinearMap.ker (C.d 0 0).hom = LinearMap.ker (C.d 0 (0 - 1)).hom
    rw [C.shape 0 0 (by simp [ComplexShape.down_Rel]),
      P103.Ch10.Complexes.supported_d_to C _ hC 0 (0 - 1) (by simp)]
    simp
  | succ n =>
    rw [ChainComplex.next_nat_succ]
    change LinearMap.ker (C.d (↑(n + 1)) n).hom = LinearMap.ker (C.d (↑(n + 1)) (↑(n + 1) - 1)).hom
    have hn : (↑(n + 1) : ℤ) - 1 = n := by omega
    rw [hn]

theorem restriction_boundaries (C : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℕ) :
    boundaries (C.restriction nonnegativeChainEmbedding) n = boundaries C (n : ℤ) := by
  unfold boundaries
  rw [ChainComplex.prev, ChainComplex.prev]
  change LinearMap.range (C.d (↑(n + 1)) n).hom = LinearMap.range (C.d ((n : ℤ) + 1) n).hom
  rw [Nat.cast_add, Nat.cast_one]

/-- Restriction of a nonnegative integer complex preserves its explicit homology. -/
def restrictionHomologyEquiv (C : ChainComplex (ModuleCat.{v} R) ℤ)
    (hC : SupportedIn C (Set.Ici 0)) (n : ℕ) :
    Homology (C.restriction nonnegativeChainEmbedding) n ≃ₗ[R] Homology C (n : ℤ) := by
  let e : cycles (C.restriction nonnegativeChainEmbedding) n ≃ₗ[R] cycles C (n : ℤ) :=
    LinearEquiv.ofEq _ _ (restriction_cycles C hC n)
  refine Submodule.Quotient.equiv _ _ e ?_
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (e x : C.X n) ∈ boundaries C n
    have hv : (e x : C.X n) = x.val := by rfl
    rw [hv, ← restriction_boundaries C n]
    exact hx
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    change ((e.symm z).val : C.X n) ∈ boundaries (C.restriction nonnegativeChainEmbedding) n
    have hv : ((e.symm z).val : C.X n) = z.val := by rfl
    rw [hv, restriction_boundaries C n]
    exact hz

@[simp] theorem restrictionHomologyEquiv_class (C : ChainComplex (ModuleCat.{v} R) ℤ)
    (hC : SupportedIn C (Set.Ici 0)) (n : ℕ)
    (z : cycles (C.restriction nonnegativeChainEmbedding) n) :
    restrictionHomologyEquiv C hC n (homologyClass _ n z) =
      homologyClass C (n : ℤ) (LinearEquiv.ofEq _ _ (restriction_cycles C hC n) z) := rfl

theorem restrictionHomologyEquiv_natural
    {C D : ChainComplex (ModuleCat.{v} R) ℤ}
    (hC : SupportedIn C (Set.Ici 0)) (hD : SupportedIn D (Set.Ici 0))
    (f : C ⟶ D) (n : ℕ) :
    (restrictionHomologyEquiv D hD n).toLinearMap.comp
      (homologyMap (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) n) =
    (homologyMap f (n : ℤ)).comp (restrictionHomologyEquiv C hC n).toLinearMap := by
  apply (cycleBoundaries (C.restriction nonnegativeChainEmbedding) n).quot_hom_ext
  intro z
  change restrictionHomologyEquiv D hD n
    (homologyMap (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) n (homologyClass _ n z)) =
    homologyMap f (n : ℤ) (restrictionHomologyEquiv C hC n (homologyClass _ n z))
  rw [P103.Ch10.Complexes.homologyMap_apply, restrictionHomologyEquiv_class,
    restrictionHomologyEquiv_class, P103.Ch10.Complexes.homologyMap_apply]
  congr 1

theorem quasiIsomorphism_restriction_nonnegative
    {C D : ChainComplex (ModuleCat.{v} R) ℤ}
    (hC : SupportedIn C (Set.Ici 0)) (hD : SupportedIn D (Set.Ici 0))
    (f : C ⟶ D) (hf : QuasiIsomorphism f) :
    QuasiIsomorphism (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) := by
  intro n
  have he := restrictionHomologyEquiv_natural hC hD f n
  have hb := (hf n).comp (restrictionHomologyEquiv C hC n).bijective
  have hb' : Function.Bijective ((homologyMap f (n : ℤ)).comp
      (restrictionHomologyEquiv C hC n).toLinearMap) := hb
  rw [← he] at hb'
  constructor
  · intro x y hxy
    apply hb'.injective
    exact congrArg (restrictionHomologyEquiv D hD n) hxy
  · intro y
    obtain ⟨x, hx⟩ := hb'.surjective (restrictionHomologyEquiv D hD n y)
    exact ⟨x, (restrictionHomologyEquiv D hD n).injective hx⟩
end Restriction

section TensorAugmentationHelpers
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
theorem quasiIsomorphism_comp_any {S : Type w} [Ring S] {ι : Type*}
    {c : ComplexShape ι} {C D E : HomologicalComplex (ModuleCat.{v} S) c}
    {f : C ⟶ D} {g : D ⟶ E} (hf : QuasiIsomorphism f) (hg : QuasiIsomorphism g) :
    QuasiIsomorphism (f ≫ g) := by
  intro n
  have hc : homologyMap (f ≫ g) n = (homologyMap g n).comp (homologyMap f n) :=
    P103.Ch10.Complexes.homologyMap_comp f g n
  rw [hc]
  exact (hg n).comp (hf n)

theorem quasiIsomorphism_of_iso_any {S : Type w} [Ring S] {ι : Type*}
    {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{v} S) c}
    (e : C ≅ D) : QuasiIsomorphism e.hom := by
  intro n
  have hl : Function.LeftInverse (homologyMap e.inv n) (homologyMap e.hom n) := by
    intro z
    have he := P103.Ch10.Complexes.homologyMap_comp e.hom e.inv n
    rw [e.hom_inv_id, P103.Ch10.Complexes.homologyMap_id] at he
    exact (LinearMap.congr_fun he z).symm
  have hr : Function.RightInverse (homologyMap e.inv n) (homologyMap e.hom n) := by
    intro z
    have he := P103.Ch10.Complexes.homologyMap_comp e.inv e.hom n
    rw [e.inv_hom_id, P103.Ch10.Complexes.homologyMap_id] at he
    exact (LinearMap.congr_fun he z).symm
  exact ⟨hl.injective, hr.surjective⟩

/-- A functor applied to the retained ordinary terms recovers its ordinary complex. -/
def restrictExtendMapIso {S : Type w} [Ring S]
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (F : ModuleCat.{v} R ⥤ ModuleCat.{x} S) [F.PreservesZeroMorphisms] :
    (((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj (extendNonnegativeChain C)).restriction
      nonnegativeChainEmbedding) ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => F.mapIso (C.extendXIso nonnegativeChainEmbedding (i := n) rfl)) (by
      intro i j _
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← F.map_comp, ← F.map_comp]
      congr 1
      erw [C.extend_d_eq nonnegativeChainEmbedding (i := i) (j := j) rfl rfl]
      simp)

/-- The vertical tensor augmentation, regarded as an augmentation of flipped columns. -/
def tensorRowAugmentation {B : Type w} [AddCommGroup B] [Module R B]
    (Q : P103.Specs.Ch10.Comparison.LeftResolution R B)
    (C : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℤ) :
    (tensorBicomplex C (extendNonnegativeChain Q.complex)).flip.X 0 ⟶
      ((tensorFunctor B).mapHomologicalComplex (ComplexShape.down ℤ)).obj C where
  f p := ModuleCat.ofHom (tensorMap LinearMap.id
    (Q.ε.comp (Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom))
  comm' p p' _ := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl

theorem tensorRowAugmentation_square {B : Type w} [AddCommGroup B] [Module R B]
    (Q : P103.Specs.Ch10.Comparison.LeftResolution R B)
    (C : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℤ) :
    (tensorBicomplex C (extendNonnegativeChain Q.complex)).flip.d 1 0 ≫
      tensorRowAugmentation Q C = 0 := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  change tmul R a (Q.ε ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
    (((extendNonnegativeChain Q.complex).d 1 0).hom b))) = 0
  have hd : (extendNonnegativeChain Q.complex).d 1 0 ≫
      (Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom =
      (Q.complex.extendXIso nonnegativeChainEmbedding (i := 1) rfl).hom ≫ Q.complex.d 1 0 := by
    erw [Q.complex.extend_d_eq nonnegativeChainEmbedding
      (i := 1) (j := 0) (i' := (1 : ℤ)) (j' := (0 : ℤ)) rfl rfl]
    simp
  have hb := congrArg (fun k => k.hom b) hd
  change (Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
      (((extendNonnegativeChain Q.complex).d 1 0).hom b) =
    (Q.complex.d 1 0).hom
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 1) rfl).hom.hom b) at hb
  rw [hb]
  have he : Q.ε ((Q.complex.d 1 0).hom
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 1) rfl).hom.hom b)) = 0 := by
    apply (show (Q.complex.d 1 0).hom
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 1) rfl).hom.hom b) ∈
      LinearMap.ker Q.ε from ?_)
    rw [← Q.exact_zero]
    exact ⟨_, rfl⟩
  rw [he]
  simp [tmul]
end TensorAugmentationHelpers

abbrev tensorBicomplex := @P103.Specs.Ch11.TorBalance.tensorBicomplex.{u,v,w}

theorem tensor_differentials : tensor_differentialsType.{u,v,w} := by
  intro R _ C D p p' q q'
  exact ⟨rfl, rfl⟩

theorem tensorTotal_d : tensorTotal_dType.{u,v,w} := by
  intro R _ C D p q n h a b
  have hd := P103.Ch10.TotalComplexAssembly.chain_totalInclusion_d
    (tensorBicomplex C D) p q n (n - 1) h
  have h₁ : (p - 1) + q = n - 1 := by omega
  have h₂ : p + (q - 1) = n - 1 := by omega
  rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h₁,
    HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h₂] at hd
  exact congrArg (fun f => f.hom (tmul R a b)) hd

theorem tensor_supported : tensor_supportedType.{u,v,w} := by
  intro R _ C D a b hC hD p q h
  change Subsingleton (Tensor R (C.X p) (D.X q))
  apply subsingleton_of_forall_eq 0
  intro z
  induction z using P103.BalancedTensor.induction_on with
  | h0 => rfl
  | ht x y =>
      rcases h with hp | hq
      · haveI := hC p (by simpa using hp)
        rw [Subsingleton.elim x 0, zero_tmul]
      · haveI := hD q (by simpa using hq)
        rw [Subsingleton.elim y 0, tmul_zero]
  | ha x y hx hy => rw [hx, hy, add_zero]

@[simp] theorem tensorBicomplexMap_id
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) :
    tensorBicomplexMap (𝟙 C) (𝟙 D) = 𝟙 (tensorBicomplex C D) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

@[simp] theorem tensorBicomplexMap_comp
    {C C' C'' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {D D' D'' : ChainComplex (ModuleCat.{w} R) ℤ}
    (f : C ⟶ C') (f' : C' ⟶ C'') (g : D ⟶ D') (g' : D' ⟶ D'') :
    tensorBicomplexMap (f ≫ f') (g ≫ g') =
      tensorBicomplexMap f g ≫ tensorBicomplexMap f' g' := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

@[simp] theorem ordinary_tensor_supported
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    SupportedQuadrant (tensorBicomplex (extendNonnegativeChain C)
      (extendNonnegativeChain D)) 0 0 :=
  tensor_supported _ _ 0 0
    (P103.Ch10.Complexes.extendNonnegativeChain_supported C)
    (P103.Ch10.Complexes.extendNonnegativeChain_supported D)

/-- Projective coefficients preserve injections without requiring that the
tested modules live in the coefficient module's universe. -/
theorem projective_tensor_injective
    {M : Type w} [AddCommGroup M] [Module R M] (hM : Module.Projective R M)
    {A : Type v} {B : Type x} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup B] [Module Rᵐᵒᵖ B]
    (f : A →ₗ[Rᵐᵒᵖ] B) (hf : Function.Injective f) :
    Function.Injective (tensorMap f (LinearMap.id : M →ₗ[R] M)) := by
  let eA : ULift.{max u v w x} A ≃ₗ[Rᵐᵒᵖ] A := ULift.moduleEquiv
  let eB : ULift.{max u v w x} B ≃ₗ[Rᵐᵒᵖ] B := ULift.moduleEquiv
  let f' := eB.symm.toLinearMap.comp (f.comp eA.toLinearMap)
  have hflat := P103.Ch02.FlatnessTests.projective_flat.{u,w,max v x} R M hM
  have hinj := hflat _ _ f' (eB.symm.injective.comp (hf.comp eA.injective))
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
  intro x y hxy
  have h' : tensorMap eA.symm.toLinearMap LinearMap.id x =
      tensorMap eA.symm.toLinearMap LinearMap.id y := by
    apply hinj
    change ((tensorMap f' (LinearMap.id : M →ₗ[R] M)).comp
      (tensorMap eA.symm.toLinearMap LinearMap.id)) x =
      ((tensorMap f' (LinearMap.id : M →ₗ[R] M)).comp
        (tensorMap eA.symm.toLinearMap LinearMap.id)) y
    rw [hrect]
    exact congrArg (tensorMap eB.symm.toLinearMap LinearMap.id) hxy
  have hh := congrArg (tensorMap eA.toLinearMap (LinearMap.id : M →ₗ[R] M)) h'
  change ((tensorMap eA.toLinearMap (LinearMap.id : M →ₗ[R] M)).comp
      (tensorMap eA.symm.toLinearMap LinearMap.id)) x =
    ((tensorMap eA.toLinearMap (LinearMap.id : M →ₗ[R] M)).comp
      (tensorMap eA.symm.toLinearMap LinearMap.id)) y at hh
  simpa only [hback, LinearMap.id_apply] using hh

/-- Exactness in the middle, including non-surjective outgoing maps. -/
theorem projective_tensor_exact
    {M : Type w} [AddCommGroup M] [Module R M] (hM : Module.Projective R M)
    {A : Type v} {B : Type x} {C : Type y} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup B] [Module Rᵐᵒᵖ B] [AddCommGroup C] [Module Rᵐᵒᵖ C]
    (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C) (he : Function.Exact f g) :
    Function.Exact (tensorMap f (LinearMap.id : M →ₗ[R] M))
      (tensorMap g (LinearMap.id : M →ₗ[R] M)) := by
  have he' : Function.Exact f g.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    simpa only [LinearMap.ker_rangeRestrict] using LinearMap.exact_iff.mp he
  have hr := (P103.HomTensorExactness.tensor_first_rightExact f g.rangeRestrict he'
    (LinearMap.surjective_rangeRestrict g) (tensorMap f (LinearMap.id : M →ₗ[R] M)).toAddMonoidHom
    (by intros; rfl) (tensorMap g.rangeRestrict LinearMap.id).toAddMonoidHom
    (by intros; rfl)).1
  have hi := projective_tensor_injective hM (LinearMap.range g).subtype Subtype.val_injective
  have hcomp : (tensorMap (LinearMap.range g).subtype (LinearMap.id : M →ₗ[R] M)).comp
      (tensorMap g.rangeRestrict LinearMap.id) = tensorMap g LinearMap.id := by
    apply tensor_hom_ext
    intro a m
    rfl
  intro z
  rw [← hcomp]
  change tensorMap (LinearMap.range g).subtype LinearMap.id
      (tensorMap g.rangeRestrict (LinearMap.id : M →ₗ[R] M) z) = 0 ↔ _
  rw [← map_zero (tensorMap (LinearMap.range g).subtype (LinearMap.id : M →ₗ[R] M)),
    hi.eq_iff]
  exact hr z

section RightProjective
open P103.Specs.Ch02.FlatnessTests
open private oppositeFlip oppositeFlip_tmul from MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem right_projective_tensor_injective
    {M : Type w} [AddCommGroup M] [Module Rᵐᵒᵖ M] (hM : Module.Projective Rᵐᵒᵖ M)
    {A : Type v} {B : Type x} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Injective f) :
    Function.Injective (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f) := by
  letI := doubleOppositeModule R A
  letI := doubleOppositeModule R B
  let fop : A →ₗ[Rᵐᵒᵖᵐᵒᵖ] B :=
    { f.toAddMonoidHom with map_smul' := fun r a => f.map_smul r.unop.unop a }
  let eA := oppositeFlip (R := R) (A := M) (B := A)
  let eB := oppositeFlip (R := R) (A := M) (B := B)
  have hcomm (z : Tensor R M A) :
      eB (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f z) =
        tensorMap fop LinearMap.id (eA z) := by
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht m a => rfl
    | ha z z' hz hz' => simp [hz, hz']
  have hinj := projective_tensor_injective (R := Rᵐᵒᵖ) hM fop hf
  intro z z' hz
  apply eA.injective
  apply hinj
  rw [← hcomm, ← hcomm, hz]

theorem right_projective_tensor_exact
    {M : Type w} [AddCommGroup M] [Module Rᵐᵒᵖ M] (hM : Module.Projective Rᵐᵒᵖ M)
    {A : Type v} {B : Type x} {C : Type y} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (he : Function.Exact f g) :
    Function.Exact (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f)
      (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) g) := by
  have he' : Function.Exact f g.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    simpa only [LinearMap.ker_rangeRestrict] using LinearMap.exact_iff.mp he
  have hr := (P103.HomTensorExactness.tensorSecond_rightExact f g.rangeRestrict he'
    (LinearMap.surjective_rangeRestrict g)
    (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f).toAddMonoidHom
    (tensorMap LinearMap.id g.rangeRestrict).toAddMonoidHom
    (by intros; rfl) (by intros; rfl)).1
  have hi := right_projective_tensor_injective hM (LinearMap.range g).subtype
    Subtype.val_injective
  have hcomp : (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) (LinearMap.range g).subtype).comp
      (tensorMap LinearMap.id g.rangeRestrict) = tensorMap LinearMap.id g := by
    apply tensor_hom_ext
    intro m a
    rfl
  intro z
  rw [← hcomp]
  change tensorMap LinearMap.id (LinearMap.range g).subtype
      (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) g.rangeRestrict z) = 0 ↔ _
  rw [← map_zero (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) (LinearMap.range g).subtype),
    hi.eq_iff]
  exact hr z

end RightProjective

theorem lift_independent : lift_independentType.{u,v,w} := by
  intro R _ A A' B B' _ _ _ _ _ _ _ _ P P' Q Q' hP hQ f g l l' m m' hl hl' hm hm' n
  have el := P103.Ch10.Comparison.chain_homology_independent Rᵐᵒᵖ ℤ
    (tensorFunctor B) A A' P P' hP f l l' n hl hl'
  have el' : homologyMap (tensorFirstMap l B) n = homologyMap (tensorFirstMap l' B) n :=
    congrArg ModuleCat.Hom.hom el
  have er := P103.Ch10.Comparison.chain_homology_independent R ℤ
    (leftTensorFunctor A') B B' Q Q' hQ g m m' n hm hm'
  have er' : homologyMap
      (((leftTensorFunctor A').mapHomologicalComplex (ComplexShape.down ℕ)).map m) n =
      homologyMap
      (((leftTensorFunctor A').mapHomologicalComplex (ComplexShape.down ℕ)).map m') n :=
    congrArg ModuleCat.Hom.hom er
  constructor
  · simp only [P103.Ch10.Complexes.homologyMap_comp, el']
  · simp only [leftTensorMap, P103.Ch10.Complexes.homologyMap_comp, er']

theorem tensorTotalMap_inclusion
    {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℤ} (f : C ⟶ C') (g : D ⟶ D')
    (p q n : ℤ) (h : p + q = n) (a : C.X p) (b : D.X q) :
    ((tensorTotalMap f g).f n).hom (tensorInclusion C D p q n h (tmul R a b)) =
      tensorInclusion C' D' p q n h (tmul R ((f.f p).hom a) ((g.f q).hom b)) := by
  exact congrArg (fun k => k.hom (tmul R a b))
    (HomologicalComplex₂.ιTotal_map _ _ (tensorBicomplexMap f g) (ComplexShape.down ℤ) p q n h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extension of a map evaluated on a retained ordinary term. -/
theorem extendMap_inv_apply
    {S : Type*} [Ring S] {C C' : ChainComplex (ModuleCat.{v} S) ℕ}
    (f : C ⟶ C') (p : ℕ) (a : C.X p) :
    ((HomologicalComplex.extendMap f nonnegativeChainEmbedding).f (p : ℤ)).hom
        ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a) =
      (C'.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom ((f.f p).hom a) := by
  have he := HomologicalComplex.extendMap_f f nonnegativeChainEmbedding
    (i := p) (i' := (p : ℤ)) rfl
  have hc : (C.extendXIso nonnegativeChainEmbedding (i := p) (i' := (p : ℤ)) rfl).inv ≫
      (HomologicalComplex.extendMap f nonnegativeChainEmbedding).f (p : ℤ) =
      f.f p ≫ (C'.extendXIso nonnegativeChainEmbedding (i := p) (i' := (p : ℤ)) rfl).inv := by
    rw [he]
    simp
  exact congrArg (fun k => k.hom a) hc

/-- Formula for the ordinary inclusion on an elementary tensor. -/
theorem ordinaryInclusion_tmul
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p + q = n)
    (a : C.X p) (b : D.X q) :
    ordinaryInclusion C D p q n h (tmul R a b) =
      tensorInclusion (extendNonnegativeChain C) (extendNonnegativeChain D)
        (p : ℤ) (q : ℤ) (n : ℤ) (by exact_mod_cast h)
        (tmul R ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
          ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The total map acts on an ordinary summand by tensoring its two components. -/
theorem ordinaryTotalMap_inclusion
    {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ} (f : C ⟶ C') (g : D ⟶ D')
    (p q n : ℕ) (h : p + q = n) (a : C.X p) (b : D.X q) :
    ((ordinaryTotalMap f g).f n).hom (ordinaryInclusion C D p q n h (tmul R a b)) =
      ordinaryInclusion C' D' p q n h (tmul R ((f.f p).hom a) ((g.f q).hom b)) := by
  have ht := tensorTotalMap_inclusion
    (HomologicalComplex.extendMap f nonnegativeChainEmbedding)
    (HomologicalComplex.extendMap g nonnegativeChainEmbedding)
    (p : ℤ) (q : ℤ) (n : ℤ) (by exact_mod_cast h)
    ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
    ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)
  rw [extendMap_inv_apply, extendMap_inv_apply] at ht
  simp only [ordinaryInclusion_tmul]
  convert ht using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The nonnegative pure tensor summands jointly determine a total-term map. -/
theorem ordinaryTotal_hom_ext
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ)
    {E : ModuleCat.{max v w} ℤ} (f g : (ordinaryTotal C D).X n ⟶ E)
    (h : ∀ (p q : ℕ) (hpq : p + q = n) (a : C.X p) (b : D.X q),
      f.hom (ordinaryInclusion C D p q n hpq (tmul R a b)) =
        g.hom (ordinaryInclusion C D p q n hpq (tmul R a b))) : f = g := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p + q = (n : ℤ) at hpq
  apply ModuleCat.hom_ext
  change f.hom.comp (tensorInclusion (extendNonnegativeChain C)
    (extendNonnegativeChain D) p q n hpq) =
    g.hom.comp (tensorInclusion (extendNonnegativeChain C)
    (extendNonnegativeChain D) p q n hpq)
  apply LinearMap.toAddMonoidHom_injective
  apply P103.BalancedTensor.hom_ext
  intro a b
  by_cases hp : 0 ≤ p
  · by_cases hq : 0 ≤ q
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      have hab := h p q (by exact_mod_cast hpq)
        ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom.hom a)
        ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).hom.hom b)
      rw [ordinaryInclusion_tmul] at hab
      have ha : (C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom
          ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom.hom a) = a :=
        congrArg (fun k => k.hom a) (C.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom_inv_id
      have hb : (D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom
          ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).hom.hom b) = b :=
        congrArg (fun k => k.hom b) (D.extendXIso nonnegativeChainEmbedding (i := q) rfl).hom_inv_id
      rw [ha, hb] at hab
      exact hab
    · haveI := P103.Ch10.Complexes.extendNonnegativeChain_supported D q (by simpa using hq)
      rw [Subsingleton.elim b 0, tmul_zero]
      simp
  · haveI := P103.Ch10.Complexes.extendNonnegativeChain_supported C p (by simpa using hp)
    rw [Subsingleton.elim a 0, zero_tmul]
    simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every augmentation specified by its summand formulas is natural in both factors. -/
theorem augmentation_natural : augmentation_naturalType.{u,v,w} := by
  intro R _ A A' B B' _ _ _ _ _ _ _ _ P P' Q Q' f g l m hl hm α β
  constructor
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ordinaryTotal_hom_ext P.complex Q.complex n
    intro p q h a b
    change (β.left.f n).hom (((ordinaryTotalMap l m).f n).hom
      (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b))) =
      ((tensorSecondMap P'.complex g).f n).hom
        (((tensorFirstMap l B).f n).hom
          ((α.left.f n).hom (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b))))
    rw [ordinaryTotalMap_inclusion]
    by_cases hq : q = 0
    · subst q
      simp only [Nat.add_zero] at h
      subst n
      rw [β.left_zero, α.left_zero]
      change tmul R ((l.f p).hom a) (Q'.ε ((m.f 0).hom b)) =
        tmul R ((l.f p).hom a) (g (Q.ε b))
      exact congrArg (tmul R ((l.f p).hom a)) (LinearMap.congr_fun hm b)
    · have ha := LinearMap.congr_fun (α.left_positive p q n h hq) (tmul R a b)
      have hb := LinearMap.congr_fun (β.left_positive p q n h hq)
        (tmul R ((l.f p).hom a) ((m.f q).hom b))
      change (α.left.f n).hom (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b)) = 0 at ha
      change (β.left.f n).hom (ordinaryInclusion P'.complex Q'.complex p q n h
        (tmul R ((l.f p).hom a) ((m.f q).hom b))) = 0 at hb
      rw [ha, hb, map_zero, map_zero]
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ordinaryTotal_hom_ext P.complex Q.complex n
    intro p q h a b
    change (β.right.f n).hom (((ordinaryTotalMap l m).f n).hom
      (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b))) =
      ((leftTensorMap f m).f n).hom
        ((α.right.f n).hom (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b)))
    rw [ordinaryTotalMap_inclusion]
    by_cases hp : p = 0
    · subst p
      simp only [Nat.zero_add] at h
      cases h
      rw [β.right_zero, α.right_zero]
      change tmul R (P'.ε ((l.f 0).hom a)) ((m.f n).hom b) =
        tmul R (f (P.ε a)) ((m.f n).hom b)
      exact congrArg (fun z => tmul R z ((m.f n).hom b)) (LinearMap.congr_fun hl a)
    · have ha := LinearMap.congr_fun (α.right_positive p q n h hp) (tmul R a b)
      have hb := LinearMap.congr_fun (β.right_positive p q n h hp)
        (tmul R ((l.f p).hom a) ((m.f q).hom b))
      change (α.right.f n).hom (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b)) = 0 at ha
      change (β.right.f n).hom (ordinaryInclusion P'.complex Q'.complex p q n h
        (tmul R ((l.f p).hom a) ((m.f q).hom b))) = 0 at hb
      rw [ha, hb, map_zero]

section AugmentedTensorAssembly
open CategoryTheory.Limits
open P103.Specs.Ch10.AugmentedAssembly
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Embeds an augmented ordinary complex with its target in degree minus one. -/
def augmentedChainEmbedding : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) where
  f n := (n : ℤ) - 1
  injective_f := by
    intro a b h
    change (a : ℤ) - 1 = (b : ℤ) - 1 at h
    exact_mod_cast (show (a : ℤ) = (b : ℤ) by omega)
  rel {i j} h := by
    change j + 1 = i at h
    change (j : ℤ) - 1 + 1 = (i : ℤ) - 1
    have hh : (j : ℤ) + 1 = (i : ℤ) := by exact_mod_cast h
    omega

variable (K : ChainBicomplex.{u,v} R) (L : ChainComplex (ModuleCat.{v} R) ℤ)
  (ε : K.X 0 ⟶ L) (hε : K.d 1 0 ≫ ε = 0)

abbrev augmentedColumnsNat : ChainComplex (ChainComplex (ModuleCat.{v} R) ℤ) ℕ :=
  ChainComplex.augment (K.restriction nonnegativeChainEmbedding) ε hε

abbrev augmentedColumns : ChainBicomplex.{u,v} R :=
  (augmentedColumnsNat K L ε hε).extend augmentedChainEmbedding

/-- Coordinate isomorphisms of retained columns. -/
def augmentedColumns_retained (p : ℕ) :
    (augmentedColumns K L ε hε).X (p : ℤ) ≅ K.X (p : ℤ) :=
  (augmentedColumnsNat K L ε hε).extendXIso augmentedChainEmbedding
    (i := p + 1) (by change ((p + 1 : ℕ) : ℤ) - 1 = (p : ℤ); push_cast; omega)

/-- The adjoined augmentation column. -/
def augmentedColumns_target : (augmentedColumns K L ε hε).X (-1) ≅ L :=
  (augmentedColumnsNat K L ε hε).extendXIso augmentedChainEmbedding (i := 0) rfl

@[reassoc] theorem augmentedColumns_retained_d (p p' : ℕ) :
    (augmentedColumns K L ε hε).d p p' ≫ (augmentedColumns_retained K L ε hε p').hom =
      (augmentedColumns_retained K L ε hε p).hom ≫ K.d p p' := by
  rw [(augmentedColumnsNat K L ε hε).extend_d_eq augmentedChainEmbedding
    (i := p + 1) (j := p' + 1) (i' := (p : ℤ)) (j' := (p' : ℤ)) (by change ((p + 1 : ℕ) : ℤ) - 1 = (p : ℤ); push_cast; omega)
    (by change ((p' + 1 : ℕ) : ℤ) - 1 = (p' : ℤ); push_cast; omega)]
  dsimp only [augmentedColumns_retained]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  congr 1
  exact ChainComplex.augment_d_succ_succ _ _ _ p p'

@[reassoc] theorem augmentedColumns_augmentation :
    (augmentedColumns K L ε hε).d 0 (-1) ≫ (augmentedColumns_target K L ε hε).hom =
      (augmentedColumns_retained K L ε hε 0).hom ≫ ε := by
  rw [(augmentedColumnsNat K L ε hε).extend_d_eq augmentedChainEmbedding
    (i := 1) (j := 0) (i' := (0 : ℤ)) (j' := (-1 : ℤ)) rfl rfl]
  dsimp only [augmentedColumns_target, augmentedColumns_retained]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Retained-column coordinates for any nonnegative integer degree. -/
def augmentedColumns_retainedZ (p : ℤ) (hp : 0 ≤ p) :
    (augmentedColumns K L ε hε).X p ≅ K.X p :=
  match p, hp with
  | .ofNat n, _ => augmentedColumns_retained K L ε hε n
  | .negSucc n, hn => False.elim (by omega)

/-- Deleting the adjoined target restores the original supported bicomplex. -/
def augmentedColumns_unaugmentedIso
    (hK : ∀ p, p < 0 → IsZero (K.X p)) :
    unaugmented (augmentedColumns K L ε hε) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => if hp : 0 ≤ p then
      retainedColumnIso (augmentedColumns K L ε hε) p hp ≪≫
        augmentedColumns_retainedZ K L ε hε p hp
      else
        IsZero.iso
          ((augmentedColumns K L ε hε).isZero_stupidTrunc_X
            (nonnegativeEmbedding (ComplexShape.down ℤ)) p (by
              intro i hi
              change i.val = p at hi
              have := i.property
              omega))
          (hK p (by omega))) (by
      intro p p' hpp'
      by_cases hp : 0 ≤ p
      · by_cases hp' : 0 ≤ p'
        · simp only [dif_pos hp, dif_pos hp', Iso.trans_hom, Category.assoc]
          obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
          obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le hp'
          change (retainedColumnIso (augmentedColumns K L ε hε) (n : ℤ) hp).hom ≫
              (augmentedColumns_retained K L ε hε n).hom ≫ K.d n n' =
            (unaugmented (augmentedColumns K L ε hε)).d n n' ≫
              (retainedColumnIso (augmentedColumns K L ε hε) (n' : ℤ) hp').hom ≫
                (augmentedColumns_retained K L ε hε n').hom
          have hd := P103.Ch10.AugmentedAssembly.retained_d_to
            (augmentedColumns K L ε hε) (n : ℤ) (n' : ℤ) hp hp'
          simp only [columnToAugmented, dif_pos hp, dif_pos hp'] at hd
          rw [← augmentedColumns_retained_d]
          rw [← Category.assoc, ← hd, Category.assoc]
        · exact (hK p' (by omega)).eq_of_tgt _ _
      · exact ((augmentedColumns K L ε hε).isZero_stupidTrunc_X
            (nonnegativeEmbedding (ComplexShape.down ℤ)) p (by
              intro i hi
              change i.val = p at hi
              have := i.property
              omega)).eq_of_src _ _)

/-- A vanishing column is a zero object in the category of complexes. -/
theorem column_isZero_of_supported (hK : SupportedQuadrant K 0 0)
    (p : ℤ) (hp : p < 0) : IsZero (K.X p) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.Hom.ext
  funext q
  haveI := hK p q (Or.inl hp)
  apply ModuleCat.hom_ext
  exact Subsingleton.elim _ _

/-- Support of the augmented columns, including the newly adjoined target. -/
theorem augmentedColumns_supported (b : ℤ) (hK : SupportedQuadrant K 0 b)
    (hL : SupportedIn L (Set.Ici b)) :
    SupportedQuadrant (augmentedColumns K L ε hε) (-1) b := by
  intro p q hpq
  by_cases hp : p < -1
  · have hz := (augmentedColumnsNat K L ε hε).isZero_extend_X
      augmentedChainEmbedding p (by
        intro i hi
        change (i : ℤ) - 1 = p at hi
        omega)
    exact ModuleCat.isZero_iff_subsingleton.mp
      ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℤ) q).map_isZero hz)
  · have hq : q < b := hpq.resolve_left hp
    by_cases hp' : p = -1
    · subst p
      apply ModuleCat.isZero_iff_subsingleton.mp
      exact (ModuleCat.isZero_iff_subsingleton.mpr (hL q (by simpa))).of_iso ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℤ) q).mapIso
          (augmentedColumns_target K L ε hε))
    · have hp0 : 0 ≤ p := by omega
      apply ModuleCat.isZero_iff_subsingleton.mp
      exact (ModuleCat.isZero_iff_subsingleton.mpr (hK p q (Or.inr hq))).of_iso
        ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℤ) q).mapIso
          (augmentedColumns_retainedZ K L ε hε p hp0))

variable (hK0 : ∀ p, p < 0 → IsZero (K.X p))

/-- Transport of the augmented assembly map to the original supported total. -/
def totalAugmentation
    (f : total (unaugmented (augmentedColumns K L ε hε)) ⟶
      (augmentedColumns K L ε hε).X (-1)) : total K ⟶ L :=
  (HomologicalComplex₂.total.mapIso
    (augmentedColumns_unaugmentedIso K L ε hε hK0) (ComplexShape.down ℤ)).inv ≫
      f ≫ (augmentedColumns_target K L ε hε).hom

@[reassoc] theorem totalAugmentation_zero
    (f : total (unaugmented (augmentedColumns K L ε hε)) ⟶
      (augmentedColumns K L ε hε).X (-1))
    (hf : ∀ n, f.f n = chainAugmentationComponent (augmentedColumns K L ε hε) n)
    (n : ℤ) :
    totalInclusion K 0 n n (by omega) ≫ (totalAugmentation K L ε hε hK0 f).f n = ε.f n := by
  let U := unaugmented (augmentedColumns K L ε hε)
  let e := augmentedColumns_unaugmentedIso K L ε hε hK0
  change totalInclusion K 0 n n _ ≫
    (HomologicalComplex₂.total.map e.inv (ComplexShape.down ℤ)).f n ≫
      f.f n ≫ (augmentedColumns_target K L ε hε).hom.f n = _
  erw [HomologicalComplex₂.ιTotal_map_assoc, hf]
  dsimp only [chainAugmentationComponent]
  simp only [Category.assoc]
  erw [← Category.assoc (totalInclusion U 0 n n _),
    P103.Ch10.TotalComplexAssembly.totalInclusion_projection_self]
  simp only [Category.id_comp]
  have hz : e.inv.f 0 ≫ columnToAugmented (augmentedColumns K L ε hε) 0 ≫
      (augmentedColumns K L ε hε).d 0 (-1) ≫ (augmentedColumns_target K L ε hε).hom = ε := by
    change (augmentedColumns_retainedZ K L ε hε 0 (by omega)).inv ≫
      (retainedColumnIso (augmentedColumns K L ε hε) 0 (by omega)).inv ≫
      columnToAugmented (augmentedColumns K L ε hε) 0 ≫
      (augmentedColumns K L ε hε).d 0 (-1) ≫ (augmentedColumns_target K L ε hε).hom = ε
    simp only [columnToAugmented, dif_pos (show (0 : ℤ) ≤ 0 by omega),
      Iso.inv_hom_id_assoc]
    rw [augmentedColumns_augmentation]
    exact (augmentedColumns_retained K L ε hε 0).inv_hom_id_assoc ε
  exact congrArg (fun g => g.f n) hz

@[reassoc] theorem totalAugmentation_positive
    (f : total (unaugmented (augmentedColumns K L ε hε)) ⟶
      (augmentedColumns K L ε hε).X (-1))
    (hf : ∀ n, f.f n = chainAugmentationComponent (augmentedColumns K L ε hε) n)
    (p q n : ℤ) (h : p + q = n) (hp : p ≠ 0) :
    totalInclusion K p q n h ≫ (totalAugmentation K L ε hε hK0 f).f n = 0 := by
  let U := unaugmented (augmentedColumns K L ε hε)
  let e := augmentedColumns_unaugmentedIso K L ε hε hK0
  change totalInclusion K p q n h ≫
    (HomologicalComplex₂.total.map e.inv (ComplexShape.down ℤ)).f n ≫
      f.f n ≫ (augmentedColumns_target K L ε hε).hom.f n = _
  erw [HomologicalComplex₂.ιTotal_map_assoc, hf]
  dsimp only [chainAugmentationComponent]
  simp only [Category.assoc]
  erw [← Category.assoc (totalInclusion U p q n h),
    P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne U p q 0 n n h (by omega)
      (Or.inl hp)]
  simp

/-- Augmented row assembly in the original unaugmented total coordinates. -/
theorem totalAugmentation_quasi (hK0 : ∀ p, p < 0 → IsZero (K.X p)) (b : ℤ)
    (hK : SupportedQuadrant K 0 b) (hL : SupportedIn L (Set.Ici b))
    (hr : RowsAcyclic (augmentedColumns K L ε hε)) :
    ∃ g : total K ⟶ L, QuasiIsomorphism g ∧
      (∀ n, totalInclusion K 0 n n (by omega) ≫ g.f n = ε.f n) ∧
      (∀ (p q n : ℤ) (h : p + q = n), p ≠ 0 →
        totalInclusion K p q n h ≫ g.f n = 0) := by
  obtain ⟨f, hf⟩ := P103.Ch10.AugmentedAssembly.chain_rows_quasiIsomorphism
    (augmentedColumns K L ε hε) b (augmentedColumns_supported K L ε hε b hK hL) hr
  refine ⟨totalAugmentation K L ε hε hK0 f, ?_,
    totalAugmentation_zero K L ε hε hK0 f hf.1,
    totalAugmentation_positive K L ε hε hK0 f hf.1⟩
  exact P103.Ch10.AugmentedAssembly.quasiIsomorphism_comp
    (P103.Ch10.AugmentedAssembly.quasiIsomorphism_of_iso
      (HomologicalComplex₂.total.mapIso
        (augmentedColumns_unaugmentedIso K L ε hε hK0) (ComplexShape.down ℤ)).symm)
    (P103.Ch10.AugmentedAssembly.quasiIsomorphism_comp hf.2.1
      (P103.Ch10.AugmentedAssembly.quasiIsomorphism_of_iso
        (augmentedColumns_target K L ε hε)))

variable {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]

/-- Horizontal tensor augmentation after extension of the ordinary resolution. -/
def tensorColumnAugmentation (P : P103.Specs.Ch10.Comparison.LeftResolution Rᵐᵒᵖ A)
    (D : ChainComplex (ModuleCat.{max u w} R) ℤ) :
    (tensorBicomplex (extendNonnegativeChain P.complex) D).X 0 ⟶ leftTensorComplex A D where
  f q := ModuleCat.ofHom (tensorMap
    (P.ε.comp (P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom)
    LinearMap.id)
  comm' q q' _ := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl

/-- The ordinary augmentation annihilates the extended differential. -/
theorem tensorColumnAugmentation_square
    (P : P103.Specs.Ch10.Comparison.LeftResolution Rᵐᵒᵖ A)
    (D : ChainComplex (ModuleCat.{max u w} R) ℤ) :
    (tensorBicomplex (extendNonnegativeChain P.complex) D).d 1 0 ≫
      tensorColumnAugmentation P D = 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  change tmul R (P.ε ((P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
    (((extendNonnegativeChain P.complex).d 1 0).hom a))) b = 0
  have hd : (extendNonnegativeChain P.complex).d 1 0 ≫
      (P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom =
      (P.complex.extendXIso nonnegativeChainEmbedding (i := 1) rfl).hom ≫ P.complex.d 1 0 := by
    erw [P.complex.extend_d_eq nonnegativeChainEmbedding
      (i := 1) (j := 0) (i' := (1 : ℤ)) (j' := (0 : ℤ)) rfl rfl]
    simp
  have ha := congrArg (fun k => k.hom a) hd
  change (P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
      (((extendNonnegativeChain P.complex).d 1 0).hom a) =
    (P.complex.d 1 0).hom
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := 1) rfl).hom.hom a) at ha
  rw [ha]
  have he : P.ε ((P.complex.d 1 0).hom
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := 1) rfl).hom.hom a)) = 0 := by
    apply (show (P.complex.d 1 0).hom
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := 1) rfl).hom.hom a) ∈
      LinearMap.ker P.ε from ?_)
    rw [← P.exact_zero]
    exact ⟨_, rfl⟩
  rw [he]
  simp [tmul]

/-- The same assembly statement for a vertically augmented bicomplex.
The signed interchange has sign one on the augmentation edge. -/
theorem totalRowAugmentation_quasi
    (K : ChainBicomplex.{u,v} R) (L : ChainComplex (ModuleCat.{v} R) ℤ)
    (ε : K.flip.X 0 ⟶ L) (hε : K.flip.d 1 0 ≫ ε = 0)
    (hK0 : ∀ p, p < 0 → IsZero (K.flip.X p)) (a : ℤ)
    (hK : SupportedQuadrant K.flip 0 a) (hL : SupportedIn L (Set.Ici a))
    (hr : RowsAcyclic (augmentedColumns K.flip L ε hε)) :
    ∃ g : total K ⟶ L, QuasiIsomorphism g ∧
      (∀ n, totalInclusion K n 0 n (by omega) ≫ g.f n = ε.f n) ∧
      (∀ (p q n : ℤ) (h : p + q = n), q ≠ 0 →
        totalInclusion K p q n h ≫ g.f n = 0) := by
  obtain ⟨g, hg, hz, hp⟩ := totalAugmentation_quasi K.flip L ε hε hK0 a hK hL hr
  refine ⟨(signedInterchange K).inv ≫ g,
    P103.Ch10.AugmentedAssembly.quasiIsomorphism_comp
      (P103.Ch10.AugmentedAssembly.quasiIsomorphism_of_iso (signedInterchange K).symm) hg,
    ?_, ?_⟩
  · intro n
    change totalInclusion K n 0 n _ ≫ (signedInterchange K).inv.f n ≫ g.f n = ε.f n
    have hi := HomologicalComplex₂.ιTotal_totalFlipIso_f_inv K (ComplexShape.down ℤ) n 0 n (by change n + 0 = n; omega)
    change totalInclusion K n 0 n _ ≫ (signedInterchange K).inv.f n =
      (n * 0).negOnePow • totalInclusion K.flip 0 n n (by omega) at hi
    simp only [mul_zero, Int.negOnePow_zero, one_smul] at hi
    rw [← Category.assoc, hi]
    exact hz n
  · intro p q n h hq
    change totalInclusion K p q n h ≫ (signedInterchange K).inv.f n ≫ g.f n = 0
    have hi := HomologicalComplex₂.ιTotal_totalFlipIso_f_inv K (ComplexShape.down ℤ) p q n h
    change totalInclusion K p q n h ≫ (signedInterchange K).inv.f n =
      (p * q).negOnePow • totalInclusion K.flip q p n (by omega) at hi
    rw [← Category.assoc, hi, Linear.units_smul_comp, hp q p n (by omega) hq, smul_zero]

def extendRowXIso {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ChainComplex (ModuleCat.{v} R) ℤ) c) (q : ℤ) :
    ∀ a, (HomologicalComplex.extend.X C a).X q ≅
      HomologicalComplex.extend.X ((HomologicalComplex₂.flip C).X q) a
  | none => CategoryTheory.Limits.IsZero.iso
      ((HomologicalComplex.eval _ _ q).map_isZero (CategoryTheory.Limits.isZero_zero _))
      (CategoryTheory.Limits.isZero_zero _)
  | some _ => Iso.refl _

/-- Taking a row commutes with extension by zero in the horizontal index. -/
def extendRowIso {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (C : HomologicalComplex (ChainComplex (ModuleCat.{v} R) ℤ) c)
    (e : c.Embedding c') (q : ℤ) :
    (HomologicalComplex₂.flip (C.extend e)).X q ≅ ((HomologicalComplex₂.flip C).X q).extend e := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p => extendRowXIso C q (e.r p)) ?_
  intro i j _
  change (extendRowXIso C q (e.r i)).hom ≫
        HomologicalComplex.extend.d ((HomologicalComplex₂.flip C).X q) (e.r i) (e.r j) =
      (HomologicalComplex.extend.d C (e.r i) (e.r j)).f q ≫
        (extendRowXIso C q (e.r j)).hom
  cases e.r i <;> cases e.r j <;>
    simp [extendRowXIso, HomologicalComplex.extend.d]

def augmentRowXIso
    (C : ChainComplex (ChainComplex (ModuleCat.{v} R) ℤ) ℕ)
    (L : ChainComplex (ModuleCat.{v} R) ℤ) (ε : C.X 0 ⟶ L)
    (w : C.d 1 0 ≫ ε = 0) (q : ℤ) :
    ∀ n, ((C.augment ε w).X n).X q ≅
      (ChainComplex.augment ((HomologicalComplex₂.flip C).X q) (ε.f q) (by exact congrArg (fun f => f.f q) w)).X n
  | 0 => Iso.refl _
  | _ + 1 => Iso.refl _

/-- Taking a row commutes with adjoining an augmentation column. -/
def augmentRowIso
    (C : ChainComplex (ChainComplex (ModuleCat.{v} R) ℤ) ℕ)
    (L : ChainComplex (ModuleCat.{v} R) ℤ) (ε : C.X 0 ⟶ L)
    (w : C.d 1 0 ≫ ε = 0) (q : ℤ) :
    (HomologicalComplex₂.flip (C.augment ε w)).X q ≅
      ChainComplex.augment ((HomologicalComplex₂.flip C).X q) (ε.f q) (by exact congrArg (fun f => f.f q) w) := by
  refine HomologicalComplex.Hom.isoOfComponents (augmentRowXIso C L ε w q) ?_
  intro i j _
  rcases i with _ | _ | i <;> rcases j with _ | j <;>
    dsimp only [augmentRowXIso, ChainComplex.augment, HomologicalComplex₂.flip, Iso.refl]
  all_goals simp only [Category.id_comp, Category.comp_id, HomologicalComplex.zero_f]
/-- Exactness of an ordinary augmented complex, including its endpoint. -/
theorem augmented_exactAt
    (C : ChainComplex (ModuleCat.{v} R) ℕ) (M : ModuleCat.{v} R)
    (ε : C.X 0 ⟶ M) (w : C.d 1 0 ≫ ε = 0)
    (hε : Function.Surjective ε)
    (hzero : Function.Exact (C.d 1 0).hom ε.hom)
    (hpos : ∀ n : ℕ, Function.Exact (C.d (n + 2) (n + 1)).hom
      (C.d (n + 1) n).hom) :
    ∀ n, (C.augment ε w).ExactAt n := by
  intro n
  rcases n with _ | _ | n
  · rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x _
    exact hε x
  · rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact hzero
  · rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1) (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    simpa using hpos n

/-- The explicit quotient homology vanishes exactly when the underlying
short complex is exact. -/
theorem acyclic_iff_exactAt {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) :
    Acyclic C ↔ ∀ n, C.ExactAt n := by
  change P103.Ch10.Complexes.Acyclic C ↔ _
  rw [P103.Ch10.Complexes.acyclic_iff]
  apply forall_congr'
  intro n
  rw [HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  rfl

/-- Componentwise exact augmentation and positive exactness imply row
acyclicity after adjoining the endpoint and extending by zero. -/
theorem augmentedColumns_rows_acyclic
    (hsurj : ∀ q, Function.Surjective (ε.f q).hom)
    (hzero : ∀ q, Function.Exact ((K.d 1 0).f q).hom (ε.f q).hom)
    (hpos : ∀ (n : ℕ) q,
      Function.Exact ((K.d (n + 2) (n + 1)).f q).hom ((K.d (n + 1) n).f q).hom) :
    RowsAcyclic (augmentedColumns K L ε hε) := by
  intro q
  let C := K.restriction nonnegativeChainEmbedding
  let e := augmentedChainEmbedding
  let row := ChainComplex.augment ((HomologicalComplex₂.flip C).X q) (ε.f q)
    (by exact congrArg (fun f => f.f q) hε)
  have hr : ∀ n, row.ExactAt n := by
    apply augmented_exactAt
    · exact hsurj q
    · exact hzero q
    · intro n
      exact hpos n q
  have he : ∀ p, (row.extend e).ExactAt p := by
    intro p
    by_cases hp : ∃ n, e.f n = p
    · obtain ⟨n, hn⟩ := hp
      exact (HomologicalComplex.extend_exactAt_iff row e hn).2 (hr n)
    · apply HomologicalComplex.extend_exactAt
      simpa only [not_exists] using hp
  let ei := extendRowIso (ChainComplex.augment C ε hε) e q ≪≫
    (e.extendFunctor (ModuleCat R)).mapIso (augmentRowIso C L ε hε q)
  apply (acyclic_iff_exactAt _).2
  intro p
  exact (he p).of_iso ei.symm

theorem exact_linearEquiv_transport
    {S : Type*} [Ring S]
    {X Y Z X' Y' Z' : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [Module S X] [Module S Y] [Module S Z]
    [Module S X'] [Module S Y'] [Module S Z']
    (f : X →ₗ[S] Y) (g : Y →ₗ[S] Z)
    (f' : X' →ₗ[S] Y') (g' : Y' →ₗ[S] Z')
    (eX : X' ≃ₗ[S] X) (eY : Y' ≃ₗ[S] Y) (eZ : Z' ≃ₗ[S] Z)
    (hf : ∀ x, eY (f' x) = f (eX x))
    (hg : ∀ y, eZ (g' y) = g (eY y))
    (he : Function.Exact f g) : Function.Exact f' g' := by
  intro y
  constructor
  · intro hy
    have hgy : g (eY y) = 0 := by rw [← hg, hy, map_zero]
    obtain ⟨x, hx⟩ := (he (eY y)).1 hgy
    refine ⟨eX.symm x, eY.injective ?_⟩
    rw [hf, eX.apply_symm_apply, hx]
  · rintro ⟨x, rfl⟩
    apply eZ.injective
    rw [hg, hf, he.apply_apply_eq_zero, map_zero]

theorem extendNonnegativeChain_d_coordinate
    {S : Type*} [Ring S] (C : ChainComplex (ModuleCat.{v} S) ℕ)
    (i j : ℕ) (a : (extendNonnegativeChain C).X (i : ℤ)) :
    (C.extendXIso nonnegativeChainEmbedding (i := j) rfl).hom.hom
        (((extendNonnegativeChain C).d i j).hom a) =
      (C.d i j).hom ((C.extendXIso nonnegativeChainEmbedding (i := i) rfl).hom.hom a) := by
  have hd : (extendNonnegativeChain C).d (i : ℤ) (j : ℤ) ≫
      (C.extendXIso nonnegativeChainEmbedding (i := j) rfl).hom =
      (C.extendXIso nonnegativeChainEmbedding (i := i) rfl).hom ≫ C.d i j := by
    change (C.extend nonnegativeChainEmbedding).d (i : ℤ) (j : ℤ) ≫
      (C.extendXIso nonnegativeChainEmbedding (i := j) rfl).hom =
      (C.extendXIso nonnegativeChainEmbedding (i := i) rfl).hom ≫ C.d i j
    rw [C.extend_d_eq nonnegativeChainEmbedding (i := i) (j := j)
      (i' := (i : ℤ)) (j' := (j : ℤ)) rfl rfl]
    simp
  exact congrArg (fun k => k.hom a) hd

theorem resolution_extended_exact_zero
    {S : Type u} [Ring S] {A : Type v} [AddCommGroup A] [Module S A]
    (P : P103.Specs.Ch10.Comparison.LeftResolution S A) :
    Function.Exact ((extendNonnegativeChain P.complex).d 1 0).hom
      (P.ε.comp (P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom) := by
  apply exact_linearEquiv_transport (P.complex.d 1 0).hom P.ε
    _ _ (P.complex.extendXIso nonnegativeChainEmbedding (i := 1) rfl).toLinearEquiv
    (P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).toLinearEquiv
    (LinearEquiv.refl S A)
  · exact extendNonnegativeChain_d_coordinate P.complex 1 0
  · intro a
    rfl
  · exact LinearMap.exact_iff.mpr P.exact_zero.symm

theorem resolution_extended_exact_succ
    {S : Type u} [Ring S] {A : Type v} [AddCommGroup A] [Module S A]
    (P : P103.Specs.Ch10.Comparison.LeftResolution S A) (n : ℕ) :
    Function.Exact ((extendNonnegativeChain P.complex).d (n + 2) (n + 1)).hom
      ((extendNonnegativeChain P.complex).d (n + 1) n).hom := by
  apply exact_linearEquiv_transport (P.complex.d (n + 2) (n + 1)).hom
    (P.complex.d (n + 1) n).hom _ _
    (P.complex.extendXIso nonnegativeChainEmbedding (i := n + 2) rfl).toLinearEquiv
    (P.complex.extendXIso nonnegativeChainEmbedding (i := n + 1) rfl).toLinearEquiv
    (P.complex.extendXIso nonnegativeChainEmbedding (i := n) rfl).toLinearEquiv
  · convert extendNonnegativeChain_d_coordinate P.complex (n + 2) (n + 1) using 1 <;>
      push_cast <;> rfl
  · convert extendNonnegativeChain_d_coordinate P.complex (n + 1) n using 1 <;>
      push_cast <;> rfl
  · exact LinearMap.exact_iff.mpr (P.exact_succ n).symm

theorem resolution_extended_projective
    {S : Type u} [Ring S] {A : Type v} [AddCommGroup A] [Module S A]
    (P : P103.Specs.Ch10.Comparison.LeftResolution S A) (hP : P.IsProjective) (q : ℤ) :
    Module.Projective S ((extendNonnegativeChain P.complex).X q) := by
  rcases q with n | n
  · letI := hP n
    exact Module.Projective.of_equiv
      (P.complex.extendXIso nonnegativeChainEmbedding (i := n) rfl).toLinearEquiv.symm
  · haveI := P103.Ch10.Complexes.extendNonnegativeChain_supported P.complex
      (Int.negSucc n) (by simp)
    infer_instance

/-- Projective terms on the left-resolution side make all horizontally
augmented tensor rows acyclic over the original, possibly noncommutative ring. -/
theorem tensorColumnAugmentation_rows_acyclic
    {B : Type w} [AddCommGroup B] [Module R B]
    (P : P103.Specs.Ch10.Comparison.LeftResolution Rᵐᵒᵖ A)
    (Q : P103.Specs.Ch10.Comparison.LeftResolution R B) (hQ : Q.IsProjective) :
    RowsAcyclic (augmentedColumns
      (tensorBicomplex (extendNonnegativeChain P.complex) (extendNonnegativeChain Q.complex))
      (leftTensorComplex A (extendNonnegativeChain Q.complex))
      (tensorColumnAugmentation P (extendNonnegativeChain Q.complex))
      (tensorColumnAugmentation_square P (extendNonnegativeChain Q.complex))) := by
  apply augmentedColumns_rows_acyclic
  · intro q
    let p := P.ε.comp
      (P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
    have hp : Function.Surjective p :=
      P.surjective.comp (P.complex.extendXIso nonnegativeChainEmbedding
        (i := 0) rfl).toLinearEquiv.surjective
    exact (P103.HomTensorExactness.tensor_first_rightExact
      ((extendNonnegativeChain P.complex).d 1 0).hom p
      (resolution_extended_exact_zero P) hp
      (tensorMap _ (LinearMap.id : (extendNonnegativeChain Q.complex).X q →ₗ[R] _)).toAddMonoidHom
      (by intros; rfl)
      (tensorMap _ (LinearMap.id : (extendNonnegativeChain Q.complex).X q →ₗ[R] _)).toAddMonoidHom
      (by intros; rfl)).2
  · intro q
    exact projective_tensor_exact (resolution_extended_projective Q hQ q)
      _ _ (resolution_extended_exact_zero P)
  · intro n q
    exact projective_tensor_exact (resolution_extended_projective Q hQ q)
      _ _ (resolution_extended_exact_succ P n)

/-- Projective right-module terms make the vertically augmented tensor
columns acyclic, with no commutativity assumption on the ring. -/
theorem tensorRowAugmentation_rows_acyclic
    {B : Type w} [AddCommGroup B] [Module R B]
    (P : P103.Specs.Ch10.Comparison.LeftResolution Rᵐᵒᵖ A)
    (Q : P103.Specs.Ch10.Comparison.LeftResolution R B) (hP : P.IsProjective) :
    RowsAcyclic (augmentedColumns
      (tensorBicomplex (extendNonnegativeChain P.complex) (extendNonnegativeChain Q.complex)).flip
      (((tensorFunctor B).mapHomologicalComplex (ComplexShape.down ℤ)).obj
        (extendNonnegativeChain P.complex))
      (tensorRowAugmentation Q (extendNonnegativeChain P.complex))
      (tensorRowAugmentation_square Q (extendNonnegativeChain P.complex))) := by
  apply augmentedColumns_rows_acyclic
  · intro p
    let q := Q.ε.comp
      (Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
    have hq : Function.Surjective q :=
      Q.surjective.comp (Q.complex.extendXIso nonnegativeChainEmbedding
        (i := 0) rfl).toLinearEquiv.surjective
    exact P103.HomTensorExactness.tensorSecond_surjective q hq
      (tensorMap (LinearMap.id : (extendNonnegativeChain P.complex).X p →ₗ[Rᵐᵒᵖ] _) q).toAddMonoidHom
      (by intros; rfl)
  · intro p
    exact right_projective_tensor_exact (resolution_extended_projective P hP p)
      _ _ (resolution_extended_exact_zero Q)
  · intro n p
    exact right_projective_tensor_exact (resolution_extended_projective P hP p)
      _ _ (resolution_extended_exact_succ Q n)

set_option maxHeartbeats 2000000 in
/-- Augmentation balance assembled from the two exact augmented tensor directions. -/
theorem balance_of_tensor_rows
    {A : Type v} {B : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup B] [Module R B]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B)
    (hrow : RowsAcyclic (augmentedColumns
      (tensorBicomplex (extendNonnegativeChain P.complex) (extendNonnegativeChain Q.complex))
      (leftTensorComplex A (extendNonnegativeChain Q.complex))
      (tensorColumnAugmentation P (extendNonnegativeChain Q.complex))
      (tensorColumnAugmentation_square P (extendNonnegativeChain Q.complex))))
    (hcol : RowsAcyclic (augmentedColumns
      (tensorBicomplex (extendNonnegativeChain P.complex) (extendNonnegativeChain Q.complex)).flip
      (((tensorFunctor B).mapHomologicalComplex (ComplexShape.down ℤ)).obj (extendNonnegativeChain P.complex))
      (tensorRowAugmentation Q (extendNonnegativeChain P.complex))
      (tensorRowAugmentation_square Q (extendNonnegativeChain P.complex)))) :
    ∃ α : Augmentations P Q, QuasiIsomorphism α.left ∧ QuasiIsomorphism α.right := by
  let K := tensorBicomplex (extendNonnegativeChain P.complex) (extendNonnegativeChain Q.complex)
  let L := leftTensorComplex A (extendNonnegativeChain Q.complex)
  let M := ((tensorFunctor B).mapHomologicalComplex (ComplexShape.down ℤ)).obj
    (extendNonnegativeChain P.complex)
  have hK : SupportedQuadrant K 0 0 := ordinary_tensor_supported P.complex Q.complex
  have hKflip : SupportedQuadrant K.flip 0 0 := by
    intro p q h
    exact hK q p (h.elim Or.inr Or.inl)
  have hL : SupportedIn L (Set.Ici 0) := by
    intro n hn
    apply ModuleCat.isZero_iff_subsingleton.mp
    exact (leftTensorFunctor A).map_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr
        (P103.Ch10.Complexes.extendNonnegativeChain_supported Q.complex n hn))
  have hM : SupportedIn M (Set.Ici 0) := by
    intro n hn
    apply ModuleCat.isZero_iff_subsingleton.mp
    exact (tensorFunctor B).map_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr
        (P103.Ch10.Complexes.extendNonnegativeChain_supported P.complex n hn))
  have hT : SupportedIn (total K) (Set.Ici 0) := by
    intro n hn
    exact P103.Ch10.TotalComplexAssembly.total_supportedBelow K 0 0 hK n (by simpa using hn)
  obtain ⟨r, hr, hr0, hrp⟩ := totalAugmentation_quasi K L
    (tensorColumnAugmentation P (extendNonnegativeChain Q.complex))
    (tensorColumnAugmentation_square P (extendNonnegativeChain Q.complex))
    (column_isZero_of_supported K hK) 0 hK hL hrow
  obtain ⟨l, hl, hl0, hlp⟩ := totalRowAugmentation_quasi K M
    (tensorRowAugmentation Q (extendNonnegativeChain P.complex))
    (tensorRowAugmentation_square Q (extendNonnegativeChain P.complex))
    (column_isZero_of_supported K.flip hKflip) 0 hKflip hM hcol
  let eL := restrictExtendMapIso P.complex (tensorFunctor B)
  let eR := restrictExtendMapIso Q.complex (leftTensorFunctor A)
  let αL : ordinaryTotal P.complex Q.complex ⟶ tensorComplex P.complex B :=
    HomologicalComplex.restrictionMap l nonnegativeChainEmbedding ≫ eL.hom
  let αR : ordinaryTotal P.complex Q.complex ⟶ leftOrdinaryTensorComplex A Q.complex :=
    HomologicalComplex.restrictionMap r nonnegativeChainEmbedding ≫ eR.hom
  refine ⟨⟨αL, αR, ?_, ?_, ?_, ?_⟩,
    quasiIsomorphism_comp_any (quasiIsomorphism_restriction_nonnegative hT hM l hl)
      (quasiIsomorphism_of_iso_any eL),
    quasiIsomorphism_comp_any (quasiIsomorphism_restriction_nonnegative hT hL r hr)
      (quasiIsomorphism_of_iso_any eR)⟩
  · intro p a b
    rw [ordinaryInclusion_tmul]
    change (eL.hom.f p).hom ((l.f (p : ℤ)).hom
      ((totalInclusion K p 0 p (by omega)).hom (tmul R
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom b)))) = _
    have hx := congrArg (fun k => k.hom (tmul R
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom b))) (hl0 (p : ℤ))
    change (l.f (p : ℤ)).hom
      ((totalInclusion K p 0 p (by omega)).hom (tmul R
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom b))) =
      tmul R ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
        (Q.ε ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
          ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom b))) at hx
    rw [hx]
    change tmul R
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom.hom
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a))
      (Q.ε ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom b))) = _
    have ha := congrArg (fun k => k.hom a)
      (P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv_hom_id
    have hb := congrArg (fun k => k.hom b)
      (Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv_hom_id
    change (P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom.hom
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a) = a at ha
    change (Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom b) = b at hb
    rw [ha, hb]
  · intro p q n h hq
    apply tensor_hom_ext
    intro a b
    change (αL.f n).hom (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b)) = 0
    rw [ordinaryInclusion_tmul]
    have hx := congrArg (fun k => k.hom (tmul R
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)))
      (hlp p q n (by exact_mod_cast h) (by exact_mod_cast hq))
    change (l.f (n : ℤ)).hom
      ((totalInclusion K p q n (by exact_mod_cast h)).hom (tmul R
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b))) = 0 at hx
    change (eL.hom.f n).hom ((l.f (n : ℤ)).hom _) = 0
    erw [hx, map_zero]
  · intro q a b
    rw [ordinaryInclusion_tmul]
    change (eR.hom.f q).hom ((r.f (q : ℤ)).hom
      ((totalInclusion K 0 q q (by omega)).hom (tmul R
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom a)
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)))) = _
    have hx := congrArg (fun k => k.hom (tmul R
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom a)
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b))) (hr0 (q : ℤ))
    change (r.f (q : ℤ)).hom
      ((totalInclusion K 0 q q (by omega)).hom (tmul R
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom a)
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b))) =
      tmul R (P.ε ((P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
          ((P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom a)))
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b) at hx
    rw [hx]
    change tmul R (P.ε ((P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom a)))
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).hom.hom
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)) = _
    have ha := congrArg (fun k => k.hom a)
      (P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv_hom_id
    have hb := congrArg (fun k => k.hom b)
      (Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv_hom_id
    change (P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom a) = a at ha
    change (Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).hom.hom
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b) = b at hb
    rw [ha, hb]
  · intro p q n h hp
    apply tensor_hom_ext
    intro a b
    change (αR.f n).hom (ordinaryInclusion P.complex Q.complex p q n h (tmul R a b)) = 0
    rw [ordinaryInclusion_tmul]
    have hx := congrArg (fun k => k.hom (tmul R
      ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
      ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)))
      (hrp p q n (by exact_mod_cast h) (by exact_mod_cast hp))
    change (r.f (n : ℤ)).hom
      ((totalInclusion K p q n (by exact_mod_cast h)).hom (tmul R
        ((P.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
        ((Q.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b))) = 0 at hx
    change (eR.hom.f n).hom ((r.f (n : ℤ)).hom _) = 0
    erw [hx, map_zero]


theorem balance : balanceType.{u,v,w} := by
  intro R _ A B _ _ _ _ P Q hP hQ
  exact balance_of_tensor_rows P Q
    (tensorColumnAugmentation_rows_acyclic P Q hQ)
    (tensorRowAugmentation_rows_acyclic P Q hP)

end AugmentedTensorAssembly

section BalancedNaturality
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[simp] theorem balanceEquiv_apply_left
    {A : Type v} {B : Type w}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B]
    {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution R B}
    (α : Augmentations P Q) (hL : QuasiIsomorphism α.left)
    (hR : QuasiIsomorphism α.right) (n : ℕ)
    (z : Homology (ordinaryTotal P.complex Q.complex) n) :
    balanceEquiv α hL hR n (homologyMap α.left n z) = homologyMap α.right n z := by
  change (LinearEquiv.ofBijective (homologyMap α.right n) (hR n))
    ((LinearEquiv.ofBijective (homologyMap α.left n) (hL n)).symm
      ((LinearEquiv.ofBijective (homologyMap α.left n) (hL n)) z)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem homologyMap_square {S : Type*} [Ring S] {ι : Type*} {c : ComplexShape ι}
    {C D E F : HomologicalComplex (ModuleCat.{v} S) c}
    (f : C ⟶ D) (b : D ⟶ F) (a : C ⟶ E) (g : E ⟶ F)
    (h : f ≫ b = a ≫ g) (n : ι) :
    (homologyMap b n).comp (homologyMap f n) =
      (homologyMap g n).comp (homologyMap a n) := by
  calc
    _ = homologyMap (f ≫ b) n := (P103.Ch10.Complexes.homologyMap_comp f b n).symm
    _ = homologyMap (a ≫ g) n := congrArg (fun k => homologyMap k n) h
    _ = _ := P103.Ch10.Complexes.homologyMap_comp a g n

theorem balanceEquiv_natural : balanceEquiv_naturalType.{u,v,w} := by
  intro R _ A A' B B' _ _ _ _ _ _ _ _ P P' Q Q' f g l m hl hm α β hαL hαR hβL hβR n
  obtain ⟨hleft, hright⟩ := augmentation_natural R A A' B B' P P' Q Q' f g l m hl hm α β
  have hleft' := homologyMap_square (ordinaryTotalMap l m) β.left α.left
    (tensorFirstMap l B ≫ tensorSecondMap P'.complex g) hleft n
  have hright' := homologyMap_square (ordinaryTotalMap l m) β.right α.right
    (leftTensorMap f m) hright n
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (hαL n).surjective x
  have heL := congrArg (fun k => k.toAddMonoidHom z) hleft'
  have heR := congrArg (fun k => k.toAddMonoidHom z) hright'
  change homologyMap β.left n (homologyMap (ordinaryTotalMap l m) n z) =
    homologyMap (tensorFirstMap l B ≫ tensorSecondMap P'.complex g) n
      (homologyMap α.left n z) at heL
  change homologyMap β.right n (homologyMap (ordinaryTotalMap l m) n z) =
    homologyMap (leftTensorMap f m) n (homologyMap α.right n z) at heR
  change balanceEquiv β hβL hβR n
      (homologyMap (tensorFirstMap l B ≫ tensorSecondMap P'.complex g) n
        (homologyMap α.left n z)) =
    homologyMap (leftTensorMap f m) n
      (balanceEquiv α hαL hαR n (homologyMap α.left n z))
  rw [← heL, balanceEquiv_apply_left, balanceEquiv_apply_left]
  exact heR

end BalancedNaturality

section Commutative
variable {K : Type u} [CommRing K]

@[simp] theorem commTensorFlip_tmul
    (A : Type v) (B : Type w) [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (a : A) (b : B) :
    letI := commRightModule K A
    letI := commRightModule K B
    commTensorFlip A B (tmul K a b) = tmul K b a := rfl

/-- Unsigned tensor flip exchanges rows and columns. The signs appear only
when passing from the flipped total to the total of the flipped factors. -/
def commBicomplexFlip
    (C : ChainComplex (ModuleCat.{v} K) ℤ)
    (D : ChainComplex (ModuleCat.{w} K) ℤ) :
    tensorBicomplex (commRightComplex C) D ≅
      (tensorBicomplex (commRightComplex D) C).flip where
  hom :=
    { f p :=
        { f q := ModuleCat.ofHom (commTensorFlip (C.X p) (D.X q))
          comm' q q' _ := by
            apply ModuleCat.hom_ext
            apply tensor_hom_ext
            intro a b
            rfl }
      comm' p p' _ := by
        apply HomologicalComplex.Hom.ext
        funext q
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro a b
        rfl }
  inv :=
    { f p :=
        { f q := ModuleCat.ofHom (commTensorFlip (D.X q) (C.X p))
          comm' q q' _ := by
            apply ModuleCat.hom_ext
            apply tensor_hom_ext
            intro b a
            rfl }
      comm' p p' _ := by
        apply HomologicalComplex.Hom.ext
        funext q
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro b a
        rfl }
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro b a
    rfl

/-- Koszul's signed flip, for arbitrary integer complexes. -/
def signedFlip
    (C : ChainComplex (ModuleCat.{v} K) ℤ)
    (D : ChainComplex (ModuleCat.{w} K) ℤ) :
    tensorTotal (commRightComplex C) D ≅ tensorTotal (commRightComplex D) C :=
  HomologicalComplex₂.total.mapIso (commBicomplexFlip C D) (ComplexShape.down ℤ) ≪≫
    signedInterchange (tensorBicomplex (commRightComplex D) C)

set_option backward.isDefEq.respectTransparency false in
theorem signedFlip_formula
    (C : ChainComplex (ModuleCat.{v} K) ℤ)
    (D : ChainComplex (ModuleCat.{w} K) ℤ)
    (p q n : ℤ) (h : p + q = n) (a : C.X p) (b : D.X q) :
    (signedFlip C D).hom.f n
        (tensorInclusion (commRightComplex C) D p q n h (tmul K a b)) =
      (p * q).negOnePow •
        tensorInclusion (commRightComplex D) C q p n (by omega) (tmul K b a) := by
  have hmap := HomologicalComplex₂.ιTotal_map _ _ (commBicomplexFlip C D).hom
    (ComplexShape.down ℤ) p q n h
  have hflip := P103.Ch10.TotalComplexAssembly.signedInterchange_chain
    (tensorBicomplex (commRightComplex D) C) q p n h
  have hm := congrArg (fun f => f.hom (tmul K a b)) hmap
  have hs := congrArg (fun f => f.hom (tmul K b a)) hflip
  change ((signedInterchange (tensorBicomplex (commRightComplex D) C)).hom.f n).hom
    (((HomologicalComplex₂.total.map (commBicomplexFlip C D).hom
      (ComplexShape.down ℤ)).f n).hom
        (tensorInclusion (commRightComplex C) D p q n h (tmul K a b))) = _
  change (((HomologicalComplex₂.total.map (commBicomplexFlip C D).hom
      (ComplexShape.down ℤ)).f n).hom
        (tensorInclusion (commRightComplex C) D p q n h (tmul K a b))) =
    ((tensorBicomplex (commRightComplex D) C).flip.ιTotal
      (ComplexShape.down ℤ) p q n h).hom (tmul K b a) at hm
  rw [hm]
  rw [mul_comm q p] at hs
  dsimp only [P103.Ch11.TorBalance.tensorBicomplex,
    P103.Ch10.TotalComplexAssembly.signedInterchange] at hs ⊢
  rcases Int.units_eq_one_or (p * q).negOnePow with hsign | hsign <;>
    simp [hsign, Units.smul_def, tensorInclusion, totalInclusion] at hs ⊢ <;>
    convert hs using 1

theorem signed_flip : signedFlipType.{u,v,w} := by
  intro K _ C D
  exact ⟨signedFlip C D, signedFlip_formula C D⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The signed interchange commutes with maps of both tensor factors. -/
theorem signedFlip_natural
    {C C' : ChainComplex (ModuleCat.{v} K) ℤ}
    {D D' : ChainComplex (ModuleCat.{w} K) ℤ} (f : C ⟶ C') (g : D ⟶ D') :
    tensorTotalMap
        (((commRightFunctor K).mapHomologicalComplex (ComplexShape.down ℤ)).map f) g ≫
        (signedFlip C' D').hom =
      (signedFlip C D).hom ≫ tensorTotalMap
        (((commRightFunctor K).mapHomologicalComplex (ComplexShape.down ℤ)).map g) f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply P103.BalancedTensor.hom_ext
  intro a b
  change ((signedFlip C' D').hom.f n).hom
      (((tensorTotalMap
        (((commRightFunctor K).mapHomologicalComplex (ComplexShape.down ℤ)).map f) g).f n).hom
          (tensorInclusion (commRightComplex C) D p q n h (tmul K a b))) =
    ((tensorTotalMap
      (((commRightFunctor K).mapHomologicalComplex (ComplexShape.down ℤ)).map g) f).f n).hom
        (((signedFlip C D).hom.f n).hom
          (tensorInclusion (commRightComplex C) D p q n h (tmul K a b)))
  rw [tensorTotalMap_inclusion, signedFlip_formula, signedFlip_formula, map_zsmul_unit,
    tensorTotalMap_inclusion]
  rfl


theorem commRight_projective (M : Type v) [AddCommGroup M] [Module K M]
    (hM : Module.Projective K M) :
    letI := commRightModule K M
    Module.Projective Kᵐᵒᵖ M := by
  letI := commRightModule K M
  letI := hM
  let σ := (RingHom.id K).toOpposite (fun _ _ => Commute.all _ _)
  let σ' := (RingHom.id K).fromOpposite (fun _ _ => Commute.all _ _)
  letI : RingHomInvPair σ σ' := ⟨rfl, rfl⟩
  letI : RingHomInvPair σ' σ := ⟨rfl, rfl⟩
  let e : M ≃ₛₗ[σ] M :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact Module.Projective.of_equiv e

theorem commRightResolution_projective {A : Type v} [AddCommGroup A] [Module K A]
    (P : LeftResolution K A) (hP : P.IsProjective) :
    letI := commRightModule K A
    (commRightResolution P).IsProjective := by
  letI := commRightModule K A
  intro n
  exact commRight_projective (K := K) (P.complex.X n) (hP n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem commOrdinaryTensorFlip_natural
    {A A' : Type v} [AddCommGroup A] [Module K A]
    [AddCommGroup A'] [Module K A'] (f : A →ₗ[K] A')
    {D D' : ChainComplex (ModuleCat.{w} K) ℕ} (m : D ⟶ D') :
    letI := commRightModule K A
    letI := commRightModule K A'
    leftTensorMap (commRightLinear f) m ≫ (commOrdinaryTensorFlip A' D').hom =
      (commOrdinaryTensorFlip A D).hom ≫
        tensorFirstMap (commRightOrdinaryMap m) A ≫
        tensorSecondMap (commRightOrdinaryComplex D') f := by
  letI := commRightModule K A
  letI := commRightModule K A'
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl


/-- Augmentations chosen from the balance theorem, for constructing symmetry. -/
def symmetryAugmentation (hb : balanceType.{u,v,w})
    {A : Type v} {B : Type w} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (P : LeftResolution K A) (Q : LeftResolution K B)
    (hP : P.IsProjective) (hQ : Q.IsProjective) :
    letI := commRightModule K A
    Augmentations (commRightResolution P) Q := by
  letI := commRightModule K A
  exact (hb K A B (commRightResolution P) Q (commRightResolution_projective P hP) hQ).choose

theorem symmetryAugmentation_quasi (hb : balanceType.{u,v,w})
    {A : Type v} {B : Type w} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (P : LeftResolution K A) (Q : LeftResolution K B)
    (hP : P.IsProjective) (hQ : Q.IsProjective) :
    letI := commRightModule K A
    QuasiIsomorphism (symmetryAugmentation hb P Q hP hQ).left ∧
      QuasiIsomorphism (symmetryAugmentation hb P Q hP hQ).right := by
  letI := commRightModule K A
  exact (hb K A B (commRightResolution P) Q (commRightResolution_projective P hP) hQ).choose_spec

/-- Balance followed by termwise interchange, on the actual TorWith models. -/
def torSymmetryEquivOfBalance (hb : balanceType.{u,v,w})
    {A : Type v} {B : Type w} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (P : LeftResolution K A) (Q : LeftResolution K B)
    (hP : P.IsProjective) (hQ : Q.IsProjective) (n : ℕ) :
    letI := commRightModule K A
    letI := commRightModule K B
    TorWith (commRightResolution P) B n ≃ₗ[ℤ] TorWith (commRightResolution Q) A n := by
  letI := commRightModule K A
  letI := commRightModule K B
  exact (balanceEquiv (symmetryAugmentation hb P Q hP hQ)
      (symmetryAugmentation_quasi hb P Q hP hQ).1
      (symmetryAugmentation_quasi hb P Q hP hQ).2 n).trans
    (((quotientHomology (ComplexShape.down ℕ) n).mapIso
      (commOrdinaryTensorFlip A Q.complex)).toLinearEquiv)

private theorem symmetry_homologyMap_comp {S : Type*} [Ring S]
    {ι : Type*} {c : ComplexShape ι}
    {C D E : HomologicalComplex (ModuleCat.{v} S) c}
    (f : C ⟶ D) (g : D ⟶ E) (n : ι) :
    homologyMap (f ≫ g) n = (homologyMap g n).comp (homologyMap f n) := by
  apply (cycleBoundaries C n).quot_hom_ext
  intro z
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def torSymmetryOfBalance (hb : balanceType.{u,v,w})
    (hn : balanceEquiv_naturalType.{u,v,w}) : TorSymmetry.{u,v,w} K where
  equivalence A B P Q hP hQ n := torSymmetryEquivOfBalance hb P Q hP hQ n
  augmentation_formula A B P Q hP hQ n := by
    letI := commRightModule K A
    letI := commRightModule K B
    exact ⟨symmetryAugmentation hb P Q hP hQ,
      (symmetryAugmentation_quasi hb P Q hP hQ).1,
      (symmetryAugmentation_quasi hb P Q hP hQ).2, rfl⟩
  naturality A A' B B' P P' Q Q' hP hP' hQ hQ' f g l m hl hm n := by
    letI := commRightModule K A
    letI := commRightModule K A'
    letI := commRightModule K B
    letI := commRightModule K B'
    have hl' : ChainLift (commRightResolution P) (commRightResolution P')
        (commRightLinear f.hom) (commRightOrdinaryMap l) := by
      apply LinearMap.ext
      intro a
      exact LinearMap.congr_fun hl a
    have he := hn K A A' B B' (commRightResolution P) (commRightResolution P') Q Q'
      (commRightLinear f.hom) g.hom (commRightOrdinaryMap l) m hl' hm
      (symmetryAugmentation hb P Q hP hQ) (symmetryAugmentation hb P' Q' hP' hQ')
      (symmetryAugmentation_quasi hb P Q hP hQ).1
      (symmetryAugmentation_quasi hb P Q hP hQ).2
      (symmetryAugmentation_quasi hb P' Q' hP' hQ').1
      (symmetryAugmentation_quasi hb P' Q' hP' hQ').2 n
    have hf := congrArg (fun k => homologyMap k n) (commOrdinaryTensorFlip_natural f.hom m)
    rw [symmetry_homologyMap_comp
      (leftTensorMap (commRightLinear f.hom) m) (commOrdinaryTensorFlip A' Q'.complex).hom n] at hf
    rw [symmetry_homologyMap_comp
      (commOrdinaryTensorFlip A Q.complex).hom
      (tensorFirstMap (commRightOrdinaryMap m) A ≫
        tensorSecondMap (commRightOrdinaryComplex Q'.complex) f.hom) n] at hf
    change (homologyMap (commOrdinaryTensorFlip A' Q'.complex).hom n).comp
        ((balanceEquiv (symmetryAugmentation hb P' Q' hP' hQ')
          (symmetryAugmentation_quasi hb P' Q' hP' hQ').1
          (symmetryAugmentation_quasi hb P' Q' hP' hQ').2 n).toLinearMap.comp _) = _
    rw [he, ← LinearMap.comp_assoc, hf]
    rfl


theorem tor_symmetry : tor_symmetryType.{u,v,w} := by
  intro K _
  exact ⟨torSymmetryOfBalance balance balanceEquiv_natural⟩


/-- Degreewise multiplication by a central scalar. -/
def scalarChainMap (C : ChainComplex (ModuleCat.{v} K) ℕ) (r : K) : C ⟶ C where
  f n := scalarMap (C.X n) r
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (C.d i j).hom.map_smul r x

/-- Moving a scalar between the two factors is precisely balancedness. -/
theorem scalarTensorFirst_eq_second
    (C : ChainComplex (ModuleCat.{v} K) ℕ) (B : ModuleCat.{w} K) (r : K) :
    tensorFirstMap (commRightOrdinaryMap (scalarChainMap C r)) B =
      tensorSecondMap (commRightOrdinaryComplex C) (scalarMap B r).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  exact P103.BalancedTensor.balance r a b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The upstream module action is represented by its coefficient scalar map. -/
theorem torModule_smul_map {n : ℕ} (E : TorMaps.{u,v,w} K n)
    {A : ModuleCat.{v} Kᵐᵒᵖ} (P : ProjectiveChoice Kᵐᵒᵖ A) (B : ModuleCat.{w} K)
    (r : K) (x : TorWith P.val B n) :
    letI := torModule E P B
    r • x = homologyMap (tensorSecondMap P.val.complex (scalarMap B r).hom) n x := by
  change E.map P P (𝟙 _) (scalarMap B r) x = _
  rw [E.formula P P (𝟙 _) (scalarMap B r) (𝟙 _)
    (P103.Ch10.Comparison.chainLift_id P.val)]
  have h : tensorFirstMap (𝟙 P.val.complex) B = 𝟙 _ := by
    exact CategoryTheory.Functor.map_id
      ((tensorFunctor (R := K) B).mapHomologicalComplex (ComplexShape.down ℕ)) _
  rw [h, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem tor_symmetry_linear : tor_symmetry_linearType.{u,v,w} := by
  intro K _ S n E E' A B P Q
  letI := commRightModule K A
  letI := commRightModule K B
  letI := torModule E (commRightProjectiveChoice P) B
  letI := torModule E' (commRightProjectiveChoice Q) A
  intro r x
  have hl : ChainLift P.val P.val (scalarMap A r).hom (scalarChainMap P.val.complex r) := by
    apply LinearMap.ext
    intro a
    exact P.val.ε.map_smul r a
  have he := S.naturality A A B B P.val P.val Q.val Q.val
    P.property P.property Q.property Q.property
    (scalarMap A r) (𝟙 B) (scalarChainMap P.val.complex r) (𝟙 Q.val.complex)
    hl (P103.Ch10.Comparison.chainLift_id Q.val) n
  have hleft : tensorFirstMap (commRightOrdinaryMap (scalarChainMap P.val.complex r)) B ≫
      tensorSecondMap (commRightResolution P.val).complex (𝟙 B : B ⟶ B).hom =
      tensorSecondMap (commRightResolution P.val).complex (scalarMap B r).hom := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    exact P103.BalancedTensor.balance r a b
  have hright : tensorFirstMap (commRightOrdinaryMap (𝟙 Q.val.complex)) A ≫
      tensorSecondMap (commRightResolution Q.val).complex (scalarMap A r).hom =
      tensorSecondMap (commRightResolution Q.val).complex (scalarMap A r).hom := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  rw [hleft, hright] at he
  rw [torModule_smul_map E (commRightProjectiveChoice P) B r x,
    torModule_smul_map E' (commRightProjectiveChoice Q) A r]
  exact LinearMap.congr_fun he x

/-- The same symmetry, bundled as a K-linear equivalence for the upstream
Tor module structures. -/
def torSymmetryLinearEquiv (S : TorSymmetry.{u,v,w} K) (n : ℕ)
    (E : TorMaps.{u,v,w} K n) (E' : TorMaps.{u,w,v} K n)
    (A : ModuleCat.{v} K) (B : ModuleCat.{w} K)
    (P : ProjectiveChoice K A) (Q : ProjectiveChoice K B) :
    letI := commRightModule K A
    letI := commRightModule K B
    letI := torModule E (commRightProjectiveChoice P) B
    letI := torModule E' (commRightProjectiveChoice Q) A
    TorWith (commRightResolution P.val) B n ≃ₗ[K]
      TorWith (commRightResolution Q.val) A n := by
  letI := commRightModule K A
  letI := commRightModule K B
  letI := torModule E (commRightProjectiveChoice P) B
  letI := torModule E' (commRightProjectiveChoice Q) A
  let e := S.equivalence A B P.val Q.val P.property Q.property n
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' := tor_symmetry_linear K S n E E' A B P Q }


section SignedBridge
open CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Scalar restriction commutes with the common extension by zero. -/
def commRightExtendXIso (C : ChainComplex (ModuleCat.{v} K) ℕ) :
    ∀ a, HomologicalComplex.extend.X (commRightOrdinaryComplex C) a ≅
      (commRightFunctor K).obj (HomologicalComplex.extend.X C a)
  | none => IsZero.iso (isZero_zero _)
      ((commRightFunctor K).map_isZero (isZero_zero _))
  | some _ => Iso.refl _

def commRightExtendIso (C : ChainComplex (ModuleCat.{v} K) ℕ) :
    extendNonnegativeChain (commRightOrdinaryComplex C) ≅
      commRightComplex (extendNonnegativeChain C) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => commRightExtendXIso C (nonnegativeChainEmbedding.r p)) ?_
  intro i j _
  change (commRightExtendXIso C (nonnegativeChainEmbedding.r i)).hom ≫
      (commRightFunctor K).map (HomologicalComplex.extend.d C
        (nonnegativeChainEmbedding.r i) (nonnegativeChainEmbedding.r j)) =
    HomologicalComplex.extend.d (commRightOrdinaryComplex C)
      (nonnegativeChainEmbedding.r i) (nonnegativeChainEmbedding.r j) ≫
        (commRightExtendXIso C (nonnegativeChainEmbedding.r j)).hom
  cases nonnegativeChainEmbedding.r i <;> cases nonnegativeChainEmbedding.r j <;>
    simp [commRightExtendXIso, HomologicalComplex.extend.d]

theorem commRightExtendIso_retained (C : ChainComplex (ModuleCat.{v} K) ℕ) (n : ℕ) :
    ((commRightExtendIso C).hom.f (n : ℤ)) ≫
        (commRightFunctor K).map (C.extendXIso nonnegativeChainEmbedding (i := n) rfl).hom =
      ((commRightOrdinaryComplex C).extendXIso nonnegativeChainEmbedding (i := n) rfl).hom := by
  have aux (a : Option ℕ) (ha : a = some n) :
      (commRightExtendXIso C a).hom ≫
        (commRightFunctor K).map (HomologicalComplex.extend.XIso C ha).hom =
      (HomologicalComplex.extend.XIso (commRightOrdinaryComplex C) ha).hom := by
    subst a
    simp [commRightExtendXIso, HomologicalComplex.extend.XIso]
  exact aux _ (nonnegativeChainEmbedding.r_eq_some (i := n) rfl)

/-- Simultaneous isomorphisms of tensor factors induce an isomorphism of their totals. -/
def tensorTotalIso {C C' : ChainComplex (ModuleCat.{v} Kᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{w} K) ℤ} (e : C ≅ C') (f : D ≅ D') :
    tensorTotal C D ≅ tensorTotal C' D' :=
  HomologicalComplex₂.total.mapIso
    { hom := tensorBicomplexMap e.hom f.hom
      inv := tensorBicomplexMap e.inv f.inv
      hom_inv_id := by
        rw [← tensorBicomplexMap_comp, e.hom_inv_id, f.hom_inv_id, tensorBicomplexMap_id]
      inv_hom_id := by
        rw [← tensorBicomplexMap_comp, e.inv_hom_id, f.inv_hom_id, tensorBicomplexMap_id] } (ComplexShape.down ℤ)

/-- Koszul interchange on the actual ordinary total model. -/
def ordinarySignedFlip
    (C : ChainComplex (ModuleCat.{v} K) ℕ) (D : ChainComplex (ModuleCat.{w} K) ℕ) :
    ordinaryTotal (commRightOrdinaryComplex C) D ≅
      ordinaryTotal (commRightOrdinaryComplex D) C :=
  ((nonnegativeChainEmbedding.restrictionFunctor (ModuleCat ℤ)).mapIso
    ((tensorTotalIso (commRightExtendIso C) (Iso.refl (extendNonnegativeChain D))) ≪≫
      signedFlip (extendNonnegativeChain C) (extendNonnegativeChain D) ≪≫
        (tensorTotalIso (commRightExtendIso D) (Iso.refl (extendNonnegativeChain C))).symm))

theorem tensorTotalIso_inclusion {C C' : ChainComplex (ModuleCat.{v} Kᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{w} K) ℤ} (e : C ≅ C') (f : D ≅ D')
    (p q n : ℤ) (h : p + q = n) (a : C.X p) (b : D.X q) :
    ((tensorTotalIso e f).hom.f n).hom (tensorInclusion C D p q n h (tmul K a b)) =
      tensorInclusion C' D' p q n h (tmul K ((e.hom.f p).hom a) ((f.hom.f q).hom b)) := by
  exact tensorTotalMap_inclusion e.hom f.hom p q n h a b

theorem tensorTotalIso_inv_inclusion {C C' : ChainComplex (ModuleCat.{v} Kᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{w} K) ℤ} (e : C ≅ C') (f : D ≅ D')
    (p q n : ℤ) (h : p + q = n) (a : C'.X p) (b : D'.X q) :
    ((tensorTotalIso e f).inv.f n).hom (tensorInclusion C' D' p q n h (tmul K a b)) =
      tensorInclusion C D p q n h (tmul K ((e.inv.f p).hom a) ((f.inv.f q).hom b)) := by
  exact tensorTotalMap_inclusion e.inv f.inv p q n h a b

theorem commRightExtendIso_on_retained
    (C : ChainComplex (ModuleCat.{v} K) ℕ) (n : ℕ) (a : C.X n) :
    ((commRightExtendIso C).hom.f (n : ℤ)).hom
      (((commRightOrdinaryComplex C).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom a) =
        (C.extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom a := by
  apply (C.extendXIso nonnegativeChainEmbedding (i := n) rfl).toLinearEquiv.injective
  have h := congrArg (fun k => k.hom
      (((commRightOrdinaryComplex C).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom a))
    (commRightExtendIso_retained C n)
  change (C.extendXIso nonnegativeChainEmbedding (i := n) rfl).hom.hom
    (((commRightExtendIso C).hom.f (n : ℤ)).hom
      (((commRightOrdinaryComplex C).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom a)) =
    ((commRightOrdinaryComplex C).extendXIso nonnegativeChainEmbedding (i := n) rfl).hom.hom
      (((commRightOrdinaryComplex C).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom a) at h
  have hn := congrArg (fun k => k.hom a)
    ((commRightOrdinaryComplex C).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv_hom_id
  have ho := congrArg (fun k => k.hom a)
    (C.extendXIso nonnegativeChainEmbedding (i := n) rfl).inv_hom_id
  exact h.trans (hn.trans ho.symm)

theorem commRightExtendIso_inv_on_retained
    (C : ChainComplex (ModuleCat.{v} K) ℕ) (n : ℕ) (a : C.X n) :
    ((commRightExtendIso C).inv.f (n : ℤ)).hom
      ((C.extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom a) =
        ((commRightOrdinaryComplex C).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom a := by
  have hh := congrArg ((commRightExtendIso C).inv.f (n : ℤ)).hom
    (commRightExtendIso_on_retained C n a)
  have hc := congrArg (fun f => f.f (n : ℤ)) (commRightExtendIso C).hom_inv_id
  have ha := congrArg (fun f => f.hom
      (((commRightOrdinaryComplex C).extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom a)) hc
  exact hh.symm.trans ha

theorem ordinarySignedFlip_formula
    (C : ChainComplex (ModuleCat.{v} K) ℕ) (D : ChainComplex (ModuleCat.{w} K) ℕ)
    (p q n : ℕ) (h : p + q = n) (a : C.X p) (b : D.X q) :
    ((ordinarySignedFlip C D).hom.f n).hom
      (ordinaryInclusion (commRightOrdinaryComplex C) D p q n h (tmul K a b)) =
      ((p : ℤ) * (q : ℤ)).negOnePow •
        ordinaryInclusion (commRightOrdinaryComplex D) C q p n (by omega) (tmul K b a) := by
  change ((tensorTotalIso (commRightExtendIso D) (Iso.refl (extendNonnegativeChain C))).inv.f (n : ℤ)).hom
    (((signedFlip (extendNonnegativeChain C) (extendNonnegativeChain D)).hom.f (n : ℤ)).hom
      (((tensorTotalIso (commRightExtendIso C) (Iso.refl (extendNonnegativeChain D))).hom.f (n : ℤ)).hom
        (tensorInclusion (extendNonnegativeChain (commRightOrdinaryComplex C))
          (extendNonnegativeChain D) p q n (by exact_mod_cast h)
          (tmul K
            (((commRightOrdinaryComplex C).extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
            ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b))))) = _
  rw [tensorTotalIso_inclusion, commRightExtendIso_on_retained]
  change ((tensorTotalIso (commRightExtendIso D) (Iso.refl (extendNonnegativeChain C))).inv.f (n : ℤ)).hom
    (((signedFlip (extendNonnegativeChain C) (extendNonnegativeChain D)).hom.f (n : ℤ)).hom
      (tensorInclusion (commRightComplex (extendNonnegativeChain C)) (extendNonnegativeChain D)
        p q n (by exact_mod_cast h)
        (tmul K ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
          ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)))) = _
  rw [signedFlip_formula, map_zsmul_unit, tensorTotalIso_inv_inclusion,
    commRightExtendIso_inv_on_retained]
  rfl

/-- The ordinary Koszul interchange induces exactly the flip used after
balance, as witnessed by the augmentation diagram. -/
theorem ordinarySignedFlip_augmentation
    {A : Type v} {B : Type w} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (P : P103.Specs.Ch10.Comparison.LeftResolution K A)
    (Q : P103.Specs.Ch10.Comparison.LeftResolution K B) :
    letI := commRightModule K A
    letI := commRightModule K B
    ∀ (α : Augmentations (commRightResolution P) Q)
      (β : Augmentations (commRightResolution Q) P),
      (ordinarySignedFlip P.complex Q.complex).hom ≫ β.left =
        α.right ≫ (commOrdinaryTensorFlip A Q.complex).hom := by
  letI := commRightModule K A
  letI := commRightModule K B
  intro α β
  apply HomologicalComplex.Hom.ext
  funext n
  apply ordinaryTotal_hom_ext (commRightOrdinaryComplex P.complex) Q.complex n
  intro p q h a b
  change (β.left.f n).hom
    (((ordinarySignedFlip P.complex Q.complex).hom.f n).hom
      (ordinaryInclusion (commRightOrdinaryComplex P.complex) Q.complex p q n h (tmul K a b))) =
    (((commOrdinaryTensorFlip A Q.complex).hom.f n).hom
      ((α.right.f n).hom
        (ordinaryInclusion (commRightOrdinaryComplex P.complex) Q.complex p q n h (tmul K a b))))
  rw [ordinarySignedFlip_formula, map_zsmul_unit]
  by_cases hp : p = 0
  · subst p
    have hn : q = n := by omega
    cases hn
    simp only [Nat.cast_zero, zero_mul, Int.negOnePow_zero, one_smul]
    change (β.left.f n).hom
      (ordinaryInclusion (commRightResolution Q).complex P.complex n 0 n (by omega) (tmul K b a)) =
      ((commOrdinaryTensorFlip A Q.complex).hom.f n).hom
        ((α.right.f n).hom
          (ordinaryInclusion (commRightResolution P).complex Q.complex 0 n n (by omega) (tmul K a b)))
    rw [β.left_zero, α.right_zero]
    rfl
  · have ha := LinearMap.congr_fun (α.right_positive p q n h hp) (tmul K a b)
    have hb := LinearMap.congr_fun (β.left_positive q p n (by omega) hp) (tmul K b a)
    change (α.right.f n).hom
      (ordinaryInclusion (commRightOrdinaryComplex P.complex) Q.complex p q n h (tmul K a b)) = 0 at ha
    change (β.left.f n).hom
      (ordinaryInclusion (commRightOrdinaryComplex Q.complex) P.complex q p n (by omega) (tmul K b a)) = 0 at hb
    rw [ha, hb, map_zero, smul_zero]




/-- On homology, the ordinary signed flip gives precisely the symmetry
obtained from the two balance augmentations. -/
theorem ordinarySignedFlip_homology
    {A : Type v} {B : Type w} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (P : LeftResolution K A) (Q : LeftResolution K B) :
    letI := commRightModule K A
    letI := commRightModule K B
    ∀ (α : Augmentations (commRightResolution P) Q)
      (β : Augmentations (commRightResolution Q) P)
      (hL : QuasiIsomorphism α.left) (hR : QuasiIsomorphism α.right)
      (n : ℕ) (z : Homology (ordinaryTotal (commRightResolution P).complex Q.complex) n),
      homologyMap (commOrdinaryTensorFlip A Q.complex).hom n
          (balanceEquiv α hL hR n (homologyMap α.left n z)) =
        homologyMap ((ordinarySignedFlip P.complex Q.complex).hom ≫ β.left) n z := by
  letI := commRightModule K A
  letI := commRightModule K B
  intro α β hL hR n z
  rw [balanceEquiv_apply_left]
  have hc : homologyMap (commOrdinaryTensorFlip A Q.complex).hom n
      (homologyMap α.right n z) =
      homologyMap (α.right ≫ (commOrdinaryTensorFlip A Q.complex).hom) n z := by
    induction z using Submodule.Quotient.induction_on with
    | _ z => rfl
  exact hc.trans
    (congrArg (fun f => homologyMap f n z) (ordinarySignedFlip_augmentation P Q α β).symm)


theorem signed_flip_induces : signed_flip_inducesType.{u,v,w} := by
  intro K _ A B _ _ _ _ P Q
  letI := commRightModule K A
  letI := commRightModule K B
  exact ⟨ordinarySignedFlip P.complex Q.complex,
    ordinarySignedFlip_formula P.complex Q.complex, fun α β =>
      ⟨ordinarySignedFlip_augmentation P Q α β, ordinarySignedFlip_homology P Q α β⟩⟩

end SignedBridge

end Commutative

end
end P103.Ch11.TorBalance
