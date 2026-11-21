import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.VanishingAndFlatness
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtBalance
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests
import MathGenome.Internal.AlgebraCore.P103.Ch10.HomologySequence
import MathGenome.Internal.AlgebraCore.P103.Ch10.InjectiveResolutions

import Batteries.Tactic.OpenPrivate

namespace P103.Ch11.VanishingAndFlatness
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Specs.Ch02.FlatnessTests
open P103.Specs.Ch11.VanishingAndFlatness
noncomputable section
universe u v w x y z
variable {R : Type u} [Ring R]

/-- Exactness at one degree kills the explicit quotient homology. -/
theorem homology_subsingleton_of_exact {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι)
    (he : Function.Exact (C.d (c.prev n) n).hom (C.d n (c.next n)).hom) :
    Subsingleton (Homology C n) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro a _
  exact (he a.val).mp a.property

/-- Changing the testing universe does not change flatness, by the finite
relations criterion, whose data are all finite. -/
theorem flat_change_universe {M : Type v} [AddCommGroup M] [Module R M]
    (h : Flat.{u,v,w} R M) : Flat.{u,v,x} R M :=
  (P103.Ch02.FlatnessTests.flat_iff_finiteRelations.{u,v,x} R M).mpr
    ((P103.Ch02.FlatnessTests.flat_iff_finiteRelations.{u,v,w} R M).mp h)

theorem flat_tensor_injective
    {M : Type w} [AddCommGroup M] [Module R M] (hM : Flat.{u,w,z} R M)
    {A : Type v} {B : Type x} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup B] [Module Rᵐᵒᵖ B]
    (f : A →ₗ[Rᵐᵒᵖ] B) (hf : Function.Injective f) :
    Function.Injective (tensorMap f (LinearMap.id : M →ₗ[R] M)) := by
  let eA : ULift.{max u v w x} A ≃ₗ[Rᵐᵒᵖ] A := ULift.moduleEquiv
  let eB : ULift.{max u v w x} B ≃ₗ[Rᵐᵒᵖ] B := ULift.moduleEquiv
  let f' := eB.symm.toLinearMap.comp (f.comp eA.toLinearMap)
  have hflat := flat_change_universe.{u,w,z,max v x} hM
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
theorem flat_tensor_exact
    {M : Type w} [AddCommGroup M] [Module R M] (hM : Flat.{u,w,z} R M)
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
  have hi := flat_tensor_injective hM (LinearMap.range g).subtype Subtype.val_injective
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

section RightFlat
open private oppositeFlip oppositeFlip_tmul from MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem right_flat_tensor_exact
    {M : Type w} [AddCommGroup M] [Module Rᵐᵒᵖ M] (hM : RightFlat.{u,w,z} R M)
    {A : Type v} {B : Type x} {C : Type y} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (he : Function.Exact f g) :
    Function.Exact (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f)
      (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) g) := by
  letI := doubleOppositeModule R A
  letI := doubleOppositeModule R B
  letI := doubleOppositeModule R C
  let fop : A →ₗ[Rᵐᵒᵖᵐᵒᵖ] B :=
    { f.toAddMonoidHom with map_smul' := fun r a => f.map_smul r.unop.unop a }
  let gop : B →ₗ[Rᵐᵒᵖᵐᵒᵖ] C :=
    { g.toAddMonoidHom with map_smul' := fun r b => g.map_smul r.unop.unop b }
  have hop := flat_tensor_exact
    ((P103.Ch02.FlatnessTests.rightFlat_iff_opposite R M).mp hM) fop gop he
  let eA := oppositeFlip (R := R) (A := M) (B := A)
  let eB := oppositeFlip (R := R) (A := M) (B := B)
  let eC := oppositeFlip (R := R) (A := M) (B := C)
  have hf (a : Tensor R M A) : eB (tensorMap LinearMap.id f a) =
      tensorMap fop LinearMap.id (eA a) := by
    induction a using induction_on with
    | h0 => simp
    | ht m a => rfl
    | ha a b ha hb => simp [ha, hb]
  have hg (b : Tensor R M B) : eC (tensorMap LinearMap.id g b) =
      tensorMap gop LinearMap.id (eB b) := by
    induction b using induction_on with
    | h0 => simp
    | ht m b => rfl
    | ha a b ha hb => simp [ha, hb]
  intro b
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := (hop (eB b)).mp (by rw [← hg, hb, map_zero])
    refine ⟨eA.symm a, eB.injective ?_⟩
    rw [hf, eA.apply_symm_apply, ha]
  · rintro ⟨a, rfl⟩
    apply eC.injective
    rw [hg, hf, hop.apply_apply_eq_zero, map_zero]
end RightFlat

/-- Flatness kills positive homology in the original right-resolution model. -/
theorem tor_left_flat_proof : tor_left_flatType.{u,v,w} := by
  intro R _ A B _ _ _ _ hB P _ n
  apply homology_subsingleton_of_exact
  rw [ChainComplex.prev, ChainComplex.next_nat_succ]
  exact flat_tensor_exact hB _ _ (LinearMap.exact_iff.mpr (P.exact_succ n).symm)

/-- The other side follows using the established noncommutative balance maps. -/
theorem tor_right_flat_proof : tor_right_flatType.{u,v,w} := by
  intro R _ A B _ _ _ _ hA P hP n
  obtain ⟨Q, hQ⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution R B
  obtain ⟨α, hL, hR⟩ := P103.Ch11.TorBalance.balance R A B P Q hP hQ
  have hv : Subsingleton (Homology (leftOrdinaryTensorComplex A Q.complex) (n+1)) := by
    apply homology_subsingleton_of_exact
    rw [ChainComplex.prev, ChainComplex.next_nat_succ]
    exact right_flat_tensor_exact hA _ _ (LinearMap.exact_iff.mpr (Q.exact_succ n).symm)
  exact (balanceEquiv α hL hR (n+1)).injective.subsingleton

/-- Injectivity of the coefficient makes the reversed Hom sequence exact. -/
theorem ext_injective_proof : ext_injectiveType.{u,v,w} := by
  intro R _ A B _ _ _ _ hB P _ n
  letI := hB
  apply homology_subsingleton_of_exact
  rw [show (ComplexShape.up ℕ).prev (n+1) = n from
    ComplexShape.prev_eq' _ rfl, CochainComplex.next]
  change Function.Exact
    (P103.HomTensorExactness.pre (Q := B) (P.complex.d (n+1) n).hom)
    (P103.HomTensorExactness.pre (Q := B) (P.complex.d (n+2) (n+1)).hom)
  exact P103.Ch11.ExtBalance.pre_exact _ _ (LinearMap.exact_iff.mpr (P.exact_succ n).symm)

/-- With a projective first variable the injective Hom model is exact. -/
theorem ext_projective_proof : ext_projectiveType.{u,v,w} := by
  intro R _ A B _ _ _ _ hA P hP n
  letI := hA
  let I : InjectiveResolution R B :=
    Classical.choice (P103.Ch10.InjectiveResolutions.existsResolution R B)
  obtain ⟨α, β, _, _, _, _, he⟩ := P103.Ch11.ExtBalance.balance R A B P I hP
  obtain ⟨e, _⟩ := he (n+1)
  have hv : Subsingleton (Homology (P103.Specs.Ch11.ExtBalance.injectiveHom A I.complex) (n+1)) := by
    apply homology_subsingleton_of_exact
    rw [show (ComplexShape.up ℕ).prev (n+1) = n from
    ComplexShape.prev_eq' _ rfl, CochainComplex.next]
    exact P103.Ch11.ExtBalance.post_exact _ _ (I.exact_succ n)
  exact e.symm.injective.subsingleton

/-- Degree-zero homology of an augmented exact chain complex is its target. -/
def zeroHomologyEquiv (C : ChainComplex (ModuleCat.{v} R) ℕ)
    {D : Type w} [AddCommGroup D] [Module R D] (ε : C.X 0 →ₗ[R] D)
    (he : Function.Exact (C.d 1 0).hom ε) (hs : Function.Surjective ε) :
    Homology C 0 ≃ₗ[R] D := by
  let g : cycles C 0 →ₗ[R] D := ε.comp (cycles C 0).subtype
  have hg : Function.Surjective g := by
    intro d
    obtain ⟨a, ha⟩ := hs d
    exact ⟨⟨a, P103.Ch11.ExtTorDefinitions.chain_mem_zero_cycles C a⟩, ha⟩
  have hk : cycleBoundaries C 0 = LinearMap.ker g := by
    ext a
    change (∃ b, (C.d ((ComplexShape.down ℕ).prev 0) 0).hom b = a.val) ↔ ε a.val = 0
    rw [ChainComplex.prev]
    exact (he a.val).symm
  exact (Submodule.quotEquivOfEq _ _ hk).trans (g.quotKerEquivOfSurjective hg)

theorem zeroHomologyEquiv_class (C : ChainComplex (ModuleCat.{v} R) ℕ)
    {D : Type w} [AddCommGroup D] [Module R D] (ε : C.X 0 →ₗ[R] D)
    (he : Function.Exact (C.d 1 0).hom ε) (hs : Function.Surjective ε)
    (a : cycles C 0) : zeroHomologyEquiv C ε he hs (homologyClass C 0 a) = ε a.val := by
  simp only [zeroHomologyEquiv, LinearEquiv.trans_apply, homologyClass,
    Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.comp_apply,
    Submodule.subtype_apply]
  rfl

/-- The elementary zero-degree tensor identification in the balanced model. -/
def leftZero {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A] :
    Homology (leftOrdinaryTensorComplex A Q.complex) 0 ≃ₗ[ℤ] Tensor R A B := by
  have he := P103.HomTensorExactness.tensorSecond_rightExact
    (A := A) (Q.complex.d 1 0).hom Q.ε
    (LinearMap.exact_iff.mpr Q.exact_zero.symm) Q.surjective
    (tensorMap LinearMap.id (Q.complex.d 1 0).hom).toAddMonoidHom
    (tensorMap LinearMap.id Q.ε).toAddMonoidHom (by intros; rfl) (by intros; rfl)
  exact zeroHomologyEquiv _ (tensorMap LinearMap.id Q.ε) he.1 he.2

theorem leftZero_class {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (a : cycles (leftOrdinaryTensorComplex A Q.complex) 0) :
    leftZero Q A (homologyClass _ 0 a) = tensorMap LinearMap.id Q.ε a.val := by
  unfold leftZero
  exact zeroHomologyEquiv_class _ _ _ _ a

/-- Transport injectivity from degree-zero homology to the tensor target. -/
theorem zero_tensor_injective {S : Type*} [Ring S]
    {U V : ChainComplex (ModuleCat.{v} S) ℕ}
    {D E : Type w} [AddCommGroup D] [Module S D] [AddCommGroup E] [Module S E]
    (f : U ⟶ V) (eU : Homology U 0 ≃+ D) (eV : Homology V 0 ≃+ E)
    (g : D →ₗ[S] E) (hn : ∀ a, eV (homologyMap f 0 a) = g (eU a))
    (hf : Function.Injective (homologyMap f 0)) : Function.Injective g := by
  intro d d' hd
  obtain ⟨a, rfl⟩ := eU.surjective d
  obtain ⟨a', rfl⟩ := eU.surjective d'
  exact congrArg eU (hf (eV.injective (by rw [hn, hn, hd])))

/-- The second-variable sequence at Tor₁→Tor₀ proves preservation of an injection. -/
theorem tensor_second_injective_of_tor_one
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    {B M C : Type w} [AddCommGroup B] [AddCommGroup M] [AddCommGroup C]
    [Module R B] [Module R M] [Module R C]
    (i : B →ₗ[R] M) (p : M →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p)
    (hv : Subsingleton (TorWith P C 1)) :
    Function.Injective (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i) := by
  let a := tensorSecondMap P.complex i
  let b := tensorSecondMap P.complex p
  have hs : P103.Specs.Ch10.HomologySequence.DegreewiseExact a b := by
    intro n
    refine ⟨P103.Ch11.TorBalance.right_projective_tensor_injective (hP n) i hi,
      P103.Ch11.TorBalance.right_projective_tensor_exact (hP n) i p he, ?_⟩
    exact P103.HomTensorExactness.tensorSecond_surjective p hp
      (tensorMap (LinearMap.id : P.complex.X n →ₗ[Rᵐᵒᵖ] P.complex.X n) p).toAddMonoidHom
      (by intros; rfl)
  obtain ⟨δ, hδ, _⟩ := P103.Ch10.HomologySequence.sequence a b hs 1 0 (by rfl)
  letI := hv
  have hinj := P103.Ch10.HomologySequence.exact_injective_of_subsingleton
    δ (homologyMap a 0) hδ.2.2.2
  apply zero_tensor_injective a
    (P103.Ch11.ExtTorDefinitions.torZero P B)
    (P103.Ch11.ExtTorDefinitions.torZero P M) _ ?_ hinj
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change P103.Ch11.ExtTorDefinitions.torZero P M
      (homologyMap a 0 (homologyClass _ 0 z)) =
      tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i
        (P103.Ch11.ExtTorDefinitions.torZero P B (homologyClass _ 0 z))
    rw [P103.Ch10.Complexes.homologyMap_apply,
      P103.Ch11.ExtTorDefinitions.torZero_class,
      P103.Ch11.ExtTorDefinitions.torZero_class]
    have ht : (tensorMap P.ε (LinearMap.id : M →ₗ[R] M)).comp
        (tensorMap LinearMap.id i) =
        (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i).comp
          (tensorMap P.ε LinearMap.id) := tensor_hom_ext _ _ (by intros; rfl)
    exact LinearMap.congr_fun ht z.val

/-- The first-variable sequence in the balanced model has the dual consequence. -/
theorem tensor_first_injective_of_left_homology_one
    {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective)
    {A M C : Type v} [AddCommGroup A] [AddCommGroup M] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ C]
    (i : A →ₗ[Rᵐᵒᵖ] M) (p : M →ₗ[Rᵐᵒᵖ] C)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p)
    (hv : Subsingleton (Homology (leftOrdinaryTensorComplex C Q.complex) 1)) :
    Function.Injective (tensorMap i (LinearMap.id : B →ₗ[R] B)) := by
  let a := leftTensorFirstMap i Q.complex
  let b := leftTensorFirstMap p Q.complex
  have hs : P103.Specs.Ch10.HomologySequence.DegreewiseExact a b := by
    intro n
    refine ⟨P103.Ch11.TorBalance.projective_tensor_injective (hQ n) i hi,
      P103.Ch11.TorBalance.projective_tensor_exact (hQ n) i p he, ?_⟩
    exact (P103.HomTensorExactness.tensor_first_rightExact i p he hp
      (tensorMap i (LinearMap.id : Q.complex.X n →ₗ[R] Q.complex.X n)).toAddMonoidHom
      (by intros; rfl) (tensorMap p LinearMap.id).toAddMonoidHom (by intros; rfl)).2
  obtain ⟨δ, hδ, _⟩ := P103.Ch10.HomologySequence.sequence a b hs 1 0 (by rfl)
  letI := hv
  have hinj := P103.Ch10.HomologySequence.exact_injective_of_subsingleton
    δ (homologyMap a 0) hδ.2.2.2
  apply zero_tensor_injective a (leftZero Q A).toAddEquiv (leftZero Q M).toAddEquiv _ ?_ hinj
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change leftZero Q M (homologyMap a 0 (homologyClass _ 0 z)) =
      tensorMap i (LinearMap.id : B →ₗ[R] B) (leftZero Q A (homologyClass _ 0 z))
    rw [P103.Ch10.Complexes.homologyMap_apply, leftZero_class, leftZero_class]
    have ht : (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) Q.ε).comp
        (tensorMap i LinearMap.id) =
        (tensorMap i (LinearMap.id : B →ₗ[R] B)).comp
          (tensorMap LinearMap.id Q.ε) := tensor_hom_ext _ _ (by intros; rfl)
    exact LinearMap.congr_fun ht z.val

/-- Vanishing on every cokernel makes the original right tensor functor flat. -/
theorem right_flat_iff_tor_one_proof : right_flat_iff_tor_oneType.{u,v,w} := by
  intro R _ A _ _
  constructor
  · intro h B _ _ P hP
    have h' : RightFlat.{u,v,max u v w} R A :=
      (P103.Ch02.FlatnessTests.rightFlat_iff_opposite R A).mpr
        (flat_change_universe ((P103.Ch02.FlatnessTests.rightFlat_iff_opposite R A).mp h))
    exact tor_right_flat_proof R A B h' P hP 0
  · intro h B M _ _ _ _ i hi F hF
    obtain ⟨P, hP⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution Rᵐᵒᵖ A
    have hinj := tensor_second_injective_of_tor_one P hP i (LinearMap.range i).mkQ hi
      (LinearMap.exact_map_mkQ_range i) (Submodule.mkQ_surjective _)
      (h (M ⧸ LinearMap.range i) P hP)
    have hmap : F = (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i).toAddMonoidHom :=
      P103.BalancedTensor.hom_ext hF
    rw [hmap]
    exact hinj

/-- The dual statement uses the first-variable balanced sequence. -/
theorem left_flat_iff_tor_one_proof : left_flat_iff_tor_oneType.{u,v,w} := by
  intro R _ B _ _
  constructor
  · intro h A _ _ P hP
    exact tor_left_flat_proof R A B (flat_change_universe h) P hP 0
  · intro h A M _ _ _ _ i hi F hF
    obtain ⟨Q, hQ⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution R B
    let C := M ⧸ LinearMap.range i
    obtain ⟨P, hP⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution Rᵐᵒᵖ C
    obtain ⟨α, hL, hR⟩ := P103.Ch11.TorBalance.balance R C B P Q hP hQ
    letI := h C P hP
    have hv : Subsingleton (Homology (leftOrdinaryTensorComplex C Q.complex) 1) :=
      (balanceEquiv α hL hR 1).symm.injective.subsingleton
    have hinj := tensor_first_injective_of_left_homology_one Q hQ i (LinearMap.range i).mkQ hi
      (LinearMap.exact_map_mkQ_range i) (Submodule.mkQ_surjective _) hv
    have hmap : F = (tensorMap i (LinearMap.id : B →ₗ[R] B)).toAddMonoidHom :=
      P103.BalancedTensor.hom_ext hF
    rw [hmap]
    exact hinj

/-- Positive Ext vanishes for projective first coefficients. -/
theorem ext_projective : ext_projectiveType.{u,v,w} := ext_projective_proof

/-- Positive Ext vanishes for injective second coefficients. -/
theorem ext_injective : ext_injectiveType.{u,v,w} := ext_injective_proof

/-- The projective Ext assertion for right modules. -/
theorem right_ext_projective : right_ext_projectiveType.{u,v,w} := by
  intro R _
  exact ext_projective_proof Rᵐᵒᵖ

/-- The injective Ext assertion for right modules. -/
theorem right_ext_injective : right_ext_injectiveType.{u,v,w} := by
  intro R _
  exact ext_injective_proof Rᵐᵒᵖ

/-- Positive Tor vanishes for flat left coefficients. -/
theorem tor_left_flat : tor_left_flatType.{u,v,w} := tor_left_flat_proof

/-- Positive Tor vanishes for flat right coefficients. -/
theorem tor_right_flat : tor_right_flatType.{u,v,w} := tor_right_flat_proof

/-- A right module is flat exactly when Tor₁ vanishes on every left module. -/
theorem right_flat_iff_tor_one : right_flat_iff_tor_oneType.{u,v,w} :=
  right_flat_iff_tor_one_proof

/-- A left module is flat exactly when Tor₁ vanishes on every right module. -/
theorem left_flat_iff_tor_one :
    ∀ (R : Type u) [Ring R] (B : Type w) [AddCommGroup B] [Module R B],
      Flat.{u,w,v} R B ↔
        ∀ (A : Type (max u v w)) [AddCommGroup A] [Module Rᵐᵒᵖ A]
          (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective → Subsingleton (TorWith P B 1) :=
  left_flat_iff_tor_one_proof

end
end P103.Ch11.VanishingAndFlatness
