import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.PrimeQuotientReduction
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FinitePrimeFiltration
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IntersectionEulerAdditivity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct
open P103.Ch11.ExtTorDefinitions (resolutionFamily)
open P103.Ch12.TorBaseChange (additiveCyclesEquiv additiveCyclesEquiv_boundary)
open P103.Specs.Ch10.Complexes (cycles cycleBoundaries Homology)
open P103.Specs.Ch12.TorBaseChange (coefficientComplex)
open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.Specs
  (cutoffEuler intersectionEuler regularLocalDimension)
open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
  (cutoffEuler_symm)
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
  (Tor torRightEquiv)
open CommutativeAlgebraNotes.Intersection.IntersectionEulerAdditivity
  (intersectionEuler_add_left intersectionEuler_add_right)

namespace CommutativeAlgebraNotes.Intersection.PrimeQuotientReduction

universe u v w v'

variable {R : Type u} [CommRing R]

theorem additivity : Specs.additivity.{u,v,w} :=
  ⟨intersectionEuler_add_left, intersectionEuler_add_right⟩

theorem dimension_maximum : Specs.dimensionMaximum.{u,v} := by
  intro R _ _ M _ F hM
  obtain ⟨i, hi, hmax⟩ := F.supportDim_maximum hM
  exact ⟨i, hi.symm, fun j => (hmax j).trans hi.symm.le⟩

/-- Compatible linear equivalences of terms identify cycles and boundaries
even when the chain complexes live in different module universes. -/
private def homologyEquivOfTermwiseEquiv
    {K : ChainComplex (ModuleCat.{v} R) ℕ} {L : ChainComplex (ModuleCat.{v'} R) ℕ}
    (e : ∀ n, K.X n ≃ₗ[R] L.X n)
    (he : ∀ i j x, e j ((K.d i j).hom x) = (L.d i j).hom (e i x))
    (n : ℕ) : Homology K n ≃ₗ[R] Homology L n := by
  let a := fun i => (e i).toAddEquiv
  let ec : cycles K n ≃ₗ[R] cycles L n :=
    { additiveCyclesEquiv a he n with
      map_smul' := by
        intro r z
        exact Subtype.ext ((e n).map_smul r z.val) }
  refine Submodule.Quotient.equiv _ _ ec ?_
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (additiveCyclesEquiv_boundary a he n x).mp hx
  · intro hz
    refine ⟨ec.symm z, (additiveCyclesEquiv_boundary a he n _).mpr ?_,
      ec.apply_symm_apply z⟩
    change ec (ec.symm z) ∈ cycleBoundaries L n
    rwa [ec.apply_symm_apply]

/-- Compute both Tor modules using the same resolution of the fixed argument. -/
private def torEquivLeft {M : ModuleCat.{v} R} {M' : ModuleCat.{v'} R}
    (e : M ≃ₗ[R] M') (N : ModuleCat.{w} R) (n : ℕ) :
    Tor M N n ≃ₗ[R] Tor M' N n := by
  let P := resolutionFamily R N
  let K := P.val.complex
  let eTensor (i : ℕ) :
      (coefficientComplex (S := R) K M).X i ≃ₗ[R]
        (coefficientComplex (S := R) K M').X i :=
    TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R (K.X i))
  have hTensor (i j : ℕ) (x : (coefficientComplex (S := R) K M).X i) :
      eTensor j (((coefficientComplex (S := R) K M).d i j).hom x) =
        ((coefficientComplex (S := R) K M').d i j).hom (eTensor i x) := by
    have hc : (eTensor j).toLinearMap.comp ((coefficientComplex (S := R) K M).d i j).hom =
        ((coefficientComplex (S := R) K M').d i j).hom.comp (eTensor i).toLinearMap :=
      TensorProduct.ext' fun _ _ => rfl
    exact LinearMap.congr_fun hc x
  exact (torRightEquiv M N P.val P.property n).trans
    ((homologyEquivOfTermwiseEquiv eTensor hTensor n).trans
      (torRightEquiv M' N P.val P.property n).symm)

section Filtration

variable [IsRegularLocalRing R]

private theorem intersectionEuler_congr_left
    {M : ModuleCat.{v} R} {M' : ModuleCat.{v'} R} (e : M ≃ₗ[R] M')
    (N : ModuleCat.{w} R) : intersectionEuler M N = intersectionEuler M' N := by
  unfold intersectionEuler cutoffEuler
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [(torEquivLeft e N n).length_eq]

private theorem intersectionEuler_zero_left (A : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R A] [Module.Finite R N] [Subsingleton A]
    (h : Module.support R A ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R}) :
    intersectionEuler A N = 0 := by
  have hzero : Function.Bijective (0 : A →ₗ[R] A) :=
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ x⟩⟩
  have hχ := intersectionEuler_add_left A A A N 0 0 hzero.1
    ((LinearMap.exact_zero_iff_surjective A _).mpr hzero.2) hzero.2 h h h
  omega

private theorem sum_prime_quotients_left (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] (F : PrimeFiltration R M)
    (h : Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R}) :
    intersectionEuler M N = ∑ i : Fin F.length,
      intersectionEuler (ModuleCat.of R (R ⧸ (F.prime i).asIdeal)) N := by
  let stage (k : Fin (F.length + 1)) := ModuleCat.of R (F.stage k)
  let factor (i : Fin F.length) := ModuleCat.of R (R ⧸ (F.prime i).asIdeal)
  have hstage (k : Fin (F.length + 1)) :
      Module.support R (stage k) ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R} :=
    (Set.inter_subset_inter_left _ (F.stage_support_subset k)).trans h
  have hstep (i : Fin F.length) :
      intersectionEuler (stage i.succ) N =
        intersectionEuler (stage i.castSucc) N + intersectionEuler (factor i) N := by
    let Q := (F.stage i.castSucc).submoduleOf (F.stage i.succ)
    let C := ModuleCat.of R ((F.stage i.succ : Submodule R M) ⧸ Q)
    have hC : Module.support R C ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R} :=
      (Set.inter_subset_inter_left _ ((F.factorEquiv i).support_eq.le.trans
        (F.factor_support_subset i))).trans h
    have he : Function.Exact (F.inclusion (Fin.castSucc_le_succ i)) Q.mkQ :=
      (F.factorEquiv i).postcomp_exact_iff_exact.mp (F.step_shortExact i).2.1
    rw [← intersectionEuler_congr_left (M := C) (M' := factor i) (F.factorEquiv i) N]
    exact intersectionEuler_add_left (stage i.castSucc) (stage i.succ) C N
      (F.inclusion (Fin.castSucc_le_succ i)) Q.mkQ (F.inclusion_injective _) he
      (Submodule.mkQ_surjective Q) (hstage _) (hstage _) hC
  have hpartial (k : ℕ) (hk : k < F.length + 1) :
      intersectionEuler (stage ⟨k, hk⟩) N =
        ∑ i : Fin k, intersectionEuler (factor (Fin.castLE (Nat.le_of_lt_succ hk) i)) N := by
    induction k with
    | zero =>
      have hbot : F.stage 0 = ⊥ := F.first_eq_bot
      have : Subsingleton (stage 0) := by
        change Subsingleton (F.stage 0)
        rw [hbot]
        infer_instance
      change intersectionEuler (stage 0) N = _
      simpa only [Finset.univ_eq_empty, Finset.sum_empty] using
        intersectionEuler_zero_left (stage 0) N (hstage 0)
    | succ k ih =>
      let i : Fin F.length := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      change intersectionEuler (stage i.succ) N = _
      rw [hstep i, Fin.sum_univ_castSucc]
      exact congrArg (fun s : ℤ => s + intersectionEuler (factor i) N)
        (ih (Nat.lt_trans (Nat.lt_succ_self k) hk))
  let e : stage (Fin.last F.length) ≃ₗ[R] M :=
    (LinearEquiv.ofEq _ _ F.last_eq_top).trans Submodule.topEquiv
  rw [← intersectionEuler_congr_left e N]
  exact hpartial F.length (Nat.lt_succ_self _)

theorem prime_filtration_reduction : Specs.primeFiltrationReduction.{u,v,w} := by
  intro R _ _ M N _ _ F G h
  have hF (i : Fin F.length) :
      Module.support R (R ⧸ (F.prime i).asIdeal) ∩ Module.support R N ⊆
        {IsLocalRing.closedPoint R} :=
    (Set.inter_subset_inter_left _ (F.factor_support_subset i)).trans h
  refine ⟨fun i j => (Set.inter_subset_inter_right _ (G.factor_support_subset j)).trans
    (hF i), ?_⟩
  rw [sum_prime_quotients_left M N F h]
  refine Finset.sum_congr rfl fun i _ => ?_
  let A := ModuleCat.of R (R ⧸ (F.prime i).asIdeal)
  have hsymm : intersectionEuler A N = intersectionEuler N A :=
    cutoffEuler_symm A N (regularLocalDimension R)
  have h' : Module.support R N ∩ Module.support R A ⊆ {IsLocalRing.closedPoint R} := by
    simpa only [Set.inter_comm] using hF i
  rw [hsymm, sum_prime_quotients_left N A G h']
  exact Finset.sum_congr rfl fun j _ => (cutoffEuler_symm
    (ModuleCat.of R (R ⧸ (G.prime j).asIdeal)) A (regularLocalDimension R))

end Filtration

section Grothendieck

variable {X : Set (PrimeSpectrum R)}

theorem class_shortExact : Specs.classShortExact.{u,v} := by
  intro R _ X A M C f g hf he hg
  have hmem : Finsupp.single M (1 : ℤ) - (Finsupp.single A 1 + Finsupp.single C 1) ∈
      exactRelations X :=
    Submodule.subset_span ⟨A, M, C, f, g, hf, he, hg, rfl⟩
  have hzero := (Submodule.Quotient.mk_eq_zero _).mpr hmem
  change (exactRelations X).mkQ _ = 0 at hzero
  simpa only [map_sub, map_add, sub_eq_zero, classOf] using hzero

theorem class_eq_of_linearEquiv : Specs.classEqOfLinearEquiv.{u,v} := by
  intro R _ X M N e
  let Z : SupportedModule.{u,v} X :=
    ⟨ModuleCat.of R (⊥ : Submodule R N.obj), inferInstance, by
      change Module.support R (⊥ : Submodule R N.obj) ⊆ X
      rw [Module.support_eq_empty]
      exact Set.empty_subset X⟩
  have hsurj {A : ModuleCat.{v} R} : Function.Surjective (0 : A →ₗ[R] Z.obj) :=
    fun z => ⟨0, Subsingleton.elim _ z⟩
  have hz : classOf Z = 0 := by
    have hh := class_shortExact Z Z Z 0 0 (fun _ _ _ => Subsingleton.elim _ _)
      ((LinearMap.exact_zero_iff_surjective Z.obj _).mpr hsurj) hsurj
    exact (add_left_cancel ((add_zero (classOf Z)).trans hh)).symm
  have hh := class_shortExact M N Z e.toLinearMap 0 e.injective
    ((LinearMap.exact_zero_iff_surjective Z.obj e.toLinearMap).mpr e.surjective) hsurj
  simpa only [hz, add_zero] using hh.symm

variable {T : Type*} [AddCommGroup T]

/-- Extend a function on supported modules that is additive on short exact
sequences to an integer linear map out of the Grothendieck group. -/
private def liftToGrothendieck (a : SupportedModule.{u,v} X → T)
    (ha : ∀ (A M C : SupportedModule.{u,v} X)
      (f : A.obj →ₗ[R] M.obj) (g : M.obj →ₗ[R] C.obj),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      a M = a A + a C) :
    GrothendieckGroup.{u,v} X →ₗ[ℤ] T :=
  (exactRelations X).liftQ (Finsupp.linearCombination ℤ a) (by
    apply Submodule.span_le.mpr
    rintro r ⟨A, M, C, f, g, hf, he, hg, rfl⟩
    change Finsupp.linearCombination ℤ a
      (Finsupp.single M 1 - (Finsupp.single A 1 + Finsupp.single C 1)) = 0
    simp only [map_sub, map_add, Finsupp.linearCombination_single,
      one_smul, sub_eq_zero]
    exact ha A M C f g hf he hg)

@[simp] private theorem liftToGrothendieck_classOf
    (a : SupportedModule.{u,v} X → T) (ha) (M : SupportedModule.{u,v} X) :
    liftToGrothendieck a ha (classOf M) = a M := by
  change Finsupp.linearCombination ℤ a (Finsupp.single M 1) = a M
  rw [Finsupp.linearCombination_single, one_smul]

private theorem grothendieck_hom_ext
    {f g : GrothendieckGroup.{u,v} X →ₗ[ℤ] T}
    (h : ∀ M : SupportedModule.{u,v} X, f (classOf M) = g (classOf M)) : f = g := by
  have hcomp : f.comp (exactRelations X).mkQ = g.comp (exactRelations X).mkQ := by
    apply Finsupp.lhom_ext
    intro M c
    rw [← Finsupp.smul_single_one M c, map_smul, map_smul]
    exact congrArg (c • ·) (h M)
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (exactRelations X) x
  exact LinearMap.congr_fun hcomp y

theorem grothendieck_pairing : Specs.grothendieckPairing.{u,v,w} := by
  intro R _ _ X Y _ _ hXY
  have hMN (M : SupportedModule.{u,v} X) (N : SupportedModule.{u,w} Y) :
      Module.support R M.obj ∩ Module.support R N.obj ⊆ {IsLocalRing.closedPoint R} :=
    (Set.inter_subset_inter M.support_subset N.support_subset).trans hXY
  let right (M : SupportedModule.{u,v} X) : GrothendieckGroup.{u,w} Y →ₗ[ℤ] ℤ :=
    liftToGrothendieck (fun N => intersectionEuler M.obj N.obj) fun A N C f g hf he hg =>
      intersectionEuler_add_right A.obj N.obj C.obj M.obj f g hf he hg
        (hMN M A) (hMN M N) (hMN M C)
  have hr (M : SupportedModule.{u,v} X) (N : SupportedModule.{u,w} Y) :
      right M (classOf N) = intersectionEuler M.obj N.obj :=
    liftToGrothendieck_classOf _ _ N
  let pairing : GrothendieckGroup.{u,v} X →ₗ[ℤ] GrothendieckGroup.{u,w} Y →ₗ[ℤ] ℤ :=
    liftToGrothendieck right fun A M C f g hf he hg => by
      apply grothendieck_hom_ext
      intro N
      change right M (classOf N) = right A (classOf N) + right C (classOf N)
      simp only [hr]
      exact intersectionEuler_add_left A.obj M.obj C.obj N.obj f g hf he hg
        (hMN A N) (hMN M N) (hMN C N)
  have hp (M : SupportedModule.{u,v} X) (N : SupportedModule.{u,w} Y) :
      pairing (classOf M) (classOf N) = intersectionEuler M.obj N.obj :=
    (congrArg (fun f : GrothendieckGroup.{u,w} Y →ₗ[ℤ] ℤ => f (classOf N))
      (liftToGrothendieck_classOf _ _ M)).trans (hr M N)
  exact ⟨pairing, hp, fun other ho =>
    grothendieck_hom_ext fun M => grothendieck_hom_ext fun N => (ho M N).trans (hp M N).symm⟩

end Grothendieck

end CommutativeAlgebraNotes.Intersection.PrimeQuotientReduction
