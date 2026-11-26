import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.FrameParameters
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.LowerRankHermitianModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.PeirceFrames
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! Faithfully flat forms of the split Hermitian quadratic Jordan algebras. -/

namespace LinearAlgebraicGroups.Albert

open _root_.Specs.LinearAlgebraicGroups.Albert (iteratedTensorEquiv towerAlgebra QuadraticOperatorLaw)
open _root_.LinearAlgebraicGroups.Composition
open HermitianSpecification CubicSpecification LowerRankSpecification
open QuadraticOperatorSpecification (applyOperator)
open TensorProduct

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

universe u v w

abbrev ParaQuadratic := SplitSpecification.ParaQuadratic
abbrev SplitRank := SplitSpecification.SplitRank
abbrev paraQuadraticBaseChange := @SplitSpecification.ParaQuadratic.baseChange
abbrev isSplitHermitianModel := @SplitSpecification.IsSplitModel
abbrev isSplitFreudenthal := @SplitSpecification.IsSplit
abbrev isFreudenthal := @SplitSpecification.IsFreudenthal
abbrev isAlbert := @SplitSpecification.IsAlbert
abbrev isReducedAlbertModel := @SplitSpecification.IsReducedModel

namespace SplitSpecification
namespace ParaQuadratic

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable (J : ParaQuadratic R M) (K : ParaQuadratic R N)

theorem groundOp_lift (x y : M) :
    J.op R (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] J.groundOp x y := by
  apply (TensorProduct.lid R M).injective
  simp [groundOp, LinearEquiv.conj_apply]

theorem natural_ground (S : Type u) [CommRing S] [Algebra R S] (x y : M) :
    J.op S (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] J.groundOp x y := by
  simpa only [groundOp_lift, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
    using (J.natural (Algebra.ofId R S) (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)).symm

theorem isIso_iff_ground (e : M ≃ₗ[R] N) : J.IsIso K e ↔ J.IsGroundIso K e := by
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun x y => (TensorProduct.lid R N).symm.injective ?_⟩
    simpa only [TensorProduct.lid_symm_apply, LinearMap.baseChange_tmul, groundOp_lift,
      LinearEquiv.coe_coe]
      using h R (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)
  · rintro ⟨hu, h⟩
    refine ⟨hu, ?_⟩
    intro S _ _ x y
    let E := e.baseChange R S M N
    let F := E.conj.toLinearMap.compQuadraticMap (J.op S)
    let G := (K.op S).comp E.toLinearMap
    have hFG : F = G := by
      let L := Module.End S (S ⊗[R] N)
      let hMod := Module.compHom L (algebraMap R S)
      have hTower := @IsScalarTower.of_algebraMap_smul R S L _ _ _ _ hMod.toSMul (fun _ _ => rfl)
      exact @baseChange_ext R S M L _ _ _ _ _ hMod _ hTower _ F G (by
        intro m
        apply LinearMap.ext
        intro z
        obtain ⟨y, rfl⟩ := E.surjective z
        change E (J.op S (1 ⊗ₜ[R] m) (E.symm (E y))) =
          K.op S (E (1 ⊗ₜ[R] m)) (E y)
        rw [LinearEquiv.symm_apply_apply]
        have he (a : S) (b : M) : E (a ⊗ₜ[R] b) = a ⊗ₜ[R] e b := rfl
        induction y using TensorProduct.inductionOn with
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b =>
          have ht : a • (1 ⊗ₜ[R] b : S ⊗[R] M) = a ⊗ₜ[R] b := by
            rw [smul_tmul', smul_eq_mul, mul_one]
          rw [← ht]
          simp only [map_smul, he, natural_ground, h]
      )
    have hval := congrArg (fun q => q x (E y)) hFG
    change E (J.op S x (E.symm (E y))) = K.op S (E x) (E y) at hval
    rw [E.symm_apply_apply] at hval
    exact hval

theorem isJordan_of_iso {e : M ≃ₗ[R] N} (h : J.IsIso K e) (hK : K.IsJordan) :
    J.IsJordan := by
  intro S _ _
  let E := e.baseChange R S M N
  have hop (x y : S ⊗[R] M) : E (J.op S x y) = K.op S (E x) (E y) := h.2 S x y
  have htr (x y z : S ⊗[R] M) :
      E (J.toQuadraticOperatorLaw.triple S x y z) =
        K.toQuadraticOperatorLaw.triple S (E x) (E y) (E z) := by
    simp only [Specs.LinearAlgebraicGroups.Albert.QuadraticOperatorLaw.triple,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, LinearMap.sub_apply, map_sub,
      hop, map_add]
  constructor
  · intro x y
    apply LinearMap.ext
    intro z
    apply E.injective
    simp only [Module.End.mul_apply, hop, (hK S).1]
  · intro x y z
    apply E.injective
    simp only [hop, htr, (hK S).2]

theorem ofJordan_isJordan (J : QuadraticJordan R M) : (ofJordan J).IsJordan :=
  fun S _ _ => ⟨J.fundamental S, J.commuting S⟩

def toJordan (h : J.IsJordan) : QuadraticJordan R M where
  toQuadraticOperatorLaw := J.toQuadraticOperatorLaw
  unit := J.unit
  op_unit := J.op_unit
  fundamental S _ _ := (h S).1
  commuting S _ _ := (h S).2

variable (S : Type u) [CommRing S] [aRS : Algebra R S]

private abbrev scalarTensorModule (M : Type v) [AddCommGroup M] [Module R M]
    (a : Algebra R S) : Type (max u v) :=
  letI := a
  S ⊗[R] M

private instance scalarTensorModule.module (M : Type v) [AddCommGroup M] [Module R M]
    (a : Algebra R S) : Module S (scalarTensorModule S M a) :=
  letI := a
  inferInstanceAs (Module S (S ⊗[R] M))

private def scalarTensor (a : Algebra R S) (s : S) (m : M) : scalarTensorModule S M a :=
  letI := a
  s ⊗ₜ[R] m

private theorem compare_lid
    (x y : scalarTensorModule S M aRS)
    (z : S ⊗[S] scalarTensorModule S M aRS)
    (a : Algebra R S) (ha : a = aRS)
    (e : (S ⊗[S] scalarTensorModule S M aRS) ≃ₗ[S] scalarTensorModule S M a)
    (he : ∀ (t s : S) (m : M),
      e (t ⊗ₜ[S] scalarTensor S aRS s m) = scalarTensor S a (s * t) m)
    (hz : e z = @QuadraticOperatorLaw.op R _ M _ _ J.toQuadraticOperatorLaw S _ a
      (e (1 ⊗ₜ[S] x)) (e (1 ⊗ₜ[S] y))) :
    TensorProduct.lid S _ z = @QuadraticOperatorLaw.op R _ M _ _ J.toQuadraticOperatorLaw S _ aRS x y := by
  subst a
  have hd : e = TensorProduct.lid S _ := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul t z =>
      induction z using TensorProduct.inductionOn with
      | tmul s m =>
        change e (t ⊗ₜ[S] (s ⊗ₜ[R] m)) = TensorProduct.lid S _ (t ⊗ₜ[S] (s ⊗ₜ[R] m))
        rw [show e (t ⊗ₜ[S] (s ⊗ₜ[R] m)) = (s * t) ⊗ₜ[R] m from he t s m,
          TensorProduct.lid_tmul, smul_tmul', smul_eq_mul, mul_comm]
      | add z q hz hq => simp only [tmul_add, map_add, hz, hq]
    | add z q hz hq => simp only [map_add, hz, hq]
  rw [hd] at hz
  simpa only [TensorProduct.lid_tmul, one_smul] using hz

private theorem iteratedTensorEquiv_on_tmul (T : Type u) [CommRing T] [Algebra S T]
    (t : T) (s : S) (m : M) :
    letI := towerAlgebra R S T
    iteratedTensorEquiv (R := R) (S := S) (M := M) T (t ⊗ₜ[S] (s ⊗ₜ[R] m)) =
      (algebraMap S T s * t) ⊗ₜ[R] m := by
  letI := towerAlgebra R S T
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  simpa only [Algebra.smul_def] using AlgebraTensorModule.cancelBaseChange_tmul R S T t m s

theorem groundOp_baseChange (x y : S ⊗[R] M) :
    (J.baseChange S).groundOp x y = J.op S x y := by
  change TensorProduct.lid S _ (J.extendedOp S S (1 ⊗ₜ[S] x) (1 ⊗ₜ[S] y)) = _
  have ha : towerAlgebra R S S = aRS := by
    apply Algebra.algebra_ext
    intro r
    change (algebraMap S S) (algebraMap R S r) = algebraMap R S r
    rw [Algebra.algebraMap_self]
    rfl
  refine J.compare_lid S x y _ (towerAlgebra R S S) ha
    (iteratedTensorEquiv (R := R) (S := S) (M := M) S) ?_ ?_
  · intro t s m
    exact iteratedTensorEquiv_on_tmul (R := R) S S t s m
  · exact J.extendedOp_apply S S _ _

theorem isSplitModel_baseChange_iff (i : SplitRank) :
    IsSplitModel (J.baseChange S) i ↔ OnComponent J S i := by
  simp only [IsSplitModel, OnComponent, groundOp_baseChange]
  rfl

theorem jordanAt_of_baseChange (T : Type u) [CommRing T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (h : (J.baseChange S).JordanAt T) : J.JordanAt T := by
  have ha : towerAlgebra R S T = ‹Algebra R T› :=
    Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply R S T r).symm)
  change @JordanAt _ _ _ _ _ J T _ _
  rw [← show @JordanAt _ _ _ _ _ J T _ (towerAlgebra R S T) = J.JordanAt T from
    congrArg (@JordanAt _ _ _ _ _ J T _) ha]
  letI := towerAlgebra R S T
  let E := iteratedTensorEquiv (R := R) (S := S) (M := M) T
  let JS := J.baseChange S
  have hop (x y : T ⊗[S] (S ⊗[R] M)) :
      E (JS.op T x y) = J.op T (E x) (E y) :=
    J.extendedOp_apply S T x y
  have htr (x y z : T ⊗[S] (S ⊗[R] M)) :
      E (JS.toQuadraticOperatorLaw.triple T x y z) =
        J.toQuadraticOperatorLaw.triple T (E x) (E y) (E z) := by
    simp only [Specs.LinearAlgebraicGroups.Albert.QuadraticOperatorLaw.triple,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, LinearMap.sub_apply, map_sub,
      hop, map_add]
  constructor
  · intro x y
    apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ := E.surjective x
    obtain ⟨b, rfl⟩ := E.surjective y
    obtain ⟨c, rfl⟩ := E.surjective z
    have hf : JS.op T (JS.op T a b) = JS.op T a * JS.op T b * JS.op T a := h.1 a b
    have ev := congrArg (fun g : Module.End T (T ⊗[S] (S ⊗[R] M)) => E (g c)) hf
    simpa only [Module.End.mul_apply, hop] using ev
  · intro x y z
    obtain ⟨a, rfl⟩ := E.surjective x
    obtain ⟨b, rfl⟩ := E.surjective y
    obtain ⟨c, rfl⟩ := E.surjective z
    have hc : JS.op T a (JS.toQuadraticOperatorLaw.triple T b a c) =
      JS.toQuadraticOperatorLaw.triple T (JS.op T a b) c a := h.2 a b c
    simpa only [hop, htr] using congrArg E hc

private theorem jordanAt_of_jointly_injective {I : Type*} (B : I → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (f : ∀ i, S →ₐ[R] B i) (h : ∀ i, J.JordanAt (B i))
    (hinj : Function.Injective (fun x : S ⊗[R] M => fun i => (f i).toLinearMap.rTensor M x)) :
    J.JordanAt S := by
  have hop (i) (x y : S ⊗[R] M) := J.natural (f i) x y
  have htr (i) (x y z : S ⊗[R] M) :
      (f i).toLinearMap.rTensor M (J.toQuadraticOperatorLaw.triple S x y z) =
        J.toQuadraticOperatorLaw.triple (B i) ((f i).toLinearMap.rTensor M x)
          ((f i).toLinearMap.rTensor M y) ((f i).toLinearMap.rTensor M z) := by
    simp only [Specs.LinearAlgebraicGroups.Albert.QuadraticOperatorLaw.triple,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, LinearMap.sub_apply, map_sub,
      hop, map_add]
  constructor
  · intro x y
    apply LinearMap.ext
    intro z
    apply hinj (funext fun i => ?_)
    simp only [Module.End.mul_apply, hop, (h i).1]
  · intro x y z
    apply hinj (funext fun i => ?_)
    simp only [hop, htr, (h i).2]

private theorem jointly_injective_product {I : Type*} [Fintype I] [DecidableEq I]
    (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (f : ∀ i, S →ₐ[R] B i)
    (e : S ≃ₗ[R] (∀ i, B i)) (he : ∀ s i, e s i = f i s) :
    Function.Injective (fun x : S ⊗[R] M => fun i => (f i).toLinearMap.rTensor M x) := by
  let E := (TensorProduct.congr e (LinearEquiv.refl R M)).trans (TensorProduct.piLeft R M B)
  have ht (x : S ⊗[R] M) : E x = fun i => (f i).toLinearMap.rTensor M x := by
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
      funext i
      simp [E, he, TensorProduct.piRightHom_tmul]
    | add x y hx hy => simp [map_add, hx, hy, Pi.add_def]
  intro x y eq
  exact E.injective ((ht x).trans (eq.trans (ht y).symm))

end ParaQuadratic

theorem split_model_exists (R : Type u) [CommRing R] (i : SplitRank) :
    ∃ J : QuadraticJordan R (i.Model R), J.unit = cubicUnit ∧
      ∀ x y, J.groundOp x y = applyOperator (i.norm R) (untwisted R) x y := by
  obtain ⟨hs, hp, hq, ho⟩ := LowerRank.restricted_models R
  cases i
  · obtain ⟨J, hu, hop, _⟩ := hs
    exact ⟨J, hu, hop⟩
  · obtain ⟨J, hu, hop, _⟩ := hp
    exact ⟨J, hu, hop⟩
  · obtain ⟨J, hu, hop, _⟩ := hq
    exact ⟨J, hu, hop⟩
  · obtain ⟨J, hu, hop, _⟩ := ho
    exact ⟨J, hu, hop⟩

theorem split_model_rank (R : Type u) [CommRing R] (i : SplitRank) :
    Module.Finite R (i.Model R) ∧ Module.Free R (i.Model R) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (i.Model R) p = i.hermitianRank := by
  have facts {C : Type u} [NonAssocRing C] [Module R C]
      {n : QuadraticForm R C} {r} (h : matrixModel n r) :
      Module.Finite R (Coordinates R C) ∧ Module.Free R (Coordinates R C) ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (Coordinates R C) p = r := by
    obtain ⟨e, _, hf, hb, hr⟩ := h
    letI := hf
    letI := hb
    exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm,
      fun p => (congrFun (Module.rankAtStalk_eq_of_equiv e) p).trans (hr p)⟩
  obtain ⟨hs, hp, hq, ho⟩ := LowerRank.matrix_models R
  cases i
  · exact facts hs
  · exact facts hp
  · exact facts hq
  · exact facts ho

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable (J : ParaQuadratic R M)

theorem isSplitModel_iff_iso (i : SplitRank) :
    IsSplitModel J i ↔ ∃ K : QuadraticJordan R (i.Model R),
      K.unit = cubicUnit ∧
      (∀ x y, K.groundOp x y = applyOperator (i.norm R) (untwisted R) x y) ∧
      ∃ e : M ≃ₗ[R] i.Model R, J.IsIso (ParaQuadratic.ofJordan K) e := by
  constructor
  · rintro ⟨e, hu, hop⟩
    obtain ⟨K, hku, hkop⟩ := split_model_exists R i
    refine ⟨K, hku, hkop, e, (J.isIso_iff_ground _ e).2 ?_⟩
    exact ⟨hu.trans hku.symm, fun x y => (hop x y).trans (hkop _ _).symm⟩
  · rintro ⟨K, hu, hop, e, h⟩
    have hg := (J.isIso_iff_ground (ParaQuadratic.ofJordan K) e).1 h
    exact ⟨e, hg.1.trans hu, fun x y => (hg.2 x y).trans (hop _ _)⟩

theorem jordan_of_split_model {i : SplitRank} (hs : IsSplitModel J i) : J.IsJordan := by
  obtain ⟨K, _, _, e, h⟩ := (isSplitModel_iff_iso J i).1 hs
  exact J.isJordan_of_iso (ParaQuadratic.ofJordan K) h (ParaQuadratic.ofJordan_isJordan K)

section Descent

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem jordan_of_faithfully_flat (S : Type u) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (h : (J.baseChange S).IsJordan) : J.IsJordan := by
  intro T _ _
  let D := S ⊗[R] T
  let f : T →ₐ[R] D := Algebra.TensorProduct.includeRight
  have hD : Module.FaithfullyFlat T D :=
    Module.FaithfullyFlat.of_linearEquiv T (T ⊗[R] S)
      (Algebra.TensorProduct.commRight R T S).toLinearEquiv.symm
  apply J.jordanAt_of_jointly_injective T (fun _ : Unit => D) (fun _ => f)
    (fun _ => J.jordanAt_of_baseChange S D (h D))
  let e := AlgebraTensorModule.cancelBaseChange R T D D M
  have hi := Module.FaithfullyFlat.tensorProduct_mk_injective (A := T) (B := D) (T ⊗[R] M)
  have hn (x : T ⊗[R] M) : e (1 ⊗ₜ[T] x) = f.toLinearMap.rTensor M x := by
    induction x using TensorProduct.inductionOn with
    | tmul t m =>
      simp [e, AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def]
      rfl
    | add x y hx hy => simp [tmul_add, map_add, hx, hy]
  intro x y eq
  exact hi (e.injective ((hn x).trans ((congrFun eq ()).trans (hn y).symm)))

variable {B : SplitRank → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

private def componentProductEquiv
    (hb : Function.Bijective (algebraMap R (∀ i, B i))) (T : Type*) [AddCommGroup T] [Module R T] :
    T ≃ₗ[R] (∀ i, B i ⊗[R] T) :=
  (TensorProduct.lid R T).symm.trans <|
    (TensorProduct.congr (AlgEquiv.ofBijective (Algebra.ofId R (∀ i, B i)) hb).toLinearEquiv
      (LinearEquiv.refl R T)).trans (TensorProduct.piLeft R T B)

private theorem componentProductEquiv_apply
    (hb : Function.Bijective (algebraMap R (∀ i, B i))) {T : Type*} [AddCommGroup T] [Module R T]
    (t : T) (i : SplitRank) : componentProductEquiv hb T t i = 1 ⊗ₜ[R] t := by
  simp [componentProductEquiv, TensorProduct.piRightHom_tmul]

theorem jordan_of_split (h : IsSplit J) : J.IsJordan := by
  rcases h with ⟨i, h⟩ | ⟨B, _, _, hb, hm⟩
  · exact jordan_of_split_model J h
  intro T _ _
  let f (i : SplitRank) : T →ₐ[R] B i ⊗[R] T := Algebra.TensorProduct.includeRight
  apply J.jordanAt_of_jointly_injective T (fun i => B i ⊗[R] T) f
  · intro i
    apply J.jordanAt_of_baseChange (B i)
    exact jordan_of_split_model _ ((J.isSplitModel_baseChange_iff _ _).2 (hm i)) _
  · apply ParaQuadratic.jointly_injective_product (M := M) T _ f (componentProductEquiv hb T)
    exact componentProductEquiv_apply hb

theorem freudenthal_is_jordan (h : IsFreudenthal J) : J.IsJordan := by
  obtain ⟨S, _, _, hf, hs⟩ := h
  exact jordan_of_faithfully_flat J S (jordan_of_split _ hs)

private theorem projective_of_split (h : IsSplit J) : Module.Finite R M ∧ Module.Projective R M := by
  rcases h with ⟨i, h⟩ | ⟨B, _, _, hb, hm⟩
  · obtain ⟨e, _, _⟩ := h
    obtain ⟨hfin, hfree, _⟩ := split_model_rank R i
    letI := hfin
    letI := hfree
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
  let e := (AlgEquiv.ofBijective (Algebra.ofId R (∀ i, B i)) hb).toLinearEquiv
  letI : Module.Finite R (∀ i, B i) := Module.Finite.equiv e
  letI : Module.Projective R (∀ i, B i) := Module.Projective.of_equiv' e
  have componentFinite (i : SplitRank) : Module.Finite R (B i) :=
    Module.Finite.of_surjective (LinearMap.proj i) (Function.surjective_eval i)
  have componentProjective (i : SplitRank) : Module.Projective R (B i) :=
    Module.Projective.of_split (LinearMap.single R B i) (LinearMap.proj i)
      (LinearMap.proj_comp_single_same R B i)
  have componentFree (i : SplitRank) : Module.Free (B i) (B i ⊗[R] M) ∧
      Module.Finite (B i) (B i ⊗[R] M) := by
    obtain ⟨g, _, _⟩ := hm i
    obtain ⟨hf, he, _⟩ := split_model_rank (B i) i
    letI := hf
    letI := he
    exact ⟨Module.Free.of_equiv g.symm, Module.Finite.equiv g.symm⟩
  have (i : SplitRank) : Module.Finite R (B i ⊗[R] M) :=
    letI := componentFinite i
    letI := (componentFree i).2
    Module.Finite.trans (B i) (B i ⊗[R] M)
  have (i : SplitRank) : Module.Projective R (B i ⊗[R] M) := by
    letI := componentProjective i
    letI := (componentFree i).1
    let b := Module.Free.chooseBasis (B i) (B i ⊗[R] M)
    let g := (b.repr.restrictScalars R).trans (finsuppLEquivDirectSum R (B i) _)
    exact Module.Projective.of_equiv' g.symm
  let F := componentProductEquiv hb M
  let g := DirectSum.linearEquivFunOnFintype R SplitRank (fun i => B i ⊗[R] M)
  exact ⟨Module.Finite.equiv F.symm, Module.Projective.of_equiv' (g.trans F.symm)⟩

private theorem finitePresentation_of_faithfully_flat (S : Type u) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := by
  haveI : Module.Finite R M := .of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  apply Module.finitePresentation_of_surjective f hf
  have hfs : Function.Surjective (f.baseChange S) := LinearMap.lTensor_surjective S hf
  have hker := Module.FinitePresentation.fg_ker (f.baseChange S) hfs
  let g := (LinearMap.ker f).subtype.baseChange S
  have hg : Function.Injective g := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (LinearMap.ker f).subtype (Submodule.subtype_injective (LinearMap.ker f))
  have hex : Function.Exact g (f.baseChange S) :=
    lTensor_exact S f.exact_subtype_ker_map hf
  have equiv : S ⊗[R] (LinearMap.ker f) ≃ₗ[S] LinearMap.ker (f.baseChange S) :=
    LinearEquiv.ofInjective g hg ≪≫ₗ LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp hex).symm
  haveI : Module.Finite S ↥(LinearMap.ker (f.baseChange S)) := .of_fg hker
  haveI : Module.Finite S (S ⊗[R] ↥(LinearMap.ker f)) := .equiv equiv.symm
  exact Module.Finite.iff_fg.mp (.of_finite_tensorProduct_of_faithfullyFlat S)

theorem freudenthal_finite_projective (h : IsFreudenthal J) :
    Module.Finite R M ∧ Module.Projective R M := by
  obtain ⟨S, _, _, hf, hs⟩ := h
  obtain ⟨hfinite, hproj⟩ := projective_of_split _ hs
  haveI : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
  haveI := Module.finitePresentation_of_projective S (S ⊗[R] M)
  haveI : Module.FinitePresentation R M := finitePresentation_of_faithfully_flat (R := R) (M := M) S
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end Descent

section Ranks

theorem split_component_rank {B : Type u} [CommRing B] [Algebra R B] {i : SplitRank}
    [Module.Finite R M] [Module.Flat R M] (h : OnComponent J B i) (p : PrimeSpectrum B) :
    Module.rankAtStalk M (p.comap (algebraMap R B)) = i.hermitianRank := by
  obtain ⟨e, _, _⟩ := h
  rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv e]
  exact (split_model_rank B i).2.2 p

private theorem exists_component_prime {B : SplitRank → Type u}
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (hb : Function.Bijective (algebraMap R (∀ i, B i))) (p : PrimeSpectrum R) :
    ∃ (i : SplitRank) (q : PrimeSpectrum (B i)), q.comap (algebraMap R (B i)) = p := by
  let e := AlgEquiv.ofBijective (Algebra.ofId R (∀ i, B i)) hb
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq (p.comap e.symm.toRingHom)
  refine ⟨i, q, ?_⟩
  change q.comap ((Pi.evalRingHom B i).comp e.toRingHom) = p
  rw [PrimeSpectrum.comap_comp_apply, hq, ← PrimeSpectrum.comap_comp_apply]
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := RingHom.ext fun r => e.symm_apply_apply r
  rw [he, PrimeSpectrum.comap_id]

theorem split_rank_locus {B : SplitRank → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (hb : Function.Bijective (algebraMap R (∀ i, B i))) (hm : ∀ i, OnComponent J (B i) i)
    (i : SplitRank) :
    Set.range (PrimeSpectrum.comap (algebraMap R (B i))) =
      {p | Module.rankAtStalk M p = i.hermitianRank} ∧
      IsClopen {p : PrimeSpectrum R | Module.rankAtStalk M p = i.hermitianRank} := by
  obtain ⟨hf, hp⟩ := projective_of_split J (Or.inr ⟨B, inferInstance, inferInstance, hb, hm⟩)
  letI := hf
  letI := hp
  letI := Module.finitePresentation_of_projective R M
  refine ⟨?_, Module.isLocallyConstant_rankAtStalk.isClopen_fiber _⟩
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact split_component_rank J (hm i) q
  · intro hr
    obtain ⟨j, q, hq⟩ := exists_component_prime hb p
    have hj := split_component_rank J (hm j) q
    rw [hq] at hj
    have h := hj.symm.trans hr
    have hi : j = i := by cases i <;> cases j <;> simp_all [SplitRank.hermitianRank]
    subst j
    exact ⟨q, hq⟩

theorem freudenthal_rank (h : IsFreudenthal J) :
    IsLocallyConstant (Module.rankAtStalk (R := R) M) ∧
      ∀ p : PrimeSpectrum R, ∃ i : SplitRank, Module.rankAtStalk M p = i.hermitianRank := by
  obtain ⟨hf, hp⟩ := freudenthal_finite_projective J h
  letI := hf
  letI := hp
  letI := Module.finitePresentation_of_projective R M
  refine ⟨Module.isLocallyConstant_rankAtStalk, ?_⟩
  obtain ⟨S, _, _, hff, hs⟩ := h
  intro p
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) p
  rw [← hq, ← Module.rankAtStalk_baseChange]
  rcases hs with ⟨i, hm⟩ | ⟨B, _, _, hb, hm⟩
  · obtain ⟨e, _, _⟩ := hm
    rw [Module.rankAtStalk_eq_of_equiv e]
    exact ⟨i, (split_model_rank S i).2.2 q⟩
  · obtain ⟨i, q', hq'⟩ := exists_component_prime hb q
    rw [← hq']
    exact ⟨i, split_component_rank (J.baseChange S) (hm i) q'⟩

private theorem subsingleton_module (B : Type u) [CommRing B] [Subsingleton B]
    (L : Type w) [AddCommGroup L] [Module B L] : Subsingleton L :=
  ⟨fun x y => by rw [← one_smul B x, ← one_smul B y, Subsingleton.elim (1 : B) 0,
    zero_smul, zero_smul]⟩

private theorem trivial_component (B : Type u) [CommRing B] [Subsingleton B] [Algebra R B]
    (i : SplitRank) : OnComponent J B i := by
  letI : Subsingleton (B ⊗[R] M) := subsingleton_module B _
  letI : Subsingleton (i.Model B) := subsingleton_module B _
  exact ⟨LinearEquiv.ofSubsingleton _ _, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩

theorem isSplit_of_model {i : SplitRank} (hm : IsSplitModel J i) : IsSplit J :=
  Or.inl ⟨i, hm⟩

private theorem rank_eq_27 {i : SplitRank} (h : i.hermitianRank = 27) : i = .octonion := by
  cases i <;> simp_all [SplitRank.hermitianRank]

theorem albert_iff_split_octonion_after_cover :
    IsAlbert J ↔ ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.FaithfullyFlat R S ∧ OnComponent J S .octonion := by
  constructor
  · intro h
    obtain ⟨hFin, hProj⟩ := freudenthal_finite_projective J h.1
    letI := hFin
    letI := hProj
    obtain ⟨S, _, _, hff, hs⟩ := h.1
    rcases hs with ⟨i, hm⟩ | ⟨B, _, _, hb, hm⟩
    · refine ⟨S, inferInstance, inferInstance, hff, ?_⟩
      have hc := (J.isSplitModel_baseChange_iff S i).1 hm
      by_cases hi : i = .octonion
      · simpa only [hi] using hc
      · haveI : Subsingleton S :=
          PrimeSpectrum.isEmpty_iff_subsingleton.mp ⟨fun q => hi (rank_eq_27 <|
            (split_component_rank J hc q).symm.trans (h.2 _))⟩
        exact trivial_component J S .octonion
    have hr (i : SplitRank) (q : PrimeSpectrum (B i)) : i.hermitianRank = 27 := by
      rw [← split_component_rank (J.baseChange S) (hm i) q, Module.rankAtStalk_baseChange, h.2]
    have htrivial (i : SplitRank) (hi : i ≠ .octonion) : Subsingleton (B i) := by
      refine PrimeSpectrum.isEmpty_iff_subsingleton.mp ⟨fun q => hi (rank_eq_27 (hr i q))⟩
    let D := B SplitRank.octonion
    have he : Function.Bijective (algebraMap S D) := by
      refine ⟨fun x y hxy => hb.1 (funext fun i => ?_), fun y => ?_⟩
      · by_cases hi : i = .octonion
        · subst i; exact hxy
        · letI := htrivial i hi
          exact Subsingleton.elim _ _
      · obtain ⟨x, hx⟩ := hb.2 (Pi.single SplitRank.octonion y)
        exact ⟨x, by simpa using congrFun hx SplitRank.octonion⟩
    let de := (AlgEquiv.ofBijective (Algebra.ofId S D) he).toLinearEquiv
    haveI : Module.FaithfullyFlat S D := Module.FaithfullyFlat.of_linearEquiv S S de.symm
    letI : Algebra R D := towerAlgebra R S D
    letI : IsScalarTower R S D := IsScalarTower.of_algebraMap_eq' rfl
    refine ⟨D, inferInstance, inferInstance, Module.FaithfullyFlat.trans R S D, ?_⟩
    obtain ⟨e, hu, hop⟩ := hm .octonion
    let E := iteratedTensorEquiv (R := R) (S := S) (M := M) D
    refine ⟨E.symm.trans e, ?_, ?_⟩
    · apply Eq.trans _ hu
      change e (E.symm (1 ⊗ₜ[R] J.unit)) = e (1 ⊗ₜ[S] (1 ⊗ₜ[R] J.unit))
      apply congrArg e
      apply E.injective
      simp [E, AlgebraTensorModule.cancelBaseChange_tmul]
    · intro x y
      have hx := J.extendedOp_apply S D (E.symm x) (E.symm y)
      change e (E.symm (J.op D x y)) =
        applyOperator (SplitRank.norm D .octonion) (untwisted D) (e (E.symm x)) (e (E.symm y))
      rw [← hop]
      congr 1
      apply E.injective
      change E (E.symm (J.op D x y)) = E (J.extendedOp S D (E.symm x) (E.symm y))
      rw [E.apply_symm_apply]
      change E (J.extendedOp S D (E.symm x) (E.symm y)) =
        J.op D (E (E.symm x)) (E (E.symm y)) at hx
      simpa only [E.apply_symm_apply] using hx.symm
  · rintro ⟨S, _, _, hf, hm⟩
    have hF : IsFreudenthal J :=
      ⟨S, inferInstance, inferInstance, hf, isSplit_of_model _ ((J.isSplitModel_baseChange_iff _ _).2 hm)⟩
    obtain ⟨hFin, hProj⟩ := freudenthal_finite_projective J hF
    letI := hFin
    letI := hProj
    refine ⟨hF, fun p => ?_⟩
    obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) p
    exact split_component_rank J hm q

end Ranks

section ReducedModels

open Polynomial

theorem unit_square_root_extension (R : Type u) [CommRing R] (a : Rˣ) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.FaithfullyFlat R S ∧ Nonempty (Module.Basis (Fin 2) R S) ∧
        ∃ b : Sˣ, b ^ 2 = Units.map (algebraMap R S) a := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    letI := h
    refine ⟨R, inferInstance, inferInstance, inferInstance, ⟨?_⟩, 1, Subsingleton.elim _ _⟩
    exact Module.Basis.ofEquivFun (LinearEquiv.ofSubsingleton R (Fin 2 → R))
  | inr h =>
    letI := h
    let p : R[X] := X ^ 2 - C (a : R)
    have hp : p.Monic := monic_X_pow_sub_C _ (by decide)
    have hd : p.natDegree = 2 := natDegree_X_pow_sub_C
    have hpos : 0 < p.degree := by rw [Polynomial.degree_eq_natDegree hp.ne_zero, hd]; decide
    let D := AdjoinRoot p
    letI : Nontrivial D := (AdjoinRoot.nontrivial_iff_of_monic hp).mpr hpos
    letI : Module.Free R D := hp.free_adjoinRoot
    have hr : (AdjoinRoot.root p) ^ 2 = algebraMap R D (a : R) := by
      change (AdjoinRoot.root p) ^ 2 = AdjoinRoot.of p (a : R)
      apply sub_eq_zero.mp
      simpa only [p, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] using AdjoinRoot.eval₂_root p
    have hb : IsUnit (AdjoinRoot.root p) :=
      (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp (by rw [hr]; exact (Units.map (algebraMap R D).toMonoidHom a).isUnit)
    refine ⟨D, inferInstance, inferInstance, inferInstance,
      ⟨(AdjoinRoot.powerBasisAux' hp).reindex (finCongr hd)⟩, hb.unit, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    exact hr

private theorem simultaneous_unit_square_roots (R : Type u) [CommRing R] {k : ℕ}
    (a : Fin k → Rˣ) : ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
    Module.FaithfullyFlat R S ∧ ∃ b : Fin k → Sˣ,
      ∀ i, b i ^ 2 = Units.map (algebraMap R S) (a i) := by
  induction k generalizing R with
  | zero =>
    exact ⟨R, inferInstance, inferInstance, inferInstance, Fin.elim0, fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨B, _, _, hb, _, b₀, hb₀⟩ := unit_square_root_extension R (a 0)
    obtain ⟨D, _, _, hd, b, h⟩ := ih B (fun i => Units.map (algebraMap R B) (a i.succ))
    letI := towerAlgebra R B D
    letI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' rfl
    refine ⟨D, inferInstance, inferInstance, Module.FaithfullyFlat.trans R B D,
      Fin.cons (Units.map (algebraMap B D) b₀) b, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero, ← map_pow, hb₀]
      rfl
    · exact h j

open Composition.Specification (OctonionNormConditions)
open Composition.PeirceSpecification (ZornIsomorphism)

private def zorn_isomorphism_extend {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    {A : Type v} [NonAssocRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [Module.Projective R A] {n : QuadraticForm R A}
    (F : ZornIsomorphism (normBaseChange S n)) : ZornIsomorphism (normBaseChange T n) := by
  letI : NonAssocRing (S ⊗[R] A) := inferInstance
  letI : NonAssocRing (T ⊗[S] (S ⊗[R] A)) := inferInstance
  let e := F.toLinearEquiv.baseChange S T (Zorn S) (S ⊗[R] A)
  let c := AlgebraTensorModule.cancelBaseChange R S T T A
  have h1 : e 1 = 1 := by
    change e (1 ⊗ₜ[S] 1) = 1 ⊗ₜ[S] 1
    simpa [e, LinearEquiv.baseChange_tmul] using congrArg (fun a : S ⊗[R] A => (1 : T) ⊗ₜ[S] a) F.map_one
  have hm (x y : T ⊗[S] Zorn S) : e (x * y) = e x * e y := by
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => rw [add_mul, map_add, map_add, add_mul, hx, hz]
    | tmul t x =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => rw [mul_add, map_add, map_add, mul_add, hy, hz]
      | tmul s y => simp [e, Algebra.TensorProduct.tmul_mul_tmul, LinearEquiv.baseChange_tmul, F.map_mul]
  have hc1 : c 1 = 1 := by
    change c (1 ⊗ₜ[S] (1 ⊗ₜ[R] (1 : A))) = 1 ⊗ₜ[R] 1
    simp [c, AlgebraTensorModule.cancelBaseChange_tmul]
  have hcm (x y : T ⊗[S] (S ⊗[R] A)) : c (x * y) = c x * c y := by
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => rw [add_mul, map_add, map_add, add_mul, hx, hz]
    | tmul t x =>
      induction x using TensorProduct.inductionOn with
      | add x z hx hz => rw [tmul_add, add_mul, map_add, map_add, add_mul, hx, hz]
      | tmul a x =>
        induction y using TensorProduct.inductionOn with
        | add y z hy hz => rw [mul_add, map_add, map_add, mul_add, hy, hz]
        | tmul s y =>
          induction y using TensorProduct.inductionOn with
          | add y z hy hz => rw [tmul_add, mul_add, map_add, map_add, mul_add, hy, hz]
          | tmul b y =>
            simp [c, AlgebraTensorModule.cancelBaseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
              Algebra.smul_def]
            congr 1
            ring
  have hn : (normBaseChange T n).comp (e.trans c).toLinearMap =
      normBaseChange T (Zorn.norm S) := by
    apply baseChange_ext
    intro x
    change normBaseChange T n (c (e (1 ⊗ₜ[S] x))) =
      normBaseChange T (Zorn.norm S) (1 ⊗ₜ[S] x)
    rw [show e (1 ⊗ₜ[S] x) = 1 ⊗ₜ[S] F.toLinearEquiv x from rfl]
    have nat (y : S ⊗[R] A) :
        normBaseChange T n (c (1 ⊗ₜ[S] y)) =
          algebraMap S T (normBaseChange S n y) := by
      let f := IsScalarTower.toAlgHom R S T
      have heq : c (1 ⊗ₜ[S] y) = f.toLinearMap.rTensor A y := by
        induction y using TensorProduct.inductionOn with
        | tmul s z =>
          simp [c, AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, f]
        | add x y hx hy => simp [tmul_add, map_add, hx, hy]
      rw [heq]
      exact Composition.Peirce.norm_tensorMap n f y
    rw [nat, F.map_norm]
    simp
  let H := Zorn.baseChange S T
  refine ⟨H.symm.trans (e.trans c), ?_, ?_, ?_⟩
  · have hh : H.symm 1 = 1 := H.symm_apply_eq.mpr (Zorn.baseChange_one (R := S) (S := T)).symm
    change c (e (H.symm 1)) = 1
    rw [hh, h1, hc1]
  · intro x y
    have hh : H.symm (x * y) = H.symm x * H.symm y := by
      apply H.injective
      rw [H.apply_symm_apply, Zorn.baseChange_mul, H.apply_symm_apply, H.apply_symm_apply]
    change c (e (H.symm (x * y))) = c (e (H.symm x)) * c (e (H.symm y))
    rw [hh, hm, hcm]
  · intro x
    have hn' := DFunLike.congr_fun hn (H.symm x)
    exact hn'.trans (by
      rw [Zorn.baseChange_norm, QuadraticMap.comp_apply]
      exact congrArg (Zorn.norm T) (H.apply_symm_apply x))

open Composition.AdjointSpecification (trace)

private def coordinateEquiv {B : Type u} [CommRing B] {A : Type v} {C : Type w} [NonAssocRing A]
    [NonAssocRing C] [Module B A] [Module B C] (f : A ≃ₗ[B] C) :
    Coordinates B A ≃ₗ[B] Coordinates B C :=
  (LinearEquiv.refl _ _).prodCongr (LinearEquiv.piCongrRight fun _ => f)

private theorem zorn_hermitian_transport {B : Type u} [CommRing B] {A : Type v} [NonAssocRing A]
    [Module B A] {n : QuadraticForm B A} (f : ZornIsomorphism n) (δ : Fin 3 → Bˣ) :
    let F := coordinateEquiv f.toLinearEquiv
    F cubicUnit = cubicUnit ∧
    ∀ x y, F (applyOperator (Zorn.norm B) δ x y) = applyOperator n δ (F x) (F y) := by
  let e := f.toLinearEquiv
  let F := coordinateEquiv e
  have d (x : Coordinates B (Zorn B)) (i : Fin 3) : (F x).1 i = x.1 i := rfl
  have b (x : Coordinates B (Zorn B)) (i : Fin 3) : (F x).2 i = e (x.2 i) := rfl
  have hnorm (x : Zorn B) : n (e x) = Zorn.norm B x := f.map_norm x
  have hmul (x y : Zorn B) : e (x * y) = e x * e y := f.map_mul x y
  have hOne : e 1 = 1 := f.map_one
  have hp (x y : Zorn B) :
      n.polarBilin (e x) (e y) = (Zorn.norm B).polarBilin x y := by
    change n (e x + e y) - n (e x) - n (e y) = _
    simp only [← map_add, hnorm]
    rfl
  have ht (x : Zorn B) : trace n (e x) = trace (Zorn.norm B) x := by
    change n.polarBilin (e x) 1 = _
    rw [← hOne, hp]
    rfl
  have hc (x : Zorn B) : e (conjugate (Zorn.norm B) x) = conjugate n (e x) := by
    change e (trace (Zorn.norm B) x • 1 - x) = trace n (e x) • 1 - e x
    simp only [map_sub, map_smul, ht, hOne]
  have hT (x y) : tracePairing n δ (F x) (F y) = tracePairing (Zorn.norm B) δ x y := by
    simp only [CubicSpecification.tracePairing, LinearMap.coe_mk, AddHom.coe_mk, d, b, hp]
  have ha (x) : F (cubicAdjoint (Zorn.norm B) δ x) = cubicAdjoint n δ (F x) := by
    apply Prod.ext
    · funext i
      simp only [CubicSpecification.cubicAdjoint, d, b, hnorm]
    · funext i
      simp only [CubicSpecification.cubicAdjoint, b, d, map_add, map_smul, hc, hmul]
  have hcross (x y) : F (adjointCross (Zorn.norm B) δ x y) = adjointCross n δ (F x) (F y) := by
    simp only [CubicSpecification.adjointCross, map_sub, ha, map_add]
  refine ⟨?_, fun x y => ?_⟩
  · exact Prod.ext rfl (funext fun _ => map_zero e)
  · change F (applyOperator (Zorn.norm B) δ x y) = applyOperator n δ (F x) (F y)
    simp only [applyOperator, map_sub, map_smul, hcross, ha, hT]

open private ground_operator from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators

private theorem zorn_remove_square_parameters (B : Type u) [CommRing B]
    (δ b : Fin 3 → Bˣ) (h : ∀ i, b i ^ 2 = δ i) :
    ∃ F : Coordinates B (Zorn B) ≃ₗ[B] Coordinates B (Zorn B),
      F cubicUnit = cubicUnit ∧ ∀ x y,
        F (applyOperator (Zorn.norm B) δ x y) =
          applyOperator (Zorn.norm B) (untwisted B) (F x) (F y) := by
  let s (i : Fin 3) := (b i)⁻¹
  have hδ : (fun i => s i ^ 2 * δ i) = untwisted B := by
    funext i
    change (b i)⁻¹ ^ 2 * δ i = 1
    rw [← h i, inv_pow]
    exact inv_mul_cancel _
  obtain ⟨F, hF, _⟩ := hermitian_square_scaling (Zorn.isOctonion B) δ s
  rw [hδ] at hF
  let H := hermitian_parameterHom δ (Zorn.isOctonion B) (untwisted B) F hF
  have h' : (ParaQuadratic.ofJordan (weightedHermitianJordan δ (Zorn.isOctonion B))).IsIso
      (ParaQuadratic.ofJordan (weightedHermitianJordan (untwisted B) (Zorn.isOctonion B))) F :=
    ⟨H.map_unit, H.map_op⟩
  have hg := (ParaQuadratic.isIso_iff_ground _ _ F).1 h'
  refine ⟨F, hF.1, fun x y => ?_⟩
  have hval := hg.2 x y
  change F ((weightedHermitianJordan δ (Zorn.isOctonion B)).groundOp x y) =
    (weightedHermitianJordan (untwisted B) (Zorn.isOctonion B)).groundOp (F x) (F y) at hval
  simpa only [ground_operator] using hval

variable {A : Type v} [NonAssocRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (hn : OctonionNormConditions n) (γ : Fin 3 → Rˣ)

theorem reduced_model_is_albert (K : ParaQuadratic R (Coordinates R A))
    (hK : IsReducedModel hn γ K) : IsAlbert K := by
  apply (albert_iff_split_octonion_after_cover K).2
  letI := hn.projective
  obtain ⟨S, _, _, _, hff, ⟨f⟩⟩ := Composition.Peirce.faithfully_flat_split hn
  obtain ⟨T, _, _, hft, b, hb⟩ := simultaneous_unit_square_roots S (baseChangedWeights S γ)
  letI := towerAlgebra R S T
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let q := normBaseChange T n
  let δ := baseChangedWeights T γ
  have hb' (i : Fin 3) : b i ^ 2 = δ i := by
    exact hb i
  let g := zorn_isomorphism_extend f (T := T)
  let G := coordinateEquiv g.toLinearEquiv
  obtain ⟨gu, gh⟩ := zorn_hermitian_transport g δ
  obtain ⟨F, hu, hF⟩ := zorn_remove_square_parameters T δ b hb'
  let e := coordinatesBaseChange (R := R) (A := A) T
  refine ⟨T, inferInstance, inferInstance, Module.FaithfullyFlat.trans R S T,
    (e.trans G.symm).trans F, ?_, ?_⟩
  · change F (G.symm (e (1 ⊗ₜ[R] K.unit))) = cubicUnit
    rw [hK.1]
    have he : e (1 ⊗ₜ[R] (cubicUnit : Coordinates R A)) = cubicUnit := by
      exact extendCoordinates_unit (R := R) (A := A) T
    rw [he, ← gu, G.symm_apply_apply, hu]
  · intro x y
    change F (G.symm (e (K.op T x y))) = _
    have hp := gh (G.symm (e x)) (G.symm (e y))
    change G (applyOperator (Zorn.norm T) δ (G.symm (e x)) (G.symm (e y))) =
      applyOperator q δ (G (G.symm (e x))) (G (G.symm (e y))) at hp
    rw [G.apply_symm_apply, G.apply_symm_apply] at hp
    have hxy : e (K.op T x y) = applyOperator q δ (e x) (e y) := hK.2 T x y
    rw [hxy, ← hp, G.symm_apply_apply, hF]
    rfl

theorem weighted_reduced_model :
    ∃ K : QuadraticJordan R (Coordinates R A),
      IsReducedModel hn γ (ParaQuadratic.ofJordan K) ∧ IsAlbert (ParaQuadratic.ofJordan K) := by
  obtain ⟨K, hu, _, ho, _⟩ := weighted_hermitian_quadratic_jordan γ hn
  have h : IsReducedModel hn γ (ParaQuadratic.ofJordan K) := ⟨hu, ho⟩
  exact ⟨K, h, reduced_model_is_albert hn γ _ h⟩

end ReducedModels

end SplitSpecification

end
end LinearAlgebraicGroups.Albert
