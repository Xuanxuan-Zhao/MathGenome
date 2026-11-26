import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdditiveStrongApproximation
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology Filter
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open scoped RestrictedProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords

open AdelicGroups
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Unipotent (Index)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}

private theorem map_evaluate {n : ℕ} {X : SchemeOver K} (f : ParameterSpace K n ⟶ X)
    {R T : Type u} [CommRing R] [Algebra K R] [CommRing T] [Algebra K T]
    (b : R →ₐ[K] T) (a : Fin n → R) :
    mapPoints (CommAlgCat.ofHom b) (evaluate f a) = evaluate f (fun l => b (a l)) := by
  have hc : CommAlgCat.ofHom (MvPolynomial.aeval a) ≫ CommAlgCat.ofHom b =
      CommAlgCat.ofHom (MvPolynomial.aeval (fun l => b (a l))) := by
    rw [← CommAlgCat.ofHom_comp, MvPolynomial.comp_aeval]
  simp only [mapPoints, evaluate, parameterPoint, ← Category.assoc, ← Functor.map_comp,
    ← op_comp, hc]

private theorem map_evaluate_matrix (i : MatrixRealization G) {n : ℕ}
    (f : ParameterSpace K n ⟶ G.val.X)
    {R T : Type u} [CommRing R] [Algebra K R] [CommRing T] [Algebra K T]
    (b : R →ₐ[K] T) (a : Fin n → R) :
    asMatrix i T (evaluate f (fun l => b (a l))) =
      Matrix.GeneralLinearGroup.map b.toRingHom (asMatrix i R (evaluate f a)) := by
  rw [← map_evaluate]
  let α := ((groupPointsFunctor K).map i.embedding) ≫ i.matrix.hom
  exact congrArg (fun h => h (evaluate f a)) (α.naturality (CommAlgCat.ofHom b))

theorem polynomialCoordinates : Specs.ApproximationOfLocalWords.PolynomialCoordinates.{u} := by
  intro K _ G i n f
  let P := MvPolynomial (Fin n) K
  let M := asMatrix i P (evaluate f (MvPolynomial.X : Fin n → P))
  refine ⟨fun l m => M.val l m, M⁻¹.val.det, fun R _ _ a => ?_⟩
  have hm : asMatrix i R (evaluate f a) =
      Matrix.GeneralLinearGroup.map (MvPolynomial.aeval a).toRingHom M := by
    simpa only [MvPolynomial.aeval_X] using map_evaluate_matrix i f
      (MvPolynomial.aeval a) (MvPolynomial.X : Fin n → P)
  dsimp only
  rw [hm, ← map_inv]
  refine ⟨fun _ _ => rfl, ?_⟩
  change ((MvPolynomial.aeval a).toRingHom.mapMatrix M⁻¹.val).det =
    (MvPolynomial.aeval a).toRingHom M⁻¹.val.det
  exact (RingHom.map_det (MvPolynomial.aeval a).toRingHom M⁻¹.val).symm

private theorem continuous_aeval {n : ℕ} {R : Type u} [CommRing R] [Algebra K R]
    [TopologicalSpace R] [IsTopologicalRing R] (p : MvPolynomial (Fin n) K) :
    Continuous (fun a : Fin n → R => MvPolynomial.aeval a p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.aeval_C] using continuous_const
  | add p q hp hq =>
    simp only [map_add]
    exact continuous_add.comp (hp.prodMk hq)
  | mul_X p l hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact continuous_mul.comp (hp.prodMk (continuous_apply l))

private theorem continuous_evaluate (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (w : D.Place) {n : ℕ} (f : ParameterSpace K n ⟶ G.val.X) :
    Continuous (Y := LocalPoints D i w) (fun a : Fin n → D.Completion w => evaluate f a) := by
  obtain ⟨p, _, hp⟩ := polynomialCoordinates i f
  apply (usualLocalTopology D i w).isInducing.continuous_iff.mpr
  refine continuous_matrix fun l m => ?_
  change Continuous (fun a : Fin n → D.Completion w => (asMatrix i _ (evaluate f a)).val l m)
  simp_rw [(hp (D.Completion w) _).1 l m]
  exact continuous_aeval (p l m)

private theorem eventually_integral_aeval (D : GlobalFieldData.{u, v} K) {n : ℕ}
    (p : MvPolynomial (Fin n) K) :
    ∀ᶠ w : D.Place in cofinite, ∀ a : Fin n → D.Completion w,
      (∀ l, a l ∈ D.localIntegerSubring w) → MvPolynomial.aeval a p ∈ D.localIntegerSubring w := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    filter_upwards [D.eventually_mem_localIntegerSubring c] with w hc a _
    rw [MvPolynomial.aeval_C]
    exact hc
  | add p q hp hq =>
    filter_upwards [hp, hq] with w hp hq a ha
    rw [map_add]
    exact (D.localIntegerSubring w).add_mem (hp a ha) (hq a ha)
  | mul_X p l hp =>
    filter_upwards [hp] with w hp a ha
    rw [map_mul, MvPolynomial.aeval_X]
    exact (D.localIntegerSubring w).mul_mem (hp a ha) (ha l)

open private glIntegral_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups

private theorem eventually_integral_evaluate (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) {n : ℕ} (f : ParameterSpace K n ⟶ G.val.X) :
    ∀ᶠ w : D.Place in cofinite, ∀ a : Fin n → D.Completion w,
      (∀ l, a l ∈ D.localIntegerSubring w) → evaluate f a ∈ localSubgroup D i w := by
  let P := MvPolynomial (Fin n) K
  let M := asMatrix i P (evaluate f (MvPolynomial.X : Fin n → P))
  have h (m : Matrix (Index.{u} i.size) (Index.{u} i.size) P) :
      ∀ᶠ w : D.Place in cofinite, ∀ l r, ∀ a : Fin n → D.Completion w,
        (∀ j, a j ∈ D.localIntegerSubring w) →
        MvPolynomial.aeval a (m l r) ∈ D.localIntegerSubring w :=
    eventually_all.mpr fun l => eventually_all.mpr fun r => eventually_integral_aeval D (m l r)
  filter_upwards [h M.val, h M⁻¹.val] with w hl hr a ha
  cases w with
  | inl w =>
    have hm : asMatrix i (D.Completion (.inl w)) (evaluate f a) =
        Matrix.GeneralLinearGroup.map (MvPolynomial.aeval a).toRingHom M := by
      simpa only [MvPolynomial.aeval_X] using map_evaluate_matrix i f
        (MvPolynomial.aeval a) (MvPolynomial.X : Fin n → P)
    change asMatrix i _ (evaluate f a) ∈ (Matrix.GeneralLinearGroup.map (D.integers w).subtype).range
    have hmInv : (asMatrix i (D.Completion (.inl w)) (evaluate f a))⁻¹ =
        Matrix.GeneralLinearGroup.map (MvPolynomial.aeval a).toRingHom M⁻¹ := by
      rw [hm, map_inv]
    refine (glIntegral_iff (D.integers w) _).mpr ⟨?_, ?_⟩
    · rw [hm]
      exact fun l r => hl l r a ha
    · rw [hmInv]
      exact fun l r => hr l r a ha
  | inr w => exact Subgroup.mem_top (G := LocalPoints D i (.inr w)) _

private theorem exists_integral_parameter_tuple (D : GlobalFieldData.{u, v} K)
    {S : Finset D.Place} (hS : S.Nonempty) {n : ℕ} (T : Finset (Outside D S))
    (V : ∀ w : (↑T : Set (Outside D S)), Set (Fin n → D.Completion w.1.1))
    (hV : ∀ w, IsOpen (V w)) (a : ∀ w, V w) :
    ∃ x : Fin n → K,
      (∀ w, (fun l => D.embedding w.1.1 (x l)) ∈ V w) ∧
      ∀ w : Outside D S, w ∉ T → ∀ l, D.embedding w.1 (x l) ∈ D.localIntegerSubring w.1 := by
  classical
  have hboxes (w : (↑T : Set (Outside D S))) :
      ∃ U : Fin n → Set (D.Completion w.1.1),
        (∀ l, IsOpen (U l)) ∧ (∀ l, (a w).1 l ∈ U l) ∧ (Set.univ.pi U ⊆ V w) := by
    obtain ⟨_, ⟨U, F, hU, rfl⟩, ha, hsub⟩ :=
      (isTopologicalBasis_pi fun _ : Fin n =>
        TopologicalSpace.isTopologicalBasis_opens (α := D.Completion w.1.1)).exists_subset_of_mem_open (a w).2 (hV w)
    refine ⟨fun l => if l ∈ F then U l else Set.univ, ?_, ?_, ?_⟩
    · intro l
      by_cases hl : l ∈ F
      · change IsOpen (if l ∈ F then U l else Set.univ)
        rw [ite_eq_left hl]
        exact hU l hl
      · simp only [ite_eq_right hl, isOpen_univ]
    · intro l
      by_cases hl : l ∈ F
      · simpa only [ite_eq_left hl] using Set.mem_pi.mp ha l hl
      · simp only [ite_eq_right hl, Set.mem_univ]
    · intro b hb
      apply hsub
      refine Set.mem_pi.mpr fun l hl => ?_
      have hl' : l ∈ F := hl
      have hbl := Set.mem_pi.mp hb l (Set.mem_univ l)
      rwa [ite_eq_left hl'] at hbl
  choose U hU ha hsub using hboxes
  have hscalar (l : Fin n) := additiveFiniteTuples D (S : Set D.Place)
    hS T (fun w => U w l) (fun w => hU w l) (fun w => ⟨_, ha w l⟩)
  choose x hx hInt using hscalar
  exact ⟨x, fun w => hsub w (Set.mem_pi.mpr fun l _ => hx l w), fun w hw l => hInt l w hw⟩

private theorem rationalClosure_eq (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (S : Finset D.Place) :
    rationalClosure D i S = ((diagonal D i S).range.topologicalClosure : Set (Adeles D i S)) := by
  change closure _ = closure _
  congr 1
  ext x
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, RestrictedProduct.ext _ _ fun w => (hg w).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, fun _ => rfl⟩

private theorem single_evaluate_mem_closure (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) {S : Finset D.Place} (hS : S.Nonempty)
    {n : ℕ} (f : ParameterSpace K n ⟶ G.val.X)
    (h0 : evaluate f (0 : Fin n → K) = (1 : RationalPoints G))
    (w : Outside D S) (a : Fin n → D.Completion w.1) [DecidableEq (Outside D S)] :
    RestrictedProduct.mulSingle (fun v : Outside D S => localSubgroup D i v.1) w (evaluate f a)
      ∈ rationalClosure D i S := by
  classical
  apply (adelicBasis D i S).mem_closure_iff.mpr
  rintro _ ⟨T, U, hU, hRest, rfl⟩ ha
  have hBad : {v : Outside D S | ¬ ∀ b : Fin n → D.Completion v.1,
      (∀ l, b l ∈ D.localIntegerSubring v.1) → evaluate f b ∈ localSubgroup D i v.1}.Finite :=
    eventually_cofinite.mp (Subtype.val_injective.tendsto_cofinite.eventually
      (eventually_integral_evaluate D i f))
  let E := insert w (T ∪ hBad.toFinset)
  let V (v : (↑E : Set (Outside D S))) : Set (Fin n → D.Completion v.1.1) :=
    (fun b => (evaluate f b : LocalPoints D i v.1.1)) ⁻¹' U v.1
  have hV (v : (↑E : Set (Outside D S))) : IsOpen (V v) :=
    (hU v.1).preimage (continuous_evaluate D i v.1.1 f)
  let b (v : Outside D S) := Pi.single (M := fun v => Fin n → D.Completion v.1) w a v
  have heval (v : Outside D S) : evaluate f (b v) =
      RestrictedProduct.mulSingle (fun v : Outside D S => localSubgroup D i v.1) w (evaluate f a) v := by
    by_cases hv : v = w
    · subst v
      simp only [b, Pi.single_eq_same, RestrictedProduct.mulSingle_eq_same]
    · have hz : evaluate f (0 : Fin n → D.Completion v.1) = (1 : LocalPoints D i v.1) := by
        have he := map_evaluate f (Algebra.ofId K (D.Completion v.1)) (0 : Fin n → K)
        change localPoint D i v.1 (evaluate f (0 : Fin n → K)) = _ at he
        rw [h0, map_one] at he
        simpa only [Pi.zero_apply, map_zero, ← Pi.zero_def] using he.symm
      simp only [b, Pi.single_eq_of_ne hv, RestrictedProduct.mulSingle_eq_of_ne _ _ hv, hz]
  have ha' (v : (↑E : Set (Outside D S))) : b v.1 ∈ V v := by
    change evaluate f (b v.1) ∈ U v.1
    rw [heval]
    exact ha v.1
  obtain ⟨x, hx, hxInt⟩ := exists_integral_parameter_tuple D hS E V hV (fun v => ⟨_, ha' v⟩)
  refine ⟨diagonal D i S (evaluate f x), ?_, ⟨evaluate f x, fun _ => rfl⟩⟩
  intro v
  have he : diagonal D i S (evaluate f x) v =
      evaluate f (fun l => D.embedding v.1 (x l)) :=
    map_evaluate f (Algebra.ofId K (D.Completion v.1)) x
  rw [he]
  by_cases hv : v ∈ E
  · exact hx ⟨v, hv⟩
  · have hvT : v ∉ T := fun h => hv (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hvB : v ∉ hBad.toFinset := fun h =>
      hv (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    have hInt : ∀ b : Fin n → D.Completion v.1,
        (∀ l, b l ∈ D.localIntegerSubring v.1) → evaluate f b ∈ localSubgroup D i v.1 := by
      by_contra h
      exact hvB (hBad.mem_toFinset.mpr h)
    rw [hRest v hvT]
    exact hInt _ (hxInt v hv)


theorem localWordClosure : Specs.ApproximationOfLocalWords.LocalWordClosure.{u, v} := by
  classical
  intro K _ G D i S hS ι n f h0 x ⟨T, hx⟩ hg
  let A (w : Outside D S) := localSubgroup D i w.1
  let C := (diagonal D i S).range.topologicalClosure
  have hsingle (w : Outside D S) :
      generatedAt f D i w.1 ≤ C.comap (RestrictedProduct.mulSingleMonoidHom A w) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, a, rfl⟩
    change RestrictedProduct.mulSingle A w (evaluate (f j) a) ∈ C
    rw [← SetLike.mem_coe, ← rationalClosure_eq]
    exact single_evaluate_mem_closure D i hS (f j) (h0 j) w a
  rw [rationalClosure_eq]
  change x ∈ C
  revert x
  induction T using Finset.induction_on with
  | empty =>
    intro x hx _
    have hx1 : x = 1 := RestrictedProduct.ext _ _ fun w => hx w (Finset.notMem_empty _)
    rw [hx1]
    exact C.one_mem
  | insert w T hw ih =>
    intro x hx hg
    let y := RestrictedProduct.mulSingle A w (x w)
    have hy : y ∈ C := hsingle w (hg w)
    have hrest : y⁻¹ * x ∈ C := by
      apply ih
      · intro v hv
        by_cases hvw : v = w
        · subst v
          simp [y, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply]
        · have he : x v = 1 := hx v (by simpa [hvw] using hv)
          simp [y, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
            RestrictedProduct.mulSingle_eq_of_ne _ _ hvw, he]
      · intro v
        apply (generatedAt f D i v.1).mul_mem _ (hg v)
        apply (generatedAt f D i v.1).inv_mem
        by_cases hvw : v = w
        · subst v
          simpa only [y, RestrictedProduct.mulSingle_eq_same] using hg w
        · simpa only [y, RestrictedProduct.mulSingle_eq_of_ne _ _ hvw] using
            (generatedAt f D i v.1).one_mem
    simpa only [mul_inv_cancel_left] using C.mul_mem hy hrest

theorem localDenseGeneration : Specs.ApproximationOfLocalWords.LocalDenseGeneration.{u, v} := by
  classical
  intro K _ G D i S hS ι n f h0 hd
  apply (adelicBasis D i S).dense_iff.mpr
  rintro _ ⟨T, U, hU, hRest, rfl⟩ ⟨x, hx⟩
  have hlocal (w : (↑T : Set (Outside D S))) :
      ∃ y : LocalPoints D i w.1.1, y ∈ U w.1 ∧ y ∈ generatedAt f D i w.1.1 :=
    mem_closure_iff.mp (hd w.1 (x w.1)) _ (hU w.1) (hx w.1)
  choose y hyU hyGen using hlocal
  let z (w : Outside D S) : LocalPoints D i w.1 := if hw : w ∈ T then y ⟨w, hw⟩ else 1
  have hzOff (w : Outside D S) (hw : w ∉ T) : z w = 1 := dite_eq_right hw
  let a : Adeles D i S := ⟨z, by
    filter_upwards [show (↑T : Set (Outside D S))ᶜ ∈ cofinite by simpa only [mem_cofinite, compl_compl] using T.finite_toSet]
      with w hw
    change z w ∈ localSubgroup D i w.1
    rw [hzOff w hw]
    exact (localSubgroup D i w.1).one_mem⟩
  have haU : a ∈ box D i S U := by
    intro w
    change z w ∈ U w
    by_cases hw : w ∈ T
    · rw [show z w = y ⟨w, hw⟩ from dite_eq_left hw]
      exact hyU ⟨w, hw⟩
    · rw [hRest w hw, hzOff w hw]
      exact (localSubgroup D i w.1).one_mem
  have haGen (w : Outside D S) : a w ∈ generatedAt f D i w.1 := by
    change z w ∈ generatedAt f D i w.1
    by_cases hw : w ∈ T
    · rw [show z w = y ⟨w, hw⟩ from dite_eq_left hw]
      exact hyGen ⟨w, hw⟩
    · rw [hzOff w hw]
      exact (generatedAt f D i w.1).one_mem
  have ha := localWordClosure D i S hS f h0 a ⟨T, hzOff⟩ haGen
  exact (adelicBasis D i S).mem_closure_iff.mp ha _ ⟨T, U, hU, hRest, rfl⟩ haU

theorem parameterPoint_surjective {n : ℕ} {R : Type u} [CommRing R] [Algebra K R] :
    Function.Surjective
      (parameterPoint : (Fin n → R) → Points (ParameterSpace K n) (CommAlgCat.of K R)) := by
  intro x
  let F := algSpec.fullyFaithful (R := CommRingCat.of K)
  let b := F.preimage x
  let a := b.unop.hom
  refine ⟨fun l => a (MvPolynomial.X l), ?_⟩
  change (testSpec K).map (CommAlgCat.ofHom (MvPolynomial.aeval (a ∘ MvPolynomial.X))).op = x
  rw [← MvPolynomial.aeval_unique a]
  exact F.map_preimage x

private theorem centeredChart (H : Specs.GroupScheme K) {n : ℕ}
    (e : ParameterSpace K n ≅ H.X) :
    ∃ e' : ParameterSpace K n ≅ H.X,
      evaluate e'.hom (0 : Fin n → K) =
        (1 : ((groupPointsFunctor K).obj H).obj (CommAlgCat.of K K)) := by
  obtain ⟨a, ha⟩ := parameterPoint_surjective
    ((1 : ((groupPointsFunctor K).obj H).obj (CommAlgCat.of K K)) ≫ e.inv)
  let P := MvPolynomial (Fin n) K
  let plus : P →ₐ[K] P := MvPolynomial.aeval fun l => MvPolynomial.X l + MvPolynomial.C (a l)
  let minus : P →ₐ[K] P := MvPolynomial.aeval fun l => MvPolynomial.X l - MvPolynomial.C (a l)
  have hplusX (l : Fin n) : plus (MvPolynomial.X l) = MvPolynomial.X l + MvPolynomial.C (a l) :=
    MvPolynomial.aeval_X _ l
  have hminusX (l : Fin n) : minus (MvPolynomial.X l) = MvPolynomial.X l - MvPolynomial.C (a l) :=
    MvPolynomial.aeval_X _ l
  have hplusC (c : K) : plus (MvPolynomial.C c) = MvPolynomial.C c :=
    MvPolynomial.aeval_C _ c
  have hminusC (c : K) : minus (MvPolynomial.C c) = MvPolynomial.C c :=
    MvPolynomial.aeval_C _ c
  have hplus : plus.comp minus = AlgHom.id K P := by
    apply MvPolynomial.algHom_ext
    intro l
    change plus (minus (MvPolynomial.X l)) = MvPolynomial.X l
    rw [hminusX, map_sub, hplusX, hplusC, add_sub_cancel_right]
  have hminus : minus.comp plus = AlgHom.id K P := by
    apply MvPolynomial.algHom_ext
    intro l
    change minus (plus (MvPolynomial.X l)) = MvPolynomial.X l
    rw [hplusX, map_add, hminusX, hminusC, sub_add_cancel]
  let t : CommAlgCat.of K P ≅ CommAlgCat.of K P :=
    { hom := CommAlgCat.ofHom minus
      inv := CommAlgCat.ofHom plus
      hom_inv_id := by rw [← CommAlgCat.ofHom_comp, hplus]; rfl
      inv_hom_id := by rw [← CommAlgCat.ofHom_comp, hminus]; rfl }
  refine ⟨(testSpec K).mapIso t.symm.op ≪≫ e, ?_⟩
  have hc : (MvPolynomial.aeval (0 : Fin n → K)).comp plus = MvPolynomial.aeval a := by
    apply MvPolynomial.algHom_ext
    intro l
    change MvPolynomial.aeval (0 : Fin n → K) (plus (MvPolynomial.X l)) =
      MvPolynomial.aeval a (MvPolynomial.X l)
    rw [hplusX, map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    change 0 + a l = a l
    exact zero_add _
  have hcomp : CommAlgCat.ofHom plus ≫ CommAlgCat.ofHom (MvPolynomial.aeval (0 : Fin n → K)) =
      CommAlgCat.ofHom (MvPolynomial.aeval a) := by
    rw [← CommAlgCat.ofHom_comp, hc]
  have ht : parameterPoint (0 : Fin n → K) ≫ (testSpec K).map t.inv.op =
      parameterPoint a := by
    change (testSpec K).map (CommAlgCat.ofHom (MvPolynomial.aeval (0 : Fin n → K))).op ≫
      (testSpec K).map (CommAlgCat.ofHom plus).op = (testSpec K).map (CommAlgCat.ofHom (MvPolynomial.aeval a)).op
    rw [← Functor.map_comp, ← op_comp, hcomp]
  change parameterPoint (0 : Fin n → K) ≫ (testSpec K).map t.inv.op ≫ e.hom = _
  rw [← Category.assoc, ht, ha, Category.assoc, e.inv_hom_id, Category.comp_id]

theorem subgroupsWithAffineCoordinates :
    Specs.ApproximationOfLocalWords.SubgroupsWithAffineCoordinates.{u, v} := by
  intro K _ G D i S hS ι n H chart
  choose e h0 using fun j => centeredChart (H j).group (chart j)
  let f (j : ι) := (e j).hom ≫ (H j).inclusion.hom.hom
  have hbase (j : ι) : evaluate (f j) (0 : Fin (n j) → K) = (1 : RationalPoints G) := by
    have he : evaluate (f j) (0 : Fin (n j) → K) =
        evaluate (e j).hom (0 : Fin (n j) → K) ≫ (H j).inclusion.hom.hom :=
      (Category.assoc _ _ _).symm
    rw [he, h0 j]
    exact map_one (((groupPointsFunctor K).map (H j).inclusion).app (CommAlgCat.of K K)).hom
  have hgen (w : D.Place) : generatedAt f D i w = generatedBySubgroups H D i w := by
    apply congrArg Subgroup.closure
    ext g
    constructor
    · rintro ⟨j, a, rfl⟩
      exact ⟨j, evaluate (e j).hom a, Category.assoc _ _ _⟩
    · rintro ⟨j, h, rfl⟩
      obtain ⟨a, ha⟩ := parameterPoint_surjective (h ≫ (e j).inv)
      refine ⟨j, a, ?_⟩
      simp [evaluate, f, ha]
  refine ⟨fun x hx hg => localWordClosure D i S hS f hbase x hx (fun w => ?_),
    fun hd => localDenseGeneration D i S hS f hbase (fun w => ?_)⟩
  · rw [hgen]
    exact hg w
  · rw [hgen]
    exact hd w

theorem subgroupsWithPolynomialCoordinates :
    Specs.ApproximationOfLocalWords.SubgroupsWithPolynomialCoordinates.{u, v} := by
  intro K _ G D i S hS ι n H A e coordinates
  apply subgroupsWithAffineCoordinates D i S hS H
  intro j
  let b := CommAlgCat.isoMk (coordinates j)
  let p : ParameterSpace K (n j) ≅ (specGroup (A j)).X :=
    (testSpec K).mapIso b.symm.op
  exact p ≪≫ (Grp.forget (SchemeOver K)).mapIso (e j)

end LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords
