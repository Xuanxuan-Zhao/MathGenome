import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeALocalModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

open CategoryTheory
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.OuterTypeALocalModels

open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.Arithmetic.OuterTypeALocalModels
open LinearAlgebraicGroups.Specs.OuterTypeAModels
open LinearAlgebraicGroups.UnitaryNormEquations
open LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras
open Algebra.TensorProduct MulOpposite
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open _root_.RM03.CSA.NormOneGroup

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open private centreProjections_bijective centreConjugation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
open private hermitian_matrix from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras

variable {K E F A : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]

local notation "Q₀" => F ⊗[K] E

private theorem centre_isField_of_no_embedding [Algebra.IsQuadraticExtension K E]
    (h : IsEmpty (E →ₐ[K] F)) : IsField (F ⊗[K] E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Q₀
  letI : M.IsMaximal := hM
  let q : Q₀ →ₐ[F] Q₀ ⧸ M := Ideal.Quotient.mkₐ F M
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hdim : Module.finrank F Q₀ = 2 :=
    (Module.finrank_baseChange ..).trans (Algebra.IsQuadraticExtension.finrank_eq_two K E)
  have hle : Module.finrank F (Q₀ ⧸ M) ≤ 2 := by
    rw [← hdim]
    exact LinearMap.finrank_le_finrank_of_surjective (f := q.toLinearMap) hq
  have hpos : 0 < Module.finrank F (Q₀ ⧸ M) := Module.finrank_pos
  have hn : Module.finrank F (Q₀ ⧸ M) ≠ 1 := by
    intro h1
    let e := AlgEquiv.ofBijective (Algebra.ofId F (Q₀ ⧸ M))
      (Module.Free.bijective_algebraMap_of_finrank_eq_one h1)
    exact h.false (((e.symm.toAlgHom.comp q).restrictScalars K).comp includeRight)
  have heq : Module.finrank F Q₀ = Module.finrank F (Q₀ ⧸ M) := by omega
  let e := AlgEquiv.ofBijective q
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := q.toLinearMap) heq).mpr hq, hq⟩
  exact e.toMulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient M).mp hM)

private theorem split_model [Algebra.IsQuadraticExtension K E] [Algebra.IsSeparable K E]
    (hA : isCentralSimple E A) {ι : Type u} [Fintype ι] (b : Module.Basis ι E A)
    (star : SecondKind K E A) {G : AffineAlgebraicGroup K} (hG : RepresentsUnitary hA b star G)
    (j : E →ₐ[K] F) : SplitModel (F := F) star hA b G := by
  letI : Algebra E F := j.toRingHom.toAlgebra
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  exact ⟨j, centreProjections_bijective (R := F) star.conjugation star.conjugation_ne,
    LinearAlgebraicGroups.OuterTypeAModels.splitCentreTypeAModel hA b star hG⟩

private theorem separable_of_quadratic_automorphism {Q : Type u} [Field Q] [Algebra F Q]
    (h : Module.finrank F Q = 2) (σ : Q ≃ₐ[F] Q) (hs : σ ≠ 1) :
    Algebra.IsSeparable F Q := by
  let : FiniteDimensional F Q := Module.finite_of_finrank_eq_succ h
  let f : Bool → Gal(Q/F) := fun b => if b then σ else 1
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f, Ne.symm hs]
  have hlo := Nat.card_le_card_of_injective f hf
  have hhi := Nat.card_le_card_of_injective
    (fun g : Gal(Q/F) => g.toAlgHom) (fun _ _ he => AlgEquiv.ext (fun x => congrArg (fun f : Q →ₐ[F] Q => f x) he))
  have hcard := hhi.trans (card_algHom_le_finrank (K := F) (M := Q) (L := Q))
  rw [Nat.card_eq_fintype_card, Fintype.card_bool] at hlo
  exact (IsGalois.of_card_aut_eq_finrank F Q (show Nat.card Gal(Q/F) = Module.finrank F Q by omega)).to_isSeparable

section ScalarExtension

local instance (priority := 2000) : Algebra E Q₀ := Algebra.TensorProduct.rightAlgebra

local instance fieldCentre [hc : Fact (IsField (F ⊗[K] E))] : Field (F ⊗[K] E) := hc.out.toField

set_option maxRecDepth 3000 in
private def localAdjoint [Fact (IsField Q₀)] (star : SecondKind K E A) : SecondKind F Q₀ (Q₀ ⊗[E] A) := by
  let σ : Q₀ ≃ₐ[F] Q₀ := centreConjugation star.conjugation
  let c₀ := associateCentre (F := K) (E := E) (R := F) (A := A)
  let c : (F ⊗[K] A) ≃ₐ[F] (Q₀ ⊗[E] A) :=
    AlgEquiv.ofRingEquiv (f := c₀.toRingEquiv) (fun _ => rfl)
  let t := (c.symm.trans (adjointEquiv (R := F) star)).trans (AlgEquiv.op c)
  refine ⟨σ, ?_, t, ?_, ?_⟩
  · intro he
    apply star.conjugation_ne
    ext a
    have ha := DFunLike.congr_fun he (includeRight (R := K) (A := F) a)
    exact includeRight_injective (FaithfulSMul.algebraMap_injective K F) ha
  · intro x
    change c (adjointAt star (c.symm (c (adjointAt star (c.symm x))))) = x
    rw [c.symm_apply_apply, adjointAt_adj, c.apply_symm_apply]
  · intro q
    have hc (x : Q₀) :
        c (map (.id F F) (IsScalarTower.toAlgHom K E A) x) =
          algebraMap Q₀ (Q₀ ⊗[E] A) x := by
      induction x using TensorProduct.inductionOn with
      | tmul r a =>
        change (r ⊗ₜ[K] (1 : E)) ⊗ₜ[E] algebraMap E A a = (r ⊗ₜ[K] a) ⊗ₜ[E] (1 : A)
        rw [Algebra.algebraMap_eq_smul_one (R := E) (A := A) a, TensorProduct.tmul_smul]
        rw [TensorProduct.smul_tmul']
        congr 1
        change (1 ⊗ₜ[K] a) * (r ⊗ₜ[K] (1 : E)) = r ⊗ₜ[K] a
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [← hc q]
    change c (adjointAt star (c.symm (c _))) = _
    rw [c.symm_apply_apply, ← hc]
    congr 1
    induction q using TensorProduct.inductionOn with
    | tmul r a =>
      change (r ⊗ₜ[K] unop (star.adjoint (algebraMap E A a))) =
        r ⊗ₜ[K] algebraMap E A (star.conjugation a)
      rw [star.adjoint_centre]
    | add x y hx hy => simp only [adjointAt, map_add, MulOpposite.unop_add] at hx hy ⊢
                       rw [hx, hy]

private theorem algClosed_of_ringEquiv {P : Type*} {Q : Type*} [Field P] [Field Q]
    [IsAlgClosed P] (e : P ≃+* Q) : IsAlgClosed Q := by
  apply IsAlgClosed.of_exists_root
  intro p hm hp
  have hdeg : (p.map e.symm.toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact (Polynomial.degree_pos_of_irreducible hp).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (p.map e.symm.toRingHom) hdeg
  refine ⟨e x, e.symm.injective ?_⟩
  rw [map_zero, ← hx]
  change e.symm (p.eval (e x)) = _
  clear hx hdeg hp hm
  induction p using Polynomial.induction_on <;> simp_all

private theorem real_quadratic_algClosed {Q : Type u} [Field Q] [Algebra F Q]
    (e : F ≃+* ℝ) (hq : Module.finrank F Q = 2) : IsAlgClosed Q := by
  let : Algebra ℝ F := e.symm.toRingHom.toAlgebra
  let : Algebra ℝ Q := ((algebraMap F Q).comp e.symm.toRingHom).toAlgebra
  let : IsScalarTower ℝ F Q := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional F Q := Module.finite_of_finrank_eq_succ hq
  have hF : Module.finrank ℝ F = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr e.symm.bijective
  have hQ : Module.finrank ℝ Q = 2 := by
    rw [← Module.finrank_mul_finrank ℝ F Q, hF, hq, one_mul]
  let : FiniteDimensional ℝ Q := Module.finite_of_finrank_eq_succ hQ
  rcases Real.nonempty_algEquiv_or Q with hr | hc
  · let r := hr.some
    have hr := r.toLinearEquiv.finrank_eq
    simp [hQ] at hr
  · exact algClosed_of_ringEquiv hc.some.symm.toRingEquiv

private theorem archimedean_quadratic_algClosed {Q : Type u} [Field Q] [Algebra F Q]
    (e : Nonempty (F ≃+* ℝ) ∨ Nonempty (F ≃+* ℂ)) (hq : Module.finrank F Q = 2) : IsAlgClosed Q := by
  rcases e with hr | hc
  · exact real_quadratic_algClosed hr.some hq
  · let : IsAlgClosed F := algClosed_of_ringEquiv hc.some.symm
    let : FiniteDimensional F Q := Module.finite_of_finrank_eq_succ hq
    have h := Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F) (K := Q))
    omega

private theorem splitting_over_algClosed {Q B : Type u} [Field Q] [IsAlgClosed Q] [Ring B]
    [Algebra Q B] (h : isCentralSimple Q B) :
    Nonempty (B ≃ₐ[Q] Mat Q (degree Q B)) := by
  let : IsSimpleRing B := h.1
  let : FiniteDimensional Q B := h.2.2
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed Q B
  have hd : degree Q B = n := by
    rw [degree, e.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp [← pow_two]
  rw [hd]
  exact ⟨e⟩

private theorem completion_splitting (D : GlobalFieldData.{u,v} K) (w : D.Place)
    {Q B : Type u} [Field Q] [hFQ : Algebra (D.Completion w) Q]
    [Algebra.IsSeparable (D.Completion w) Q] [Ring B] [Algebra (D.Completion w) B]
    [Algebra Q B] [IsScalarTower (D.Completion w) Q B]
    (hQ : Module.finrank (D.Completion w) Q = 2)
    (hB : isCentralSimple Q B) (s : SecondKind (D.Completion w) Q B) :
    Nonempty (B ≃ₐ[Q] Mat Q (degree Q B)) := by
  cases w with
  | inl w =>
    let : ValuativeRel (D.Completion (.inl w)) := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
    let : IsNonarchimedeanLocalField (D.Completion (.inl w)) := D.finiteCompletion_isLocalField w
    exact local_splitting hQ hB s
  | inr w =>
    cases D with
    | number hK =>
      let : NumberField K := hK
      have h : Nonempty (w.Completion ≃+* ℝ) ∨ Nonempty (w.Completion ≃+* ℂ) := by
        rcases w.isReal_or_isComplex with hw | hw
        · exact .inl ⟨(numberRealCompletion w hw).choose⟩
        · exact .inr ⟨(numberComplexCompletion w hw).choose⟩
      letI : Field w.Completion := inferInstanceAs (Field w.Completion)
      letI : Algebra w.Completion Q := hFQ
      have : IsAlgClosed Q := archimedean_quadratic_algClosed h hQ
      exact splitting_over_algClosed hB
    | function F t => exact w.elim

section MatrixPoints

variable [Fact (IsField (F ⊗[K] E))]


variable {R S : Type u} [CommRing R] [Algebra K R] [Algebra F R] [IsScalarTower K F R]
  [CommRing S] [Algebra K S] [Algebra F S] [IsScalarTower K F S]

local notation "C" R:max => R ⊗[F] (F ⊗[K] E)
local notation "C₀" R:max => R ⊗[K] E

local instance : Algebra Q₀ (C R) := rightAlgebra
local instance : Algebra E (C₀ R) := rightAlgebra
local instance : Algebra E (C R) :=
  ((algebraMap Q₀ (C R)).comp (algebraMap E Q₀)).toAlgebra
local instance : IsScalarTower E Q₀ (C R) :=
  IsScalarTower.of_algebraMap_eq' rfl

private def extendCentre : C₀ R ≃ₐ[E] C R :=
  AlgEquiv.ofRingEquiv
    (f := (factorScalarExtension (E := K) (L := F) (R := R) (A := E)).toRingEquiv)
    (fun a : E => by rfl)

omit [Fact (IsField (F ⊗[K] E))] in
private theorem extendCentre_tmul (r : R) (a : E) :
    extendCentre (F := F) (r ⊗ₜ[K] a) = r ⊗ₜ[F] (1 ⊗ₜ[K] a : Q₀) := rfl

variable {n : ℕ}

private def pointMatrix (e : (Q₀ ⊗[E] A) ≃ₐ[Q₀] Mat Q₀ n) :
    (R ⊗[K] A) ≃+* Mat (C R) n :=
  (associateCentre (F := K) (E := E) (R := R) (A := A)).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (extendCentre (K := K) (E := E) (R := R) (F := F)) (.refl : A ≃ₐ[E] A)).toRingEquiv.trans
      (extendSplitting (k := E) (A := A) (K := Q₀) (R := C R) e).toRingEquiv)

private theorem pointMatrix_tmul (e : (Q₀ ⊗[E] A) ≃ₐ[Q₀] Mat Q₀ n) (r : R) (a : A) :
    pointMatrix (K := K) (E := E) (F := F) (R := R) e (r ⊗ₜ[K] a) =
      (r ⊗ₜ[F] (1 : Q₀)) • (e (1 ⊗ₜ[E] a)).map (includeRight (R := F) (A := R)) := by
  change extendSplitting (k := E) (K := Q₀) (R := C R) e ((extendCentre (F := F) (r ⊗ₜ[K] (1 : E))) ⊗ₜ[E] a) = _
  rw [extendSplitting_tmul, extendCentre_tmul, Algebra.TensorProduct.one_def]
  rfl

private theorem pointMatrix_det (hA : isCentralSimple E A) {ι : Type u} [Fintype ι]
    (b : Module.Basis ι E A) (e : (Q₀ ⊗[E] A) ≃ₐ[Q₀] Mat Q₀ (degree E A))
    (x : R ⊗[K] A) :
    (pointMatrix e x).det = extendCentre (F := F) (unitaryNorm hA b x) := by
  change (extendSplitting (k := E) (K := Q₀) (R := C R) e
      (changeCoefficients (extendCentre (K := K) (F := F) (R := R) (E := E)).toAlgHom
        (associateCentre (F := K) (E := E) (R := R) x))).det = _
  let y := associateCentre (F := K) (E := E) (R := R) x
  let f := (extendCentre (K := K) (F := F) (E := E) (R := R)).toAlgHom
  exact (normAt_eq_det (K := Q₀) (R := C R) hA b e (changeCoefficients f y)).symm.trans
    (normAt_natural hA b f y)

private theorem pointMatrix_natural (e : (Q₀ ⊗[E] A) ≃ₐ[Q₀] Mat Q₀ n) (f : R →ₐ[F] S) (x : R ⊗[K] A) :
    pointMatrix e (map (f.restrictScalars K) (.id K A) x) =
      (pointMatrix e x).map (map f (.id F Q₀)) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, pointMatrix_tmul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, map_one, AlgHom.restrictScalars_apply]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    exact (map_add (map f (.id F Q₀)).toRingHom.mapMatrix _ _).symm

private theorem localAdjoint_one_tmul (star : SecondKind K E A) (a : A) :
    ((localAdjoint (F := F) star).adjoint (1 ⊗ₜ[E] a)).unop =
      (1 : Q₀) ⊗ₜ[E] (star.adjoint a).unop := by
  let c₀ := associateCentre (F := K) (E := E) (R := F) (A := A)
  have hc : c₀.symm ((1 : Q₀) ⊗ₜ[E] a) = (1 : F) ⊗ₜ[K] a :=
    c₀.symm_apply_eq.mpr rfl
  change c₀ (adjointAt star (c₀.symm ((1 : Q₀) ⊗ₜ[E] a))) = _
  rw [hc, adjointAt_tmul]
  rfl

private theorem pointMatrix_adjoint (star : SecondKind K E A)
    (e : (Q₀ ⊗[E] A) ≃ₐ[Q₀] Mat Q₀ n) (H : (Mat Q₀ n)ˣ)
    (he : ∀ a, e ((localAdjoint (F := F) star).adjoint a).unop =
      (↑H⁻¹ : Mat Q₀ n) * conjugateTranspose (localAdjoint (F := F) star).conjugation (e a) * H.val)
    (x : R ⊗[K] A) :
    let σ := (localAdjoint (F := F) star).conjugation
    let j : Q₀ →ₐ[F] C R := includeRight
    let barR := map (.id R R) σ.toAlgHom
    pointMatrix e (adjointAt star x) =
      ((↑H⁻¹ : Mat Q₀ n).map j) * ((pointMatrix e x).map barR).transpose * (H.val.map j) := by
  dsimp only
  let σ := (localAdjoint (F := F) star).conjugation
  let j : Q₀ →ₐ[F] C R := includeRight
  let barR : C R →ₐ[R] C R := map (.id R R) σ.toAlgHom
  change pointMatrix e (adjointAt star x) =
    ((↑H⁻¹ : Mat Q₀ n).map j) * ((pointMatrix e x).map barR).transpose * (H.val.map j)
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [adjointAt_tmul, pointMatrix_tmul, pointMatrix_tmul, ← localAdjoint_one_tmul star a, he]
    have hcomm (Y : Mat Q₀ n) :
        (conjugateTranspose σ Y).map j = ((Y.map j).map barR).transpose := rfl
    have hfixed : barR (r ⊗ₜ[F] (1 : Q₀)) = r ⊗ₜ[F] (1 : Q₀) := by
      simp only [barR, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    rw [Matrix.map_mul (f := j), Matrix.map_mul (f := j), hcomm]
    symm
    rw [Matrix.map_smul' (f := barR) _ _ (map_mul barR), hfixed, Matrix.transpose_smul]
    let X := (((e (1 ⊗ₜ[E] a)).map j).map barR).transpose
    let D := H.val.map j
    let D' := (↑H⁻¹ : Mat Q₀ n).map j
    let r' := r ⊗ₜ[F] (1 : Q₀)
    change D' * (r' • X) * D = r' • (D' * X * D)
    exact (congrArg (· * D) (Matrix.mul_smul D' r' X)).trans (Matrix.smul_mul _ _ _)
  | add x y hx hy =>
    simp only [adjointAt, map_add, MulOpposite.unop_add] at hx hy ⊢
    rw [hx, hy]
    change _ = _ * (barR.toRingHom.mapMatrix (pointMatrix e x + pointMatrix e y)).transpose * _
    rw [map_add, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
    rfl

open LinearAlgebraicGroups.Specs.Unipotent (baseChangedAlgebraicGroup)
open private baseChangePointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA

set_option maxHeartbeats 950000 in
private theorem represents_hermitian (hA : isCentralSimple E A) {ι : Type u} [Fintype ι]
    (b : Module.Basis ι E A) (star : SecondKind K E A) {G : AffineAlgebraicGroup K}
    (hG : RepresentsUnitary hA b star G)
    (e : (Q₀ ⊗[E] A) ≃ₐ[Q₀] Mat Q₀ (degree E A)) (H : (Mat Q₀ (degree E A))ˣ)
    (he : ∀ a, e ((localAdjoint (F := F) star).adjoint a).unop =
      (↑H⁻¹ : Mat Q₀ (degree E A)) *
        conjugateTranspose (localAdjoint (F := F) star).conjugation (e a) * H.val) :
    RepresentsHermitian (localAdjoint (F := F) star).conjugation H.val
      (baseChangedAlgebraicGroup F G) := by
  obtain ⟨point, hmul, hnat⟩ := hG
  let σ := (localAdjoint (F := F) star).conjugation
  let c := baseChangePointIso (K := F) G.val
  let T (R : TestAlgebra F) := restrictTestAlgebraObj K F R
  let tower (R : TestAlgebra F) : IsScalarTower K F (T R) := IsScalarTower.of_algebraMap_eq' rfl
  let P (R : TestAlgebra F) : ((T R) ⊗[K] A) ≃+* Mat (C R) (degree E A) :=
    letI := tower R
    pointMatrix e
  have hP (R : TestAlgebra F) (u : ((T R) ⊗[K] A)ˣ) :
      IsSpecialUnitary hA b star u ↔
        ∃ hg : (P R u.val).det = 1,
          PreservesHermitianMatrix σ H.val R ⟨P R u.val, hg⟩ := by
    letI := tower R
    let j : Q₀ →ₐ[F] C R := includeRight
    let D := H.val.map j
    let D' := (↑H⁻¹ : Mat Q₀ (degree E A)).map j
    have hDD : D * D' = 1 := by
      simp only [D, D', ← Matrix.map_mul (f := j), Units.mul_inv]
      exact Matrix.map_one j (map_zero _) (map_one _)
    have hDD' : D' * D = 1 := by
      simp only [D, D', ← Matrix.map_mul (f := j), Units.inv_mul]
      exact Matrix.map_one j (map_zero _) (map_one _)
    have hn (x : (T R) ⊗[K] A) :
        (P R x).det = 1 ↔ unitaryNorm hA b x = 1 := by
      rw [show (P R x).det = extendCentre (F := F) (K := K) (E := E) (R := T R)
        (unitaryNorm hA b x) from pointMatrix_det hA b e x]
      exact (extendCentre (F := F) (K := K) (E := E) (R := T R)).injective.eq_iff' (map_one _)
    have ha : adjointAt star u.val * u.val = 1 ↔
        ((P R u.val).map (conjugationAt σ R)).transpose * D * P R u.val = D := by
      let M := ((P R u.val).map (conjugationAt σ R)).transpose * D * P R u.val
      have ha₀ := pointMatrix_adjoint (R := T R) star e H he u.val
      have hform : P R (adjointAt star u.val * u.val) = D' * M := by
        rw [map_mul]
        change pointMatrix e (adjointAt star u.val) * _ = _
        rw [ha₀]
        simp only [M, D, D', mul_assoc]
        rfl
      constructor
      · intro h
        have hh : D' * M = 1 := hform.symm.trans (by rw [h, map_one])
        simpa only [← mul_assoc, hDD, one_mul, mul_one] using congrArg (D * ·) hh
      · intro h
        apply (P R).injective
        rw [hform, show M = D from h, hDD', map_one]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨(hn _).mpr h₂, ha.mp h₁⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨ha.mpr h₂, (hn _).mp h₁⟩
  let cmp (R : TestAlgebra F) :
      {u : ((T R) ⊗[K] A)ˣ // IsSpecialUnitary hA b star u} ≃
        {g : Matrix.SpecialLinearGroup (Fin (degree E A)) (C R) //
          PreservesHermitianMatrix σ H.val R g} :=
    Equiv.ofBijective
      (fun u => ⟨⟨P R u.val.val, ((hP R u.val).mp u.property).choose⟩,
        ((hP R u.val).mp u.property).choose_spec⟩) (by
        refine ⟨?_, ?_⟩
        · intro u v h
          apply Subtype.ext
          apply Units.ext
          exact (P R).injective (congrArg (fun x => x.val.val) h)
        · intro g
          have hu : IsUnit g.val.val :=
            (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [g.val.property]; exact isUnit_one)
          let u := (Units.mapEquiv (P R).toMulEquiv).symm hu.unit
          have hv : P R u.val = g.val.val :=
            (congrArg Units.val ((Units.mapEquiv (P R).toMulEquiv).apply_symm_apply _)).trans hu.unit_spec
          have hw : IsSpecialUnitary hA b star u := (hP R u).mpr ⟨hv ▸ g.val.property, by
            change ((P R u.val).map (conjugationAt σ R)).transpose * _ * P R u.val = _
            rw [hv]
            exact g.property⟩
          refine ⟨⟨u, hw⟩, ?_⟩
          exact Subtype.ext (Subtype.ext hv))
  let w (R : TestAlgebra F) :
      AdjointRepresentation.GroupPoints (baseChangedAlgebraicGroup F G).val R ≃
        {g : Matrix.SpecialLinearGroup (Fin (degree E A)) (C R) //
          PreservesHermitianMatrix σ H.val R g} := (c.app R).groupIsoToMulEquiv.toEquiv.trans
    ((point (T R)).trans (cmp R))
  have hw (R : TestAlgebra F) (x : (groupPointsFunctor F).obj (baseChangedAlgebraicGroup F G).val |>.obj R) :
      (w R x).val.val = P R (point (T R) (c.hom.app R x)).val.val := rfl
  refine ⟨w, ?_, ?_⟩
  · intro R x y
    apply Subtype.ext
    change (w R (x * y)).val.val = (w R x).val.val * (w R y).val.val
    rw [hw, hw, hw, map_mul (c.hom.app R).hom, hmul, Units.val_mul, map_mul]
  · intro R S f x
    apply Subtype.ext
    letI := tower R
    letI := tower S
    have hx := NatTrans.naturality_apply c.hom f x
    change c.hom.app S (mapPoints f x) =
      mapPoints ((restrictTestAlgebra K F).map f) (c.hom.app R x) at hx
    change (w S (mapPoints f x)).val.val =
      (w R x).val.val.map (map f.hom (.id F Q₀))
    rw [hw, hw, hx, hnat]
    exact pointMatrix_natural (R := T R) (S := T S) e f.hom _

end MatrixPoints

end ScalarExtension

section Isotropy

variable {Q : Type u} [Field Q] {n : ℕ}

private theorem extreme_coefficient (H : Mat Q n) (σ : Q ≃+* Q)
    (X : Mat (LaurentPolynomial Q) n) (j : Fin n) (d : ℤ) (hd : d ≠ 0)
    (hbound : (∀ i (m : ℤ), (X i j).coeff m ≠ 0 → m ≤ d) ∨
      (∀ i (m : ℤ), (X i j).coeff m ≠ 0 → d ≤ m))
    (hX : (X.map (AddMonoidAlgebra.mapRingHom ℤ σ.toRingHom)).transpose *
      H.map LaurentPolynomial.C * X = H.map LaurentPolynomial.C) :
    dotProduct (σ ∘ fun i => (X i j).coeff d) (H.mulVec fun i => (X i j).coeff d) = 0 := by
  classical
  let b := AddMonoidAlgebra.mapRingHom ℤ σ.toRingHom
  have hC (p : LaurentPolynomial Q) (a : Q) (m : ℤ) :
      (b p * LaurentPolynomial.C a).coeff m = σ (p.coeff m) * a := by
    rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_mul_single_zero,
      AddMonoidAlgebra.coeff_mapRingHom]
    rfl
  have hprod (i k : Fin n) :
      (b (X i j) * LaurentPolynomial.C (H i k) * X k j).coeff (d + d) =
        σ ((X i j).coeff d) * H i k * (X k j).coeff d := by
    rw [AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd, hC]
    intro a c ha hc hac
    rw [Finsupp.mem_support_iff, hC] at ha
    have ha' : (X i j).coeff a ≠ 0 := by
      intro h
      simp [h] at ha
    have hc' := Finsupp.mem_support_iff.mp hc
    rcases hbound with h | h
    · have h₁ := h i a ha'
      have h₂ := h k c hc'
      exact ⟨by omega, by omega⟩
    · have h₁ := h i a ha'
      have h₂ := h k c hc'
      exact ⟨by omega, by omega⟩
  have h := congrArg (fun M : Mat (LaurentPolynomial Q) n => (M j j).coeff (d + d)) hX
  have hz : d + d ≠ 0 := by omega
  change (((X.map b).transpose * H.map LaurentPolynomial.C * X) j j).coeff (d + d) = _ at h
  have hH0 : ((H.map LaurentPolynomial.C) j j).coeff (d + d) = 0 := by
    simp only [Matrix.map_apply, ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne hz]
  rw [hH0] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at h
  have hh : (∑ k, ∑ i, (b (X i j) * LaurentPolynomial.C (H i k) * X k j).coeff (d + d)) =
      ∑ k, ∑ i, σ ((X i j).coeff d) * H i k * (X k j).coeff d :=
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => hprod i k
  have h' := hh.symm.trans h
  rw [Finset.sum_comm] at h'
  simpa only [dotProduct, Matrix.mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc] using h'

private theorem isotropic_of_nonconstant_laurent (H : Mat Q n) (σ : Q ≃+* Q)
    (X : Mat (LaurentPolynomial Q) n)
    (hX : (X.map (AddMonoidAlgebra.mapRingHom ℤ σ.toRingHom)).transpose *
      H.map LaurentPolynomial.C * X = H.map LaurentPolynomial.C)
    (hn : ∃ i j d, d ≠ (0 : ℤ) ∧ (X i j).coeff d ≠ 0) :
    ∃ x : Fin n → Q, x ≠ 0 ∧ dotProduct (σ ∘ x) (H.mulVec x) = 0 := by
  classical
  obtain ⟨i, j, m, hm, hXm⟩ := hn
  let S := Finset.univ.biUnion fun i => (X i j).coeff.support
  have hS (k : Fin n) (d : ℤ) (h : (X k j).coeff d ≠ 0) : d ∈ S :=
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩
  have hSne : S.Nonempty := ⟨m, hS i m hXm⟩
  have hD : ∃ d ∈ S, d ≠ 0 ∧
      ((∀ z ∈ S, z ≤ d) ∨ (∀ z ∈ S, d ≤ z)) := by
    by_cases hp : 0 < m
    · exact ⟨S.max' hSne, S.max'_mem hSne, (hp.trans_le (S.le_max' _ (hS i m hXm))).ne',
        .inl fun z hz => S.le_max' z hz⟩
    · exact ⟨S.min' hSne, S.min'_mem hSne,
        (lt_of_le_of_lt (S.min'_le _ (hS i m hXm)) (by omega)).ne,
        .inr fun z hz => S.min'_le z hz⟩
  obtain ⟨d, hdS, hd, hb⟩ := hD
  refine ⟨fun i => (X i j).coeff d, ?_, extreme_coefficient H σ X j d hd ?_ hX⟩
  · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hdS
    intro h
    exact (Finsupp.mem_support_iff.mp hk) (congrFun h k)
  · exact hb.imp (fun h i m hm => h m (hS i m hm)) (fun h i m hm => h m (hS i m hm))

open LinearAlgebraicGroups.CocharacterDynamics
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.Specs.Arithmetic.OppositeRadicals (IsNoncentral MultiplicativeGroup)
open private unitEquiv unitEquiv_unitPoint evalLaurent evalLaurent_parameter
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private cocharacterPoint_mul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

private def laurentCentre [Algebra F Q] :
    (LaurentPolynomial F ⊗[F] Q) ≃ₐ[F] LaurentPolynomial Q :=
  (Algebra.TensorProduct.comm F (LaurentPolynomial F) Q).trans
    ((AddMonoidAlgebra.scalarTensorEquiv F Q (M := ℤ)).restrictScalars F)

private theorem laurentCentre_symm_single [Algebra F Q] (d : ℤ) (a : Q) :
    (laurentCentre (F := F) (Q := Q)).symm (AddMonoidAlgebra.single d a) =
      AddMonoidAlgebra.single d (1 : F) ⊗ₜ[F] a := by
  change (Algebra.TensorProduct.comm F (LaurentPolynomial F) Q).symm
    ((AddMonoidAlgebra.scalarTensorEquiv F Q (M := ℤ)).symm (AddMonoidAlgebra.single d a)) = _
  rw [AddMonoidAlgebra.scalarTensorEquiv_symm_single]
  rfl

private theorem laurentCentre_constant [Algebra F Q] (a : Q) :
    laurentCentre (F := F) (Q := Q) (1 ⊗ₜ[F] a) = LaurentPolynomial.C a := by
  apply (laurentCentre (F := F) (Q := Q)).symm.injective
  rw [AlgEquiv.symm_apply_apply, ← LaurentPolynomial.single_eq_C, laurentCentre_symm_single]
  rfl

private theorem laurentCentre_conjugation [Algebra F Q] (σ : Q ≃ₐ[F] Q)
    (z : LaurentPolynomial F ⊗[F] Q) :
    laurentCentre (map (.id (LaurentPolynomial F) (LaurentPolynomial F)) σ.toAlgHom z) =
      AddMonoidAlgebra.mapRingHom ℤ σ.toRingHom (laurentCentre z) := by
  set L := laurentCentre (F := F) (Q := Q)
  let a : LaurentPolynomial Q →+* LaurentPolynomial Q :=
    L.toRingHom.comp ((map (.id (LaurentPolynomial F) (LaurentPolynomial F)) σ.toAlgHom).toRingHom.comp
      L.symm.toRingHom)
  have h : a = AddMonoidAlgebra.mapRingHom ℤ σ.toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro q
      change L (map (.id (LaurentPolynomial F) (LaurentPolynomial F)) σ.toAlgHom
        (L.symm (AddMonoidAlgebra.single 0 q))) = _
      simp only [L, laurentCentre_symm_single, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AddMonoidAlgebra.mapRingHom_single]
      change L (AddMonoidAlgebra.single 0 (1 : F) ⊗ₜ[F] σ q) =
        AddMonoidAlgebra.single 0 (σ q)
      exact (congrArg L (laurentCentre_symm_single (F := F) 0 (σ q)).symm).trans
        (L.apply_symm_apply _)
    · intro m
      change L (map (.id (LaurentPolynomial F) (LaurentPolynomial F)) σ.toAlgHom
        (L.symm (AddMonoidAlgebra.single m 1))) = _
      simp only [L, laurentCentre_symm_single, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        map_one, AddMonoidAlgebra.mapRingHom_single]
      rw [← laurentCentre_symm_single (F := F) m (1 : Q), AlgEquiv.apply_symm_apply]
  have hx := DFunLike.congr_fun h (L z)
  change L (map (.id (LaurentPolynomial F) (LaurentPolynomial F)) σ.toAlgHom
    (L.symm (L z))) = _ at hx
  simpa only [AlgEquiv.symm_apply_apply] using hx

open scoped CategoryTheory.MonObj in
private theorem cocharacter_central_of_trivial_points {G : AffineAlgebraicGroup F}
    (c : Cocharacter G.val) (h : ∀ (R : TestAlgebra F) (s : Rˣ), cocharacterPoint c R s = 1) :
    ¬ IsNoncentral c := by
  have hzero : c.hom.hom = (1 : (MultiplicativeGroup F).X ⟶ G.val.X) := by
    apply hom_ext_of_points
    · exact inferInstanceAs (AlgebraicGeometry.IsAffine
        (AlgebraicGeometry.Spec (CommRingCat.of
          (MonoidAlgebra F (DiagonalizableGroups.IntegerCharacters.{u})))))
    · intro R p
      let s := unitEquiv R p
      have hs : unitPoint R s = p := (unitEquiv R).injective (unitEquiv_unitPoint R s)
      rw [← hs, CategoryTheory.MonObj.comp_one]
      exact h R s
  rintro ⟨T, g, hg⟩
  apply hg
  exact (centralizes_iff c g).mpr fun U a b => by
    rw [hzero, CategoryTheory.MonObj.comp_one]
    exact Commute.one_right _

private theorem cocharacter_isotropic [Algebra F Q] {G : AffineAlgebraicGroup F}
    (c : Cocharacter G.val) (hc : IsNoncentral c)
    (σ : Q ≃ₐ[F] Q) (H : Mat Q n) (hG : RepresentsHermitian σ H G) :
    ∃ x : Fin n → Q, x ≠ 0 ∧ dotProduct (σ ∘ x) (H.mulVec x) = 0 := by
  classical
  obtain ⟨e, hmul, hnat⟩ := hG
  let B : TestAlgebra F := CommAlgCat.of F F
  let R := laurentAlgebra B
  let p := cocharacterPoint c R (laurentParameter B)
  let L := laurentCentre (F := F) (Q := Q)
  let X : Mat (LaurentPolynomial Q) n := (e R p).val.val.map L
  have hX : (X.map (AddMonoidAlgebra.mapRingHom ℤ σ.toRingHom)).transpose *
        H.map LaurentPolynomial.C * X = H.map LaurentPolynomial.C := by
    have h := (e R p).property
    unfold PreservesHermitianMatrix at h
    let j : Q →ₐ[F] R ⊗[F] Q := includeRight
    let M := (e R p).val.val
    let β := conjugationAt σ R
    change ((M.map β).transpose * H.map j * M) = H.map j at h
    have h' := congrArg (fun Y : Mat (R ⊗[F] Q) n => Y.map L) h
    simp only [Matrix.map_mul (f := L)] at h'
    have hj : (H.map j).map L = H.map LaurentPolynomial.C := by
      apply Matrix.ext
      intro i j
      exact laurentCentre_constant (F := F) (H i j)
    have hb : ((M.map β).transpose).map L =
        (X.map (AddMonoidAlgebra.mapRingHom ℤ σ.toRingHom)).transpose := by
      apply Matrix.ext
      intro i j
      exact laurentCentre_conjugation σ (M j i)
    rw [hj, hb] at h'
    exact h'
  apply isotropic_of_nonconstant_laurent H σ.toRingEquiv X hX
  by_contra! hconst
  have hconstant (i j : Fin n) :
      (e R p).val.val i j = (1 : R) ⊗ₜ[F] (X i j).coeff 0 := by
    apply L.injective
    rw [show L ((1 : R) ⊗ₜ[F] (X i j).coeff 0) = LaurentPolynomial.C ((X i j).coeff 0)
      from laurentCentre_constant _]
    change X i j = _
    ext d
    rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single]
    by_cases hd : d = 0
    · subst d
      simp
    · simpa [Finsupp.single_eq_of_ne hd] using hconst i j d hd
  apply cocharacter_central_of_trivial_points c _ hc
  intro S t
  let a : B ⟶ S := CommAlgCat.ofHom (Algebra.ofId F S)
  let f (s : Sˣ) : R ⟶ S := evalLaurent a s
  have hp (s : Sˣ) : mapPoints (f s) p = cocharacterPoint c S s := by
    unfold p cocharacterPoint
    change (((groupPointsFunctor F).obj G.val).map (f s))
        (((groupPointsFunctor F).map c).app R (unitPoint R (laurentParameter B))) = _
    rw [← NatTrans.naturality_apply ((groupPointsFunctor F).map c)]
    congr 1
    change mapPoints (f s) (unitPoint R (laurentParameter B)) = unitPoint S s
    rw [mapPoints_unitPoint, evalLaurent_parameter]
  have hmap (s : Sˣ) (i j : Fin n) :
      (e S (cocharacterPoint c S s)).val.val i j = (1 : S) ⊗ₜ[F] (X i j).coeff 0 := by
    rw [← hp s]
    have h := congrArg (fun y : Matrix.SpecialLinearGroup (Fin n) (S ⊗[F] Q) => y.val i j)
      (hnat (f s) p)
    change _ = map (f s).hom (.id F Q) ((e R p).val.val i j) at h
    rw [h, hconstant, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have heq : cocharacterPoint c S t = cocharacterPoint c S 1 := by
    apply (e S).injective
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    exact (hmap t i j).trans (hmap 1 i j).symm
  rw [heq]
  let y := cocharacterPoint c S 1
  have h1 : y = y * y := by simpa only [one_mul] using cocharacterPoint_mul c S 1 1
  apply mul_left_cancel (a := y)
  exact h1.symm.trans (mul_one y).symm

end Isotropy

open LinearAlgebraicGroups.CocharacterDynamics (cocharacterCentralizerExists)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open LinearAlgebraicGroups.Specs.Unipotent (baseChangedAlgebraicGroup)
open private gm_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private noncentral_extend from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

local instance (priority := 2000) : Algebra E (F ⊗[K] E) := rightAlgebra
attribute [local instance] fieldCentre

set_option maxHeartbeats 1200000 in
theorem unitaryLocalModels : UnitaryLocalModels.{u,v} := by
  intro K E A _ _ _ _ _ _ _ _ _ hA ι _ b star G hG D w
  let F := D.Completion w
  by_cases hj : Nonempty (E →ₐ[K] F)
  · exact .inr (split_model hA b star hG hj.some)
  · let : Fact (IsField (F ⊗[K] E)) := ⟨centre_isField_of_no_embedding (not_nonempty_iff.mp hj)⟩
    let Q := F ⊗[K] E
    let B := Q ⊗[E] A
    let s := localAdjoint (F := F) star
    have hQ : Module.finrank F Q = 2 :=
      (Module.finrank_baseChange ..).trans (Algebra.IsQuadraticExtension.finrank_eq_two K E)
    let : Algebra.IsSeparable F Q := separable_of_quadratic_automorphism hQ s.conjugation s.conjugation_ne
    have hB : isCentralSimple Q B := _root_.RM03.CSA.isCentralSimple_baseChange hA
    have hd : degree Q B = degree E A :=
      congrArg Nat.sqrt (_root_.RM03.CSA.finrank_baseChange (L := Q) hA)
    obtain ⟨e⟩ := completion_splitting D w hQ hB s
    change B ≃ₐ[Q] Mat Q (degree Q B) at e
    rw [hd] at e
    obtain ⟨H, hH, he⟩ := hermitian_matrix s e
    have hr := represents_hermitian hA b star hG e H he
    refine .inl ⟨Q, inferInstance, inferInstance, inferInstance, .refl, hQ,
      s.conjugation, H, s.conjugation_ne, ?_, hH, ?_, hr, ?_⟩
    · intro a
      rfl
    · refine ⟨e, fun a => ?_⟩
      have h := he (1 ⊗ₜ[E] a)
      rw [localAdjoint_one_tmul] at h
      exact h
    · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
      · obtain ⟨Z, hZ⟩ := cocharacterCentralizerExists G c
        obtain ⟨f, _⟩ := gm_baseChange K F
        let c' : Cocharacter (baseChangedAlgebraicGroup F G).val :=
          f.hom ≫ (groupBaseChange K F).map c
        have hc' : IsNoncentral c' := noncentral_extend hc hZ f
        exact cocharacter_isotropic c' hc' s.conjugation H.val hr
      · exact cocharacter_isotropic c hc s.conjugation H.val hr

theorem localModelsForTrivialization : LocalModelsForTrivialization.{u,v} := by
  intro K L _ _ _ _ _ n hn S G s i χ g hg hχ
  obtain ⟨χ', g', β, hg', hu, hβ, _, _, _, hM⟩ :=
    LinearAlgebraicGroups.OuterTypeAModels.typeAModelForTrivialization hn s i
  have hχ' := hu χ g hg
  subst χ'
  obtain ⟨hdeg, hsep, ρ, hρ, hA, hd, star, hstar, hbar, ι, hι, b, hG⟩ := hM.2 hχ
  letI : Algebra.IsQuadraticExtension K (DiagramField χ) := ⟨hdeg⟩
  exact ⟨g', β, hg', hβ, hdeg, hsep, ρ, hρ, hA, hd, star, hstar, hbar, ι, hι, b, hG,
    unitaryLocalModels hA b star G hG⟩

end

end LinearAlgebraicGroups.Arithmetic.OuterTypeALocalModels
