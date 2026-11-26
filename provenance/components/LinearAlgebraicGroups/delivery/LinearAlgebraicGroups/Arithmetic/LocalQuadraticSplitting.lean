import Specs.LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting
import LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.MatrixDivision
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SubfieldSplitting
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.QuaternionSplitting
import MathGenome.Internal.D07.Ch23.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Perfect

/-! Quadratic splitting and embeddings for local quaternion algebras. The
embedding proof lifts a quadratic generator into the cyclic division model.
The degree of a splitting field is controlled by its split column module. -/

open scoped TensorProduct Matrix.Module WithZero Pointwise
open _root_.Specs.RM03.CSA (baseChange degree isCentralDivision isCentralSimple splits isSplit)

namespace LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

open LocalDivisionAlgebras ValuativeRel
open LocalDivisionRamification (normalizedValuation)

universe u v w

private def matrixOne {F D : Type*} [Field F] [Ring D] [Algebra F D] :
    Matrix (Fin 1) (Fin 1) D ≃ₐ[F] D where
  toFun M := M 0 0
  invFun d := fun _ _ => d
  left_inv M := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  right_inv _ := rfl
  map_mul' _ _ := by simp [Matrix.mul_apply]
  map_add' _ _ := rfl
  commutes' _ := by simp [Matrix.algebraMap_matrix_apply]

/-- The split column module has dimension twice the extension degree over the
base field. In degree two it has division-algebra rank one, and the commuting
scalar action gives right multiplication. -/
theorem splitting_degree : SplittingDegree.{u,v,w} := by
  intro F _ B _ _ E _ _ _ hB hd hs
  have hS := RM03.CSA.isCentralSimple_of_isCentralDivision F B hB
  obtain ⟨n, _, ⟨e⟩⟩ := hs
  have hn : n = 2 := (RM03.CSA.degree_eq_matrix_size hS e).symm.trans hd
  subst n
  let ρ : B →ₐ[F] Matrix (Fin 2) (Fin 2) E :=
    (e.toAlgHom.restrictScalars F).comp Algebra.TensorProduct.includeRight
  let V := Fin 2 → E
  let : Module B V := Module.compHom V ρ.toRingHom
  have hact (b : B) (x : V) : b • x = ρ b • x := rfl
  let : IsScalarTower F B V := ⟨fun a b x => by
    change ρ (a • b) • x = a • (ρ b • x)
    rw [map_smul, smul_assoc]⟩
  have hV : Module.finrank F V = 2 * Module.finrank F E := by
    simp [V, Module.finrank_pi_fintype, two_mul]
  have hBdim : Module.finrank F B = 4 := by
    change RM03.CSA.degree _ _ = 2 at hd
    simpa [hd] using RM03.CSA.finrank_eq_degree_sq hS
  have hr := Module.finrank_mul_finrank F B V
  rw [hV, hBdim] at hr
  refine ⟨⟨Module.finrank B V, by omega⟩, fun he => ?_⟩
  have hv : Module.finrank B V = 1 := by omega
  obtain ⟨j⟩ := (Module.nonempty_linearEquiv_iff_finrank_eq_one (R := B) (M := V)).2 hv
  let z : V := j 1
  have hc (a : E) (b : B) (x : V) : a • (b • x) = b • (a • x) := by
    rw [hact, hact]
    exact smul_comm a (ρ b) x
  let f : E → B := fun a => j.symm (a • z)
  have hf (a : E) : j (f a) = a • z := j.apply_symm_apply _
  have hfj (b : B) : j b = b • z := by
    simpa [z] using j.map_smul b (1 : B)
  have hop (a b : E) : f (a * b) = f b * f a := by
    apply j.injective
    calc
      j (f (a * b)) = a • (b • z) := (hf _).trans (mul_smul a b z)
      _ = a • (f b • z) := by rw [← hfj, hf]
      _ = f b • (a • z) := hc a (f b) z
      _ = j (f b * f a) := by
        rw [← hf a]
        exact (j.map_smul (f b) (f a)).symm
  exact ⟨{
    toFun := f
    map_zero' := by apply j.injective; rw [hf, zero_smul, map_zero]
    map_one' := by apply j.injective; rw [hf, one_smul]
    map_add' := fun a b => by apply j.injective; rw [hf, add_smul, map_add, hf, hf]
    map_mul' := fun a b => by rw [mul_comm a b, hop]
    commutes' := fun a => by
      apply j.injective
      rw [hf, hfj]
      exact (algebraMap_smul E a z).trans (algebraMap_smul B a z).symm }⟩

theorem odd_extension_division : OddExtensionDivision.{u,v,w} := by
  intro F _ B _ _ E _ _ _ hB hd hodd
  have hS := RM03.CSA.isCentralSimple_of_isCentralDivision F B hB
  have hT : RM03.CSA.IsCentralSimple E (baseChange F E B) :=
    RM03.CSA.isCentralSimple_baseChange hS
  have hdT : RM03.CSA.degree E (baseChange F E B) = 2 := by
    change Nat.sqrt (Module.finrank E (baseChange F E B)) = 2
    rw [RM03.CSA.finrank_baseChange hS]
    exact hd
  obtain ⟨n, D, _, _, hD, hn, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation _ _ hT
  have hD' := RM03.CSA.isCentralSimple_of_isCentralDivision E D hD
  have hmul := RM03.CSA.degree_matrix_division hT hD hn e
  rw [hdT] at hmul
  have hp := RM03.CSA.degree_pos hD'
  have hnle : n ≤ 2 := by nlinarith
  have hnone : n = 1 := by
    by_contra h
    have hn2 : n = 2 := by omega
    subst n
    have hdeg : RM03.CSA.degree E D = 1 := by omega
    have hdim : Module.finrank E D = 1 := by
      simpa [hdeg] using RM03.CSA.finrank_eq_degree_sq hD'
    obtain ⟨d⟩ := (Module.nonempty_algEquiv_iff_finrank_eq_one (R := E) (S := D)).2 hdim
    have hs : splits F E B :=
      ⟨2, by decide, ⟨e.trans (d.symm.mapMatrix (m := Fin 2))⟩⟩
    have heven := (splitting_degree hB hd hs).1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr heven)
  subst n
  let e' := e.trans (matrixOne)
  refine ⟨e'.symm.injective.nontrivial, fun x hx => ?_⟩
  have hne : e' x ≠ 0 := fun h => hx (e'.injective (h.trans e'.map_zero.symm))
  simpa using (isUnit_iff_ne_zero.mpr hne).map e'.symm.toMonoidHom

theorem complex_splitting : ComplexSplitting.{v} := by
  intro A _ _ hA hd
  have hT := RM03.CSA.isCentralSimple_baseChange (L := ℂ) hA
  let := hT.1
  let := hT.2.2
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed ℂ
    (baseChange ℝ ℂ A)
  have hn : n = 2 := (RM03.CSA.degree_eq_matrix_size hA e).symm.trans hd
  subst n
  exact ⟨e⟩

theorem real_division : RealDivision.{v} := by
  intro B _ _ hB hd
  have hS := RM03.CSA.isCentralSimple_of_isCentralDivision ℝ B hB
  have hdim : Module.finrank ℝ B = 4 := by
    change RM03.CSA.degree _ _ = 2 at hd
    simpa [hd] using RM03.CSA.finrank_eq_degree_sq hS
  let := hB.2
  obtain ⟨n, hn, _⟩ := D07.Ch23.Frobenius.finiteDimensionalClassification B
  obtain ⟨e⟩ : Nonempty (B ≃ₐ[ℝ] Quaternion ℝ) := by
    rcases hn with ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
    · have h := e.toLinearEquiv.finrank_eq
      simp [hdim] at h
    · have h := e.toLinearEquiv.finrank_eq
      simp [hdim, Complex.finrank_real_complex] at h
    · exact ⟨e.symm⟩
  obtain ⟨i, _, _, _, _, _, _⟩ := RM03.Brauer.QuaternionSplitting.complex_subfield
  let j := e.symm.toAlgHom.comp i
  refine ⟨⟨e⟩, ⟨j, ?_⟩, complex_splitting hS hd⟩
  let ej := AlgEquiv.ofInjective j j.injective
  have hf : IsField j.range :=
    ej.symm.toRingEquiv.toMulEquiv.isField (Field.toIsField ℂ)
  have hdeg : Module.finrank ℝ j.range = RM03.CSA.degree ℝ B :=
    ej.toLinearEquiv.finrank_eq.symm.trans (Complex.finrank_real_complex.trans hd.symm)
  exact (RM03.CSA.maximal_subfield_iff_centralizer_eq hB _ hf).1
    ((RM03.CSA.maximal_subfield_iff_degree hB _ hf).2 hdeg)

private theorem splittingOfEmbedding (hembed : QuadraticEmbedding.{u,v,w}) :
    QuadraticSplitting.{u,v,w} := by
  intro F _ _ _ _ A _ _ E _ _ _ hA hd hE
  obtain ⟨n, D, _, _, hD, hn, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation F A hA
  have hD' := RM03.CSA.isCentralSimple_of_isCentralDivision F D hD
  have hmul := RM03.CSA.degree_matrix_division hA hD hn e
  change RM03.CSA.degree F A = 2 at hd
  rw [hd] at hmul
  have hp := RM03.CSA.degree_pos hD'
  have hnle : n ≤ 2 := by nlinarith
  rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
  · let e' := e.trans (matrixOne)
    have hdD : degree F D = 2 := by change RM03.CSA.degree F D = 2; omega
    obtain ⟨i⟩ := hembed hD hdD hE
    have hdeg : Module.finrank F E = RM03.CSA.degree F D := hE.trans hdD.symm
    obtain ⟨s⟩ := RM03.CSA.subfield_splits i hD hdeg
    rw [show RM03.CSA.degree F D = 2 from hdD] at s
    exact ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E) e').trans s⟩
  · have hdD : RM03.CSA.degree F D = 1 := by omega
    have hdim : Module.finrank F D = 1 := by
      simpa [hdD] using RM03.CSA.finrank_eq_degree_sq hD'
    obtain ⟨d⟩ := (Module.nonempty_algEquiv_iff_finrank_eq_one (R := F) (S := D)).2 hdim
    let e' := e.trans (d.symm.mapMatrix (m := Fin 2))
    let f : A →ₐ[F] Matrix (Fin 2) (Fin 2) E :=
      ((Algebra.ofId F E).mapMatrix (m := Fin 2)).comp e'.toAlgHom
    let g := AlgHom.liftEquiv F E A (Matrix (Fin 2) (Fin 2) E) f
    have hT := RM03.CSA.isCentralSimple_baseChange (L := E) hA
    let := hT.1
    have hg : Function.Injective g := g.toRingHom.injective
    have hdim' : Module.finrank E (baseChange F E A) =
        Module.finrank E (Matrix (Fin 2) (Fin 2) E) := by
      rw [RM03.CSA.finrank_baseChange hA, e'.toLinearEquiv.finrank_eq]
      simp [Module.finrank_matrix]
    let e'' := LinearEquiv.ofInjectiveOfFinrankEq g.toLinearMap hg hdim'
    exact ⟨AlgEquiv.ofBijective g ⟨hg, e''.surjective⟩⟩

open Polynomial

private noncomputable def quadratic {R : Type*} [CommRing R] (b c : R) : R[X] :=
  X ^ 2 + C b * X + C c

private theorem quadratic_monic {R : Type*} [CommRing R] [Nontrivial R] (b c : R) :
    (quadratic b c).Monic := by
  have h : (C b * X + C c : R[X]).degree < (X ^ 2 : R[X]).degree := by
    rw [degree_X_pow]
    apply (degree_add_le _ _).trans_lt
    apply max_lt
    · exact (degree_mul_le _ _).trans_lt (by
        grw [degree_C_le, degree_X]; decide)
    · exact degree_C_le.trans_lt (by decide)
  rw [quadratic, add_assoc]
  exact (monic_X_pow 2).add_of_left h

private theorem quadratic_natDegree {R : Type*} [CommRing R] [Nontrivial R] (b c : R) :
    (quadratic b c).natDegree = 2 := by
  have h : (C b * X + C c : R[X]).natDegree < (X ^ 2 : R[X]).natDegree := by
    rw [natDegree_X_pow]
    apply (natDegree_add_le _ _).trans_lt
    apply max_lt
    · have h₁ : (C b * X : R[X]).natDegree ≤ 1 := by
        exact natDegree_mul_le.trans (by simp)
      omega
    · simp
  rw [quadratic, add_assoc, natDegree_add_eq_left_of_natDegree_lt h, natDegree_X_pow]

private theorem quadratic_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (b c : R) :
    (quadratic b c).map f = quadratic (f b) (f c) := by simp [quadratic]

private theorem quadratic_aeval {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    (b c : R) (x : S) :
    aeval x (quadratic b c) = x ^ 2 + algebraMap R S b * x + algebraMap R S c := by
  simp [quadratic]

private theorem quadratic_derivative {R : Type*} [CommRing R] (b c : R) :
    (quadratic b c).derivative = C 2 * X + C b := by
  simp [quadratic, derivative_mul]
  rw [map_ofNat]
  norm_num

private theorem liftSimpleRoot {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (f : R[X]) (hf : f.Monic)
    (x : IsLocalRing.ResidueField R) (hx : aeval x f = 0)
    (h'x : aeval x f.derivative ≠ 0) :
    ∃ y : R, f.IsRoot y ∧ IsLocalRing.residue R y = x := by
  obtain ⟨x₀, rfl⟩ := IsLocalRing.residue_surjective (R := R) x
  rw [aeval_def, IsLocalRing.ResidueField.algebraMap_eq, eval₂_at_apply] at hx h'x
  obtain ⟨y, hy, hyx⟩ := HenselianRing.is_henselian f hf x₀
    (Ideal.Quotient.eq_zero_iff_mem.mp hx) (isUnit_iff_ne_zero.mpr h'x)
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hyx
  change IsLocalRing.residue R (y - x₀) = 0 at h
  exact ⟨y, hy, sub_eq_zero.mp (by simpa only [map_sub] using h)⟩

private noncomputable def quadraticLift {F A : Type*} [Field F] [Ring A] [Algebra F A]
    {b c : F} {x : A} (hx : aeval x (quadratic b c) = 0) :
    QuadraticAlgebra F (-c) (-b) →ₐ[F] A :=
  QuadraticAlgebra.lift ⟨x, by
    rw [quadratic_aeval] at hx
    have hx' : x * x + (algebraMap F A b * x + algebraMap F A c) = 0 := by
      simpa only [pow_two, ← add_assoc] using hx
    calc
      x * x = -(algebraMap F A b * x + algebraMap F A c) := eq_neg_iff_add_eq_zero.mpr hx'
      _ = _ := by simp [Algebra.smul_def, neg_add_rev]⟩

private noncomputable def quadraticEquiv {F E : Type*} [Field F] [Field E] [Algebra F E]
    (hd : Module.finrank F E = 2) {b c : F} {x : E}
    (hxs : x ∉ Set.range (algebraMap F E)) (hx : aeval x (quadratic b c) = 0) :
    QuadraticAlgebra F (-c) (-b) ≃ₐ[F] E := by
  let f := quadraticLift hx
  let : Module.Finite F E := Module.finite_of_finrank_eq_succ hd
  have hinj : Function.Injective f.toLinearMap := LinearMap.ker_eq_bot.mp (by
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    change f z = 0 at hz
    change z.re • (1 : E) + z.im • x = 0 at hz
    simp only [Algebra.smul_def, mul_one] at hz
    have him : z.im = 0 := by
      by_contra hn
      apply hxs
      refine ⟨-z.re / z.im, ?_⟩
      rw [map_div₀, map_neg, div_eq_iff (map_ne_zero_iff _ (algebraMap F E).injective |>.2 hn)]
      linear_combination -hz
    have hre : z.re = 0 := by
      simp [him] at hz
      exact (algebraMap F E).injective (by simpa using hz)
    ext <;> assumption)
  have hd' : Module.finrank F (QuadraticAlgebra F (-c) (-b)) = Module.finrank F E := by
    rw [QuadraticAlgebra.finrank_eq_two, hd]
  exact AlgEquiv.ofBijective f ⟨hinj, (LinearEquiv.ofInjectiveOfFinrankEq f.toLinearMap hinj hd').surjective⟩

private theorem embedOfRoot {F E B : Type*} [Field F] [Field E] [Algebra F E]
    [Ring B] [Algebra F B] (hd : Module.finrank F E = 2) {b c : F}
    {x : E} (hxs : x ∉ Set.range (algebraMap F E)) (hx : aeval x (quadratic b c) = 0)
    {y : B} (hy : aeval y (quadratic b c) = 0) : Nonempty (E →ₐ[F] B) :=
  ⟨(quadraticLift hy).comp (quadraticEquiv hd hxs hx).symm.toAlgHom⟩

section Normalize

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {E : Type*} [Field E] [Algebra F E]

private def IntegralQuadraticGenerator (b c : Integers F) : Prop :=
  ∃ x : E, x ∉ Set.range (algebraMap F E) ∧ aeval x (quadratic (b : F) (c : F)) = 0

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem initialIntegralGenerator (hd : Module.finrank F E = 2) :
    ∃ b c : Integers F, IntegralQuadraticGenerator (E := E) F b c := by
  let : Algebra.IsQuadraticExtension F E := ⟨hd⟩
  obtain ⟨a, b, ⟨e⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := F) (A := E)
  let x := e.symm QuadraticAlgebra.omega
  have hxs : x ∉ Set.range (algebraMap F E) := by
    rintro ⟨y, hy⟩
    have h := congrArg QuadraticAlgebra.im ((e.commutes y).symm.trans (congrArg e hy))
    simp [x] at h
  have hx : x ^ 2 = algebraMap F E a + algebraMap F E b * x := by
    apply e.injective
    simp [x, pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  obtain ⟨a₀, a₁, ha₁, ha⟩ := IsFractionRing.div_surjective (Integers F) a
  obtain ⟨b₀, b₁, hb₁, hb⟩ := IsFractionRing.div_surjective (Integers F) b
  let d : Integers F := a₁ * b₁
  have ha₁' : (a₁ : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero ha₁
  have hb₁' : (b₁ : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb₁
  have hd₀ : (d : F) ≠ 0 := mul_ne_zero ha₁' hb₁'
  have hbd : b * (d : F) = (b₀ * a₁ : Integers F) := by
    rw [← hb]
    change (b₀ : F) / (b₁ : F) * ((a₁ : F) * (b₁ : F)) = (b₀ : F) * (a₁ : F)
    field_simp [hb₁']
  have had : a * (d : F) ^ 2 = (a₀ * a₁ * b₁ ^ 2 : Integers F) := by
    rw [← ha]
    change (a₀ : F) / (a₁ : F) * ((a₁ : F) * (b₁ : F)) ^ 2 =
      (a₀ : F) * (a₁ : F) * (b₁ : F) ^ 2
    field_simp [ha₁']
  refine ⟨-(b₀ * a₁), -(a₀ * a₁ * b₁ ^ 2), algebraMap F E (d : F) * x, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    apply hxs
    refine ⟨y / (d : F), ?_⟩
    rw [map_div₀, div_eq_iff (map_ne_zero_iff _ (algebraMap F E).injective |>.2 hd₀)]
    simpa [mul_comm] using hy
  · rw [quadratic_aeval]
    change _ + algebraMap F E (-((b₀ * a₁ : Integers F) : F)) * _ +
      algebraMap F E (-((a₀ * a₁ * b₁ ^ 2 : Integers F) : F)) = 0
    rw [← hbd, ← had, map_neg, map_neg, map_mul, map_mul, map_pow]
    linear_combination (algebraMap F E (d : F)) ^ 2 * hx

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem generatorMinpoly (hd : Module.finrank F E = 2) {b c : F} {x : E}
    (hxs : x ∉ Set.range (algebraMap F E)) (hx : aeval x (quadratic b c) = 0) :
    quadratic b c = minpoly F x := by
  let : Module.Finite F E := Module.finite_of_finrank_eq_succ hd
  have hxp := Algebra.IsIntegral.isIntegral (R := F) x
  have hnd : (minpoly F x).natDegree = 2 := by
    have h1 := (minpoly.two_le_natDegree_iff hxp).2 hxs
    have h2 : (minpoly F x).natDegree ≤ 2 := hd ▸ minpoly.natDegree_le x
    omega
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxp) (quadratic_monic b c)
    (minpoly.dvd F x hx) (by rw [quadratic_natDegree, hnd])

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem generatorDiscriminantNeZero [Algebra.IsSeparable F E]
    (hd : Module.finrank F E = 2) {b c : Integers F}
    (h : IntegralQuadraticGenerator (E := E) F b c) : b ^ 2 - 4 * c ≠ 0 := by
  obtain ⟨x, hxs, hx⟩ := h
  have hsep : (quadratic (b : F) (c : F)).Separable := by
    rw [generatorMinpoly F hd hxs hx]
    exact Algebra.IsSeparable.isSeparable F x
  have hd' := hsep.aeval_derivative_ne_zero hx
  rw [quadratic_derivative] at hd'
  simp only [map_add, map_mul, aeval_C, aeval_X, map_ofNat] at hd'
  rw [quadratic_aeval] at hx
  intro hn
  let i : Integers F →+* E := (algebraMap F E).comp (valuation F).valuationSubring.subtype
  have hn' : (i b) ^ 2 - 4 * i c = 0 := by
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_zero] using congrArg i hn
  have hz : (2 * x + algebraMap F E (b : F)) ^ 2 = 0 := by
    change (2 * x + i b) ^ 2 = 0
    change x ^ 2 + i b * x + i c = 0 at hx
    linear_combination 4 * hx + hn'
  exact hd' (eq_zero_of_pow_eq_zero hz)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem generatorNoScalarRoot {b c : Integers F}
    (h : IntegralQuadraticGenerator (E := E) F b c) (y : Integers F) :
    ¬ (quadratic b c).IsRoot y := by
  obtain ⟨x, hxs, hx⟩ := h
  intro hy
  rw [quadratic_aeval] at hx
  have hy' : (algebraMap F E (y : F)) ^ 2 + algebraMap F E (b : F) *
      algebraMap F E (y : F) + algebraMap F E (c : F) = 0 := by
    have h₀ : y ^ 2 + b * y + c = 0 := by simpa [Polynomial.IsRoot, quadratic] using hy
    let i : Integers F →+* E := (algebraMap F E).comp (valuation F).valuationSubring.subtype
    change (i y) ^ 2 + i b * i y + i c = 0
    simpa only [map_add, map_mul, map_pow, map_zero] using congrArg i h₀
  have hfac : (x - algebraMap F E (y : F)) *
      (x + algebraMap F E (b : F) + algebraMap F E (y : F)) = 0 := by
    linear_combination hx - hy'
  rcases mul_eq_zero.mp hfac with h₁ | h₂
  · exact hxs ⟨(y : F), (sub_eq_zero.mp h₁).symm⟩
  · apply hxs
    refine ⟨-(b : F) - (y : F), ?_⟩
    rw [map_sub, map_neg]
    linear_combination -h₂

/-- Minimize the discriminant valuation over integral quadratic generators.
A repeated residue root can be translated to zero. If the translated constant
is divisible by the square of the uniformizer, dividing the generator by the
uniformizer would lower the discriminant valuation. -/
private theorem normalizedGenerator [Algebra.IsSeparable F E]
    (hd : Module.finrank F E = 2) (π : Integers F) (hπ : Irreducible π) :
    ∃ b c : Integers F, IntegralQuadraticGenerator (E := E) F b c ∧
      ((∀ x : BaseResidue F, aeval x (quadratic b c) ≠ 0) ∨
        (π ∣ b) ∧ (π ∣ c) ∧ ¬ π ^ 2 ∣ c) := by
  classical
  let R := Integers F
  let P (n : ℕ) := ∃ b c : R, IntegralQuadraticGenerator (E := E) F b c ∧
    IsDiscreteValuationRing.addVal R (b ^ 2 - 4 * c) = n
  have hn : ∃ n, P n := by
    obtain ⟨b, c, hbc⟩ := initialIntegralGenerator F hd
    obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (generatorDiscriminantNeZero F hd hbc) hπ
    exact ⟨n, b, c, hbc, IsDiscreteValuationRing.addVal_def _ e hπ n he⟩
  obtain ⟨b, c, hbc, hv⟩ := Nat.find_spec hn
  by_cases h : ∀ x : BaseResidue F, aeval x (quadratic b c) ≠ 0
  · exact ⟨b, c, hbc, Or.inl h⟩
  push Not at h
  obtain ⟨x, hx⟩ := h
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
    inferInstanceAs (IsAdicComplete (IsLocalRing.maximalIdeal (Valuation.integer (valuation F)))
      (Valuation.integer (valuation F)))
  have hx' : aeval x (quadratic b c).derivative = 0 := by
    by_contra hne
    obtain ⟨y, hy, -⟩ := liftSimpleRoot _ (quadratic_monic b c) x hx hne
    exact generatorNoScalarRoot F hbc y hy
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective (R := R) x
  let b' := b + 2 * s
  let c' := s ^ 2 + b * s + c
  have hb' : π ∣ b' := by
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq, ← Ideal.Quotient.eq_zero_iff_mem]
    change IsLocalRing.residue R b' = 0
    rw [quadratic_derivative] at hx'
    simp only [map_add, map_mul, aeval_C, aeval_X] at hx'
    change IsLocalRing.residue R 2 * IsLocalRing.residue R s + IsLocalRing.residue R b = 0 at hx'
    simpa only [b', map_add, map_mul, add_comm] using hx'
  have hc' : π ∣ c' := by
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq, ← Ideal.Quotient.eq_zero_iff_mem]
    change IsLocalRing.residue R c' = 0
    rw [quadratic_aeval] at hx
    change IsLocalRing.residue R s ^ 2 + IsLocalRing.residue R b *
      IsLocalRing.residue R s + IsLocalRing.residue R c = 0 at hx
    simpa only [c', map_add, map_mul, map_pow] using hx
  let i : R →+* E := (algebraMap F E).comp (valuation F).valuationSubring.subtype
  have hbc' : IntegralQuadraticGenerator (E := E) F b' c' := by
    obtain ⟨z, hz, hz'⟩ := hbc
    refine ⟨z - algebraMap F E (s : F), ?_, ?_⟩
    · rintro ⟨r, hr⟩
      apply hz
      refine ⟨r + (s : F), ?_⟩
      rw [map_add, hr, sub_add_cancel]
    · rw [quadratic_aeval] at hz' ⊢
      change (z - i s) ^ 2 + i b' * (z - i s) + i c' = 0
      change z ^ 2 + i b * z + i c = 0 at hz'
      simp only [b', c', map_add, map_mul, map_pow, map_ofNat]
      linear_combination hz'
  by_cases hdiv : π ^ 2 ∣ c'
  swap
  · exact ⟨b', c', hbc', Or.inr ⟨hb', hc', hdiv⟩⟩
  obtain ⟨b₀, hb₀⟩ := hb'
  obtain ⟨c₀, hc₀⟩ := hdiv
  have hdisc : b ^ 2 - 4 * c = π ^ 2 * (b₀ ^ 2 - 4 * c₀) := by
    calc
      _ = b' ^ 2 - 4 * c' := by dsimp [b', c']; ring
      _ = _ := by rw [hb₀, hc₀]; ring
  have hp : (π : F) ≠ 0 := by exact_mod_cast hπ.ne_zero
  have hpE : algebraMap F E (π : F) ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).2 hp
  have hbc₀ : IntegralQuadraticGenerator (E := E) F b₀ c₀ := by
    obtain ⟨z, hz, hz'⟩ := hbc'
    refine ⟨z / algebraMap F E (π : F), ?_, ?_⟩
    · rintro ⟨r, hr⟩
      apply hz
      use r * (π : F)
      rw [map_mul, hr, div_mul_cancel₀ _ hpE]
    · rw [quadratic_aeval] at hz' ⊢
      change (z / i π) ^ 2 + i b₀ * (z / i π) + i c₀ = 0
      change z ^ 2 + i b' * z + i c' = 0 at hz'
      rw [hb₀, hc₀, map_mul, map_mul, map_pow] at hz'
      change i π ≠ 0 at hpE
      field_simp
      linear_combination hz'
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (generatorDiscriminantNeZero F hd hbc₀) hπ
  have hv₀ := IsDiscreteValuationRing.addVal_def _ e hπ n he
  have hsmall := Nat.find_min' hn (show P n from ⟨b₀, c₀, hbc₀, hv₀⟩)
  rw [hdisc, IsDiscreteValuationRing.addVal_mul, hπ.addVal_pow, hv₀, ← Nat.cast_add] at hv
  have heq : Nat.find hn = 2 + n := by exact_mod_cast hv.symm
  omega

end Normalize

section IntegerRings

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem base_le {x y : F} : baseValue F x ≤ baseValue F y ↔
    valuation F x ≤ valuation F y :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toOrderIso.le_iff_le

private theorem base_lt {x y : F} : baseValue F x < baseValue F y ↔
    valuation F x < valuation F y :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toOrderIso.lt_iff_lt

private theorem base_one : baseValue F (1 : F) = 1 := map_one (normalizedValuation F)

private theorem exp_neg_one_lt_one : WithZero.exp (-1 : ℤ) < 1 := by simp

private theorem lt_one_iff_le_uniformizer (γ : ℤᵐ⁰) :
    γ < 1 ↔ γ ≤ WithZero.exp (-1) := by
  by_cases h : γ = 0
  · subst γ
    simp
  · rw [← WithZero.exp_log h, WithZero.exp_lt_one_iff, WithZero.exp_le_exp]
    omega

private theorem parameterIntegral {t : F} (ht : baseValue F t = WithZero.exp (-1)) :
    t ∈ Integers F :=
  base_le.mp (by rw [ht, base_one]; exact exp_neg_one_lt_one.le)

private theorem parameterIrreducible {t : F} (ht : baseValue F t = WithZero.exp (-1)) :
    Irreducible (⟨t, parameterIntegral ht⟩ : Integers F) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext a
  rw [Valuation.mem_maximalIdeal_iff, Ideal.mem_span_singleton,
    (Valuation.valuationSubring.integers (valuation F)).dvd_iff_le]
  change valuation F (a : F) < 1 ↔ valuation F (a : F) ≤ valuation F t
  rw [← map_one (valuation F), ← base_lt, ← base_le, base_one, ht]
  exact lt_one_iff_le_uniformizer _

private theorem congruencePrincipal {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    {I : Ideal R} {π : R} (hI : I = Ideal.span {π}) (n : ℕ) (x y : N) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R N)] ↔ ∃ z : N, π ^ n • z = x - y := by
  rw [SModEq.sub_mem, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem adicCompletePair {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} [IsAdicComplete I R] (π : R) (hI : I = Ideal.span {π})
    (e : M ≃ₗ[R] R × R) : IsAdicComplete I M := by
  have h₂ (n : ℕ) (x y : M) :
      x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
        (e x).1 ≡ (e y).1 [SMOD (I ^ n • ⊤ : Submodule R R)] ∧
        (e x).2 ≡ (e y).2 [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    simp only [congruencePrincipal hI]
    constructor
    · rintro ⟨z, hz⟩
      have he := congrArg e hz
      rw [map_smul, map_sub] at he
      exact ⟨⟨(e z).1, congrArg Prod.fst he⟩, ⟨(e z).2, congrArg Prod.snd he⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨e.symm (a, b), e.injective ?_⟩
      rw [map_smul, e.apply_symm_apply, map_sub]
      exact Prod.ext ha hb
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply e.injective
    refine Prod.ext ?_ ?_
    · simp only [map_zero, Prod.fst_zero]
      apply IsHausdorff.haus' (I := I)
      intro n
      simpa using ((h₂ n x 0).1 (hx n)).1
    · simp only [map_zero, Prod.snd_zero]
      apply IsHausdorff.haus' (I := I)
      intro n
      simpa using ((h₂ n x 0).1 (hx n)).2
  · intro f hf
    obtain ⟨a, ha⟩ := IsPrecomplete.prec' (I := I) (fun n => (e (f n)).1)
      (fun h => ((h₂ _ _ _).1 (hf h)).1)
    obtain ⟨b, hb⟩ := IsPrecomplete.prec' (I := I) (fun n => (e (f n)).2)
      (fun h => ((h₂ _ _ _).1 (hf h)).2)
    exact ⟨e.symm (a, b), fun n => (h₂ _ _ _).2 (by simpa using And.intro (ha n) (hb n))⟩

end IntegerRings

private theorem autsTwo {G : Type*} [Group G] [Fintype G] (hc : Nat.card G = 2)
    (s : G) (hs : s ≠ 1) [DecidableEq G] :
    (Finset.univ : Finset G) = {1, s} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hc, Finset.card_insert_of_notMem]
  · simp
  · simpa using hs.symm

section LocalPresentation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B]

private theorem obtainPresentation (hB : isCentralSimple F B) :
    ∃ (wB : Valuation B ℤᵐ⁰) (r : ResidueData (F := F) wB),
        letI := r.isField.toField
        letI := r.algebra
        Module.finrank (BaseResidue F) (ResidueRing wB) = degree F B ∧
          Nonempty (CyclicPresentation wB r) := by
  obtain ⟨wB, hwB, _⟩ := valuation_exists hB
  obtain ⟨r⟩ := residue_field hB wB hwB
  exact ⟨wB, r, (cyclic_structure hB wB hwB r).2⟩

private def ResidueAsField {wB : Valuation B ℤᵐ⁰} (_ : ResidueData (F := F) wB) : Type v :=
  ResidueRing wB

variable {wB : Valuation B ℤᵐ⁰} {r : ResidueData (F := F) wB}
  (p : CyclicPresentation wB r)

noncomputable section

-- The quotient ring and the field extension of its structure have definitionally
-- equal additive operations. Instance search needs to unfold those operations
-- when using the same algebra structure through the field interface.
set_option backward.isDefEq.respectTransparency false

local notation "k" => BaseResidue F
local notation "l" => ResidueAsField r
local instance : Field l := r.isField.toField
local instance : Algebra k l := r.algebra
local instance : Finite k :=
  inferInstanceAs (Finite (IsLocalRing.ResidueField (Valuation.integer (valuation F))))
local instance : Fintype k := Fintype.ofFinite k
local instance : Field p.L := p.fieldL
local instance : Algebra F p.L := p.algebraL
local instance : IsGalois F p.L := p.galois
local instance : Finite l := r.finite
local instance : FiniteDimensional k l := Module.Finite.of_finite

private def integerInclusion :
    Integers F →+* p.vL.valuationSubring where
  toFun a := ⟨algebraMap F p.L (a : F), by
    change p.vL (algebraMap F p.L (a : F)) ≤ 1
    rw [p.base_value, ← base_one (F := F)]
    exact base_le.mpr a.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

private def residueInclusion : p.vL.valuationSubring →+* l :=
  p.residueEquiv.toRingHom.comp (IsLocalRing.residue _)

private theorem residueInclusion_surjective : Function.Surjective (residueInclusion p) :=
  p.residueEquiv.surjective.comp IsLocalRing.residue_surjective

private theorem residueInclusion_eq_zero (a : p.vL.valuationSubring) :
    residueInclusion p a = 0 ↔ p.vL (a : p.L) < 1 := by
  change p.residueEquiv (IsLocalRing.residue _ a) = 0 ↔ _
  rw [map_eq_zero_iff p.residueEquiv p.residueEquiv.injective, IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff p.L p.vL

private theorem residueInclusion_base (a : Integers F) :
    residueInclusion p (integerInclusion p a) =
      algebraMap (BaseResidue F) l (IsLocalRing.residue _ a) :=
  p.residue_scalar a (integerInclusion p a) rfl

private theorem involutionSquare (hd : degree F B = 2) : p.τ ^ 2 = 1 := by
  let : Module.Finite F p.L := Module.finite_of_finrank_eq_succ (p.degree.trans hd)
  have hc : Nat.card (p.L ≃ₐ[F] p.L) = 2 := by
    exact (IsGalois.card_aut_eq_finrank F p.L).trans (p.degree.trans hd)
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [← hc]
  exact orderOf_dvd_natCard p.τ

private theorem involution_ne_one (hd : degree F B = 2) : p.τ ≠ 1 := by
  let : Module.Finite F p.L := Module.finite_of_finrank_eq_succ (p.degree.trans hd)
  intro h
  have hf : Nat.card (p.L ≃ₐ[F] p.L) = 2 := by
    exact (IsGalois.card_aut_eq_finrank F p.L).trans (p.degree.trans hd)
  have hsub : (⊥ : Subgroup (p.L ≃ₐ[F] p.L)) = ⊤ := by
    simpa [h] using p.gen
  have he : ∀ q : p.L ≃ₐ[F] p.L, q = 1 := fun q => by
    have hq : q ∈ (⊤ : Subgroup (p.L ≃ₐ[F] p.L)) := Subgroup.mem_top q
    simpa [← hsub] using hq
  let : Subsingleton (p.L ≃ₐ[F] p.L) := ⟨fun a b => (he a).trans (he b).symm⟩
  rw [Nat.card_unique] at hf
  contradiction

private theorem norm_pair (hd : degree F B = 2) (a : p.L) :
    algebraMap F p.L (Algebra.norm F a) = a * p.τ a := by
  classical
  let : Module.Finite F p.L := Module.finite_of_finrank_eq_succ (p.degree.trans hd)
  have hc : Nat.card (p.L ≃ₐ[F] p.L) = 2 := by
    exact (IsGalois.card_aut_eq_finrank F p.L).trans (p.degree.trans hd)
  rw [Algebra.norm_eq_prod_automorphisms, autsTwo hc p.τ (involution_ne_one p hd)]
  rw [Finset.prod_insert, Finset.prod_singleton, AlgEquiv.one_apply]
  simpa only [Finset.mem_singleton] using (involution_ne_one p hd).symm

private theorem trace_pair (hd : degree F B = 2) (a : p.L) :
    algebraMap F p.L (Algebra.trace F p.L a) = a + p.τ a := by
  classical
  let : Module.Finite F p.L := Module.finite_of_finrank_eq_succ (p.degree.trans hd)
  have hc : Nat.card (p.L ≃ₐ[F] p.L) = 2 := by
    exact (IsGalois.card_aut_eq_finrank F p.L).trans (p.degree.trans hd)
  rw [trace_eq_sum_automorphisms, autsTwo hc p.τ (involution_ne_one p hd)]
  rw [Finset.sum_insert, Finset.sum_singleton, AlgEquiv.one_apply]
  simpa only [Finset.mem_singleton] using (involution_ne_one p hd).symm

private def integerNorm (hd : degree F B = 2)
    (a : p.vL.valuationSubring) : Integers F :=
  ⟨Algebra.norm F (a : p.L), base_le.mp (by
    rw [← p.base_value, norm_pair p hd, map_mul, p.τ_preserves_value, base_one]
    exact (mul_le_of_le_one_left' a.property).trans a.property)⟩

private def integerTrace (hd : degree F B = 2)
    (a : p.vL.valuationSubring) : Integers F :=
  ⟨Algebra.trace F p.L (a : p.L), base_le.mp (by
    rw [← p.base_value, trace_pair p hd, base_one]
    exact p.vL.map_add_le a.property ((p.τ_preserves_value _).trans_le a.property))⟩

private def integralConjugate (a : p.vL.valuationSubring) : p.vL.valuationSubring :=
  ⟨p.τ (a : p.L), (p.τ_preserves_value _).trans_le a.property⟩

private theorem residue_conjugate (hd : degree F B = 2)
    (hr : Module.finrank (BaseResidue F) (l) = degree F B)
    (a : p.vL.valuationSubring) :
    residueInclusion p (integralConjugate p a) =
      FiniteField.frobeniusAlgEquivOfAlgebraic (BaseResidue F) (l)
        (residueInclusion p a) := by
  classical
  let := Fintype.ofFinite l
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic (BaseResidue F) (l)
  obtain ⟨m, hm, hf⟩ := p.frobenius
  have hσ : orderOf σ = 2 := by
    dsimp only [σ]
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hr, hd]
  have hm' : m % 2 = 1 := by
    rw [hd, Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd] at hm
    omega
  have hs : σ ^ m = σ := by
    rw [← pow_mod_orderOf, hσ, hm', pow_one]
  have hf' : residueInclusion p (integralConjugate p a) =
      (residueInclusion p a) ^ (Nat.card k ^ m) := hf _ _ rfl
  have hpw : (residueInclusion p a) ^ (Nat.card k ^ m) =
      (σ ^ m) (residueInclusion p a) := by
    rw [Nat.card_eq_fintype_card, AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  change residueInclusion p (integralConjugate p a) = σ (residueInclusion p a)
  rw [hf', hpw, hs]

private theorem norm_reduction (hd : degree F B = 2)
    (hr : Module.finrank (BaseResidue F) (l) = degree F B)
    (a : p.vL.valuationSubring) :
    IsLocalRing.residue _ (integerNorm p hd a) =
      Algebra.norm (BaseResidue F) (residueInclusion p a) := by
  classical
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k l
  have hσ : σ ≠ 1 := by
    intro h
    have h' : orderOf σ = 2 := by
      dsimp only [σ]
      rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hr, hd]
    simp [h] at h'
  have hcard : Nat.card (l ≃ₐ[k] l) = 2 := by
    exact (IsGalois.card_aut_eq_finrank k l).trans (hr.trans hd)
  have hnorm : integerInclusion p (integerNorm p hd a) =
      a * integralConjugate p a := Subtype.ext (norm_pair p hd (a : p.L))
  apply (algebraMap k l).injective
  rw [← residueInclusion_base p, hnorm, map_mul, residue_conjugate p hd hr,
    Algebra.norm_eq_prod_automorphisms, autsTwo hcard σ hσ]
  rw [Finset.prod_insert, Finset.prod_singleton, AlgEquiv.one_apply]
  simpa only [Finset.mem_singleton] using hσ.symm

private theorem trace_reduction (hd : degree F B = 2)
    (hr : Module.finrank (BaseResidue F) (l) = degree F B)
    (a : p.vL.valuationSubring) :
    IsLocalRing.residue _ (integerTrace p hd a) =
      Algebra.trace (BaseResidue F) (l) (residueInclusion p a) := by
  classical
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k l
  have hσ : σ ≠ 1 := by
    intro h
    have h' : orderOf σ = 2 := by
      dsimp only [σ]
      rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hr, hd]
    simp [h] at h'
  have hcard : Nat.card (l ≃ₐ[k] l) = 2 := by
    exact (IsGalois.card_aut_eq_finrank k l).trans (hr.trans hd)
  have htrace : integerInclusion p (integerTrace p hd a) =
      a + integralConjugate p a := Subtype.ext (trace_pair p hd (a : p.L))
  apply (algebraMap k l).injective
  rw [← residueInclusion_base p, htrace, map_add, residue_conjugate p hd hr,
    trace_eq_sum_automorphisms, autsTwo hcard σ hσ]
  rw [Finset.sum_insert, Finset.sum_singleton, AlgEquiv.one_apply]
  simpa only [Finset.mem_singleton] using hσ.symm

private def pairCoordinates {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (x : S) :
    R × R →ₗ[R] S where
  toFun y := algebraMap R S y.1 + algebraMap R S y.2 * x
  map_add' a b := by simp [Prod.fst_add, Prod.snd_add, add_mul]; ring
  map_smul' a b := by simp [Algebra.smul_def]; ring

private theorem existsResidueGenerator
    (hr : Module.finrank k l = degree F B) (hd : degree F B = 2) :
    ∃ x : p.vL.valuationSubring, residueInclusion p x ∉ Set.range (algebraMap k l) := by
  by_contra! h
  have hs : Function.Surjective (algebraMap k l) := by
    intro y
    obtain ⟨x, rfl⟩ := residueInclusion_surjective p y
    exact h x
  let e := AlgEquiv.ofBijective (Algebra.ofId k l) ⟨(algebraMap k l).injective, hs⟩
  have he := e.toLinearEquiv.finrank_eq
  rw [hr, hd, Module.finrank_self] at he
  norm_num at he

private theorem integerCoordinates (hd : degree F B = 2) {x : p.vL.valuationSubring}
    (hx : residueInclusion p x ∉ Set.range (algebraMap k l)) :
    letI := (integerInclusion p).toAlgebra
    Nonempty (p.vL.valuationSubring ≃ₗ[Integers F] Integers F × Integers F) := by
  let R := Integers F
  let S := p.vL.valuationSubring
  let i := integerInclusion p
  let : Algebra R S := i.toAlgebra
  have hfins : Module.Finite F p.L := Module.finite_of_finrank_eq_succ (p.degree.trans hd)
  have hxs : (x : p.L) ∉ Set.range (algebraMap F p.L) := by
    rintro ⟨a, ha⟩
    have hv : a ∈ Integers F := by
      have h := x.property
      change p.vL (x : p.L) ≤ 1 at h
      rw [← ha, p.base_value, ← base_one (F := F)] at h
      exact base_le.mp h
    have he : i ⟨a, hv⟩ = x := Subtype.ext ha
    apply hx
    refine ⟨IsLocalRing.residue R ⟨a, hv⟩, ?_⟩
    exact (residueInclusion_base p ⟨a, hv⟩).symm.trans (congrArg (residueInclusion p) he)
  let f := pairCoordinates (R := F) (x : p.L)
  have hker : ∀ y : F × F, f y = 0 → y = 0 := by
    rintro ⟨a,b⟩ h
    change algebraMap F p.L a + algebraMap F p.L b * (x : p.L) = 0 at h
    have hb : b = 0 := by
      by_contra hbn
      apply hxs
      refine ⟨-a / b, ?_⟩
      rw [map_div₀, map_neg, div_eq_iff ((map_ne_zero_iff _ (algebraMap F p.L).injective).2 hbn)]
      linear_combination -h
    have ha : a = 0 := by
      apply (algebraMap F p.L).injective
      simpa [hb] using h
    exact Prod.ext ha hb
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  have hf : Module.finrank F (F × F) = Module.finrank F p.L := by
    rw [Module.finrank_prod, Module.finrank_self, p.degree, hd]
  let e := LinearEquiv.ofInjectiveOfFinrankEq f hinj hf
  have intCoords (a b : F)
      (h : p.vL (algebraMap F p.L a + algebraMap F p.L b * (x : p.L)) ≤ 1) :
      a ∈ Integers F ∧ b ∈ Integers F := by
    have compare (d : F) (ha : baseValue F a ≤ baseValue F d)
        (hb : baseValue F b ≤ baseValue F d) (hd' : 1 < baseValue F d) (he : d = a ∨ d = b) :
        False := by
      let f₀ := normalizedValuation F
      have hd₀ : d ≠ 0 := by
        intro he
        subst d
        change 1 < f₀ 0 at hd'
        simp at hd'
      have h0 : 0 < baseValue F d := zero_lt_one.trans hd'
      have hab : a / d ∈ Integers F := base_le.mp (by
        change f₀ (a / d) ≤ f₀ 1
        rw [map_div₀, map_one]
        exact (div_le_one₀ h0).2 ha)
      have hbb : b / d ∈ Integers F := base_le.mp (by
        change f₀ (b / d) ≤ f₀ 1
        rw [map_div₀, map_one]
        exact (div_le_one₀ h0).2 hb)
      let a₀ : R := ⟨a / d, hab⟩
      let b₀ : R := ⟨b / d, hbb⟩
      have hs : p.vL ((i a₀ + i b₀ * x : S) : p.L) < 1 := by
        have heq : ((i a₀ + i b₀ * x : S) : p.L) =
            (algebraMap F p.L a + algebraMap F p.L b * (x : p.L)) /
              algebraMap F p.L d := by
          change algebraMap F p.L (a / d) + algebraMap F p.L (b / d) * (x : p.L) = _
          rw [map_div₀, map_div₀]
          ring
        rw [heq, map_div₀, p.base_value, div_lt_one₀ h0]
        exact h.trans_lt hd'
      have hzero := (residueInclusion_eq_zero p _).2 hs
      change residueInclusion p (integerInclusion p a₀ +
        integerInclusion p b₀ * x) = 0 at hzero
      simp only [map_add, map_mul, residueInclusion_base] at hzero
      rcases he with rfl | rfl
      · have ha₀ : a₀ = 1 := Subtype.ext (div_self hd₀)
        rw [ha₀, map_one, map_one] at hzero
        have hne : IsLocalRing.residue R b₀ ≠ 0 := by
          intro hz
          rw [hz, map_zero, zero_mul, add_zero] at hzero
          exact one_ne_zero hzero
        apply hx
        refine ⟨-1 / IsLocalRing.residue R b₀, ?_⟩
        rw [map_div₀, map_neg, map_one,
          div_eq_iff ((map_ne_zero_iff _ (algebraMap k l).injective).2 hne)]
        linear_combination -hzero
      · have hb₀ : b₀ = 1 := Subtype.ext (div_self hd₀)
        rw [hb₀, map_one, map_one, one_mul] at hzero
        apply hx
        refine ⟨-IsLocalRing.residue R a₀, ?_⟩
        rw [map_neg]
        linear_combination -hzero
    change valuation F a ≤ 1 ∧ valuation F b ≤ 1
    rw [← map_one (valuation F), ← base_le, ← base_le, base_one]
    obtain hab | hba := le_total (baseValue F a) (baseValue F b)
    · have hb : baseValue F b ≤ 1 := le_of_not_gt (fun ht => compare b hab le_rfl ht (.inr rfl))
      exact ⟨hab.trans hb, hb⟩
    · have ha : baseValue F a ≤ 1 := le_of_not_gt (fun ht => compare a le_rfl hba ht (.inl rfl))
      exact ⟨ha, hba.trans ha⟩
  let g := pairCoordinates (R := R) x
  have hg (z : R × R) :
      ((g z : S) : p.L) = f ((z.1 : F), (z.2 : F)) := rfl
  have gi : Function.Injective g := by
    intro a b h
    have he := congrArg Subtype.val h
    rw [hg, hg] at he
    have hh := hinj he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  have gs : Function.Surjective g := by
    intro y
    obtain ⟨⟨a,b⟩, hab⟩ := e.surjective (y : p.L)
    change f (a,b) = (y : p.L) at hab
    have hy := y.property
    change p.vL (y : p.L) ≤ 1 at hy
    rw [← hab] at hy
    have hh := intCoords a b hy
    exact ⟨(⟨a, hh.1⟩, ⟨b, hh.2⟩), Subtype.ext hab⟩
  exact ⟨(LinearEquiv.ofBijective g ⟨gi, gs⟩).symm⟩

private theorem completeIntegerRing (hd : degree F B = 2) (hr : Module.finrank k l = degree F B) :
    IsAdicComplete (IsLocalRing.maximalIdeal (p.vL.valuationSubring)) (p.vL.valuationSubring) := by
  let R := Integers F
  let S := p.vL.valuationSubring
  let i := integerInclusion p
  let : Algebra R S := i.toAlgebra
  let π : R := ⟨p.parameter, parameterIntegral p.value_parameter⟩
  have hπ : Irreducible π := parameterIrreducible p.value_parameter
  obtain ⟨x, hx⟩ := existsResidueGenerator p hr hd
  obtain ⟨e⟩ := integerCoordinates p hd hx
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
    inferInstanceAs (IsAdicComplete (IsLocalRing.maximalIdeal (Valuation.integer (valuation F)))
      (Valuation.integer (valuation F)))
  have hI := adicCompletePair π hπ.maximalIdeal_eq e
  have hspan : IsLocalRing.maximalIdeal S = Ideal.span {i π} := by
    ext a
    rw [Valuation.mem_maximalIdeal_iff, Ideal.mem_span_singleton,
      (Valuation.valuationSubring.integers p.vL).dvd_iff_le]
    change p.vL (a : p.L) < 1 ↔ p.vL (a : p.L) ≤ p.vL (algebraMap F p.L p.parameter)
    rw [p.base_value, p.value_parameter]
    exact lt_one_iff_le_uniformizer _
  rw [hspan, ← Set.image_singleton, ← Ideal.map_span, ← hπ.maximalIdeal_eq]
  exact (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal R) S).mpr hI

private theorem unitTraceElement (hd : degree F B = 2) (hr : Module.finrank k l = degree F B) :
    ∃ z : p.vL.valuationSubring, IsUnit (integerTrace p hd z) ∧
      IsUnit (integerNorm p hd z) := by
  obtain ⟨x, hx⟩ := Algebra.trace_surjective k l 1
  obtain ⟨z, hz⟩ := residueInclusion_surjective p x
  refine ⟨z, ?_, ?_⟩
  · apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    rw [trace_reduction p hd hr, hz, hx]
    exact one_ne_zero
  · apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    rw [norm_reduction p hd hr, hz]
    have hx0 : x ≠ 0 := by
      intro he
      rw [he, map_zero] at hx
      exact zero_ne_one hx
    exact Algebra.norm_ne_zero_iff.mpr hx0

/-- First lift a residue norm. Then a correction of the form `1 + s z` has
norm `1 + s Tr(z) + s² N(z)`. Its parameter is found by Hensel's lemma
using an integral element with unit trace. -/
private theorem normUnits (hd : degree F B = 2) (hr : Module.finrank k l = degree F B)
    (u₀ : Integers F) (hu : IsUnit u₀) :
    ∃ a : p.L, p.vL a = 1 ∧ Algebra.norm F a = (u₀ : F) := by
  let R := Integers F
  let n := integerNorm p hd
  let tr := integerTrace p hd
  let res : R →+* k := IsLocalRing.residue R
  obtain ⟨x, hx⟩ := FiniteField.norm_surjective k l (res u₀)
  obtain ⟨a, ha⟩ := residueInclusion_surjective p x
  have hna : res (n a) = res u₀ := by
    rw [norm_reduction p hd hr, ha, hx]
  have hnu : IsUnit (n a) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    (hna ▸ (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu)
  obtain ⟨z, ht, hn⟩ := unitTraceElement p hd hr
  let v₀ : R := u₀ * ↑(hnu.unit⁻¹)
  have hv₀ : n a * v₀ = u₀ := by
    change n a * (u₀ * (↑(hnu.unit⁻¹) : R)) = u₀
    have h : n a * (↑(hnu.unit⁻¹) : R) = 1 := by
      calc
        n a * (↑(hnu.unit⁻¹) : R) = ↑hnu.unit * (↑(hnu.unit⁻¹) : R) :=
          congrArg (fun x : R => x * ↑(hnu.unit⁻¹)) hnu.unit_spec.symm
        _ = 1 := Units.mul_inv hnu.unit
    rw [mul_left_comm, h, mul_one]
  have hv : res v₀ = 1 := by
    have h := congrArg res hv₀
    rw [map_mul, hna] at h
    exact (mul_left_cancel₀ ((IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu))
      (by simpa using h)
  let b : R := ↑(hn.unit⁻¹) * tr z
  let c : R := ↑(hn.unit⁻¹) * (1 - v₀)
  have hnz : n z * (↑(hn.unit⁻¹) : R) = 1 := by
    calc
      n z * (↑(hn.unit⁻¹) : R) = ↑hn.unit * (↑(hn.unit⁻¹) : R) :=
        congrArg (fun x : R => x * ↑(hn.unit⁻¹)) hn.unit_spec.symm
      _ = 1 := Units.mul_inv hn.unit
  have hc : res c = 0 := by simp [c, res, hv]
  have hb : res b ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2
    ((hn.unit⁻¹).isUnit.mul ht)
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
    inferInstanceAs (IsAdicComplete (IsLocalRing.maximalIdeal (Valuation.integer (valuation F)))
      (Valuation.integer (valuation F)))
  have h₀ : aeval (0 : k) (quadratic b c) = 0 := by
    rw [quadratic_aeval]
    change 0 ^ 2 + res b * 0 + res c = 0
    simpa using hc
  have h₁ : aeval (0 : k) (quadratic b c).derivative ≠ 0 := by
    rw [quadratic_derivative]
    simp only [map_add, map_mul, aeval_C, aeval_X, mul_zero, zero_add]
    exact hb
  obtain ⟨s, hs, _⟩ := liftSimpleRoot _ (quadratic_monic b c) 0 h₀ h₁
  have hs' : n z * s ^ 2 + tr z * s + 1 = v₀ := by
    have h : s ^ 2 + b * s + c = 0 := by simpa [Polynomial.IsRoot.def, quadratic] using hs
    change s ^ 2 + (↑(hn.unit⁻¹) * tr z) * s + ↑(hn.unit⁻¹) * (1 - v₀) = 0 at h
    have hmul : n z * (s ^ 2 + (↑(hn.unit⁻¹) * tr z) * s +
        ↑(hn.unit⁻¹) * (1 - v₀)) = 0 := by rw [h, mul_zero]
    simp only [mul_add, ← mul_assoc, hnz, one_mul] at hmul
    linear_combination hmul
  let sL := algebraMap F p.L (s : F)
  have hn1 : Algebra.norm F (1 + sL * (z : p.L)) = (v₀ : F) := by
    apply (algebraMap F p.L).injective
    rw [norm_pair p hd]
    have h := congrArg (integerInclusion p) hs'
    simp only [map_add, map_mul, map_pow, map_one] at h
    have he := congrArg Subtype.val h
    change algebraMap F p.L (Algebra.norm F (z : p.L)) * sL ^ 2 +
      algebraMap F p.L (Algebra.trace F p.L (z : p.L)) * sL + 1 =
      algebraMap F p.L (v₀ : F) at he
    rw [norm_pair p hd, trace_pair p hd] at he
    simp only [map_add, map_mul, map_one, sL, p.τ.commutes]
    change (1 + sL * (z : p.L)) * (1 + sL * p.τ (z : p.L)) = _
    linear_combination he
  let d := (a : p.L) * (1 + sL * (z : p.L))
  have hdNorm : Algebra.norm F d = (u₀ : F) := by
    dsimp only [d]
    rw [map_mul, hn1]
    exact congrArg Subtype.val hv₀
  refine ⟨d, ?_, hdNorm⟩
  have huVal : valuation F (u₀ : F) = 1 :=
    (Valuation.valuationSubring.integers (valuation F)).isUnit_iff_valuation_eq_one.mp hu
  have huBase : baseValue F (u₀ : F) = 1 :=
    (congrArg (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F) huVal).trans (map_one _)
  have h := congrArg p.vL (norm_pair p hd d)
  rw [hdNorm, p.base_value, huBase, map_mul, p.τ_preserves_value, ← pow_two] at h
  exact (pow_left_inj₀ (by simp) (by simp) (by decide : (2 : ℕ) ≠ 0)).mp
    (h.symm.trans (one_pow 2).symm)

private theorem quadraticResidueRoot (hd : degree F B = 2) (hr : Module.finrank k l = degree F B)
    {b c : Integers F} (hn : ∀ x : k, aeval x (quadratic b c) ≠ 0) :
    ∃ x : l, (quadratic b c).eval₂ ((algebraMap k l).comp (IsLocalRing.residue _)) x = 0 ∧
      (quadratic b c).derivative.eval₂ ((algebraMap k l).comp (IsLocalRing.residue _)) x ≠ 0 := by
  let f := quadratic b c
  let g := f.map (IsLocalRing.residue (Integers F))
  have hgm : g.Monic := (quadratic_monic b c).map _
  have hg2 : g.natDegree = 2 := by
    change ((quadratic b c).map _).natDegree = 2
    rw [quadratic_map, quadratic_natDegree]
  have hgi : Irreducible g := by
    apply irreducible_of_degree_le_three_of_not_isRoot (p := g)
    · rw [hg2]; decide
    · intro x
      change g.eval x ≠ 0
      change (f.map (IsLocalRing.residue (Integers F))).eval x ≠ 0
      rw [eval_map]
      exact hn x
  let : Fact (Irreducible g) := ⟨hgi⟩
  have hdim : Module.finrank k (AdjoinRoot g) = 2 :=
    ((AdjoinRoot.powerBasis hgm.ne_zero).finrank).trans hg2
  obtain ⟨j⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := k) (K := AdjoinRoot g) (L := l) (by rw [hdim, hr, hd])
  let x := j (AdjoinRoot.root g)
  have hx : aeval x g = 0 := by
    change aeval (j (AdjoinRoot.root g)) g = 0
    rw [Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hsep : g.Separable := PerfectField.separable_of_irreducible hgi
  have hx' := hsep.aeval_derivative_ne_zero hx
  exact ⟨x, by simpa [g, f, aeval_def, eval₂_map] using hx,
    by simpa [g, f, aeval_def, derivative_map, eval₂_map] using hx'⟩

private theorem unramifiedRoot (hd : degree F B = 2) (hr : Module.finrank k l = degree F B) {b c : Integers F}
    (hn : ∀ x : k, aeval x (quadratic b c) ≠ 0) :
    ∃ y : p.L, aeval y (quadratic (b : F) (c : F)) = 0 := by
  let S := p.vL.valuationSubring
  let i := integerInclusion p
  let G := (quadratic b c).map i
  let ϕ := IsLocalRing.residue S
  let : IsAdicComplete (IsLocalRing.maximalIdeal S) S := completeIntegerRing p hd hr
  obtain ⟨x, hx, hx'⟩ := quadraticResidueRoot (r := r) hd hr hn
  let y := p.residueEquiv.symm x
  have hy : p.residueEquiv y = x := p.residueEquiv.apply_symm_apply _
  have hh : p.residueEquiv.toRingHom.comp (ϕ.comp i) =
      (algebraMap k l).comp (IsLocalRing.residue _) :=
    RingHom.ext (residueInclusion_base p)
  have h0 : aeval y G = 0 := by
    apply p.residueEquiv.injective
    rw [map_zero, aeval_def, IsLocalRing.ResidueField.algebraMap_eq]
    change p.residueEquiv.toRingHom (G.eval₂ ϕ y) = 0
    rw [hom_eval₂, eval₂_map, RingHom.comp_assoc, hh]
    rwa [show p.residueEquiv.toRingHom y = x from hy]
  have h1 : aeval y G.derivative ≠ 0 := by
    intro hn0
    apply hx'
    have h := congrArg p.residueEquiv.toRingHom hn0
    rw [map_zero, aeval_def, IsLocalRing.ResidueField.algebraMap_eq,
      hom_eval₂, derivative_map, eval₂_map, RingHom.comp_assoc, hh] at h
    rw [show p.residueEquiv.toRingHom y = x from hy] at h
    exact h
  obtain ⟨z, hz, _⟩ := liftSimpleRoot G ((quadratic_monic b c).map i) y h0 h1
  refine ⟨(z : p.L), ?_⟩
  have h := congrArg p.vL.valuationSubring.subtype (Polynomial.IsRoot.def.mp hz)
  unfold G at h
  rw [quadratic_map] at h
  simpa [quadratic, quadratic_aeval, i, integerInclusion] using h

private theorem involutionApplySquare (hd : degree F B = 2) (a : p.L) :
    p.τ (p.τ a) = a := by
  have h := congrArg (fun e : p.L ≃ₐ[F] p.L => e a) (involutionSquare p hd)
  simpa only [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] using h

private theorem cyclicMultiply {F L B : Type*} [Field F] [Field L] [Algebra F L]
    [Ring B] [Algebra F B] (i : L →ₐ[F] B) (τ : L ≃ₐ[F] L)
    (hτ : ∀ a, τ (τ a) = a) {t : F} {j : B}
    (hconj : ∀ a, j * i a = i (τ a) * j) (hsq : j ^ 2 = algebraMap F B t)
    (a b c d : L) :
    (i a + j * i b) * (i c + j * i d) =
      i (a * c + algebraMap F L t * (τ b * d)) + j * i (τ a * d + b * c) := by
  have hcomm (x : L) : i x * j = j * i (τ x) := by
    rw [hconj, hτ]
  have hbd : (j * i b) * (j * i d) = algebraMap F B t * (i (τ b) * i d) := by
    calc
      _ = j * (i b * j) * i d := by noncomm_ring
      _ = (j * j) * (i (τ b) * i d) := by rw [hcomm]; noncomm_ring
      _ = _ := by rw [← pow_two, hsq]
  have had : i a * (j * i d) = j * (i (τ a) * i d) := by
    rw [← mul_assoc, hcomm, mul_assoc]
  rw [add_mul, mul_add, mul_add, had, hbd]
  simp only [map_add, map_mul, i.commutes]
  noncomm_ring

private theorem cyclicRootRelation (hd : degree F B = 2) (a b : p.L) :
    let y := p.embed a + (p.uniformizer : B) * p.embed b
    y ^ 2 = algebraMap F B (Algebra.trace F p.L a) * y -
      algebraMap F B (Algebra.norm F a - p.parameter * Algebra.norm F b) := by
  dsimp only
  have hs : (p.uniformizer : B) ^ 2 = algebraMap F B p.parameter := by
    simpa [hd] using p.power_uniformizer
  rw [pow_two, cyclicMultiply p.embed p.τ (involutionApplySquare p hd) p.conjugation hs]
  have hf₀ : a * a + algebraMap F p.L p.parameter * (p.τ b * b) =
      algebraMap F p.L (Algebra.trace F p.L a) * a -
        algebraMap F p.L (Algebra.norm F a - p.parameter * Algebra.norm F b) := by
    simp only [map_sub, map_mul, trace_pair p hd, norm_pair p hd]
    ring
  have hf₁ : p.τ a * b + b * a = algebraMap F p.L (Algebra.trace F p.L a) * b := by
    rw [trace_pair p hd]
    ring
  rw [hf₀, hf₁]
  simp only [map_sub, map_mul, p.embed.commutes, mul_add]
  have hcomm := Algebra.commutes (R := F) (A := B) (Algebra.trace F p.L a) (p.uniformizer : B)
  rw [← mul_assoc (p.uniformizer : B), ← hcomm]
  noncomm_ring

/-- For `X² + b X + c`, choose the integral part with trace `-b` and in the
uniformizer ideal. The remaining norm equation for the second coordinate has
a unit right-hand side because `c` is divisible by exactly one uniformizer. -/
private theorem eisensteinRoot (hd : degree F B = 2)
    (hr : Module.finrank k l = degree F B) {b c : Integers F}
    (hb : (⟨p.parameter, parameterIntegral p.value_parameter⟩ : Integers F) ∣ b)
    (hc : (⟨p.parameter, parameterIntegral p.value_parameter⟩ : Integers F) ∣ c)
    (hc₂ : ¬ (⟨p.parameter, parameterIntegral p.value_parameter⟩ : Integers F) ^ 2 ∣ c) :
    ∃ y : B, aeval y (quadratic (b : F) (c : F)) = 0 := by
  let R := Integers F
  let i := integerInclusion p
  let π : R := ⟨p.parameter, parameterIntegral p.value_parameter⟩
  let ϕ := IsLocalRing.residue R
  have hπ : Irreducible π := parameterIrreducible p.value_parameter
  obtain ⟨b₁, hb₁⟩ := hb
  obtain ⟨c₁, hc₁⟩ := hc
  have hc₁' : ϕ c₁ ≠ 0 := by
    intro he
    have hh : π ∣ c₁ := by
      rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff]
      exact he
    obtain ⟨d, hd'⟩ := hh
    apply hc₂
    use d
    rw [hc₁, hd', pow_two, mul_assoc]
  have hrπ : ϕ π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨z, hz, _⟩ := unitTraceElement p hd hr
  let s : R := (-b₁) * ↑(hz.unit⁻¹)
  let y := i s * z
  let a := (i π * y : p.vL.valuationSubring)
  have hsz : s * integerTrace p hd z = -b₁ := by
    have h : (↑(hz.unit⁻¹) : R) * integerTrace p hd z = 1 := by
      calc
        _ = (↑(hz.unit⁻¹) : R) * ↑hz.unit :=
          congrArg (fun r : R => (↑(hz.unit⁻¹) : R) * r) hz.unit_spec.symm
        _ = 1 := Units.inv_mul hz.unit
    change -b₁ * (↑(hz.unit⁻¹) : R) * integerTrace p hd z = -b₁
    rw [mul_assoc, h, mul_one]
  have hat : Algebra.trace F p.L (a : p.L) = -(b : F) := by
    have hh := congrArg (fun r : R => (r : F)) hsz
    change (s : F) * Algebra.trace F p.L (z : p.L) = -(b₁ : F) at hh
    change Algebra.trace F p.L
      (algebraMap F p.L (π : F) * (algebraMap F p.L (s : F) * (z : p.L))) = -(b : F)
    simp only [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    rw [hh, hb₁]
    change (π : F) * -(b₁ : F) = -((π : F) * (b₁ : F))
    exact mul_neg _ _
  let u₀ : R := π * integerNorm p hd y - c₁
  have hu : IsUnit u₀ := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by
    change ϕ (π * integerNorm p hd y - c₁) ≠ 0
    rw [map_sub, map_mul, hrπ, zero_mul, zero_sub, neg_ne_zero]
    exact hc₁')
  obtain ⟨d, _, hdn⟩ := normUnits p hd hr u₀ hu
  have han : Algebra.norm F (a : p.L) - p.parameter * Algebra.norm F d = (c : F) := by
    change (Algebra.norm F) (algebraMap F p.L (π : F) * (y : p.L)) -
      p.parameter * Algebra.norm F d = (c : F)
    rw [map_mul, Algebra.norm_algebraMap, p.degree, hd, hdn, hc₁]
    change (π : F) ^ 2 * Algebra.norm F (y : p.L) -
        (π : F) * ((π : F) * Algebra.norm F (y : p.L) - (c₁ : F)) = (π : F) * (c₁ : F)
    ring
  refine ⟨p.embed (a : p.L) + (p.uniformizer : B) * p.embed d, ?_⟩
  rw [quadratic_aeval, cyclicRootRelation p hd, hat, han, map_neg]
  noncomm_ring

private theorem lift_nonscalar {x : p.vL.valuationSubring} (hx : residueInclusion p x ∉ Set.range (algebraMap k l)) :
    (x : p.L) ∉ Set.range (algebraMap F p.L) := by
  rintro ⟨a, ha⟩
  have hv : a ∈ Integers F := by
    have h := x.property
    change p.vL (x : p.L) ≤ 1 at h
    rw [← ha, p.base_value, ← base_one (F := F)] at h
    exact base_le.mp h
  have he : integerInclusion p ⟨a, hv⟩ = x := Subtype.ext ha
  apply hx
  exact ⟨IsLocalRing.residue _ ⟨a, hv⟩,
    (residueInclusion_base p ⟨a, hv⟩).symm.trans (congrArg (residueInclusion p) he)⟩

private theorem noBaseRoot {K M : Type*} [Field K] [Field M] [Algebra K M] {b c : K} {x : M}
    (hxs : x ∉ Set.range (algebraMap K M)) (hx : aeval x (quadratic b c) = 0) (y : K) :
    (quadratic b c).eval y ≠ 0 := by
  intro hy
  rw [quadratic_aeval] at hx
  have hfac : (x - algebraMap K M y) * (x + algebraMap K M b + algebraMap K M y) = 0 := by
    have hy' : (algebraMap K M y) ^ 2 + algebraMap K M b * algebraMap K M y +
        algebraMap K M c = 0 := by
      simpa [quadratic] using congrArg (algebraMap K M) hy
    linear_combination hx - hy'
  rcases mul_eq_zero.mp hfac with h₁ | h₂
  · exact hxs ⟨y, (sub_eq_zero.mp h₁).symm⟩
  · apply hxs
    refine ⟨-b - y, ?_⟩
    rw [map_sub, map_neg]
    linear_combination -h₂

private theorem goodGenerator (hd : degree F B = 2)
    (hr : Module.finrank k l = degree F B) :
    ∃ (b c : Integers F) (x : p.L), x ∉ Set.range (algebraMap F p.L) ∧
      aeval x (quadratic (b : F) (c : F)) = 0 ∧
      (∀ y : k, aeval y (quadratic b c) ≠ 0) := by
  obtain ⟨x, hx⟩ := existsResidueGenerator p hr hd
  let b := -integerTrace p hd x
  let c := integerNorm p hd x
  have hb : integerInclusion p b = -(x + integralConjugate p x) := by
    apply Subtype.ext
    change algebraMap F p.L (-Algebra.trace F p.L (x : p.L)) = -((x : p.L) + p.τ (x : p.L))
    rw [map_neg, trace_pair p hd]
  have hc : integerInclusion p c = x * integralConjugate p x :=
    Subtype.ext (norm_pair p hd (x : p.L))
  have hrel : x ^ 2 + integerInclusion p b * x + integerInclusion p c = 0 := by
    rw [hb, hc]
    ring
  refine ⟨b, c, (x : p.L), lift_nonscalar p hx, ?_, ?_⟩
  · rw [quadratic_aeval]
    exact congrArg Subtype.val hrel
  · have h := congrArg (residueInclusion p) hrel
    simp only [map_add, map_pow, map_mul, map_zero, residueInclusion_base] at h
    intro y
    have hh : aeval (residueInclusion p x)
        (quadratic (IsLocalRing.residue _ b) (IsLocalRing.residue _ c)) = 0 := by
      rw [quadratic_aeval]
      exact h
    have hn := noBaseRoot hx hh y
    change (quadratic b c).eval₂ (IsLocalRing.residue _) y ≠ 0
    rwa [← eval_map, quadratic_map]

private def pairToFinTwo (L : Type*) : (L × L) ≃ (Fin 2 → L) where
  toFun z := ![z.1, z.2]
  invFun f := (f 0, f 1)
  left_inv _ := rfl
  right_inv f := by funext i; fin_cases i <;> rfl

private def cyclicCoordinates (hd : degree F B = 2) : p.L × p.L ≃ B :=
  let := _root_.Specs.RM03.CSA.rightSubfieldModule p.embed
  let b := p.basis.reindex (finCongr hd)
  (pairToFinTwo p.L).trans b.equivFun.toEquiv.symm

private theorem cyclicCoordinates_apply (hd : degree F B = 2) (a b : p.L) :
    cyclicCoordinates p hd (a, b) = p.embed a + (p.uniformizer : B) * p.embed b := by
  let := _root_.Specs.RM03.CSA.rightSubfieldModule p.embed
  change (p.basis.reindex (finCongr hd)).equivFun.symm ![a, b] = _
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
  simp only [Module.Basis.reindex_apply, Matrix.cons_val_zero, Matrix.cons_val_one, p.basis_eq]
  have h0 : ((finCongr hd).symm 0).val = 0 := rfl
  have h1 : ((finCongr hd).symm 1).val = 1 := rfl
  rw [h0, h1, pow_zero, pow_one]
  change 1 * p.embed a + (p.uniformizer : B) * p.embed b = _
  rw [one_mul]

end

end LocalPresentation

private theorem compareCyclic {F L M B D : Type*} [Field F] [Field L] [Field M]
    [DivisionRing B] [DivisionRing D] [Algebra F L] [Algebra F M] [Algebra F B] [Algebra F D]
    (i : L →ₐ[F] B) (i' : M →ₐ[F] D) (τ : L ≃ₐ[F] L) (τ' : M ≃ₐ[F] M)
    (hτ : ∀ a, τ (τ a) = a) (hτ' : ∀ a, τ' (τ' a) = a) (e : L ≃ₐ[F] M)
    (he : ∀ a, e (τ a) = τ' (e a)) {t : F} {j : B} {j' : D}
    (hj : ∀ a, j * i a = i (τ a) * j) (hj' : ∀ a, j' * i' a = i' (τ' a) * j')
    (hjs : j ^ 2 = algebraMap F B t) (hjs' : j' ^ 2 = algebraMap F D t)
    (c : L × L ≃ B) (c' : M × M ≃ D)
    (hc : ∀ a b, c (a, b) = i a + j * i b) (hc' : ∀ a b, c' (a, b) = i' a + j' * i' b) :
    Nonempty (B ≃ₐ[F] D) := by
  let f := c.symm.trans ((e.toEquiv.prodCongr e.toEquiv).trans c')
  have hf (a b : L) : f (i a + j * i b) = i' (e a) + j' * i' (e b) := by
    rw [← hc]
    change c' (e (c.symm (c (a, b))).1, e (c.symm (c (a, b))).2) = _
    rw [c.symm_apply_apply, hc']
  refine ⟨{ f with
    map_mul' := ?_
    map_add' := ?_
    commutes' := ?_ }⟩
  · intro x y
    change f (x * y) = f x * f y
    obtain ⟨⟨a,b⟩, rfl⟩ := c.surjective x
    obtain ⟨⟨d,g⟩, rfl⟩ := c.surjective y
    rw [hc, hc, cyclicMultiply i τ hτ hj hjs, hf, hf, hf,
      cyclicMultiply i' τ' hτ' hj' hjs']
    simp only [map_add, map_mul, e.commutes, he]
  · intro x y
    change f (x + y) = f x + f y
    obtain ⟨⟨a,b⟩, rfl⟩ := c.surjective x
    obtain ⟨⟨d,g⟩, rfl⟩ := c.surjective y
    rw [hc, hc]
    have h : (i a + j * i b) + (i d + j * i g) = i (a + d) + j * i (b + g) := by
      simp only [map_add, mul_add]
      abel
    rw [h, hf, hf, hf]
    simp only [map_add, mul_add]
    abel
  · intro a
    change f (algebraMap F B a) = algebraMap F D a
    have h := hf (algebraMap F L a) 0
    simpa only [map_zero, mul_zero, add_zero, i.commutes, i'.commutes, e.commutes] using h

theorem quadratic_embedding : QuadraticEmbedding.{u,v,w} := by
  intro F _ _ _ _ B _ _ E _ _ _ hB hd hE
  obtain ⟨wB, r, hr, ⟨p⟩⟩ :=
    obtainPresentation (RM03.CSA.isCentralSimple_of_isCentralDivision F B hB)
  let π : Integers F := ⟨p.parameter, parameterIntegral p.value_parameter⟩
  obtain ⟨b, c, ⟨x, hxs, hx⟩, h⟩ := normalizedGenerator F hE π (parameterIrreducible p.value_parameter)
  have hy : ∃ y : B, aeval y (quadratic (b : F) (c : F)) = 0 := by
    rcases h with hu | ⟨hb, hc, hc₂⟩
    · obtain ⟨y, hy⟩ := unramifiedRoot p hd hr hu
      exact ⟨p.embed y, by simpa only [Polynomial.aeval_algHom_apply, map_zero] using congrArg p.embed hy⟩
    · exact eisensteinRoot p hd hr hb hc hc₂
  obtain ⟨y, hy⟩ := hy
  exact embedOfRoot hE hxs hx hy

theorem quadratic_splitting : QuadraticSplitting.{u,v,w} :=
  splittingOfEmbedding quadratic_embedding

theorem local_division_unique : LocalDivisionUnique.{u,v,w} := by
  intro F _ _ _ _ B _ _ D _ _ hB hdB hD hdD
  obtain ⟨wB, rB, hrB, ⟨p⟩⟩ :=
    obtainPresentation (RM03.CSA.isCentralSimple_of_isCentralDivision F B hB)
  obtain ⟨wD, rD, hrD, ⟨q⟩⟩ :=
    obtainPresentation (RM03.CSA.isCentralSimple_of_isCentralDivision F D hD)
  let : Field p.L := p.fieldL
  let : Field q.L := q.fieldL
  let : Algebra F p.L := p.algebraL
  let : Algebra F q.L := q.algebraL
  let : IsGalois F q.L := q.galois
  let : Module.Finite F p.L := Module.finite_of_finrank_eq_succ (p.degree.trans hdB)
  let : Module.Finite F q.L := Module.finite_of_finrank_eq_succ (q.degree.trans hdD)
  obtain ⟨b, c, x, hxs, hx, hred⟩ := goodGenerator p hdB hrB
  obtain ⟨y, hy⟩ := unramifiedRoot q hdD hrD hred
  obtain ⟨g⟩ := embedOfRoot (p.degree.trans hdB) hxs hx hy
  have hdim : Module.finrank F p.L = Module.finrank F q.L :=
    (p.degree.trans hdB).trans (q.degree.trans hdD).symm
  let lin := LinearEquiv.ofInjectiveOfFinrankEq g.toLinearMap g.injective hdim
  let e : p.L ≃ₐ[F] q.L := AlgEquiv.ofBijective g ⟨g.injective, lin.surjective⟩
  have he (a : p.L) : e (p.τ a) = q.τ (e a) := by
    classical
    let σ : q.L ≃ₐ[F] q.L := e.symm.trans (p.τ.trans e)
    have hσ : σ ≠ 1 := by
      intro h
      apply involution_ne_one p hdB
      ext z
      have hz := congrArg (fun f : q.L ≃ₐ[F] q.L => f (e z)) h
      apply e.injective
      simpa [σ, AlgEquiv.trans_apply] using hz
    have hcard : Nat.card (q.L ≃ₐ[F] q.L) = 2 :=
      (IsGalois.card_aut_eq_finrank F q.L).trans (q.degree.trans hdD)
    have hm : σ ∈ (Finset.univ : Finset (q.L ≃ₐ[F] q.L)) := Finset.mem_univ _
    rw [autsTwo hcard q.τ (involution_ne_one q hdD), Finset.mem_insert, Finset.mem_singleton] at hm
    have h := congrArg (fun f : q.L ≃ₐ[F] q.L => f (e a)) (hm.resolve_left hσ)
    simpa [σ, AlgEquiv.trans_apply] using h
  let f := normalizedValuation F
  have ht : f (p.parameter / q.parameter) = 1 := by
    rw [map_div₀]
    change baseValue F p.parameter / baseValue F q.parameter = 1
    rw [p.value_parameter, q.value_parameter, div_self WithZero.exp_ne_zero]
  have hqt : q.parameter ≠ 0 := by
    intro h
    have hh := q.value_parameter
    rw [h] at hh
    change f 0 = _ at hh
    exact WithZero.exp_ne_zero ((map_zero f).symm.trans hh).symm
  let ratio : Integers F := ⟨p.parameter / q.parameter,
    base_le.mp (by change f _ ≤ baseValue F 1; rw [ht, base_one])⟩
  have hru : IsUnit ratio := by
    apply (Valuation.valuationSubring.integers (valuation F)).isUnit_iff_valuation_eq_one.mpr
    change valuation F (p.parameter / q.parameter) = 1
    rw [← map_one (valuation F)]
    have hv : baseValue F (p.parameter / q.parameter) = baseValue F (1 : F) :=
      ht.trans (base_one (F := F)).symm
    exact le_antisymm (base_le.mp hv.le) (base_le.mp hv.ge)
  obtain ⟨z, hzVal, hz⟩ := normUnits q hdD hrD ratio hru
  have hz₀ : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hzVal
    exact zero_ne_one hzVal
  let j' := (q.uniformizer : D) * q.embed z
  have hj' (a : q.L) : j' * q.embed a = q.embed (q.τ a) * j' := by
    dsimp [j']
    calc
      _ = (q.uniformizer : D) * (q.embed a * q.embed z) := by
        rw [mul_assoc, ← map_mul, mul_comm z a, map_mul]
      _ = _ := by rw [← mul_assoc, q.conjugation, mul_assoc]
  have hjq : (q.uniformizer : D) ^ 2 = algebraMap F D q.parameter := by
    simpa [hdD] using q.power_uniformizer
  have hsq : j' ^ 2 = algebraMap F D p.parameter := by
    have h := cyclicMultiply q.embed q.τ (involutionApplySquare q hdD) q.conjugation hjq 0 z 0 z
    simp only [map_zero, mul_zero, zero_mul, zero_add, add_zero, ← pow_two, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    change j' ^ 2 = q.embed (algebraMap F q.L q.parameter * (q.τ z * z)) at h
    rw [h, mul_comm (q.τ z) z, ← norm_pair q hdD, ← map_mul, q.embed.commutes, hz]
    change algebraMap F D (q.parameter * (p.parameter / q.parameter)) = _
    rw [mul_comm, div_mul_cancel₀ _ hqt]
  let C := (Equiv.refl (α := q.L)).prodCongr (Equiv.mulLeft₀ z hz₀)
  let c' := C.trans (cyclicCoordinates q hdD)
  have hcoords (a b : q.L) : c' (a, b) = q.embed a + j' * q.embed b := by
    change cyclicCoordinates q hdD (a, z * b) = _
    rw [cyclicCoordinates_apply, map_mul, ← mul_assoc]
  exact compareCyclic p.embed q.embed p.τ q.τ
    (involutionApplySquare p hdB) (involutionApplySquare q hdD) e he p.conjugation hj'
    (by simpa [hdB] using p.power_uniformizer) hsq
    (cyclicCoordinates p hdB) c' (cyclicCoordinates_apply p hdB) hcoords

section LocalDivisionExistence

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem existsResidueQuadratic (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ a : Integers F, ∀ z : BaseResidue F, z ^ 2 + z ≠ IsLocalRing.residue _ a := by
  -- The polynomial map takes the same value at `0` and `-1`.
  let k := BaseResidue F
  let : Finite k := (localField_properties F).2.1
  let f (z : k) : k := z ^ 2 + z
  have hf : ¬ Function.Injective f := by
    intro h
    have h01 : (0 : k) = -1 := h (by dsimp [f]; ring)
    exact one_ne_zero (neg_eq_zero.mp h01.symm)
  have hs : ¬ Function.Surjective f := fun h => hf (Finite.injective_iff_surjective.mpr h)
  obtain ⟨a, ha⟩ : ∃ a : k, a ∉ Set.range f := not_forall.mp hs
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective (R := Integers F) a
  exact ⟨a₀, fun z hz => ha ⟨z, hz⟩⟩

/-- A unit of the integer ring has normalized value one. -/
private theorem normalizedValue_eq_one_of_residue_ne_zero {z : Integers F}
    (hz : IsLocalRing.residue _ z ≠ 0) : normalizedValuation F (z : F) = 1 := by
  have hu := (IsLocalRing.residue_ne_zero_iff_isUnit z).mp hz
  have hv : valuation F (z : F) = 1 :=
    (Valuation.valuationSubring.integers (valuation F)).isUnit_iff_valuation_eq_one.mp hu
  exact (congrArg (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F) hv).trans (map_one _)

private def binaryNorm (a x y : F) : F := x ^ 2 + x * y - a * y ^ 2

/-- Scaling by a coordinate of largest value reduces the norm calculation to a
unit, since the reduced quadratic has no root. -/
private theorem binaryNorm_value (a : Integers F)
    (ha : ∀ z : BaseResidue F, z ^ 2 + z ≠ IsLocalRing.residue _ a) (x y : F) :
    normalizedValuation F (binaryNorm (a : F) x y) =
      max (normalizedValuation F x) (normalizedValuation F y) ^ 2 := by
  obtain rfl | hy := eq_or_ne y 0
  · simp [binaryNorm]
  rcases le_or_gt (valuation F x) (valuation F y) with hxy | hxy
  · have hxy' : normalizedValuation F x ≤ normalizedValuation F y := base_le.mpr hxy
    rw [max_eq_right hxy']
    have hval : valuation F (x / y) ≤ 1 := by
      rw [map_div₀]
      exact (div_le_one₀ (pos_iff_ne_zero.mpr ((_root_.map_ne_zero _).mpr hy))).mpr hxy
    let z : Integers F := ⟨x / y, hval⟩
    have hz : IsLocalRing.residue _ (z ^ 2 + z - a) ≠ 0 := by
      simpa only [map_sub, map_pow, map_add, sub_ne_zero] using ha (IsLocalRing.residue _ z)
    have heq : binaryNorm (a : F) x y = y ^ 2 * ((z ^ 2 + z - a : Integers F) : F) := by
      change x ^ 2 + x * y - (a : F) * y ^ 2 = y ^ 2 * ((x / y) ^ 2 + x / y - (a : F))
      field_simp
    rw [heq, map_mul, map_pow, normalizedValue_eq_one_of_residue_ne_zero hz, mul_one]
  · have hyx : normalizedValuation F y ≤ normalizedValuation F x := base_le.mpr hxy.le
    rw [max_eq_left hyx]
    have hx : x ≠ 0 :=
      (map_ne_zero (valuation F)).mp (ne_of_gt (lt_of_le_of_lt _root_.zero_le hxy))
    have hval : valuation F (y / x) < 1 := by
      rw [map_div₀]
      exact (div_lt_one₀ (pos_iff_ne_zero.mpr ((_root_.map_ne_zero _).mpr hx))).mpr hxy
    let z : Integers F := ⟨y / x, hval.le⟩
    have hz : IsLocalRing.residue _ z = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
      exact hval
    have hunit : IsLocalRing.residue _ (1 + z - a * z ^ 2) ≠ 0 := by simp [hz]
    have heq : binaryNorm (a : F) x y = x ^ 2 * ((1 + z - a * z ^ 2 : Integers F) : F) := by
      change x ^ 2 + x * y - (a : F) * y ^ 2 = x ^ 2 * (1 + y / x - (a : F) * (y / x) ^ 2)
      field_simp
    rw [heq, map_mul, map_pow, normalizedValue_eq_one_of_residue_ne_zero hunit, mul_one]

/-- A square value and a uniformizer times a square value can only agree at zero. -/
private theorem square_eq_uniformizer_mul_square {x y : ℤᵐ⁰}
    (h : x ^ 2 = WithZero.exp (-1) * y ^ 2) : x = 0 ∧ y = 0 := by
  obtain rfl | hy := eq_or_ne y 0
  · simpa using h
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact (mul_ne_zero WithZero.exp_ne_zero (pow_ne_zero _ hy)) h.symm
  rw [← WithZero.exp_log hx, ← WithZero.exp_log hy, pow_two, pow_two,
    ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add] at h
  have he := WithZero.exp_injective h
  omega

private theorem quaternionNorm_ne_zero (a : Integers F)
    (ha : ∀ z : BaseResidue F, z ^ 2 + z ≠ IsLocalRing.residue _ a) {t : F}
    (ht : normalizedValuation F t = WithZero.exp (-1)) {q : QuaternionAlgebra F (a : F) 1 t}
    (hq : q ≠ 0) : (q * star q).re ≠ 0 := by
  have hnorm : (q * star q).re = binaryNorm (a : F) q.re q.imI -
      t * binaryNorm (a : F) q.imJ q.imK := by
    simp [binaryNorm]
    ring
  intro h
  rw [hnorm, sub_eq_zero] at h
  have hval := congrArg (normalizedValuation F) h
  simp only [map_mul, binaryNorm_value a ha, ht] at hval
  obtain ⟨hx, hy⟩ := square_eq_uniformizer_mul_square hval
  have eq_zero {z : F} (hz : normalizedValuation F z ≤ 0) : z = 0 :=
    (map_eq_zero (normalizedValuation F)).mp (le_antisymm hz _root_.zero_le)
  exact hq (QuaternionAlgebra.ext
    (eq_zero ((le_max_left _ _).trans_eq hx))
    (eq_zero ((le_max_right _ _).trans_eq hx))
    (eq_zero ((le_max_left _ _).trans_eq hy))
    (eq_zero ((le_max_right _ _).trans_eq hy)))

end LocalDivisionExistence

private theorem quaternion_isUnit_of_norm_ne_zero {F : Type*} [Field F] {a b t : F}
    {q : QuaternionAlgebra F a b t} (hq : (q * star q).re ≠ 0) : IsUnit q := by
  let A := QuaternionAlgebra F a b t
  let r := (q * star q).re
  have hnorm : q * star q = algebraMap F A r := q.mul_star_eq_coe
  have hnorm' : star q * q = algebraMap F A r := (star_comm_self' q).trans hnorm
  refine ⟨⟨q, algebraMap F A r⁻¹ * star q, ?_, ?_⟩, rfl⟩
  · rw [← mul_assoc, ← Algebra.commutes r⁻¹ q, mul_assoc, hnorm, ← map_mul,
      inv_mul_cancel₀ hq, map_one]
  · rw [mul_assoc, hnorm', ← map_mul, inv_mul_cancel₀ hq, map_one]

private theorem quaternion_central {F : Type*} [Field F] {a t : F}
    (hu : ∀ q : QuaternionAlgebra F a 1 t, IsUnit q ∨ q = 0) :
    Algebra.IsCentral F (QuaternionAlgebra F a 1 t) := by
  let A := QuaternionAlgebra F a 1 t
  constructor
  intro q hq
  rw [Algebra.mem_bot]
  refine ⟨q.re, ?_⟩
  have hc := (Subalgebra.mem_center_iff (R := F)).mp hq
  let i : A := ⟨0, 1, 0, 0⟩
  let j : A := ⟨0, 0, 1, 0⟩
  let p : A := ⟨q.re, q.imI, 0, 0⟩
  let r : A := ⟨0, 0, q.imJ, q.imK⟩
  have hqpr : q = p + r := by ext <;> simp [A, p, r]
  have hp : i * p = p * i := by ext <;> simp [A, i, p]
  have hr : r * i = (1 - i) * r := by
    ext <;> simp [A, i, r]
    ring
  have hri : i * r = r * i := by
    have he := hc i
    rw [hqpr, mul_add, add_mul, hp] at he
    exact add_left_cancel he
  have hz : (1 - i - i) * r = 0 := by rw [sub_mul, ← hr, ← hri, sub_self]
  have hi : (1 - i - i : A) ≠ 0 := by
    intro h
    have h' := congrArg QuaternionAlgebra.re h
    simp [A, i] at h'
  have hr0 : r = 0 := by
    let : DivisionRing A := DivisionRing.ofIsUnitOrEqZero hu
    exact (mul_eq_zero.mp hz).resolve_left hi
  have hm : (j * p).imJ = (p * j).imJ := by
    have he := hc j
    rw [hqpr, hr0, add_zero] at he
    exact congrArg QuaternionAlgebra.imJ he
  have himI : q.imI = 0 := by
    have h' : q.re + q.imI = q.re := by simpa [A, p, j] using hm
    exact add_left_cancel (h'.trans (add_zero _).symm)
  rw [hqpr, hr0, add_zero]
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, p, himI]

/-- A residue quadratic with no root gives a quaternion algebra whose conjugate
norm is anisotropic when the second generator squares to a uniformizer. -/
theorem local_division_exists : LocalDivisionExists.{u} := by
  intro F _ _ _ _
  obtain ⟨a, ha⟩ := existsResidueQuadratic F
  obtain ⟨t, ht⟩ : ∃ t : F, baseValue F t = WithZero.exp (-1) :=
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).surjective.comp
      (valuation_surjective (K := F))) (WithZero.exp (-1))
  let A := QuaternionAlgebra F (a : F) 1 t
  have hu (q : A) : IsUnit q ∨ q = 0 := by
    obtain rfl | hq := eq_or_ne q 0
    · exact Or.inr rfl
    · exact Or.inl (quaternion_isUnit_of_norm_ne_zero (quaternionNorm_ne_zero a ha ht hq))
  let : DivisionRing A := DivisionRing.ofIsUnitOrEqZero hu
  refine ⟨A, inferInstance, inferInstance, ⟨quaternion_central hu, inferInstance⟩, ?_⟩
  change Nat.sqrt (Module.finrank F (QuaternionAlgebra F (a : F) 1 t)) = 2
  rw [QuaternionAlgebra.finrank_eq_four]
  exact Nat.sqrt_eq' 2

end LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting
