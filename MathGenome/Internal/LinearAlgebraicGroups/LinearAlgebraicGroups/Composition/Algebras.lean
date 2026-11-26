import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.Algebras
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Tactic.Ring

/-! Regular composition norms and their extension to arbitrary scalar rings. -/

namespace LinearAlgebraicGroups.Composition

open scoped TensorProduct
open TensorProduct
open LinearMap (BilinForm)

universe u v w
variable {R : Type u} {A : Type v}

/-- A regular composition norm on a nonzero finite-dimensional unital algebra. -/
abbrev IsFieldCompositionNorm := @Specification.FieldNormConditions

/-- A composition norm on a finite locally free unital algebra of rank eight. -/
abbrev IsOctonionNorm := @Specification.OctonionNormConditions

/-- Scalar extension of the norm, including in characteristic two. -/
noncomputable abbrev normBaseChange := @Specification.normBaseChange

/-- The norm takes the value zero on some nonzero vector. -/
def IsIsotropic := @Specification.isotropic

/-- The octonion algebra with its norm is isomorphic to the Zorn model over the base ring. -/
def IsSplitOctonion := @Specification.splitOctonion

/-- Identification with the standard split model of the corresponding dimension. -/
def IsSplit := @Specification.split

/-- The norm of the scalar composition model is the square. -/
def scalarNorm := Specification.scalarNorm

/-- The standard involution on the scalar model is the identity. -/
def scalarConjugate := Specification.scalarConjugate

theorem full_polar_formula [CommRing R] [AddCommGroup A] [Module R A]
    (n : QuadraticForm R A) (x y : A) :
    n.polarBilin x y = n (x + y) - n x - n y := rfl

@[simp] theorem normBaseChange_tmul [CommRing R] [AddCommGroup A] [Module R A]
    [projective : Module.Projective R A] (S : Type w) [CommRing S] [Algebra R S]
    (n : QuadraticForm R A) (s : S) (x : A) :
    Specification.normBaseChange S n (s ⊗ₜ x) = s * s * algebraMap R S (n x) := by
  let retraction := Finsupp.linearCombination R (id : A → A)
  let sectionMap := (Module.projective_def (R := R) (P := A)).mp projective |>.choose
  have retracts : retraction (sectionMap x) = x :=
    (Module.projective_def (R := R) (P := A)).mp projective |>.choose_spec x
  let basis := Module.Free.chooseBasis R (A →₀ R)
  let : LinearOrder (Module.Free.ChooseBasisIndex R (A →₀ R)) :=
    IsWellOrder.linearOrder WellOrderingRel
  let b := (n.comp retraction).toBilin basis
  change (BilinForm.baseChange S (b.compl₁₂ sectionMap sectionMap)).toQuadraticMap
      (s ⊗ₜ x) = _
  rw [LinearMap.BilinMap.toQuadraticMap_apply, BilinForm.baseChange_tmul,
    LinearMap.compl₁₂_apply, ← LinearMap.BilinMap.toQuadraticMap_apply,
    QuadraticMap.toQuadraticMap_toBilin, QuadraticMap.comp_apply, retracts]
  rw [Algebra.smul_def, mul_comm]

theorem polar_normBaseChange : Specification.polarBaseChange := by
  intro R A _ _ _ _ S _ _ n
  apply AlgebraTensorModule.ext
  intro s x
  apply AlgebraTensorModule.ext
  intro t y
  have onOriginal :
      (Specification.normBaseChange S n).polarBilin (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) =
        algebraMap R S (n.polarBilin x y) := by
    rw [full_polar_formula, ← TensorProduct.tmul_add]
    simp [QuadraticMap.polar]
  have hs : s ⊗ₜ[R] x = s • ((1 : S) ⊗ₜ[R] x) := by simp [TensorProduct.smul_tmul']
  have ht : t ⊗ₜ[R] y = t • ((1 : S) ⊗ₜ[R] y) := by simp [TensorProduct.smul_tmul']
  simp only [BilinForm.baseChange_tmul, Algebra.smul_def]
  rw [hs, ht, LinearMap.map_smul₂, map_smul, onOriginal]
  simp only [smul_eq_mul]
  ring

theorem perfect_polar_normBaseChange : Specification.perfectPolarAfterBaseChange := by
  intro R A _ _ _ _ _ S _ _ n h
  let b := (normBaseChange S n).polarBilin
  let e := LinearEquiv.ofBijective n.polarBilin h.bijective_left
  let baseEquiv := (e.baseChange R S A (Module.Dual R A)).restrictScalars R
  let liftEquiv := (LinearMap.liftBaseChangeEquiv S :
    (A →ₗ[R] S) ≃ₗ[S] Module.Dual S (S ⊗[R] A)).restrictScalars R
  let extended := baseEquiv.trans ((TensorProduct.comm R S (Module.Dual R A)).trans
    ((dualTensorHomEquiv R A S).trans liftEquiv))
  have eq : b.restrictScalars R = extended.toLinearMap := by
    apply TensorProduct.ext'
    intro s x
    apply AlgebraTensorModule.ext
    intro t y
    change b (s ⊗ₜ x) (t ⊗ₜ y) = extended (s ⊗ₜ x) (t ⊗ₜ y)
    have hbase : b = BilinForm.baseChange S n.polarBilin := polar_normBaseChange S n
    rw [hbase, BilinForm.baseChange_tmul]
    simp [extended, baseEquiv, liftEquiv, e, Algebra.smul_def,
      mul_assoc, mul_comm, mul_left_comm]
  have bij : Function.Bijective b := by
    change Function.Bijective (b.restrictScalars R)
    rw [eq]
    exact extended.bijective
  have symmetric : b.flip = b := LinearMap.ext₂ fun x y =>
    QuadraticMap.polar_comm (normBaseChange S n) y x
  exact ⟨bij, symmetric.symm ▸ bij⟩

private theorem multiplicative_of_one_tmul {S : Type w}
    [CommRing R] [NonAssocRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [CommRing S] [Algebra R S] (q : QuadraticForm S (S ⊗[R] A))
    (h : ∀ a b : A, q ((1 ⊗ₜ[R] a) * (1 ⊗ₜ[R] b)) =
      q (1 ⊗ₜ[R] a) * q (1 ⊗ₜ[R] b))
    (x y : S ⊗[R] A) : q (x * y) = q x * q y := by
  let m := LinearMap.mul S (S ⊗[R] A)
  have onOriginal (a : A) : q.comp (m (1 ⊗ₜ[R] a)) = q (1 ⊗ₜ[R] a) • q := by
    refine baseChange_ext (R := R) (A := S) fun b => ?_
    simpa only [m, QuadraticMap.comp_apply, LinearMap.mul_apply', smul_apply,
      smul_eq_mul] using h a b
  have extended : q.comp (m.flip y) = q y • q := by
    refine baseChange_ext (R := R) (A := S) fun a => ?_
    have ha := congrArg (fun F : QuadraticForm S (S ⊗[R] A) => F y) (onOriginal a)
    simpa only [m, QuadraticMap.comp_apply, LinearMap.mul_apply', smul_apply,
      smul_eq_mul, LinearMap.flip_apply, mul_comm] using ha
  have hx := congrArg (fun F : QuadraticForm S (S ⊗[R] A) => F x) extended
  simpa only [m, QuadraticMap.comp_apply, LinearMap.mul_apply', smul_apply,
    smul_eq_mul, LinearMap.flip_apply, mul_comm] using hx

theorem norm_comp_after_baseChange : Specification.normCompositionAfterBaseChange := by
  intro R A _ _ _ _ _ _ n multiplicative S _ _
  apply multiplicative_of_one_tmul
  intro a b
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, normBaseChange_tmul,
    multiplicative, map_mul]

theorem norm_comp_before_baseChange : Specification.normCompositionBeforeBaseChange := by
  intro R A _ _ _ _ _ _ n h x y
  simpa [normBaseChange_tmul] using h (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)

theorem octonion_norm_mul : Specification.octonionNormMultiplicative := by
  intro R A _ _ _ _ _ n h
  let := h.projective
  exact norm_comp_before_baseChange n (h.multiplicative_after_baseChange R)

theorem octonion_norm_baseChange : Specification.octonionNormAfterBaseChange := by
  intro R A _ _ _ _ _ n h S _ _
  let := h.projective
  let := h.finite
  refine ⟨inferInstance, inferInstance, ?_, perfect_polar_normBaseChange S n h.perfect, ?_⟩
  · intro p
    rw [Module.rankAtStalk_baseChange, h.rank_eight]
  · exact norm_comp_after_baseChange _ (norm_comp_after_baseChange n (octonion_norm_mul h) S)

theorem octonion_norm_iff_field : Specification.octonionNormOverField := by
  intro R A _ _ _ _ _ n
  constructor
  · intro h
    let := h.finite
    let p : PrimeSpectrum R := Classical.choice inferInstance
    have dim : Module.finrank R A = 8 := by
      simpa using h.rank_eight p
    have : Nontrivial A := Module.finrank_pos_iff.mp (by rw [dim]; decide)
    exact ⟨⟨h.finite, inferInstance, h.perfect.nondegenerate, octonion_norm_mul h⟩, dim⟩
  · rintro ⟨h, dim⟩
    let := h.finite
    refine ⟨h.finite, inferInstance, fun p => ?_, ?_, ?_⟩
    · simpa using dim
    · apply LinearMap.IsPerfPair.of_injective
      · exact LinearMap.ker_eq_bot.mp
          (LinearMap.separatingLeft_iff_ker_eq_bot.mp h.nondegenerate.1)
      · rw [show n.polarBilin.flip = n.polarBilin from
            LinearMap.ext₂ fun x y => QuadraticMap.polar_comm n y x]
        exact LinearMap.ker_eq_bot.mp
          (LinearMap.separatingLeft_iff_ker_eq_bot.mp h.nondegenerate.1)
    · exact norm_comp_after_baseChange n h.multiplicative

theorem field_norm_one : Specification.fieldNormOne := by
  intro R A _ _ _ _ _ n h
  have := h.nontrivial
  by_contra hne
  have hn (x : A) : n x = 0 := by
    have hx : n x = n 1 * n x := by simpa only [one_mul] using h.multiplicative 1 x
    have hz : (1 - n 1) * n x = 0 := by rw [sub_mul, one_mul, ← hx, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  have : (1 : A) = 0 := h.nondegenerate.1 _ fun x => by simp [QuadraticMap.polar, hn]
  exact one_ne_zero this

theorem octonion_norm_one : Specification.octonionNormOne := by
  intro R A _ _ _ _ _ n h
  have mulNorm := octonion_norm_mul h
  let := h.projective
  let := h.finite
  have annihilates : 1 - n 1 ∈ Module.annihilator R A := by
    apply Module.mem_annihilator.mpr
    intro x
    apply h.perfect.separatingLeft
    intro y
    have hn (z : A) : n z = n 1 * n z := by
      simpa only [one_mul] using mulNorm 1 z
    calc
      n.polarBilin ((1 - n 1) • x) y = (1 - n 1) * n.polarBilin x y := by
        simp
      _ = 0 := by
        have hz (z : A) : (1 - n 1) * n z = 0 := by
          rw [sub_mul, one_mul, ← hn, sub_self]
        simp only [full_polar_formula, mul_sub, hz, sub_zero]
  have unit : IsUnit (n 1) := by
    by_contra hnu
    obtain ⟨m, hm, hmem⟩ := Ideal.exists_le_maximal (Ideal.span {n 1})
      (fun ht => hnu (Ideal.span_singleton_eq_top.mp ht))
    let p : PrimeSpectrum R := ⟨m, hm.isPrime⟩
    have support : p ∈ Module.support R A := by
      by_contra hn
      have hz := (Module.rankAtStalk_eq_zero_iff_notMem_support p).mpr hn
      rw [h.rank_eight p] at hz
      contradiction
    have he : n 1 ∈ m := hmem (Ideal.subset_span (Set.mem_singleton _))
    have hc : 1 - n 1 ∈ m := Module.annihilator_le_of_mem_support support annihilates
    have hone := m.add_mem hc he
    rw [sub_add_cancel] at hone
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m hone isUnit_one)
  have hidem : n 1 = n 1 * n 1 := by simpa only [one_mul] using mulNorm 1 1
  exact unit.mul_left_cancel (show n 1 * n 1 = n 1 * 1 by simpa using hidem.symm)

theorem left_norm_similarity : Specification.leftSimilarity := by
  intro R A _ _ _ _ _ n h x y z
  rw [full_polar_formula, ← mul_add, h, h, h, full_polar_formula]
  ring

theorem right_norm_similarity : Specification.rightSimilarity := by
  intro R A _ _ _ _ _ n h x y z
  rw [full_polar_formula, ← add_mul, h, h, h, full_polar_formula]
  ring

theorem scalar_model_laws : Specification.scalarModelLaws := by
  intro R _
  change (1 : R) * 1 = 1 ∧ (∀ x y : R, (x * y) * (x * y) = (x * x) * (y * y)) ∧
    (∀ x : R, x = x ∧ x * x = x * x) ∧ (∀ x y : R, x * y = y * x)
  exact ⟨one_mul _, fun x y => mul_mul_mul_comm _ _ _ _, fun _ => ⟨rfl, rfl⟩, mul_comm⟩

@[simp] theorem scalar_polar : Specification.scalarPolar := by
  intro R _ x y
  rw [full_polar_formula]
  change (x + y) * (x + y) - x * x - y * y = 2 * x * y
  ring

theorem scalar_polar_perfect_iff : Specification.scalarPerfectIff := by
  intro R _
  let p := (Specification.scalarNorm R).polarBilin
  let e := LinearMap.ringLmapEquivSelf R R R
  change p.IsPerfPair ↔ IsUnit (2 : R)
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.bijective_left.surjective (e.symm 1)
    have he : e (p x) = 1 := by rw [hx, e.apply_symm_apply]
    change p x 1 = 1 at he
    rw [show p x 1 = 2 * x * 1 from scalar_polar R x 1, mul_one] at he
    exact ⟨⟨2, x, he, (mul_comm x 2).trans he⟩, rfl⟩
  · rintro ⟨a, ha⟩
    let f : R ≃ₗ[R] R := LinearEquiv.smulOfUnit a
    have he (x : R) : e (p x) = f x := by
      change p x 1 = (a : R) * x
      rw [show p x 1 = 2 * x * 1 from scalar_polar R x 1, mul_one, ha]
    have bij : Function.Bijective p :=
      Function.Bijective.of_comp_iff' e.bijective p |>.mp
        ((show e ∘ p = f from funext he).symm ▸ f.bijective)
    have symmetric : p.flip = p :=
      LinearMap.ext₂ fun x y => QuadraticMap.polar_comm (Specification.scalarNorm R) y x
    exact ⟨bij, symmetric.symm ▸ bij⟩

theorem rank_one_requires_two_ne_zero : Specification.rankOneRequiresTwoNeZero := by
  intro R A _ _ _ _ _ n h dim twoZero
  have := h.nontrivial
  apply (one_ne_zero : (1 : A) ≠ 0)
  apply h.nondegenerate.1
  intro y
  obtain ⟨r, rfl⟩ := exists_smul_eq_of_finrank_eq_one dim (one_ne_zero : (1 : A) ≠ 0) y
  rw [map_smul, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
  simp [two_smul, ← two_mul, twoZero]

end LinearAlgebraicGroups.Composition
