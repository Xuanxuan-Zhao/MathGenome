import Specs.LinearAlgebraicGroups.Arithmetic.QuaternionMixedCommutators
import Specs.LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting
import LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.MvPolynomial

import LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting
namespace LinearAlgebraicGroups.Arithmetic.QuaternionMixedCommutators

open scoped commutatorElement TensorProduct
open RM03.CSA
open LocalQuadraticSplitting

section General

variable {F : Type*} [Field F] {B : Type*} [DivisionRing B] [Algebra F B]
  {E : Type*} [Field E] [Algebra F E] (i : E →ₐ[F] B)

private theorem mixed_mem (a : Bˣ) (b : Eˣ) :
    ⁅a, Units.map i.toMonoidHom b⁆ ∈ mixedSubgroup i :=
  Subgroup.subset_closure ⟨a, b, rfl⟩

private theorem mixed_normal : (mixedSubgroup i).Normal := by
  constructor
  intro x hx c
  refine Subgroup.closure_induction (p := fun y _ => c * y * c⁻¹ ∈ mixedSubgroup i)
    (fun y hy => ?_) (by simp)
    (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_) hx
  · obtain ⟨a, b, rfl⟩ := hy
    have h : c * ⁅a, Units.map i.toMonoidHom b⁆ * c⁻¹ =
        ⁅c * a, Units.map i.toMonoidHom b⁆ * ⁅c, Units.map i.toMonoidHom b⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact (mixedSubgroup i).mul_mem (mixed_mem i _ _) ((mixedSubgroup i).inv_mem (mixed_mem i _ _))
  · have h : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
    rw [h]
    exact (mixedSubgroup i).mul_mem ha hb
  · have h : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
    rw [h]
    exact (mixedSubgroup i).inv_mem ha

private noncomputable def normHom (hB : IsCentralSimple F B) : Bˣ →* Fˣ :=
  Units.map
    { toFun := reducedNorm hB
      map_one' := reducedNorm_one hB
      map_mul' := reducedNorm_mul hB }

private theorem mixed_le_normOne (hB : IsCentralSimple F B) :
    (mixedSubgroup i : Set Bˣ) ⊆ normOne hB := by
  let N := normHom hB
  have hh : mixedSubgroup i ≤ N.ker := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨a, b, rfl⟩
    change N _ = 1
    simp only [commutatorElement_def, map_mul, map_inv]
    rw [mul_right_comm (N a), mul_inv_cancel, one_mul, mul_inv_cancel]
  intro x hx
  exact congrArg Units.val (hh hx : N x = 1)

private theorem continuous_reducedNorm [TopologicalSpace F] [IsTopologicalRing F]
    (hB : IsCentralSimple F B) :
    let : TopologicalSpace B := moduleTopology F B
    Continuous (reducedNorm hB : B → F) := by
  let : TopologicalSpace B := moduleTopology F B
  let : Module.Finite F B := hB.2.2
  let b := Module.finBasis F B
  have he (x : B) : reducedNorm hB x = MvPolynomial.eval (b.equivFun x) (genericReducedNorm hB b) :=
    (reducedNorm_basis_eval hB b x).symm
  exact ((MvPolynomial.continuous_eval (p := genericReducedNorm hB b)).comp
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)).congr
      (fun x => (he x).symm)

private theorem isClosed_normOne [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    (hB : IsCentralSimple F B) :
    letI := unitsTopology F B
    IsClosed (normOne hB) := by
  let := unitsTopology F B
  let : TopologicalSpace B := moduleTopology F B
  exact isClosed_singleton.preimage
    ((continuous_reducedNorm hB).comp continuous_induced_dom)

end General

section DegreeTwo


variable {F : Type*} [Field F] {B : Type*} [DivisionRing B] [Algebra F B]

private noncomputable def traceValue (hB : IsCentralSimple F B) (x : B) : F :=
  LocalDivisionAlgebras.reducedTrace hB x

private theorem matrix_trace_reindex {L : Type*} [Field L] {n : ℕ}
    (e : Fin n ≃ Fin 2) (M : Matrix (Fin n) (Fin n) L) :
    ((Matrix.reindex e e) M).trace = M.trace :=
  (Fintype.sum_equiv e.symm _ _ (fun _ => rfl))

private theorem exists_matrix_model (hB : IsCentralSimple F B) (hd : degree F B = 2)
    {L : Type*} [Field L] [Algebra F L]
    (e : BaseChange F L B ≃ₐ[L] Matrix (Fin (degree F B)) (Fin (degree F B)) L) :
    ∃ f : B →ₐ[F] Matrix (Fin 2) (Fin 2) L,
      (∀ x, algebraMap F L (reducedNorm hB x) = (f x).det) ∧
      (∀ x, algebraMap F L (traceValue hB x) = (f x).trace) := by
  let j : Fin (degree F B) ≃ Fin 2 := finCongr hd
  let f := ((e.trans (Matrix.reindexAlgEquiv L L j)).toAlgHom.restrictScalars F).comp
    Algebra.TensorProduct.includeRight
  refine ⟨f, fun x => ?_, fun x => ?_⟩
  · rw [reducedNorm_map hB x e]
    exact (Matrix.det_reindex_self j (e (1 ⊗ₜ[F] x))).symm
  · rw [traceValue, LocalDivisionAlgebras.reducedTrace_map hB e x]
    exact (matrix_trace_reindex j (e (1 ⊗ₜ[F] x))).symm

private theorem matrix_quadratic {L : Type*} [Field L] (M : Matrix (Fin 2) (Fin 2) L) :
    M * M - M.trace • M + M.det • 1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two,
      Fin.sum_univ_two] <;> ring

private theorem quadratic_identity (hB : IsCentralSimple F B) (hd : degree F B = 2) (x : B) :
    x * x - algebraMap F B (traceValue hB x) * x + algebraMap F B (reducedNorm hB x) = 0 := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hB
  obtain ⟨f, hn, ht⟩ := exists_matrix_model hB hd e
  apply f.injective
  have scalar (a : F) : f (algebraMap F B a) =
      (algebraMap F (AlgebraicClosure F) a) • (1 : Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) := by
    rw [f.commutes,
      IsScalarTower.algebraMap_apply F (AlgebraicClosure F) (Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)),
      Algebra.algebraMap_eq_smul_one]
  change f (x * x - algebraMap F B (traceValue hB x) * x +
    algebraMap F B (reducedNorm hB x)) = f 0
  simp only [map_add, map_sub, map_mul, map_zero, scalar, ht, hn,
    Matrix.smul_mul, one_mul]
  exact matrix_quadratic (f x)

private noncomputable def traceLinear (hB : IsCentralSimple F B) (hd : degree F B = 2) :
    B →ₗ[F] F := by
  let L := AlgebraicClosure F
  have hf : ∃ f : B →ₐ[F] Matrix (Fin 2) (Fin 2) L,
      ∀ x, algebraMap F L (traceValue hB x) = (f x).trace := by
    obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hB
    obtain ⟨f, _, ht⟩ := exists_matrix_model hB hd e
    exact ⟨f, ht⟩
  refine
    { toFun := traceValue hB
      map_add' := fun x y => ?_
      map_smul' := fun a x => ?_ }
  · obtain ⟨f, ht⟩ := hf
    apply (algebraMap F L).injective
    change algebraMap F L (traceValue hB (x + y)) =
      algebraMap F L (traceValue hB x + traceValue hB y)
    rw [ht (x + y), map_add f, Matrix.trace_add, map_add (algebraMap F L), ht x, ht y]
  · obtain ⟨f, ht⟩ := hf
    apply (algebraMap F L).injective
    change algebraMap F L (traceValue hB (a • x)) =
      algebraMap F L (a * traceValue hB x)
    rw [ht, map_smul, map_mul, ht]
    rw [← Algebra.smul_def]
    exact Matrix.trace_smul _ _

private theorem trace_one (hB : IsCentralSimple F B) (hd : degree F B = 2) :
    traceLinear hB hd 1 = 2 := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hB
  obtain ⟨f, _, ht⟩ := exists_matrix_model hB hd e
  apply (algebraMap F (AlgebraicClosure F)).injective
  change algebraMap F (AlgebraicClosure F) (traceValue hB 1) = _
  rw [ht, map_one, Matrix.trace_one, Fintype.card_fin, map_ofNat]
  rfl

private theorem trace_sub_one_ne_zero (hB : IsCentralSimple F B) (hd : degree F B = 2)
    {x : B} (hx : reducedNorm hB x = 1) (hx1 : x ≠ 1) :
    traceLinear hB hd (x - 1) ≠ 0 := by
  intro hz
  rw [map_sub, trace_one] at hz
  have ht : traceValue hB x = 2 := sub_eq_zero.mp hz
  have hquad := quadratic_identity hB hd x
  rw [hx, ht, map_one, map_ofNat] at hquad
  have hsq : (x - 1) * (x - 1) = 0 := calc
    (x - 1) * (x - 1) = x * x - (2 : B) * x + 1 := by noncomm_ring
    _ = 0 := hquad
  exact hx1 (sub_eq_zero.mp (mul_self_eq_zero.mp hsq))

/-- The quadratic identity constructs an intertwiner of two elements with the
same reduced trace and norm. An element outside the center guarantees a nonzero
intertwiner. -/
private theorem exists_intertwiner (hB : IsCentralSimple F B) (hd : degree F B = 2)
    {b y : B} (hb : b ∉ Set.range (algebraMap F B))
    (ht : traceValue hB y = traceValue hB b)
    (hn : reducedNorm hB y = reducedNorm hB b) :
    ∃ a : B, a ≠ 0 ∧ y * a = a * b := by
  let t := algebraMap F B (traceValue hB b)
  let n := algebraMap F B (reducedNorm hB b)
  have hty (c : B) : t * c = c * t := Algebra.commutes _ _
  have hnc (c : B) : n * c = c * n := Algebra.commutes _ _
  have hyy : y * y - t * y = -n := by
    have h := quadratic_identity hB hd y
    rw [ht, hn] at h
    exact eq_neg_of_add_eq_zero_left h
  have hbb : b * b - t * b = -n := eq_neg_of_add_eq_zero_left
    (quadratic_identity hB hd b)
  let a (c : B) := y * c + c * b - t * c
  have ha (c : B) : y * a c = a c * b := by
    calc
      y * a c = (y * y - t * y) * c + y * c * b := by
        dsimp only [a]
        rw [mul_sub, mul_add, sub_mul, ← mul_assoc y, ← mul_assoc y c,
          ← mul_assoc y t, ← hty y]
        abel
      _ = (-n) * c + y * c * b := by rw [hyy]
      _ = y * c * b + c * (-n) := by rw [neg_mul, mul_neg, hnc, add_comm]
      _ = y * c * b + c * (b * b - t * b) := by rw [hbb]
      _ = a c * b := by
        dsimp only [a]
        rw [mul_sub, sub_mul, add_mul, ← mul_assoc c b, ← mul_assoc c t, ← hty c]
        abel
  by_contra! h
  have hz (c : B) : a c = 0 := by
    by_contra hc
    exact h (a c) hc (ha c)
  have hyb : y = t - b := by
    have h1 := hz 1
    simp only [a, mul_one, one_mul, sub_eq_zero] at h1
    exact eq_sub_of_add_eq h1
  have hcomm (c : B) : c * b = b * c := by
    have hc := hz c
    simp only [a, hyb, sub_mul, sub_eq_zero] at hc
    apply add_left_cancel (a := t * c - b * c)
    rw [hc]
    abel
  have hc : b ∈ Subalgebra.center F B := Subalgebra.mem_center_iff.mpr hcomm
  exact hb (Algebra.mem_bot.mp (hB.2.1.out hc))

variable {E : Type*} [Field E] [Algebra F E]

private theorem exists_nonscalar (hE : Module.finrank F E = 2) :
    ∃ b : E, b ∉ Set.range (algebraMap F E) := by
  by_contra! h
  have hsurj : Function.Surjective (algebraMap F E) := h
  have hdim : Module.finrank F E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr ⟨(algebraMap F E).injective, hsurj⟩
  rw [hE] at hdim
  contradiction

/-- A nonidentity norm-one quaternion is a single commutator with second
entry in the fixed subfield. The trace condition is arranged by a scalar
shift of a nonscalar element of that subfield. -/
private theorem exists_mixed_commutator (hB : IsCentralSimple F B) (hd : degree F B = 2)
    (i : E →ₐ[F] B) (hE : Module.finrank F E = 2) {x : Bˣ}
    (hx : reducedNorm hB (x : B) = 1) (hx1 : x ≠ 1) :
    ∃ (a : Bˣ) (b : Eˣ), x = ⁅a, Units.map i.toMonoidHom b⁆ := by
  let tr := traceLinear hB hd
  let l := tr.comp ((LinearMap.mulLeft F ((x : B) - 1)).comp i.toLinearMap)
  have hl1 : l 1 ≠ 0 := by
    change tr (((x : B) - 1) * i 1) ≠ 0
    rw [map_one, mul_one]
    exact trace_sub_one_ne_zero hB hd hx (fun he => hx1 (Units.ext he))
  obtain ⟨b₀, hb₀⟩ := exists_nonscalar hE
  let c := l b₀ / l 1
  let b := b₀ - c • (1 : E)
  have hlb : l b = 0 := by
    change l (b₀ - c • (1 : E)) = 0
    rw [map_sub, map_smul, smul_eq_mul, show c * l 1 = l b₀ from div_mul_cancel₀ _ hl1,
      sub_self]
  have hb : i b ∉ Set.range (algebraMap F B) := by
    rintro ⟨d, hd⟩
    have he : algebraMap F E d = b := i.injective ((i.commutes d).trans hd)
    apply hb₀
    exact ⟨d + c, by
      rw [map_add, he, Algebra.algebraMap_eq_smul_one]
      exact sub_add_cancel _ _⟩
  have hbne : b ≠ 0 := by
    intro he
    apply hb
    exact ⟨0, by rw [he, map_zero, map_zero]⟩
  let y := (x : B) * i b
  have ht : traceValue hB y = traceValue hB (i b) := by
    change tr (((x : B) - 1) * i b) = 0 at hlb
    rw [sub_mul, one_mul, map_sub] at hlb
    exact sub_eq_zero.mp hlb
  have hn : reducedNorm hB y = reducedNorm hB (i b) := by
    change reducedNorm hB ((x : B) * i b) = _
    rw [reducedNorm_mul, hx, one_mul]
  obtain ⟨a, ha, hconj⟩ := exists_intertwiner hB hd hb ht hn
  let ua := Units.mk0 a ha
  let ub := Units.mk0 b hbne
  let vb := Units.map i.toMonoidHom ub
  have hyu : (x * vb) * ua = ua * vb := Units.ext hconj
  refine ⟨ua, ub, ?_⟩
  calc
    x = (x * vb * ua) * ua⁻¹ * vb⁻¹ := by group
    _ = ⁅ua, vb⁆ := by rw [hyu, commutatorElement_def]

private theorem mixed_eq_normOne (hB : IsCentralSimple F B) (hd : degree F B = 2)
    (i : E →ₐ[F] B) (hE : Module.finrank F E = 2) :
    (mixedSubgroup i : Set Bˣ) = normOne hB := by
  refine Set.Subset.antisymm (mixed_le_normOne i hB) (fun x hx => ?_)
  by_cases hx1 : x = 1
  · exact hx1 ▸ (mixedSubgroup i).one_mem
  · obtain ⟨a, b, rfl⟩ := exists_mixed_commutator hB hd i hE hx hx1
    exact mixed_mem i a b

end DegreeTwo

/-- Over nonarchimedean local fields, the mixed commutators are dense in the
norm-one group. The algebraic equality holds over any field. -/
theorem nonarchimedean_mixed_commutators_conditional.{u, v, w}
    (_ : ComplexSplitting.{v})
    (_ : LocalDivisionUnique.{u, v, w})
    (_ : OddExtensionDivision.{u, v, w})
    (_ : QuadraticEmbedding.{u, v, w})
    (_ : QuadraticSplitting.{u, v, w})
    (_ : RealDivision.{v})
    (_ : SplittingDegree.{u, v, w}) :
    NonarchimedeanMixedCommutators.{u, v, w} := by
  intro F _ _ _ _ B _ _ hB hd E _ _ _ i hE
  let := unitsTopology F B
  refine ⟨mixed_normal i, ?_⟩
  rw [mixed_eq_normOne hB hd i hE, (isClosed_normOne hB).closure_eq]

/-- Over the reals the mixed commutators generate the full norm-one group. -/
theorem real_mixed_commutators_conditional.{v}
    (_ : ComplexSplitting.{v})
    (_ : LocalDivisionUnique.{v, v, v})
    (_ : OddExtensionDivision.{v, v, v})
    (_ : QuadraticEmbedding.{v, v, v})
    (_ : QuadraticSplitting.{v, v, v})
    (_ : RealDivision.{v})
    (_ : SplittingDegree.{v, v, v}) :
    RealMixedCommutators.{v} := by
  intro B _ _ hB hd i
  let := unitsTopology ℝ B
  have he := mixed_eq_normOne hB hd i Complex.finrank_real_complex
  refine ⟨mixed_normal i, he, ?_⟩
  rw [he]
  exact (isClosed_normOne hB).closure_eq

end LinearAlgebraicGroups.Arithmetic.QuaternionMixedCommutators

universe v8_closure_4a9ddbe6754af5af_u0 v8_closure_4a9ddbe6754af5af_u1 v8_closure_4a9ddbe6754af5af_u2
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionMixedCommutators».«nonarchimedean_mixed_commutators» : _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionMixedCommutators».«NonarchimedeanMixedCommutators».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u1, v8_closure_4a9ddbe6754af5af_u2} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionMixedCommutators».«nonarchimedean_mixed_commutators_conditional».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u1, v8_closure_4a9ddbe6754af5af_u2} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«complex_splitting».{v8_closure_4a9ddbe6754af5af_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«local_division_unique».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u1, v8_closure_4a9ddbe6754af5af_u2}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«odd_extension_division».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u1, v8_closure_4a9ddbe6754af5af_u2}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«quadratic_embedding».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u1, v8_closure_4a9ddbe6754af5af_u2}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«quadratic_splitting».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u1, v8_closure_4a9ddbe6754af5af_u2}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«real_division».{v8_closure_4a9ddbe6754af5af_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«splitting_degree».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u1, v8_closure_4a9ddbe6754af5af_u2})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionMixedCommutators».«real_mixed_commutators» : _root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionMixedCommutators».«RealMixedCommutators».{v8_closure_4a9ddbe6754af5af_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuaternionMixedCommutators».«real_mixed_commutators_conditional».{v8_closure_4a9ddbe6754af5af_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«complex_splitting».{v8_closure_4a9ddbe6754af5af_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«local_division_unique».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«odd_extension_division».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«quadratic_embedding».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«quadratic_splitting».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«real_division».{v8_closure_4a9ddbe6754af5af_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuadraticSplitting».«splitting_degree».{v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u0, v8_closure_4a9ddbe6754af5af_u0})
