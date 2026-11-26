import Specs.LinearAlgebraicGroups.Albert.CliffordModel
import LinearAlgebraicGroups.Composition.ZornModel
import Mathlib.Order.Sum.Order
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace LinearAlgebraicGroups.Albert.CliffordModel

open CliffordAlgebra Module
open scoped TensorProduct

universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {I : Type w} [LinearOrder I]

noncomputable abbrev orderedWord := @CliffordSpecification.orderedWord

private theorem negativeTriangular (q : QuadraticForm R V) (b : Basis I R V) :
    LinearMap.BilinMap.toQuadraticMap (-(q.toBilin b).flip) = 0 - q := by
  ext x
  have hx := congrArg (fun Q : QuadraticForm R V => Q x) (q.toQuadraticMap_toBilin b)
  change q.toBilin b x x = q x at hx
  simp [LinearMap.BilinMap.toQuadraticMap_apply, hx]

private theorem negativeTriangular_vanishes (q : QuadraticForm R V) (b : Basis I R V)
    {i j : I} (h : i < j) : (-(q.toBilin b).flip) (b i) (b j) = 0 := by
  simp [QuadraticMap.toBilin_apply, h.ne', h.not_gt]

private theorem contract_ordered_tail (q : QuadraticForm R V) (b : Basis I R V)
    (i : I) (l : List I) (h : ∀ j ∈ l, i < j) :
    contractLeft (Q := (0 : QuadraticForm R V)) ((-(q.toBilin b).flip) (b i))
      (l.map (ι (0 : QuadraticForm R V) ∘ b)).prod = 0 := by
  induction l with
  | nil => simp [contractLeft_one]
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, Function.comp_apply]
    rw [contractLeft_ι_mul, negativeTriangular_vanishes q b (h j (by simp)),
      ih (fun j hj => h j (by simp [hj])), zero_smul, mul_zero, sub_zero]

private theorem changeForm_ordered_list (q : QuadraticForm R V) (b : Basis I R V)
    (l : List I) (h : l.Pairwise (· < ·)) :
    changeForm (negativeTriangular q b) (l.map (ι q ∘ b)).prod =
      (l.map (ι (0 : QuadraticForm R V) ∘ b)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.pairwise_cons] at h
    simp only [List.map_cons, List.prod_cons, Function.comp_apply]
    rw [changeForm_ι_mul (negativeTriangular q b) (b i), ih h.2,
      contract_ordered_tail q b i l h.1, sub_zero]

/-- The ordered squarefree monomials form a basis, in every characteristic. -/
theorem ordered_basis : CliffordSpecification.orderedBasisType.{u,v,w} := by
  unfold CliffordSpecification.orderedBasisType
  intro R _ V _ _ I _ q b
  let e := changeFormEquiv (negativeTriangular q b)
  refine ⟨b.ExteriorAlgebra.map e.symm, fun s => ?_⟩
  rw [Basis.map_apply, LinearEquiv.symm_apply_eq]
  rw [ExteriorAlgebra.basis_apply_ofCard b (s := s) (n := s.card) rfl]
  let f := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl)
  change ExteriorAlgebra.ιMulti R s.card (b ∘ f) =
    changeForm (negativeTriangular q b) (CliffordSpecification.orderedWord q b s)
  rw [ExteriorAlgebra.ιMulti_apply]
  have h := (changeForm_ordered_list q b (List.ofFn f)
    (List.pairwise_ofFn.mpr fun i j hij => f.strictMono hij)).symm
  rw [List.map_ofFn, List.map_ofFn] at h
  exact h

noncomputable abbrev coefficientForm := @CliffordSpecification.coefficientForm

theorem coefficientForm_tmul (S : Type z) [CommRing S] [Algebra R S]
    (q : QuadraticForm R V) (b : Basis I R V) (a : S) (x : V) :
    coefficientForm S q b (a ⊗ₜ[R] x) = a * a * algebraMap R S (q x) := by
  change (LinearMap.BilinForm.baseChange S (q.toBilin b)).toQuadraticMap (a ⊗ₜ[R] x) = _
  rw [LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinForm.baseChange_tmul]
  have hx := congrArg (fun Q : QuadraticForm R V => Q x) (q.toQuadraticMap_toBilin b)
  change q.toBilin b x x = q x at hx
  rw [hx, Algebra.smul_def, mul_comm]

theorem coefficient_form_unique : CliffordSpecification.coefficientFormUniqueType.{u,v,w,z} := by
  intro R _ V _ _ I _ S _ _ q b Q
  constructor
  · rintro rfl x
    simpa using coefficientForm_tmul S q b 1 x
  · intro h
    apply baseChange_ext
    intro x
    simpa [coefficientForm_tmul] using h x


theorem vector_summand : CliffordSpecification.vectorSummandType.{u,v,w} := by
  unfold CliffordSpecification.vectorSummandType
  intro R _ V _ _ I _ q b
  let powers : ℕ → Submodule R (ExteriorAlgebra R V) := fun n => ⋀[R]^n V
  let P := DirectSum.component R ℕ (fun n => ↥(powers n)) 1 ∘ₗ
    (DirectSum.decomposeLinearEquiv powers).toLinearMap
  refine ⟨(exteriorPower.oneEquiv R V).toLinearMap ∘ₗ P ∘ₗ
    (changeForm (negativeTriangular q b)), ?_⟩
  ext x
  change exteriorPower.oneEquiv R V (P (changeForm (negativeTriangular q b) (ι q x))) = x
  rw [changeForm_ι]
  let f : Fin 1 → V := fun _ => x
  have he : (exteriorPower.ιMulti R 1 f : ExteriorAlgebra R V) = ExteriorAlgebra.ι R x := by
    simp [ExteriorAlgebra.ιMulti_succ_apply, f]
  suffices P (ExteriorAlgebra.ι R x) = exteriorPower.ιMulti R 1 f by
    rw [this, exteriorPower.oneEquiv_ιMulti]
  apply Subtype.ext
  rw [he]
  exact DirectSum.decompose_of_mem_same powers (he ▸ (exteriorPower.ιMulti R 1 f).property)

theorem coefficient_form_agreement : CliffordSpecification.coefficientFormAgreementType.{u,v,w,z} := by
  intro R _ V _ _ _ I _ S _ _ q b
  symm
  apply (coefficient_form_unique S q b _).mpr
  intro x
  simpa using Composition.normBaseChange_tmul S q (1 : S) x

private theorem prod_generators_mem (q : QuadraticForm R V) (l : List V) :
    (l.map (ι q)).prod ∈ evenOdd q (l.length : ZMod 2) := by
  induction l with
  | nil =>
    simpa using (SetLike.one_mem_graded (A := evenOdd q))
  | cons x l ih =>
    simpa only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
      add_comm (l.length : ZMod 2) 1] using
      SetLike.mul_mem_graded (ι_mem_evenOdd_one q x) ih

theorem ordered_word_parity (q : QuadraticForm R V) (b : Basis I R V) (s : Finset I) :
    CliffordSpecification.orderedWord q b s ∈ evenOdd q (s.card : ZMod 2) := by
  unfold CliffordSpecification.orderedWord
  have h := prod_generators_mem q (List.ofFn fun i : Fin s.card => b
    (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl) i))
  rw [List.map_ofFn, List.length_ofFn] at h
  exact h

private noncomputable def parityProjection (q : QuadraticForm R V) (k : ZMod 2) :
    CliffordAlgebra q →ₗ[R] CliffordAlgebra q :=
  (evenOdd q k).subtype ∘ₗ DirectSum.component R (ZMod 2) (fun j => ↥(evenOdd q j)) k ∘ₗ
    (DirectSum.decomposeLinearEquiv (evenOdd q)).toLinearMap

theorem parity_span : CliffordSpecification.paritySpanType.{u,v,w} := by
  unfold CliffordSpecification.paritySpanType
  intro R _ V _ _ I _ q b k
  classical
  obtain ⟨B, hB⟩ := ordered_basis q b
  refine le_antisymm (fun x hx => ?_) (Submodule.span_le.mpr ?_)
  · have hproj : parityProjection q k x = x := DirectSum.decompose_of_mem_same _ hx
    rw [← hproj, ← B.linearCombination_repr x, Finsupp.linearCombination_apply]
    rw [Finsupp.sum, map_sum]
    apply Submodule.sum_mem
    intro s _
    rw [map_smul, hB]
    apply Submodule.smul_mem
    by_cases h : (s.card : ZMod 2) = k
    · have hw : parityProjection q k (CliffordSpecification.orderedWord q b s) =
          CliffordSpecification.orderedWord q b s :=
        DirectSum.decompose_of_mem_same (evenOdd q) (i := k) (h ▸ ordered_word_parity q b s)
      rw [hw]
      exact Submodule.subset_span ⟨s, h, rfl⟩
    · have hw : parityProjection q k (CliffordSpecification.orderedWord q b s) = 0 :=
        DirectSum.decompose_of_mem_ne _ (ordered_word_parity q b s) h
      rw [hw]
      exact Submodule.zero_mem _
  · rintro _ ⟨s, hs, rfl⟩
    exact hs ▸ ordered_word_parity q b s


section BaseChange

variable (S : Type z) [CommRing S] [Algebra R S]
variable (q : QuadraticForm R V) (b : Basis I R V)

private noncomputable def fromOriginal :
    CliffordAlgebra q →ₐ[R] CliffordAlgebra (coefficientForm S q b) :=
  lift q ⟨(ι (coefficientForm S q b)).restrictScalars R ∘ₗ TensorProduct.mk R S V 1, fun x => by
    change ι (coefficientForm S q b) (1 ⊗ₜ[R] x) * ι _ (1 ⊗ₜ[R] x) = _
    rw [ι_sq_scalar, coefficientForm_tmul, one_mul, one_mul, ← IsScalarTower.algebraMap_apply R S]⟩

private theorem fromOriginal_ι (x : V) :
    fromOriginal S q b (ι q x) = ι (coefficientForm S q b) (1 ⊗ₜ[R] x) :=
  lift_ι_apply _ _ _

private noncomputable def fromTensor : S ⊗[R] CliffordAlgebra q →ₐ[S]
    CliffordAlgebra (coefficientForm S q b) :=
  AlgHom.liftEquiv R S _ _ (fromOriginal S q b)

private theorem fromTensor_ι (a : S) (x : V) :
    fromTensor S q b (a ⊗ₜ[R] ι q x) = ι (coefficientForm S q b) (a ⊗ₜ[R] x) := by
  rw [fromTensor, AlgHom.liftEquiv_tmul, fromOriginal_ι, ← map_smul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private noncomputable def toTensor : CliffordAlgebra (coefficientForm S q b) →ₐ[S]
    S ⊗[R] CliffordAlgebra q := by
  let f := (ι q).baseChange S
  let k := (Algebra.linearMap S (S ⊗[R] CliffordAlgebra q))
  let mulQ := LinearMap.BilinMap.toQuadraticMap (LinearMap.mul S (S ⊗[R] CliffordAlgebra q))
  refine lift _ ⟨f, fun x => ?_⟩
  have h : mulQ.comp f = k.compQuadraticMap (coefficientForm S q b) := by
    apply baseChange_ext
    intro v
    change f (1 ⊗ₜ[R] v) * f (1 ⊗ₜ[R] v) = k (coefficientForm S q b (1 ⊗ₜ[R] v))
    rw [show f = (ι q).baseChange S from rfl, LinearMap.baseChange_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ι_sq_scalar, coefficientForm_tmul, one_mul,
      one_mul]
    change (1 : S) ⊗ₜ[R] algebraMap R (CliffordAlgebra q) (q v) = algebraMap S _ _
    rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply R S]
    rfl
  change (mulQ.comp f) x = (k.compQuadraticMap (coefficientForm S q b)) x
  rw [h]

private theorem toTensor_ι (a : S) (x : V) :
    toTensor S q b (ι (coefficientForm S q b) (a ⊗ₜ[R] x)) = a ⊗ₜ[R] ι q x := by
  unfold toTensor
  exact (lift_ι_apply _ _ _).trans (LinearMap.baseChange_tmul _ _ _)

/-- The algebra isomorphism is induced by transport of the vector generators. -/
noncomputable def baseChangeEquiv : S ⊗[R] CliffordAlgebra q ≃ₐ[S]
    CliffordAlgebra (coefficientForm S q b) :=
  AlgEquiv.ofAlgHom (fromTensor S q b) (toTensor S q b)
    (by
      apply CliffordAlgebra.hom_ext
      apply (b.baseChange S).ext
      intro i
      change fromTensor S q b (toTensor S q b (ι _ ((b.baseChange S) i))) =
        ι _ ((b.baseChange S) i)
      rw [Basis.baseChange_apply, toTensor_ι, fromTensor_ι])
    (by
      apply Algebra.TensorProduct.ext_ring
      apply CliffordAlgebra.hom_ext
      ext x
      change toTensor S q b (fromTensor S q b (1 ⊗ₜ[R] ι q x)) = 1 ⊗ₜ[R] ι q x
      rw [fromTensor_ι, toTensor_ι])

@[simp] theorem baseChangeEquiv_ι (a : S) (x : V) :
    baseChangeEquiv S q b (a ⊗ₜ[R] ι q x) = ι (coefficientForm S q b) (a ⊗ₜ[R] x) :=
  fromTensor_ι S q b a x

private theorem baseChangeEquiv_word (s : Finset I) :
    baseChangeEquiv S q b (1 ⊗ₜ[R] CliffordSpecification.orderedWord q b s) =
      CliffordSpecification.orderedWord (coefficientForm S q b) (b.baseChange S) s := by
  change ((baseChangeEquiv S q b).toAlgHom.restrictScalars R)
    (Algebra.TensorProduct.includeRight (CliffordSpecification.orderedWord q b s)) = _
  rw [CliffordSpecification.orderedWord, CliffordSpecification.orderedWord, map_list_prod,
    map_list_prod, List.map_ofFn, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [Basis.baseChange_apply]
  exact baseChangeEquiv_ι S q b 1 _

private theorem baseChangeEquiv_evenOdd (k : ZMod 2) :
    ((evenOdd q k).baseChange S).map (baseChangeEquiv S q b).toLinearEquiv.toLinearMap =
      evenOdd (coefficientForm S q b) k := by
  rw [parity_span q b k, Submodule.baseChange_span, Submodule.map_span,
    parity_span (coefficientForm S q b) (b.baseChange S) k]
  simp only [Set.image_image]
  apply congrArg (Submodule.span S)
  exact congrArg (fun f : Finset I → CliffordAlgebra (coefficientForm S q b) =>
    f '' {s | (s.card : ZMod 2) = k}) (funext (baseChangeEquiv_word S q b))

private theorem fromOriginal_reverse (x : CliffordAlgebra q) :
    fromOriginal S q b (reverse x) = reverse (fromOriginal S q b x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [reverse.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply R S, reverse.commutes]
  | ι x => simp only [reverse_ι, fromOriginal_ι]
  | mul x y hx hy => simp only [reverse.map_mul, map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem baseChangeEquiv_reverse (x : S ⊗[R] CliffordAlgebra q) :
    baseChangeEquiv S q b ((reverse (Q := q)).baseChange S x) =
      reverse (baseChangeEquiv S q b x) := by
  induction x with
  | tmul a y =>
    rw [LinearMap.baseChange_tmul]
    change fromTensor S q b (a ⊗ₜ[R] reverse y) = reverse (fromTensor S q b (a ⊗ₜ[R] y))
    simp only [fromTensor, AlgHom.liftEquiv_tmul, map_smul, fromOriginal_reverse]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem base_change_model : CliffordSpecification.baseChangeType.{u,v,w,z} := by
  intro R _ V _ _ I _ S _ _ q b
  exact ⟨baseChangeEquiv S q b, baseChangeEquiv_ι S q b, baseChangeEquiv_word S q b,
    baseChangeEquiv_evenOdd S q b, baseChangeEquiv_reverse S q b⟩

end BaseChange


private theorem grade_step (k : ZMod 2) : 1 + (1 + k) = k := by
  rw [← add_assoc, show (1 + 1 : ZMod 2) = 0 by decide, zero_add]

private theorem parity_cases (k : ZMod 2) : k = 0 ∨ k = 1 := by
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl

section GradedAction

variable {W : Type z} [AddCommGroup W] [Module R W]

private theorem word_action (q : QuadraticForm R V) (P : ZMod 2 → Submodule R W)
    (f : CliffordAlgebra q →ₐ[R] Module.End R W)
    (hv : ∀ k v x, x ∈ P k → f (ι q v) x ∈ P (1 + k))
    (l : List V) (j : ZMod 2) (x : W) (hx : x ∈ P j) :
    f (l.map (ι q)).prod x ∈ P ((l.length : ZMod 2) + j) := by
  induction l with
  | nil => simpa [Module.End.one_apply] using hx
  | cons v l ih =>
    simpa only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, List.length_cons,
      Nat.cast_add, Nat.cast_one, ← add_assoc, add_comm (1 : ZMod 2) (l.length : ZMod 2)] using
      hv _ v _ ih

private theorem graded_action (q : QuadraticForm R V) (b : Basis I R V)
    (P : ZMod 2 → Submodule R W) (f : CliffordAlgebra q →ₐ[R] Module.End R W)
    (hv : ∀ k v x, x ∈ P k → f (ι q v) x ∈ P (1 + k))
    {i j : ZMod 2} {a : CliffordAlgebra q} (ha : a ∈ evenOdd q i)
    {x : W} (hx : x ∈ P j) : f a x ∈ P (i + j) := by
  rw [parity_span q b i] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, hs, rfl⟩ := ha
    have hw := word_action q P f hv (List.ofFn fun k : Fin s.card => b
      (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl) k)) j x hx
    rw [List.map_ofFn, List.length_ofFn] at hw
    change (s.card : ZMod 2) = i at hs
    rw [← hs]
    exact hw
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add, LinearMap.add_apply] using (P _).add_mem ha hb
  | smul r a _ ha => simpa only [map_smul, LinearMap.smul_apply] using (P _).smul_mem r ha

private theorem even_iff_preserves_blocks
    (q : QuadraticForm R V) (b : Basis I R V)
    (P : ZMod 2 → Submodule R W) (hP : IsCompl (P 0) (P 1))
    (f : CliffordAlgebra q →ₐ[R] Module.End R W) (hf : Function.Injective f)
    (hv : ∀ k v x, x ∈ P k → f (ι q v) x ∈ P (1 + k))
    (a : CliffordAlgebra q) :
    a ∈ evenOdd q 0 ↔ ∀ k x, x ∈ P k → f a x ∈ P k := by
  constructor
  · intro ha k x hx
    simpa only [zero_add] using graded_action q b P f hv ha hx
  · intro ha
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp
      (show a ∈ evenOdd q 0 ⊔ evenOdd q 1 by rw [(evenOdd_isCompl (Q := q)).sup_eq_top]; trivial)
    suffices hz0 : z = 0 by simpa [hz0] using hy
    apply hf
    apply LinearMap.ext
    intro x
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ :=
      Submodule.mem_sup.mp (show x ∈ P 0 ⊔ P 1 by rw [hP.sup_eq_top]; trivial)
    have h₀ : f z x₀ ∈ P 0 := by
      have hsum := ha 0 x₀ hx₀
      rw [map_add, LinearMap.add_apply] at hsum
      have hy₀ : f y x₀ ∈ P 0 := by
        simpa only [zero_add] using graded_action q b P f hv hy hx₀
      simpa using (P 0).sub_mem hsum hy₀
    have h₁ : f z x₁ ∈ P 1 := by
      have hsum := ha 1 x₁ hx₁
      rw [map_add, LinearMap.add_apply] at hsum
      have hy₁ : f y x₁ ∈ P 1 := by
        simpa only [zero_add] using graded_action q b P f hv hy hx₁
      simpa using (P 1).sub_mem hsum hy₁
    have hz₀ : f z x₀ = 0 := Submodule.disjoint_def.mp hP.disjoint _ h₀ (by
      simpa only [add_zero] using graded_action q b P f hv hz hx₀)
    have hz₁ : f z x₁ = 0 := Submodule.disjoint_def.mp hP.disjoint _ (by
      simpa only [show (1 + 1 : ZMod 2) = 0 by decide] using graded_action q b P f hv hz hx₁) h₁
    simp [map_add, hz₀, hz₁]

end GradedAction

section Hyperbolic

private abbrev zeroForm : QuadraticForm R V := 0

private noncomputable def create (x : V) : Module.End R (ExteriorAlgebra R V) :=
  (Algebra.lmul R _ (ExteriorAlgebra.ι R x))

private abbrev contract (d : Module.Dual R V) : Module.End R (ExteriorAlgebra R V) :=
  contractLeft (Q := (zeroForm : QuadraticForm R V)) d

private theorem hyperbolicOperator_apply (d : Module.Dual R V) (x : V)
    (a : ExteriorAlgebra R V) :
    CliffordSpecification.hyperbolicOperator (d, x) a =
      ExteriorAlgebra.ι R x * a + contract d a := rfl

private theorem hyperbolicOperator_sq (x : Module.Dual R V × V) :
    CliffordSpecification.hyperbolicOperator x * CliffordSpecification.hyperbolicOperator x =
      algebraMap R _ (QuadraticForm.dualProd R V x) := by
  obtain ⟨d,x⟩ := x
  apply LinearMap.ext
  intro a
  change CliffordSpecification.hyperbolicOperator (d, x)
    (CliffordSpecification.hyperbolicOperator (d, x) a) = d x • a
  simp only [hyperbolicOperator_apply, map_add]
  have hc := contractLeft_ι_mul (Q := (0 : QuadraticForm R V)) d x a
  change contract d (ExteriorAlgebra.ι R x * a) =
    d x • a - ExteriorAlgebra.ι R x * contract d a at hc
  rw [hc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul,
    contractLeft_contractLeft, zero_add, add_zero]
  abel

/-- The Clifford action by exterior multiplication and contraction. -/
def hyperbolicRepresentation :
    CliffordAlgebra (QuadraticForm.dualProd R V) →ₐ[R] Module.End R (ExteriorAlgebra R V) :=
  lift _ ⟨CliffordSpecification.hyperbolicOperator, hyperbolicOperator_sq⟩

theorem hyperbolicRepresentation_ι (x : Module.Dual R V × V) :
    hyperbolicRepresentation (ι _ x) = CliffordSpecification.hyperbolicOperator x :=
  lift_ι_apply _ _ _

private noncomputable def exteriorWord (b : Basis I R V) (l : List I) :
    ExteriorAlgebra R V := (l.map (ExteriorAlgebra.ι R ∘ b)).prod

omit [LinearOrder I] in
private theorem exteriorWord_cons (b : Basis I R V) (i : I) (l : List I) :
    exteriorWord b (i :: l) = ExteriorAlgebra.ι R (b i) * exteriorWord b l := rfl

private theorem contract_absent (b : Basis I R V) (i : I) (l : List I) (h : i ∉ l) :
    contract (b.coord i) (exteriorWord b l) = 0 := by
  classical
  induction l with
  | nil => exact contractLeft_one (Q := (0 : QuadraticForm R V)) (b.coord i)
  | cons j l ih =>
    simp only [List.mem_cons, not_or] at h
    rw [exteriorWord_cons, contractLeft_ι_mul, ih h.2, Basis.coord_apply]
    simp [h.1]

private theorem create_contract_word (b : Basis I R V) (i : I) (l : List I) (h : l.Nodup) :
    create (b i) (contract (b.coord i) (exteriorWord b l)) =
      if i ∈ l then exteriorWord b l else 0 := by
  classical
  induction l with
  | nil => simp [exteriorWord, create, contractLeft_one]
  | cons j l ih =>
    rw [List.nodup_cons] at h
    by_cases hij : i = j
    · subst j
      simp [exteriorWord_cons, create, contractLeft_ι_mul, contract_absent b i l h.1]
    · have hswap : ExteriorAlgebra.ι R (b i) * ExteriorAlgebra.ι R (b j) =
          -(ExteriorAlgebra.ι R (b j) * ExteriorAlgebra.ι R (b i)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      have hrec := ih h.2
      change ExteriorAlgebra.ι R (b i) * contract (b.coord i) (exteriorWord b l) = _ at hrec
      change ExteriorAlgebra.ι R (b i) * contract (b.coord i) (exteriorWord b (j :: l)) = _
      rw [exteriorWord_cons, contractLeft_ι_mul, Basis.coord_apply,
        show (b.repr (b j)) i = 0 by simp [hij], zero_smul, zero_sub, mul_neg,
        ← mul_assoc, hswap, neg_mul, neg_neg, mul_assoc, hrec]
      by_cases hil : i ∈ l <;> simp [hij, hil]

private noncomputable def orderedIndices (s : Finset I) : List I :=
  List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl))

private theorem mem_orderedIndices (i : I) (s : Finset I) :
    i ∈ orderedIndices s ↔ i ∈ s := by
  rw [orderedIndices, List.mem_ofFn]
  exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ i

private theorem orderedIndices_nodup (s : Finset I) : (orderedIndices s).Nodup := by
  unfold orderedIndices
  rw [List.nodup_ofFn]
  exact (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl)).injective

private theorem exteriorBasis_word (b : Basis I R V) (s : Finset I) :
    b.ExteriorAlgebra s = exteriorWord b (orderedIndices s) := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (s := s) rfl, exteriorWord, orderedIndices,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
  rfl

private theorem create_contract_basis (b : Basis I R V) (i : I) (s : Finset I) :
    create (b i) (contract (b.coord i) (b.ExteriorAlgebra s)) =
      if i ∈ s then b.ExteriorAlgebra s else 0 := by
  classical
  rw [exteriorBasis_word b s, create_contract_word b i _ (orderedIndices_nodup s)]
  simp only [mem_orderedIndices]

private theorem create_in_range (x : V) : create x ∈
    (hyperbolicRepresentation (R := R) (V := V)).range :=
  ⟨ι _ (0, x), by
    change hyperbolicRepresentation (ι _ (0, x)) = _
    rw [hyperbolicRepresentation_ι]
    apply LinearMap.ext
    intro a
    simp [hyperbolicOperator_apply, create]⟩

private theorem contract_in_range (d : Module.Dual R V) : contract d ∈
    (hyperbolicRepresentation (R := R) (V := V)).range :=
  ⟨ι _ (d, 0), by
    change hyperbolicRepresentation (ι _ (d, 0)) = _
    rw [hyperbolicRepresentation_ι]
    apply LinearMap.ext
    intro a
    simp [hyperbolicOperator_apply]⟩

private noncomputable def occupation (b : Basis I R V) (i : I) :
    Module.End R (ExteriorAlgebra R V) :=
  create (b i) * contract (b.coord i)

private noncomputable def matchingOccupation [DecidableEq I]
    (b : Basis I R V) (t : Finset I) (i : I) : Module.End R (ExteriorAlgebra R V) :=
  if i ∈ t then occupation b i else 1 - occupation b i

private theorem matchingOccupation_apply [DecidableEq I] (b : Basis I R V)
    (t s : Finset I) (i : I) :
    matchingOccupation b t i (b.ExteriorAlgebra s) =
      if (i ∈ t ↔ i ∈ s) then b.ExteriorAlgebra s else 0 := by
  have h : occupation b i (b.ExteriorAlgebra s) = _ := create_contract_basis b i s
  by_cases ht : i ∈ t <;> by_cases hs : i ∈ s <;>
    simp [matchingOccupation, ht, hs, h, Module.End.one_apply]

private theorem occupationProduct_apply [DecidableEq I] (b : Basis I R V)
    (t s : Finset I) (l : List I) :
    (l.map (matchingOccupation b t)).prod (b.ExteriorAlgebra s) =
      if (∀ i ∈ l, i ∈ t ↔ i ∈ s) then b.ExteriorAlgebra s else 0 := by
  induction l with
  | nil => simp [Module.End.one_apply]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
    by_cases h : ∀ j ∈ l, j ∈ t ↔ j ∈ s
    · rw [ite_eq_left h, matchingOccupation_apply]
      have hiff : (∀ j ∈ i :: l, j ∈ t ↔ j ∈ s) ↔ (i ∈ t ↔ i ∈ s) :=
        List.forall_mem_cons.trans (and_iff_left h)
      simp only [hiff]
    · rw [ite_eq_right h, map_zero, ite_eq_right (fun hh => h (List.forall_mem_cons.mp hh).2)]

private noncomputable def wedgeProjector [Fintype I] (b : Basis I R V) (t : Finset I) :
    Module.End R (ExteriorAlgebra R V) := by
  classical
  exact ((Finset.univ : Finset I).toList.map (matchingOccupation b t)).prod

private theorem wedgeProjector_apply [Fintype I] (b : Basis I R V) (t s : Finset I) :
    wedgeProjector b t (b.ExteriorAlgebra s) = if t = s then b.ExteriorAlgebra s else 0 := by
  classical
  rw [wedgeProjector, occupationProduct_apply]
  simp only [Finset.mem_toList, Finset.mem_univ, true_implies, ← Finset.ext_iff]

private theorem wedgeProjector_in_range [Fintype I] (b : Basis I R V) (t : Finset I) :
    wedgeProjector b t ∈ (hyperbolicRepresentation (R := R) (V := V)).range := by
  classical
  unfold wedgeProjector
  let p := (hyperbolicRepresentation (R := R) (V := V)).range
  suffices ∀ l : List I, (l.map (matchingOccupation b t)).prod ∈ p by exact this _
  intro l
  induction l with
  | nil => exact p.one_mem
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons]
    apply p.mul_mem _ ih
    have ho : occupation b i ∈ p := p.mul_mem (create_in_range _) (contract_in_range _)
    by_cases h : i ∈ t
    · simpa [matchingOccupation, h] using ho
    · simpa [matchingOccupation, h] using p.sub_mem p.one_mem ho

private noncomputable def peelWord (b : Basis I R V) (l : List I) :
    Module.End R (ExteriorAlgebra R V) := (l.reverse.map (contract ∘ b.coord)).prod

private theorem peelWord_apply (b : Basis I R V) (l : List I) (hl : l.Nodup) :
    peelWord b l (exteriorWord b l) = 1 := by
  classical
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [peelWord, List.reverse_cons, List.map_append, List.prod_append, Module.End.mul_apply]
    change peelWord b l (contract (b.coord i) (exteriorWord b (i :: l))) = _
    rw [exteriorWord_cons, contractLeft_ι_mul, contract_absent b i l hl.1, Basis.coord_apply]
    simpa using ih hl.2

omit [LinearOrder I] in
private theorem peelWord_in_range (b : Basis I R V) (l : List I) :
    peelWord b l ∈ (hyperbolicRepresentation (R := R) (V := V)).range := by
  unfold peelWord
  let p := (hyperbolicRepresentation (R := R) (V := V)).range
  suffices ∀ l : List I, (l.map (contract ∘ b.coord)).prod ∈ p by exact this _
  intro l
  induction l with
  | nil => exact p.one_mem
  | cons i l ih => exact p.mul_mem (contract_in_range _) ih

private theorem exteriorWord_lmul_in_range (b : Basis I R V) (l : List I) :
    Algebra.lmul R _ (exteriorWord b l) ∈ (hyperbolicRepresentation (R := R) (V := V)).range := by
  induction l with
  | nil =>
    change Algebra.lmul R _ 1 ∈ _
    rw [map_one]
    exact Subalgebra.one_mem _
  | cons i l ih =>
    rw [exteriorWord_cons, map_mul]
    exact Subalgebra.mul_mem _ (create_in_range _) ih

private theorem matrixUnit_in_range [Fintype I] (b : Basis I R V) (s t : Finset I) :
    ((LinearMap.toSpanSingleton R _ (b.ExteriorAlgebra s)).comp (b.ExteriorAlgebra.coord t)) ∈
      (hyperbolicRepresentation (R := R) (V := V)).range := by
  classical
  let p := (hyperbolicRepresentation (R := R) (V := V)).range
  let f := Algebra.lmul R _ (b.ExteriorAlgebra s) * (peelWord b (orderedIndices t) * wedgeProjector b t)
  have hf : f ∈ p := p.mul_mem
    (by rw [exteriorBasis_word]; exact exteriorWord_lmul_in_range b _)
    (p.mul_mem (peelWord_in_range b _) (wedgeProjector_in_range b t))
  suffices f = (LinearMap.toSpanSingleton R _ (b.ExteriorAlgebra s)).comp
      (b.ExteriorAlgebra.coord t) by exact this ▸ hf
  apply b.ExteriorAlgebra.ext
  intro u
  change b.ExteriorAlgebra s *
    peelWord b (orderedIndices t) (wedgeProjector b t (b.ExteriorAlgebra u)) =
    (b.ExteriorAlgebra.coord t (b.ExteriorAlgebra u)) • b.ExteriorAlgebra s
  rw [wedgeProjector_apply, Basis.coord_apply]
  by_cases h : t = u
  · subst u
    rw [ite_eq_left rfl, exteriorBasis_word b t, peelWord_apply _ _ (orderedIndices_nodup t)]
    simp [← exteriorBasis_word b t]
  · simp [h]

theorem hyperbolicRepresentation_surjective [Fintype I] (b : Basis I R V) :
    Function.Surjective (hyperbolicRepresentation (R := R) (V := V)) := by
  classical
  intro f
  change f ∈ (hyperbolicRepresentation (R := R) (V := V)).range
  let B := b.ExteriorAlgebra
  let p := (hyperbolicRepresentation (R := R) (V := V)).range
  let term (s t : Finset I) := (B.repr (f (B t))) s •
    ((LinearMap.toSpanSingleton R _ (B s)).comp (B.coord t))
  have hmem : (∑ t, ∑ s, term s t) ∈ p := by
    apply p.toSubmodule.sum_mem
    intro t _
    apply p.toSubmodule.sum_mem
    intro s _
    exact p.toSubmodule.smul_mem _ (matrixUnit_in_range b s t)
  suffices (∑ t, ∑ s, term s t) = f by exact this ▸ hmem
  apply B.ext
  intro u
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, term, Basis.coord_apply]
  rw [Finset.sum_eq_single u]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

private noncomputable def hyperbolicBasis [Fintype I] (b : Basis I R V) :
    Basis (I ⊕ₗ I) R (Module.Dual R V × V) :=
  (b.dualBasis.prod b).reindex toLex

theorem hyperbolicRepresentation_bijective [Fintype I] (b : Basis I R V) :
    Function.Bijective (hyperbolicRepresentation (R := R) (V := V)) := by
  have hs := hyperbolicRepresentation_surjective b
  rcases subsingleton_or_nontrivial R with h | h
  · let := Module.subsingleton R (CliffordAlgebra (QuadraticForm.dualProd R V))
    exact ⟨Function.injective_of_subsingleton _, hs⟩
  classical
  obtain ⟨B, _⟩ := ordered_basis (QuadraticForm.dualProd R V) (hyperbolicBasis b)
  let E := b.ExteriorAlgebra
  have := Module.Free.of_basis B
  have := Module.Finite.of_basis B
  have := Module.Free.of_basis E
  have := Module.Finite.of_basis E
  apply OrzechProperty.bijective_of_surjective_of_finrank_le hyperbolicRepresentation.toLinearMap hs
  rw [Module.finrank_eq_card_basis B, Module.finrank_linearMap, Module.finrank_eq_card_basis E,
    Fintype.card_finset, Fintype.card_finset,
    ← Fintype.card_congr (toLex : (I ⊕ I) ≃ (I ⊕ₗ I)), Fintype.card_sum, pow_add]

/-- The hyperbolic Clifford algebra is the full endomorphism algebra of the exterior algebra. -/
noncomputable def hyperbolicEquiv [Fintype I] (b : Basis I R V) :
    CliffordAlgebra (QuadraticForm.dualProd R V) ≃ₐ[R] Module.End R (ExteriorAlgebra R V) :=
  AlgEquiv.ofBijective hyperbolicRepresentation (hyperbolicRepresentation_bijective b)

@[simp] theorem hyperbolicEquiv_ι [Fintype I] (b : Basis I R V) (x : Module.Dual R V × V) :
    hyperbolicEquiv b (ι _ x) = CliffordSpecification.hyperbolicOperator x :=
  hyperbolicRepresentation_ι x

theorem hyperbolic_scalar_centralizer [Fintype I] (b : Basis I R V)
    (a : CliffordAlgebra (QuadraticForm.dualProd R V)) :
    (∀ v, Commute a (ι (QuadraticForm.dualProd R V) v)) ↔
      ∃ r : R, a = algebraMap R _ r := by
  constructor
  · intro h
    let e := hyperbolicEquiv b
    let B := b.ExteriorAlgebra
    let r := B.coord ∅ (e a (B ∅))
    have hc (z : CliffordAlgebra (QuadraticForm.dualProd R V)) : Commute a z := by
      induction z using CliffordAlgebra.induction with
      | algebraMap t => exact (Algebra.commutes t a).symm
      | ι x => exact h x
      | mul x y hx hy => exact hx.mul_right hy
      | add x y hx hy => exact hx.add_right hy
    refine ⟨r, e.injective ?_⟩
    rw [AlgEquiv.commutes]
    apply LinearMap.ext
    intro x
    let f : Module.End R (ExteriorAlgebra R V) :=
      (LinearMap.toSpanSingleton R _ x).comp (B.coord ∅)
    have hm : Commute (e a) f := by
      simpa using (hc (e.symm f)).map e
    have he := congrArg (fun T : Module.End R (ExteriorAlgebra R V) => T (B ∅)) hm.eq
    change e a (B.coord ∅ (B ∅) • x) = r • x at he
    simpa using he
  · rintro ⟨r, rfl⟩ v
    exact Algebra.commutes r _

private theorem contract_list_grade (d : Module.Dual R V) (l : List V) :
    contract d (l.map (ExteriorAlgebra.ι R)).prod ∈
      evenOdd (0 : QuadraticForm R V) (1 + (l.length : ZMod 2)) := by
  induction l with
  | nil => simp [contractLeft_one]
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hindex : (1 : ZMod 2) + ((l.length : ZMod 2) + 1) = (l.length : ZMod 2) := by
      rw [add_comm (l.length : ZMod 2) 1, grade_step]
    rw [hindex, contractLeft_ι_mul]
    refine (evenOdd (0 : QuadraticForm R V) _).sub_mem ?_ ?_
    · apply Submodule.smul_mem
      exact prod_generators_mem (0 : QuadraticForm R V) l
    · simpa only [grade_step] using SetLike.mul_mem_graded
        (ι_mem_evenOdd_one (0 : QuadraticForm R V) x) ih

private theorem contract_grade (b : Basis I R V) (d : Module.Dual R V)
    (j : ZMod 2) (x : ExteriorAlgebra R V) (hx : x ∈ evenOdd (0 : QuadraticForm R V) j) :
    contract d x ∈ evenOdd (0 : QuadraticForm R V) (1 + j) := by
  change x ∈ evenOdd (0 : QuadraticForm R V) j at hx
  rw [parity_span (0 : QuadraticForm R V) b j] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    have hw := contract_list_grade d (List.ofFn fun k : Fin s.card => b
      (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl) k))
    rw [List.map_ofFn, List.length_ofFn] at hw
    change (s.card : ZMod 2) = j at hs
    rw [← hs]
    exact hw
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (evenOdd _ _).add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using (evenOdd _ _).smul_mem r hx

private theorem hyperbolicOperator_grade (b : Basis I R V) (j : ZMod 2)
    (v : Module.Dual R V × V) (x : ExteriorAlgebra R V)
    (hx : x ∈ evenOdd (0 : QuadraticForm R V) j) :
    CliffordSpecification.hyperbolicOperator v x ∈ evenOdd (0 : QuadraticForm R V) (1 + j) := by
  obtain ⟨d, v⟩ := v
  rw [hyperbolicOperator_apply]
  exact (evenOdd _ _).add_mem
    (SetLike.mul_mem_graded (ι_mem_evenOdd_one (0 : QuadraticForm R V) v) hx)
    (contract_grade b d j x hx)

theorem hyperbolicEquiv_even [Fintype I] (b : Basis I R V)
    (a : CliffordAlgebra (QuadraticForm.dualProd R V)) :
    a ∈ evenOdd (QuadraticForm.dualProd R V) 0 ↔
      ∀ k x, x ∈ evenOdd (0 : QuadraticForm R V) k →
        hyperbolicEquiv b a x ∈ evenOdd (0 : QuadraticForm R V) k :=
  even_iff_preserves_blocks _ (hyperbolicBasis b) _ (evenOdd_isCompl (0 : QuadraticForm R V))
    (hyperbolicEquiv b).toAlgHom (hyperbolicEquiv b).injective
    (fun k v x hx => by
      change hyperbolicEquiv b (ι _ v) x ∈ _
      rw [hyperbolicEquiv_ι]
      exact hyperbolicOperator_grade b k v x hx) a

theorem hyperbolic_model : CliffordSpecification.hyperbolicModelType.{u,v,w} := by
  intro R _ V _ _ I _ _ b
  exact ⟨hyperbolicEquiv b, hyperbolicEquiv_ι b, hyperbolicEquiv_even b,
    hyperbolic_scalar_centralizer b⟩

end Hyperbolic


section Octonions

open _root_.LinearAlgebraicGroups.Composition Composition.Zorn

private abbrev octonionNorm := Composition.Zorn.norm

private theorem octonionOperator_sq (c : Zorn R) :
    CliffordSpecification.octonionOperator c * CliffordSpecification.octonionOperator c =
      algebraMap R _ (octonionNorm R c) := by
  apply LinearMap.ext
  intro x
  have h := (isOctonion R).toNormLaws
  exact Prod.ext (conjugate_left_products h c x.1).2 (conjugate_left_products h c x.2).1

/-- The split octonion Clifford action on two copies of the octonions. -/
def octonionRepresentation :
    CliffordAlgebra (octonionNorm R) →ₐ[R] Module.End R (Zorn R × Zorn R) :=
  lift _ ⟨CliffordSpecification.octonionOperator, octonionOperator_sq⟩

theorem octonionRepresentation_ι (c : Zorn R) :
    octonionRepresentation (ι _ c) = CliffordSpecification.octonionOperator c :=
  lift_ι_apply _ _ _

private theorem octonionOperator_adjoint (c : Zorn R) :
    LinearMap.IsAdjointPair CliffordSpecification.octonionPairing
      CliffordSpecification.octonionPairing (CliffordSpecification.octonionOperator c)
      (CliffordSpecification.octonionOperator c) := by
  intro x y
  let n := octonionNorm R
  have h := (isOctonion R).toNormLaws
  change n.polarBilin (c * x.2) y.1 + n.polarBilin (conjugate n c * x.1) y.2 =
    n.polarBilin x.1 (c * y.2) + n.polarBilin x.2 (conjugate n c * y.1)
  rw [show n.polarBilin (c * x.2) y.1 = n.polarBilin x.2 (conjugate n c * y.1) from
    left_mul_adjoint h c x.2 y.1]
  rw [show n.polarBilin (conjugate n c * x.1) y.2 =
    n.polarBilin x.1 (conjugate n (conjugate n c) * y.2) from
    left_mul_adjoint h (conjugate n c) x.1 y.2, conjugate_involutive h, add_comm]

theorem octonionRepresentation_adjoint (a : CliffordAlgebra (octonionNorm R)) :
    LinearMap.IsAdjointPair CliffordSpecification.octonionPairing
      CliffordSpecification.octonionPairing (octonionRepresentation a)
      (octonionRepresentation (reverse a)) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [reverse.commutes, AlgHom.commutes]
    intro x y
    change CliffordSpecification.octonionPairing (r • x) y =
      CliffordSpecification.octonionPairing x (r • y)
    rw [LinearMap.map_smul₂, map_smul]
  | ι c => simpa only [reverse_ι, octonionRepresentation_ι] using octonionOperator_adjoint c
  | mul a b ha hb =>
    rw [reverse.map_mul, map_mul, map_mul]
    exact hb.comp ha
  | add a b ha hb =>
    rw [map_add, map_add, map_add]
    exact ha.add hb

/-- A unital algebra endomorphism of a finite square matrix algebra is invertible.
Its determinant is a unit because the map over every maximal-ideal quotient is injective. -/
private theorem matrixAlgHom_bijective {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (f : Matrix J J R →ₐ[R] Matrix J J R) : Function.Bijective f := by
  suffices h : IsUnit f.toLinearMap.det by
    have hfun : ((LinearMap.equivOfIsUnitDet (f := f.toLinearMap) h) :
        Matrix J J R → Matrix J J R) = f := by
      funext x
      exact LinearMap.equivOfIsUnitDet_apply h x
    exact hfun ▸ (LinearMap.equivOfIsUnitDet h).bijective
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ fun hh =>
    h (Ideal.span_singleton_eq_top.mp hh)
  let : m.IsMaximal := hm
  let K := R ⧸ m
  let : Field K := Ideal.Quotient.field m
  let e := (matrixEquivTensor J R K).symm
  let g := Algebra.TensorProduct.map (AlgHom.id R K) f
  let gK := e.toAlgHom.comp (g.comp e.symm.toAlgHom)
  have hinj : Function.Injective g := by
    intro x y hxy
    apply e.injective
    apply gK.toRingHom.injective
    have hK (z : K ⊗[R] Matrix J J R) : gK (e z) = e (g z) := by
      simp [gK]
    change gK (e x) = gK (e y)
    rw [hK, hK, hxy]
  have hf : Function.Injective (f.toLinearMap.baseChange K) := hinj
  have hn : (f.toLinearMap.baseChange K).det ≠ 0 :=
    fun hz => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hf)
  apply hn
  rw [LinearMap.det_baseChange]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_singleton _)))

private noncomputable def octonionIndexOrder : LinearOrder (Option (Fin 3)) :=
  IsWellOrder.linearOrder WellOrderingRel

private theorem octonionRepresentation_bijective : Function.Bijective
    (octonionRepresentation (R := R)) := by
  classical
  let E := Option (Fin 3)
  let : LinearOrder E := octonionIndexOrder
  let b := Pi.basisFun R E
  let bZ := Zorn.coordinateBasis R
  let B := bZ.prod bZ
  let i : Finset E ≃ ((E ⊕ E) ⊕ (E ⊕ E)) := Fintype.equivOfCardEq
    (by simp [E, Fintype.card_finset, Fintype.card_sum, Fintype.card_option, Fintype.card_fin])
  let D := b.ExteriorAlgebra.reindex i
  let a := (equivOfIsometry (hyperbolicIsometry R)).trans
    ((hyperbolicEquiv b).trans (LinearMap.toMatrixAlgEquiv D))
  let d := LinearMap.toMatrixAlgEquiv B
  let g := d.toAlgHom.comp (octonionRepresentation.comp a.symm.toAlgHom)
  have hg := matrixAlgHom_bijective g
  have hcomp : (octonionRepresentation (R := R) : _ → _) = d.symm ∘ g ∘ a := by
    funext x
    simp [g]
  rw [hcomp]
  exact d.symm.bijective.comp (hg.comp a.bijective)

noncomputable def octonionEquiv :
    CliffordAlgebra (octonionNorm R) ≃ₐ[R] Module.End R (Zorn R × Zorn R) :=
  AlgEquiv.ofBijective octonionRepresentation octonionRepresentation_bijective

@[simp] theorem octonionEquiv_ι (c : Zorn R) :
    octonionEquiv (ι _ c) = CliffordSpecification.octonionOperator c :=
  octonionRepresentation_ι c

theorem octonionEquiv_adjoint (a : CliffordAlgebra (octonionNorm R)) :
    LinearMap.IsAdjointPair CliffordSpecification.octonionPairing
      CliffordSpecification.octonionPairing (octonionEquiv a)
      (octonionEquiv (reverse a)) :=
  octonionRepresentation_adjoint a

private def octonionBlock (R : Type u) [CommRing R] (k : ZMod 2) :
    Submodule R (Zorn R × Zorn R) :=
  if k = 0 then LinearMap.range (LinearMap.inl R _ _) else
    LinearMap.range (LinearMap.inr R _ _)

private theorem octonionBlock_zero (x : Zorn R × Zorn R) :
    x ∈ octonionBlock R 0 ↔ x.2 = 0 := by
  simp [octonionBlock, LinearMap.range_inl, LinearMap.mem_ker]

private theorem octonionBlock_one (x : Zorn R × Zorn R) :
    x ∈ octonionBlock R 1 ↔ x.1 = 0 := by
  simp [octonionBlock, LinearMap.range_inr, LinearMap.mem_ker]

private theorem octonionBlock_isCompl (R : Type u) [CommRing R] :
    IsCompl (octonionBlock R 0) (octonionBlock R 1) := by
  simpa [octonionBlock] using (LinearMap.isCompl_range_inl_inr (R := R) (M := Zorn R) (M₂ := Zorn R))

private theorem octonionOperator_grade (k : ZMod 2) (c : Zorn R)
    (x : Zorn R × Zorn R) (hx : x ∈ octonionBlock R k) :
    CliffordSpecification.octonionOperator c x ∈ octonionBlock R (1 + k) := by
  rcases parity_cases k with rfl | rfl
  · rw [add_zero, octonionBlock_one]
    change c * x.2 = 0
    rw [(octonionBlock_zero x).mp hx, mul_zero]
  · rw [show (1 + 1 : ZMod 2) = 0 by decide, octonionBlock_zero]
    change conjugate (octonionNorm R) c * x.1 = 0
    rw [(octonionBlock_one x).mp hx, mul_zero]

theorem octonionEquiv_even (a : CliffordAlgebra (octonionNorm R)) :
    a ∈ evenOdd (octonionNorm R) 0 ↔
      (∀ x, (octonionEquiv a (x, 0)).2 = 0) ∧
      (∀ y, (octonionEquiv a (0, y)).1 = 0) := by
  let : LinearOrder (Option (Fin 3)) := octonionIndexOrder
  have h := even_iff_preserves_blocks (octonionNorm R)
    ((coordinateBasis R).reindex
      (toLex : (Option (Fin 3) ⊕ Option (Fin 3)) ≃
        Lex (Option (Fin 3) ⊕ Option (Fin 3))))
    (octonionBlock R) (octonionBlock_isCompl R) octonionEquiv.toAlgHom
    octonionEquiv.injective (fun k c x hx => by
      change octonionEquiv (ι _ c) x ∈ _
      rw [octonionEquiv_ι]
      exact octonionOperator_grade k c x hx) a
  rw [h]
  constructor
  · intro hh
    exact ⟨fun x => (octonionBlock_zero _).mp (hh 0 (x, 0) ((octonionBlock_zero _).mpr rfl)),
      fun y => (octonionBlock_one _).mp (hh 1 (0, y) ((octonionBlock_one _).mpr rfl))⟩
  · rintro ⟨h₀, h₁⟩ k ⟨x, y⟩ hx
    rcases parity_cases k with rfl | rfl
    · have hy : y = 0 := (octonionBlock_zero (x, y)).mp hx
      subst y
      exact (octonionBlock_zero _).mpr (h₀ x)
    · have hzero : x = 0 := (octonionBlock_one (x, y)).mp hx
      subst x
      exact (octonionBlock_one _).mpr (h₁ y)

theorem octonion_model : CliffordSpecification.octonionModelType.{u} := by
  intro R _
  exact ⟨octonionEquiv, octonionEquiv_ι, octonionEquiv_even, octonionEquiv_adjoint⟩

end Octonions

end LinearAlgebraicGroups.Albert.CliffordModel
