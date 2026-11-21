import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.JacobianPresentation
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Hypersurfaces
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic.FinCases

namespace AdvCommAlg.Differentials
universe u
noncomputable section
open Specs.AdvCommAlg.Differentials
set_option backward.isDefEq.respectTransparency false

/-- A matrix with one column has as image the span of that column. -/
lemma range_one_column {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) :
    LinearMap.range (Matrix.mulVecLin (fun i (_ : Fin 1) => v i)) =
      Submodule.span R {v} := by
  ext x
  rw [LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a 0, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  · rintro ⟨a, rfl⟩
    refine ⟨fun _ => a, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]

theorem hypersurface_presentation : hypersurfacePresentation.{u} := by
  intro A _ n f
  let P : Algebra.Presentation A (Hypersurface A n f) (Fin n) (Fin 1) :=
    Algebra.Presentation.naive (v := fun _ : Fin 1 => f)
  have hm : presentationJacobian P = fun i (_ : Fin 1) => hypersurfaceGradient A n f i := by
    ext i j
    change MvPolynomial.aeval P.val (MvPolynomial.pderiv i f) = _
    have he : MvPolynomial.aeval P.val = Ideal.Quotient.mkₐ A (Ideal.span (Set.range (fun _ : Fin 1 => f))) := by
      ext i
      rw [MvPolynomial.aeval_X]
      rfl
    rw [he]
    rfl
  obtain ⟨e, he, _⟩ := jacobian_cokernel A (Hypersurface A n f) n 1 P
  have hr : LinearMap.range (jacobianRelationMap P) =
      Submodule.span (Hypersurface A n f) {hypersurfaceGradient A n f} := by
    rw [jacobianRelationMap, hm, range_one_column]
  refine ⟨(Submodule.quotEquivOfEq _ _ hr.symm).trans e, ?_⟩
  intro x
  change e ((Submodule.quotEquivOfEq _ _ hr.symm) (Submodule.Quotient.mk x)) = _
  rw [Submodule.quotEquivOfEq_mk]
  exact he x

lemma hypersurfaceDifferential_apply (A : Type u) [CommRing A] (n : ℕ)
    (f : MvPolynomial (Fin n) A) (x : Fin n → Hypersurface A n f) :
    hypersurfaceDifferential A n f x = ∑ i, x i •
      KaehlerDifferential.D A (Hypersurface A n f) (hypersurfaceVariable A n f i) := by
  classical
  conv_lhs => rw [← (Pi.basisFun (Hypersurface A n f) (Fin n)).sum_repr x]
  simp [hypersurfaceDifferential]

theorem hypersurface_relation : hypersurfaceRelation.{u} := by
  intro A _ n f
  obtain ⟨e, he⟩ := hypersurface_presentation A n f
  rw [← hypersurfaceDifferential_apply, ← he]
  have hz : (Submodule.span (Hypersurface A n f) {hypersurfaceGradient A n f}).mkQ
      (hypersurfaceGradient A n f) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span (Set.mem_singleton _))
  rw [hz, map_zero]


lemma hypersurfaceDifferential_single (A : Type u) [CommRing A] (n : ℕ)
    (f : MvPolynomial (Fin n) A) (i : Fin n) :
    hypersurfaceDifferential A n f (Pi.single i 1) =
      KaehlerDifferential.D A (Hypersurface A n f) (hypersurfaceVariable A n f i) := by
  change ((Pi.basisFun (Hypersurface A n f) (Fin n)).constr (Hypersurface A n f)
    (fun i => KaehlerDifferential.D A (Hypersurface A n f)
      (hypersurfaceVariable A n f i))) (Pi.single i 1) = _
  rw [← Pi.basisFun_apply, Module.Basis.constr_basis]

theorem node_presentation : nodePresentation.{u} := by
  intro A _
  have hg : hypersurfaceGradient A 2 (MvPolynomial.X 0 * MvPolynomial.X 1) =
      ![nodeY A, nodeX A] := by
    ext i
    fin_cases i <;> simp [hypersurfaceGradient, nodeX, nodeY, hypersurfaceVariable]
  have H := hypersurface_presentation A 2 (MvPolynomial.X 0 * MvPolynomial.X 1)
  rw [hg] at H
  obtain ⟨e, he⟩ := H
  have hrel := hypersurface_relation A 2 (MvPolynomial.X 0 * MvPolynomial.X 1)
  rw [hg] at hrel
  refine ⟨e, ?_, ?_, ?_⟩
  · exact (he _).trans (hypersurfaceDifferential_single _ _ _ _)
  · exact (he _).trans (hypersurfaceDifferential_single _ _ _ _)
  · simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hrel

/-- Polynomial and singleton multivariate coordinates agree on ordinary differentiation. -/
lemma singleton_pderiv (A : Type u) [CommRing A] (f : Polynomial A) :
    MvPolynomial.pderiv (0 : Fin 1) ((MvPolynomial.uniqueAlgEquiv A (Fin 1)).symm f) =
      (MvPolynomial.uniqueAlgEquiv A (Fin 1)).symm f.derivative := by
  have he : (MvPolynomial.uniqueAlgEquiv A (Fin 1)).symm.toAlgHom =
      Polynomial.aeval (MvPolynomial.X (0 : Fin 1)) := by
    ext
    simp [MvPolynomial.uniqueAlgEquiv]
  change MvPolynomial.pderiv (0 : Fin 1)
    ((MvPolynomial.uniqueAlgEquiv A (Fin 1)).symm.toAlgHom f) =
      (MvPolynomial.uniqueAlgEquiv A (Fin 1)).symm.toAlgHom f.derivative
  rw [he, Derivation.map_aeval]
  simp

/-- An actual one-generator, one-relation presentation of A[X]/(f). -/
def univariatePresentation (A : Type u) [CommRing A] (f : Polynomial A) :
    Algebra.Presentation A (AdjoinRoot f) (Fin 1) (Fin 1) where
  toGenerators := Algebra.Generators.ofAlgHom
    ((AdjoinRoot.mkₐ f).comp (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toAlgHom)
    (AdjoinRoot.mk_surjective.comp (MvPolynomial.uniqueAlgEquiv A (Fin 1)).surjective)
  relation _ := (MvPolynomial.uniqueAlgEquiv A (Fin 1)).symm f
  span_range_relation_eq_ker := by
    ext p
    rw [Set.range_const, Ideal.mem_span_singleton, Algebra.Generators.ker_ofAlgHom]
    rw [RingHom.mem_ker]
    change (MvPolynomial.uniqueAlgEquiv A (Fin 1)).symm f ∣ p ↔
      AdjoinRoot.mk f ((MvPolynomial.uniqueAlgEquiv A (Fin 1)) p) = 0
    rw [AdjoinRoot.mk_eq_zero, ← map_dvd_iff (MvPolynomial.uniqueAlgEquiv A (Fin 1)),
      AlgEquiv.apply_symm_apply]

lemma univariatePresentation_val (A : Type u) [CommRing A] (f : Polynomial A) (i : Fin 1) :
    (univariatePresentation A f).val i = AdjoinRoot.root f := by
  simp [univariatePresentation, Algebra.Generators.ofAlgHom,
    MvPolynomial.uniqueAlgEquiv, AdjoinRoot.mk_X]

lemma univariatePresentation_jacobian (A : Type u) [CommRing A] (f : Polynomial A) :
    presentationJacobian (univariatePresentation A f) =
      fun (_ : Fin 1) (_ : Fin 1) => AdjoinRoot.mk f f.derivative := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change MvPolynomial.aeval (univariatePresentation A f).val
    (MvPolynomial.pderiv 0 ((MvPolynomial.uniqueAlgEquiv A (Fin 1)).symm f)) = _
  rw [singleton_pderiv]
  have he : MvPolynomial.aeval (univariatePresentation A f).val =
      (AdjoinRoot.mkₐ f).comp (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toAlgHom := by
    ext i
    simp [univariatePresentation_val, MvPolynomial.uniqueAlgEquiv, AdjoinRoot.mk_X]
  rw [he]
  change AdjoinRoot.mk f ((MvPolynomial.uniqueAlgEquiv A (Fin 1))
    ((MvPolynomial.uniqueAlgEquiv A (Fin 1)).symm f.derivative)) = _
  rw [AlgEquiv.apply_symm_apply]

theorem univariate_hypersurface : univariateHypersurface.{u} := by
  intro A _ f
  let B := AdjoinRoot f
  let P := univariatePresentation A f
  let I : Submodule B B := Ideal.span {AdjoinRoot.mk f f.derivative}
  let c : (Fin 1 → B) ≃ₗ[B] B := LinearEquiv.funUnique (Fin 1) B B
  have hr : (LinearMap.range (jacobianRelationMap P)).map c.toLinearMap = I := by
    rw [jacobianRelationMap, univariatePresentation_jacobian, range_one_column,
      Submodule.map_span, Set.image_singleton]
    change Submodule.span B {AdjoinRoot.mk f f.derivative} = _
    exact Ideal.submodule_span_eq
  let ec := Submodule.Quotient.equiv _ I c hr
  obtain ⟨e, he, _⟩ := jacobian_cokernel A B 1 1 P
  refine ⟨ec.symm.trans e, ?_⟩
  intro b
  change e ((LinearMap.range (jacobianRelationMap P)).mkQ (fun _ => b)) = _
  rw [he]
  have hx : (fun _ : Fin 1 => b) = b • (Pi.single 0 1 : Fin 1 → B) := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  rw [hx, map_smul, jacobian_variables, univariatePresentation_val]


lemma dual_derivative (A : Type u) [CommRing A] :
    AdjoinRoot.mk (Polynomial.X ^ 2 : Polynomial A)
      (Polynomial.derivative (Polynomial.X ^ 2)) = (2 : DualQuotient A) * epsilon A := by
  rw [Polynomial.derivative_X_pow]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, map_mul, AdjoinRoot.mk_C]
  rfl

theorem dual_number_presentation : dualNumberPresentation.{u} := by
  intro A _
  obtain ⟨e, he⟩ := univariate_hypersurface A (Polynomial.X ^ 2)
  let I : Submodule (DualQuotient A) (DualQuotient A) :=
    Ideal.span {(AdjoinRoot.mk (Polynomial.X ^ 2 : Polynomial A) (Polynomial.derivative (Polynomial.X ^ 2)))}
  let J : Submodule (DualQuotient A) (DualQuotient A) := Ideal.span {(2 : DualQuotient A) * epsilon A}
  have hIJ : I = J := by dsimp only [I, J]; rw [dual_derivative A]
  let e' := (Submodule.quotEquivOfEq J I hIJ.symm).trans e
  have he' (b : DualQuotient A) : e' (Ideal.Quotient.mk _ b) =
      b • KaehlerDifferential.D A (DualQuotient A) (epsilon A) := by
    change e ((Submodule.quotEquivOfEq J I hIJ.symm) (Submodule.Quotient.mk b)) = _
    rw [Submodule.quotEquivOfEq_mk]
    exact he b
  refine ⟨e', he', ?_⟩
  rw [← he']
  have hz : Ideal.Quotient.mk (Ideal.span {(2 : DualQuotient A) * epsilon A})
      ((2 : DualQuotient A) * epsilon A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hz, map_zero]

theorem dual_number_nilpotent : dualNumberNilpotent.{u} := by
  intro K _
  constructor
  · have h := AdjoinRoot.mk_ne_zero_of_natDegree_lt
      (Polynomial.monic_X.pow 2 : (Polynomial.X ^ 2 : Polynomial K).Monic)
      (Polynomial.X_ne_zero : (Polynomial.X : Polynomial K) ≠ 0) (by simp)
    exact h
  · change AdjoinRoot.mk (Polynomial.X ^ 2 : Polynomial K) Polynomial.X ^ 2 = 0
    rw [← map_pow, AdjoinRoot.mk_self]

theorem dual_number_char_two : dualNumberCharTwo.{u} := by
  intro K _ _
  let B := DualQuotient K
  let I : Submodule B B := Ideal.span {(2 : B) * epsilon K}
  have htwo : (2 : B) = 0 := by
    calc
      (2 : B) = algebraMap K B (2 : K) := (map_ofNat (algebraMap K B) 2).symm
      _ = 0 := by rw [show (2 : K) = 0 from CharP.cast_eq_zero K 2, map_zero]
  have hI : I = ⊥ := by simp [I, htwo]
  obtain ⟨e, he, _⟩ := dual_number_presentation K
  let c : B ≃ₗ[B] KaehlerDifferential K B := (I.quotEquivOfEqBot hI).symm.trans e
  refine ⟨(Module.Basis.singleton Unit B).map c, ?_⟩
  change c ((Module.Basis.singleton Unit B) ()) = _
  rw [Module.Basis.singleton_apply]
  change e (Ideal.Quotient.mk _ 1) = _
  simpa using he 1


/-- Evaluation at ε = 0 in the literal dual-number quotient. -/
def dualAugmentation (A : Type u) [CommRing A] : DualQuotient A →ₐ[A] A :=
  AdjoinRoot.liftAlgHom (Polynomial.X ^ 2) (AlgHom.id A A) 0 (by simp)

@[simp] lemma dualAugmentation_epsilon (A : Type u) [CommRing A] :
    dualAugmentation A (epsilon A) = 0 := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Killing ε recovers A, as an A-algebra, over every commutative ring. -/
def dualQuotientEpsilonEquiv (A : Type u) [CommRing A] :
    (DualQuotient A ⧸ Ideal.span {epsilon A}) ≃ₐ[A] A := by
  let B := DualQuotient A
  let I : Ideal B := Ideal.span {epsilon A}
  have hI : I ≤ RingHom.ker (dualAugmentation A) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change dualAugmentation A (epsilon A) = 0
    exact dualAugmentation_epsilon A
  let f : (B ⧸ I) →ₐ[A] A := Ideal.Quotient.liftₐ I (dualAugmentation A) (fun x hx => hI hx)
  let g : A →ₐ[A] (B ⧸ I) := Algebra.ofId A (B ⧸ I)
  have hfg : f.comp g = AlgHom.id A A := by ext
  have hgf : g.comp f = AlgHom.id A (B ⧸ I) := by
    apply Ideal.Quotient.algHom_ext A
    apply AdjoinRoot.algHom_ext
    change g (dualAugmentation A (epsilon A)) = Ideal.Quotient.mk I (epsilon A)
    rw [dualAugmentation_epsilon, map_zero]
    symm
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  exact AlgEquiv.ofAlgHom f g hfg hgf

theorem dual_number_char_ne_two : dualNumberCharNeTwo.{u} := by
  intro K _ htwo
  let B := DualQuotient K
  let I : Submodule B B := Ideal.span {(2 : B) * epsilon K}
  let J : Submodule B B := Ideal.span {epsilon K}
  have hunit : IsUnit (2 : B) := by
    have h := (isUnit_iff_ne_zero.mpr htwo).map (algebraMap K B)
    simpa only [map_ofNat] using h
  have hIJ : I = J := Ideal.span_singleton_mul_left_unit hunit (epsilon K)
  obtain ⟨e, he, hrel⟩ := dual_number_presentation K
  let ec : (B ⧸ J) ≃ₗ[B] KaehlerDifferential K B :=
    (Submodule.quotEquivOfEq J I hIJ.symm).trans e
  let a := dualQuotientEpsilonEquiv K
  let c : K ≃ₗ[K] KaehlerDifferential K B :=
    a.symm.toLinearEquiv.trans (ec.restrictScalars K)
  refine ⟨c, ?_, ?_⟩
  · change ec (a.symm 1) = _
    rw [map_one]
    change e ((Submodule.quotEquivOfEq J I hIJ.symm) (Submodule.Quotient.mk 1)) = _
    rw [Submodule.quotEquivOfEq_mk]
    simpa using he 1
  · intro ω
    obtain ⟨b, hb⟩ := e.surjective ω
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← hb, he, smul_comm]
    have hz : epsilon K • KaehlerDifferential.D K B (epsilon K) = 0 := by
      apply hunit.smul_eq_zero.mp
      simpa only [smul_smul] using hrel
    rw [hz, smul_zero]

end
end AdvCommAlg.Differentials
