import MathGenome.Internal.Specs.D07.Ch16.OperatorBridgeRationalCanonicalDecomposition
import MathGenome.Internal.D07.Ch16.OperatorBridgePolynomialModuleCorrespondence
import MathGenome.Internal.D07.Ch11.LinearAlgebraBridge
import MathGenome.LinearAlgebra.CanonicalForms

/-!
The rational form is reused from the verified D05 library, whose conclusion
contains the actual evaluated polynomial module and actual principal quotients.
Its invariant-factor formulas apply to every such quotient representation.
The local proofs identify invertible intertwiners, translate the nilpotent
quotient to (X-λ)^e, and assemble the primary quotient representation from a
Jordan basis. No splitting is used before the final split-case theorem.
-/
noncomputable section
universe u v w
namespace D07.Ch16.OperatorBridgeRationalCanonicalDecomposition
open Polynomial Module
open scoped BigOperators
open Specs.D07.Ch16.OperatorBridgeRationalCanonicalDecomposition

theorem evaluationAction : EvaluationAction.{u,v} := by
  intro F _ V _ _ T p x
  rfl

theorem finiteTorsion : FiniteTorsion.{u,v} := by
  intro F _ V _ _ _ T
  refine ⟨inferInstance, ?_⟩
  intro x
  obtain ⟨_, p, hp, _, he⟩ := D07.Ch11.LinearAlgebraBridge.finiteAnnihilator F V T
  refine ⟨⟨p, mem_nonZeroDivisors_of_ne_zero hp⟩, ?_⟩
  change (aeval T p) ((Module.AEval'.of T).symm x) = 0
  rw [he, LinearMap.zero_apply]

theorem rationalDecomposition : RationalDecomposition.{u,v} := by
  intro F _ V _ _ _ T
  obtain ⟨s, f, hm, hp, hc, he, _⟩ := D05.M10.Rational.rational_form T
  exact ⟨s, f, ⟨hm, hp, hc⟩, he⟩

theorem infiniteAlgebraicExample : InfiniteAlgebraicExample.{u} := by
  intro F _
  exact ⟨Polynomial.not_finite, aeval_X _⟩


theorem companionQuotient : CompanionQuotient.{u} := by
  intro F _ f hf hp
  refine ⟨D05.M10.Companion.quotientBasis F f hf,
    D05.M10.Companion.residue_basis f hf hp,
    D05.M10.Companion.matrix_representation f hf hp, ?_, ?_⟩
  · intro p
    let := hf.finite_adjoinRoot
    have hm : minpoly F (Algebra.lmul F (AdjoinRoot f) (AdjoinRoot.root f)) = f :=
      D05.M10.Companion.minimal_polynomial f hf hp
    have h : aeval (Algebra.lmul F (AdjoinRoot f) (AdjoinRoot.root f)) p = 0 ↔
        minpoly F (Algebra.lmul F (AdjoinRoot f) (AdjoinRoot.root f)) ∣ p :=
      minpoly.dvd_iff.symm
    simpa only [hm] using h
  · exact ⟨D05.M10.Companion.characteristic_polynomial f hf hp,
      D05.M10.Companion.minimal_polynomial f hf hp⟩

theorem blockFormulas : BlockFormulas.{u,v} := by
  intro F _ V _ _ _ T s f hf ⟨e⟩
  obtain ⟨b, hb, hd⟩ := D05.M10.Rational.companion_basis_of_equiv T f hf.1 hf.2.1 e
  have hr : Specs.D05.M10.InvariantFactors.RationalFactors T f :=
    ⟨hf.1, hf.2.1, hf.2.2, b, hb⟩
  refine ⟨⟨b, hb⟩, hd, D05.M10.InvariantFactors.charpoly_product T f hr,
    D05.M10.InvariantFactors.nonempty_factors T f hr, ?_⟩
  intro h
  cases s with
  | zero => omega
  | succ n =>
    simpa only [Nat.add_sub_cancel, Fin.last] using
      D05.M10.InvariantFactors.minpoly_largest T f hr

theorem factorUniqueness : FactorUniqueness.{u,v} := by
  intro F _ V _ _ _ T s t f g hf hg he hf'
  exact (D05.M10.InvariantFactors.module_identification T f hf.1 hf.2.1 hf.2.2 he).symm.trans
    (D05.M10.InvariantFactors.module_identification T g hg.1 hg.2.1 hg.2.2 hf')

/-- On the canonical synonyms the general intertwining criterion identifies
exactly the same underlying maps, with no finite-dimensional hypothesis. -/
def polynomialIntertwiner {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V]
    {W : Type w} [AddCommGroup W] [Module F W]
    (T : Module.End F V) (S : Module.End F W)
    (e : V ≃ₗ[F] W) (he : ∀ x, e (T x) = S (e x)) :
    Module.AEval' T ≃ₗ[F[X]] Module.AEval' S :=
  LinearEquiv.ofAEval T (e.trans (Module.AEval'.of S)) (by
    intro x
    change Module.AEval'.of S (e (T x)) = (X : F[X]) • Module.AEval'.of S (e x)
    rw [he, Module.AEval'.X_smul_of])

/-- Restriction to constants, and the X-equation, recover the invertible
intertwiner on the original vector spaces. -/
def fieldIntertwiner {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V]
    {W : Type w} [AddCommGroup W] [Module F W]
    (T : Module.End F V) (S : Module.End F W)
    (q : Module.AEval' T ≃ₗ[F[X]] Module.AEval' S) : V ≃ₗ[F] W :=
  (Module.AEval'.of T).trans ((q.restrictScalars F).trans (Module.AEval'.of S).symm)

lemma fieldIntertwiner_commutes {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V]
    {W : Type w} [AddCommGroup W] [Module F W]
    (T : Module.End F V) (S : Module.End F W)
    (q : Module.AEval' T ≃ₗ[F[X]] Module.AEval' S) (x : V) :
    fieldIntertwiner T S q (T x) = S (fieldIntertwiner T S q x) := by
  change (Module.AEval'.of S).symm (q (Module.AEval'.of T (T x))) =
    S ((Module.AEval'.of S).symm (q (Module.AEval'.of T x)))
  rw [← Module.AEval'.X_smul_of, map_smul, Module.AEval'.of_symm_X_smul]

theorem similarityClassification : SimilarityClassification.{u,v,w} := by
  intro F _ V _ _ _ W _ _ _ T S s t f g hf hg ⟨ef⟩ ⟨eg⟩
  constructor
  · rintro ⟨e, he⟩
    exact factorUniqueness F V T s t f g hf hg ⟨ef⟩
      ⟨(polynomialIntertwiner T S e he).trans eg⟩
  · intro h
    have hst : s = t := by
      simpa only [List.length_ofFn] using congrArg List.length h
    subst t
    have hfg : f = g := List.ofFn_inj.mp h
    subst g
    let q := ef.trans eg.symm
    exact ⟨fieldIntertwiner T S q, fieldIntertwiner_commutes T S q⟩

theorem zeroSpace : ZeroSpace.{u,v} := by
  intro F _ V _ _ _ T h
  have hz := D05.M10.InvariantFactors.zero_case T h
  obtain ⟨s, f, hf, he⟩ := rationalDecomposition F V T
  have hs : s = 0 := ((blockFormulas F V T s f hf he).2.2.2.1).mpr h
  subst s
  exact ⟨hz.2.1, hz.2.2, f, hf, he⟩

/-- Translate the nilpotent quotient without changing the coefficient field. -/
def shiftQuotient {F : Type u} [Field F] (lam : F) (e : ℕ) :
    AdjoinRoot (X ^ e : F[X]) ≃ₐ[F] AdjoinRoot ((X - C lam) ^ e) :=
  Ideal.quotientEquivAlg (Ideal.span {(X ^ e : F[X])})
    (Ideal.span {((X - C lam) ^ e : F[X])}) (algEquivAevalXAddC (-lam)) (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1
      simp [algEquivAevalXAddC_apply, sub_eq_add_neg])

lemma shiftQuotient_mk {F : Type u} [Field F] (lam : F) (e : ℕ) (p : F[X]) :
    shiftQuotient lam e (AdjoinRoot.mk _ p) =
      AdjoinRoot.mk _ (aeval (X - C lam) p) := by
  change AdjoinRoot.mk _ ((algEquivAevalXAddC (-lam)) p) = _
  simp [algEquivAevalXAddC_apply, sub_eq_add_neg]

theorem jordanQuotient : JordanQuotient.{u} := by
  intro F _ lam e he
  obtain ⟨b, hb, hz, hs⟩ := D05.M10.JordanChains.quotient_chain_basis (K := F) e he
  let E := shiftQuotient lam e
  refine ⟨b.map E.toLinearEquiv, ?_, ?_, ?_⟩
  · intro j
    rw [Basis.map_apply, hb]
    exact (shiftQuotient_mk lam e _).trans (by simp)
  · intro j hj
    have hroot : E (AdjoinRoot.root (X ^ e : F[X])) =
        AdjoinRoot.root ((X - C lam) ^ e) - algebraMap F _ lam := by
      simpa only [aeval_X, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq] using
        shiftQuotient_mk lam e X
    change AdjoinRoot.root _ * E (b j) = lam • E (b j)
    have hmul := congrArg E (hz j hj)
    rw [map_mul, hroot, map_zero, sub_mul] at hmul
    rw [Algebra.smul_def]
    exact sub_eq_zero.mp hmul
  · intro j k hjk
    have hroot : E (AdjoinRoot.root (X ^ e : F[X])) =
        AdjoinRoot.root ((X - C lam) ^ e) - algebraMap F _ lam := by
      simpa only [aeval_X, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq] using
        shiftQuotient_mk lam e X
    change AdjoinRoot.root _ * E (b j) = lam • E (b j) + E (b k)
    have hmul := congrArg E (hs j k hjk)
    rw [map_mul, hroot, sub_mul] at hmul
    rw [Algebra.smul_def]
    exact (sub_eq_iff_eq_add.mp hmul).trans (add_comm _ _)

/-- Identity on residue classes, with the two canonical field actions. -/
def quotientResidueEquiv {F : Type u} [Field F] (f : F[X]) :
    AdjoinRoot f ≃ₗ[F] Cyclic f where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The X-action on a finite product of the actual quotient rings. -/
def quotientProductX {F : Type u} [Field F] {r : ℕ} (f : Fin r → F[X]) :
    Module.End F (∀ i, Cyclic (f i)) where
  toFun z i := (X : F[X]) • z i
  map_add' z w := by ext i; exact smul_add _ _ _
  map_smul' a z := by ext i; exact smul_comm (X : F[X]) a (z i)

/-- Joining the reversed quotient bases gives the componentwise Jordan action. -/
lemma primaryProductBasis {F : Type u} [Field F] {r : ℕ}
    (e : Fin r → ℕ) (lam : Fin r → F) (he : ∀ i, 0 < e i) :
    ∃ B : Basis (Σ i, Fin (e i)) F (∀ i, Cyclic ((X - C (lam i)) ^ e i)),
      LinearMap.toMatrix B B (quotientProductX (fun i => (X - C (lam i)) ^ e i)) =
        Specs.D05.M10.JordanExistence.jordanMatrix e lam := by
  classical
  choose b hb hz hs using (fun i => jordanQuotient F (lam i) (e i) (he i))
  let bq (i : Fin r) := (b i).map (quotientResidueEquiv ((X - C (lam i)) ^ e i))
  let B := Pi.basis bq
  have hB (i : Fin r) (j : Fin (e i)) : B ⟨i,j⟩ = Pi.single (M := fun i => Cyclic ((X - C (lam i)) ^ e i)) i (bq i j) :=
    Pi.basis_apply bq ⟨i,j⟩
  let P := quotientProductX (fun i => (X - C (lam i)) ^ e i)
  refine ⟨B, D05.M10.JordanExistence.matrix_of_chain_basis e lam P B ?_ ?_⟩
  · intro i j hj
    rw [hB]
    ext k
    by_cases hk : k = i
    · subst k
      change (X : F[X]) • Pi.single (M := fun i => Cyclic ((X - C (lam i)) ^ e i)) i (bq i j) i = lam i • Pi.single (M := fun i => Cyclic ((X - C (lam i)) ^ e i)) i (bq i j) i
      rw [Pi.single_eq_same]
      change quotientResidueEquiv _ (AdjoinRoot.root _ * b i j) =
        lam i • quotientResidueEquiv _ (b i j)
      rw [hz i j hj, map_smul]
    · simp [hk, P,
        quotientProductX]
  · intro i j k hjk
    rw [hB, hB]
    ext l
    by_cases hl : l = i
    · subst l
      change (X : F[X]) • Pi.single (M := fun i => Cyclic ((X - C (lam i)) ^ e i)) i (bq i j) i =
        lam i • Pi.single (M := fun i => Cyclic ((X - C (lam i)) ^ e i)) i (bq i j) i + Pi.single (M := fun i => Cyclic ((X - C (lam i)) ^ e i)) i (bq i k) i
      rw [Pi.single_eq_same, Pi.single_eq_same]
      change quotientResidueEquiv _ (AdjoinRoot.root _ * b i j) =
        lam i • quotientResidueEquiv _ (b i j) + quotientResidueEquiv _ (b i k)
      rw [hs i j k hjk, map_add, map_smul]
    · simp [hl, P,
        quotientProductX]

theorem splitPrimaryJordan : SplitPrimaryJordan.{u,v} := by
  intro F _ V _ _ _ T s f hf hfac hsplit
  classical
  have hchi : T.charpoly.Splits := by
    obtain ⟨eqv⟩ := hfac
    obtain ⟨b, hb, _⟩ := D05.M10.Rational.companion_basis_of_equiv T f hf.1 hf.2.1 eqv
    rw [D05.M10.InvariantFactors.charpoly_product T f ⟨hf.1, hf.2.1, hf.2.2, b, hb⟩]
    exact Polynomial.Splits.prod (fun i _ => hsplit i)
  obtain ⟨r, e, lam, he, b, hb, hd⟩ := D05.M10.JordanExistence.jordan_form T hchi
  obtain ⟨B, hB⟩ := primaryProductBasis e lam he
  let E := b.equiv B (Equiv.refl _)
  have hP : E.toLinearMap.comp T =
      (quotientProductX (fun i => (X - C (lam i)) ^ e i)).comp E.toLinearMap := by
    apply (LinearMap.toMatrix b B).injective
    rw [LinearMap.toMatrix_comp b b B, LinearMap.toMatrix_comp b B B,
      LinearMap.toMatrix_basis_equiv, Matrix.one_mul, Matrix.mul_one, hb, hB]
  let q : Module.AEval' T ≃ₗ[F[X]] (∀ i, Cyclic ((X - C (lam i)) ^ e i)) :=
    LinearEquiv.ofAEval T E (by
      intro x
      exact LinearMap.congr_fun hP x)
  exact ⟨r, e, lam, he, ⟨q⟩, b, hb, hd⟩


end D07.Ch16.OperatorBridgeRationalCanonicalDecomposition
