import MathGenome.Internal.Specs.D07.Ch16.OperatorBridge
import MathGenome.Internal.D07.Ch16.OperatorBridgePolynomialModuleCorrespondence
import MathGenome.Internal.D07.Ch16.OperatorBridgeRationalCanonicalDecomposition

/-!
Final bridge for paper.tex:3330–3380. The accepted correspondence and
canonical decomposition prerequisites supply the module and matrix results.
Here their conclusions are assembled, the annihilator intersection is made
explicit, and the converse to the split-primary Jordan construction is proved.
-/
noncomputable section
universe u v w
namespace D07.Ch16.OperatorBridge
open Polynomial Module
open scoped BigOperators
open Specs.D07.Ch16.OperatorBridge
open Specs.D07.Ch16.OperatorBridgeRationalCanonicalDecomposition

namespace Correspondence
export D07.Ch16.OperatorBridgePolynomialModuleCorrespondence
  (operatorToModule moduleToOperator actionFormula equivalenceCharacterization)
end Correspondence
namespace Canonical
export D07.Ch16.OperatorBridgeRationalCanonicalDecomposition
  (evaluationAction finiteTorsion infiniteAlgebraicExample rationalDecomposition
   companionQuotient blockFormulas factorUniqueness similarityClassification
   zeroSpace jordanQuotient splitPrimaryJordan)
end Canonical

theorem polynomialCorrespondence : PolynomialCorrespondence.{u,v,w} :=
  ⟨Correspondence.operatorToModule, Correspondence.moduleToOperator,
    Correspondence.actionFormula, Correspondence.equivalenceCharacterization,
    Canonical.evaluationAction⟩

theorem finiteTorsion : Specs.D07.Ch16.OperatorBridge.FiniteTorsion.{u,v} :=
  Canonical.finiteTorsion

theorem basisSpans : BasisSpans.{u,v} := by
  intro F _ V _ _ T n b
  have hb : Submodule.span F (Set.range (fun i => Module.AEval'.of T (b i))) = ⊤ :=
    (b.map (Module.AEval'.of T)).span_eq
  exact Submodule.span_eq_top_of_span_eq_top F F[X] _ hb

theorem vectorPowersDependent : VectorPowersDependent.{u,v} := by
  intro F _ V _ _ _ T x
  constructor
  · intro hi
    have hc := hi.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hc
    omega
  · have hchi := D07.Ch11.LinearAlgebraBridge.charpolyDegree F V T
    refine ⟨T.charpoly, hchi.1.ne_zero, hchi.2.2.le, ?_⟩
    rw [D07.Ch11.LinearAlgebraBridge.cayleyHamilton F V T, LinearMap.zero_apply]

theorem infiniteAlgebraicExample : Specs.D07.Ch16.OperatorBridge.InfiniteAlgebraicExample.{u} :=
  Canonical.infiniteAlgebraicExample

/-- Annihilation in the evaluation module is exactly vanishing of the
endomorphism obtained by polynomial evaluation. No dimension assumption. -/
lemma evaluation_annihilator {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V] (T : Module.End F V) :
    Module.annihilator F[X] (Module.AEval' T) =
      Specs.D07.Ch11.LinearAlgebraBridge.annihilator F V T := by
  ext p
  rw [Module.mem_annihilator]
  change (∀ x : Module.AEval' T, (aeval T p) ((Module.AEval'.of T).symm x) = 0) ↔
    aeval T p = 0
  constructor
  · intro h
    ext x
    exact h (Module.AEval'.of T x)
  · intro h x
    rw [h, LinearMap.zero_apply]

theorem noFreePart : NoFreePart.{u,v} := by
  intro F _ V _ _ _ T g hg
  obtain ⟨_, p, hp, _, he⟩ := D07.Ch11.LinearAlgebraBridge.finiteAnnihilator F V T
  have ha : p ∈ Module.annihilator F[X] (Module.AEval' T) := by
    rw [evaluation_annihilator]
    exact he
  have hz : g p = 0 := by
    have h := Module.mem_annihilator.mp ha (g 1)
    simpa only [← map_smul, smul_eq_mul, mul_one] using h
  exact hp (hg (hz.trans g.map_zero.symm))

theorem cyclicAnnihilator : CyclicAnnihilator.{u} := by
  intro F _ f
  refine ⟨Ideal.annihilator_quotient, ?_⟩
  intro p
  change Ideal.Quotient.mk (Ideal.span {f}) p * 1 = 0 ↔ f ∣ p
  rw [mul_one, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Finite products model the finite external direct sum. -/
lemma product_annihilator {F : Type u} [Field F] {s : ℕ} (f : Fin s → F[X]) :
    Module.annihilator F[X] (∀ i, Cyclic (f i)) = ⨅ i, Ideal.span {f i} := by
  rw [Module.annihilator_pi]
  simp_rw [Ideal.annihilator_quotient]

theorem intersectionAnnihilator : IntersectionAnnihilator.{u,v} := by
  intro F _ V _ _ T s f ⟨E⟩
  refine ⟨evaluation_annihilator T, ?_⟩
  rw [← evaluation_annihilator T, E.annihilator_eq, product_annihilator]

theorem largestAnnihilator : LargestAnnihilator.{u,v} := by
  intro F _ V _ _ T s f hf hfac
  have hI := (intersectionAnnihilator F V T s f hfac).2
  constructor
  · intro hs
    subst s
    simpa using hI
  · intro hs
    rw [hI]
    apply le_antisymm
    · exact iInf_le (fun i : Fin s => Ideal.span {f i})
        ⟨s - 1, Nat.sub_lt hs (by decide)⟩
    · apply le_iInf
      intro i
      apply Ideal.span_singleton_le_span_singleton.mpr
      exact hf.2.2 i ⟨s - 1, Nat.sub_lt hs (by decide)⟩ (by
        change i.val ≤ s - 1
        omega)

theorem companionBlocks : CompanionBlocks.{u} := Canonical.companionQuotient

theorem rationalCanonicalForm : RationalCanonicalForm.{u,v} := by
  intro F _ V _ _ _ T
  obtain ⟨s, f, hf, hfac⟩ := Canonical.rationalDecomposition F V T
  exact ⟨s, f, hf, hfac, Canonical.blockFormulas F V T s f hf hfac⟩

theorem allBlockFormulas : AllBlockFormulas.{u,v} := Canonical.blockFormulas

theorem classification : Classification.{u,v,w} :=
  ⟨Canonical.factorUniqueness, Canonical.similarityClassification⟩

theorem zeroSpace : Specs.D07.Ch16.OperatorBridge.ZeroSpace.{u,v} := Canonical.zeroSpace

theorem jordanQuotient : Specs.D07.Ch16.OperatorBridge.JordanQuotient.{u} :=
  Canonical.jordanQuotient

/-- In any quotient representation, every factor divides every global
annihilator. The test on the residue generator 1 suffices. -/
lemma factor_dvd_annihilator {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V] (T : Module.End F V)
    {s : ℕ} (f : Fin s → F[X]) (hf : HasFactors T f) {p : F[X]}
    (hp : p ∈ Specs.D07.Ch11.LinearAlgebraBridge.annihilator F V T) (i : Fin s) :
    f i ∣ p := by
  rw [(intersectionAnnihilator F V T s f hf).2] at hp
  exact Ideal.mem_span_singleton.mp ((Ideal.mem_iInf.mp hp) i)

/-- A product of the primary annihilators kills their entire finite product. -/
lemma product_mem_annihilator {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V] (T : Module.End F V)
    {r : ℕ} (g : Fin r → F[X]) (hg : HasFactors T g) :
    (∏ j, g j) ∈ Specs.D07.Ch11.LinearAlgebraBridge.annihilator F V T := by
  rw [(intersectionAnnihilator F V T r g hg).2, Ideal.mem_iInf]
  intro j
  exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem g (Finset.mem_univ j))

theorem jordanCriterion : JordanCriterion.{u,v} := by
  intro F _ V _ _ _ T s f hf hfac
  classical
  constructor
  · exact Canonical.splitPrimaryJordan F V T s f hf hfac
  · rintro ⟨r, e, lam, _, hprimary, _⟩
    let g : Fin r → F[X] := fun j => (X - C (lam j)) ^ e j
    have hsplit : (∏ j, g j).Splits :=
      Polynomial.Splits.prod (fun j _ => (Polynomial.Splits.X_sub_C (lam j)).pow (e j))
    have hn : (∏ j, g j) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact pow_ne_zero _ (X_sub_C_ne_zero (lam j))
    have ha := product_mem_annihilator T g hprimary
    intro i
    exact hsplit.of_dvd hn (factor_dvd_annihilator T f hfac ha i)

end D07.Ch16.OperatorBridge
