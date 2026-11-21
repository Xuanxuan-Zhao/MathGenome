import MathGenome.Internal.Specs.D07.Ch12.Inseparability
import MathGenome.Internal.D07.Ch12.SimpleDegree
import MathGenome.Internal.D07.Ch12.SimpleEmbeddings
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Tactic.Ring

/-! K07.12.inseparability. The rational function degree obstructs a p-th
root of t in F_p(t); the prime-degree binomial criterion gives irreducibility.
Frobenius gives the repeated-root factorization. The general decomposition
uses degree descent for existence and injectivity of expansion for uniqueness. -/

universe u v w

namespace D07.Ch12.Inseparability

open Polynomial
open Specs.D07.Ch12.Inseparability

lemma intDegree_pow {F : Type*} [Field F] (b : RatFunc F) (hb : b ≠ 0) (n : ℕ) :
    RatFunc.intDegree (b ^ n) = (n : ℤ) * RatFunc.intDegree b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ hb) hb, ih]
    push_cast
    ring

theorem example_irreducible : ExampleIrreducible := by
  intro p hp
  have hprime : p.Prime := Fact.out
  apply X_pow_sub_C_irreducible_of_prime hprime
  intro b heq
  have hb : b ≠ 0 := by
    intro hb
    apply RatFunc.X_ne_zero (K := ZMod p)
    simpa [hb, hprime.ne_zero] using heq.symm
  have hd := congrArg RatFunc.intDegree heq
  rw [intDegree_pow b hb, RatFunc.intDegree_X] at hd
  have hdiv : (p : ℤ) ∣ 1 := ⟨RatFunc.intDegree b, hd.symm⟩
  have : p ∣ 1 := Int.natCast_dvd_natCast.mp hdiv
  exact hprime.not_dvd_one this

lemma example_monic (p : ℕ) [Fact p.Prime] : (examplePolynomial p).Monic :=
  monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero

lemma example_natDegree (p : ℕ) [Fact p.Prime] : (examplePolynomial p).natDegree = p :=
  natDegree_X_pow_sub_C

lemma example_minpoly (p : ℕ) [Fact p.Prime] (L : Type v) [Field L]
    [Algebra (RatFunc (ZMod p)) L] (u : L)
    (hu : aeval u (examplePolynomial p) = 0) :
    minpoly (RatFunc (ZMod p)) u = examplePolynomial p :=
  (minpoly.eq_of_irreducible_of_monic (example_irreducible p) hu (example_monic p)).symm

lemma example_integral (p : ℕ) [Fact p.Prime] (L : Type v) [Field L]
    [Algebra (RatFunc (ZMod p)) L] (u : L)
    (hu : aeval u (examplePolynomial p) = 0) : IsIntegral (RatFunc (ZMod p)) u :=
  ⟨examplePolynomial p, example_monic p, hu⟩

theorem example_root_exists : ExampleRootExists.{v} := by
  intro p _ Ω _ _ _
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (RatFunc (ZMod p)) Ω RatFunc.X) (Fact.out : p.Prime).pos
  exact ⟨u, by simpa [examplePolynomial] using sub_eq_zero.mpr hu⟩

theorem example_degree : ExampleDegree.{v} := by
  intro p _ L _ _ u hu
  have h := SimpleDegree.simple_degree (RatFunc (ZMod p)) L u
    (example_integral p L u hu).isAlgebraic
  simpa [example_minpoly p L u hu, example_natDegree] using h

theorem example_factorization : ExampleFactorization.{v} := by
  intro p _ L _ _ u hu
  have : CharP L p := charP_of_injective_algebraMap' (RatFunc (ZMod p)) p
  have hpow : u ^ p = algebraMap (RatFunc (ZMod p)) L RatFunc.X := by
    simpa [examplePolynomial, sub_eq_zero] using hu
  simp only [examplePolynomial, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  rw [sub_pow_char, ← map_pow, hpow]

theorem example_unique_root : ExampleUniqueRoot.{v} := by
  intro p _ L _ _ u hu x
  constructor
  · intro hx
    have h := congrArg (Polynomial.eval x) (example_factorization p L u hu)
    have hz : (x - u) ^ p = 0 := by
      simpa [eval_map_algebraMap, hx] using h.symm
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  · rintro rfl
    exact hu

theorem example_unique_embedding : ExampleUniqueEmbedding.{v, w} := by
  intro p _ L Ω _ _ _ _ _ u hu
  obtain ⟨x, hx⟩ := example_root_exists p Ω
  have hm := example_minpoly p L u hu
  obtain ⟨e, _⟩ := SimpleEmbeddings.embeddingsRoots (RatFunc (ZMod p)) L Ω u
    (example_integral p L u hu).isAlgebraic
  have hx' : aeval x (minpoly (RatFunc (ZMod p)) u) = 0 := hm.symm ▸ hx
  refine ⟨e.symm ⟨x, hx'⟩, trivial, ?_⟩
  intro f _
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact (example_unique_root p Ω x hx (e f).val).mp (hm ▸ (e f).property)

theorem example_normal_inseparable : ExampleNormalInseparable.{v} := by
  intro p _ L _ _ u hu
  let K := RatFunc (ZMod p)
  have hpow : u ^ p = algebraMap K L RatFunc.X := by
    simpa [examplePolynomial, sub_eq_zero] using hu
  have : IsPurelyInseparable K (IntermediateField.adjoin K {u}) :=
    (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem K L p).mpr
      ⟨1, RatFunc.X, by simpa using hpow.symm⟩
  have hns : ¬ IsSeparable K u := by
    change ¬ (minpoly K u).Separable
    rw [example_minpoly p L u hu,
      Polynomial.separable_iff_derivative_ne_zero (example_irreducible p)]
    simp [examplePolynomial, derivative_X_pow]
  refine ⟨inferInstance, hns, ?_⟩
  intro hs
  have := hs
  apply hns
  have hgen : IsSeparable K (IntermediateField.AdjoinSimple.gen K u) :=
    Algebra.IsSeparable.isSeparable K _
  change (minpoly K (IntermediateField.AdjoinSimple.gen K u)).Separable at hgen
  simpa only [IsSeparable, IntermediateField.minpoly_eq,
    IntermediateField.AdjoinSimple.coe_gen] using hgen

theorem unique_separable_decomposition : UniqueSeparableDecomposition.{u} := by
  intro K _ p _ hp f hf hi
  obtain ⟨r, g, hg, he⟩ := Polynomial.exists_separable_of_irreducible p hi hp.ne_zero
  have hgi : Irreducible g := Polynomial.of_irreducible_expand (pow_ne_zero r hp.ne_zero)
    (he.symm ▸ hi)
  have hgm : g.Monic := (Polynomial.monic_expand_iff (pow_pos hp.pos r)).mp (he.symm ▸ hf)
  refine ⟨(r, g), ⟨hgm, hgi, hg, he.symm⟩, ?_⟩
  rintro ⟨s, h⟩ ⟨_, _, hh, hhf⟩
  obtain ⟨hrs, hgh⟩ := Polynomial.unique_separable_of_irreducible p hi hp.pos
    s h hh hhf.symm r g hg he
  exact Prod.ext hrs hgh

end D07.Ch12.Inseparability
