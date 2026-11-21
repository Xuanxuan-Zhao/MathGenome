import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalBCH
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FormalExpLog
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module

noncomputable section
namespace LieAlgebrasAndRepresentations.FormalBCH
open CompletedPrimitives FormalExpLog
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v w

def formalBCH (k : Type u) (V : Type v) [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] : Completion k V → Completion k V → Completion k V :=
  bch k V

def universalFormalBCH (k : Type u) [Field k] [CharZero k] : Completion k (Two k) :=
  universalBCH k

section
variable (k : Type u) (V : Type v) [Field k] [CharZero k]
  [AddCommGroup V] [Module k V]

@[simp] theorem bch_positive (p q : Completion k V) : Positive k V (bch k V p q) :=
  logarithm_constant _ _

theorem exp_product_constant (p q : Completion k V) :
    PowerSeries.coeff 0
      (exponential (generators k V) p * exponential (generators k V) q).val = 1 := by
  change PowerSeries.coeff 0
    ((exponential (generators k V) p).val * (exponential (generators k V) q).val) = 1
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff, exponential_constant, one_mul]

@[simp] theorem exponential_bch (p q : Completion k V) :
    exponential (generators k V) (bch k V p q) =
      exponential (generators k V) p * exponential (generators k V) q :=
  (Jets.inverse_laws _).2 _ (exp_product_constant k V p q)

theorem bch_associative (p q r : Completion k V) :
    bch k V (bch k V p q) r = bch k V p (bch k V q r) := by
  unfold bch
  rw [(Jets.inverse_laws _).2 _ (exp_product_constant k V p q),
    (Jets.inverse_laws _).2 _ (exp_product_constant k V q r), mul_assoc]

theorem groupLike_mul (g h : Completion k V)
    (hg : IsGroupLike k V (completedCoproduct k V) (completedLeft k V) (completedRight k V) g)
    (hh : IsGroupLike k V (completedCoproduct k V) (completedLeft k V) (completedRight k V) h) :
    IsGroupLike k V (completedCoproduct k V) (completedLeft k V) (completedRight k V) (g*h) := by
  constructor
  · change PowerSeries.coeff 0 (g.val*h.val) = 1
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, hg.1, hh.1] using (one_mul (1 : A k V))
  · rw [map_mul, hg.2, hh.2, map_mul, map_mul]
    have hc := completedLeft_right_commute k V h g
    calc
      _ = completedLeft k V g *
          (completedRight k V g * completedLeft k V h) * completedRight k V h := by
        simp only [mul_assoc]
      _ = _ := by rw [← hc.eq]; simp only [mul_assoc]

theorem bch_primitive (p q : Completion k V)
    (hp : IsCompletedPrimitive k V p) (hq : IsCompletedPrimitive k V q) :
    IsCompletedPrimitive k V (bch k V p q) := by
  have hH := hopf_of_formal_laws k V (Jets.inverse_laws _) (Jets.inverse_laws _)
    (Jets.commutingExp_laws _)
  exact hH.2 _ (groupLike_mul k V _ _ (hH.1 p hp) (hH.1 q hq))

theorem bch_completedLie (p q : Completion k V)
    (hp : InCompletedLie k V p) (hq : InCompletedLie k V q) :
    Positive k V (bch k V p q) ∧ InCompletedLie k V (bch k V p q) := by
  have h := (completed_spec k V).2.1
  exact (h _).mp (bch_primitive k V p q
    ((h p).mpr ⟨completedLie_positive k V hp, hp⟩)
    ((h q).mpr ⟨completedLie_positive k V hq, hq⟩))

omit [CharZero k] in
@[simp] theorem letter_coeff (x : V) (n : ℕ) :
    PowerSeries.coeff n (letter k V x).val =
      if n = 1 then TensorAlgebra.ι k x else 0 := PowerSeries.coeff_monomial _ _ _

theorem letter_completedLie (x : V) : InCompletedLie k V (letter k V x) := by
  rw [completedLie_iff_coeff]
  intro n
  rw [letter_coeff]
  split_ifs
  · exact LieSubalgebra.subset_lieSpan (Set.mem_range_self x)
  · exact (tensorLie k V).zero_mem

end

theorem lie_spec : Specs.LieAlgebrasAndRepresentations.FormalBCH.lieExpected.{u} := by
  intro k _ _
  exact bch_completedLie k (Two k) _ _
    (letter_completedLie k (Two k) _) (letter_completedLie k (Two k) _)

theorem closure_spec : Specs.LieAlgebrasAndRepresentations.FormalBCH.closureExpected.{u,v} :=
  bch_completedLie

theorem associativity_spec :
    Specs.LieAlgebrasAndRepresentations.FormalBCH.associativityExpected.{u,v} := by
  intro k V _ _ _ _ p q r _ _ _
  exact bch_associative k V p q r

section Substitution
variable {k : Type u} {V : Type v} {W : Type w} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
theorem completion_val_sum {ι : Type*} (s : Finset ι) (g : ι → Completion k V) :
    (∑ i ∈ s, g i).val = ∑ i ∈ s, (g i).val :=
  map_sum (degreeSeries (generators k V)).val g s

variable (f : V →ₗ[k] Completion k W) (hf : ∀ x, Positive k W (f x))
include hf

/-- Evaluation at positive series does not lower tensor degree. -/
theorem evaluation_vanishes {m : ℕ} {a : A k V} (ha : a ∈ degree k V m) :
    ∀ n < m, PowerSeries.coeff n ((TensorAlgebra.lift k f) a).val = 0 := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => intro n hn; omega
  | add a b i ha hb ia ib =>
    intro n hn
    simp only [map_add, Subalgebra.coe_add, ia n hn, ib n hn, add_zero]
  | mem_mul a ha i b hb ih =>
    obtain ⟨x, rfl⟩ := ha
    intro n hn
    rw [map_mul, TensorAlgebra.lift_ι_apply, Subalgebra.coe_mul, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have hij' := Finset.mem_antidiagonal.mp hij
    by_cases h : ij.1 = 0
    · rw [h, hf x, zero_mul]
    · rw [ih ij.2 (by omega), mul_zero]

omit hf in
@[simp] theorem substitute_coeff (p : Completion k V) (n : ℕ) :
    PowerSeries.coeff n (substitute f p).val =
      ∑ m ∈ Finset.range (n+1),
        PowerSeries.coeff n ((TensorAlgebra.lift k f) (PowerSeries.coeff m p.val)).val :=
  by simp only [substitute, PowerSeries.coeff_mk]

theorem substitute_coeff_cutoff (p : Completion k V) (n N : ℕ) (hN : n < N) :
    PowerSeries.coeff n (substitute f p).val =
      ∑ m ∈ Finset.range N,
        PowerSeries.coeff n ((TensorAlgebra.lift k f) (PowerSeries.coeff m p.val)).val := by
  rw [substitute_coeff]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro m hm hm'
  apply evaluation_vanishes f hf (p.property m) n
  simp only [Finset.mem_range, not_lt] at hm'
  omega

/-- The ordinary tensor representing a finite jet of a completed tensor. -/
def tensorTruncation (N : ℕ) (p : Completion k V) : A k V :=
  ∑ m ∈ Finset.range N, PowerSeries.coeff m p.val

omit hf in
theorem tensorTruncation_coeff (N : ℕ) (p : Completion k V) (n : ℕ) (hn : n < N) :
    PowerSeries.coeff n (ordinaryInclusion k V (tensorTruncation N p)).val =
      PowerSeries.coeff n p.val := by
  classical
  simp only [tensorTruncation, map_sum, completion_val_sum]
  simp_rw [ordinaryInclusion_coeff_homogeneous k V (p.property _)]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b hb hbn; simp [Ne.symm hbn]
  · intro h; exact (h (Finset.mem_range.mpr hn)).elim

/-- The evaluation of an ordinary tensor depends only on the corresponding
finite source jet. The discarded homogeneous pieces evaluate above the cutoff. -/
theorem evaluation_respects_jet (N : ℕ) (a b : A k V)
    (hab : Jets.project (k := k) N (ordinaryInclusion k V a).val =
      Jets.project (k := k) N (ordinaryInclusion k V b).val) :
    Jets.project (k := k) N ((TensorAlgebra.lift k f) a).val =
      Jets.project (k := k) N ((TensorAlgebra.lift k f) b).val := by
  classical
  have hz : ∀ n < N, PowerSeries.coeff n
      (ordinaryInclusion k V (a-b)).val = 0 := by
    intro n hn
    simpa only [map_sub, Subalgebra.coe_sub, sub_eq_zero] using
      (Jets.project_eq_iff (k := k) N _ _).mp hab n hn
  suffices h : Jets.project (k := k) N ((TensorAlgebra.lift k f) (a-b)).val = 0 by
    simpa only [map_sub, Subalgebra.coe_sub, sub_eq_zero] using h
  apply (Jets.project_eq_iff (k := k) N _ _).mpr
  intro n hn
  rw [map_zero]
  conv_lhs => rw [← DirectSum.sum_support_decompose (degree k V) (a-b)]
  simp only [map_sum, completion_val_sum]
  apply Finset.sum_eq_zero
  intro m hm
  by_cases hmN : m < N
  · have hzero : (DirectSum.decompose (degree k V) (a-b) m : A k V) = 0 := by
      simpa only [ordinaryInclusion_coeff] using hz m hmN
    rw [hzero, map_zero, Subalgebra.coe_zero, map_zero]
  · exact evaluation_vanishes f hf
      (DirectSum.decompose (degree k V) (a-b) m).property n (by omega)

theorem project_substitute (N : ℕ) (p : Completion k V) :
    Jets.project (k := k) N (substitute f p).val =
      Jets.project (k := k) N ((TensorAlgebra.lift k f) (tensorTruncation N p)).val := by
  apply (Jets.project_eq_iff (k := k) N _ _).mpr
  intro n hn
  rw [substitute_coeff_cutoff f hf p n N hn]
  simp only [tensorTruncation, map_sum, completion_val_sum]

omit hf in
theorem project_truncation (N : ℕ) (p : Completion k V) :
    Jets.project (k := k) N (ordinaryInclusion k V (tensorTruncation N p)).val =
      Jets.project (k := k) N p.val :=
  (Jets.project_eq_iff (k := k) N _ _).mpr (tensorTruncation_coeff N p)

theorem substitute_jet_congr (N : ℕ) (p q : Completion k V)
    (h : Jets.project (k := k) N p.val = Jets.project (k := k) N q.val) :
    Jets.project (k := k) N (substitute f p).val =
      Jets.project (k := k) N (substitute f q).val := by
  rw [project_substitute f hf, project_substitute f hf]
  apply evaluation_respects_jet f hf
  rw [project_truncation, project_truncation, h]

/-- Unital algebra substitution in arbitrary positive-degree arguments. -/
def substitutionHom : Completion k V →ₐ[k] Completion k W where
  toFun := substitute f
  map_zero' := by
    apply Subtype.ext; apply PowerSeries.ext; intro n
    simp [substitute_coeff]
  map_one' := by
    apply Subtype.ext; apply PowerSeries.ext; intro n
    apply (Jets.project_eq_iff (k := k) (n+1) _ _).mp ?_ n (by omega)
    rw [project_substitute f hf]
    calc
      _ = Jets.project (k := k) (n+1) ((TensorAlgebra.lift k f) 1).val := by
        apply evaluation_respects_jet f hf
        rw [project_truncation, map_one]
      _ = _ := by simp
  map_add' p q := by
    apply Subtype.ext; apply PowerSeries.ext; intro n
    apply (Jets.project_eq_iff (k := k) (n+1) _ _).mp ?_ n (by omega)
    rw [project_substitute f hf]
    calc
      _ = Jets.project (k := k) (n+1)
          ((TensorAlgebra.lift k f) (tensorTruncation (n+1) p + tensorTruncation (n+1) q)).val := by
        apply evaluation_respects_jet f hf
        simp only [map_add, Subalgebra.coe_add, project_truncation]
      _ = _ := by
        simp only [map_add, Subalgebra.coe_add, ← project_substitute f hf]
  map_mul' p q := by
    apply Subtype.ext; apply PowerSeries.ext; intro n
    apply (Jets.project_eq_iff (k := k) (n+1) _ _).mp ?_ n (by omega)
    rw [project_substitute f hf]
    calc
      _ = Jets.project (k := k) (n+1)
          ((TensorAlgebra.lift k f) (tensorTruncation (n+1) p * tensorTruncation (n+1) q)).val := by
        apply evaluation_respects_jet f hf
        simp only [map_mul, Subalgebra.coe_mul, project_truncation]
      _ = _ := by
        simp only [map_mul, Subalgebra.coe_mul, ← project_substitute f hf]
  commutes' c := by
    apply Subtype.ext; apply PowerSeries.ext; intro n
    apply (Jets.project_eq_iff (k := k) (n+1) _ _).mp ?_ n (by omega)
    rw [project_substitute f hf]
    calc
      _ = Jets.project (k := k) (n+1) ((TensorAlgebra.lift k f) (algebraMap k (A k V) c)).val := by
        apply evaluation_respects_jet f hf
        rw [project_truncation, AlgHom.commutes]
      _ = _ := by rw [AlgHom.commutes]

@[simp] theorem substitutionHom_apply (p : Completion k V) :
    substitutionHom f hf p = substitute f p := rfl

theorem substitute_letter (x : V) : substitute f (letter k V x) = f x := by
  apply Subtype.ext; apply PowerSeries.ext; intro n
  by_cases hn : n = 0
  · subst n
    simpa [substitute_coeff, letter_coeff] using (hf x).symm
  · rw [substitute_coeff, Finset.sum_eq_single 1]
    · simp [letter_coeff]
    · intro m hm hm1; simp [letter_coeff, hm1]
    · intro h; exact (h (Finset.mem_range.mpr (by omega))).elim

theorem substitute_positive (p : Completion k V) (hp : Positive k V p) :
    Positive k W (substitute f p) := by
  change PowerSeries.coeff 0 (substitute f p).val = 0
  rw [substitute_coeff]
  norm_num only [Nat.zero_add, Finset.range_one, Finset.sum_singleton]
  rw [hp, map_zero, Subalgebra.coe_zero, map_zero]

/-- Substitution commutes with every scalar formal series on positive inputs.
Both sides are tested in each finite jet, where they are finite polynomials. -/
theorem substitute_seriesEval (c : ℕ → k) (p : Completion k V) (hp : Positive k V p) :
    substitutionHom f hf (seriesEval (generators k V) c p) =
      seriesEval (generators k W) c (substitutionHom f hf p) := by
  apply Subtype.ext; apply PowerSeries.ext; intro n
  apply (Jets.project_eq_iff (k := k) (n+1) _ _).mp ?_ n (by omega)
  have hjet : Jets.project (k := k) (n+1) (seriesEval (generators k V) c p).val =
      Jets.project (k := k) (n+1) (∑ m ∈ Finset.range (n+1), c m • p^m : Completion k V).val := by
    rw [Jets.project_seriesEval _ _ _ _ hp]
    simp only [completion_val_sum, Subalgebra.coe_smul, Subalgebra.coe_pow, map_sum,
      map_smul, map_pow]
  have h := substitute_jet_congr f hf (n+1) _ _ hjet
  change Jets.project (k := k) (n+1)
    (substitutionHom f hf (seriesEval (generators k V) c p)).val =
      Jets.project (k := k) (n+1)
        (substitutionHom f hf (∑ m ∈ Finset.range (n+1), c m • p^m)).val at h
  rw [h, map_sum]
  simp only [map_smul, map_pow, completion_val_sum, Subalgebra.coe_smul,
    Subalgebra.coe_pow, map_sum]
  exact (Jets.project_seriesEval (n+1) (generators k W) c (substitutionHom f hf p)
    (substitute_positive f hf p hp)).symm

theorem substitute_exponential (p : Completion k V) (hp : Positive k V p) :
    substitutionHom f hf (exponential (generators k V) p) =
      exponential (generators k W) (substitutionHom f hf p) :=
  substitute_seriesEval f hf _ p hp

theorem substitute_logarithm (g : Completion k V)
    (hg : PowerSeries.coeff 0 g.val = 1) :
    substitutionHom f hf (logarithm (generators k V) g) =
      logarithm (generators k W) (substitutionHom f hf g) := by
  have hpos : Positive k V (g-1) := by
    change PowerSeries.coeff 0 (g.val-1) = 0
    rw [map_sub, hg]; simp
  unfold logarithm
  rw [substitute_seriesEval f hf _ (g-1) hpos, map_sub, map_one]

end Substitution

theorem substitution_spec :
    Specs.LieAlgebrasAndRepresentations.FormalBCH.substitutionExpected.{u,v,w} := by
  intro k V W _ _ _ _ _ _ f hf
  refine ⟨?_, substitute_coeff_cutoff f hf, substitutionHom f hf, fun _ => rfl,
    substitute_letter f hf, substitute_positive f hf,
    substitute_exponential f hf, substitute_logarithm f hf⟩
  intro m n a ha hn
  exact evaluation_vanishes f hf ha n hn

theorem evaluation_spec :
    Specs.LieAlgebrasAndRepresentations.FormalBCH.evaluationExpected.{u,w} := by
  intro k W _ _ _ _ p q hp hq
  have hp' : PowerSeries.coeff 0 p.val = 0 := hp
  have hq' : PowerSeries.coeff 0 q.val = 0 := hq
  let f := twoInputMap p q
  have hf : ∀ a, Positive k W (f a) := by
    intro a
    change PowerSeries.coeff 0 (a 0 • p.val + a 1 • q.val) = 0
    simp only [map_add, PowerSeries.coeff_smul, hp', hq', smul_zero, add_zero]
  change substitutionHom f hf (bch k (Two k) (X k) (Y k)) = bch k W p q
  unfold bch
  rw [substitute_logarithm f hf _ (exp_product_constant k (Two k) _ _), map_mul]
  have hx : Positive k (Two k) (X k) := by simp [Positive, X, letter_coeff]
  have hy : Positive k (Two k) (Y k) := by simp [Positive, Y, letter_coeff]
  rw [substitute_exponential f hf _ hx, substitute_exponential f hf _ hy]
  have hX : substitutionHom f hf (X k) = p := by
    rw [substitutionHom_apply, X, substitute_letter f hf]
    simp [f, twoInputMap, Pi.single_apply]
  have hY : substitutionHom f hf (Y k) = q := by
    rw [substitutionHom_apply, Y, substitute_letter f hf]
    simp [f, twoInputMap, Pi.single_apply]
  rw [hX, hY]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
/-- The homogeneous expansion of the universal BCH series through degree three.
The defining sums are finite in each of these degrees. After expansion of the
Cauchy products, scalar normalization gives the two cubic commutators. -/
theorem cubic_spec : Specs.LieAlgebrasAndRepresentations.FormalBCH.cubicExpected.{u} := by
  intro k _ _ n hn
  interval_cases n <;>
    norm_num [universalBCH, bch, logarithm, exponential, seriesEval_coeff,
      Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_smul,
      Finset.sum_range_succ, expCoefficients, logCoefficients, Nat.factorial,
      pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
      map_sub, map_add, PowerSeries.coeff_one, PowerSeries.coeff_smul,
      X, Y, letter_coeff, cubic] <;>
    (try simp only [add_mul, mul_add, sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, mul_assoc]
     module)

end LieAlgebrasAndRepresentations.FormalBCH
