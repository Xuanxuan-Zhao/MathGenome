import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.HilbertSamuelPolynomial
import MathGenome.Internal.AlgebraCore.P103.Ch06.FiniteColength
import MathGenome.Internal.AlgebraCore.P103.Ch07.ReesGradedConstruction
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertSerreLength
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.Polynomial.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

namespace P103.HilbertSamuelPolynomial
noncomputable section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

lemma powerSubmodule_antitone (Q : Ideal R) : Antitone (powerSubmodule Q M) :=
  fun _ _ h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

/-- The natural inclusion Q^n M/Q^(n+1) M → M/Q^(n+1) M. -/
def layerInclusion (Q : Ideal R) (n : ℕ) : Layer Q M n →ₗ[R] Quotient Q M n :=
  (successorSubmodule Q M n).liftQ
    ((powerSubmodule Q M (n + 1)).mkQ.comp (powerSubmodule Q M n).subtype)
    (by intro x hx; exact (Submodule.Quotient.mk_eq_zero _).mpr hx)

lemma layerInclusion_injective (Q : Ideal R) (n : ℕ) :
    Function.Injective (layerInclusion (M := M) Q n) := by
  rw [← LinearMap.ker_eq_bot, layerInclusion, Submodule.ker_liftQ_eq_bot]
  simp [LinearMap.ker_comp, Submodule.ker_mkQ, successorSubmodule]

/-- Finite colength propagates to every positive ideal power; no faithfulness
of M is used. -/
lemma quotient_finite_length [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] [Nontrivial M] (Q : Ideal R)
    (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (h : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M)))) (n : ℕ) :
    IsFiniteLength R (Quotient Q M n) := by
  have hrad := (P103.Ch06.FiniteColength.finite_colength_iff R M Q hQ).mp h
  apply (P103.Ch06.FiniteColength.finite_colength_iff R M (Q ^ (n + 1))
    ((Ideal.pow_le_self (by omega)).trans hQ)).mpr
  rw [Ideal.radical_sup, Ideal.radical_pow Q (by omega), ← Ideal.radical_sup]
  exact hrad

theorem finite_lengths : Specs.P103.HilbertSamuelPolynomial.finiteLengthsType := by
  intro R _ _ _ M _ _ _ _ Q hQ h n
  have hf := quotient_finite_length Q hQ h n
  exact ⟨hf.of_injective (layerInclusion_injective Q n), hf⟩

/-- Surjective restriction of scalars preserves both the extended length
and finite length, including zero modules. -/
theorem scalar_lengths : Specs.P103.HilbertSamuelPolynomial.scalarLengthsType := by
  intro R S _ _ _ N _ _ _ _ h
  have he : Module.length R N = Module.length S N := Module.length_eq_of_surjective h
  exact ⟨he, by rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff, he]⟩

/-- The next quotient maps onto the preceding quotient. -/
def quotientReduction (Q : Ideal R) (n : ℕ) :
    Quotient Q M (n + 1) →ₗ[R] Quotient Q M n :=
  Submodule.factor (powerSubmodule_antitone Q (Nat.le_succ (n + 1)))

lemma layer_exact (Q : Ideal R) (n : ℕ) :
    Function.Exact (layerInclusion (M := M) Q (n + 1)) (quotientReduction Q n) := by
  intro x
  obtain ⟨m, rfl⟩ := (powerSubmodule Q M (n + 2)).mkQ_surjective x
  constructor
  · intro hx
    have hm : m ∈ powerSubmodule Q M (n + 1) :=
      (Submodule.Quotient.mk_eq_zero _).mp hx
    exact ⟨(successorSubmodule Q M (n + 1)).mkQ ⟨m, hm⟩, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := (successorSubmodule Q M (n + 1)).mkQ_surjective y
    rw [← hy]
    exact (Submodule.Quotient.mk_eq_zero _).mpr z.2

lemma quotientLength_succ [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] [Nontrivial M] (Q : Ideal R)
    (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (h : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M)))) (n : ℕ) :
    quotientLength Q M (n + 1) = layerLength Q M (n + 1) + quotientLength Q M n := by
  have he := Module.length_eq_add_of_exact (layerInclusion (M := M) Q (n + 1))
    (quotientReduction Q n) (layerInclusion_injective Q (n + 1))
    (Submodule.factor_surjective (powerSubmodule_antitone Q (Nat.le_succ (n + 1))))
    (layer_exact Q n)
  have hf := finite_lengths R M Q hQ h (n + 1)
  have hg := quotient_finite_length Q hQ h n
  unfold quotientLength layerLength
  rw [he, ENat.toNat_add ((Module.length_ne_top_iff).mpr hf.1)
    ((Module.length_ne_top_iff).mpr hg)]

lemma layerLength_zero (Q : Ideal R) : layerLength Q M 0 = quotientLength Q M 0 := by
  let e : powerSubmodule Q M 0 ≃ₗ[R] M :=
    (LinearEquiv.ofEq _ _ (by simp [powerSubmodule])).trans Submodule.topEquiv
  have he : (successorSubmodule Q M 0).map e.toLinearMap = powerSubmodule Q M 1 := by
    ext m
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hm
      exact ⟨e.symm m, hm, e.apply_symm_apply m⟩
  exact congrArg ENat.toNat (Submodule.Quotient.equiv _ _ e he).length_eq

theorem sum_layers : Specs.P103.HilbertSamuelPolynomial.sumLayersType := by
  intro R _ _ _ M _ _ _ _ Q hQ h n
  induction n with
  | zero => simpa using (layerLength_zero (M := M) Q).symm
  | succ n ih =>
    rw [quotientLength_succ Q hQ h, ih]
    simp only [Finset.sum_range_succ]
    omega

/-- A polynomial over Q has a polynomial discrete primitive. -/
lemma exists_discrete_primitive (p : Polynomial ℚ) :
    ∃ q : Polynomial ℚ, ∀ x : ℚ, q.eval (x + 1) = q.eval x + p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨q, hq⟩ := hp
    obtain ⟨s, hs⟩ := hr
    refine ⟨q + s, fun x => ?_⟩
    simp only [Polynomial.eval_add, hq, hs]
    ring
  | monomial n a =>
    refine ⟨Polynomial.C (a / (n + 1 : ℚ)) * Polynomial.bernoulli (n + 1), fun x => ?_⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_monomial]
    rw [add_comm x, Polynomial.bernoulli_eval_one_add]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    have hn : (n + 1 : ℚ) ≠ 0 := by positivity
    field_simp

/-- Eventual polynomial differences have eventual polynomial partial sums.
The finitely many initial terms are retained as a constant correction. -/
lemma eventuallyPolynomial_of_recurrence (f g : ℕ → ℕ)
    (hrec : ∀ n, g (n + 1) = f (n + 1) + g n)
    (hpoly : ∃ p : Polynomial ℚ, EventuallyPolynomial f p) :
    ∃ q : Polynomial ℚ, EventuallyPolynomial g q := by
  obtain ⟨p, N, hp⟩ := hpoly
  obtain ⟨q, hq⟩ := exists_discrete_primitive p
  refine ⟨q.comp (Polynomial.X + 1) + Polynomial.C ((g N : ℚ) - q.eval ((N : ℚ) + 1)), N, ?_⟩
  intro n hn
  simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_C]
  induction n, hn using Nat.le_induction with
  | base => ring
  | succ n hn ih =>
    rw [hrec, Nat.cast_add, ih, hp (n + 1) (by omega)]
    push_cast
    have hstep := hq ((n : ℚ) + 1)
    linarith

lemma quotientLength_pos [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] [Nontrivial M] (Q : Ideal R)
    (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (h : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M)))) (n : ℕ) :
    0 < quotientLength Q M n := by
  have : Nontrivial (Quotient Q M n) :=
    P103.Ch06.FiniteColength.quotient_nontrivial R M (Q ^ (n + 1))
      ((Ideal.pow_le_self (by omega)).trans hQ)
  have hf := (Module.length_ne_top_iff).mpr (quotient_finite_length Q hQ h n)
  exact ENat.toNat_pos (Module.length_pos.ne') hf

/-- Nonnegative eventual values force a positive leading coefficient for
any nonconstant rational polynomial. -/
lemma leadingCoeff_pos_of_eventuallyPolynomial (f : ℕ → ℕ) (p : Polynomial ℚ)
    (hp : EventuallyPolynomial f p) (hd : 0 < p.natDegree) : 0 < p.leadingCoeff := by
  obtain ⟨N, hN⟩ := hp
  by_contra! hc
  have ht := (p.tendsto_atBot_of_leadingCoeff_nonpos
    (Polynomial.natDegree_pos_iff_degree_pos.mp hd) hc).comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℚ))
        Filter.atTop Filter.atTop)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_atBot 0)
  have hk := hK (max N K) (le_max_right N K)
  change p.eval ((max N K : ℕ) : ℚ) < 0 at hk
  rw [← hN (max N K) (le_max_left N K)] at hk
  exact (Nat.cast_nonneg (f (max N K))).not_gt hk

/-- Eventual polynomiality of the layers, together with exactness, gives
the nonzero cumulative polynomial and the sign of its leading coefficient. -/
lemma quotient_polynomial_of_layer [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] [Nontrivial M] (Q : Ideal R)
    (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (h : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))))
    (hpoly : ∃ p : Polynomial ℚ, EventuallyPolynomial (layerLength Q M) p) :
    ∃ p : Polynomial ℚ, EventuallyPolynomial (quotientLength Q M) p ∧ p ≠ 0 ∧
      (0 < p.natDegree → 0 < p.leadingCoeff) := by
  obtain ⟨p, hp⟩ := eventuallyPolynomial_of_recurrence _ _
    (quotientLength_succ Q hQ h) hpoly
  refine ⟨p, hp, ?_, leadingCoeff_pos_of_eventuallyPolynomial _ _ hp⟩
  intro hz
  obtain ⟨N, hN⟩ := hp
  have he := hN N le_rfl
  rw [hz, Polynomial.eval_zero, Nat.cast_eq_zero] at he
  exact (quotientLength_pos Q hQ h N).ne' he

/-- Adding the annihilator to Q changes none of the powers acting on M.
This is an alternative to changing the scalar ring to R/Ann(M). -/
lemma powerSubmodule_sup_annihilator (Q : Ideal R) (n : ℕ) :
    powerSubmodule (Q ⊔ Module.annihilator R M) M n = powerSubmodule Q M n := by
  induction n with
  | zero => simp [powerSubmodule]
  | succ n ih =>
    simp only [powerSubmodule, pow_succ', Submodule.mul_smul] at ih ⊢
    rw [ih, Submodule.sup_smul]
    have ha : Module.annihilator R M • (Q ^ n • (⊤ : Submodule R M)) = ⊥ :=
      Submodule.le_annihilator_iff.mp (by
        rw [← Submodule.annihilator_top]
        exact Submodule.annihilator_mono le_top)
    rw [ha, sup_bot_eq]

open P103.Rees P103.Graded P103.HilbertSerreLength in
/-- The actual degree-zero ring of the Rees grading is the original quotient R/Q. -/
def associatedBaseMap (Q : Ideal R) (G : NonnegativeGrading (AssociatedRing Q))
    (hG : ∀ n : ℕ, G.piece n = ringPiece Q n) : (R ⧸ Q) →+* Base G where
  toFun b := ⟨algebraMap (R ⧸ Q) (AssociatedRing Q) b, by
    change algebraMap (R ⧸ Q) (AssociatedRing Q) b ∈ G.piece (0 : ℤ)
    rw [show G.piece 0 = ringPiece Q 0 by simpa using hG 0]
    exact (congrArg (fun s : Set (AssociatedRing Q) =>
      algebraMap (R ⧸ Q) (AssociatedRing Q) b ∈ s) (P103.Rees.degree_zero Q).2) ▸ ⟨b, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

open P103.Rees P103.Graded in
lemma associatedBaseMap_bijective (Q : Ideal R) (G : NonnegativeGrading (AssociatedRing Q))
    (hG : ∀ n : ℕ, G.piece n = ringPiece Q n) :
    Function.Bijective (associatedBaseMap Q G hG) := by
  constructor
  · intro x y h
    exact (P103.Rees.degree_zero Q).1 (congrArg Subtype.val h)
  · intro b
    have hb : (b : AssociatedRing Q) ∈ G.piece (0 : ℤ) := b.2
    rw [show G.piece 0 = ringPiece Q 0 by simpa using hG 0] at hb
    have hb' : (b : AssociatedRing Q) ∈ Set.range (algebraMap (R ⧸ Q) (AssociatedRing Q)) :=
      (congrArg (fun s : Set (AssociatedRing Q) => (b : AssociatedRing Q) ∈ s)
        (P103.Rees.degree_zero Q).2).symm ▸ hb
    obtain ⟨x, hx⟩ := hb'
    exact ⟨x, Subtype.ext hx⟩

open P103.Rees in
lemma moduleClass_smul_base (Q : Ideal R) (n : ℕ) (r : R)
    (m : (Q ^ n • (⊤ : Submodule R M) : Submodule R M)) :
    moduleClass Q M n (r • m) =
      algebraMap (R ⧸ Q) (AssociatedRing Q) (Ideal.Quotient.mk Q r) • moduleClass Q M n m := by
  change (quotientSubmodule Q M).mkQ (term Q M n (r • m)) =
    (algebraMap (ReesAlgebra Q) (AssociatedRing Q) (algebraMap R (ReesAlgebra Q) r)) •
      (quotientSubmodule Q M).mkQ (term Q M n m)
  rw [IsScalarTower.algebraMap_smul, ← _root_.map_smul]
  congr 1
  apply Subtype.ext
  change PolynomialModule.single R n (r • m.1) =
    (algebraMap R (Polynomial R) r) • PolynomialModule.single R n m.1
  rw [IsScalarTower.algebraMap_smul]
  exact PolynomialModule.single_smul n r m.1

open P103.Rees P103.Graded P103.HilbertSerreLength in
lemma component_length_eq (Q : Ideal R) (G : NonnegativeGrading (AssociatedRing Q))
    (hG : ∀ n : ℕ, G.piece n = ringPiece Q n)
    (U : ModuleGrading G (AssociatedModule Q M))
    (hU : ∀ n : ℕ, U.piece n = modulePiece Q M n) (n : ℕ) :
    Module.length R (Layer Q M n) = Module.length (Base G) (component G U n) := by
  obtain ⟨e₀, he₀⟩ := (P103.Rees.component_identifications Q M).2 n
  let e : Layer Q M n ≃+ modulePiece Q M n := e₀
  have he (m : powerSubmodule Q M n) :
      (e ((successorSubmodule Q M n).mkQ m) : AssociatedModule Q M) = moduleClass Q M n m :=
    he₀ m
  let d : modulePiece Q M n ≃+ component G U n :=
    { toFun := fun x => ⟨x.1, by change x.1 ∈ U.piece n; rw [hU]; exact x.2⟩
      invFun := fun x => ⟨x.1, by rw [← hU]; exact x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let σ : R →+* Base G := (associatedBaseMap Q G hG).comp (Ideal.Quotient.mk Q)
  have hσ : Function.Surjective σ :=
    (associatedBaseMap_bijective Q G hG).2.comp Ideal.Quotient.mk_surjective
  let : RingHomSurjective σ := ⟨hσ⟩
  let f : Layer Q M n →ₛₗ[σ] component G U n :=
    { __ := e.trans d
      map_smul' := by
        intro r x
        obtain ⟨m, rfl⟩ := (successorSubmodule Q M n).mkQ_surjective x
        apply Subtype.ext
        change (e ((successorSubmodule Q M n).mkQ (r • m)) : AssociatedModule Q M) =
          (algebraMap (R ⧸ Q) (AssociatedRing Q) (Ideal.Quotient.mk Q r)) •
            (e ((successorSubmodule Q M n).mkQ m) : AssociatedModule Q M)
        rw [he, he]
        exact moduleClass_smul_base Q n r m }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso
      (Submodule.orderIsoMapComapOfBijective f (e.trans d).bijective)]

open P103.Rees P103.Graded P103.HilbertSerreLength in
lemma layer_polynomial_of_artinian_quotient [IsNoetherianRing R] [Module.Finite R M]
    (Q : Ideal R) [IsArtinianRing (R ⧸ Q)] :
    ∃ p : Polynomial ℚ, EventuallyPolynomial (layerLength Q M) p := by
  obtain ⟨G, hG, ⟨U, hU⟩, hstd⟩ := P103.Rees.integer_grading Q M
  let : Module.Finite (AssociatedRing Q) (AssociatedModule Q M) :=
    P103.Rees.quotient_finite Q M inferInstance
  let : IsArtinianRing (Base G) := (associatedBaseMap_bijective Q G hG).2.isArtinianRing
  obtain ⟨b, p, e, q, _, _, ⟨J, hq⟩, _, _⟩ :=
    (P103.HilbertSerreLength.hilbert_serre G U (hstd inferInstance)).2
  refine ⟨q, J.toNat, fun n hn => ?_⟩
  have hj : J ≤ (n : ℤ) := by omega
  have he := hq n hj
  simp only [hilbertFunction, Int.cast_natCast] at he
  rw [← component_length_eq Q G hG U hU n] at he
  exact he

/-- The effective base quotient is Artinian even when R/Q itself is not. -/
lemma effective_quotient_artinian [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] [Nontrivial M] (Q : Ideal R)
    (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (h : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M)))) :
    IsArtinianRing (R ⧸ (Q ⊔ Module.annihilator R M)) := by
  have hrad := (P103.Ch06.FiniteColength.finite_colength_iff R M Q hQ).mp h
  apply isArtinianRing_iff_krullDimLE_zero.mpr
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro P hP
  have hm : IsLocalRing.maximalIdeal R ≤ P := by
    rw [← hrad]
    exact hP.isPrime.radical_le_iff.mpr hP.1.2
  have he := (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hP.isPrime.ne_top hm
  rw [← he]
  infer_instance

lemma nestedQuotient_length_congr (P P' N N' : Submodule R M) (hP : P = P') (hN : N = N') :
    Module.length R (P ⧸ N.comap P.subtype) =
      Module.length R (P' ⧸ N'.comap P'.subtype) := by
  subst P'
  subst N'
  rfl

theorem layer_polynomial : Specs.P103.HilbertSamuelPolynomial.layerPolynomialType := by
  intro R _ _ _ M _ _ _ _ Q hQ h
  let := effective_quotient_artinian Q hQ h
  have hp := layer_polynomial_of_artinian_quotient (M := M) (Q ⊔ Module.annihilator R M)
  have he : layerLength (Q ⊔ Module.annihilator R M) M = layerLength Q M := by
    funext n
    apply congrArg ENat.toNat
    exact nestedQuotient_length_congr _ _ _ _ (powerSubmodule_sup_annihilator Q n)
      (powerSubmodule_sup_annihilator Q (n + 1))
  rw [he] at hp
  exact hp

theorem quotient_polynomial : Specs.P103.HilbertSamuelPolynomial.quotientPolynomialType := by
  intro R _ _ _ M _ _ _ _ Q hQ h
  exact quotient_polynomial_of_layer Q hQ h (layer_polynomial R M Q hQ h)

/-- In particular, the canonical action of the annihilator quotient preserves
length and finite length, without requiring faithfulness of the original action. -/
lemma annihilator_scalar_lengths :
    letI := Module.quotientAnnihilator (R := R) (M := M)
    Module.length R M = Module.length (R ⧸ Module.annihilator R M) M ∧
      (IsFiniteLength R M ↔ IsFiniteLength (R ⧸ Module.annihilator R M) M) := by
  letI := Module.quotientAnnihilator (R := R) (M := M)
  let : IsScalarTower R (R ⧸ Module.annihilator R M) M :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
  exact scalar_lengths R (R ⧸ Module.annihilator R M) M Ideal.Quotient.mk_surjective

universe u v

theorem polynomial_existence : Specs.P103.HilbertSamuelPolynomial.polynomialExistenceType.{u,v} :=
  ⟨finite_lengths, sum_layers, layer_polynomial, quotient_polynomial, scalar_lengths⟩

end
end P103.HilbertSamuelPolynomial
