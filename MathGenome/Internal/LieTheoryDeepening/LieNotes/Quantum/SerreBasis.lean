import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.SerrePresentation
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.SerreBasis
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.FinCases

namespace LieNotes.Quantum.SerreBasis

open SerrePresentation
open scoped TensorProduct

universe u v
variable {A : Type u} [CommRing A]
variable {D : Type v} [Ring D] [Algebra A D]

abbrev OrderedAlgebra := Specs.LieNotes.Quantum.SerreBasis.OrderedAlgebra
abbrev orderedGenerator := @Specs.LieNotes.Quantum.SerreBasis.orderedGenerator
abbrev orderedMonomial := @Specs.LieNotes.Quantum.SerreBasis.orderedMonomial
private abbrev orderedIdeal := @Specs.LieNotes.Quantum.SerreBasis.orderedIdeal

private theorem serre_left (q : Aˣ) (a b : D) :
    a * (a * b - (↑(q⁻¹) : A) • (b * a)) -
      (↑q : A) • ((a * b - (↑(q⁻¹) : A) • (b * a)) * a) =
        serrePolynomial q a b := by
  simp only [Specs.LieNotes.Quantum.SerrePresentation.serrePolynomial, pow_two,
    mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul, Units.mul_inv,
    one_smul, add_smul, mul_assoc]
  abel

private theorem serre_right (q : Aˣ) (a b : D) :
    (a * b - (↑(q⁻¹) : A) • (b * a)) * b -
      (↑q : A) • (b * (a * b - (↑(q⁻¹) : A) • (b * a))) =
        serrePolynomial q b a := by
  simp only [Specs.LieNotes.Quantum.SerrePresentation.serrePolynomial, pow_two,
    mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul, Units.mul_inv,
    one_smul, add_smul, mul_assoc]
  abel

theorem xz (q : Aˣ) : x q * z q = (↑q : A) • (z q * x q) :=
  sub_eq_zero.mp ((serre_left q (x q) (y q)).trans (relationXY_zero q))

theorem zy (q : Aˣ) : z q * y q = (↑q : A) • (y q * z q) :=
  sub_eq_zero.mp ((serre_right q (x q) (y q)).trans (relationYX_zero q))

theorem yx (q : Aˣ) : y q * x q = (↑q : A) • (x q * y q) - (↑q : A) • z q := by
  change _ = _ - (↑q : A) • (x q * y q - (↑(q⁻¹) : A) • (y q * x q))
  rw [smul_sub, smul_smul, Units.mul_inv, one_smul]
  abel

theorem relations : Specs.LieNotes.Quantum.SerreBasis.relationsProp.{u} :=
  fun q => ⟨xz q, zy q, yx q⟩

theorem zx (q : Aˣ) : z q * x q = (↑(q⁻¹) : A) • (x q * z q) := by
  rw [xz q, smul_smul, Units.inv_mul, one_smul]

theorem yz (q : Aˣ) : y q * z q = (↑(q⁻¹) : A) • (z q * y q) := by
  rw [zy q, smul_smul, Units.inv_mul, one_smul]

private theorem serre_of_ordered (q : Aˣ) (a c b : D)
    (hZX : c * a = (↑(q⁻¹) : A) • (a * c))
    (hYZ : b * c = (↑(q⁻¹) : A) • (c * b))
    (hYX : b * a = (↑q : A) • (a * b) - (↑q : A) • c) :
    a * b - (↑(q⁻¹) : A) • (b * a) = c ∧
      serrePolynomial q a b = 0 ∧ serrePolynomial q b a = 0 := by
  have hc : a * b - (↑(q⁻¹) : A) • (b * a) = c := by
    simp only [hYX, smul_sub, smul_smul, Units.inv_mul, one_smul, sub_sub_cancel]
  refine ⟨hc, ?_, ?_⟩
  · rw [← serre_left, hc, hZX, smul_smul, Units.mul_inv, one_smul, sub_self]
  · rw [← serre_right, hc, hYZ, smul_smul, Units.mul_inv, one_smul, sub_self]

private def threeValues (a c b : D) : Fin 3 → D :=
  Fin.cases a (Fin.cases c (fun _ => b))

private def orderedLift (q : Aˣ) (a c b : D)
    (hZX : c * a = (↑(q⁻¹) : A) • (a * c))
    (hYZ : b * c = (↑(q⁻¹) : A) • (c * b))
    (hYX : b * a = (↑q : A) • (a * b) - (↑q : A) • c) :
    OrderedAlgebra A q →ₐ[A] D :=
  let ev := FreeAlgebra.lift A (threeValues a c b)
  Ideal.Quotient.liftₐ (orderedIdeal q).asIdeal ev (by
    have h : orderedIdeal q ≤ TwoSidedIdeal.ker (ev : FreeAlgebra A (Fin 3) →+* D) := by
      apply TwoSidedIdeal.span_le.mpr
      intro r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      apply (TwoSidedIdeal.mem_ker (ev : FreeAlgebra A (Fin 3) →+* D)).mpr
      change ev r = 0
      rcases hr with rfl | rfl | rfl <;>
        simp only [ev, map_sub, map_mul, map_smul, FreeAlgebra.lift_ι_apply]
      · exact sub_eq_zero.mpr hZX
      · exact sub_eq_zero.mpr hYZ
      · exact sub_eq_zero.mpr hYX
    exact fun r hr => (TwoSidedIdeal.mem_ker (ev : FreeAlgebra A (Fin 3) →+* D)).mp
      (h (TwoSidedIdeal.mem_asIdeal.mp hr)))

@[simp] private theorem orderedLift_generator (q : Aˣ) (a c b : D) (hZX hYZ hYX)
    (i : Fin 3) :
    orderedLift q a c b hZX hYZ hYX (orderedGenerator q i) = threeValues a c b i := by
  unfold orderedLift
  change (_ : FreeAlgebra A (Fin 3) →ₐ[A] D) (FreeAlgebra.ι A i) = _
  exact FreeAlgebra.lift_ι_apply _ _

private theorem ordered_hom_ext {q : Aˣ} {F G : OrderedAlgebra A q →ₐ[A] D}
    (h : ∀ i, F (orderedGenerator q i) = G (orderedGenerator q i)) : F = G := by
  apply Ideal.Quotient.algHom_ext A
  exact FreeAlgebra.hom_ext (funext h)

private theorem ordered_relations (q : Aˣ) :
    let X := orderedGenerator q 0
    let Z := orderedGenerator q 1
    let Y := orderedGenerator q 2
    Z * X = (↑(q⁻¹) : A) • (X * Z) ∧
      Y * Z = (↑(q⁻¹) : A) • (Z * Y) ∧
      Y * X = (↑q : A) • (X * Y) - (↑q : A) • Z := by
  dsimp only
  let p := Ideal.Quotient.mkₐ A (orderedIdeal q).asIdeal
  have hp (r : FreeAlgebra A (Fin 3)) (hr : r ∈ orderedIdeal q) : p r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (TwoSidedIdeal.mem_asIdeal.mpr hr)
  refine ⟨sub_eq_zero.mp ?_, sub_eq_zero.mp ?_, sub_eq_zero.mp ?_⟩
  all_goals
    simp only [Specs.LieNotes.Quantum.SerreBasis.orderedGenerator, ← map_mul, ← map_smul,
      ← map_sub]
    apply hp
    apply TwoSidedIdeal.subset_span
    simp

private theorem ordered_serre (q : Aˣ) :
    orderedGenerator q 0 * orderedGenerator q 2 -
        (↑(q⁻¹) : A) • (orderedGenerator q 2 * orderedGenerator q 0) = orderedGenerator q 1 ∧
      serrePolynomial q (orderedGenerator q 0) (orderedGenerator q 2) = 0 ∧
      serrePolynomial q (orderedGenerator q 2) (orderedGenerator q 0) = 0 :=
  serre_of_ordered q (orderedGenerator q 0) (orderedGenerator q 1) (orderedGenerator q 2)
    (ordered_relations q).1 (ordered_relations q).2.1 (ordered_relations q).2.2

private def toSerre (q : Aˣ) : OrderedAlgebra A q →ₐ[A] SerreAlgebra A q :=
  orderedLift q (x q) (z q) (y q) (zx q) (yz q) (yx q)

private def twoValues (a b : D) : Fin 2 → D :=
  Fin.cases a (fun _ => b)

private def fromSerre (q : Aˣ) : SerreAlgebra A q →ₐ[A] OrderedAlgebra A q :=
  lift q (twoValues (orderedGenerator q 0) (orderedGenerator q 2))
    (ordered_serre q).2.1 (ordered_serre q).2.2

@[simp] private theorem toSerre_generator (q : Aˣ) (i : Fin 3) :
    toSerre q (orderedGenerator q i) = threeValues (x q) (z q) (y q) i :=
  orderedLift_generator q _ _ _ _ _ _ i

@[simp] private theorem fromSerre_x (q : Aˣ) :
    fromSerre q (x q) = orderedGenerator q 0 :=
  lift_generator q _ (ordered_serre q).2.1 (ordered_serre q).2.2 0

@[simp] private theorem fromSerre_y (q : Aˣ) :
    fromSerre q (y q) = orderedGenerator q 2 :=
  lift_generator q _ (ordered_serre q).2.1 (ordered_serre q).2.2 1

@[simp] private theorem fromSerre_z (q : Aˣ) :
    fromSerre q (z q) = orderedGenerator q 1 := by
  simp only [Specs.LieNotes.Quantum.SerrePresentation.z, map_sub, map_mul, map_smul,
    fromSerre_x, fromSerre_y]
  exact (ordered_serre q).1

/-- Elimination of the middle generator identifies the two presentations. -/
def orderedEquiv (q : Aˣ) : OrderedAlgebra A q ≃ₐ[A] SerreAlgebra A q :=
  AlgEquiv.ofAlgHom (toSerre q) (fromSerre q)
    (hom_ext (by intro i; fin_cases i <;>
      change toSerre q (fromSerre q _) = _ <;>
      first | exact (congrArg (toSerre q) (fromSerre_x q)).trans (toSerre_generator q 0)
            | exact (congrArg (toSerre q) (fromSerre_y q)).trans (toSerre_generator q 2)))
    (ordered_hom_ext (by
      intro i
      change fromSerre q (toSerre q (orderedGenerator q i)) = orderedGenerator q i
      rw [toSerre_generator]
      fin_cases i
      · exact fromSerre_x q
      · exact fromSerre_z q
      · exact fromSerre_y q))

theorem orderedPresentation :
    Specs.LieNotes.Quantum.SerreBasis.orderedPresentationProp.{u} :=
  fun q => ⟨orderedEquiv q, toSerre_generator q 0, toSerre_generator q 1,
    toSerre_generator q 2⟩


section Basis

private abbrev Exponents := ℕ × ℕ × ℕ
private abbrev Coefficients (A : Type u) [CommRing A] := Exponents →₀ A

private noncomputable def term (A : Type u) [CommRing A] (a b d : ℕ) : Coefficients A :=
  Finsupp.single (a, b, d) 1

/-- The coefficient of the term with one fewer x when y is moved past a power of x. -/
private def correction (q : Aˣ) : ℕ → A
  | 0 => 0
  | a + 1 => (↑q : A) * correction q a + (↑q : A) * (↑(q⁻¹) : A) ^ a

private noncomputable def opX (A : Type u) [CommRing A] : Module.End A (Coefficients A) :=
  Finsupp.linearCombination A fun i => term A (i.1 + 1) i.2.1 i.2.2

private noncomputable def opZ (q : Aˣ) : Module.End A (Coefficients A) :=
  Finsupp.linearCombination A fun i => (↑(q⁻¹) : A) ^ i.1 • term A i.1 (i.2.1 + 1) i.2.2

private noncomputable def opY (q : Aˣ) : Module.End A (Coefficients A) :=
  Finsupp.linearCombination A fun i =>
    ((↑q : A) ^ i.1 * (↑(q⁻¹) : A) ^ i.2.1) • term A i.1 i.2.1 (i.2.2 + 1) -
      correction q i.1 • term A (i.1 - 1) (i.2.1 + 1) i.2.2

@[simp] private theorem opX_term (a b d : ℕ) :
    opX A (term A a b d) = term A (a + 1) b d := by
  simp [opX, term]

@[simp] private theorem opZ_term (q : Aˣ) (a b d : ℕ) :
    opZ q (term A a b d) = (↑(q⁻¹) : A) ^ a • term A a (b + 1) d := by
  simp [opZ, term]

@[simp] private theorem opY_term (q : Aˣ) (a b d : ℕ) :
    opY q (term A a b d) =
      ((↑q : A) ^ a * (↑(q⁻¹) : A) ^ b) • term A a b (d + 1) -
        correction q a • term A (a - 1) (b + 1) d := by
  simp [opY, term]

private theorem term_ext {M : Type*} [AddCommMonoid M] [Module A M]
    {f g : Coefficients A →ₗ[A] M}
    (h : ∀ a b d, f (term A a b d) = g (term A a b d)) : f = g := by
  apply Finsupp.lhom_ext
  rintro ⟨a, b, d⟩ c
  change f (Finsupp.single (a, b, d) c) = g (Finsupp.single (a, b, d) c)
  rw [← Finsupp.smul_single_one, map_smul, map_smul]
  exact congrArg (c • ·) (h a b d)

private theorem opZX (q : Aˣ) :
    opZ q * opX A = (↑(q⁻¹) : A) • (opX A * opZ q) := by
  apply term_ext
  intro a b d
  simp only [Module.End.mul_apply, LinearMap.smul_apply, opX_term, opZ_term, map_smul,
    smul_smul, pow_succ']

private theorem opYZ (q : Aˣ) :
    opY q * opZ q = (↑(q⁻¹) : A) • (opZ q * opY q) := by
  apply term_ext
  intro a b d
  rcases a with _ | a <;>
    simp only [Module.End.mul_apply, LinearMap.smul_apply, opZ_term, opY_term,
      map_sub, map_smul, smul_sub, smul_smul]
  · simp [correction, pow_succ, mul_comm]
  · simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

private theorem opYX (q : Aˣ) :
    opY q * opX A = (↑q : A) • (opX A * opY q) - (↑q : A) • opZ q := by
  apply term_ext
  intro a b d
  rcases a with _ | a <;>
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      opX_term, opZ_term, opY_term, map_sub, map_smul, smul_sub, smul_smul]
  · simp [correction]
  · simp only [Nat.add_sub_cancel, correction, add_smul, sub_sub, pow_succ,
      mul_assoc, mul_comm]

private theorem op_serre (q : Aˣ) :
    opX A * opY q - (↑(q⁻¹) : A) • (opY q * opX A) = opZ q ∧
      serrePolynomial q (opX A) (opY q) = 0 ∧ serrePolynomial q (opY q) (opX A) = 0 :=
  serre_of_ordered q (opX A) (opZ q) (opY q) (opZX q) (opYZ q) (opYX q)

private noncomputable def action (q : Aˣ) : SerreAlgebra A q →ₐ[A] Module.End A (Coefficients A) :=
  lift q (twoValues (opX A) (opY q)) (op_serre q).2.1 (op_serre q).2.2

@[simp] private theorem action_x (q : Aˣ) : action q (x q) = opX A :=
  lift_generator q (twoValues (opX A) (opY q)) (op_serre q).2.1 (op_serre q).2.2 0

@[simp] private theorem action_y (q : Aˣ) : action q (y q) = opY q :=
  lift_generator q (twoValues (opX A) (opY q)) (op_serre q).2.1 (op_serre q).2.2 1

@[simp] private theorem action_z (q : Aˣ) : action q (z q) = opZ q := by
  simp only [Specs.LieNotes.Quantum.SerrePresentation.z, map_sub, map_mul, map_smul,
    action_x, action_y]
  exact (op_serre q).1

private theorem opX_pow (n a b d : ℕ) :
    (opX A ^ n) (term A a b d) = term A (a + n) b d := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, opX_term, Nat.add_assoc]

private theorem opZ_pow (q : Aˣ) (n b d : ℕ) :
    (opZ q ^ n) (term A 0 b d) = term A 0 (b + n) d := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, opZ_term]; simp [Nat.add_assoc]

private theorem opY_pow (q : Aˣ) (n d : ℕ) :
    (opY q ^ n) (term A 0 0 d) = term A 0 0 (d + n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, opY_term]; simp [correction, Nat.add_assoc]

private noncomputable def expand (q : Aˣ) : Coefficients A →ₗ[A] SerreAlgebra A q :=
  Finsupp.linearCombination A (orderedMonomial q)

@[simp] private theorem expand_term (q : Aˣ) (a b d : ℕ) :
    expand q (term A a b d) = orderedMonomial q (a, b, d) := by
  simp [expand, term]

private noncomputable def coefficients (q : Aˣ) : SerreAlgebra A q →ₗ[A] Coefficients A :=
  (LinearMap.applyₗ (R := A) (term A 0 0 0)).comp (action q).toLinearMap

private theorem coefficients_expand (q : Aˣ) :
    (coefficients q).comp (expand q) = LinearMap.id := by
  apply term_ext
  intro a b d
  simp [coefficients, Specs.LieNotes.Quantum.SerreBasis.orderedMonomial,
    Module.End.mul_apply, opY_pow, opZ_pow, opX_pow]


private theorem orderedMonomial_independent (q : Aˣ) : LinearIndependent A (orderedMonomial q) := by
  apply linearIndependent_iff_injective_finsuppLinearCombination.mpr
  have h (v : Coefficients A) : coefficients q (expand q v) = v :=
    LinearMap.congr_fun (coefficients_expand q) v
  exact (show Function.LeftInverse (coefficients q) (expand q) from h).injective

private theorem skew_mul_pow {a b : D} {r : A} (h : a * b = r • (b * a)) (n : ℕ) :
    a * b ^ n = r ^ n • (b ^ n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      a * b ^ (n + 1) = (a * b) * b ^ n := by rw [pow_succ', mul_assoc]
      _ = r • (b * (a * b ^ n)) := by rw [h, smul_mul_assoc, mul_assoc]
      _ = r ^ (n + 1) • (b ^ (n + 1) * a) := by
        rw [ih, mul_smul_comm, smul_smul, pow_succ', pow_succ', mul_assoc]

private theorem monomial_x (q : Aˣ) (a b d : ℕ) :
    x q * orderedMonomial q (a, b, d) = orderedMonomial q (a + 1, b, d) := by
  simp only [Specs.LieNotes.Quantum.SerreBasis.orderedMonomial, pow_succ' (x q) a, mul_assoc]

private theorem monomial_z (q : Aˣ) (a b d : ℕ) :
    z q * orderedMonomial q (a, b, d) =
      (↑(q⁻¹) : A) ^ a • orderedMonomial q (a, b + 1, d) := by
  change z q * (x q ^ a * z q ^ b * y q ^ d) = _ • (x q ^ a * z q ^ (b + 1) * y q ^ d)
  rw [← mul_assoc, ← mul_assoc, skew_mul_pow (zx q), smul_mul_assoc, smul_mul_assoc,
    mul_assoc (x q ^ a), ← pow_succ']

private theorem orderedMonomial_span (q : Aˣ) :
    Submodule.span A (Set.range (orderedMonomial q)) = ⊤ := by
  let M := Submodule.span A (Set.range (orderedMonomial q))
  have memMon (a b d : ℕ) : orderedMonomial q (a, b, d) ∈ M :=
    Submodule.subset_span ⟨(a, b, d), rfl⟩
  have extend (w : SerreAlgebra A q) (h : ∀ a b d, w * orderedMonomial q (a, b, d) ∈ M)
      (m : SerreAlgebra A q) (hm : m ∈ M) : w * m ∈ M := by
    have hle : M ≤ M.comap (LinearMap.mulLeft A w) := Submodule.span_le.mpr (by
      rintro _ ⟨⟨a, b, d⟩, rfl⟩
      exact h a b d)
    exact hle hm
  have hX := extend (x q) (fun a b d => (monomial_x q a b d) ▸ memMon (a + 1) b d)
  have hY := extend (y q) (by
    intro a b d
    induction a with
    | zero =>
      change y q * (x q ^ 0 * z q ^ b * y q ^ d) ∈ M
      rw [pow_zero, one_mul, ← mul_assoc, skew_mul_pow (yz q), smul_mul_assoc, mul_assoc,
        ← pow_succ']
      apply M.smul_mem
      simpa only [Specs.LieNotes.Quantum.SerreBasis.orderedMonomial, pow_zero, one_mul]
        using memMon 0 b (d + 1)
    | succ a ih =>
      rw [← monomial_x, ← mul_assoc, yx, sub_mul, smul_mul_assoc, smul_mul_assoc,
        mul_assoc, monomial_z]
      exact M.sub_mem (M.smul_mem _ (hX _ ih)) (M.smul_mem _ (M.smul_mem _ (memMon a (b + 1) d))))
  have hFree (a : FreeAlgebra A (Fin 2)) :
      ∀ m ∈ M, quotientMap q a * m ∈ M := by
    induction a using FreeAlgebra.induction with
    | grade0 r =>
      intro m hm
      rw [AlgHom.commutes, ← Algebra.smul_def]
      exact M.smul_mem r hm
    | grade1 i =>
      fin_cases i
      · exact hX
      · exact hY
    | mul a b ha hb =>
      intro m hm
      simpa only [map_mul, mul_assoc] using ha _ (hb _ hm)
    | add a b ha hb =>
      intro m hm
      simpa only [map_add, add_mul] using M.add_mem (ha _ hm) (hb _ hm)
  have hOne : (1 : SerreAlgebra A q) ∈ M := by
    simpa [Specs.LieNotes.Quantum.SerreBasis.orderedMonomial] using memMon 0 0 0
  apply top_unique
  intro v _
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective A (serreIdeal q).asIdeal v
  change quotientMap q a ∈ M
  simpa only [mul_one] using hFree a 1 hOne

/-- The ordered monomials x^a z^b y^d, including the unit, form an A-basis. -/
noncomputable def basis (q : Aˣ) : Module.Basis (ℕ × ℕ × ℕ) A (SerreAlgebra A q) :=
  Module.Basis.mk (orderedMonomial_independent q) (ge_of_eq (orderedMonomial_span q))

@[simp] theorem basis_apply (q : Aˣ) (i : ℕ × ℕ × ℕ) :
    basis q i = orderedMonomial q i :=
  Module.Basis.mk_apply _ _ _

@[simp] theorem basis_zero (q : Aˣ) : basis q (0, 0, 0) = 1 := by
  simp [Specs.LieNotes.Quantum.SerreBasis.orderedMonomial]

theorem basis_exists : Specs.LieNotes.Quantum.SerreBasis.basisProp.{u} :=
  fun q => ⟨basis q, basis_apply q⟩

end Basis

section BaseChange

variable {B : Type v} [CommRing B] [Algebra A B]

private abbrev mappedUnit (B : Type v) [CommRing B] [Algebra A B] (q : Aˣ) : Bˣ :=
  Units.map (algebraMap A B) q

private theorem serre_map_coefficients {C : Type*} [Ring C] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] (q : Aˣ) (a b : C) :
    serrePolynomial q a b = serrePolynomial (mappedUnit B q) a b := by
  have h : (↑(mappedUnit B q) + ↑((mappedUnit B q)⁻¹) : B) =
      algebraMap A B (↑q + ↑(q⁻¹) : A) := by
    rw [map_add]
    rfl
  simp only [Specs.LieNotes.Quantum.SerrePresentation.serrePolynomial, h, algebraMap_smul]

private noncomputable def baseChangeForward (q : Aˣ) :
    B ⊗[A] SerreAlgebra A q →ₐ[B] SerreAlgebra B (mappedUnit B q) := by
  let C := SerreAlgebra B (mappedUnit B q)
  letI : Algebra A C := Algebra.restrictScalars A B C
  letI : IsScalarTower A B C := IsScalarTower.restrictScalars A B C
  refine (AlgHom.liftEquiv A B (SerreAlgebra A q) C) ?_
  exact lift q (generator (mappedUnit B q))
    ((serre_map_coefficients (B := B) q _ _).trans (relationXY_zero _))
    ((serre_map_coefficients (B := B) q _ _).trans (relationYX_zero _))

@[simp] private theorem baseChangeForward_generator (q : Aˣ) (i : Fin 2) :
    baseChangeForward (B := B) q ((1 : B) ⊗ₜ[A] generator q i) =
      generator (mappedUnit B q) i := by
  simp only [baseChangeForward, AlgHom.liftEquiv_tmul, lift_generator, one_smul]

private abbrev tensorInclusion (q : Aˣ) :
    SerreAlgebra A q →ₐ[A] B ⊗[A] SerreAlgebra A q :=
  Algebra.TensorProduct.includeRight

private def tensorGenerator (q : Aˣ) (i : Fin 2) : B ⊗[A] SerreAlgebra A q :=
  tensorInclusion (B := B) q (generator q i)

private theorem tensorGenerator_serre (q : Aˣ) :
    serrePolynomial (mappedUnit B q) (tensorGenerator (B := B) q 0) (tensorGenerator (B := B) q 1) = 0 ∧
    serrePolynomial (mappedUnit B q) (tensorGenerator (B := B) q 1) (tensorGenerator (B := B) q 0) = 0 := by
  let inc := tensorInclusion (B := B) q
  have h (a b : SerreAlgebra A q) :
      serrePolynomial (mappedUnit B q) (inc a) (inc b) = inc (serrePolynomial q a b) := by
    rw [← serre_map_coefficients (B := B) q, map_serrePolynomial]
  exact ⟨(h (x q) (y q)).trans (by rw [relationXY_zero, map_zero]),
    (h (y q) (x q)).trans (by rw [relationYX_zero, map_zero])⟩

private noncomputable def baseChangeInverse (q : Aˣ) :
    SerreAlgebra B (mappedUnit B q) →ₐ[B] B ⊗[A] SerreAlgebra A q :=
  lift (mappedUnit B q) (tensorGenerator (B := B) q)
    (tensorGenerator_serre (B := B) q).1 (tensorGenerator_serre (B := B) q).2

@[simp] private theorem baseChangeInverse_generator (q : Aˣ) (i : Fin 2) :
    baseChangeInverse (B := B) q (generator (mappedUnit B q) i) = (1 : B) ⊗ₜ[A] generator q i :=
  lift_generator (mappedUnit B q) (tensorGenerator (B := B) q)
    (tensorGenerator_serre (B := B) q).1 (tensorGenerator_serre (B := B) q).2 i

/-- The canonical change of coefficients for the Serre presentation. -/
noncomputable def baseChange (q : Aˣ) :
    B ⊗[A] SerreAlgebra A q ≃ₐ[B] SerreAlgebra B (mappedUnit B q) :=
  AlgEquiv.ofAlgHom (baseChangeForward (B := B) q) (baseChangeInverse (B := B) q)
    (hom_ext (by
      intro i
      change baseChangeForward (B := B) q (baseChangeInverse (B := B) q (generator (mappedUnit B q) i)) = _
      rw [baseChangeInverse_generator, baseChangeForward_generator]
      rfl))
    (Algebra.TensorProduct.ext_ring (by
      apply hom_ext
      intro i
      change baseChangeInverse (B := B) q (baseChangeForward (B := B) q ((1 : B) ⊗ₜ[A] generator q i)) = _
      rw [baseChangeForward_generator, baseChangeInverse_generator]
      rfl))

@[simp] theorem baseChange_generator (q : Aˣ) (i : Fin 2) :
    baseChange (B := B) q ((1 : B) ⊗ₜ[A] generator q i) =
      generator (mappedUnit B q) i :=
  baseChangeForward_generator (B := B) q i

@[simp] theorem baseChange_z (q : Aˣ) :
    baseChange (B := B) q ((1 : B) ⊗ₜ[A] z q) = z (mappedUnit B q) := by
  let inc : SerreAlgebra A q →ₐ[A] B ⊗[A] SerreAlgebra A q := Algebra.TensorProduct.includeRight
  change baseChange (B := B) q (inc (z q)) = z (mappedUnit B q)
  have hx : baseChange (B := B) q (inc (x q)) = x (mappedUnit B q) := baseChange_generator (B := B) q 0
  have hy : baseChange (B := B) q (inc (y q)) = y (mappedUnit B q) := baseChange_generator (B := B) q 1
  simp only [Specs.LieNotes.Quantum.SerrePresentation.z, map_sub, map_mul]
  rw [map_smul, ← algebraMap_smul B (↑(q⁻¹) : A)]
  simp only [map_smul, map_mul, hx, hy]
  rfl

@[simp] theorem baseChange_monomial (q : Aˣ) (i : ℕ × ℕ × ℕ) :
    baseChange (B := B) q ((1 : B) ⊗ₜ[A] orderedMonomial q i) =
      orderedMonomial (mappedUnit B q) i := by
  let inc : SerreAlgebra A q →ₐ[A] B ⊗[A] SerreAlgebra A q := Algebra.TensorProduct.includeRight
  change baseChange (B := B) q (inc (orderedMonomial q i)) = orderedMonomial (mappedUnit B q) i
  have hx : baseChange (B := B) q (inc (x q)) = x (mappedUnit B q) := baseChange_generator (B := B) q 0
  have hy : baseChange (B := B) q (inc (y q)) = y (mappedUnit B q) := baseChange_generator (B := B) q 1
  have hz : baseChange (B := B) q (inc (z q)) = z (mappedUnit B q) := baseChange_z (B := B) q
  simp only [Specs.LieNotes.Quantum.SerreBasis.orderedMonomial, map_mul, map_pow, hx, hy, hz]

@[simp] theorem baseChange_basis (q : Aˣ) (i : ℕ × ℕ × ℕ) :
    baseChange (B := B) q ((basis q).baseChange B i) =
      basis (mappedUnit B q) i := by
  rw [Module.Basis.baseChange_apply, basis_apply, baseChange_monomial, basis_apply]

theorem baseChange_exists : Specs.LieNotes.Quantum.SerreBasis.baseChangeProp.{u,v} := by
  intro A _ B _ _ q
  exact ⟨baseChange (B := B) q, baseChange_generator (B := B) q,
    baseChange_z (B := B) q, baseChange_monomial (B := B) q,
    basis q, basis (mappedUnit B q), basis_apply q, basis_apply (mappedUnit B q),
    baseChange_basis (B := B) q⟩

/-- Scalar extension for the ordered presentation, via elimination of z on each side. -/
noncomputable def orderedBaseChange (q : Aˣ) :
    B ⊗[A] OrderedAlgebra A q ≃ₐ[B] OrderedAlgebra B (mappedUnit B q) :=
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) (orderedEquiv q)).trans
    (baseChange (B := B) q)).trans (orderedEquiv (mappedUnit B q)).symm

@[simp] theorem orderedBaseChange_generator (q : Aˣ) (i : Fin 3) :
    orderedBaseChange (B := B) q ((1 : B) ⊗ₜ[A] orderedGenerator q i) =
      orderedGenerator (mappedUnit B q) i := by
  apply (orderedEquiv (mappedUnit B q)).injective
  simp only [orderedBaseChange, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom]
  change baseChange (B := B) q ((1 : B) ⊗ₜ[A] toSerre q (orderedGenerator q i)) =
    toSerre (mappedUnit B q) (orderedGenerator (mappedUnit B q) i)
  rw [toSerre_generator, toSerre_generator]
  fin_cases i
  · exact baseChange_generator (B := B) q 0
  · exact baseChange_z (B := B) q
  · exact baseChange_generator (B := B) q 1

theorem orderedBaseChange_exists :
    Specs.LieNotes.Quantum.SerreBasis.orderedBaseChangeProp.{u,v} := by
  intro A _ B _ _ q
  exact ⟨orderedBaseChange (B := B) q, orderedBaseChange_generator (B := B) q⟩

end BaseChange

end LieNotes.Quantum.SerreBasis
