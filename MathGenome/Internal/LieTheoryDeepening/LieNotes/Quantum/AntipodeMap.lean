import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.AntipodeMap
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Presentation
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace LieNotes.Quantum.AntipodeMap

open LieNotes.Quantum.Presentation
open Specs.LieNotes.Quantum.AntipodeMap (GeneratorFormulas SquareFormulas)
open Specs.LieNotes.Quantum.SerrePresentation (serrePolynomial)
open MulOpposite

universe u v w

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

/-- The identities of the two Cartan coefficient choices used by the antipode. -/
structure CartanLaws (C : Cartan A T) : Prop where
  involutive : Function.Involutive C.kappa
  kappa_tau : ∀ i t, C.kappa (C.tau i t) = (C.tau i).symm (C.kappa t)
  kappa_K : ∀ i, C.kappa (↑(C.K i)) = ↑((C.K i)⁻¹)
  kappa_D : ∀ i, C.kappa (C.D i) = -C.D i
  scale : ∀ i l, C.tau i (↑(C.K l)) =
    (↑(C.q ^ cartanMatrix l i) : A) • (↑(C.K l) : T)

variable (C : Cartan A T)

private abbrev K (i : Root) : U C := cartan C (↑(C.K i))
private abbrev Ki (i : Root) : U C := cartan C (↑((C.K i)⁻¹))

private theorem cartan_comm (s t : T) :
    cartan C s * cartan C t = cartan C t * cartan C s := by
  rw [← map_mul, mul_comm s t, map_mul]

private theorem cartan_E (i : Root) (t : T) :
    cartan C t * E C i = E C i * cartan C (C.tau i t) := by
  rw [(relations C).eCartan, AlgEquiv.symm_apply_apply]

private theorem F_cartan (i : Root) (t : T) :
    F C i * cartan C t = cartan C (C.tau i t) * F C i := by
  rw [(relations C).cartanF, AlgEquiv.symm_apply_apply]

private theorem kappa_tau_symm (h : CartanLaws C) (i : Root) (t : T) :
    C.kappa ((C.tau i).symm t) = C.tau i (C.kappa t) := by
  apply (C.tau i).symm.injective
  rw [← h.kappa_tau, AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply]

private theorem scale_inv {f : T ≃ₐ[A] T} {p : Aˣ} {k : Tˣ}
    (h : f (k : T) = (p : A) • (k : T)) :
    f (↑k⁻¹ : T) = (↑p⁻¹ : A) • (↑k⁻¹ : T) := by
  have hu : Units.map f.toAlgHom.toMonoidHom k =
      Units.map (algebraMap A T).toMonoidHom p * k := by
    apply Units.ext
    change f (k : T) = algebraMap A T (p : A) * (k : T)
    simpa only [Algebra.smul_def] using h
  have hi := congrArg (fun z : Tˣ => ((z⁻¹ : Tˣ) : T)) hu
  simpa [Algebra.smul_def, mul_comm] using hi

private theorem scale_symm {f : T ≃ₐ[A] T} {p : Aˣ} {k : Tˣ}
    (h : f (k : T) = (p : A) • (k : T)) :
    f.symm (k : T) = (↑p⁻¹ : A) • (k : T) := by
  apply f.injective
  rw [AlgEquiv.apply_symm_apply, map_smul, h, ← mul_smul, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_smul]

private theorem E_Ki (h : CartanLaws C) (i l : Root) :
    E C i * Ki C l = (↑(C.q ^ cartanMatrix l i) : A) • (Ki C l * E C i) := by
  unfold Ki
  rw [(relations C).eCartan, scale_inv (scale_symm (h.scale i l)), inv_inv,
    map_smul, Algebra.smul_mul_assoc]

private theorem K_F (h : CartanLaws C) (i l : Root) :
    K C l * F C i = (↑((C.q ^ cartanMatrix l i)⁻¹) : A) • (F C i * K C l) := by
  unfold K
  rw [(relations C).cartanF, scale_symm (h.scale i l), map_smul, Algebra.mul_smul_comm]

private theorem F_Ki (h : CartanLaws C) (i l : Root) :
    F C i * Ki C l = (↑((C.q ^ cartanMatrix l i)⁻¹) : A) • (Ki C l * F C i) := by
  unfold Ki
  rw [F_cartan, scale_inv (h.scale i l), map_smul, Algebra.smul_mul_assoc]

private theorem K_E (h : CartanLaws C) (i l : Root) :
    K C l * E C i = (↑(C.q ^ cartanMatrix l i) : A) • (E C i * K C l) := by
  unfold K
  rw [cartan_E, h.scale i l, map_smul, Algebra.mul_smul_comm]

private theorem matrix_symm (i j : Root) : cartanMatrix i j = cartanMatrix j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · simp [Specs.LieNotes.Quantum.Presentation.cartanMatrix, hij, Ne.symm hij]

private def cartanImage : T →ₐ[A] (U C)ᵐᵒᵖ :=
  ((cartan C).comp C.kappa.toAlgHom).toOpposite fun s t =>
    cartan_comm C (C.kappa s) (C.kappa t)

private def eImage (i : Root) : (U C)ᵐᵒᵖ := op (-(Ki C i * E C i))
private def fImage (i : Root) : (U C)ᵐᵒᵖ := op (-(F C i * K C i))

private theorem mixedImage (h : CartanLaws C) (i j : Root) :
    (F C j * K C j) * (Ki C i * E C i) - (Ki C i * E C i) * (F C j * K C j) =
      cartan C (C.kappa (mixed C i j)) := by
  have hf : (F C j * K C j) * (Ki C i * E C i) =
      (Ki C i * (F C j * E C i)) * K C j := by
    calc
      _ = (F C j * Ki C i) * (K C j * E C i) := by
        change (F C j * cartan C _ ) * (cartan C _ * E C i) = _
        simp only [K, Ki, ← mul_assoc]
        rw [mul_assoc (F C j), cartan_comm C, ← mul_assoc]
      _ = _ := by
        rw [F_Ki C h, K_E C h, matrix_symm i j, Algebra.smul_mul_assoc,
          Algebra.mul_smul_comm, ← mul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_smul]
        simp only [mul_assoc]
  rw [hf, show (Ki C i * (F C j * E C i)) * K C j -
      (Ki C i * E C i) * (F C j * K C j) =
      -(Ki C i * (E C i * F C j - F C j * E C i) * K C j) by noncomm_ring,
    (relations C).comm]
  by_cases hij : i = j
  · subst j
    simp only [Specs.LieNotes.Quantum.Presentation.mixed, ite_true, h.kappa_D, map_neg]
    congr 1
    simp only [K, Ki, ← map_mul]
    congr 1
    rw [mul_comm (↑((C.K i)⁻¹) : T) (C.D i), mul_assoc, Units.inv_mul, mul_one]
  · simp [Specs.LieNotes.Quantum.Presentation.mixed, hij]

private theorem basicImages (h : CartanLaws C) :
    SatisfiesBasic C (cartanImage C) (eImage C) (fImage C) where
  cartanF t j := by
    apply unop_injective
    change -(F C j * K C j) * cartan C (C.kappa t) =
      cartan C (C.kappa ((C.tau j).symm t)) * -(F C j * K C j)
    rw [neg_mul, mul_neg, kappa_tau_symm C h, mul_assoc, cartan_comm C,
      ← mul_assoc, F_cartan, mul_assoc]
  eCartan i t := by
    apply unop_injective
    change cartan C (C.kappa t) * -(Ki C i * E C i) =
      -(Ki C i * E C i) * cartan C (C.kappa ((C.tau i).symm t))
    rw [mul_neg, neg_mul, kappa_tau_symm C h, ← mul_assoc, cartan_comm C,
      mul_assoc, cartan_E C i (C.kappa t), ← mul_assoc]
  comm i j := by
    apply unop_injective
    change -(F C j * K C j) * -(Ki C i * E C i) -
      -(Ki C i * E C i) * -(F C j * K C j) = cartan C (C.kappa (mixed C i j))
    simpa only [neg_mul_neg] using mixedImage C h i j

section Serre

variable {B : Type w} [Ring B] [Algebra A B]

/-- Moving the Cartan factors to the left crosses each pair of root letters once. -/
private theorem collectCartan (X L : Root → B) (p : Aˣ)
    (h : ∀ i j, X i * L j = (↑(p ^ cartanMatrix j i) : A) • (L j * X i)) (i j l : Root) :
    (L i * X i) * (L j * X j) * (L l * X l) =
      (↑(p ^ (cartanMatrix j i + cartanMatrix l i + cartanMatrix l j)) : A) •
        ((L i * L j * L l) * (X i * X j * X l)) := by
  have cross : X i * X j * L l =
      (↑(p ^ cartanMatrix l i) * ↑(p ^ cartanMatrix l j) : A) • (L l * (X i * X j)) := by
    rw [mul_assoc, h j l, Algebra.mul_smul_comm, ← mul_assoc, h i l,
      Algebra.smul_mul_assoc, smul_smul, mul_comm, mul_assoc]
  have pair : (L i * X i) * (L j * X j) =
      (↑(p ^ cartanMatrix j i) : A) • ((L i * L j) * (X i * X j)) := by
    rw [← mul_assoc (L i * X i), mul_assoc (L i), h i j, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, ← mul_assoc]
    simp only [mul_assoc]
  rw [pair, Algebra.smul_mul_assoc, ← mul_assoc ((L i * L j) * (X i * X j)),
    mul_assoc (L i * L j), cross, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    smul_smul, zpow_add, zpow_add, Units.val_mul, Units.val_mul]
  simp only [mul_assoc]

private theorem twistedSerre (q p : Aˣ) (X L : Root → B)
    (cross : ∀ i j, X i * L j = (↑(p ^ cartanMatrix j i) : A) • (L j * X i))
    (comm : ∀ i j, L i * L j = L j * L i) {i j : Root} (hij : i ≠ j)
    (hs : serrePolynomial q (X i) (X j) = 0) :
    serrePolynomial q (-(L i * X i)) (-(L j * X j)) = 0 := by
  have w₁ : cartanMatrix i i + cartanMatrix j i + cartanMatrix j i = 0 := by
    norm_num [Specs.LieNotes.Quantum.Presentation.cartanMatrix, Ne.symm hij]
  have w₂ : cartanMatrix j i + cartanMatrix i i + cartanMatrix i j = 0 := by
    norm_num [Specs.LieNotes.Quantum.Presentation.cartanMatrix, hij, Ne.symm hij]
  have w₃ : cartanMatrix i j + cartanMatrix i j + cartanMatrix i i = 0 := by
    norm_num [Specs.LieNotes.Quantum.Presentation.cartanMatrix, hij]
  have h₁ := collectCartan X L p cross i i j
  have h₂ := collectCartan X L p cross i j i
  have h₃ := collectCartan X L p cross j i i
  simp only [w₁, w₂, w₃, zpow_zero, Units.val_one, one_smul] at h₁ h₂ h₃
  have reorder : L i * L j * L i = L i * L i * L j := by
    rw [mul_assoc, comm j i, ← mul_assoc]
  rw [reorder] at h₂
  rw [comm j i, reorder] at h₃
  have negSerre (x y : B) : serrePolynomial q (-x) (-y) = -serrePolynomial q x y := by
    simp only [serrePolynomial, pow_two, mul_neg, neg_mul, neg_neg, smul_neg]
    abel
  rw [negSerre, neg_eq_zero]
  simp only [serrePolynomial, pow_two] at hs ⊢
  rw [← mul_assoc (L j * X j) (L i * X i), h₁, h₂, h₃,
    mul_assoc (X j) (X i) (X i), ← Algebra.mul_smul_comm, ← mul_sub, ← mul_add, hs, mul_zero]

private theorem serre_op (q : Aˣ) (a b : B) :
    (serrePolynomial q (op a) (op b)).unop = serrePolynomial q a b := by
  simp only [serrePolynomial, unop_add, unop_sub, unop_smul, unop_mul, unop_pow, unop_op]
  rw [mul_assoc a b a]
  abel

end Serre

private theorem serreImages (h : CartanLaws C) :
    SatisfiesSerre C.q (eImage C) (fImage C) where
  pos i j hij := by
    apply unop_injective
    rw [unop_zero, eImage, eImage, serre_op]
    exact twistedSerre C.q C.q (E C) (Ki C) (E_Ki C h)
      (fun i j => cartan_comm C _ _) hij ((serre_relations C).pos i j hij)
  neg i j hij := by
    have hs : serrePolynomial C.q (op (F C i)) (op (F C j)) = 0 := by
      apply unop_injective
      rw [serre_op, unop_zero]
      exact (serre_relations C).neg i j hij
    apply twistedSerre C.q C.q⁻¹ (fun i => op (F C i)) (fun i => op (K C i)) _ _ hij hs
    · intro i j
      apply unop_injective
      simpa only [unop_mul, unop_op, unop_smul, inv_zpow] using K_F C h i j
    · intro i j
      exact congrArg op (cartan_comm C (↑(C.K j)) (↑(C.K i)))

/-- The algebra map into the opposite algebra induced by the antipode formulas. -/
def antipode (h : CartanLaws C) : U C →ₐ[A] (U C)ᵐᵒᵖ :=
  liftU C (cartanImage C) (eImage C) (fImage C) (basicImages C h) (serreImages C h)

@[simp] theorem antipode_cartan (h : CartanLaws C) (t : T) :
    (antipode C h (cartan C t)).unop = cartan C (C.kappa t) :=
  congrArg unop (liftU_cartan C _ _ _ (basicImages C h) (serreImages C h) t)

@[simp] theorem antipode_E (h : CartanLaws C) (i : Root) :
    (antipode C h (E C i)).unop = -(Ki C i * E C i) :=
  congrArg unop (liftU_E C _ _ _ (basicImages C h) (serreImages C h) i)

@[simp] theorem antipode_F (h : CartanLaws C) (i : Root) :
    (antipode C h (F C i)).unop = -(F C i * K C i) :=
  congrArg unop (liftU_F C _ _ _ (basicImages C h) (serreImages C h) i)

theorem antipode_formulas (h : CartanLaws C) : GeneratorFormulas C (antipode C h) :=
  ⟨antipode_cartan C h, antipode_E C h, antipode_F C h⟩

@[simp] theorem antipode_K (h : CartanLaws C) (i : Root) :
    (antipode C h (K C i)).unop = Ki C i := by
  simp only [K, Ki, antipode_cartan, h.kappa_K]

theorem antipode_unique (h : CartanLaws C) {S : U C →ₐ[A] (U C)ᵐᵒᵖ}
    (hS : GeneratorFormulas C S) : S = antipode C h := by
  obtain ⟨ht, he, hf⟩ := hS
  apply hom_ext C
  · intro t
    exact unop_injective ((ht t).trans (antipode_cartan C h t).symm)
  · intro i
    exact unop_injective ((he i).trans (antipode_E C h i).symm)
  · intro i
    exact unop_injective ((hf i).trans (antipode_F C h i).symm)

private theorem Ki_K (i : Root) : Ki C i * K C i = 1 := by
  simp only [Ki, K, ← map_mul, Units.inv_mul, map_one]

theorem antipode_square (h : CartanLaws C) : SquareFormulas C (antipode C h) := by
  have hi (i : Root) : C.kappa (↑((C.K i)⁻¹)) = (↑(C.K i) : T) := by
    rw [← h.kappa_K, h.involutive]
  have diag (i : Root) : cartanMatrix i i = 2 := by
    simp [Specs.LieNotes.Quantum.Presentation.cartanMatrix]
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rw [antipode_cartan, antipode_cartan, h.involutive]
  · intro i
    have hE : E C i * K C i = (↑(C.q ^ (-2 : ℤ)) : A) • (K C i * E C i) := by
      unfold K
      rw [(relations C).eCartan, scale_symm (h.scale i i), map_smul, Algebra.smul_mul_assoc,
        diag, ← zpow_neg]
    simp only [antipode_E, map_neg, unop_neg, map_mul, unop_mul, antipode_cartan, hi,
      neg_mul, neg_neg]
    rw [mul_assoc, hE, Algebra.mul_smul_comm, ← mul_assoc, Ki_K, one_mul]
  · intro i
    have hF : Ki C i * F C i = (↑(C.q ^ (2 : ℤ)) : A) • (F C i * Ki C i) := by
      unfold Ki
      rw [(relations C).cartanF, scale_inv (scale_symm (h.scale i i)), inv_inv, map_smul,
        Algebra.mul_smul_comm, diag]
    simp only [antipode_F, map_neg, unop_neg, map_mul, unop_mul, antipode_K, mul_neg, neg_neg]
    rw [← mul_assoc, hF, Algebra.smul_mul_assoc, mul_assoc, Ki_K, mul_one]

private theorem serre_smul {B : Type w} [Ring B] [Algebra A B]
    (q : Aˣ) (r s : A) (x y : B) :
    serrePolynomial q (r • x) (s • y) = (r * r * s) • serrePolynomial q x y := by
  simp only [serrePolynomial, pow_two, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_smul, smul_add, smul_sub, mul_assoc, mul_left_comm, mul_comm]

private theorem scaleBasic (a : Aˣ) :
    SatisfiesBasic C (cartan C) (fun i => (a : A) • E C i)
      (fun i => (↑a⁻¹ : A) • F C i) where
  cartanF t i := by
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, (relations C).cartanF]
  eCartan i t := by
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, (relations C).eCartan]
  comm i j := by
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, ← Units.val_mul,
      mul_inv_cancel, inv_mul_cancel, Units.val_one, one_smul, (relations C).comm]

private theorem scaleSerre (a : Aˣ) :
    SatisfiesSerre C.q (fun i => (a : A) • E C i) (fun i => (↑a⁻¹ : A) • F C i) where
  pos i j hij := by rw [serre_smul, (serre_relations C).pos i j hij, smul_zero]
  neg i j hij := by rw [serre_smul, (serre_relations C).neg i j hij, smul_zero]

/-- Scaling all positive root generators by a unit and the negative ones by its inverse. -/
private def scaleRoots (a : Aˣ) : U C →ₐ[A] U C :=
  liftU C (cartan C) _ _ (scaleBasic C a) (scaleSerre C a)

@[simp] private theorem scaleRoots_cartan (a : Aˣ) (t : T) :
    scaleRoots C a (cartan C t) = cartan C t :=
  liftU_cartan C (cartan C) _ _ (scaleBasic C a) (scaleSerre C a) t

@[simp] private theorem scaleRoots_E (a : Aˣ) (i : Root) :
    scaleRoots C a (E C i) = (a : A) • E C i :=
  liftU_E C (cartan C) _ _ (scaleBasic C a) (scaleSerre C a) i

@[simp] private theorem scaleRoots_F (a : Aˣ) (i : Root) :
    scaleRoots C a (F C i) = (↑a⁻¹ : A) • F C i :=
  liftU_F C (cartan C) _ _ (scaleBasic C a) (scaleSerre C a) i

private theorem scaleRoots_inverse (a : Aˣ) :
    (scaleRoots C a⁻¹).comp (scaleRoots C a) = AlgHom.id A (U C) := by
  apply hom_ext C <;> intro x <;>
    simp only [AlgHom.comp_apply, AlgHom.id_apply, scaleRoots_cartan, scaleRoots_E,
      scaleRoots_F, map_smul, smul_smul, inv_inv, ← Units.val_mul, mul_inv_cancel,
      inv_mul_cancel, Units.val_one, one_smul]

private theorem scaleRoots_bijective (a : Aˣ) : Function.Bijective (scaleRoots C a) := by
  let g := scaleRoots C a⁻¹
  have left : Function.LeftInverse g (scaleRoots C a) := fun x =>
    DFunLike.congr_fun (scaleRoots_inverse C a) x
  have right : Function.RightInverse g (scaleRoots C a) := fun x => by
    have h := scaleRoots_inverse C a⁻¹
    rw [inv_inv] at h
    exact DFunLike.congr_fun h x
  exact ⟨left.injective, right.surjective⟩

theorem antipode_bijective (h : CartanLaws C) : Function.Bijective (antipode C h) := by
  let S := antipode C h
  let S₂ := (AlgHom.opComm S).comp S
  obtain ⟨ht, he, hf⟩ := antipode_square C h
  have eq_scale : S₂ = scaleRoots C (C.q ^ (-2 : ℤ)) := by
    apply hom_ext C
    · intro t
      rw [scaleRoots_cartan]
      exact ht t
    · intro i
      rw [scaleRoots_E]
      exact he i
    · intro i
      rw [scaleRoots_F, ← zpow_neg]
      exact hf i
  have hb : Function.Bijective S₂ := eq_scale ▸ scaleRoots_bijective C (C.q ^ (-2 : ℤ))
  constructor
  · intro x y hxy
    apply hb.injective
    exact congrArg (AlgHom.opComm S) hxy
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective y.unop
    exact ⟨(S x).unop, unop_injective hx⟩

section Concrete

open Specs.LieNotes.Quantum.Presentation (exponentialUnit polynomialKappa)
open LieNotes.Quantum.Truncations (cartanTruncate)

variable {k : Type u} [Field k] [CharZero k]

theorem genericCartanLaws (q : kˣ) (hq : (q : k)^2 ≠ 1) : CartanLaws (generic q hq) where
  involutive := generic_kappa_involutive q hq
  kappa_tau := generic_kappa_tau q hq
  kappa_K := generic_kappa_K q hq
  kappa_D := generic_kappa_D q hq
  scale := generic_scale q hq

private theorem truncated_kappa_K (N : ℕ) (i : Root) :
    (truncated k N).kappa (↑((truncated k N).K i)) = ↑(((truncated k N).K i)⁻¹) := by
  let g := polynomialKappa (Truncations.A k N)
  let f := polynomialKappa k
  let x := (MvPolynomial.X i : PolynomialCartan k)
  let tr := cartanTruncate (R := k) Root N
  have hneg : exponentialUnit (-x) = (exponentialUnit x)⁻¹ :=
    map_inv (exponentialHom (PolynomialCartan k)) (Multiplicative.ofAdd x)
  change g.toAlgHom (tr (↑(exponentialUnit x))) =
    (↑((Units.map tr.toMonoidHom (exponentialUnit x))⁻¹) : TruncatedCartan k N)
  rw [← map_inv, ← hneg, Units.coe_map, exponentialUnit_val, exponentialUnit_val,
    cartanTruncate_map N f.toAlgHom g.toAlgHom, Truncations.map_expH]
  · change tr (Truncations.expH (f x)) = tr (Truncations.expH (-x))
    rw [show f x = -x from polynomialKappa_X _ _]
  · intro j
    simp [f, g]

theorem truncatedCartanLaws (N : ℕ) : CartanLaws (truncated k N) where
  involutive := truncated_kappa_involutive N
  kappa_tau := truncated_kappa_tau N
  kappa_K := truncated_kappa_K N
  kappa_D := truncated_kappa_D N
  scale := truncated_scale N

/-- The antipode of the fixed-parameter presentation. -/
abbrev genericAntipode (q : kˣ) (hq : (q : k)^2 ≠ 1) :=
  antipode (generic q hq) (genericCartanLaws q hq)

/-- The antipode of the presentation over the rational function field. -/
abbrev indeterminateAntipode (k : Type u) [Field k] [CharZero k] :=
  genericAntipode (rationalQ k) (Specs.LieNotes.Quantum.Presentation.rationalQ_sq_ne k)

/-- The antipode of the formal presentation at level N. -/
abbrev truncatedAntipode (k : Type u) [Field k] [CharZero k] (N : ℕ) :=
  antipode (truncated k N) (truncatedCartanLaws N)

@[simp] theorem truncatedAntipode_H (N : ℕ) (i : Root) :
    (truncatedAntipode k N (cartan (truncated k N) (MvPolynomial.X i))).unop =
      -(cartan (truncated k N) (MvPolynomial.X i)) := by
  rw [antipode_cartan, truncated_kappa_H, map_neg]

theorem genericAntipode_spec : Specs.LieNotes.Quantum.AntipodeMap.genericAntipodeProp := by
  intro k _ _ q hq
  let C := generic q hq
  let h := genericCartanLaws q hq
  exact ⟨genericAntipode q hq,
    ⟨antipode_formulas C h, antipode_square C h, antipode_bijective C h, antipode_K C h⟩,
    fun _ hw => antipode_unique C h hw.1⟩

theorem indeterminateAntipode_spec :
    Specs.LieNotes.Quantum.AntipodeMap.indeterminateAntipodeProp := by
  intro k _ _
  exact genericAntipode_spec (rationalQ k)
    (Specs.LieNotes.Quantum.Presentation.rationalQ_sq_ne k)

theorem truncatedAntipode_spec : Specs.LieNotes.Quantum.AntipodeMap.truncatedAntipodeProp := by
  intro k _ _ N
  let C := truncated k N
  let h := truncatedCartanLaws (k := k) N
  exact ⟨truncatedAntipode k N, ⟨antipode_formulas C h, antipode_square C h,
    antipode_bijective C h, truncatedAntipode_H N, antipode_K C h⟩,
    fun _ hw => antipode_unique C h hw.1⟩

end Concrete

section Reduction

variable {k : Type u} [Field k] [CharZero k] {M N : ℕ}

private theorem cartanReduce_kappa (e : M ≤ N) (t : TruncatedCartan k N) :
    cartanReduce e ((truncated k N).kappa t) =
      (truncated k M).kappa (cartanReduce e t) := by
  let r := cartanReduce (k := k) e
  let κN := (truncated k N).kappa.toAlgHom
  let κM := (truncated k M).kappa.toAlgHom
  have eq_comp : r.comp κN.toRingHom = κM.toRingHom.comp r := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change r (κN (MvPolynomial.C a)) = κM (r (MvPolynomial.C a))
      change r (κN (algebraMap _ _ a)) = κM (r (algebraMap _ _ a))
      rw [κN.commutes]
      change r (MvPolynomial.C a) = κM (r (MvPolynomial.C a))
      rw [show r (MvPolynomial.C a) = MvPolynomial.C (Truncations.reduce e a) from
        MvPolynomial.map_C _ _]
      exact (κM.commutes _).symm
    · intro i
      change r ((truncated k N).kappa (MvPolynomial.X i)) =
        (truncated k M).kappa (r (MvPolynomial.X i))
      rw [truncated_kappa_H, map_neg, show r (MvPolynomial.X i) = MvPolynomial.X i from
        MvPolynomial.map_X _ _, truncated_kappa_H]
  exact DFunLike.congr_fun eq_comp t

private theorem reduce_Ki (e : M ≤ N) (i : Root) :
    reduce e (Ki (truncated k N) i) = Ki (truncated k M) i := by
  have hK : Units.map (cartanReduce (k := k) e).toMonoidHom ((truncated k N).K i) =
      (truncated k M).K i :=
    Units.ext (Specs.LieNotes.Quantum.Presentation.cartanReduce_K e i)
  have hinv := congrArg (fun u : (TruncatedCartan k M)ˣ => (↑u⁻¹ : TruncatedCartan k M)) hK
  rw [Ki, Ki, reduce_cartan]
  exact congrArg (cartan (truncated k M)) hinv

theorem reduceAntipode_spec : Specs.LieNotes.Quantum.AntipodeMap.reduceAntipodeProp := by
  intro k _ _ M N e SN SM hN hM x
  obtain ⟨htN, heN, hfN⟩ := hN
  obtain ⟨htM, heM, hfM⟩ := hM
  let CN := truncated k N
  let CM := truncated k M
  have comp_eq : (RingHom.op (reduce e)).comp SN.toRingHom = SM.toRingHom.comp (reduce e) := by
    apply ringHom_ext CN
    · intro a
      apply unop_injective
      change reduce e (SN (algebraMap (Truncations.A k N) (Uₙ k N) a)).unop =
        (SM (reduce e (algebraMap (Truncations.A k N) (Uₙ k N) a))).unop
      rw [SN.commutes, MulOpposite.algebraMap_apply, unop_op, reduce_scalar,
        SM.commutes, MulOpposite.algebraMap_apply, unop_op]
    · intro t
      apply unop_injective
      change reduce e (SN (cartan CN t)).unop = (SM (reduce e (cartan CN t))).unop
      rw [htN, reduce_cartan, reduce_cartan, htM, cartanReduce_kappa]
    · intro i
      apply unop_injective
      change reduce e (SN (E CN i)).unop = (SM (reduce e (E CN i))).unop
      rw [heN, reduce_E, heM, map_neg, map_mul, reduce_E]
      exact congrArg (fun t => -(t * E CM i)) (reduce_Ki e i)
    · intro i
      apply unop_injective
      change reduce e (SN (F CN i)).unop = (SM (reduce e (F CN i))).unop
      rw [hfN, reduce_F, hfM, map_neg, map_mul, reduce_F, reduce_K]
  exact congrArg unop (DFunLike.congr_fun comp_eq x)

theorem reduce_truncatedAntipode (e : M ≤ N) (x : Uₙ k N) :
    reduce e (truncatedAntipode k N x).unop = (truncatedAntipode k M (reduce e x)).unop :=
  reduceAntipode_spec e (truncatedAntipode k N) (truncatedAntipode k M)
    (antipode_formulas _ _) (antipode_formulas _ _) x

end Reduction

end LieNotes.Quantum.AntipodeMap
