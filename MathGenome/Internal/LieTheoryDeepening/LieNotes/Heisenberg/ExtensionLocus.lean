import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.ExtensionLocus
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.NormalizedObstruction
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.DeformationTransport
import Batteries.Tactic.OpenPrivate

noncomputable section

open scoped TensorProduct

namespace LieNotes.Heisenberg.ExtensionLocus

open Specs.LieNotes.Heisenberg (ModelValue)
open Specs.LieNotes.Heisenberg.ExtensionLocus
open Specs.LieNotes.Heisenberg.NormalizedObstruction (IsLieBracket cyclicJacobiator)
open Specs.LieNotes.Heisenberg.DeformationTransport (Carrier LieBracket tensorCoordinates)

universe u

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

private theorem skew_of_alt {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (B : V →ₗ[R] V →ₗ[R] W) (hB : ∀ x, B x x = 0) (x y : V) :
    B y x = -B x y := by
  have h := hB (x + y)
  simp only [map_add, LinearMap.add_apply, hB, add_zero, zero_add] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem coordinateBracket_apply
    (B : (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k))
    (p q : Carrier A) :
    coordinateBracket B p q =
      tensorCoordinates (B (tensorCoordinates.symm p) (tensorCoordinates.symm q)) :=
  rfl

private def toCoordinateLieBracket
    {B : (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k)}
    (h : IsLieBracket B) : LieBracket A where
  bracket := coordinateBracket B
  alternating := by simp [coordinateBracket_apply, h.1]
  jacobi := by
    intro p q r
    let E := tensorCoordinates (k := k) (A := A)
    simp only [coordinateBracket_apply, LinearEquiv.symm_apply_apply]
    rw [← map_add, ← map_add]
    apply (map_eq_zero_iff E E.injective).2
    change B (E.symm p) (B (E.symm q) (E.symm r)) +
      B (E.symm q) (B (E.symm r) (E.symm p)) +
      B (E.symm r) (B (E.symm p) (E.symm q)) = 0
    have hj := congrArg Neg.neg (h.2 (E.symm q) (E.symm r) (E.symm p))
    simp only [cyclicJacobiator, neg_add, neg_zero] at hj
    have skew := skew_of_alt B h.1
    exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) (skew _ _) (skew _ _)) (skew _ _)).trans hj

open scoped Polynomial PowerSeries
open AdvancedHomologicalAlgebra.CE
open _root_.LieAlgebrasAndRepresentations.AbelianExtensions
open _root_.LieAlgebrasAndRepresentations.InfinitesimalDeformations
open _root_.LieAlgebrasAndRepresentations.DeformationObstructions (originalBracket originalBracket_apply)
open LieModule.Cohomology

open Specs.LieNotes.Heisenberg.NormalizedObstruction (Cochain normalized bracket)
open Specs.LieNotes.Heisenberg.DeformationTransport (reduce constantVector)

open private normalized_cocycle normalized_apply bracket_alt truncated_cube extend_tmul
  from MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.NormalizedObstruction
open private truncatedReduction_parameter formalReduction_parameter formalReduction_constant
  from MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.DeformationTransport

private abbrev normal (p : Fin 5 → k) : Cochain k :=
  normalized (p 0) (p 1) (p 2) (p 3) (p 4)

private def normalModel [CharZero k] (p : Fin 5 → k) : Deformation k (ModelValue k) :=
  model ⟨normal p, normalized_cocycle _ _ _ _ _⟩

omit [Algebra k A] in
private theorem reduce_add (ρ : A →+* DualNumber k) (p q : Carrier A) :
    reduce ρ (p + q) = reduce ρ p + reduce ρ q := by
  apply Prod.ext <;> apply ModelValue.ext <;> funext i <;> simp [reduce, Specs.LieNotes.Heisenberg.coords_add]

private theorem coordinates_scalar_tmul (s : A) (x : ModelValue k) :
    tensorCoordinates (s ⊗ₜ[k] x) = s • constantVector (algebraMap k A) x :=
  (DeformationTransport.scalarExtension k A 0 s x).1

private theorem reduce_tmul (ρ : A →+* DualNumber k)
    (hρ : ∀ a, ρ (algebraMap k A a) = TrivSqZeroExt.inl a) (s : A) (x : ModelValue k) :
    reduce ρ (tensorCoordinates (s ⊗ₜ[k] x)) =
      dualSMul k (ModelValue k) (ρ s) (x, 0) := by
  rw [coordinates_scalar_tmul]
  apply Prod.ext <;> apply ModelValue.ext <;> funext i
  · change (ρ (s * algebraMap k A (x.coords i))).fst = (ρ s).fst * x.coords i
    rw [map_mul, hρ]
    rfl
  · change (ρ (s * algebraMap k A (x.coords i))).snd =
      (ρ s).fst * 0 + (ρ s).snd * x.coords i
    rw [map_mul, hρ, DualNumber.snd_mul]
    rfl

private theorem coordinateBracket_tmul (t s r : A) (p : Fin 5 → k)
    (ψ : Cochain k) (x y : ModelValue k) :
    coordinateBracket (bracket t (p 0) (p 1) (p 2) (p 3) (p 4) ψ)
        (tensorCoordinates (s ⊗ₜ[k] x)) (tensorCoordinates (r ⊗ₜ[k] y)) =
      tensorCoordinates ((s * r) ⊗ₜ[k] ⁅x,y⁆ + (t * (s * r)) ⊗ₜ[k] normal p x y +
        (t ^ 2 * (s * r)) ⊗ₜ[k] ψ x y) := by
  simp only [coordinateBracket_apply, LinearEquiv.symm_apply_apply, bracket,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [extend_tmul originalBracket s r x y, extend_tmul (normal p) s r x y,
    extend_tmul ψ s r x y, originalBracket_apply]
  rfl

private theorem zero_cochain (x y : ModelValue k) : (0 : Cochain k) x y = 0 := rfl

private theorem reduce_linearBracket [CharZero k] (ρ : A →+* DualNumber k) (t : A)
    (hρ : ∀ a, ρ (algebraMap k A a) = TrivSqZeroExt.inl a) (ht : ρ t = DualNumber.eps)
    (p : Fin 5 → k) (x y : Carrier A) :
    reduce ρ (coordinateBracket (linearBracket t p) x y) =
      bracketFormula (normal p) (reduce ρ x) (reduce ρ y) := by
  let E := tensorCoordinates (k := k) (A := A)
  let B := coordinateBracket (linearBracket t p)
  let F := (normalModel p).bracket
  change reduce ρ (B x y) = F (reduce ρ x) (reduce ρ y)
  obtain ⟨x, rfl⟩ := E.surjective x
  obtain ⟨y, rfl⟩ := E.surjective y
  have hpure (s r : A) (x y : ModelValue k) :
      reduce ρ (B (E (s ⊗ₜ[k] x)) (E (r ⊗ₜ[k] y))) =
        F (reduce ρ (E (s ⊗ₜ[k] x))) (reduce ρ (E (r ⊗ₜ[k] y))) := by
    dsimp only [B, E]
    rw [coordinateBracket_tmul]
    simp only [zero_cochain, TensorProduct.tmul_zero, add_zero,
      map_add, reduce_add, reduce_tmul ρ hρ, map_mul, ht]
    rw [(normalModel p).scalar_left, (normalModel p).scalar_right]
    change dualSMul k _ (ρ s * ρ r) (⁅x,y⁆, 0) +
      dualSMul k _ (DualNumber.eps * (ρ s * ρ r)) (normal p x y, 0) =
        dualSMul k _ (ρ s) (dualSMul k _ (ρ r) (bracketFormula (normal p) (x, 0) (y, 0)))
    apply Prod.ext <;> apply ModelValue.ext <;> funext i <;>
      simp [bracketFormula, twistedBracket, dualSMul, TrivSqZeroExt.fst_mul,
        Specs.LieNotes.Heisenberg.coords_add, Specs.LieNotes.Heisenberg.coords_smul] <;> ring
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ =>
    simpa only [map_add, LinearMap.add_apply, reduce_add] using congrArg₂ (· + ·) h₁ h₂
  | tmul s x =>
    induction y using TensorProduct.inductionOn with
    | tmul r y => exact hpure s r x y
    | add y₁ y₂ h₁ h₂ =>
      simpa only [map_add, LinearMap.add_apply, reduce_add] using congrArg₂ (· + ·) h₁ h₂


open Specs.LieNotes.Heisenberg (basisValue xValue yValue zValue)
open Specs.LieNotes.Heisenberg.DeformationTransport
  (Truncated truncatedParameter truncatedReduction formalReduction ReducesTo)
open private makeTwo makeTwo_values from MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.AdjointCohomology

private theorem ascending_pair {i j : Fin 3} (hij : i < j) :
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;> first | decide | exact (False.elim ((by decide : ¬ (_ < _)) hij))

private theorem alternating_ext {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (b : Module.Basis (Fin 3) R V) {B C : V →ₗ[R] V →ₗ[R] W}
    (hB : ∀ x, B x x = 0) (hC : ∀ x, C x x = 0)
    (h : ∀ i j : Fin 3, i < j → B (b i) (b j) = C (b i) (b j)) : B = C := by
  apply LinearMap.ext_basis b b
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact h i j hij
  · rw [hB, hC]
  · rw [skew_of_alt B hB (b j) (b i), skew_of_alt C hC (b j) (b i), h j i hji]

private theorem isLieBracket_of_coordinates
    {B : (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k)}
    (C : LieBracket A) (hC : C.bracket = coordinateBracket B) : IsLieBracket B := by
  let E := tensorCoordinates (k := k) (A := A)
  have h (x y : A ⊗[k] ModelValue k) : C.bracket (E x) (E y) = E (B x y) := by
    rw [hC, coordinateBracket_apply]
    simp [E]
  have halt (x : A ⊗[k] ModelValue k) : B x x = 0 := by
    apply E.injective
    rw [← h, map_zero, C.alternating]
  refine ⟨halt, fun x y z => ?_⟩
  have hj := C.jacobi (E z) (E x) (E y)
  simp only [h, ← map_add] at hj
  have hj' : B z (B x y) + B x (B y z) + B y (B z x) = 0 :=
    (map_eq_zero_iff E E.injective).1 hj
  have hjneg := congrArg Neg.neg hj'
  simp only [neg_add, neg_zero, skew_of_alt B halt (B x y) z,
    skew_of_alt B halt (B y z) x, skew_of_alt B halt (B z x) y, neg_neg] at hjneg
  exact hjneg

/-- A coefficient with zero first-order reduction is a scalar multiple of (t^2). -/
private theorem truncated_kernel (a : Truncated k) (ha : truncatedReduction k a = 0) :
    ∃ s : k, a = truncatedParameter k ^ 2 * algebraMap k (Truncated k) s := by
  obtain ⟨w, rfl⟩ := ((DeformationTransport.modTwoReductions k).2.1 a).mp ha
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective w
  obtain ⟨r, hr⟩ := (Polynomial.X_dvd_sub_C (p := q))
  refine ⟨q.coeff 0, ?_⟩
  let X : Polynomial k := Polynomial.X
  let m := AdjoinRoot.mk (X ^ 3)
  have hh : m q - algebraMap k (Truncated k) (q.coeff 0) = truncatedParameter k * m r := by
    change m q - m (Polynomial.C (q.coeff 0)) = m X * m r
    rw [← map_sub, hr, map_mul]
  change truncatedParameter k ^ 2 * m q = truncatedParameter k ^ 2 * algebraMap k (Truncated k) (q.coeff 0)
  rw [← sub_eq_zero, ← mul_sub, hh, ← mul_assoc, ← pow_succ]
  have hcube : truncatedParameter k ^ 3 = 0 := truncated_cube
  rw [hcube, zero_mul]

private theorem reduce_truncated_linear [CharZero k] (p : Fin 5 → k)
    (x y : Carrier (Truncated k)) :
    reduce (truncatedReduction k).toRingHom (coordinateBracket (linearBracket (truncatedParameter k) p) x y) =
      bracketFormula (normal p) (reduce (truncatedReduction k).toRingHom x)
        (reduce (truncatedReduction k).toRingHom y) :=
  reduce_linearBracket (truncatedReduction k).toRingHom (truncatedParameter k)
    (truncatedReduction k).commutes truncatedReduction_parameter p x y

private theorem truncated_difference [CharZero k] (p : Fin 5 → k)
    (B : LieBracket (Truncated k)) (hB : ReducesTo (truncatedReduction k).toRingHom B (normal p))
    (x y : Carrier (Truncated k)) :
    ∃ w : ModelValue k,
      B.bracket x y = coordinateBracket (linearBracket (truncatedParameter k) p) x y +
        tensorCoordinates ((truncatedParameter k ^ 2) ⊗ₜ[k] w) := by
  let C := coordinateBracket (linearBracket (truncatedParameter k) p)
  have hred := (hB x y).trans (reduce_truncated_linear p x y).symm
  have hzero (i : Fin 3) : truncatedReduction k (B.bracket x y i - C x y i) = 0 := by
    rw [map_sub, sub_eq_zero]
    apply TrivSqZeroExt.ext
    · exact congrArg (fun v : ModelValue k × ModelValue k => v.1.coords i) hred
    · exact congrArg (fun v : ModelValue k × ModelValue k => v.2.coords i) hred
  choose w hw using fun i => truncated_kernel _ (hzero i)
  refine ⟨⟨w⟩, ?_⟩
  rw [coordinates_scalar_tmul]
  funext i
  exact (sub_eq_iff_eq_add.mp (hw i)).trans (add_comm _ _)

private theorem truncated_normalized_iff [CharZero k] (p : Fin 5 → k) :
    (∃ B : LieBracket (Truncated k), ReducesTo (truncatedReduction k).toRingHom B (normal p)) ↔
      Locus p := by
  let t := truncatedParameter k
  let E := tensorCoordinates (k := k) (A := Truncated k)
  let b := basisValue k
  let v := (b.baseChange (Truncated k)).map E
  have hv (i : Fin 3) : v i = E (1 ⊗ₜ[k] b i) := by
    simp only [v, Module.Basis.map_apply, Module.Basis.baseChange_apply]
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨w01, h01⟩ := truncated_difference p B hB (v 0) (v 1)
    obtain ⟨w02, h02⟩ := truncated_difference p B hB (v 0) (v 2)
    obtain ⟨w12, h12⟩ := truncated_difference p B hB (v 1) (v 2)
    -- The three quadratic coefficients determine the whole alternating cochain.
    let ψ := exteriorCochain (makeTwo b w01 w02 w12)
    have hψ : ψ (b 0) (b 1) = w01 ∧ ψ (b 0) (b 2) = w02 ∧ ψ (b 1) (b 2) = w12 :=
      makeTwo_values b w01 w02 w12
    have hterm (i j : Fin 3) :
        coordinateBracket (bracket t (p 0) (p 1) (p 2) (p 3) (p 4) ψ) (v i) (v j) =
          coordinateBracket (linearBracket t p) (v i) (v j) +
            E ((t ^ 2) ⊗ₜ[k] ψ (b i) (b j)) := by
      rw [hv, hv, coordinateBracket_tmul, coordinateBracket_tmul]
      simp only [mul_one, zero_cochain, TensorProduct.tmul_zero,
        add_zero, map_add]
      rfl
    have heq : B.bracket = coordinateBracket (bracket t (p 0) (p 1) (p 2) (p 3) (p 4) ψ) := by
      apply alternating_ext v B.alternating
      · intro x
        rw [coordinateBracket_apply, bracket_alt, map_zero]
      · intro i j hij
        rw [hterm]
        rcases ascending_pair hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hψ.1]; exact h01
        · rw [hψ.2.1]; exact h02
        · rw [hψ.2.2]; exact h12
    apply (NormalizedObstruction.extension_iff k (p 0) (p 1) (p 2) (p 3) (p 4)).1
    exact ⟨ψ, isLieBracket_of_coordinates B heq⟩
  · intro h
    have hl := NormalizedObstruction.linear_bracket k (Truncated k) t
      (p 0) (p 1) (p 2) (p 3) (p 4) h
    exact ⟨toCoordinateLieBracket hl, reduce_truncated_linear p⟩

theorem normalized_extension : NormalizedExtensionType := by
  intro k _ _ p
  refine ⟨truncated_normalized_iff p, fun hp => ?_⟩
  obtain ⟨hpoly, hformal⟩ := NormalizedObstruction.polynomial_formal k
    (p 0) (p 1) (p 2) (p 3) (p 4) hp
  refine ⟨hpoly, hformal, toCoordinateLieBracket hformal, rfl, ?_⟩
  intro x y
  exact reduce_linearBracket (formalReduction k) (PowerSeries.X : k⟦X⟧)
    formalReduction_constant formalReduction_parameter p x y


open Specs.LieNotes.Heisenberg (basisLieEquivValue)
open Specs.LieNotes.Heisenberg.AdjointCohomology
  (HeisenbergBasis HasNormalValues Cochains Cycles H2 d)
open Specs.LieNotes.Heisenberg.DeformationTransport (pullbackValue)

universe v

variable {L : Type v} [LieRing L] [LieAlgebra k L]

private abbrev basisIdentification (b : Module.Basis (Fin 3) k L) (hb : HeisenbergBasis b) :=
  basisLieEquivValue b hb.1 hb.2.1 hb.2.2

private theorem normal_pairs (p : Fin 5 → k) :
    normal p (basisValue k 0) (basisValue k 1) = 0 ∧
    normal p (basisValue k 0) (basisValue k 2) =
      p 0 • basisValue k 0 + p 1 • basisValue k 1 + p 2 • basisValue k 2 ∧
    normal p (basisValue k 1) (basisValue k 2) =
      p 3 • basisValue k 0 - p 0 • basisValue k 1 + p 4 • basisValue k 2 := by
  obtain ⟨hx, hy, hz⟩ := basis_vectors k
  change basisValue k 0 = xValue k at hx
  change basisValue k 1 = yValue k at hy
  change basisValue k 2 = zValue k at hz
  rw [hx, hy, hz]
  simpa only [normal, normalized_apply, LieNotes.Heisenberg.x, LieNotes.Heisenberg.y,
    LieNotes.Heisenberg.z] using phi_pairs k (p 0) (p 1) (p 2) (p 3) (p 4)

private theorem normal_transport (b : Module.Basis (Fin 3) k L) (hb : HeisenbergBasis b)
    (p : Fin 5 → k) (f : Cochains k L 2) (hf : HasNormalValues b p f)
    (x y : ModelValue k) :
    basisIdentification b hb (normal p x y) =
      exteriorCochain f (basisIdentification b hb x) (basisIdentification b hb y) := by
  let E := (basisIdentification b hb).toLinearEquiv
  let B := (normal p).1.compr₂ E.toLinearMap
  let C := (exteriorCochain f).1.compl₁₂ E.toLinearMap E.toLinearMap
  have hE (i : Fin 3) : E (basisValue k i) = b i :=
    basisLieEquiv_apply_basis b hb.1 hb.2.1 hb.2.2 i
  have h : B = C := by
    apply alternating_ext (basisValue k)
    · intro z
      change E (normal p z z) = 0
      rw [twoCochain_alt, map_zero]
    · intro z
      exact twoCochain_alt (exteriorCochain f) (E z)
    · intro i j hij
      change E (normal p (basisValue k i) (basisValue k j)) =
        f (wedge k L 2 ![E (basisValue k i), E (basisValue k j)])
      rw [hE, hE]
      obtain ⟨h01, h02, h12⟩ := normal_pairs p
      obtain ⟨f01, f02, f12⟩ := hf
      rcases ascending_pair hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [h01, f01, map_zero]
      · simp only [h02, f02, map_add, map_smul, hE]
      · simp only [h12, f12, map_add, map_sub, map_smul, hE]
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

private theorem normalized_reduction_in_basis
    (b : Module.Basis (Fin 3) k L) (hb : HeisenbergBasis b) (ρ : A →+* DualNumber k)
    (p : Fin 5 → k) (f : Cochains k L 2) (hf : HasNormalValues b p f)
    (D : Deformation k L)
    (hD : ∀ x y, D.bracket x y = bracketFormula (exteriorCochain f) x y) :
    ExtendsInBasis b hb ρ D ↔ ∃ B : LieBracket A, ReducesTo ρ B (normal p) := by
  let E := basisIdentification b hb
  let G := E.toLinearEquiv.prodCongr E.toLinearEquiv
  have hformula (x y : ModelValue k × ModelValue k) :
      G (bracketFormula (normal p) x y) = D.bracket (G x) (G y) := by
    rw [hD]
    apply Prod.ext
    · change E ⁅x.1, y.1⁆ = ⁅E x.1, E y.1⁆
      exact E.map_lie _ _
    · change E (⁅x.1, y.2⁆ - ⁅y.1, x.2⁆ + normal p x.1 y.1) =
        ⁅E x.1, E y.2⁆ - ⁅E y.1, E x.2⁆ + exteriorCochain f (E x.1) (E y.1)
      rw [map_add, map_sub, E.map_lie, E.map_lie]
      exact congrArg (_ + ·) (normal_transport b hb p f hf x.1 y.1)
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun x y => G.injective ?_⟩
    exact (hB x y).trans (hformula (reduce ρ x) (reduce ρ y)).symm
  · rintro ⟨B, hB⟩
    refine ⟨B, fun x y => ?_⟩
    exact (congrArg G (hB x y)).trans (hformula (reduce ρ x) (reduce ρ y))

private theorem extends_of_lift (b : Module.Basis (Fin 3) k L) (hb : HeisenbergBasis b)
    (ρ : A →+* DualNumber k) (D D' : Deformation k L)
    (S : (L × L) ≃ₗ[k] (L × L)) (U : Carrier A ≃ₗ[A] Carrier A)
    (hU : ∀ p, reduceInBasis b hb ρ (U p) = S (reduceInBasis b hb ρ p))
    (hS : ∀ p q, S (D'.bracket p q) = D.bracket (S p) (S q)) :
    ExtendsInBasis b hb ρ D → ExtendsInBasis b hb ρ D' := by
  rintro ⟨B, hB⟩
  refine ⟨pullbackValue A U B, fun p q => S.injective ?_⟩
  rw [← hU, hS, ← hU, ← hU]
  change reduceInBasis b hb ρ (U (U.symm (B.bracket (U p) (U q)))) =
    D.bracket (reduceInBasis b hb ρ (U p)) (reduceInBasis b hb ρ (U q))
  rw [U.apply_symm_apply]
  exact hB (U p) (U q)

private theorem extends_iff_of_lift (b : Module.Basis (Fin 3) k L) (hb : HeisenbergBasis b)
    (ρ : A →+* DualNumber k) (D D' : Deformation k L)
    (S : (L × L) ≃ₗ[k] (L × L)) (U : Carrier A ≃ₗ[A] Carrier A)
    (hU : ∀ p, reduceInBasis b hb ρ (U p) = S (reduceInBasis b hb ρ p))
    (hS : ∀ p q, S (D'.bracket p q) = D.bracket (S p) (S q)) :
    ExtendsInBasis b hb ρ D ↔ ExtendsInBasis b hb ρ D' := by
  refine ⟨extends_of_lift b hb ρ D D' S U hU hS,
    extends_of_lift b hb ρ D' D S.symm U.symm ?_ ?_⟩
  · intro p
    apply S.injective
    rw [← hU, U.apply_symm_apply, S.apply_symm_apply]
  · intro p q
    apply S.injective
    rw [S.apply_symm_apply, hS, S.apply_symm_apply, S.apply_symm_apply]

private theorem equiv_preserves_extensions [CharZero k]
    (b : Module.Basis (Fin 3) k L) (hb : HeisenbergBasis b)
    (D D' : Deformation k L) (h : Equivalent D D') :
    (ExtendsInBasis b hb (truncatedReduction k).toRingHom D ↔
      ExtendsInBasis b hb (truncatedReduction k).toRingHom D') ∧
    (ExtendsInBasis b hb (formalReduction k) D ↔
      ExtendsInBasis b hb (formalReduction k) D') := by
  obtain ⟨S, hS⟩ := h
  let E := (basisIdentification b hb).toLinearEquiv
  let f := E.symm.conj (coordinateCoefficient S)
  have lift_reduction {R : Type u} [CommRing R] (ρ : R →+* DualNumber k)
      (U : Carrier R ≃ₗ[R] Carrier R)
      (hU : ∀ p, reduce ρ (U p) = shear f (reduce ρ p)) (p : Carrier R) :
      reduceInBasis b hb ρ (U p) = S.equiv (reduceInBasis b hb ρ p) := by
    rw [coordinate_normal_form]
    change (E (reduce ρ (U p)).1, E (reduce ρ (U p)).2) =
      shear (coordinateCoefficient S) (E (reduce ρ p).1, E (reduce ρ p).2)
    rw [hU]
    apply Prod.ext
    · rfl
    · change E ((reduce ρ p).2 + f (reduce ρ p).1) =
        E (reduce ρ p).2 + coordinateCoefficient S (E (reduce ρ p).1)
      rw [map_add]
      simp [f, LinearEquiv.conj_apply_apply]
  obtain ⟨U, _, _, hU⟩ := DeformationTransport.truncatedTransport k f
  obtain ⟨V, _, _, hV⟩ := DeformationTransport.formalTransport k f
  exact ⟨extends_iff_of_lift b hb _ D D' S.equiv U (lift_reduction _ U hU) hS,
    extends_iff_of_lift b hb _ D D' S.equiv V (lift_reduction _ V hV) hS⟩

theorem extension_locus : ExtensionLocusType := by
  intro k _ _ L _ _ b hb
  obtain ⟨e, he, _⟩ := AdjointCohomology.normal_form k L b hb
  have hs (n : ℕ) : (d k L (n + 1)).comp (d k L n) = 0 := by
    apply LinearMap.ext
    intro f
    exact AdjointCohomology.d_squared n f
  obtain ⟨classOf, hsurj, hequiv, hclass⟩ :=
    _root_.LieAlgebrasAndRepresentations.InfinitesimalDeformations.classification_spec
      (k := k) (g := L) (d k L) hs AdjointCohomology.d_formula
  refine ⟨e, classOf, he, hsurj, hequiv, hclass, fun D p hD => ?_⟩
  obtain ⟨f, hf, _⟩ := he p
  let c := exteriorCochain f.1
  have hcExterior : cochainExterior c = f.1 :=
    (twoCochainExteriorEquiv (k := k) (g := L) (M := L)).apply_symm_apply f.1
  have hc : d₂₃ k L L c = 0 := by
    apply (exterior_cycle_iff _ AdjointCohomology.d_formula c).mp
    rw [hcExterior]
    exact f.property
  let D₀ := model (⟨c, hc⟩ : twoCocycle k L L)
  have hD₀ (x y : L × L) : D₀.bracket x y = bracketFormula c x y := rfl
  obtain ⟨g, hg, hclassD₀⟩ := hclass D₀ ⟨c, hc⟩ hD₀
  have hgf : g = f := by
    apply Subtype.ext
    apply wedge_ext
    intro x
    rw [← hcExterior, cochainExterior_wedge]
    have hv : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    conv_lhs => rw [hv]
    exact hg (x 0) (x 1)
  have hsame : Equivalent D₀ D :=
    (hequiv _ _).mp (hclassD₀.trans ((congrArg Submodule.Quotient.mk hgf).trans (hf.2.trans hD.symm)))
  obtain ⟨htr, hfo⟩ := equiv_preserves_extensions b hb D₀ D hsame
  obtain ⟨hnormal, hformal⟩ := normalized_extension k p
  have htr₀ := normalized_reduction_in_basis b hb (truncatedReduction k).toRingHom p f.1 hf.1 D₀ hD₀
  have hfo₀ := normalized_reduction_in_basis b hb (formalReduction k) p f.1 hf.1 D₀ hD₀
  exact ⟨htr.symm.trans (htr₀.trans hnormal), fun hp =>
    hfo.mp (hfo₀.mpr (by
      obtain ⟨_, _, B, _, hB⟩ := hformal hp
      exact ⟨B, hB⟩))⟩

end LieNotes.Heisenberg.ExtensionLocus
