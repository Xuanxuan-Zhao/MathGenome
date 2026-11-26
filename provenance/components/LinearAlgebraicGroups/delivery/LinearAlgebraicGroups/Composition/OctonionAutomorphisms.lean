import Specs.LinearAlgebraicGroups.Composition.OctonionAutomorphisms
import LinearAlgebraicGroups.Composition.PeirceFrames
import LinearAlgebraicGroups.Composition.Algebras
import LinearAlgebraicGroups.Albert.AutomorphismScheme
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import LinearAlgebraicGroups.Reductive.GeometricRadicals
import LinearAlgebraicGroups.Solvable.LieKolchin
import LinearAlgebraicGroups.Unipotent.CentralSeries
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Smooth.Locus

import LinearAlgebraicGroups.RootData.SchemeCentre
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Composition.OctonionAutomorphisms

open OctonionAutomorphismSpecification
open Specification
open scoped Matrix

noncomputable section

section Diagonal

variable {R : Type u} [CommRing R]

private def scaleVector (d : Fin 3 → Rˣ) (x : Fin 3 → R) : Fin 3 → R :=
  fun i => (d i).val * x i

private def scaleSlots (d : Fin 3 → Rˣ) (x : ZornCoordinates R) : ZornCoordinates R :=
  (x.1, scaleVector d x.2.1, scaleVector d⁻¹ x.2.2.1, x.2.2.2)

private def diagonalLinearEquiv (d : Fin 3 → Rˣ) : Zorn R ≃ₗ[R] Zorn R :=
  (Zorn.coordinates R).trans <| ({
    toFun := scaleSlots d
    invFun := scaleSlots d⁻¹
    left_inv := by
      rintro ⟨a, x, y, b⟩
      have h (e : Fin 3 → Rˣ) (w : Fin 3 → R) : scaleVector e⁻¹ (scaleVector e w) = w := by
        funext i
        change ((e i)⁻¹ : Rˣ).val * ((e i).val * w i) = w i
        rw [← mul_assoc, Units.inv_mul, one_mul]
      have hy := h d⁻¹ y
      simp only [inv_inv] at hy
      simp only [scaleSlots, inv_inv, h d x, hy]
    right_inv := by
      rintro ⟨a, x, y, b⟩
      have h (e : Fin 3 → Rˣ) (w : Fin 3 → R) : scaleVector e (scaleVector e⁻¹ w) = w := by
        funext i
        change (e i).val * (((e i)⁻¹ : Rˣ).val * w i) = w i
        rw [← mul_assoc, Units.mul_inv, one_mul]
      have hy := h d⁻¹ y
      simp only [inv_inv] at hy
      simp only [scaleSlots, inv_inv, h d x, hy]
    map_add' := by
      rintro ⟨a, x, y, b⟩ ⟨c, w, t, f⟩
      simp only [scaleSlots, Prod.mk_add_mk, Prod.mk.injEq, true_and, and_true]
      constructor <;> funext i <;> simp [scaleVector, mul_add]
    map_smul' := by
      rintro r ⟨a, x, y, b⟩
      simp only [scaleSlots, Prod.smul_mk, RingHom.id_apply, Prod.mk.injEq, true_and, and_true]
      constructor <;> funext i <;> simp [scaleVector, smul_eq_mul, mul_left_comm]
  } : ZornCoordinates R ≃ₗ[R] ZornCoordinates R).trans (Zorn.coordinates R).symm

private theorem scale_dot (d : Fin 3 → Rˣ) (x y : Fin 3 → R) :
    scaleVector d x ⬝ᵥ scaleVector d⁻¹ y = x ⬝ᵥ y := by
  apply Finset.sum_congr rfl
  intro i _
  change ((d i).val * x i) * (((d i)⁻¹ : Rˣ).val * y i) = x i * y i
  calc
    _ = ((d i).val * ((d i)⁻¹ : Rˣ).val) * (x i * y i) := by ring
    _ = _ := by rw [Units.mul_inv, one_mul]

private theorem scale_cross (d : Fin 3 → Rˣ)
    (h : d 0 * d 1 * d 2 = 1) (x y : Fin 3 → R) :
    scaleVector d x ⨯₃ scaleVector d y = scaleVector d⁻¹ (x ⨯₃ y) := by
  have h0 : (d 1).val * (d 2).val = ((d 0)⁻¹ : Rˣ).val := by
    have H : d 0 * (d 1 * d 2) = 1 := by simpa only [mul_assoc] using h
    exact congrArg Units.val (eq_inv_of_mul_eq_one_right H)
  have h1 : (d 2).val * (d 0).val = ((d 1)⁻¹ : Rˣ).val := by
    have H : d 1 * (d 2 * d 0) = 1 := by calc
      _ = d 0 * d 1 * d 2 := by ac_rfl
      _ = 1 := h
    exact congrArg Units.val (eq_inv_of_mul_eq_one_right H)
  have h2 : (d 0).val * (d 1).val = ((d 2)⁻¹ : Rˣ).val :=
    congrArg Units.val (eq_inv_of_mul_eq_one_left h)
  funext i
  fin_cases i
  · change ((d 1).val * x 1) * ((d 2).val * y 2) -
        ((d 2).val * x 2) * ((d 1).val * y 1) = ((d 0)⁻¹ : Rˣ).val * (x 1 * y 2 - x 2 * y 1)
    rw [← h0]
    ring
  · change ((d 2).val * x 2) * ((d 0).val * y 0) -
        ((d 0).val * x 0) * ((d 2).val * y 2) = ((d 1)⁻¹ : Rˣ).val * (x 2 * y 0 - x 0 * y 2)
    rw [← h1]
    ring
  · change ((d 0).val * x 0) * ((d 1).val * y 1) -
        ((d 1).val * x 1) * ((d 0).val * y 0) = ((d 2)⁻¹ : Rˣ).val * (x 0 * y 1 - x 1 * y 0)
    rw [← h2]
    ring

private theorem diagonal_mul (d : Fin 3 → Rˣ) (h : d 0 * d 1 * d 2 = 1) (x y : Zorn R) :
    diagonalLinearEquiv d (x * y) = diagonalLinearEquiv d x * diagonalLinearEquiv d y := by
  obtain ⟨⟨a, p, q, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
  obtain ⟨⟨c, w, t, f⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective y
  apply (Zorn.coordinates R).injective
  have hi : d⁻¹ 0 * d⁻¹ 1 * d⁻¹ 2 = 1 := by
    change (d 0)⁻¹ * (d 1)⁻¹ * (d 2)⁻¹ = 1
    rw [← mul_inv, ← mul_inv, h, inv_one]
  have hd (r s : R) (e : Fin 3 → Rˣ) (x y z : Fin 3 → R) :
      scaleVector e (r • x + s • y + z) =
        r • scaleVector e x + s • scaleVector e y + scaleVector e z := by
    funext i
    simp [scaleVector, smul_eq_mul]
    ring
  have hs (r s : R) (e : Fin 3 → Rˣ) (x y z : Fin 3 → R) :
      scaleVector e (r • x + s • y - z) =
        r • scaleVector e x + s • scaleVector e y - scaleVector e z := by
    funext i
    simp [scaleVector, smul_eq_mul]
    ring
  change scaleSlots d (zornProduct (a, p, q, b) (c, w, t, f)) =
    zornProduct (scaleSlots d (a, p, q, b)) (scaleSlots d (c, w, t, f))
  simp only [scaleSlots, zornProduct, scale_dot, scale_cross d h, scale_cross d⁻¹ hi,
    inv_inv, hd, hs, Prod.mk.injEq, true_and]
  rw [dotProduct_comm (scaleVector d⁻¹ q), scale_dot, dotProduct_comm]

private theorem diagonal_one (d : Fin 3 → Rˣ) :
    diagonalLinearEquiv d (1 : Zorn R) = 1 := by
  apply (Zorn.coordinates R).injective
  change scaleSlots d ((1 : R), 0, 0, 1) = (1, 0, 0, 1)
  have hz (e : Fin 3 → Rˣ) : scaleVector e 0 = 0 := by
    funext i
    exact mul_zero _
  simp [scaleSlots, hz]

end Diagonal

section GeometricRepresentation

variable {K : Type u} [Field K]

private theorem point_one (g : ZornPointGroup K) : g.val.val 1 = 1 :=
  g.property.1 _ (Set.mem_singleton _)

private theorem point_mul (g : ZornPointGroup K) (x y : Zorn K) :
    g.val.val (x * y) = g.val.val x * g.val.val y :=
  g.property.2 x y

open private octonion_norm_comp_equiv from LinearAlgebraicGroups.Composition.Adjoints in
private theorem point_norm_trace (g : ZornPointGroup K) :
    (Zorn.norm K).comp g.val.val = Zorn.norm K ∧
    (compositionTrace (Zorn.norm K)).comp g.val.val = compositionTrace (Zorn.norm K) := by
  let e : Zorn K ≃ₗ[K] Zorn K := LinearMap.GeneralLinearGroup.toLinearEquiv g.val
  have h := octonion_norm_unique (octonion_norm_comp_equiv (Zorn.isOctonion K) e (point_mul g))
    (Zorn.isOctonion K)
  refine ⟨h.1, LinearMap.ext fun x => ?_⟩
  change compositionTrace (Zorn.norm K) (e x) = compositionTrace (Zorn.norm K) x
  have H := LinearMap.congr_fun h.2 x
  simpa only [compositionTrace_apply, QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply,
    LinearEquiv.coe_coe, show e 1 = 1 from point_one g] using H

private def traceAction (g : ZornPointGroup K) : Module.End K (traceZero K) :=
  (g.val.val.comp (traceZero K).subtype).codRestrict (traceZero K) fun x => by
    change compositionTrace (Zorn.norm K) (g.val.val x.val) = 0
    rw [show compositionTrace (Zorn.norm K) (g.val.val x.val) =
      compositionTrace (Zorn.norm K) x.val from LinearMap.congr_fun (point_norm_trace g).2 _]
    exact x.property

private def traceActionHom : ZornPointGroup K →* Module.End K (traceZero K) where
  toFun := traceAction
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

private def traceRepresentation : ZornPointGroup K →* (Module.End K (traceZero K))ˣ :=
  MonoidHom.toHomUnits traceActionHom

private theorem traceRepresentation_apply (g : ZornPointGroup K) (x : traceZero K) :
    ((traceRepresentation g).val x).val = g.val.val x.val := rfl

private abbrev scalarTraceLine (K : Type u) [Field K] : Submodule K (traceZero K) :=
  (scalarLine K).comap (traceZero K).subtype

private theorem scalar_mem_trace (h : (2 : K) = 0) : scalarLine K ≤ traceZero K := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact (compositionTrace_one (Zorn.isOctonion K).toNormLaws).trans h

private theorem trace_action_preserves_line (g : ZornPointGroup K) (x : traceZero K)
    (hx : x ∈ scalarTraceLine K) : traceAction g x ∈ scalarTraceLine K := by
  change x.val ∈ scalarLine K at hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  change g.val.val x.val ∈ scalarLine K
  rw [← ha, map_smul, point_one]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

private def quotientAction (g : ZornPointGroup K) : Module.End K (traceZeroQuotient K) :=
  (scalarTraceLine K).mapQ (scalarTraceLine K) (traceAction g)
    (fun x hx => trace_action_preserves_line g x hx)

private def quotientActionHom : ZornPointGroup K →* Module.End K (traceZeroQuotient K) where
  toFun := quotientAction
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective _) x
    rfl
  map_mul' _ _ := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective _) x
    rfl

private def quotientRepresentation :
    ZornPointGroup K →* (Module.End K (traceZeroQuotient K))ˣ :=
  MonoidHom.toHomUnits quotientActionHom

private theorem quotientRepresentation_apply (g : ZornPointGroup K) (x : traceZero K) :
    (quotientRepresentation g).val (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((traceRepresentation g).val x) := rfl

private theorem trace_first : compositionTrace (Zorn.norm K) (Zorn.first K) = 1 :=
  (Peirce.firstPoint K).property.1

private theorem point_eq_one_of_fixes_trace (g : ZornPointGroup K)
    (h : ∀ x : traceZero K, g.val.val x.val = x.val) : g = 1 := by
  let u : traceZero K := ⟨Zorn.ofCoordinates (0, Pi.single (0 : Fin 3) 1, 0, 0), by
    change compositionTrace (Zorn.norm K) (Zorn.ofCoordinates (0, _, 0, 0)) = 0
    rw [Zorn.trace_formula, add_zero]⟩
  let w : traceZero K := ⟨Zorn.ofCoordinates (0, 0, Pi.single (0 : Fin 3) 1, 0), by
    change compositionTrace (Zorn.norm K) (Zorn.ofCoordinates (0, 0, _, 0)) = 0
    rw [Zorn.trace_formula, add_zero]⟩
  have hu : u.val * w.val = Zorn.first K := by
    apply (Zorn.coordinates K).injective
    rw [Zorn.coordinates_mul]
    change zornProduct ((0 : K), Pi.single (0 : Fin 3) 1, 0, 0)
      (0, 0, Pi.single (0 : Fin 3) 1, 0) = (1, 0, 0, 0)
    simp [zornProduct, dotProduct, Fin.sum_univ_three]
  have he : g.val.val (Zorn.first K) = Zorn.first K := by
    rw [← hu, point_mul, h u, h w]
  apply Subtype.ext
  apply Units.ext
  ext x
  let a := compositionTrace (Zorn.norm K) x
  let y : traceZero K := ⟨x - a • Zorn.first K, by
    change compositionTrace (Zorn.norm K) (x - a • Zorn.first K) = 0
    rw [map_sub, map_smul, trace_first, smul_eq_mul, mul_one, sub_self]⟩
  change g.val.val x = x
  have hx : y.val + a • Zorn.first K = x := sub_add_cancel _ _
  calc
    g.val.val x = g.val.val (y.val + a • Zorn.first K) := congrArg _ hx.symm
    _ = y.val + a • Zorn.first K := by rw [map_add, map_smul, h y, he]
    _ = x := hx

private theorem trace_representation_injective :
    Function.Injective (traceRepresentation (K := K)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  apply point_eq_one_of_fixes_trace g
  intro x
  have hh := congrArg (fun f : (Module.End K (traceZero K))ˣ => (f.val x).val) hg
  exact hh

private theorem quotient_representation_injective :
    Function.Injective (quotientRepresentation (K := K)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  apply point_eq_one_of_fixes_trace g
  intro x
  have hh : (Submodule.Quotient.mk ((traceRepresentation g).val x) : traceZeroQuotient K)
      = Submodule.Quotient.mk x := by
    rw [← quotientRepresentation_apply, hg]
    rfl
  have hm := (Submodule.Quotient.eq (scalarTraceLine K)).mp hh
  change g.val.val x.val - x.val ∈ scalarLine K at hm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have hsum : g.val.val x.val = a • (1 : Zorn K) + x.val := (eq_add_of_sub_eq ha.symm)
  have hn := DFunLike.congr_fun (point_norm_trace g).1 x.val
  change Zorn.norm K (g.val.val x.val) = Zorn.norm K x.val at hn
  rw [hsum, add_comm] at hn
  have hp : (Zorn.norm K).polarBilin x.val (a • (1 : Zorn K)) = 0 := by
    rw [map_smul, ← compositionTrace_apply, show compositionTrace (Zorn.norm K) x.val = 0 from
      x.property, smul_zero]
  rw [full_polar_formula, hn, norm_scalar (Zorn.isOctonion K).toNormLaws, sub_self,
    zero_sub, neg_eq_zero, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)] at hp
  rw [hp, zero_smul, zero_add] at hsum
  exact hsum

private def pointOfLinearEquiv (e : Zorn K ≃ₗ[K] Zorn K) (h₁ : e 1 = 1)
    (hm : ∀ x y : Zorn K, e (x * y) = e x * e y) : ZornPointGroup K :=
  ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv e, by
    refine ⟨?_, hm⟩
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact h₁⟩

private abbrev TraceIndex := Option (Bool × Fin 3)

private def traceSlots (x : ZornCoordinates K) : TraceIndex → K
  | none => x.1
  | some (false, i) => x.2.1 i
  | some (true, i) => x.2.2.1 i

private def traceVector (f : TraceIndex → K) : traceZero K :=
  ⟨Zorn.ofCoordinates (f none, (fun i => f (some (false, i))),
      (fun i => f (some (true, i))), -f none), by
    change compositionTrace (Zorn.norm K) (Zorn.ofCoordinates (_, _, _, _)) = 0
    rw [Zorn.trace_formula, add_neg_cancel]⟩

private def traceCoordinates : traceZero K ≃ₗ[K] (TraceIndex → K) where
  toFun x := traceSlots (Zorn.coordinates K x.val)
  invFun := traceVector
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨⟨a, p, q, b⟩, rfl⟩ := (Zorn.coordinates K).symm.surjective x
    change compositionTrace (Zorn.norm K) (Zorn.ofCoordinates (a, p, q, b)) = 0 at hx
    rw [Zorn.trace_formula, add_eq_zero_iff_eq_neg] at hx
    apply Subtype.ext
    change Zorn.ofCoordinates (a, p, q, -a) = Zorn.ofCoordinates (a, p, q, b)
    rw [hx, neg_neg]
  right_inv f := by
    funext i
    rcases i with _ | ⟨b, i⟩
    · rfl
    · cases b <;> rfl
  map_add' x y := by
    funext i
    rcases i with _ | ⟨b, i⟩
    · rfl
    · cases b <;> rfl
  map_smul' a x := by
    funext i
    rcases i with _ | ⟨b, i⟩
    · rfl
    · cases b <;> rfl

private def traceBasis (i : TraceIndex) : traceZero K :=
  traceVector (Pi.single i 1)

private theorem traceBasis_coords (i : TraceIndex) :
    traceCoordinates (traceBasis (K := K) i) = Pi.single i 1 :=
  traceCoordinates.apply_symm_apply _

private theorem traceBasis_ne_zero (i : TraceIndex) : traceBasis (K := K) i ≠ 0 := by
  intro h
  have hi := congrArg (fun x : traceZero K => traceCoordinates x i) h
  simp [traceBasis_coords] at hi

private def diagonalPoint (d : Fin 3 → Kˣ) (h : d 0 * d 1 * d 2 = 1) : ZornPointGroup K :=
  pointOfLinearEquiv (diagonalLinearEquiv d) (diagonal_one d) (diagonal_mul d h)

private def traceWeight (d : Fin 3 → Kˣ) : TraceIndex → Kˣ
  | none => 1
  | some (false, i) => d i
  | some (true, i) => (d i)⁻¹

private theorem diagonal_traceCoordinates (d : Fin 3 → Kˣ) (h : d 0 * d 1 * d 2 = 1)
    (x : traceZero K) (i : TraceIndex) :
    traceCoordinates (traceAction (diagonalPoint d h) x) i =
      (traceWeight d i).val * traceCoordinates x i := by
  rcases i with _ | ⟨b, i⟩
  · change (Zorn.coordinates K x.val).1 = 1 * _
    rw [one_mul]
    rfl
  · cases b <;> rfl

private theorem exists_distinct_trace_weights [Infinite K] :
    ∃ d : Fin 3 → Kˣ, d 0 * d 1 * d 2 = 1 ∧ Function.Injective (fun i => (traceWeight d i).val) := by
  classical
  let P : Fin 6 → Polynomial K := fun n => Polynomial.X ^ (n.val + 1) - 1
  have hP (n : Fin 6) : P n ≠ 0 := by
    intro h
    have h' := congrArg (fun p : Polynomial K => p.coeff (n.val + 1)) h
    simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_one] at h'
  have hs : (⋃ n : Fin 6, {a | (P n).IsRoot a}).Finite :=
    Set.finite_iUnion fun n => Polynomial.finite_setOfPred_isRoot (hP n)
  obtain ⟨a, ha⟩ := (hs.insert 0).exists_notMem
  simp only [Set.mem_insert_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at ha
  let z : Kˣ := Units.mk0 a ha.1
  let d : Fin 3 → Kˣ := ![z, z ^ 2, z ^ (-3 : ℤ)]
  have hz (n : ℕ) (hn : 0 < n) (hn' : n ≤ 6) : z ^ n ≠ 1 := by
    intro h
    have H := congrArg Units.val h
    have hpow : a ^ n = 1 := by simpa [z] using H
    let j : Fin 6 := ⟨n - 1, by omega⟩
    apply ha.2 j
    simp [P, Polynomial.IsRoot, j, show n - 1 + 1 = n by omega, hpow]
  let e : TraceIndex → ℤ
    | none => 0
    | some (false, i) => ![1, 2, -3] i
    | some (true, i) => ![-1, -2, 3] i
  have he (i : TraceIndex) : traceWeight d i = z ^ e i := by
    rcases i with _ | ⟨b, i⟩
    · simp [traceWeight, e]
    · cases b <;> fin_cases i <;> norm_num [traceWeight, d, e, zpow_neg, zpow_natCast]
  have hbounds (i : TraceIndex) : -3 ≤ e i ∧ e i ≤ 3 := by
    rcases i with _ | ⟨b, i⟩
    · norm_num [e]
    · cases b <;> fin_cases i <;> norm_num [e]
  have hei : Function.Injective e := by
    intro i j hij
    rcases i with _ | ⟨b, i⟩ <;> rcases j with _ | ⟨c, j⟩
    · rfl
    · cases c <;> fin_cases j <;> norm_num [e] at hij
    · cases b <;> fin_cases i <;> norm_num [e] at hij
    · cases b <;> cases c <;> fin_cases i <;> fin_cases j <;> norm_num [e] at hij <;> rfl
  refine ⟨d, ?_, ?_⟩
  · change z * z ^ 2 * z ^ (-3 : ℤ) = 1
    calc
      _ = z ^ (1 : ℤ) * z ^ (2 : ℤ) * z ^ (-3 : ℤ) := by simp
      _ = 1 := by rw [← zpow_add, ← zpow_add]; norm_num
  · intro i j h
    apply hei
    have H := Units.ext h
    rw [he i, he j] at H
    suffices aux : ∀ p q : TraceIndex, e p < e q → z ^ e p = z ^ e q → False by
      rcases lt_trichotomy (e i) (e j) with hlt | heq | hgt
      · exact (aux i j hlt H).elim
      · exact heq
      · exact (aux j i hgt H.symm).elim
    intro p q hpq hp
    have hlow : 0 < e q - e p := by omega
    have hhigh : e q - e p ≤ 6 := by have := hbounds p; have := hbounds q; omega
    apply hz (e q - e p).toNat (by omega) (by omega)
    rw [← zpow_natCast, Int.toNat_of_nonneg hlow.le, zpow_sub, hp, mul_inv_cancel]

private theorem coordinateVector_mem_of_action {I : Type*} [Fintype I] [DecidableEq I]
    (U : Submodule K (I → K)) (f : Module.End K (I → K)) (weight : I → K)
    (hinj : Function.Injective weight) (hf : ∀ x i, f x i = weight i * x i)
    (hU : ∀ x ∈ U, f x ∈ U) (x : I → K) (hx : x ∈ U) (i : I) (hi : x i ≠ 0) :
    Pi.single i 1 ∈ U := by
  classical
  have aux (s : Finset I) (hs : i ∉ s) :
      ∃ y ∈ U, y i = x i ∧ ∀ j ∈ s, y j = 0 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨x, hx, rfl, by simp⟩
    | @insert j s hj ih =>
      have hij : i ≠ j := fun h => hs (h ▸ Finset.mem_insert_self _ _)
      obtain ⟨y, hy, hiy, hsy⟩ := ih fun h => hs (Finset.mem_insert_of_mem h)
      let z := (weight i - weight j)⁻¹ • (f y - weight j • y)
      have eval_z (k : I) : z k = (weight i - weight j)⁻¹ * ((weight k - weight j) * y k) := by
        simp [z, hf, smul_eq_mul, sub_mul]
      refine ⟨z, U.smul_mem _ (U.sub_mem (hU y hy) (U.smul_mem _ hy)), ?_, ?_⟩
      · rw [eval_z, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr (fun h => hij (hinj h))),
          one_mul, hiy]
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · rw [eval_z, sub_self, zero_mul, mul_zero]
        · rw [eval_z, hsy _ hk, mul_zero, mul_zero]
  obtain ⟨y, hy, hiy, hsy⟩ := aux (Finset.univ.erase i) (by simp)
  have heq : (x i)⁻¹ • y = Pi.single i (1 : K) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [hiy, hi, smul_eq_mul]
    · simp [Pi.single_eq_of_ne hj, hsy j (by simp [hj]), smul_eq_mul]
  rw [← heq]
  exact U.smul_mem _ hy

private def swapSlots (x : ZornCoordinates K) : ZornCoordinates K :=
  (x.2.2.2, -x.2.2.1, -x.2.1, x.1)

private def swapLinearEquiv : Zorn K ≃ₗ[K] Zorn K :=
  (Zorn.coordinates K).trans <| ({
    toFun := swapSlots
    invFun := swapSlots
    left_inv := by rintro ⟨a, x, y, b⟩; simp [swapSlots]
    right_inv := by rintro ⟨a, x, y, b⟩; simp [swapSlots]
    map_add' := by rintro ⟨a, x, y, b⟩ ⟨c, u, v, d⟩; simp [swapSlots, add_comm]
    map_smul' := by rintro r ⟨a, x, y, b⟩; simp [swapSlots]
  } : ZornCoordinates K ≃ₗ[K] ZornCoordinates K).trans (Zorn.coordinates K).symm

private def swapPoint : ZornPointGroup K := by
  refine pointOfLinearEquiv swapLinearEquiv ?_ ?_
  · apply (Zorn.coordinates K).injective
    change swapSlots ((1 : K), 0, 0, 1) = (1, 0, 0, 1)
    simp [swapSlots]
  · intro x y
    obtain ⟨⟨a, p, q, b⟩, rfl⟩ := (Zorn.coordinates K).symm.surjective x
    obtain ⟨⟨c, u, v, d⟩, rfl⟩ := (Zorn.coordinates K).symm.surjective y
    apply (Zorn.coordinates K).injective
    change swapSlots (zornProduct (a, p, q, b) (c, u, v, d)) =
      zornProduct (swapSlots (a, p, q, b)) (swapSlots (c, u, v, d))
    simp [swapSlots, zornProduct, sub_eq_add_neg]
    constructor <;> abel

private def rotateVector (x : Fin 3 → K) : Fin 3 → K := fun i => x (i + 2)

private def rotateSlots (x : ZornCoordinates K) : ZornCoordinates K :=
  (x.1, rotateVector x.2.1, rotateVector x.2.2.1, x.2.2.2)

omit [Field K] in
private theorem rotateSlots_cube (x : ZornCoordinates K) :
    rotateSlots (rotateSlots (rotateSlots x)) = x := by
  rcases x with ⟨a, p, q, b⟩
  simp only [rotateSlots, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext i <;> fin_cases i <;> rfl

private def rotateLinearEquiv : Zorn K ≃ₗ[K] Zorn K :=
  (Zorn.coordinates K).trans <| ({
    toFun := rotateSlots
    invFun := rotateSlots ∘ rotateSlots
    left_inv := rotateSlots_cube
    right_inv := rotateSlots_cube
    map_add' := by rintro ⟨a, x, y, b⟩ ⟨c, u, v, d⟩; rfl
    map_smul' := by rintro r ⟨a, x, y, b⟩; rfl
  } : ZornCoordinates K ≃ₗ[K] ZornCoordinates K).trans (Zorn.coordinates K).symm

private def rotatePoint : ZornPointGroup K := by
  refine pointOfLinearEquiv rotateLinearEquiv ?_ ?_
  · apply (Zorn.coordinates K).injective
    rfl
  · intro x y
    obtain ⟨⟨a, p, q, b⟩, rfl⟩ := (Zorn.coordinates K).symm.surjective x
    obtain ⟨⟨c, u, v, d⟩, rfl⟩ := (Zorn.coordinates K).symm.surjective y
    apply (Zorn.coordinates K).injective
    have hd (p q : Fin 3 → K) : rotateVector p ⬝ᵥ rotateVector q = p ⬝ᵥ q := by
      simp only [dotProduct, Fin.sum_univ_three, rotateVector]
      change p 2 * q 2 + p 0 * q 0 + p 1 * q 1 = _
      ring
    have hc (p q : Fin 3 → K) : rotateVector (p ⨯₃ q) = rotateVector p ⨯₃ rotateVector q := by
      funext i
      fin_cases i <;> rfl
    change rotateSlots (zornProduct (a, p, q, b) (c, u, v, d)) =
      zornProduct (rotateSlots (a, p, q, b)) (rotateSlots (c, u, v, d))
    simp only [rotateSlots, zornProduct, hd, Prod.mk.injEq, true_and, and_true]
    constructor <;> (funext i; rw [← hc]; rfl)

private theorem rotate_traceBasis (b : Bool) (i : Fin 3) :
    traceAction (rotatePoint (K := K)) (traceBasis (some (b, i))) =
      traceBasis (some (b, i + 1)) := by
  cases b <;> fin_cases i <;> apply Subtype.ext <;> apply (Zorn.coordinates K).injective <;>
    simp [traceAction, rotatePoint, rotateLinearEquiv, pointOfLinearEquiv,
      traceBasis, traceVector, rotateSlots] <;>
    constructor <;> funext j <;> fin_cases j <;> simp [rotateVector]

private theorem swap_traceBasis (i : Fin 3) :
    traceAction (swapPoint (K := K)) (traceBasis (some (false, i))) =
      -traceBasis (some (true, i)) := by
  apply Subtype.ext
  apply (Zorn.coordinates K).injective
  simp [traceAction, swapPoint, swapLinearEquiv, pointOfLinearEquiv,
    traceBasis, traceVector, swapSlots]
  funext j
  simp [Pi.single_apply]

private theorem swap_traceBasis_lower (i : Fin 3) :
    traceAction (swapPoint (K := K)) (traceBasis (some (true, i))) =
      -traceBasis (some (false, i)) := by
  apply Subtype.ext
  apply (Zorn.coordinates K).injective
  simp [traceAction, swapPoint, swapLinearEquiv, pointOfLinearEquiv,
    traceBasis, traceVector, swapSlots]
  funext j
  simp [Pi.single_apply]

open private zornOfBasis_first from LinearAlgebraicGroups.Composition.PeirceFrames in
private theorem exists_point_move_first :
    ∃ g : ZornPointGroup K, g.val.val (Zorn.first K) =
      Zorn.first K + (traceBasis (K := K) (some (false, 0))).val := by
  let x : Zorn K := Zorn.ofCoordinates (1, Pi.single (0 : Fin 3) 1, 0, 0)
  let e : Peirce.QuadricPoint (Zorn.norm K) := ⟨x, by
    change compositionTrace (Zorn.norm K) (Zorn.ofCoordinates (1, _, 0, 0)) = 1
    rw [Zorn.trace_formula, add_zero], by
    rw [Zorn.norm_formula]
    change zornNorm (1, Pi.single (0 : Fin 3) (1 : K), 0, 0) = 0
    simp [zornNorm]⟩
  have hn := Zorn.isOctonion K
  obtain ⟨hV, _, _, _⟩ := Peirce.projective_corners hn e
  let := hV
  let p : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  have hr := (Peirce.corner_rank hn e p).1
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  obtain ⟨b⟩ := Peirce.oriented_basis_exists hn e ⟨(Module.finBasis K _).reindex (finCongr hr)⟩
  let F := Peirce.zornOfBasis hn e b
  refine ⟨pointOfLinearEquiv F.toLinearEquiv F.map_one F.map_mul, ?_⟩
  change F.toLinearEquiv (Zorn.first K) = _
  rw [zornOfBasis_first]
  apply (Zorn.coordinates K).injective
  simp [e, x, traceBasis, traceVector, Zorn.first, ZornSpecification.first]
  constructor
  · funext i
    simp [Pi.single_apply]
  · rfl

private theorem trace_basis_mem_of_coord [Infinite K]
    (U : Submodule K (traceZero K)) (hU : ∀ g x, x ∈ U → traceAction g x ∈ U)
    (x : traceZero K) (hx : x ∈ U) (i : TraceIndex) (hi : traceCoordinates x i ≠ 0) :
    traceBasis i ∈ U := by
  obtain ⟨d, hd, hinj⟩ := exists_distinct_trace_weights (K := K)
  let e : traceZero K ≃ₗ[K] (TraceIndex → K) := traceCoordinates
  let f : Module.End K (TraceIndex → K) :=
    e.toLinearMap.comp ((traceAction (diagonalPoint d hd)).comp e.symm.toLinearMap)
  let W := U.comap e.symm.toLinearMap
  have hf (y : TraceIndex → K) (j : TraceIndex) : f y j = (traceWeight d j).val * y j := by
    change e (traceAction (diagonalPoint d hd) (e.symm y)) j = _
    rw [show e = traceCoordinates from rfl, diagonal_traceCoordinates, LinearEquiv.apply_symm_apply]
  have hW (y : TraceIndex → K) (hy : y ∈ W) : f y ∈ W := by
    change e.symm (e (traceAction (diagonalPoint d hd) (e.symm y))) ∈ U
    rw [LinearEquiv.symm_apply_apply]
    exact hU _ _ hy
  have H := coordinateVector_mem_of_action W f _ hinj hf hW (e x)
    (show e.symm (e x) ∈ U by simpa using hx) i hi
  exact H

private theorem all_vector_basis_mem (U : Submodule K (traceZero K))
    (hU : ∀ g x, x ∈ U → traceAction g x ∈ U)
    (b : Bool) (i : Fin 3) (hi : traceBasis (some (b, i)) ∈ U) :
    ∀ (c : Bool) (j : Fin 3), traceBasis (some (c, j)) ∈ U := by
  have rotate (c : Bool) (j : Fin 3) (hj : traceBasis (some (c, j)) ∈ U) :
      traceBasis (some (c, j + 1)) ∈ U := by
    rw [← rotate_traceBasis]
    exact hU _ _ hj
  have swap : traceBasis (some (!b, i)) ∈ U := by
    have h : traceAction (swapPoint (K := K)) (traceBasis (some (b, i))) =
        -traceBasis (some (!b, i)) := by
      cases b
      · exact swap_traceBasis i
      · exact swap_traceBasis_lower i
    have H := hU swapPoint _ hi
    rwa [h, neg_mem_iff] at H
  have along (c : Bool) (hc : traceBasis (some (c, i)) ∈ U) (j : Fin 3) :
      traceBasis (some (c, j)) ∈ U := by
    have h₁ := rotate c i hc
    have h₂ := rotate c (i + 1) h₁
    fin_cases i <;> fin_cases j
    all_goals first | exact hc | exact h₁ | exact h₂
  intro c j
  cases b <;> cases c
  · exact along false hi j
  · exact along true swap j
  · exact along false swap j
  · exact along true hi j

private theorem traceBasis_upper_val (i : Fin 3) :
    (traceBasis (K := K) (some (false, i))).val = Zorn.ofCoordinates (0, Pi.single i 1, 0, 0) := by
  apply (Zorn.coordinates K).injective
  simp [traceBasis, traceVector]
  constructor
  · funext j
    simp [Pi.single_apply]
  · rfl

private theorem traceBasis_lower_val (i : Fin 3) :
    (traceBasis (K := K) (some (true, i))).val = Zorn.ofCoordinates (0, 0, Pi.single i 1, 0) := by
  apply (Zorn.coordinates K).injective
  simp [traceBasis, traceVector]
  constructor
  · rfl
  · funext j
    simp [Pi.single_apply]

private theorem traceBasis_none_val :
    (traceBasis (K := K) none).val = (2 : K) • Zorn.first K - 1 := by
  apply (Zorn.coordinates K).injective
  change ((1, 0, 0, -1) : ZornCoordinates K) =
    (2 : K) • ((1, 0, 0, 0) : ZornCoordinates K) - ((1, 0, 0, 1) : ZornCoordinates K)
  simp [sub_eq_add_neg, show (2 : K) = 1 + 1 by norm_num, add_assoc]

private theorem traceAction_move_none (g : ZornPointGroup K) (hg :
    g.val.val (Zorn.first K) = Zorn.first K + (traceBasis (K := K) (some (false, 0))).val) :
    traceAction g (traceBasis none) = traceBasis none + (2 : K) • traceBasis (some (false, 0)) := by
  apply Subtype.ext
  change g.val.val (traceBasis none).val =
    (traceBasis none).val + (2 : K) • (traceBasis (some (false, 0))).val
  rw [traceBasis_none_val, map_sub, map_smul, point_one, hg, smul_add]
  abel

private theorem trace_submodule_eq_top (U : Submodule K (traceZero K))
    (hU : ∀ i, traceBasis i ∈ U) : U = ⊤ := by
  apply top_unique
  intro x _
  have hsum : x = ∑ i, traceCoordinates x i • traceBasis i := by
    apply (traceCoordinates (K := K)).injective
    simp only [map_sum, map_smul, traceBasis_coords]
    funext j
    simp [smul_eq_mul, Pi.single_apply]
  rw [hsum]
  exact Submodule.sum_mem _ (fun i _ => U.smul_mem _ (hU i))

private theorem trace_irreducible [Infinite K] (h2 : (2 : K) ≠ 0) :
    IrreduciblePointAction K (traceRepresentation (K := K)) := by
  refine ⟨⟨traceBasis none, 0, traceBasis_ne_zero none⟩, ?_⟩
  intro U hU
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  have hU' : ∀ g x, x ∈ U → traceAction g x ∈ U := hU
  obtain ⟨x, hx, hn⟩ := (Submodule.ne_bot_iff U).mp hbot
  have hi : ∃ i, traceCoordinates x i ≠ 0 := by
    by_contra! h
    apply hn
    apply (traceCoordinates (K := K)).injective
    ext i
    rw [map_zero]
    exact h i
  obtain ⟨i, hi⟩ := hi
  have hm := trace_basis_mem_of_coord U hU' x hx i hi
  have upper : ∃ b j, traceBasis (some (b, j)) ∈ U := by
    rcases i with _ | ⟨b, j⟩
    · obtain ⟨g, hg⟩ := exists_point_move_first (K := K)
      have H := hU' g _ hm
      rw [traceAction_move_none g hg] at H
      have hs := U.sub_mem H hm
      rw [add_sub_cancel_left] at hs
      refine ⟨false, 0, ?_⟩
      simpa [smul_smul, h2] using U.smul_mem (2 : K)⁻¹ hs
    · exact ⟨b, j, hm⟩
  obtain ⟨b, j, hj⟩ := upper
  have hall := all_vector_basis_mem U hU' b j hj
  -- A proper subspace containing both triples cannot omit the zero weight line:
  -- apply the scalar-slot swap after moving the idempotent, or use norm orthogonality.
  have hzero : traceBasis none ∈ U := by
    by_contra hn
    have hupper (x : traceZero K) (hx : x ∈ U) : traceCoordinates x none = 0 := by
      by_contra hi
      exact hn (trace_basis_mem_of_coord U hU' x hx none hi)
    have hp (x : traceZero K) (hx : x ∈ U) :
        (Zorn.norm K).polarBilin x.val (traceBasis (K := K) none).val = 0 := by
      obtain ⟨x, hx0⟩ := x
      obtain ⟨⟨a, p, q, b⟩, rfl⟩ := (Zorn.coordinates K).symm.surjective x
      have ha : a = 0 := hupper _ hx
      change compositionTrace (Zorn.norm K) (Zorn.ofCoordinates (a, p, q, b)) = 0 at hx0
      rw [Zorn.trace_formula, ha, zero_add] at hx0
      change (Zorn.norm K).polarBilin (Zorn.ofCoordinates (a, p, q, b))
        (Zorn.ofCoordinates (1, 0, 0, -1)) = 0
      rw [Zorn.polar_formula, ha, hx0]
      simp
    obtain ⟨g, hg⟩ := exists_point_move_first (K := K)
    let w : traceZero K := traceBasis (some (true, 0))
    have hw : w ∈ U := hall true 0
    have H := hp (traceAction g⁻¹ w) (hU' _ _ hw)
    have Hpres (x y : Zorn K) :
        (Zorn.norm K).polarBilin (g.val.val x) (g.val.val y) = (Zorn.norm K).polarBilin x y := by
      have E := congrArg (fun Q : QuadraticForm K (Zorn K) => Q.polarBilin x y)
        (point_norm_trace g).1
      simpa only [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply] using E
    have Hact := Hpres (traceAction g⁻¹ w).val (traceBasis (K := K) none).val
    have hg' : g.val.val (traceAction g⁻¹ w).val = w.val := by
      change (traceAction (g * g⁻¹) w).val = _
      rw [mul_inv_cancel]
      rfl
    have hnz : (Zorn.norm K).polarBilin w.val
        (traceBasis (K := K) (some (false, 0))).val = -1 := by
      rw [show w = traceBasis (some (true, 0)) from rfl, traceBasis_lower_val,
        traceBasis_upper_val, Zorn.polar_formula]
      simp [dotProduct, Fin.sum_univ_three]
    have hm : g.val.val (traceBasis (K := K) none).val =
        (traceBasis (K := K) none).val +
          (2 : K) • (traceBasis (K := K) (some (false, 0))).val :=
      congrArg Subtype.val (traceAction_move_none g hg)
    rw [hg', hm, map_add, map_smul, hp w hw, hnz, zero_add, smul_eq_mul, mul_neg_one, H] at Hact
    exact h2 (neg_eq_zero.mp Hact)
  exact trace_submodule_eq_top U fun i => by
    rcases i with _ | ⟨b, i⟩
    · exact hzero
    · exact hall b i

private theorem scalarTraceLine_iff (h2 : (2 : K) = 0) (x : traceZero K) :
    x ∈ scalarTraceLine K ↔ ∀ b i, traceCoordinates x (some (b, i)) = 0 := by
  change x.val ∈ scalarLine K ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩ b i
    change traceSlots (Zorn.coordinates K x.val) (some (b, i)) = 0
    rw [← ha]
    cases b <;> exact mul_zero a
  · intro h
    let a := traceCoordinates x none
    refine ⟨a, ?_⟩
    apply (Zorn.coordinates K).injective
    conv_rhs => rw [← (traceCoordinates (K := K)).symm_apply_apply x]
    change (a * 1, a • (0 : Fin 3 → K), a • (0 : Fin 3 → K), a * 1) =
      (a, (fun i => traceCoordinates x (some (false, i))),
        (fun i => traceCoordinates x (some (true, i))), -a)
    have hneg : -a = a := by
      apply neg_eq_iff_add_eq_zero.mpr
      rw [← two_mul, h2, zero_mul]
    simp [hneg, h]
    rfl

private theorem quotient_irreducible [Infinite K] (h2 : (2 : K) = 0) :
    IrreduciblePointAction K (quotientRepresentation (K := K)) := by
  let q := (scalarTraceLine K).mkQ
  have hq : Function.Surjective q := Submodule.Quotient.mk_surjective _
  refine ⟨⟨q (traceBasis (some (false, 0))), 0, ?_⟩, ?_⟩
  · intro h
    have hmem := (Submodule.Quotient.mk_eq_zero (p := scalarTraceLine K)).mp h
    have hh := (scalarTraceLine_iff h2 _).mp hmem false 0
    simp [traceBasis_coords] at hh
  · intro U hU
    let W := U.comap q
    have hW (g : ZornPointGroup K) (x : traceZero K) (hx : x ∈ W) :
        traceAction g x ∈ W := hU g (q x) hx
    by_cases h : ∀ x ∈ W, ∀ b i, traceCoordinates x (some (b, i)) = 0
    · left
      apply bot_unique
      intro y hy
      obtain ⟨x, rfl⟩ := hq y
      have hxW : x ∈ W := hy
      have hx := (scalarTraceLine_iff h2 x).mpr (h x hxW)
      exact (Submodule.mem_bot (R := K)).mpr ((Submodule.Quotient.mk_eq_zero (p := scalarTraceLine K)).mpr hx)
    · right
      push Not at h
      obtain ⟨x, hx, b, i, hi⟩ := h
      have hm := trace_basis_mem_of_coord W hW x hx (some (b, i)) hi
      have hall := all_vector_basis_mem W hW b i hm
      have hnone : traceBasis none ∈ W := by
        have hz : q (traceBasis none) = 0 := by
          apply (Submodule.Quotient.mk_eq_zero (p := scalarTraceLine K)).mpr
          apply (scalarTraceLine_iff h2 _).mpr
          intro b i
          simp [traceBasis_coords]
        change q (traceBasis none) ∈ U
        rw [hz]
        exact U.zero_mem
      have htop : W = ⊤ := trace_submodule_eq_top W fun i => by
        rcases i with _ | ⟨b, i⟩
        · exact hnone
        · exact hall b i
      apply top_unique
      intro y _
      obtain ⟨x, rfl⟩ := hq y
      exact (show x ∈ W by rw [htop]; exact Submodule.mem_top)

theorem splitGeometricRepresentation_conditional
    (_centre : LinearAlgebraicGroups.Specs.SchemeCentre.CentreFormula.{u}) :
    SplitGeometricRepresentation.{u} := by
  intro K _ _
  refine ⟨traceRepresentation, traceRepresentation_apply, ?_, ?_⟩
  · intro h
    exact ⟨trace_irreducible h, trace_representation_injective⟩
  · intro h
    exact ⟨scalar_mem_trace h, quotientRepresentation, quotientRepresentation_apply,
      quotient_irreducible h, quotient_representation_injective⟩

end GeometricRepresentation

section Centre

open Opposite
open LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open CharacterDescent (Character)
open DiagonalizableGroups (groupAlgebra)
open SchemeCentre (CentreFormula rootLattice)

private theorem groupAlgebraPoint_eq_one {K : Type u} [Field K]
    (M : Type u) [CommGroup M] [Subsingleton M]
    (S : TestAlgebra K) (x : Points (specGroup (groupAlgebra K M)).X S) : x = 1 := by
  let F := algSpec (CommRingCat.of K)
  let FF := algSpec.fullyFaithful (R := CommRingCat.of K)
  let A := CommAlgCat.of K (MonoidAlgebra K M)
  change (x : F.obj (op S) ⟶ F.obj (op A)) = _
  rw [← FF.map_preimage x, ← FF.map_preimage (1 : Points (specGroup (groupAlgebra K M)).X S)]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply MonoidAlgebra.algHom_ext _ (Subsingleton.elim _ _)
  intro m
  let f : MonoidAlgebra K M →ₐ[K] S := (FF.preimage x).unop.hom
  let g : MonoidAlgebra K M →ₐ[K] S :=
    (FF.preimage (1 : Points (specGroup (groupAlgebra K M)).X S)).unop.hom
  change f (MonoidAlgebra.single m 1) = g (MonoidAlgebra.single m 1)
  rw [Subsingleton.elim m 1, ← MonoidAlgebra.one_def]
  simp

private theorem trivial_centre_of_root_lattice {K : Type u} [Field K]
    (centre : CentreFormula.{u}) {G : AffineAlgebraicGroup K} (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hm : IsGeometricallyMaximal T) (hr : rootLattice T = ⊤) : HasTrivialCentre G.val := by
  obtain ⟨_, e, _, hZ, hP, _⟩ := centre G hG T hT hm
  intro S g hg
  obtain ⟨z, hz⟩ := (hP _ g).mp hg
  let : Subsingleton (Character T.group ⧸ rootLattice T) :=
    QuotientGroup.subsingleton_iff.mpr hr
  rw [← hz, groupAlgebraPoint_eq_one _ S z, MonObj.one_comp]

end Centre

section SplitPoints

open Opposite CategoryTheory.Limits
open PeirceSpecification (ZornIsomorphism SplitAutomorphism tensorMap)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open scoped TensorProduct

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}

/-- Split coordinates on the scalar extension used by the automorphism scheme. -/
private def splitCoordinates (F : ZornIsomorphism n) (S : Type u) [CommRing S] [Algebra R S] :
    Zorn S ≃ₗ[S] S ⊗[R] C :=
  (ZornSpecification.baseChange R S).symm.trans (F.toLinearEquiv.baseChange R S _ _)

omit [IsScalarTower R C C] [SMulCommClass R C C] in
private theorem splitCoordinates_one (F : ZornIsomorphism n)
    (S : Type u) [CommRing S] [Algebra R S] :
    splitCoordinates F S 1 = (1 : S ⊗[R] C) := by
  have h : (ZornSpecification.baseChange R S).symm 1 = (1 : S ⊗[R] Zorn R) :=
    (LinearEquiv.symm_apply_eq _).mpr Zorn.baseChange_one.symm
  simp only [splitCoordinates, LinearEquiv.trans_apply, h]
  change F.toLinearEquiv.baseChange R S _ _ (1 ⊗ₜ[R] (1 : Zorn R)) = 1 ⊗ₜ[R] (1 : C)
  rw [LinearEquiv.baseChange_tmul, F.map_one]

private theorem baseChange_mul_of_linearEquiv {D : Type*} [NonAssocRing D] [Module R D]
    [IsScalarTower R D D] [SMulCommClass R D D] (e : D ≃ₗ[R] C)
    (he : ∀ x y, e (x * y) = e x * e y)
    (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] D) :
    e.baseChange R S _ _ (x * y) = e.baseChange R S _ _ x * e.baseChange R S _ _ y := by
  induction x using TensorProduct.inductionOn with
  | tmul s d =>
    induction y using TensorProduct.inductionOn with
    | tmul t f => simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearEquiv.baseChange_tmul, he]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]

private theorem splitCoordinates_mul (F : ZornIsomorphism n) (S : Type u)
    [CommRing S] [Algebra R S] (x y : Zorn S) :
    splitCoordinates F S (x * y) = splitCoordinates F S x * splitCoordinates F S y := by
  simp only [splitCoordinates, LinearEquiv.trans_apply]
  rw [← baseChange_mul_of_linearEquiv F.toLinearEquiv F.map_mul]
  congr 1
  apply (ZornSpecification.baseChange R S).injective
  rw [LinearEquiv.apply_symm_apply, Zorn.baseChange_mul, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

omit [IsScalarTower R C C] [SMulCommClass R C C] in
private theorem baseChange_linear_natural {D : Type*} [AddCommGroup D] [Module R D]
    (e : D ≃ₗ[R] C) {S T : Type u} [CommRing S] [Algebra R S]
    [CommRing T] [Algebra R T] (f : S →ₐ[R] T) (x : S ⊗[R] D) :
    e.baseChange R T _ _ (tensorMap f x) = tensorMap f (e.baseChange R S _ _ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s z =>
    rw [show tensorMap f (s ⊗ₜ[R] z) = f s ⊗ₜ[R] z from rfl, LinearEquiv.baseChange_tmul,
      LinearEquiv.baseChange_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsScalarTower R C C] [SMulCommClass R C C] in
private theorem splitCoordinates_natural (F : ZornIsomorphism n) {S T : Type u}
    [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] (f : S →ₐ[R] T) (x : Zorn S) :
    splitCoordinates F T (ZornSpecification.mapCoordinates f.toRingHom x) =
      tensorMap f (splitCoordinates F S x) := by
  obtain ⟨y, rfl⟩ := (ZornSpecification.baseChange R S).surjective x
  rw [← Peirce.zorn_baseChange_naturality f y]
  simp only [splitCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact baseChange_linear_natural F.toLinearEquiv f y

private theorem octonionAlgebra_product (S : Type u) [CommRing S] [Algebra R S]
    (x y : S ⊗[R] C) :
    ((octonionAlgebra (R := R) (C := C)).product.baseChange S) x y = x * y := by
  induction x using TensorProduct.inductionOn with
  | tmul s c =>
    induction y using TensorProduct.inductionOn with
    | tmul t d =>
      simp [octonionAlgebra, LinearMap.BilinMap.baseChange_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, add_mul, hx, hy]

private theorem octonionAlgebra_preserves_iff (S : Type u) [CommRing S] [Algebra R S]
    (g : (Module.End S (S ⊗[R] C))ˣ) :
    g ∈ bilinearStabilizer (octonionAlgebra (R := R) (C := C)) S ↔
      g.val 1 = 1 ∧ ∀ x y, g.val (x * y) = g.val x * g.val y := by
  rw [mem_bilinearStabilizer]
  change (∀ e ∈ (some (1 : C) : Option C), g.val (1 ⊗ₜ[R] e) = 1 ⊗ₜ[R] e) ∧ _ ↔ _
  simp only [octonionAlgebra_product]
  constructor
  · rintro ⟨h, hm⟩
    exact ⟨h 1 rfl, hm⟩
  · rintro ⟨h, hm⟩
    exact ⟨fun e he => by cases he; exact h, hm⟩

set_option maxRecDepth 2048 in
private def splitAutomorphismsEquiv (F : ZornIsomorphism n) (S : Type u)
    [CommRing S] [Algebra R S] :
    (bilinearStabilizer (octonionAlgebra (R := R) (C := C)) S) ≃ SplitAutomorphism S := by
  let E := splitCoordinates F S
  let h₁ : E 1 = 1 := splitCoordinates_one F S
  let hm := splitCoordinates_mul F S
  let he (x y : S ⊗[R] C) : E.symm (x * y) = E.symm x * E.symm y := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply, hm, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let he₁ : E.symm 1 = 1 := (LinearEquiv.symm_apply_eq _).mpr h₁.symm
  refine
    { toFun := fun g => ⟨(E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv g.val)).trans E.symm, ?_⟩
      invFun := fun g => ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv ((E.symm.trans g.val).trans E), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨hg₁, hgm⟩ := (octonionAlgebra_preserves_iff S _).mp g.property
    constructor
    · change E.symm (g.val.val (E 1)) = 1
      rw [h₁, hg₁, he₁]
    · intro x y
      change E.symm (g.val.val (E (x * y))) = E.symm (g.val.val (E x)) * E.symm (g.val.val (E y))
      rw [hm, hgm, he]
  · apply (octonionAlgebra_preserves_iff S _).mpr
    constructor
    · change E (g.val (E.symm 1)) = 1
      rw [he₁, g.property.1, h₁]
    · intro x y
      change E (g.val (E.symm (x * y))) = E (g.val (E.symm x)) * E (g.val (E.symm y))
      rw [he, g.property.2, hm]
  · intro g
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    change E (E.symm (g.val.val (E (E.symm x)))) = g.val.val x
    simp
  · intro g
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change E.symm (E (g.val (E.symm (E x)))) = g.val x
    simp

private def splitSchemePoints (F : ZornIsomorphism n) (A : AutomorphismGroup R C)
    (S : CommAlgCat.{u} R) :
    ((schemePoints R).obj A.group).obj S ≃ SplitAutomorphism S :=
  (A.subgroupPoints S).toEquiv.trans (splitAutomorphismsEquiv F S)

private theorem subgroup_scalarChange (A : AutomorphismGroup R C)
    {S T : CommAlgCat.{u} R} (f : S ⟶ T) (g : ((schemePoints R).obj A.group).obj S)
    (x : S ⊗[R] C) :
    (A.subgroupPoints T (((schemePoints R).obj A.group).map f g)).val.val (tensorMap f.hom x) =
      tensorMap f.hom ((A.subgroupPoints S g).val.val x) := by
  rw [← A.evaluatesInclusion, ← A.evaluatesInclusion]
  have H : ((schemePoints R).obj A.generalLinear).map f
        (((schemePoints R).map A.inclusion).app S g) =
      ((schemePoints R).map A.inclusion).app T (((schemePoints R).obj A.group).map f g) :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom (((schemePoints R).map A.inclusion).naturality f)) g
  rw [← H]
  exact A.scalarChange f _ x

private theorem splitSchemePoints_natural (F : ZornIsomorphism n) (A : AutomorphismGroup R C)
    {S T : CommAlgCat.{u} R} (f : S ⟶ T) (g : ((schemePoints R).obj A.group).obj S)
    (x : Zorn S) :
    (splitSchemePoints F A T (((schemePoints R).obj A.group).map f g)).val
        (ZornSpecification.mapCoordinates f.hom.toRingHom x) =
      ZornSpecification.mapCoordinates f.hom.toRingHom ((splitSchemePoints F A S g).val x) := by
  apply (splitCoordinates F T).injective
  change splitCoordinates F T ((splitCoordinates F T).symm
    ((A.subgroupPoints T (((schemePoints R).obj A.group).map f g)).val.val
      (splitCoordinates F T (ZornSpecification.mapCoordinates f.hom.toRingHom x)))) =
    splitCoordinates F T (ZornSpecification.mapCoordinates f.hom.toRingHom
      ((splitCoordinates F S).symm ((A.subgroupPoints S g).val.val (splitCoordinates F S x))))
  rw [LinearEquiv.apply_symm_apply, splitCoordinates_natural, splitCoordinates_natural,
    subgroup_scalarChange, LinearEquiv.apply_symm_apply]

end SplitPoints

section AffineComparison

open Opposite CategoryTheory.Limits
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)

variable {R : Type u} [CommRing R]

private abbrev affineScheme (R : Type u) [CommRing R] (D : Type u)
    [CommRing D] [Algebra R D] : RingScheme R :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R D))

private abbrev ringPoint (X : RingScheme R) (S : CommAlgCat.{u} R) :=
  (algSpec (CommRingCat.of R)).obj (op S) ⟶ X

private def affinePointEquiv {D : Type u} [CommRing D] [Algebra R D]
    {X : RingScheme R} (i : affineScheme R D ≅ X) (S : CommAlgCat.{u} R) :
    (D →ₐ[R] S) ≃ ringPoint X S where
  toFun f := (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op ≫ i.hom
  invFun x := ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage (x ≫ i.inv)).unop.hom
  left_inv f := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Functor.FullyFaithful.preimage_map]
    rfl
  right_inv x := by
    change (algSpec (CommRingCat.of R)).map
      ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage (x ≫ i.inv)) ≫ i.hom = x
    simp

private theorem affinePointEquiv_natural {D : Type u} [CommRing D] [Algebra R D]
    {X : RingScheme R} (i : affineScheme R D ≅ X) {S T : CommAlgCat.{u} R}
    (f : D →ₐ[R] S) (g : S ⟶ T) :
    affinePointEquiv i T (g.hom.comp f) =
      (algSpec (CommRingCat.of R)).map g.op ≫ affinePointEquiv i S f := by
  change (algSpec (CommRingCat.of R)).map ((CommAlgCat.ofHom f ≫ g).op) ≫ i.hom = _
  rw [op_comp, Functor.map_comp, Category.assoc]
  rfl

private theorem iso_of_affine_points {D E : Type u} [CommRing D] [CommRing E]
    [Algebra R D] [Algebra R E] (e : ∀ (S : CommAlgCat.{u} R),
      (D →ₐ[R] S) ≃ (E →ₐ[R] S))
    (h : ∀ (S T : CommAlgCat.{u} R) (f : D →ₐ[R] S) (g : S ⟶ T),
      e T (g.hom.comp f) = g.hom.comp (e S f)) :
    ∃ i : E ≃ₐ[R] D, ∀ (S : CommAlgCat.{u} R) (f : D →ₐ[R] S),
      e S f = f.comp i.toAlgHom := by
  let a := e (CommAlgCat.of R D) (AlgHom.id R D)
  let b := (e (CommAlgCat.of R E)).symm (AlgHom.id R E)
  have ha (S : CommAlgCat.{u} R) (f : D →ₐ[R] S) : e S f = f.comp a := by
    have hs := h (CommAlgCat.of R D) S (AlgHom.id R D) (CommAlgCat.ofHom f)
    change e S (f.comp (AlgHom.id R D)) = f.comp a at hs
    simpa only [AlgHom.comp_id] using hs
  have hb : b.comp a = AlgHom.id R E := (ha _ b).symm.trans (Equiv.apply_symm_apply _ _)
  have hc : a.comp b = AlgHom.id R D := by
    apply (e (CommAlgCat.of R D)).injective
    rw [ha, AlgHom.comp_assoc, hb, AlgHom.comp_id]
  exact ⟨AlgEquiv.ofAlgHom a b hc hb, ha⟩

private theorem affineRingPoints_ext {X Y : RingScheme R} (hX : IsAffine X.left)
    {a b : X ⟶ Y}
    (h : ∀ (S : CommAlgCat.{u} R) (x : ringPoint X S), x ≫ a = x ≫ b) : a = b := by
  obtain ⟨D, ⟨i⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  exact (cancel_epi i.hom).mp (h D.unop i.hom)

private theorem morphism_of_ring_points {X Y : RingScheme R} (hX : IsAffine X.left)
    (F : ∀ (S : CommAlgCat.{u} R), ringPoint X S → ringPoint Y S)
    (h : ∀ {S T : CommAlgCat.{u} R} (f : S ⟶ T) (x : ringPoint X S),
      F T ((algSpec (CommRingCat.of R)).map f.op ≫ x) =
        (algSpec (CommRingCat.of R)).map f.op ≫ F S x) :
    ∃ a : X ⟶ Y, ∀ (S : CommAlgCat.{u} R) (x : ringPoint X S), x ≫ a = F S x := by
  obtain ⟨D, ⟨i⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  refine ⟨i.inv ≫ F D.unop i.hom, fun S x => ?_⟩
  let ff := algSpec.fullyFaithful (R := CommRingCat.of R)
  let f := ff.preimage (x ≫ i.inv)
  have hf : (algSpec (CommRingCat.of R)).map f = x ≫ i.inv := ff.map_preimage _
  have hx : (algSpec (CommRingCat.of R)).map f ≫ i.hom = x := by simp [hf]
  have hh := h f.unop i.hom
  change F S ((algSpec (CommRingCat.of R)).map f ≫ i.hom) = _ at hh
  rw [hx] at hh
  rw [← Category.assoc, ← hf]
  exact hh.symm

end AffineComparison

section SplitPresentation

open Opposite CategoryTheory.Limits
open PeirceSpecification (ZornIsomorphism SplitAutomorphism SplitQuadricRing SplitEvaluationOver)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)
open private zornBasis map_zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}

private theorem splitPresentation (F : ZornIsomorphism n) (A : AutomorphismGroup R C) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D)
      (ρ : SplitQuadricRing R →ₐ[R] D) (_a : affineScheme R D ≅ A.group.X),
      Algebra.FinitePresentation R D ∧
      SplitEvaluationOver.{u, u} R (SplitQuadricRing R) D ρ := by
  obtain ⟨D, _, _, ρ, hD, hρ⟩ := Peirce.split_evaluation_scheme.{u, u} R
  obtain ⟨e, he, E, heval, hmap⟩ := hρ
  obtain ⟨B, ⟨b⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr A.groupAffine
  let P (S : CommAlgCat.{u} R) : (B.unop →ₐ[R] S) ≃ SplitAutomorphism S :=
    (affinePointEquiv b S).trans (splitSchemePoints F A S)
  let Q (S : CommAlgCat.{u} R) : (B.unop →ₐ[R] S) ≃ (D →ₐ[R] S) :=
    (P S).trans (E S).symm
  have hQ (S T : CommAlgCat.{u} R) (f : B.unop →ₐ[R] S) (g : S ⟶ T) :
      Q T (g.hom.comp f) = g.hom.comp (Q S f) := by
    apply (E T).injective
    have h₁ : E T (Q T (g.hom.comp f)) = P T (g.hom.comp f) := (E T).apply_symm_apply _
    have h₂ : E S (Q S f) = P S f := (E S).apply_symm_apply _
    rw [h₁]
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply (zornBasis T).ext
    intro i
    change (P T (g.hom.comp f)).val (zornBasis T i) =
      (E T (g.hom.comp (Q S f))).val (zornBasis T i)
    rw [← map_zornBasis g.hom.toRingHom i, hmap S T (Q S f) g.hom, h₂]
    change (splitSchemePoints F A T (affinePointEquiv b T (g.hom.comp f))).val
        (ZornSpecification.mapCoordinates g.hom.toRingHom (zornBasis S i)) =
      ZornSpecification.mapCoordinates g.hom.toRingHom
        ((splitSchemePoints F A S (affinePointEquiv b S f)).val (zornBasis S i))
    rw [affinePointEquiv_natural]
    exact splitSchemePoints_natural F A g _ _
  obtain ⟨i, _⟩ := iso_of_affine_points Q hQ
  let j : CommAlgCat.of R D ≅ B.unop :=
    { hom := CommAlgCat.ofHom i.toAlgHom
      inv := CommAlgCat.ofHom i.symm.toAlgHom
      hom_inv_id := by apply CommAlgCat.hom_ext; exact i.symm_comp
      inv_hom_id := by apply CommAlgCat.hom_ext; ext x; exact i.apply_symm_apply x }
  exact ⟨D, inferInstance, inferInstance, ρ,
    (algSpec (CommRingCat.of R)).mapIso j.op.symm ≪≫ b, hD, e, he, E, heval, hmap⟩

end SplitPresentation

section SplitFrameCharts

open Opposite CategoryTheory.Limits
open PeirceSpecification (SplitAutomorphism SplitQuadricRing SL3Ring SplitEvaluationOver
  QuadricPoint RepresentsQuadric tensorMap)
open Algebra.TensorProduct (includeLeft includeRight productMap)
open scoped TensorProduct
open private zornBasis map_zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

variable {R : Type u} [CommRing R]

private def awayHomEquiv {D S : Type u} [CommRing D] [CommRing S] [Algebra R D] [Algebra R S]
    (r : D) :
    (Localization.Away r →ₐ[R] S) ≃ {f : D →ₐ[R] S // IsUnit (f r)} where
  toFun f := ⟨f.comp (IsScalarTower.toAlgHom R D (Localization.Away r)), by
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).map f⟩
  invFun f := IsLocalization.Away.liftAlgHom r f.property
  left_inv f := by
    apply IsLocalization.algHom_ext (Submonoid.powers r)
    ext x
    have hu : IsUnit ((f.comp (IsScalarTower.toAlgHom R D (Localization.Away r))) r) :=
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).map f
    exact IsLocalization.Away.lift_eq r hu x
  right_inv f := by
    apply Subtype.ext
    ext x
    exact IsLocalization.Away.lift_eq r f.property x

private def tensorHomEquiv {B C S : Type u} [CommRing B] [CommRing C] [CommRing S]
    [Algebra R B] [Algebra R C] [Algebra R S] :
    (B ⊗[R] C →ₐ[R] S) ≃ (B →ₐ[R] S) × (C →ₐ[R] S) where
  toFun f := (f.comp includeLeft, f.comp includeRight)
  invFun p := productMap p.1 p.2
  left_inv f := by
    apply Algebra.TensorProduct.ext
    · rw [Algebra.TensorProduct.productMap_left]
    · change (productMap (f.comp includeLeft) (f.comp includeRight)).comp includeRight = _
      rw [Algebra.TensorProduct.productMap_right]
      rfl
  right_inv p := Prod.ext (Algebra.TensorProduct.productMap_left _ _)
    (Algebra.TensorProduct.productMap_right _ _)

variable {A D : Type u} [CommRing A] [CommRing D] [Algebra R A] [Algebra R D]
  (ρ : A →ₐ[R] D) (r : A)

private theorem compatibleMapImage_isUnit {S : Type u} [CommRing S] [Algebra R S]
    (p : Σ (a : Localization.Away r →ₐ[R] S), {f : D →ₐ[R] S //
        f.comp ρ = a.comp (IsScalarTower.toAlgHom R A (Localization.Away r))}) :
    IsUnit (p.2.val (ρ r)) := by
  have hp := AlgHom.congr_fun p.2.property r
  change p.2.val (ρ r) = p.1 (algebraMap A (Localization.Away r) r) at hp
  rw [hp]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).map p.1

private def chartCompatibleMapsEquiv (S : Type u) [CommRing S] [Algebra R S] :
    (Localization.Away (ρ r) →ₐ[R] S) ≃
      (Σ (a : Localization.Away r →ₐ[R] S), {f : D →ₐ[R] S //
        f.comp ρ = a.comp (IsScalarTower.toAlgHom R A (Localization.Away r))}) where
  toFun d := ⟨d.comp (IsLocalization.Away.mapₐ _ _ ρ r), (awayHomEquiv (ρ r) d).val, by
    ext x
    change d (algebraMap D (Localization.Away (ρ r)) (ρ x)) =
      d (IsLocalization.Away.mapₐ _ _ ρ r (algebraMap A (Localization.Away r) x))
    simp [IsLocalization.Away.map]⟩
  invFun p := (awayHomEquiv (ρ r)).symm ⟨p.2.val, compatibleMapImage_isUnit ρ r p⟩
  left_inv d := (awayHomEquiv (ρ r)).symm_apply_apply d
  right_inv p := by
    let z := (awayHomEquiv (ρ r)).symm ⟨p.2.val, compatibleMapImage_isUnit ρ r p⟩
    have hd : (awayHomEquiv (ρ r) z).val = p.2.val :=
      congrArg Subtype.val (Equiv.apply_symm_apply (awayHomEquiv (ρ r)) _)
    have hfst : z.comp (IsLocalization.Away.mapₐ _ _ ρ r) = p.1 := by
      apply IsLocalization.algHom_ext (Submonoid.powers r)
      apply AlgHom.ext
      intro x
      change z (IsLocalization.Away.mapₐ _ _ ρ r (algebraMap A (Localization.Away r) x)) =
        p.1 (algebraMap A (Localization.Away r) x)
      simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
        IsLocalization.map_eq]
      exact (AlgHom.congr_fun (congrArg (fun h : D →ₐ[R] S => h.comp ρ) hd) x).trans
        (AlgHom.congr_fun p.2.property x)
    refine Sigma.ext hfst ?_
    exact (Subtype.heq_iff_coe_eq (fun f => by
      change (f.comp ρ = (z.comp (IsLocalization.Away.mapₐ _ _ ρ r)).comp
        (IsScalarTower.toAlgHom R A (Localization.Away r))) ↔
        f.comp ρ = p.1.comp (IsScalarTower.toAlgHom R A (Localization.Away r))
      rw [hfst])).mpr hd

private theorem chartCompatibleMapsEquiv_natural {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (d : Localization.Away (ρ r) →ₐ[R] S) :
    (chartCompatibleMapsEquiv ρ r T (g.comp d)).1 = g.comp (chartCompatibleMapsEquiv ρ r S d).1 ∧
    (chartCompatibleMapsEquiv ρ r T (g.comp d)).2.val =
      g.comp (chartCompatibleMapsEquiv ρ r S d).2.val :=
  ⟨AlgHom.comp_assoc _ _ _, AlgHom.comp_assoc _ _ _⟩

/-- The coordinate ring on each principal open in the frame bundle is the tensor product
of the localized quadric and the determinant-one matrix ring. -/
private theorem splitFrameChartAlgebra (h : SplitEvaluationOver.{u, u} R A D ρ)
    (p : PrimeSpectrum A) :
    ∃ r : A, r ∉ p.asIdeal ∧
      ∃ q : Localization.Away r ⊗[R] SL3Ring R ≃ₐ[R] Localization.Away (ρ r),
        q.toAlgHom.comp includeLeft = IsLocalization.Away.mapₐ _ _ ρ r := by
  classical
  obtain ⟨e, he, E, heval, hmap⟩ := h
  obtain ⟨r, hr, b, hb⟩ := Peirce.split_frame_charts.{u, u} R A e p
  choose Z hZ using hb
  let B := Localization.Away r
  let j := IsScalarTower.toAlgHom R A B
  let e' := Peirce.mapPoint j e
  have hFst (S : Type u) [CommRing S] [Algebra R S] (a : B →ₐ[R] S)
      (g : Matrix.SpecialLinearGroup (Fin 3) S) :
      (Z S a g).val.val (ZornSpecification.first S) =
        ZornSpecification.baseChange R S (tensorMap a e'.val) := by
    exact (Z S a g).property.trans
      (congrArg (ZornSpecification.baseChange R S) (Peirce.tensorMap_comp j a e.val))
  have hZMap := Peirce.split_frame_chart_naturality.{u, u} R B e' b
    (fun S _ _ a g => (Z S a g).val) hFst hZ
  obtain ⟨_, L, hL⟩ := Peirce.special_linear_three_scheme.{u, u} R
  let Q (S : CommAlgCat.{u} R) (a : B →ₐ[R] S) :
      {f : D →ₐ[R] S // f.comp ρ = a.comp j} ≃
        {F : SplitAutomorphism S // F.val (ZornSpecification.first S) =
          ZornSpecification.baseChange R S (tensorMap (a.comp j) e.val)} :=
    (E S).subtypeEquiv (fun f => by
      rw [heval S f]
      constructor
      · intro hf
        rw [hf]
      · intro hf
        exact (he S).1 ((ZornSpecification.baseChange R S).injective hf))
  let U (S : CommAlgCat.{u} R) (a : B →ₐ[R] S) :=
    (Q S a).trans ((Z S a).symm.trans (L S).symm)
  let V (S : CommAlgCat.{u} R) : (Localization.Away (ρ r) →ₐ[R] S) ≃
      (B ⊗[R] SL3Ring R →ₐ[R] S) :=
    (chartCompatibleMapsEquiv ρ r S).trans
      (((Equiv.sigmaCongrRight (U S)).trans (Equiv.sigmaEquivProd _ _)).trans
        tensorHomEquiv.symm)
  refine ⟨r, hr, ?_⟩
  have hV (S T : CommAlgCat.{u} R) (f : Localization.Away (ρ r) →ₐ[R] S) (g : S ⟶ T) :
      V T (g.hom.comp f) = g.hom.comp (V S f) := by
    let d := chartCompatibleMapsEquiv ρ r S f
    let d' := chartCompatibleMapsEquiv ρ r T (g.hom.comp f)
    have hd := chartCompatibleMapsEquiv_natural ρ r g.hom f
    change d'.1 = g.hom.comp d.1 ∧ d'.2.val = g.hom.comp d.2.val at hd
    have hsecond : U T d'.1 d'.2 = g.hom.comp (U S d.1 d.2) := by
      apply (L T).injective
      let s := (Z S d.1).symm (Q S d.1 d.2)
      have hs : Z S d.1 s = Q S d.1 d.2 := Equiv.apply_symm_apply _ _
      have hs' : (Z S d.1 s).val = E S d.2.val := congrArg Subtype.val hs
      change (L T) ((L T).symm ((Z T d'.1).symm (Q T d'.1 d'.2))) =
        L T (g.hom.comp ((L S).symm s))
      rw [Equiv.apply_symm_apply, hL S T ((L S).symm s) g.hom, Equiv.apply_symm_apply]
      apply (Z T d'.1).injective
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      apply Subtype.ext
      apply LinearEquiv.toLinearMap_injective
      apply (zornBasis T).ext
      intro i
      change (E T d'.2.val).val (zornBasis T i) =
        (Z T d'.1 (Matrix.SpecialLinearGroup.map g.hom.toRingHom s)).val.val (zornBasis T i)
      rw [← map_zornBasis g.hom.toRingHom i, hd.2, hmap S T d.2.val g.hom, hd.1,
        hZMap S T d.1 g.hom s, hs']
    change productMap d'.1 (U T d'.1 d'.2) =
      g.hom.comp (productMap d.1 (U S d.1 d.2))
    rw [hsecond, hd.1]
    apply Algebra.TensorProduct.ext
    · rw [Algebra.TensorProduct.productMap_left, AlgHom.comp_assoc,
        Algebra.TensorProduct.productMap_left]
    · change (productMap (g.hom.comp d.1) (g.hom.comp (U S d.1 d.2))).comp includeRight =
        (g.hom.comp (productMap d.1 (U S d.1 d.2))).comp includeRight
      rw [Algebra.TensorProduct.productMap_right, AlgHom.comp_assoc,
        Algebra.TensorProduct.productMap_right]
  obtain ⟨q, hq⟩ := iso_of_affine_points (R := R) (D := Localization.Away (ρ r))
    (E := B ⊗[R] SL3Ring R) V hV
  refine ⟨q, ?_⟩
  have eq := hq (CommAlgCat.of R (Localization.Away (ρ r))) (AlgHom.id R _)
  rw [AlgHom.id_comp] at eq
  rw [← eq]
  change (productMap _ _).comp includeLeft = _
  rw [Algebra.TensorProduct.productMap_left]
  exact AlgHom.id_comp _

end SplitFrameCharts

section SplitSmoothness

open Opposite
open PeirceSpecification (ZornIsomorphism SplitQuadricRing SL3Ring SplitEvaluationOver)
open scoped TensorProduct

variable {R : Type u} [CommRing R]

private theorem splitAutomorphismRing_smooth
    {D : Type u} [CommRing D] [Algebra R D] [Algebra.FinitePresentation R D]
    {ρ : SplitQuadricRing R →ₐ[R] D}
    (h : SplitEvaluationOver.{u, u} R (SplitQuadricRing R) D ρ) :
    Algebra.Smooth R D := by
  obtain ⟨_, _, hs⟩ := Peirce.split_quadric_scheme.{u, u} R
  let : Algebra.Smooth R (SplitQuadricRing R) := hs
  let : Algebra.Smooth R (SL3Ring R) := (Peirce.special_linear_three_scheme.{u, u} R).1
  refine ⟨?_, inferInstance⟩
  apply (Algebra.smoothLocus_eq_univ_iff (R := R) (A := D)).mp
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨r, hr, e, _⟩ := splitFrameChartAlgebra (ρ := ρ) h (PrimeSpectrum.comap ρ.toRingHom p)
  let : Algebra.Smooth (SplitQuadricRing R) (Localization.Away r) :=
    Algebra.Smooth.of_isLocalization_Away r
  let : Algebra.Smooth R (Localization.Away r) :=
    Algebra.Smooth.comp R (SplitQuadricRing R) (Localization.Away r)
  let : Algebra.Smooth R (Localization.Away r ⊗[R] SL3Ring R) :=
    Algebra.Smooth.comp R (Localization.Away r) _
  have hChart : Algebra.Smooth R (Localization.Away (ρ r)) := Algebra.Smooth.of_equiv (A := Localization.Away r ⊗[R] SL3Ring R) e
  exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := R) (A := D)).mpr hChart hr

private theorem splitAutomorphismScheme_smooth
    {C : Type v} [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}
    (F : ZornIsomorphism n) (A : AutomorphismGroup R C) :
    Smooth A.group.X.hom := by
  obtain ⟨D, _, _, ρ, i, hD, hρ⟩ := splitPresentation F A
  let : Algebra.FinitePresentation R D := hD
  have hs := splitAutomorphismRing_smooth hρ
  have h : Smooth ((affineScheme R D).hom) := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R D)))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr hs)
  have : IsIso i.inv.left := by
    change IsIso ((Over.forget _).map i.inv)
    infer_instance
  have : Smooth i.inv.left := inferInstance
  have : Smooth (i.inv.left ≫ (affineScheme R D).hom) := inferInstance
  exact (Over.w i.inv) ▸ this

end SplitSmoothness

section ScalarExtension

open Opposite CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)
open PeirceSpecification (tensorMap)
open scoped TensorProduct

variable {R : Type u} [CommRing R] {K : Type u} [CommRing K] [Algebra R K]

private abbrev scalarSpecMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

private def forgetScalarsMap {S T : CommAlgCat.{u} K} (f : S ⟶ T) :
    forgetScalars (R := R) S ⟶ forgetScalars (R := R) T :=
  ConcreteCategory.ofHom (C := CommAlgCat R)
    ({ toRingHom := f.hom.toRingHom
       commutes' := fun a => f.hom.commutes (algebraMap R K a) } :
    (forgetScalars (R := R) S) →ₐ[R] (forgetScalars (R := R) T))

private theorem forgetFiberPoint_bijective (X : RingScheme R) (S : CommAlgCat.{u} K) :
    Function.Bijective (forgetFiberPoint X S) := by
  constructor
  · intro p q h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg (fun a : ringPoint X (forgetScalars S) => a.left) h
    · exact (Over.w p).trans (Over.w q).symm
  · intro p
    let T := affineScheme K S
    have hp : p.left ≫ X.hom = T.hom ≫ scalarSpecMap (R := R) (K := K) := by
      rw [Over.w p]
      exact Spec.map_comp (CommRingCat.ofHom (algebraMap R K))
        (CommRingCat.ofHom (algebraMap K S))
    refine ⟨Over.homMk (pullback.lift p.left T.hom hp) (pullback.lift_snd ..), ?_⟩
    apply Over.OverMorphism.ext
    exact pullback.lift_fst ..

private theorem forgetFiberPoint_comp {X Y : RingScheme R} (f : X ⟶ Y)
    (S : CommAlgCat.{u} K) (x : ringPoint ((scalarExtension K).obj X) S) :
    forgetFiberPoint Y S (x ≫ (scalarExtension K).map f) = forgetFiberPoint X S x ≫ f := by
  apply Over.OverMorphism.ext
  change (x.left ≫ ((scalarExtension K).map f).left) ≫ pullback.fst Y.hom (scalarSpecMap) =
    (x.left ≫ pullback.fst X.hom (scalarSpecMap)) ≫ f.left
  simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]

private theorem forgetFiberPoint_natural (X : RingScheme R)
    {S T : CommAlgCat.{u} K} (f : S ⟶ T)
    (x : ringPoint ((scalarExtension K).obj X) S) :
    forgetFiberPoint X T ((algSpec (CommRingCat.of K)).map f.op ≫ x) =
      (algSpec (CommRingCat.of R)).map (forgetScalarsMap f).op ≫ forgetFiberPoint X S x := by
  apply Over.OverMorphism.ext
  simp only [forgetFiberPoint, Over.homMk_left, Over.comp_left]
  rfl

private theorem forgetFiberPoint_mul (G : Grp (RingScheme R)) (S : CommAlgCat.{u} K)
    (p q : ((schemePoints K).obj ((scalarExtensionGroup K).obj G)).obj S) :
    forgetFiberPoint G.X S (p * q) = forgetFiberPoint G.X S p * forgetFiberPoint G.X S q := by
  let F := scalarExtension (R := R) K
  let p' : ringPoint (F.obj G.X) S := p
  let q' : ringPoint (F.obj G.X) S := q
  let x := forgetFiberPoint G.X S p'
  let y := forgetFiberPoint G.X S q'
  let t : ringPoint (F.obj (G.X ⊗ G.X)) S := lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X
  have hxy : forgetFiberPoint (G.X ⊗ G.X) S t = lift x y := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← forgetFiberPoint_comp (fst G.X G.X), lift_fst]
      change forgetFiberPoint G.X S
        ((lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X) ≫ F.map (fst G.X G.X)) = x
      rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
    · rw [← forgetFiberPoint_comp (snd G.X G.X), lift_snd]
      change forgetFiberPoint G.X S
        ((lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X) ≫ F.map (snd G.X G.X)) = y
      rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
  change forgetFiberPoint G.X S (lift p' q' ≫
      (Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X])) = lift x y ≫ μ[G.X]
  rw [← Category.assoc]
  change forgetFiberPoint G.X S (t ≫ F.map μ[G.X]) = _
  rw [forgetFiberPoint_comp, hxy]

private def forgetFiberPointMulEquiv (G : Grp (RingScheme R)) (S : CommAlgCat.{u} K) :
    ((schemePoints K).obj ((scalarExtensionGroup K).obj G)).obj S ≃*
      ((schemePoints R).obj G).obj (forgetScalars S) where
  toEquiv := Equiv.ofBijective _ (forgetFiberPoint_bijective G.X S)
  map_mul' := forgetFiberPoint_mul G S

private theorem scalarExtension_isClosedImmersion {X Y : RingScheme R} (f : X ⟶ Y)
    [IsClosedImmersion f.left] :
    IsClosedImmersion ((scalarExtension (R := R) K).map f).left := by
  let m := scalarSpecMap (R := R) (K := K)
  have h : IsPullback ((scalarExtension (R := R) K).map f).left (pullback.fst X.hom m)
      (pullback.fst Y.hom m) f.left := by
    change IsPullback ((Over.pullback m).map f).left (pullback.fst X.hom m)
      (pullback.fst Y.hom m) f.left
    apply IsPullback.of_right (h₁₂ := pullback.snd Y.hom m) (h₂₂ := Y.hom) (v₁₃ := m)
    · simp only [Over.pullback_map_left, pullback.lift_snd, Over.w f]
      exact (IsPullback.of_hasPullback X.hom m).flip
    · simp only [Over.pullback_map_left, pullback.lift_fst]
    · exact (IsPullback.of_hasPullback Y.hom m).flip
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip ‹_›

end ScalarExtension

section TensorExtension

open Opposite CategoryTheory.Limits
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open PeirceSpecification (tensorMap)
open TensorProduct.AlgebraTensorModule (cancelBaseChange cancelBaseChange_tmul)
open scoped TensorProduct

variable {R : Type u} [CommRing R] {K : Type u} [CommRing K] [Algebra R K]
  {C : Type v} [NonAssocRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]

local notation "↓" S => (forgetScalars (R := R) S)

/-- Cancel the intermediate scalar extension in a test algebra of the new base ring. -/
private def tensorScalarExtension (S : CommAlgCat.{u} K) :
    S ⊗[K] (K ⊗[R] C) ≃ₗ[S] (↓S) ⊗[R] C := by
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  exact cancelBaseChange R K S S C

omit [IsScalarTower R C C] [SMulCommClass R C C] in
private theorem cancelBaseChange_natural {S T : Type u} [CommRing S] [CommRing T]
    [Algebra K S] [Algebra K T] [Algebra R S] [Algebra R T]
    [IsScalarTower R K S] [IsScalarTower R K T] (f : S →ₐ[K] T)
    (x : S ⊗[K] (K ⊗[R] C)) :
    cancelBaseChange R K T T C (tensorMap f x) =
      tensorMap (f.restrictScalars R) (cancelBaseChange R K S S C x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s c =>
    induction c using TensorProduct.inductionOn with
    | tmul k c =>
      simp only [Peirce.tensorMap_tmul, cancelBaseChange_tmul,
        AlgHom.restrictScalars_apply, map_smul]
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

set_option backward.isDefEq.respectTransparency false in
private theorem cancelBaseChange_mul {S : Type u} [CommRing S]
    [Algebra K S] [Algebra R S] [IsScalarTower R K S]
    (x y : S ⊗[K] (K ⊗[R] C)) :
    cancelBaseChange R K S S C (x * y) =
      cancelBaseChange R K S S C x * cancelBaseChange R K S S C y := by
  have add_right (a b c : S ⊗[K] (K ⊗[R] C)) :
      a * (b + c) = a * b + a * c :=
    (Algebra.TensorProduct.mul (R := K) a).map_add b c
  have add_left (a b c : S ⊗[K] (K ⊗[R] C)) :
      (a + b) * c = a * c + b * c :=
    LinearMap.congr_fun ((Algebra.TensorProduct.mul (R := K)).map_add a b) c
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    induction y using TensorProduct.inductionOn with
    | tmul t y =>
      induction x using TensorProduct.inductionOn with
      | tmul k c =>
        induction y using TensorProduct.inductionOn with
        | tmul l d =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, cancelBaseChange_tmul]
          rw [smul_mul_assoc, mul_smul_comm, smul_smul]
        | add a b ha hb =>
          rw [TensorProduct.tmul_add, add_right, map_add, ha, hb, map_add, mul_add]
      | add a b ha hb =>
        rw [TensorProduct.tmul_add, add_left, map_add, ha, hb, map_add, add_mul]
    | add a b ha hb => rw [add_right, map_add, ha, hb, map_add, mul_add]
  | add a b ha hb => rw [add_left, map_add, ha, hb, map_add, add_mul]

omit [IsScalarTower R C C] [SMulCommClass R C C] in
private theorem tensorScalarExtension_one (S : CommAlgCat.{u} K) :
    tensorScalarExtension (R := R) (C := C) S (1 : S ⊗[K] (K ⊗[R] C)) = 1 := by
  let : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  change cancelBaseChange R K S S C ((1 : S) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] (1 : C))) =
    ((1 : S) ⊗ₜ[R] (1 : C))
  rw [cancelBaseChange_tmul, one_smul]

private theorem tensorScalarExtension_mul (S : CommAlgCat.{u} K)
    (x y : S ⊗[K] (K ⊗[R] C)) :
    tensorScalarExtension (R := R) S (x * y) =
      tensorScalarExtension (R := R) S x * tensorScalarExtension (R := R) S y := by
  let : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  exact cancelBaseChange_mul x y

omit [IsScalarTower R C C] [SMulCommClass R C C] in
private theorem tensorScalarExtension_natural {S T : CommAlgCat.{u} K} (f : S ⟶ T)
    (x : S ⊗[K] (K ⊗[R] C)) :
    tensorScalarExtension (R := R) T (tensorMap f.hom x) =
      tensorMap (forgetScalarsMap (R := R) f).hom (tensorScalarExtension (R := R) S x) := by
  let : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  let : Algebra R T := ((algebraMap K T).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R K T := IsScalarTower.of_algebraMap_eq' rfl
  exact cancelBaseChange_natural f.hom x

section Conjugation

variable {S : Type u} [CommRing S] {M : Type v} {N : Type*}
  [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]

private def conjugateUnits (e : M ≃ₗ[S] N) :
    (Module.End S M)ˣ ≃* (Module.End S N)ˣ :=
  Units.mapEquiv e.conjRingEquiv.toMulEquiv

private theorem conjugateUnits_apply (e : M ≃ₗ[S] N) (g : (Module.End S M)ˣ) (x : M) :
    (conjugateUnits e g).val (e x) = e (g.val x) := by
  change e (g.val (e.symm (e x))) = _
  rw [LinearEquiv.symm_apply_apply]

end Conjugation

section PreserveProduct

variable {S : Type u} [CommRing S] {M : Type v} {N : Type*}
  [NonAssocRing M] [NonAssocRing N] [Module S M] [Module S N]

private theorem conjugateUnits_preserves_iff (e : M ≃ₗ[S] N)
    (h₁ : e 1 = 1) (hm : ∀ x y, e (x * y) = e x * e y) (g : (Module.End S M)ˣ) :
    ((conjugateUnits e g).val 1 = 1 ∧ ∀ x y,
        (conjugateUnits e g).val (x * y) = (conjugateUnits e g).val x * (conjugateUnits e g).val y) ↔
      (g.val 1 = 1 ∧ ∀ x y, g.val (x * y) = g.val x * g.val y) := by
  have he : (conjugateUnits e g).val 1 = e (g.val 1) := h₁ ▸ conjugateUnits_apply e g 1
  constructor
  · rintro ⟨h, hp⟩
    refine ⟨e.injective (he.symm.trans (h.trans h₁.symm)), ?_⟩
    intro x y
    apply e.injective
    have hh := hp (e x) (e y)
    rwa [← hm x y, conjugateUnits_apply, conjugateUnits_apply, conjugateUnits_apply, ← hm] at hh
  · rintro ⟨h, hp⟩
    refine ⟨he.trans ((congrArg e h).trans h₁), ?_⟩
    intro x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← hm x y, conjugateUnits_apply, hp, hm, conjugateUnits_apply, conjugateUnits_apply]

end PreserveProduct

private def tensorScalarExtensionUnits (S : CommAlgCat.{u} K) :
    (Module.End S (S ⊗[K] (K ⊗[R] C)))ˣ ≃* (Module.End (↓S) ((↓S) ⊗[R] C))ˣ :=
  conjugateUnits (S := S) (M := S ⊗[K] (K ⊗[R] C)) (N := (↓S) ⊗[R] C)
    (tensorScalarExtension (R := R) S)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private def tensorScalarExtensionStabilizer (S : CommAlgCat.{u} K) :
    bilinearStabilizer (octonionAlgebra (R := K) (C := K ⊗[R] C)) S ≃*
      bilinearStabilizer (octonionAlgebra (R := R) (C := C)) (↓S) := by
  let e := tensorScalarExtensionUnits (R := R) (C := C) S
  let P := bilinearStabilizer (octonionAlgebra (R := K) (C := K ⊗[R] C)) S
  let Q := bilinearStabilizer (octonionAlgebra (R := R) (C := C)) (↓S)
  have he (g : (Module.End S (S ⊗[K] (K ⊗[R] C)))ˣ) : e g ∈ Q ↔ g ∈ P := by
    have ht := conjugateUnits_preserves_iff (S := S) (M := S ⊗[K] (K ⊗[R] C))
      (N := (↓S) ⊗[R] C) (tensorScalarExtension (R := R) S)
      (tensorScalarExtension_one (R := R) S) (tensorScalarExtension_mul (R := R) S) g
    exact (octonionAlgebra_preserves_iff (R := R) (C := C) (↓S) (e g)).trans
      (ht.trans (octonionAlgebra_preserves_iff (R := K) (C := K ⊗[R] C) S g).symm)

  refine
    { toFun := fun g => ⟨e g.val, (he g.val).2 g.property⟩
      invFun := fun g => ⟨e.symm g.val, (he (e.symm g.val)).1 ((e.apply_symm_apply g.val).symm ▸ g.property)⟩
      left_inv := fun g => Subtype.ext (e.symm_apply_apply g.val)
      right_inv := fun g => Subtype.ext (e.apply_symm_apply g.val)
      map_mul' := fun g h => Subtype.ext (e.map_mul g.val h.val) }

end TensorExtension

section ScalarExtendedAutomorphisms

open Opposite CategoryTheory.Limits
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open PeirceSpecification (tensorMap)
open scoped TensorProduct

variable {R : Type u} [CommRing R] {K : Type u} [CommRing K] [Algebra R K]
  {C : Type v} [NonAssocRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]

local notation "↓" S => (forgetScalars (R := R) S)

private def scalarExtendedLinearPoints
    (A : AutomorphismGroup R C) (S : CommAlgCat.{u} K) :
    ((schemePoints K).obj ((scalarExtensionGroup K).obj A.generalLinear)).obj S ≃*
      (Module.End S (S ⊗[K] (K ⊗[R] C)))ˣ :=
  (forgetFiberPointMulEquiv A.generalLinear S).trans <|
    (A.linearPoints (↓S)).trans (tensorScalarExtensionUnits (R := R) (C := C) S).symm

private def scalarExtendedSubgroupPoints
    (A : AutomorphismGroup R C) (S : CommAlgCat.{u} K) :
    ((schemePoints K).obj ((scalarExtensionGroup K).obj A.group)).obj S ≃*
      bilinearStabilizer (octonionAlgebra (R := K) (C := K ⊗[R] C)) S :=
  (forgetFiberPointMulEquiv A.group S).trans <|
    (A.subgroupPoints (↓S)).trans (tensorScalarExtensionStabilizer (R := R) (C := C) S).symm

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtendedLinearPoints_apply
    (A : AutomorphismGroup R C) (S : CommAlgCat.{u} K)
    (g : ((schemePoints K).obj ((scalarExtensionGroup K).obj A.generalLinear)).obj S)
    (x : S ⊗[K] (K ⊗[R] C)) :
    tensorScalarExtension (R := R) S ((scalarExtendedLinearPoints A S g).val x) =
      (A.linearPoints (↓S) (forgetFiberPoint A.generalLinear.X S g)).val
        (tensorScalarExtension (R := R) S x) := by
  have h := conjugateUnits_apply (tensorScalarExtension (R := R) S)
    (scalarExtendedLinearPoints A S g) x
  change (tensorScalarExtensionUnits (R := R) (C := C) S
      (scalarExtendedLinearPoints A S g)).val (tensorScalarExtension (R := R) S x) = _ at h
  rw [show tensorScalarExtensionUnits (R := R) (C := C) S
      (scalarExtendedLinearPoints A S g) =
    A.linearPoints (↓S) (forgetFiberPoint A.generalLinear.X S g) from
      (tensorScalarExtensionUnits (R := R) (C := C) S).apply_symm_apply _] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
/-- Base change of the actual representing group realizes the scalar-extended algebra. -/
private def scalarExtendedAutomorphisms (A : AutomorphismGroup R C) :
    AutomorphismGroup K (K ⊗[R] C) := by
  let : IsAffine A.group.X.left := A.groupAffine
  let : IsAffine A.generalLinear.X.left := A.linearAffine
  let : LocallyOfFiniteType A.group.X.hom := A.groupFiniteType
  let : LocallyOfFiniteType A.generalLinear.X.hom := A.linearFiniteType
  let : QuasiCompact A.group.X.hom := A.groupQuasiCompact
  let : QuasiCompact A.generalLinear.X.hom := A.linearQuasiCompact
  let : IsClosedImmersion A.inclusion.hom.hom.left := A.closed
  let B := scalarExtensionGroup (R := R) K
  let m := scalarSpecMap (R := R) (K := K)
  refine { group := B.obj A.group
           generalLinear := B.obj A.generalLinear
           inclusion := B.map A.inclusion
           closed := scalarExtension_isClosedImmersion (K := K) A.inclusion.hom.hom
           groupAffine := ?_
           linearAffine := ?_
           groupFiniteType := ?_
           linearFiniteType := ?_
           groupQuasiCompact := ?_
           linearQuasiCompact := ?_
           linearPoints := scalarExtendedLinearPoints A
           subgroupPoints := scalarExtendedSubgroupPoints A
           evaluatesInclusion := ?_
           scalarChange := ?_ }
  · change IsAffine (pullback A.group.X.hom m)
    infer_instance
  · change IsAffine (pullback A.generalLinear.X.hom m)
    infer_instance
  · change LocallyOfFiniteType (pullback.snd A.group.X.hom m)
    infer_instance
  · change LocallyOfFiniteType (pullback.snd A.generalLinear.X.hom m)
    infer_instance
  · change QuasiCompact (pullback.snd A.group.X.hom m)
    infer_instance
  · change QuasiCompact (pullback.snd A.generalLinear.X.hom m)
    infer_instance
  · intro S p
    apply (tensorScalarExtensionUnits (R := R) (C := C) S).injective
    change (tensorScalarExtensionUnits (R := R) (C := C) S)
      ((tensorScalarExtensionUnits (R := R) (C := C) S).symm (A.linearPoints (↓S)
        (forgetFiberPoint A.generalLinear.X S (p ≫ (B.map A.inclusion).hom.hom)))) =
      (tensorScalarExtensionUnits (R := R) (C := C) S) ((scalarExtendedSubgroupPoints A S p).val)
    have hp : forgetFiberPoint A.generalLinear.X S (p ≫ (B.map A.inclusion).hom.hom) =
        forgetFiberPoint A.group.X S p ≫ A.inclusion.hom.hom :=
      forgetFiberPoint_comp A.inclusion.hom.hom S p
    rw [(tensorScalarExtensionUnits (R := R) (C := C) S).apply_symm_apply, hp]
    rw [show A.linearPoints (↓S) (forgetFiberPoint A.group.X S p ≫ A.inclusion.hom.hom) =
      (A.subgroupPoints (↓S) (forgetFiberPoint A.group.X S p)).val from A.evaluatesInclusion _ _]
    exact (congrArg Subtype.val
      ((tensorScalarExtensionStabilizer (R := R) (C := C) S).apply_symm_apply _)).symm
  · intro S T f p x
    apply (tensorScalarExtension (R := R) (C := C) T).injective
    change tensorScalarExtension (R := R) T
      ((scalarExtendedLinearPoints A T ((algSpec (CommRingCat.of K)).map f.op ≫ p)).val
        (tensorMap f.hom x)) =
      tensorScalarExtension (R := R) T (tensorMap f.hom ((scalarExtendedLinearPoints A S p).val x))
    rw [scalarExtendedLinearPoints_apply A T _ (tensorMap f.hom x),
      tensorScalarExtension_natural f x, forgetFiberPoint_natural A.generalLinear.X f p,
      tensorScalarExtension_natural f, scalarExtendedLinearPoints_apply A S p x]
    exact A.scalarChange (forgetScalarsMap f) (forgetFiberPoint A.generalLinear.X S p) _

end ScalarExtendedAutomorphisms

section SpecialLinearDomain

open PeirceSpecification (SL3Ring)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open scoped TensorProduct

private def determinantOnePart {S : Type u} [CommRing S] (M : Matrix.GeneralLinearGroup (Fin 3) S) :
    Matrix.SpecialLinearGroup (Fin 3) S :=
  ⟨Matrix.diagonal (fun i => if i = 0 then (M.det⁻¹ : Sˣ).val else 1) * M.val, by
    rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using (Units.inv_mul M.det)⟩

private theorem determinantOnePart_toGL {S : Type u} [CommRing S]
    (M : Matrix.SpecialLinearGroup (Fin 3) S) :
    determinantOnePart (Matrix.SpecialLinearGroup.toGL M) = M := by
  apply Subtype.ext
  change Matrix.diagonal (fun i => if i = 0 then
        ((Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL M))⁻¹ : Sˣ).val else 1) *
        (Matrix.SpecialLinearGroup.toGL M).val = _
  simp [Matrix.diagonal_one, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

private theorem determinantOnePart_natural {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (M : Matrix.GeneralLinearGroup (Fin 3) S) :
    Matrix.SpecialLinearGroup.map f (determinantOnePart M) =
      determinantOnePart (Matrix.GeneralLinearGroup.map f M) := by
  apply Subtype.ext
  change (Matrix.diagonal (fun i => if i = 0 then (M.det⁻¹ : Sˣ).val else 1) * M.val).map f =
    Matrix.diagonal (fun i => if i = 0 then
      (((Matrix.GeneralLinearGroup.map f M).det)⁻¹ : Tˣ).val else 1) * M.val.map f
  rw [Matrix.map_mul, Matrix.GeneralLinearGroup.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i = 0 <;> simp [hi, Matrix.diagonal_apply_eq, ← map_inv]
  · simp [h]

private abbrev MatrixIndex := ULift.{u} (Fin 3)

private def lowerMatrixIndex (S : Type u) [CommRing S] :
    Matrix.GeneralLinearGroup MatrixIndex.{u} S ≃* Matrix.GeneralLinearGroup (Fin 3) S :=
  Units.mapEquiv (Matrix.reindexRingEquiv S Equiv.ulift).toMulEquiv

private theorem lowerMatrixIndex_natural {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (x : Matrix.GeneralLinearGroup MatrixIndex.{u} S) :
    lowerMatrixIndex T (Matrix.GeneralLinearGroup.map f x) =
      Matrix.GeneralLinearGroup.map f (lowerMatrixIndex S x) := by
  apply Matrix.GeneralLinearGroup.ext
  intro _ _
  rfl

private theorem matrixCoordinates_domain (B : Type u) [CommRing B] [IsDomain B] :
    IsDomain (MatrixCoordinates B MatrixIndex.{u}) := by
  apply Localization.Away.isDomain
  intro h
  let f : MvPolynomial (MatrixIndex.{u} × MatrixIndex.{u}) B →ₐ[B] B :=
    MvPolynomial.aeval (fun p => (1 : Matrix MatrixIndex.{u} MatrixIndex.{u} B) p.1 p.2)
  have hf : f ((genericMatrix B MatrixIndex.{u}).det) = 1 := by
    change f.toRingHom ((genericMatrix B MatrixIndex.{u}).det) = 1
    rw [RingHom.map_det f.toRingHom]
    change Matrix.det (f.mapMatrix (genericMatrix B MatrixIndex.{u})) = 1
    have hm : f.mapMatrix (genericMatrix B MatrixIndex.{u}) = 1 := by
      ext i j
      exact MvPolynomial.aeval_X _ _
    rw [hm, Matrix.det_one]
  rw [h, map_zero] at hf
  exact zero_ne_one hf

/-- The determinant-one coordinate algebra over an integral domain (including
a base change of its equations) is a subalgebra of the general linear coordinates. -/
private theorem determinantOneAlgebra_domain (R B : Type u) [CommRing R] [CommRing B]
    [Algebra R B] [IsDomain B] : IsDomain (B ⊗[R] SL3Ring R) := by
  let W := B ⊗[R] SL3Ring R
  let C := MatrixCoordinates B MatrixIndex.{u}
  obtain ⟨_, L, hL⟩ := Peirce.special_linear_three_scheme.{u, u} R
  let y := L W Algebra.TensorProduct.includeRight
  obtain ⟨EC, hC⟩ := LinearAlgebraicGroups.Albert.Automorphisms.matrixCoordinateEvaluation
    B MatrixIndex.{u} C
  obtain ⟨EW, hW⟩ := LinearAlgebraicGroups.Albert.Automorphisms.matrixCoordinateEvaluation
    B MatrixIndex.{u} W
  let x := EC (AlgHom.id B C)
  let j := EW.symm ((lowerMatrixIndex W).symm (Matrix.SpecialLinearGroup.toGL y))
  have hj : Matrix.GeneralLinearGroup.map j.toRingHom x =
      (lowerMatrixIndex W).symm (Matrix.SpecialLinearGroup.toGL y) := by
    rw [← EW.apply_symm_apply ((lowerMatrixIndex W).symm (Matrix.SpecialLinearGroup.toGL y))]
    apply Matrix.GeneralLinearGroup.ext
    intro i k
    change j (x.val i k) = (EW j).val i k
    rw [hW, show x.val = (AlgHom.id B C).mapMatrix coordinateMatrix from hC _]
    rfl
  let q := (L C).symm (determinantOnePart (lowerMatrixIndex C x))
  have hq : (j.restrictScalars R).comp q = Algebra.TensorProduct.includeRight := by
    apply (L W).injective
    rw [hL C W q (j.restrictScalars R)]
    change Matrix.SpecialLinearGroup.map j.toRingHom (L C q) = y
    rw [show L C q = determinantOnePart (lowerMatrixIndex C x) from (L C).apply_symm_apply _, determinantOnePart_natural,
      ← lowerMatrixIndex_natural, hj, MulEquiv.apply_symm_apply, determinantOnePart_toGL]
  let i := AlgHom.liftEquiv R B (SL3Ring R) C q
  have hji : j.comp i = AlgHom.id B W := by
    apply (AlgHom.liftEquiv R B (SL3Ring R) W).symm.injective
    apply AlgHom.ext
    intro a
    rw [AlgHom.liftEquiv_symm_apply, AlgHom.liftEquiv_symm_apply]
    change j (i (1 ⊗ₜ[R] a)) = 1 ⊗ₜ[R] a
    rw [show i (1 ⊗ₜ[R] a) = q a by simp [i]]
    exact AlgHom.congr_fun hq a
  let : IsDomain C := matrixCoordinates_domain B
  exact Function.Injective.isDomain i.toRingHom
    (fun a b h => (AlgHom.congr_fun hji a).symm.trans
      ((congrArg j h).trans (AlgHom.congr_fun hji b)))

end SpecialLinearDomain

section ConnectedFibers

open Opposite CategoryTheory.Limits
open PeirceSpecification (ZornIsomorphism SplitQuadricRing SL3Ring SplitEvaluationOver tensorMap)
open scoped TensorProduct

variable {R : Type u} [CommRing R]

private theorem splitQuadricRing_domain (K : Type u) [Field K] : IsDomain (SplitQuadricRing K) := by
  have : IsDomain (K ⊗[K] SplitQuadricRing K) := (Peirce.split_quadric_fibers.{u, u} K K).1
  let e := Algebra.TensorProduct.lid K (SplitQuadricRing K)
  exact Function.Injective.isDomain e.symm.toRingHom e.symm.injective

private theorem splitEvaluation_genericPoint
    {A D : Type u} [CommRing A] [CommRing D] [Algebra R A] [Algebra R D] [IsDomain A]
    {ρ : A →ₐ[R] D}
    (h : SplitEvaluationOver.{u, u} R A D ρ) :
    ∃ q : PrimeSpectrum D, PrimeSpectrum.comap ρ.toRingHom q = ⟨⊥, Ideal.isPrime_bot⟩ := by
  obtain ⟨e, he, E, heval, _⟩ := h
  let p : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨r, hr, _, hchart⟩ := Peirce.split_frame_charts.{u, u} R A e p
  let L := FractionRing A
  let a := IsScalarTower.toAlgHom R A L
  have ha : Function.Injective a := IsFractionRing.injective A L
  have hr' : r ≠ 0 := fun hz => hr (hz ▸ p.asIdeal.zero_mem)
  have hu : IsUnit (a r) := isUnit_iff_ne_zero.mpr (fun hz => hr' (ha (hz.trans (map_zero a).symm)))
  let a' := (awayHomEquiv (R := R) r).symm ⟨a, hu⟩
  obtain ⟨F, _⟩ := hchart L a'
  let d := (E L).symm (F 1).val
  have hd : d.comp ρ = a := by
    have hF : E L d = (F 1).val := (E L).apply_symm_apply _
    have hg := heval L d
    rw [hF, (F 1).property] at hg
    refine ((he L).1 ((ZornSpecification.baseChange R L).injective hg.symm)).trans ?_
    exact congrArg Subtype.val ((awayHomEquiv (R := R) r).apply_symm_apply ⟨a, hu⟩)
  refine ⟨PrimeSpectrum.comap d.toRingHom (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L), ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply,
    show d.toRingHom.comp ρ.toRingHom = a.toRingHom from congrArg AlgHom.toRingHom hd]
  apply PrimeSpectrum.ext
  apply bot_unique
  intro x hx
  apply Ideal.mem_bot.mpr
  apply ha
  exact (Ideal.mem_bot.mp hx).trans (map_zero a).symm

private theorem splitAutomorphismRing_connected {K : Type u} [Field K]
    {D : Type u} [CommRing D] [Algebra K D] {ρ : SplitQuadricRing K →ₐ[K] D}
    (h : SplitEvaluationOver.{u, u} K (SplitQuadricRing K) D ρ) : ConnectedSpace (PrimeSpectrum D) := by
  classical
  let A := SplitQuadricRing K
  let : IsDomain A := splitQuadricRing_domain K
  obtain ⟨q₀, hq₀⟩ := splitEvaluation_genericPoint h
  choose r hr e _ using splitFrameChartAlgebra (ρ := ρ) h
  let U (p : PrimeSpectrum A) : Set (PrimeSpectrum D) := PrimeSpectrum.basicOpen (ρ (r p))
  have hU (p : PrimeSpectrum A) : _root_.IsConnected (U p) := by
    have hn : r p ≠ 0 := fun hz => hr p (hz ▸ p.asIdeal.zero_mem)
    let : IsDomain (Localization.Away (r p)) := Localization.Away.isDomain hn
    let : IsDomain (Localization.Away (r p) ⊗[K] SL3Ring K) :=
      determinantOneAlgebra_domain K (Localization.Away (r p))
    let : IsDomain (Localization.Away (ρ (r p))) :=
      Function.Injective.isDomain (e p).symm.toRingHom (e p).symm.injective
    rw [show U p = Set.range (PrimeSpectrum.comap (algebraMap D (Localization.Away (ρ (r p))))) from
      (PrimeSpectrum.localization_away_comap_range _ _).symm]
    exact isConnected_range (PrimeSpectrum.continuous_comap _)
  have hq (p : PrimeSpectrum A) : q₀ ∈ U p := by
    change r p ∉ (PrimeSpectrum.comap ρ.toRingHom q₀).asIdeal
    rw [hq₀]
    intro hz
    exact hr p ((Ideal.mem_bot.mp hz).symm ▸ p.asIdeal.zero_mem)
  have hcov : (⋃ p, U p) = Set.univ := Set.eq_univ_of_forall fun q => by
    let p := PrimeSpectrum.comap ρ.toRingHom q
    exact Set.mem_iUnion.mpr ⟨p, hr p⟩
  let hCommon : (⋂ p, U p).Nonempty := ⟨q₀, Set.mem_iInter.mpr hq⟩
  apply connectedSpace_iff_univ.mpr
  rw [← hcov]
  exact ⟨⟨q₀, Set.mem_iUnion.mpr ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A), hq _⟩⟩,
    isPreconnected_iUnion hCommon (fun p => (hU p).2)⟩

private theorem splitAutomorphismScheme_connected {K : Type u} [Field K]
    {C : Type v} [NonAssocRing C] [Module K C]
    [IsScalarTower K C C] [SMulCommClass K C C] {n : QuadraticForm K C}
    (F : ZornIsomorphism n) (A : AutomorphismGroup K C) :
    ConnectedSpace A.group.X.left := by
  obtain ⟨D, _, _, _, i, _, h⟩ := splitPresentation F A
  have hc : ConnectedSpace (PrimeSpectrum D) := splitAutomorphismRing_connected h
  let j := (Over.forget (Spec (CommRingCat.of K))).mapIso i
  exact j.hom.homeomorph.connectedSpace_iff.mp hc

end ConnectedFibers

section Descent

open Opposite CategoryTheory.Limits
open PeirceSpecification (ZornIsomorphism)
open _root_.LinearAlgebraicGroups.Specs
open scoped TensorProduct

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}

private theorem octonion_splits_over_algebraically_closed {K : Type u} [Field K] [IsAlgClosed K]
    {D : Type*} [NonAssocRing D] [Module K D] [IsScalarTower K D D] [SMulCommClass K D D]
    {q : QuadraticForm K D} (hq : OctonionNormConditions q) :
    Nonempty (ZornIsomorphism q) := by
  obtain ⟨e⟩ := Peirce.points_over_algebraically_closed hq
  apply Peirce.isotropic_field_split hq
  refine ⟨e.val, ?_, e.property.2⟩
  intro h
  have htrace := e.property.1
  rw [h, map_zero] at htrace
  exact zero_ne_one htrace

private theorem octonionAutomorphismScheme_smooth (h : OctonionNormConditions n)
    (A : AutomorphismGroup R C) : Smooth A.group.X.hom := by
  let : Module.Projective R C := h.projective
  obtain ⟨K, _, _, _, hff, ⟨F⟩⟩ := Peirce.faithfully_flat_split h
  let B := scalarExtendedAutomorphisms (K := K) A
  have hB := splitAutomorphismScheme_smooth F B
  let m := scalarSpecMap (R := R) (K := K)
  have hFlat : Flat m ∧ Surjective m :=
    (flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
  have hQC : QuasiCompact m := inferInstance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨hFlat.2, hFlat.1⟩, hQC⟩ hB

private theorem octonionAutomorphismScheme_geometricallyConnected (h : OctonionNormConditions n)
    (A : AutomorphismGroup R C) : GeometricallyConnected A.group.X.hom := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := (ConnectedSpace ·))).mpr ?_⟩
  intro K _ _
  let : Module.Projective R C := h.projective
  let B := scalarExtendedAutomorphisms (K := K) A
  let L := AlgebraicClosure K
  let B' := scalarExtendedAutomorphisms (K := L) B
  have hk : OctonionNormConditions (normBaseChange K n) := octonion_norm_baseChange h K
  let : Module.Projective K (K ⊗[R] C) := hk.projective
  have hL := octonion_norm_baseChange hk L
  obtain ⟨F⟩ := octonion_splits_over_algebraically_closed hL
  let hc : ConnectedSpace B'.group.X.left := splitAutomorphismScheme_connected F B'
  let f := scalarSpecMap (R := K) (K := L)
  have hff : Module.FaithfullyFlat K L := inferInstance
  have hs : Surjective f := ((flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)).2
  let π := pullback.fst B.group.X.hom f
  have hπ : Surjective π := by
    let : Surjective f := hs
    infer_instance
  let : ConnectedSpace ((pullback B.group.X.hom f : Scheme.{u})) := hc
  exact hπ.surj.connectedSpace π.continuous

/-- The actual automorphism scheme is smooth with connected geometric fibers for
every regular rank-eight octonion algebra. -/
private theorem exists_smooth_connected_automorphismScheme (h : OctonionNormConditions n) :
    ∃ A : AutomorphismGroup R C, Smooth A.group.X.hom ∧ GeometricallyConnected A.group.X.hom := by
  let : Module.Projective R C := h.projective
  let : Module.Finite R C := h.finite
  obtain ⟨A⟩ := LinearAlgebraicGroups.Albert.Automorphisms.bilinearAutomorphismScheme
    (octonionAlgebra (R := R) (C := C))
  exact ⟨A, octonionAutomorphismScheme_smooth h A,
    octonionAutomorphismScheme_geometricallyConnected h A⟩

end Descent

section FrameTorusCoordinates

open Opposite CategoryTheory.Limits
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)

variable {R : Type u} [CommRing R]

private abbrev FrameRing := MonoidAlgebra R FrameCharacters.{u}

private abbrev framePoint (S : CommAlgCat.{u} R) :=
  ((schemePoints R).obj (frameTorus R)).obj S

private def framePointConvolution (S : CommAlgCat.{u} R) :
    WithConv (FrameRing (R := R) →ₐ[R] S) ≃* framePoint S :=
  Spec.mapMulEquiv

private def framePointAlgebraHom (S : CommAlgCat.{u} R) (t : framePoint S) :
    FrameRing (R := R) →ₐ[R] S :=
  ((framePointConvolution S).symm t).ofConv

private theorem framePointAlgebraHom_spec (S : CommAlgCat.{u} R) (t : framePoint S) :
    (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom (framePointAlgebraHom S t)).op = t :=
  (framePointConvolution S).apply_symm_apply t

private theorem frameCoordinate_eval (i : Fin 3) (S : CommAlgCat.{u} R) (t : framePoint S) :
    frameCoordinate i S t = framePointAlgebraHom S t (MonoidAlgebra.single (frameExponent i) 1) := by
  nth_rw 1 [← framePointAlgebraHom_spec S t]
  unfold frameCoordinate
  rw [Functor.FullyFaithful.preimage_map]
  rfl

private theorem frameExponents_product :
    frameExponent 0 * frameExponent 1 * frameExponent 2 = (1 : FrameCharacters.{u}) := by
  decide

private def frameMonomial : FrameCharacters.{u} →* (FrameRing (R := R))ˣ :=
  MonoidHom.toHomUnits (MonoidAlgebra.of R _)

private def frameUnits (S : CommAlgCat.{u} R) (t : framePoint S) (i : Fin 3) : Sˣ :=
  Units.map (framePointAlgebraHom S t).toMonoidHom (frameMonomial (frameExponent i))

private theorem frameUnits_val (S : CommAlgCat.{u} R) (t : framePoint S) (i : Fin 3) :
    (frameUnits S t i).val = frameCoordinate i S t := (frameCoordinate_eval i S t).symm

private theorem frameUnits_product (S : CommAlgCat.{u} R) (t : framePoint S) :
    frameUnits S t 0 * frameUnits S t 1 * frameUnits S t 2 = 1 := by
  simp only [frameUnits, ← map_mul, frameExponents_product, map_one]

private theorem frameUnits_inv_val (S : CommAlgCat.{u} R) (t : framePoint S) (i : Fin 3) :
    ((frameUnits S t i)⁻¹ : Sˣ).val =
      frameCoordinate (i + 1) S t * frameCoordinate (i + 2) S t := by
  have h := frameUnits_product S t
  have hi : frameUnits S t i * (frameUnits S t (i + 1) * frameUnits S t (i + 2)) = 1 := by
    fin_cases i
    · change frameUnits S t 0 * (frameUnits S t 1 * frameUnits S t 2) = 1
      simpa only [mul_assoc] using h
    · change frameUnits S t 1 * (frameUnits S t 2 * frameUnits S t 0) = 1
      calc
        _ = frameUnits S t 0 * frameUnits S t 1 * frameUnits S t 2 := by ac_rfl
        _ = 1 := h
    · change frameUnits S t 2 * (frameUnits S t 0 * frameUnits S t 1) = 1
      calc
        _ = frameUnits S t 0 * frameUnits S t 1 * frameUnits S t 2 := by ac_rfl
        _ = 1 := h

  rw [← frameUnits_val S t (i + 1), ← frameUnits_val S t (i + 2)]
  exact congrArg Units.val (eq_inv_of_mul_eq_one_right hi).symm

private theorem frameUnits_mul (S : CommAlgCat.{u} R) (t u : framePoint S) :
    frameUnits S (t * u) = frameUnits S t * frameUnits S u := by
  funext i
  apply Units.ext
  change (((framePointConvolution S).symm (t * u)).ofConv) (MonoidAlgebra.single (frameExponent i) 1) =
    (((framePointConvolution S).symm t).ofConv) (MonoidAlgebra.single (frameExponent i) 1) *
      (((framePointConvolution S).symm u).ofConv) (MonoidAlgebra.single (frameExponent i) 1)
  rw [map_mul, AlgHom.convMul_apply]
  simp

private theorem framePointAlgebraHom_natural {S T : CommAlgCat.{u} R} (f : S ⟶ T)
    (t : framePoint S) :
    framePointAlgebraHom T (((schemePoints R).obj (frameTorus R)).map f t) =
      f.hom.comp (framePointAlgebraHom S t) := by
  let F := algSpec (CommRingCat.of R)
  have hF : F.map (CommAlgCat.ofHom (framePointAlgebraHom T
      (((schemePoints R).obj (frameTorus R)).map f t))).op =
      F.map ((CommAlgCat.ofHom (framePointAlgebraHom S t) ≫ f).op) := by
    rw [framePointAlgebraHom_spec, op_comp, Functor.map_comp, framePointAlgebraHom_spec]
    rfl
  exact congrArg (fun h => h.unop.hom) ((algSpec.fullyFaithful (R := CommRingCat.of R)).map_injective hF)


private theorem frameUnits_natural {S T : CommAlgCat.{u} R} (f : S ⟶ T) (t : framePoint S) (i : Fin 3) :
    frameUnits T (((schemePoints R).obj (frameTorus R)).map f t) i =
      Units.map f.hom.toMonoidHom (frameUnits S t i) := by
  apply Units.ext
  change framePointAlgebraHom T (((schemePoints R).obj (frameTorus R)).map f t)
      (MonoidAlgebra.single (frameExponent i) 1) =
    f.hom (framePointAlgebraHom S t (MonoidAlgebra.single (frameExponent i) 1))
  rw [framePointAlgebraHom_natural f t]
  rfl

end FrameTorusCoordinates

section FrameTorusMorphism

open Opposite CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open PeirceSpecification (ZornIsomorphism SplitAutomorphism)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)
open private zornBasis map_zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}

private theorem diagonalLinearEquiv_comp {S : Type u} [CommRing S] (d e : Fin 3 → Sˣ) (x : Zorn S) :
    diagonalLinearEquiv (d * e) x = diagonalLinearEquiv d (diagonalLinearEquiv e x) := by
  obtain ⟨⟨a, v, w, b⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective x
  apply (Zorn.coordinates S).injective
  change scaleSlots (d * e) (a, v, w, b) = scaleSlots d (scaleSlots e (a, v, w, b))
  simp only [scaleSlots, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext i
  · change ((d i).val * (e i).val) * v i = (d i).val * ((e i).val * v i)
    exact mul_assoc _ _ _
  · change ((d i * e i)⁻¹ : Sˣ).val * w i = ((d i)⁻¹ : Sˣ).val * (((e i)⁻¹ : Sˣ).val * w i)
    rw [mul_inv, Units.val_mul, mul_assoc]

private theorem diagonalLinearEquiv_natural {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (d : Fin 3 → Sˣ) (x : Zorn S) :
    diagonalLinearEquiv (fun i => Units.map f.toMonoidHom (d i))
        (ZornSpecification.mapCoordinates f x) =
      ZornSpecification.mapCoordinates f (diagonalLinearEquiv d x) := by
  obtain ⟨⟨a, v, w, b⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective x
  apply (Zorn.coordinates T).injective
  change scaleSlots (fun i => Units.map f.toMonoidHom (d i)) (f a, f ∘ v, f ∘ w, f b) =
    (f a, f ∘ scaleVector d v, f ∘ scaleVector d⁻¹ w, f b)
  simp only [scaleSlots, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext i
  · change f ((d i).val) * f (v i) = f ((d i).val * v i)
    exact (map_mul f _ _).symm
  · have h := map_inv (Units.map f.toMonoidHom) (d i)
    change ((Units.map f.toMonoidHom (d i))⁻¹ : Tˣ).val * f (w i) =
      f (((d i)⁻¹ : Sˣ).val * w i)
    rw [← h, map_mul]
    rfl

private def frameSplitAutomorphism (S : CommAlgCat.{u} R) (t : framePoint S) : SplitAutomorphism S :=
  ⟨diagonalLinearEquiv (frameUnits S t), diagonal_one _, diagonal_mul _ (frameUnits_product S t)⟩

private def framePointMap (F : ZornIsomorphism n) (A : AutomorphismGroup R C)
    (S : CommAlgCat.{u} R) (t : framePoint S) : ((schemePoints R).obj A.group).obj S :=
  (splitSchemePoints F A S).symm (frameSplitAutomorphism S t)

private theorem splitSchemePoints_action (F : ZornIsomorphism n) (A : AutomorphismGroup R C)
    (S : CommAlgCat.{u} R) (g : ((schemePoints R).obj A.group).obj S) (x : Zorn S) :
    splitCoordinates F S ((splitSchemePoints F A S g).val x) =
      (A.subgroupPoints S g).val.val (splitCoordinates F S x) :=
  (splitCoordinates F S).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
private theorem framePointMap_mul (F : ZornIsomorphism n) (A : AutomorphismGroup R C)
    (S : CommAlgCat.{u} R) (t u : framePoint S) :
    framePointMap F A S (t * u) = framePointMap F A S t * framePointMap F A S u := by
  apply (splitSchemePoints F A S).injective
  rw [show splitSchemePoints F A S (framePointMap F A S (t * u)) = frameSplitAutomorphism S (t * u)
    from (splitSchemePoints F A S).apply_symm_apply _]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply (splitCoordinates F S).injective
  rw [splitSchemePoints_action, map_mul]
  change splitCoordinates F S ((frameSplitAutomorphism S (t * u)).val x) =
    (A.subgroupPoints S (framePointMap F A S t)).val.val
      ((A.subgroupPoints S (framePointMap F A S u)).val.val (splitCoordinates F S x))
  rw [← splitSchemePoints_action F A S (framePointMap F A S u),
    ← splitSchemePoints_action F A S (framePointMap F A S t)]
  simp only [framePointMap, Equiv.apply_symm_apply]
  congr 1
  change diagonalLinearEquiv (frameUnits S (t * u)) x =
    diagonalLinearEquiv (frameUnits S t) (diagonalLinearEquiv (frameUnits S u) x)
  rw [frameUnits_mul, diagonalLinearEquiv_comp]

private theorem framePointMap_natural (F : ZornIsomorphism n) (A : AutomorphismGroup R C)
    {S T : CommAlgCat.{u} R} (f : S ⟶ T) (t : framePoint S) :
    framePointMap F A T (((schemePoints R).obj (frameTorus R)).map f t) =
      ((schemePoints R).obj A.group).map f (framePointMap F A S t) := by
  apply (splitSchemePoints F A T).injective
  simp only [framePointMap, Equiv.apply_symm_apply]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (zornBasis T).ext
  intro i
  change (frameSplitAutomorphism T (((schemePoints R).obj (frameTorus R)).map f t)).val (zornBasis T i) =
    (splitSchemePoints F A T (((schemePoints R).obj A.group).map f
      ((splitSchemePoints F A S).symm (frameSplitAutomorphism S t)))).val (zornBasis T i)
  rw [← map_zornBasis f.hom.toRingHom i, splitSchemePoints_natural, Equiv.apply_symm_apply]
  change diagonalLinearEquiv (frameUnits T (((schemePoints R).obj (frameTorus R)).map f t))
      (ZornSpecification.mapCoordinates f.hom.toRingHom (zornBasis S i)) =
    ZornSpecification.mapCoordinates f.hom.toRingHom
      (diagonalLinearEquiv (frameUnits S t) (zornBasis S i))
  rw [show frameUnits T (((schemePoints R).obj (frameTorus R)).map f t) =
    fun j => Units.map f.hom.toMonoidHom (frameUnits S t j) from
      funext (frameUnits_natural f t)]
  exact diagonalLinearEquiv_natural f.hom.toRingHom _ _

private theorem isMonHom_of_ring_points {G H : Grp (RingScheme R)}
    (affine : IsAffine G.X.left) (i : G.X ⟶ H.X)
    (hone : ∀ (S : CommAlgCat.{u} R), (1 : ringPoint G.X S) ≫ i = 1)
    (hmul : ∀ (S : CommAlgCat.{u} R) (x y : ringPoint G.X S),
      (x * y) ≫ i = (x ≫ i) * (y ≫ i)) : IsMonHom i := by
  constructor
  · apply affineRingPoints_ext (X := 𝟙_ (RingScheme R))
    · change IsAffine (Spec (CommRingCat.of R))
      infer_instance
    · intro S p
      rw [show p = toUnit ((algSpec (CommRingCat.of R)).obj (op S)) from toUnit_unique _ _]
      exact hone S
  · apply affineRingPoints_ext (X := G.X ⊗ G.X)
    · let : IsAffine G.X.left := affine
      change IsAffine (pullback G.X.hom G.X.hom)
      infer_instance
    · intro S p
      let x := p ≫ fst G.X G.X
      let y := p ≫ snd G.X G.X
      calc
        p ≫ μ[G.X] ≫ i = (x * y) ≫ i := by simp [x, y, Hom.mul_def]
        _ = (x ≫ i) * (y ≫ i) := hmul S x y
        _ = p ≫ (i ⊗ₘ i) ≫ μ[H.X] := by
          have hl : lift (x ≫ i) (y ≫ i) = p ≫ (i ⊗ₘ i) := by
            apply CartesianMonoidalCategory.hom_ext <;> simp [x, y]
          simp only [Hom.mul_def, hl, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 570000 in
/-- The determinant-one diagonal coordinate action is induced by a morphism of group schemes. -/
private theorem exists_frameTorusMorphism (F : ZornIsomorphism n) (A : AutomorphismGroup R C) :
    ∃ i : frameTorus R ⟶ A.group, IsFrameTorus F A i ∧
      ∀ S t, t ≫ i.hom.hom = framePointMap F A S t := by
  have hT : IsAffine (frameTorus R).X.left := by
    change IsAffine (Spec (CommRingCat.of (FrameRing (R := R))))
    infer_instance
  obtain ⟨i, hi⟩ := morphism_of_ring_points hT (framePointMap F A) (framePointMap_natural F A)
  have h : IsMonHom i := isMonHom_of_ring_points hT i (fun S =>
    (hi S 1).trans (MonoidHom.mk' (framePointMap F A S) (framePointMap_mul F A S)).map_one)
    (fun S t u => by
      rw [hi S (t * u), hi S t, hi S u]
      exact framePointMap_mul F A S t u)
  refine ⟨Grp.homMk i, ?_, hi⟩
  intro S t x
  have H := splitSchemePoints_action F A S (framePointMap F A S t) x
  rw [show splitSchemePoints F A S (framePointMap F A S t) = frameSplitAutomorphism S t
    from (splitSchemePoints F A S).apply_symm_apply _] at H
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective x
  change (A.subgroupPoints S (t ≫ i)).val.val (splitCoordinates F S (Zorn.ofCoordinates (a, u, v, b)))
    = _
  rw [hi S t, ← H]
  simp only [Zorn.ofCoordinates]
  congr 1
  apply (Zorn.coordinates S).injective
  change scaleSlots (frameUnits S t) (a, u, v, b) =
    (a, (fun j => frameCoordinate j S t * u j),
      (fun j => frameCoordinate (j + 1) S t * frameCoordinate (j + 2) S t * v j), b)
  simp only [scaleSlots, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext j
  · change (frameUnits S t j).val * u j = _
    rw [frameUnits_val]
  · change ((frameUnits S t j)⁻¹ : Sˣ).val * v j = _
    rw [frameUnits_inv_val]

end FrameTorusMorphism

section FrameTorusClosed

open Opposite
open PeirceSpecification (ZornIsomorphism)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}

private theorem frameExponent_decompose (m : FrameCharacters.{u}) :
    frameExponent 0 ^ (Multiplicative.toAdd m.down 0) *
      frameExponent 1 ^ (Multiplicative.toAdd m.down 1) = m := by
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  funext i
  change ((Multiplicative.toAdd m.down 0) • (![1, 0] : Fin 2 → ℤ) +
      (Multiplicative.toAdd m.down 1) • (![0, 1] : Fin 2 → ℤ)) i =
    Multiplicative.toAdd m.down i
  simp only [Pi.add_apply, zsmul_eq_mul]
  fin_cases i
  · change Multiplicative.toAdd m.down 0 * 1 + Multiplicative.toAdd m.down 1 * 0 = _
    simp
  · change Multiplicative.toAdd m.down 0 * 0 + Multiplicative.toAdd m.down 1 * 1 = _
    simp

private theorem frameRing_surjective {B : Type u} [CommRing B] [Algebra R B]
    (f : B →ₐ[R] FrameRing (R := R))
    (hPos : ∀ i : Fin 3, MonoidAlgebra.single (frameExponent i) 1 ∈ f.range)
    (hNeg : ∀ i : Fin 3, MonoidAlgebra.single (frameExponent i)⁻¹ 1 ∈ f.range) :
    Function.Surjective f := by
  intro x
  change x ∈ f.range
  have hz (i : Fin 3) (a : ℤ) : (MonoidAlgebra.of R _ (frameExponent i ^ a)) ∈ f.range := by
    cases a with
    | ofNat a =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, map_pow]
      exact f.range.pow_mem (hPos i) a
    | negSucc a =>
      rw [zpow_negSucc, ← inv_pow, map_pow]
      exact f.range.pow_mem (hNeg i) (a + 1)
  have hx (m : FrameCharacters.{u}) : (MonoidAlgebra.of R _ m) ∈ f.range := by
    have he := f.range.mul_mem (hz 0 (Multiplicative.toAdd m.down 0))
      (hz 1 (Multiplicative.toAdd m.down 1))
    rwa [← map_mul, frameExponent_decompose] at he
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact f.range.zero_mem
  | add a b ha hb => exact f.range.add_mem ha hb
  | single m a =>
    change (MonoidAlgebra.single m a : FrameRing (R := R)) ∈ f.range
    have h : a • MonoidAlgebra.of R _ m ∈ f.range := f.range.smul_mem (hx m) a
    simpa only [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', smul_eq_mul, mul_one] using h

set_option backward.isDefEq.respectTransparency false in
private theorem frameTorusMorphism_closed (F : ZornIsomorphism n) (A : AutomorphismGroup R C)
    (i : frameTorus R ⟶ A.group)
    (hi : ∀ (S : CommAlgCat.{u} R) (t : framePoint S), t ≫ i.hom.hom = framePointMap F A S t) :
    IsClosedImmersion i.hom.hom.left := by
  let Q := CommAlgCat.of R (FrameRing (R := R))
  let W := algSpec (CommRingCat.of R)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of R)
  obtain ⟨B, ⟨b⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr A.groupAffine
  let p : W.obj (op Q) ⟶ A.group.X := i.hom.hom
  let f : B.unop ⟶ Q := (ff.preimage (p ≫ b.inv)).unop
  have hp : W.map f.op ≫ b.hom = p := by
    change W.map (ff.preimage (p ≫ b.inv)) ≫ b.hom = p
    rw [ff.map_preimage]
    simp
  let t : framePoint Q := 𝟙 (W.obj (op Q))
  have ht : framePointAlgebraHom Q t = AlgHom.id R (FrameRing (R := R)) := by
    have H := framePointAlgebraHom_spec Q t
    apply AlgHom.ext
    intro x
    have he : (CommAlgCat.ofHom (framePointAlgebraHom Q t)).op = 𝟙 (op Q) := by
      apply ff.map_injective
      rw [H, W.map_id]
    exact congrArg (fun h => h.unop.hom x) he
  have hact (x : Zorn B.unop) :
      ZornSpecification.mapCoordinates f.hom.toRingHom ((splitSchemePoints F A B.unop b.hom).val x) =
        diagonalLinearEquiv (frameUnits Q t) (ZornSpecification.mapCoordinates f.hom.toRingHom x) := by
    have hf := (splitSchemePoints_natural F A f b.hom x).symm
    change ZornSpecification.mapCoordinates f.hom.toRingHom ((splitSchemePoints F A B.unop b.hom).val x) =
      (splitSchemePoints F A Q (W.map f.op ≫ b.hom)).val (ZornSpecification.mapCoordinates f.hom.toRingHom x) at hf
    rw [hp, show p = t ≫ i.hom.hom from (Category.id_comp _).symm, hi Q t, framePointMap,
      Equiv.apply_symm_apply] at hf
    exact hf
  have hg (j : Fin 3) (s : Bool) :
      (MonoidAlgebra.single (if s then (frameExponent j)⁻¹ else frameExponent j) 1 :
          FrameRing (R := R)) ∈ f.hom.range := by
    let x : Zorn B.unop := if s then Zorn.ofCoordinates (0, 0, Pi.single j 1, 0)
      else Zorn.ofCoordinates (0, Pi.single j 1, 0, 0)
    let getCoord {S : Type u} [CommRing S] (y : Zorn S) : S :=
      if s then (Zorn.coordinates S y).2.2.1 j else (Zorn.coordinates S y).2.1 j
    refine ⟨getCoord ((splitSchemePoints F A B.unop b.hom).val x), ?_⟩
    have H := congrArg (getCoord (S := Q)) (hact x)
    cases s <;>
      simp only [getCoord, x, Bool.false_eq_true, ite_false, ite_true] at H ⊢
    · change f.hom _ = ((frameUnits Q t j).val * f.hom ((Pi.single j 1 : Fin 3 → B.unop) j)) at H
      rw [Pi.single_eq_same, map_one, mul_one, frameUnits_val, frameCoordinate_eval, ht] at H
      exact H
    · change f.hom _ = ((frameUnits Q t j)⁻¹ : Qˣ).val *
        f.hom ((Pi.single j 1 : Fin 3 → B.unop) j) at H
      rw [Pi.single_eq_same, map_one, mul_one] at H
      change f.hom _ = ((Units.map (framePointAlgebraHom Q t).toMonoidHom
        (frameMonomial (frameExponent j)))⁻¹ : Qˣ).val at H
      rw [← map_inv, ← map_inv, ht] at H
      exact H
  have hf : Function.Surjective f.hom :=
    frameRing_surjective f.hom (fun j => hg j false) (fun j => hg j true)
  have hSpec : IsClosedImmersion (W.map f.op).left :=
    IsClosedImmersion.spec_of_surjective _ hf
  have : IsIso b.hom.left := by
    change IsIso ((Over.forget _).map b.hom)
    infer_instance
  have H : IsClosedImmersion ((W.map f.op).left ≫ b.hom.left) := inferInstance
  exact (congrArg Over.Hom.left hp) ▸ H

private theorem exists_closedFrameTorus (F : ZornIsomorphism n) (A : AutomorphismGroup R C) :
    ∃ i : frameTorus R ⟶ A.group, IsClosedImmersion i.hom.hom.left ∧ IsFrameTorus F A i := by
  obtain ⟨i, hF, h⟩ := exists_frameTorusMorphism F A
  exact ⟨i, frameTorusMorphism_closed F A i h, hF⟩

end FrameTorusClosed

section FrameTorusBaseChange

open Opposite CategoryTheory.Limits
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)

variable {R : Type u} [CommRing R]

private theorem groupIso_of_ring_points {G H : Grp (RingScheme R)}
    (hG : IsAffine G.X.left) (hH : IsAffine H.X.left)
    (E : ∀ (S : CommAlgCat.{u} R), ringPoint G.X S ≃* ringPoint H.X S)
    (hE : ∀ {S T : CommAlgCat.{u} R} (f : S ⟶ T) (x : ringPoint G.X S),
      E T ((algSpec (CommRingCat.of R)).map f.op ≫ x) =
        (algSpec (CommRingCat.of R)).map f.op ≫ E S x) :
    ∃ i : G ≅ H, ∀ (S : CommAlgCat.{u} R) (x : ringPoint G.X S), x ≫ i.hom.hom.hom = E S x := by
  have inv_nat {S T : CommAlgCat.{u} R} (f : S ⟶ T) (x : ringPoint H.X S) :
      (E T).symm ((algSpec (CommRingCat.of R)).map f.op ≫ x) =
        (algSpec (CommRingCat.of R)).map f.op ≫ (E S).symm x := by
    apply (E T).injective
    rw [MulEquiv.apply_symm_apply, hE, MulEquiv.apply_symm_apply]
  obtain ⟨i, hi⟩ := morphism_of_ring_points hG (fun S => E S) hE
  obtain ⟨j, hj⟩ := morphism_of_ring_points hH (fun S => (E S).symm) inv_nat
  let ii : IsMonHom i := isMonHom_of_ring_points hG i
    (fun S => (hi S 1).trans (map_one (E S)))
    (by intro S x y; rw [hi, hi, hi, map_mul])
  let jj : IsMonHom j := isMonHom_of_ring_points hH j
    (fun S => (hj S 1).trans (map_one (E S).symm))
    (by intro S x y; rw [hj, hj, hj, map_mul])
  refine ⟨⟨Grp.homMk i, Grp.homMk j, ?_, ?_⟩, hi⟩
  · apply Grp.hom_ext
    apply affineRingPoints_ext hG
    intro S x
    change x ≫ (i ≫ j) = x ≫ 𝟙 _
    rw [← Category.assoc, hi, hj, MulEquiv.symm_apply_apply, Category.comp_id]
  · apply Grp.hom_ext
    apply affineRingPoints_ext hH
    intro S x
    change x ≫ (j ≫ i) = x ≫ 𝟙 _
    rw [← Category.assoc, hj, hi, MulEquiv.apply_symm_apply, Category.comp_id]

private def frameTorusCharacters (S : CommAlgCat.{u} R) : framePoint S ≃* (FrameCharacters.{u} →* Sˣ) :=
  (framePointConvolution S).symm.trans
    ((MonoidAlgebra.liftMulEquiv R S FrameCharacters.{u}).symm.trans MonoidHom.toHomUnitsMulEquiv)

private theorem frameTorusCharacters_eval (S : CommAlgCat.{u} R) (t : framePoint S)
    (m : FrameCharacters.{u}) :
    ((frameTorusCharacters S t) m).val = framePointAlgebraHom S t (MonoidAlgebra.single m 1) :=
  rfl

private theorem frameTorusCharacters_natural {S T : CommAlgCat.{u} R} (f : S ⟶ T) (t : framePoint S)
    (m : FrameCharacters.{u}) :
    frameTorusCharacters T (((schemePoints R).obj (frameTorus R)).map f t) m =
      Units.map f.hom.toMonoidHom ((frameTorusCharacters S t) m) := by
  apply Units.ext
  rw [frameTorusCharacters_eval, framePointAlgebraHom_natural]
  exact congrArg f.hom (frameTorusCharacters_eval S t m).symm

variable {K : Type u} [CommRing K] [Algebra R K]

private def frameFiberPointsEquiv (S : CommAlgCat.{u} K) :
    ringPoint ((scalarExtensionGroup (R := R) K).obj (frameTorus R)).X S ≃*
      ringPoint (frameTorus K).X S :=
  (forgetFiberPointMulEquiv (frameTorus R) S).trans <|
    (frameTorusCharacters (forgetScalars S)).trans (frameTorusCharacters S).symm

private theorem frameFiberPointsEquiv_eval (S : CommAlgCat.{u} K)
    (t : ringPoint ((scalarExtensionGroup (R := R) K).obj (frameTorus R)).X S) :
    frameTorusCharacters S (frameFiberPointsEquiv S t) =
      frameTorusCharacters (forgetScalars S) (forgetFiberPoint (frameTorus R).X S t) :=
  (frameTorusCharacters S).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
private theorem frameFiberPointsEquiv_natural {S T : CommAlgCat.{u} K}
    (f : S ⟶ T) (t : ringPoint ((scalarExtensionGroup (R := R) K).obj (frameTorus R)).X S) :
    frameFiberPointsEquiv T ((algSpec (CommRingCat.of K)).map f.op ≫ t) =
      (algSpec (CommRingCat.of K)).map f.op ≫ frameFiberPointsEquiv S t := by
  apply (frameTorusCharacters T).injective
  apply MonoidHom.ext
  intro m
  have ht := frameFiberPointsEquiv_eval T ((algSpec (CommRingCat.of K)).map f.op ≫ t)
  have hs := frameFiberPointsEquiv_eval S t
  rw [ht, forgetFiberPoint_natural (frameTorus R).X f t]
  have h := frameTorusCharacters_natural (forgetScalarsMap f)
    (forgetFiberPoint (frameTorus R).X S t) m
  have h' := frameTorusCharacters_natural f (frameFiberPointsEquiv S t) m
  change frameTorusCharacters T ((algSpec (CommRingCat.of K)).map f.op ≫ frameFiberPointsEquiv S t) m =
    Units.map f.hom.toMonoidHom (frameTorusCharacters S (frameFiberPointsEquiv S t) m) at h'
  rw [h', hs]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension carries the specified frame torus to the frame torus over the
new base, with the same exponent coordinates. -/
private theorem frameTorusBaseChange :
    ∃ i : (scalarExtensionGroup (R := R) K).obj (frameTorus R) ≅ frameTorus K,
      ∀ (S : CommAlgCat.{u} K) (t : ringPoint ((scalarExtensionGroup (R := R) K).obj (frameTorus R)).X S)
        (j : Fin 3),
        frameCoordinate j S (t ≫ i.hom.hom.hom) =
          frameCoordinate j (forgetScalars S) (forgetFiberPoint (frameTorus R).X S t) := by
  have hA (B : Type u) [CommRing B] : IsAffine (frameTorus B).X.left := by
    change IsAffine (Spec (CommRingCat.of (FrameRing (R := B))))
    infer_instance
  have hAR : IsAffine ((scalarExtensionGroup (R := R) K).obj (frameTorus R)).X.left := by
    have := hA R
    change IsAffine (pullback (frameTorus R).X.hom (scalarSpecMap (R := R) (K := K)))
    infer_instance
  obtain ⟨i, hi⟩ := groupIso_of_ring_points hAR (hA K) frameFiberPointsEquiv frameFiberPointsEquiv_natural
  refine ⟨i, fun S t j => ?_⟩
  have h := congrArg (fun p : FrameCharacters.{u} →* Sˣ => (p (frameExponent j)).val)
    (frameFiberPointsEquiv_eval S t)
  rw [hi S t]
  rw [frameCoordinate_eval j S _, frameCoordinate_eval j (forgetScalars S) _]
  simpa only [frameTorusCharacters_eval] using h

end FrameTorusBaseChange

section FrameCharacterLattice

open Opposite
open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsSplitTorus)
open CharacterDescent (Character StandardLattice)
open CharacterPairing (characterValue absoluteRoots)
open SchemeCentre (rootLattice)
open DiagonalizableGroups (groupAlgebra integerGenerator)
open private integerHopfHomEquiv integerHopfHomEquiv_generator
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent

variable {K : Type u} [Field K]

private def frameLatticeEquiv : FrameCharacters.{u} ≃* StandardLattice.{u} 2 where
  toFun m j := ⟨Multiplicative.ofAdd (m.down.toAdd j)⟩
  invFun m := ⟨Multiplicative.ofAdd (fun j => (m j).down.toAdd)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem frameTorus_isSplit : IsSplitTorus (frameTorus K) := by
  let e := MonoidAlgebra.domCongrBialgEquiv K K frameLatticeEquiv.symm
  obtain ⟨i⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) 2
  exact ⟨2, ⟨(hopfSpec (CommRingCat.of K)).mapIso (CommHopfAlgCat.isoMk e).op ≪≫ i⟩⟩

private def frameCharacterEquiv : FrameCharacters.{u} ≃* Character (frameTorus K) :=
  (LinearAlgebraicGroups.CharacterDescent.monomialCharacterEquiv K).trans
    (LinearAlgebraicGroups.CharacterDescent.groupLikeCharacterEquiv (groupAlgebra K FrameCharacters.{u}))

private theorem frameCharacterEquiv_monomial_eval (S : TestAlgebra K) (t : framePoint S)
    (m : FrameCharacters.{u}) : characterValue (frameCharacterEquiv (K := K) m) S t =
      framePointAlgebraHom S t (MonoidAlgebra.single m 1) := by
  let x := LinearAlgebraicGroups.CharacterDescent.monomialCharacterEquiv K m
  let a := integerHopfHomEquiv (groupAlgebra K FrameCharacters.{u}) x
  have ha := integerHopfHomEquiv_generator (groupAlgebra K FrameCharacters.{u}) x
  have hEq : frameCharacterEquiv (K := K) m = specGroupMap a := rfl
  rw [hEq]
  let W := algSpec (CommRingCat.of K)
  unfold characterValue
  nth_rw 1 [← framePointAlgebraHom_spec S t]
  change ((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage
    (W.map (CommAlgCat.ofHom (framePointAlgebraHom S t)).op ≫
      W.map (CommAlgCat.ofHom a.hom.toAlgHom).op)).unop.hom
        (MonoidAlgebra.single integerGenerator 1) = _
  rw [← Functor.map_comp, Functor.FullyFaithful.preimage_map]
  change framePointAlgebraHom S t (a.hom (MonoidAlgebra.single integerGenerator 1)) =
    framePointAlgebraHom S t (MonoidAlgebra.single m 1)
  change a.hom (MonoidAlgebra.single integerGenerator 1) = x.val at ha
  rw [ha]
  rfl

private theorem frameCharacterEquiv_eval (S : TestAlgebra K) (t : framePoint S)
    (i : Fin 3) : characterValue (frameCharacterEquiv (K := K) (frameExponent i)) S t =
      frameCoordinate i S t :=
  (frameCharacterEquiv_monomial_eval S t (frameExponent i)).trans (frameCoordinate_eval i S t).symm

private theorem frameExponents_relations (m : Fin 3 → ℤ) :
    (∏ j, frameExponent j ^ m j) = (1 : FrameCharacters.{u}) ↔ ∀ i j, m i = m j := by
  rw [Fin.prod_univ_three]
  have h (j : Fin 2) :
      ((frameExponent 0 ^ m 0 * frameExponent 1 ^ m 1 *
        frameExponent 2 ^ m 2).down.toAdd j) = m j.castSucc - m 2 := by
    change ((m 0) • (![1, 0] : Fin 2 → ℤ) + (m 1) • (![0, 1] : Fin 2 → ℤ) +
      (m 2) • (![-1, -1] : Fin 2 → ℤ)) j = m j.castSucc - m 2
    simp only [Pi.add_apply, zsmul_eq_mul]
    fin_cases j
    · change m 0 * 1 + m 1 * 0 + m 2 * (-1) = m 0 - m 2
      ring
    · change m 0 * 0 + m 1 * 1 + m 2 * (-1) = m 1 - m 2
      ring
  constructor
  · intro he
    have ha (i : Fin 2) : m i.castSucc = m 2 := by
      have hi := congrArg (fun x : FrameCharacters.{u} => x.down.toAdd i) he
      rw [h] at hi
      exact sub_eq_zero.mp hi
    have ha₀ : m 0 = m 2 := ha 0
    have ha₁ : m 1 = m 2 := ha 1
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all
  · intro he
    apply ULift.ext
    apply Multiplicative.toAdd.injective
    funext i
    rw [h, he i.castSucc 2, sub_self]
    rfl

private theorem frameCharacters_relations :
    let χ := fun i : Fin 3 => frameCharacterEquiv (K := K) (frameExponent i)
    (∏ i, χ i) = 1 ∧
      ∀ m : Fin 3 → ℤ, (∏ i, χ i ^ m i) = 1 ↔ ∀ i j, m i = m j := by
  intro χ
  constructor
  · change (∏ i, frameCharacterEquiv (K := K) (frameExponent i)) = 1
    rw [← map_prod, Fin.prod_univ_three, frameExponents_product, map_one]
  · intro m
    rw [← frameExponents_relations]
    change (∏ i, (frameCharacterEquiv (K := K) (frameExponent i)) ^ m i) = 1 ↔ _
    simp only [← map_zpow, ← map_prod, ← (frameCharacterEquiv (K := K)).map_one]
    exact (frameCharacterEquiv (K := K)).injective.eq_iff

end FrameCharacterLattice

section FramePointCentralizer

open PeirceSpecification (SplitAutomorphism)
open private split_automorphism_ext from LinearAlgebraicGroups.Composition.PeirceFrames

variable {K : Type u} [Field K]

private theorem diagonal_traceBasis (d : Fin 3 → Kˣ) (hd : d 0 * d 1 * d 2 = 1) (i : TraceIndex) :
    traceAction (diagonalPoint d hd) (traceBasis i) = (traceWeight d i).val • traceBasis i := by
  apply traceCoordinates.injective
  rw [map_smul]
  funext j
  rw [diagonal_traceCoordinates, traceBasis_coords]
  by_cases h : j = i
  · subst j
    rfl
  · simp [Pi.single_eq_of_ne h]

private theorem traceBasis_scaled_of_commutes
    (d : Fin 3 → Kˣ) (hd : d 0 * d 1 * d 2 = 1)
    (hweights : Function.Injective (fun i => (traceWeight d i).val))
    (g : ZornPointGroup K) (hg : Commute (diagonalPoint d hd) g) (i : TraceIndex) :
    ∃ a : K, a ≠ 0 ∧ traceAction g (traceBasis i) = a • traceBasis i := by
  let x := traceAction g (traceBasis i)
  have h : traceAction (diagonalPoint d hd) x = (traceWeight d i).val • x := calc
    _ = traceAction (diagonalPoint d hd * g) (traceBasis i) := rfl
    _ = traceAction (g * diagonalPoint d hd) (traceBasis i) := by rw [hg.eq]
    _ = traceAction g (traceAction (diagonalPoint d hd) (traceBasis i)) := rfl
    _ = _ := by rw [diagonal_traceBasis, map_smul]
  let a := traceCoordinates x i
  have hxa : x = a • traceBasis i := by
    apply traceCoordinates.injective
    rw [map_smul, traceBasis_coords]
    funext j
    change traceCoordinates x j = a * (Pi.single i (1 : K) : TraceIndex → K) j
    by_cases hij : j = i
    · subst j
      rw [Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne hij, mul_zero]
      have he := congrArg (fun y : traceZero K => traceCoordinates y j) h
      rw [diagonal_traceCoordinates, map_smul, Pi.smul_apply, smul_eq_mul] at he
      have hh : ((traceWeight d j).val - (traceWeight d i).val) * traceCoordinates x j = 0 := by
        rw [sub_mul, he, sub_self]
      exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (fun hj => hij (hweights hj)))
  refine ⟨a, ?_, hxa⟩
  intro hz
  have hx : x = 0 := by rw [hxa, hz, zero_smul]
  have hinj := (LinearMap.GeneralLinearGroup.toLinearEquiv g.val).injective
  have hh : g.val.val (traceBasis (K := K) i).val = g.val.val 0 := by
    rw [map_zero]
    exact congrArg Subtype.val hx
  exact traceBasis_ne_zero i (Subtype.ext (hinj hh))

private theorem upperLower_basis_product (i : Fin 3) :
    (traceBasis (K := K) (some (false, i))).val * (traceBasis (K := K) (some (true, i))).val =
      Zorn.first K := by
  rw [traceBasis_upper_val, traceBasis_lower_val]
  apply (Zorn.coordinates K).injective
  change zornProduct ((0 : K), Pi.single i 1, 0, 0) (0, 0, Pi.single i 1, 0) =
    (1, 0, 0, 0)
  fin_cases i <;> simp [zornProduct, dotProduct, Fin.sum_univ_three]

private theorem upper_basis_product :
    (traceBasis (K := K) (some (false, (0 : Fin 3)))).val *
        (traceBasis (K := K) (some (false, (1 : Fin 3)))).val =
      (traceBasis (K := K) (some (true, (2 : Fin 3)))).val := by
  rw [traceBasis_upper_val, traceBasis_upper_val, traceBasis_lower_val]
  apply (Zorn.coordinates K).injective
  change zornProduct ((0 : K), Pi.single (0 : Fin 3) 1, 0, 0)
    (0, Pi.single (1 : Fin 3) 1, 0, 0) = (0, 0, Pi.single (2 : Fin 3) 1, 0)
  simp [zornProduct, cross_apply]
  funext i
  fin_cases i <;> simp

private def splitAutomorphism_of_point (g : ZornPointGroup K) : SplitAutomorphism K :=
  ⟨LinearMap.GeneralLinearGroup.toLinearEquiv g.val, point_one g, point_mul g⟩

/-- Over an infinite field a diagonal element with seven distinct trace-zero weights
has exactly the diagonal frame torus as its centralizer on points. -/
private theorem point_centralizer_of_separating_diagonal
    (d : Fin 3 → Kˣ) (hd : d 0 * d 1 * d 2 = 1)
    (hweights : Function.Injective (fun i => (traceWeight d i).val))
    (g : ZornPointGroup K) (hg : Commute (diagonalPoint d hd) g) :
    ∃ e : Fin 3 → Kˣ, ∃ he : e 0 * e 1 * e 2 = 1, g = diagonalPoint e he := by
  choose a ha hA using traceBasis_scaled_of_commutes d hd hweights g hg
  let upperScale (i : Fin 3) := a (some (false, i))
  let lowerScale (i : Fin 3) := a (some (true, i))
  let U (i : Fin 3) := (traceBasis (K := K) (some (false, i))).val
  let V (i : Fin 3) := (traceBasis (K := K) (some (true, i))).val
  have hgU (i : Fin 3) : g.val.val (U i) = upperScale i • U i :=
    congrArg Subtype.val (hA (some (false, i)))
  have hgV (i : Fin 3) : g.val.val (V i) = lowerScale i • V i :=
    congrArg Subtype.val (hA (some (true, i)))
  have hp (i : Fin 3) : g.val.val (Zorn.first K) = (upperScale i * lowerScale i) • Zorn.first K := calc
    _ = g.val.val (U i * V i) := congrArg _ (upperLower_basis_product i).symm
    _ = (upperScale i • U i) * (lowerScale i • V i) := by rw [point_mul, hgU, hgV]
    _ = _ := by rw [smul_mul_assoc, mul_smul_comm, smul_smul, upperLower_basis_product]
  have hpair (i : Fin 3) : upperScale i * lowerScale i = 1 := by
    have ht := LinearMap.congr_fun (point_norm_trace g).2 (Zorn.first K)
    change compositionTrace (Zorn.norm K) (g.val.val (Zorn.first K)) = _ at ht
    rw [hp i, map_smul, trace_first, smul_eq_mul, mul_one] at ht
    exact ht
  have he : g.val.val (Zorn.first K) = Zorn.first K := by rw [hp 0, hpair, one_smul]
  have hcross : upperScale 0 * upperScale 1 = lowerScale 2 := by
    have H := point_mul g (U 0) (U 1)
    rw [upper_basis_product, hgV, hgU, hgU, smul_mul_assoc, mul_smul_comm, smul_smul,
      upper_basis_product] at H
    have hv : V 2 ≠ 0 := fun h => traceBasis_ne_zero _ (Subtype.ext h)
    exact smul_left_injective K hv H.symm
  let e (i : Fin 3) : Kˣ := Units.mk0 (upperScale i) (ha (some (false, i)))
  have heprod : e 0 * e 1 * e 2 = 1 := by
    apply Units.ext
    change upperScale 0 * upperScale 1 * upperScale 2 = 1
    rw [hcross, mul_comm, hpair]
  refine ⟨e, heprod, ?_⟩
  have hF : splitAutomorphism_of_point g = splitAutomorphism_of_point (diagonalPoint e heprod) := by
    apply split_automorphism_ext
    · change g.val.val (Zorn.first K) = diagonalLinearEquiv e (Zorn.first K)
      rw [he]
      apply (Zorn.coordinates K).injective
      change ((1 : K), 0, 0, 0) = scaleSlots e (1, 0, 0, 0)
      simp only [scaleSlots, Prod.mk.injEq, true_and, and_true]
      constructor <;> funext j <;> change (0 : K) = _ * 0 <;> rw [mul_zero]
    · intro i
      change g.val.val (Zorn.ofCoordinates (0, Pi.single i 1, 0, 0)) =
        diagonalLinearEquiv e (Zorn.ofCoordinates (0, Pi.single i 1, 0, 0))
      rw [← traceBasis_upper_val i, hgU]
      simp only [U, traceBasis_upper_val]
      apply (Zorn.coordinates K).injective
      change ((upperScale i * 0, upperScale i • Pi.single i 1, upperScale i • (0 : Fin 3 → K), upperScale i * 0) : ZornCoordinates K) =
        scaleSlots e (0, Pi.single i 1, 0, 0)
      simp only [scaleSlots, mul_zero, smul_zero, Prod.mk.injEq, true_and, and_true]
      constructor
      · funext j
        by_cases h : j = i <;> simp [scaleVector, h, e, Pi.smul_apply, smul_eq_mul]
      · funext j
        change (0 : K) = _ * 0
        rw [mul_zero]
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun F : SplitAutomorphism K => F.val.toLinearMap) hF

end FramePointCentralizer

section ZornDerivations

open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (IsDerivation)

variable {R : Type u} [CommRing R]

/-- The derivation moving the first idempotent in an upper Peirce direction. -/
private def upperDerivationSlots (p : Fin 3 → R) (x : ZornCoordinates R) : ZornCoordinates R :=
  (-(p ⬝ᵥ x.2.2.1), (x.1 - x.2.2.2) • p, p ⨯₃ x.2.1, p ⬝ᵥ x.2.2.1)

private def upperDerivation (p : Fin 3 → R) : Module.End R (Zorn R) :=
  (Zorn.coordinates R).symm.toLinearMap.comp <|
    ({ toFun := upperDerivationSlots p
       map_add' := by
         rintro ⟨a, x, y, b⟩ ⟨c, u, v, d⟩
         simp only [upperDerivationSlots, Prod.mk_add_mk, Prod.mk.injEq, dotProduct_add,
           neg_add, map_add, ← add_smul, true_and, and_true]
         congr 1
         abel
       map_smul' := by
         rintro r ⟨a, x, y, b⟩
         simp only [upperDerivationSlots, Prod.smul_mk, RingHom.id_apply, dotProduct_smul,
           map_smul, smul_neg, Prod.mk.injEq, true_and, and_true]
         rw [smul_smul]
         congr 1
         exact (mul_sub r a b).symm } :
      Module.End R (ZornCoordinates R)).comp (Zorn.coordinates R).toLinearMap

private theorem upperDerivation_first (p : Fin 3 → R) :
    upperDerivation p (Zorn.first R) = Zorn.ofCoordinates (0, p, 0, 0) := by
  apply (Zorn.coordinates R).injective
  change upperDerivationSlots p ((1 : R), 0, 0, 0) = (0, p, 0, 0)
  simp [upperDerivationSlots]

private theorem upperDerivation_rule (p : Fin 3 → R) :
    IsDerivation (LinearMap.mul R (Zorn R)) (upperDerivation p) := by
  intro x y
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
  obtain ⟨⟨c, w, z, d⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective y
  apply (Zorn.coordinates R).injective
  change upperDerivationSlots p (zornProduct (a, u, v, b) (c, w, z, d)) =
    zornProduct (upperDerivationSlots p (a, u, v, b)) (c, w, z, d) +
      zornProduct (a, u, v, b) (upperDerivationSlots p (c, w, z, d))
  simp only [upperDerivationSlots, zornProduct, Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨?_, funext ?_, funext ?_, ?_⟩
  · simp [cross_apply, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro i
    fin_cases i <;>
      simp [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] <;> ring
  · intro i
    fin_cases i <;>
      simp [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] <;> ring
  · simp [cross_apply, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

private theorem diagonal_upperDerivation (d : Fin 3 → Rˣ)
    (h : d 0 * d 1 * d 2 = 1) (p : Fin 3 → R) (x : Zorn R) :
    diagonalLinearEquiv d (upperDerivation p x) =
      upperDerivation (scaleVector d p) (diagonalLinearEquiv d x) := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
  apply (Zorn.coordinates R).injective
  change scaleSlots d (upperDerivationSlots p (a, u, v, b)) =
    upperDerivationSlots (scaleVector d p) (scaleSlots d (a, u, v, b))
  simp only [scaleSlots, upperDerivationSlots, scale_cross d h, scale_dot,
    Prod.mk.injEq, true_and, and_true]
  funext i
  simp [scaleVector, smul_eq_mul, mul_left_comm]

end ZornDerivations

section ElementaryDerivations

open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (IsDerivation)

variable {R : Type u} [CommRing R]

/-- The infinitesimal elementary change of the upper frame and its dual action. -/
private def elementaryDerivationSlots (i j : Fin 3) (x : ZornCoordinates R) :
    ZornCoordinates R :=
  (0, Pi.single i (x.2.1 j), Pi.single j (-x.2.2.1 i), 0)

private def elementaryDerivation (i j : Fin 3) : Module.End R (Zorn R) :=
  (Zorn.coordinates R).symm.toLinearMap.comp
    (({ toFun := elementaryDerivationSlots i j
        map_add' := by
          rintro ⟨a, u, v, b⟩ ⟨c, w, z, d⟩
          simp only [elementaryDerivationSlots, Prod.mk_add_mk, Prod.mk.injEq, zero_add,
            Pi.add_apply, neg_add, true_and, and_true]
          constructor <;> funext k <;> simp [Pi.single_apply] <;> split_ifs <;> simp
        map_smul' := by
          rintro r ⟨a, u, v, b⟩
          simp only [elementaryDerivationSlots, RingHom.id_apply, Prod.smul_mk,
            Prod.mk.injEq, smul_zero, true_and, and_true]
          constructor <;> funext k <;> simp [Pi.single_apply] } :
        Module.End R (ZornCoordinates R)).comp (Zorn.coordinates R).toLinearMap)

set_option maxHeartbeats 550000 in
private theorem elementaryDerivation_rule (i j : Fin 3) (hij : i ≠ j) :
    IsDerivation (LinearMap.mul R (Zorn R)) (elementaryDerivation i j) := by
  intro x y
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
  obtain ⟨⟨c, w, z, d⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective y
  apply (Zorn.coordinates R).injective
  change elementaryDerivationSlots i j (zornProduct (a, u, v, b) (c, w, z, d)) =
    zornProduct (elementaryDerivationSlots i j (a, u, v, b)) (c, w, z, d) +
      zornProduct (a, u, v, b) (elementaryDerivationSlots i j (c, w, z, d))
  simp only [elementaryDerivationSlots, zornProduct, Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨?_, funext ?_, funext ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first | exact (hij rfl).elim | simp [dotProduct, Fin.sum_univ_three]
  · intro k
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals first
      | exact (hij rfl).elim
      | simp [cross_apply, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    all_goals ring
  · intro k
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals first
      | exact (hij rfl).elim
      | simp [cross_apply, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    all_goals ring
  · fin_cases i <;> fin_cases j <;>
      first | exact (hij rfl).elim | simp [dotProduct, Fin.sum_univ_three]

end ElementaryDerivations

section GeometricPointComparison

open Opposite CategoryTheory.Limits
open PeirceSpecification (SplitAutomorphism ZornIsomorphism)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)

variable {K : Type u} [Field K]
  {C : Type v} [NonAssocRing C] [Module K C] [IsScalarTower K C C] [SMulCommClass K C C]
  {n : QuadraticForm K C}

private def splitAutomorphismPointEquiv : SplitAutomorphism K ≃ ZornPointGroup K where
  toFun f := pointOfLinearEquiv f.val f.property.1 f.property.2
  invFun := splitAutomorphism_of_point
  left_inv f := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl
  right_inv f := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    rfl

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private def splitPointGroupEquiv (F : ZornIsomorphism n) (A : AutomorphismGroup K C) :
    ringPoint A.group.X (CommAlgCat.of K K) ≃* ZornPointGroup K where
  toEquiv := (splitSchemePoints F A (CommAlgCat.of K K)).trans splitAutomorphismPointEquiv
  map_mul' f g := by
    let S := CommAlgCat.of K K
    let E := splitSchemePoints F A S
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    change (E (f * g)).val x = (E f).val ((E g).val x)
    apply (splitCoordinates F K).injective
    change splitCoordinates F S ((E (f * g)).val x) = splitCoordinates F S ((E f).val ((E g).val x))
    rw [splitSchemePoints_action F A S (f * g) x, splitSchemePoints_action F A S f ((E g).val x),
      map_mul, splitSchemePoints_action F A S g x]
    rfl

private theorem splitPointGroupEquiv_frame (F : ZornIsomorphism n) (A : AutomorphismGroup K C)
    (t : framePoint (CommAlgCat.of K K)) :
    splitPointGroupEquiv F A (framePointMap F A (CommAlgCat.of K K) t) =
      diagonalPoint (frameUnits _ t) (frameUnits_product _ t) := by
  change splitAutomorphismPointEquiv (splitSchemePoints F A _
    ((splitSchemePoints F A _).symm (frameSplitAutomorphism _ t))) = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem exists_framePoint_for_diagonal {R : Type u} [CommRing R]
    (S : CommAlgCat.{u} R) (d : Fin 3 → Sˣ) (hd : d 0 * d 1 * d 2 = 1) :
    ∃ t : framePoint S, frameUnits S t = d := by
  let χ : FrameCharacters.{u} →* Sˣ :=
    { toFun := fun m => d 0 ^ m.down.toAdd 0 * d 1 ^ m.down.toAdd 1
      map_one' := by
        change d 0 ^ (0 : ℤ) * d 1 ^ (0 : ℤ) = 1
        simp
      map_mul' := by
        intro a b
        change d 0 ^ (a.down.toAdd 0 + b.down.toAdd 0) * d 1 ^ (a.down.toAdd 1 + b.down.toAdd 1) =
          (d 0 ^ a.down.toAdd 0 * d 1 ^ a.down.toAdd 1) *
            (d 0 ^ b.down.toAdd 0 * d 1 ^ b.down.toAdd 1)
        simp only [zpow_add]
        ac_rfl }
  let t := (frameTorusCharacters S).symm χ
  have h (i : Fin 3) : frameUnits S t i = χ (frameExponent i) := by
    apply Units.ext
    have h := frameTorusCharacters_eval S t (frameExponent i)
    rw [show frameTorusCharacters S t = χ from (frameTorusCharacters S).apply_symm_apply _] at h
    exact h.symm
  refine ⟨t, funext fun i => (h i).trans ?_⟩
  fin_cases i
  · change d 0 ^ (1 : ℤ) * d 1 ^ (0 : ℤ) = d 0
    simp
  · change d 0 ^ (0 : ℤ) * d 1 ^ (1 : ℤ) = d 1
    simp
  · change d 0 ^ (-1 : ℤ) * d 1 ^ (-1 : ℤ) = d 2
    simpa only [zpow_neg, zpow_one, ← mul_inv] using eq_inv_of_mul_eq_one_right hd |>.symm

end GeometricPointComparison

section GeometricSubgroupInclusion

open Opposite CategoryTheory.Limits
open _root_.LinearAlgebraicGroups.Specs
open SchemeDerivedGroup (IsSubgroupOf)

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Rational-point factorization through a closed subgroup suffices for a reduced
source of finite type over a geometric field. -/
private theorem subgroupOf_of_geometricPoints {G : GroupScheme K} (T S : ClosedSubgroup G)
    (hReduced : IsReduced S.group.X.left) (hAffine : IsAffine S.group.X.left)
    (hFinite : LocallyOfFiniteType S.group.X.hom)
    (h : ∀ p : Points S.group.X (CommAlgCat.of K K),
      ∃ t : Points T.group.X (CommAlgCat.of K K), t ≫ T.inclusion.hom.hom = p ≫ S.inclusion.hom.hom) :
    IsSubgroupOf S T := by
  let t := T.inclusion.hom.hom
  let s := S.inclusion.hom.hom
  let P := pullback t.left s.left
  let p : P ⟶ S.group.X.left := pullback.snd t.left s.left
  let : IsClosedImmersion t.left := T.isClosedImmersion
  let : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.snd t.left s.left))
  have hfib : closedPoints S.group.X.left ⊆ Set.range p := by
    intro x hx
    let y : Points S.group.X (CommAlgCat.of K K) :=
      Over.homMk (pointOfClosedPoint S.group.X.hom x hx) (by
        change pointOfClosedPoint S.group.X.hom x hx ≫ S.group.X.hom =
          Spec.map (CommRingCat.ofHom (algebraMap K K))
        rw [Algebra.algebraMap_self]
        exact (pointOfClosedPoint_comp S.group.X.hom x hx).trans (Scheme.Spec.map_id _).symm)
    obtain ⟨z, hz⟩ := h y
    have hz' : z.left ≫ t.left = y.left ≫ s.left := congrArg Over.Hom.left hz
    let l : Spec (CommRingCat.of K) ⟶ P := pullback.lift z.left y.left hz'
    refine ⟨l (IsLocalRing.closedPoint K), ?_⟩
    change (l ≫ p) (IsLocalRing.closedPoint K) = x
    rw [show l ≫ p = y.left from pullback.lift_snd ..]
    exact pointOfClosedPoint_apply S.group.X.hom x hx _
  have hJac : JacobsonSpace S.group.X.left := LocallyOfFiniteType.jacobsonSpace S.group.X.hom
  have hsurj : Surjective p := by
    constructor
    have hcl := (p.isClosedEmbedding.isClosed_range).closure_subset_iff.mpr hfib
    rw [closure_closedPoints] at hcl
    exact Set.range_eq_univ.mp (Set.Subset.antisymm (Set.subset_univ _) hcl)
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  let j : S.group.X.left ⟶ T.group.X.left := inv p ≫ pullback.fst t.left s.left
  have hj : j ≫ t.left = s.left := by simp [j, p, pullback.condition]
  let j' : S.group.X ⟶ T.group.X :=
    Over.homMk j (by
      rw [← Over.w t, ← Category.assoc, hj, Over.w s])
  have hj' : j' ≫ t = s := by
    apply Over.OverMorphism.ext
    exact hj
  have : Mono t := Over.mono_of_mono_left t
  have hj₁ (B : TestAlgebra K) : (1 : Points S.group.X B) ≫ j' = 1 := by
    apply (cancel_mono t).mp
    simp only [Category.assoc, hj', MonObj.one_comp]
  have hjm (B : TestAlgebra K) (x y : Points S.group.X B) :
      (x * y) ≫ j' = (x ≫ j') * (y ≫ j') := by
    apply (cancel_mono t).mp
    have h := MonObj.mul_comp (x ≫ j') (y ≫ j') t
    rw [Category.assoc, hj']
    rw [h, Category.assoc, Category.assoc, hj']
    exact MonObj.mul_comp x y s
  let : IsMonHom j' := isMonHom_of_ring_points hAffine j' hj₁ hjm
  refine ⟨Grp.homMk j', ?_⟩
  apply Grp.hom_ext
  exact hj'

end GeometricSubgroupInclusion

section GeometricFrameMaximality

open Opposite CategoryTheory.Limits
open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsMaximalTorus IsTorus)
open PeirceSpecification (ZornIsomorphism)
open private isCommMonObj_of_groupIso from LinearAlgebraicGroups.Affine.HopfAlgebras

variable {K : Type u} [Field K] [IsAlgClosed K]
  {C : Type v} [NonAssocRing C] [Module K C] [IsScalarTower K C C] [SMulCommClass K C C]
  {n : QuadraticForm K C}

private theorem frameTorus_isTorus : IsTorus (frameTorus K) := by
  obtain ⟨i, _⟩ := frameTorusBaseChange (R := K) (K := K)
  obtain ⟨r, ⟨j⟩⟩ := frameTorus_isSplit (K := K)
  exact ⟨K, inferInstance, inferInstance, inferInstance, r, ⟨i ≪≫ j⟩⟩

private theorem torus_reduced_of_algClosed {H : GroupScheme K} (h : IsTorus H) :
    IsReduced H.X.left := by
  obtain ⟨E, _, _, hsep, r, ⟨i⟩⟩ := h
  let : Algebra.IsSeparable K E := hsep
  let e : K ≃+* E := RingEquiv.ofBijective (algebraMap K E)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have : IsIso (fieldSpecMap K E) :=
    (Scheme.Spec : CommRingCatᵒᵖ ⥤ Scheme).map_isIso
      ((RingEquiv.toCommRingCatIso e).hom.op)
  let A := StandardGroups.LaurentPowerCoordinates E (ULift.{u} (Fin r))
  let : IsDomain A := inferInstanceAs (IsDomain (AddMonoidAlgebra E (ULift.{u} (Fin r) → ℤ)))
  let F := Grp.forget (SchemeOver E) ⋙ Over.forget _
  have hstd : IsReduced (F.obj (StandardGroups.multiplicativePowerGroup E (ULift.{u} (Fin r))).val) :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of A)))
  let hred : IsReduced (F.obj ((groupBaseChange K E).obj H)) :=
    @isReduced_of_isOpenImmersion _ _ (F.mapIso i).hom inferInstance hstd
  let π := pullback.fst H.X.hom (fieldSpecMap K E)
  let : IsIso π := inferInstanceAs (IsIso (pullback.fst H.X.hom (fieldSpecMap K E)))
  let : IsReduced ((pullback H.X.hom (fieldSpecMap K E) : Scheme.{u})) := hred
  exact isReduced_of_isOpenImmersion (inv π)

omit [IsAlgClosed K] in
private theorem affine_torus_commutative {H : GroupScheme K}
    (hA : IsAffine H.X.left) (h : IsTorus H) : IsCommMonObj H.X := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_hopfSpec.mpr hA
  obtain ⟨E, _, _, hsep, r, ⟨j⟩⟩ := h
  let hT : IsTorus (specGroup A.unop) :=
    ⟨E, inferInstance, inferInstance, hsep, r, ⟨(groupBaseChange K E).mapIso e ≪≫ j⟩⟩
  have hCoord := (LinearAlgebraicGroups.CharacterDescent.torusOnSchemes A.unop).mpr hT
  exact isCommMonObj_of_groupIso e
    (LinearAlgebraicGroups.CharacterDescent.multiplicativeTypeProperties A.unop
      (LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType A.unop hCoord)).2

omit [IsAlgClosed K] in
private theorem diagonalPoint_congr {d e : Fin 3 → Kˣ}
    (h : d = e) (hd : d 0 * d 1 * d 2 = 1) (he : e 0 * e 1 * e 2 = 1) :
    diagonalPoint d hd = diagonalPoint e he := by
  subst e
  rfl

omit [IsAlgClosed K] in
private theorem splitPointGroupEquiv_frame_of_diagonal
    (F : ZornIsomorphism n) (A : AutomorphismGroup K C)
    (i : frameTorus K ⟶ A.group)
    (hi : ∀ S (t : framePoint S), t ≫ i.hom.hom = framePointMap F A S t)
    (d : Fin 3 → Kˣ) (hd : d 0 * d 1 * d 2 = 1)
    (t : framePoint (CommAlgCat.of K K)) (ht : frameUnits _ t = d) :
    splitPointGroupEquiv F A (t ≫ i.hom.hom) = diagonalPoint d hd := by
  rw [hi _ t, splitPointGroupEquiv_frame]
  exact diagonalPoint_congr ht _ _

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal frame torus is maximal over an algebraically closed field. -/
private theorem frameTorus_maximal_over_algClosed (F : ZornIsomorphism n)
    (A : AutomorphismGroup K C) (i : frameTorus K ⟶ A.group)
    (hci : IsClosedImmersion i.hom.hom.left)
    (hi : ∀ S (t : framePoint S), t ≫ i.hom.hom = framePointMap F A S t) :
    IsMaximalTorus (⟨frameTorus K, i, hci⟩ : ClosedSubgroup A.group) := by
  let T : ClosedSubgroup A.group := ⟨frameTorus K, i, hci⟩
  let G : AffineAlgebraicGroup K := ⟨A.group, A.groupAffine, A.groupFiniteType, A.groupQuasiCompact⟩
  change IsMaximalTorus T
  refine ⟨frameTorus_isTorus, ?_⟩
  intro S hS hTS
  let S' := Unipotent.closedSubgroupAlgebraicGroup (G := G) S
  let : IsCommMonObj S.group.X := affine_torus_commutative S'.property.1 hS
  let Gpoint := splitPointGroupEquiv F A
  obtain ⟨j, hj⟩ := hTS
  obtain ⟨d, hd, hweights⟩ := exists_distinct_trace_weights (K := K)
  obtain ⟨t, ht⟩ := exists_framePoint_for_diagonal (CommAlgCat.of K K) d hd
  have hTd := splitPointGroupEquiv_frame_of_diagonal F A i hi d hd t ht
  refine subgroupOf_of_geometricPoints T S (torus_reduced_of_algClosed hS) S'.property.1
    S'.property.2.1 ?_
  intro p
  let B := CommAlgCat.of K K
  let q : Points S.group.X B := t ≫ j.hom.hom
  have hcomm : Commute q p := by
    let := ((isCommMonObj_iff_isMulCommutative S.group.X).mp (show IsCommMonObj S.group.X from inferInstance))
      ((testSpec K).obj (op B))
    exact mul_comm' _ _
  let incl : Points S.group.X B →* Points A.group.X B :=
    { toFun := fun p => p ≫ S.inclusion.hom.hom
      map_one' := MonObj.one_comp _
      map_mul' := fun p q => MonObj.mul_comp p q _ }
  have hq : incl q = t ≫ i.hom.hom := by
    change (t ≫ j.hom.hom) ≫ S.inclusion.hom.hom = _
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (t ≫ ·) (congrArg (fun f : T.group ⟶ A.group => f.hom.hom) hj)
  have hc := hcomm.map (Gpoint.toMonoidHom.comp incl)
  change Commute (Gpoint (incl q)) (Gpoint (incl p)) at hc
  rw [hq, show Gpoint (t ≫ i.hom.hom) = diagonalPoint d hd from hTd] at hc
  obtain ⟨c, hcp, hc⟩ := point_centralizer_of_separating_diagonal d hd hweights _ hc
  obtain ⟨b, hb⟩ := exists_framePoint_for_diagonal B c hcp
  refine ⟨b, Gpoint.injective ?_⟩
  exact (splitPointGroupEquiv_frame_of_diagonal F A i hi c hcp b hb).trans hc.symm

end GeometricFrameMaximality

section ScalarOctonionActions

variable {K : Type u} [Field K]

/-- A scalar action on trace zero has scalar one, by multiplication of two
upper coordinate vectors. -/
private theorem point_eq_one_of_scalar_trace (g : ZornPointGroup K) (c : K)
    (h : (traceRepresentation g).val = c • (1 : Module.End K (traceZero K))) : g = 1 := by
  have hg (x : traceZero K) : g.val.val x.val = c • x.val := by
    have hx := DFunLike.congr_fun h x
    exact congrArg Subtype.val hx
  let x := traceBasis (K := K) (some (false, 0))
  let y := traceBasis (K := K) (some (false, 1))
  let z := traceBasis (K := K) (some (true, 2))
  have hp : x.val * y.val = z.val := upper_basis_product
  have hz : z.val ≠ 0 := fun h => traceBasis_ne_zero _ (Subtype.ext h)
  have hc : c = c * c := by
    have hh := point_mul g x.val y.val
    rw [hp, hg z, hg x, hg y, smul_mul_assoc, mul_smul_comm, smul_smul, hp] at hh
    exact smul_left_injective K hz hh
  have hne : c ≠ 0 := by
    intro h0
    have h₁ : g.val.val z.val = g.val.val 0 := by
      rw [hg z, h0, zero_smul, map_zero]
    exact hz ((LinearMap.GeneralLinearGroup.toLinearEquiv g.val).injective h₁)
  have h₁ : c = 1 := mul_left_cancel₀ hne (hc.symm.trans (mul_one c).symm)
  apply point_eq_one_of_fixes_trace
  intro x
  rw [hg x, h₁, one_smul]

/-- In characteristic two the induced nondegenerate opposite-corner pairing
forces a scalar action on the trace-zero quotient to have scalar one. -/
private theorem point_eq_one_of_scalar_quotient (h2 : (2 : K) = 0)
    (g : ZornPointGroup K) (c : K)
    (h : (quotientRepresentation g).val = c • (1 : Module.End K (traceZeroQuotient K))) :
    g = 1 := by
  have hg (x : traceZero K) : ∃ a : K, g.val.val x.val = a • (1 : Zorn K) + c • x.val := by
    have hp := DFunLike.congr_fun h (Submodule.Quotient.mk x : traceZeroQuotient K)
    rw [quotientRepresentation_apply] at hp
    change (Submodule.Quotient.mk ((traceRepresentation g).val x) : traceZeroQuotient K) =
      Submodule.Quotient.mk (c • x) at hp
    have hm := (Submodule.Quotient.eq (scalarTraceLine K)).mp hp
    change g.val.val x.val - c • x.val ∈ scalarLine K at hm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨a, eq_add_of_sub_eq ha.symm⟩
  let x := traceBasis (K := K) (some (false, 0))
  let y := traceBasis (K := K) (some (true, 0))
  let B := (Zorn.norm K).polarBilin
  obtain ⟨a, ha⟩ := hg x
  obtain ⟨b, hb⟩ := hg y
  have hB (u v : Zorn K) : B (g.val.val u) (g.val.val v) = B u v := by
    have H := congrArg (fun q : QuadraticForm K (Zorn K) => q.polarBilin u v) (point_norm_trace g).1
    simpa only [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply] using H
  have h1 : B 1 1 = 0 := (compositionTrace_one (Zorn.isOctonion K).toNormLaws).trans h2
  have hx : B x.val 1 = 0 := x.property
  have hy : B 1 y.val = 0 := by
    rw [show B 1 y.val = B y.val 1 from QuadraticMap.polar_comm _ _ _]
    exact y.property
  have hxy : B x.val y.val = -1 := by
    change (Zorn.norm K).polarBilin
      (traceBasis (K := K) (some (false, 0))).val (traceBasis (K := K) (some (true, 0))).val = -1
    rw [traceBasis_upper_val, traceBasis_lower_val, Zorn.polar_formula]
    simp [dotProduct, Fin.sum_univ_three]
  have hh := hB x.val y.val
  rw [ha, hb] at hh
  simp only [LinearMap.add_apply, map_add, LinearMap.smul_apply, map_smul, h1, hx, hy, hxy,
    smul_eq_mul, mul_zero, zero_add, add_zero, mul_neg, mul_one] at hh
  have hc : c * c = 1 := neg_injective hh
  have hpow : (c - 1) ^ 2 = 0 := by
    rw [sub_sq, pow_two c, hc, h2]
    simpa only [zero_mul, sub_zero, one_pow, one_add_one_eq_two] using h2
  have h₁ : c = 1 := sub_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hpow)
  apply (injective_iff_map_eq_one _).mp (quotient_representation_injective (K := K))
  apply Units.ext
  rw [h, h₁, one_smul]
  rfl

end ScalarOctonionActions

section RootLattice

open _root_.LinearAlgebraicGroups.Specs
open CharacterDescent (Character)
open CharacterPairing (absoluteRoots)
open SchemeCentre (rootLattice)

variable {K : Type u} [Field K]

private def charactersAlongIso {T H : GroupScheme K} (i : T ≅ H) :
    Character H ≃* Character T where
  toFun χ := i.hom ≫ χ
  invFun χ := i.inv ≫ χ
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' χ ψ := by
    apply Grp.hom_ext
    exact MonObj.comp_mul i.hom.hom.hom χ.hom.hom ψ.hom.hom

private def rootFrameCharacters {G : GroupScheme K} {T : ClosedSubgroup G}
    (i : T.group ≅ frameTorus K) : Fin 3 → Character T.group :=
  fun j => i.hom ≫ frameCharacterEquiv (K := K) (frameExponent j)

/-- Once the nonzero tangent weights have the specified list, the diagonal
characters generate the entire lattice and satisfy precisely the determinant relation. -/
private theorem hasG2Roots_of_tangent_weights {G : GroupScheme K} {T : ClosedSubgroup G}
    (i : T.group ≅ frameTorus K)
    (hw : let ε := rootFrameCharacters i
      absoluteRoots T =
        {χ | (∃ i j : Fin 3, i ≠ j ∧ χ = ε i * (ε j)⁻¹) ∨
          (∃ i : Fin 3, χ = ε i ∨ χ = (ε i)⁻¹)}) :
    HasG2Roots T (rootFrameCharacters i) := by
  let e : FrameCharacters.{u} ≃* Character T.group :=
    (frameCharacterEquiv (K := K)).trans (charactersAlongIso i)
  have hχ (j : Fin 3) : rootFrameCharacters i j = e (frameExponent j) := rfl
  refine ⟨?_, ?_, hw, ?_⟩
  · simp only [hχ, ← map_prod, Fin.prod_univ_three, frameExponents_product, map_one]
  · intro m
    simp only [hχ, ← map_zpow, ← map_prod, ← e.map_one, e.injective.eq_iff]
    exact frameExponents_relations m
  · apply top_unique
    intro χ _
    obtain ⟨m, rfl⟩ := e.surjective χ
    have h (j : Fin 3) : e (frameExponent j) ∈ rootLattice T := by
      apply Subgroup.subset_closure
      rw [hw]
      exact Or.inr ⟨j, Or.inl (hχ j).symm⟩
    rw [← frameExponent_decompose m, map_mul, map_zpow, map_zpow]
    exact (rootLattice T).mul_mem
      ((rootLattice T).zpow_mem (h 0) _) ((rootLattice T).zpow_mem (h 1) _)

end RootLattice

private theorem octonionAutomorphismsOverField_of_ring
    (h : OctonionAutomorphisms.{u, v}) : OctonionAutomorphismsOverField.{u, v} := by
  intro k _ C _ _ _ _ n hn hd
  exact h ((octonion_norm_iff_field n).mpr ⟨hn, hd⟩)

section SplitAlgebraExtension

open PeirceSpecification (ZornIsomorphism)
open scoped TensorProduct

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] [Module.Projective R C]
  {n : QuadraticForm R C}

omit [IsScalarTower R C C] [SMulCommClass R C C] in
private theorem splitCoordinates_norm (F : ZornIsomorphism n) (S : Type u)
    [CommRing S] [Algebra R S] (x : Zorn S) :
    normBaseChange S n (splitCoordinates F S x) = Zorn.norm S x := by
  let e := F.toLinearEquiv.baseChange R S (Zorn R) C
  have h0 : n.comp F.toLinearEquiv.toLinearMap = Zorn.norm R := by
    ext y
    exact F.map_norm y
  have hp (x y : S ⊗[R] Zorn R) : (normBaseChange S n).polarBilin (e x) (e y) =
      (normBaseChange S (Zorn.norm R)).polarBilin x y := by
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
        have hh := congrArg (fun q : QuadraticForm R (Zorn R) => q.polarBilin x y) h0
        rw [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply] at hh
        simp only [e, LinearEquiv.baseChange_tmul]
        rw [polar_normBaseChange S n, polar_normBaseChange S (Zorn.norm R),
          LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]
        exact congrArg (fun c : R => c • (a * b)) hh
      | add y z hy hz => simp only [map_add, hy, hz]
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  have hq (x : S ⊗[R] Zorn R) :
      normBaseChange S n (e x) = normBaseChange S (Zorn.norm R) x := by
    induction x using TensorProduct.inductionOn with
    | tmul a x => simp [e, normBaseChange_tmul, F.map_norm]
    | add x y hx hy =>
      rw [map_add, QuadraticMap.map_add (normBaseChange S n) (e x) (e y),
        QuadraticMap.map_add (normBaseChange S (Zorn.norm R)) x y, hx, hy]
      exact congrArg (fun b => normBaseChange S (Zorn.norm R) x +
        normBaseChange S (Zorn.norm R) y + b) (hp x y)
  obtain ⟨y, rfl⟩ := (ZornSpecification.baseChange R S).surjective x
  simp only [splitCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact (hq y).trans (DFunLike.congr_fun (Zorn.baseChange_norm (R := R) (S := S)) y)

private def zornIsomorphismBaseChange (F : ZornIsomorphism n) (S : Type u)
    [CommRing S] [Algebra R S] : ZornIsomorphism (normBaseChange S n) where
  toLinearEquiv := splitCoordinates F S
  map_one := splitCoordinates_one F S
  map_mul := splitCoordinates_mul F S
  map_norm := splitCoordinates_norm F S

end SplitAlgebraExtension

section SplitCoordinateTower

open PeirceSpecification (ZornIsomorphism)
open TensorProduct.AlgebraTensorModule (cancelBaseChange cancelBaseChange_tmul)
open scoped TensorProduct
open private zornBasis map_zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] [Module.Projective R C]
  {n : QuadraticForm R C}

omit [IsScalarTower R C C] [SMulCommClass R C C] [Module.Projective R C] in
private theorem splitCoordinates_basis (F : ZornIsomorphism n) (S : Type u)
    [CommRing S] [Algebra R S] (j : Option (Fin 3) ⊕ Option (Fin 3)) :
    splitCoordinates F S (zornBasis S j) = (1 : S) ⊗ₜ[R] F.toLinearEquiv (zornBasis R j) := by
  have h : ZornSpecification.baseChange R S ((1 : S) ⊗ₜ[R] zornBasis R j) = zornBasis S j := by
    rw [Zorn.baseChange_tmul, one_smul, map_zornBasis]
  rw [← h, splitCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.baseChange_tmul]

variable {K : Type u} [CommRing K] [Algebra R K]

/-- The split coordinates agree when an intermediate scalar extension is cancelled. -/
private theorem splitCoordinates_scalarTower (F : ZornIsomorphism n)
    (S : CommAlgCat.{u} K) (x : Zorn S) :
    tensorScalarExtension (R := R) S (splitCoordinates (zornIsomorphismBaseChange F K) S x) =
      splitCoordinates F (forgetScalars (R := R) S) x := by
  let B := forgetScalars (R := R) S
  let f : Zorn S →ₗ[S] B ⊗[R] C :=
    (tensorScalarExtension (R := R) S).toLinearMap.comp
      (splitCoordinates (zornIsomorphismBaseChange F K) S).toLinearMap
  let g : Zorn S →ₗ[S] B ⊗[R] C := (splitCoordinates F B).toLinearMap
  suffices hf : f = g from LinearMap.congr_fun hf x
  apply (zornBasis S).ext
  intro j
  change tensorScalarExtension (R := R) S
      (splitCoordinates (zornIsomorphismBaseChange F K) S (zornBasis S j)) =
    splitCoordinates F B (zornBasis B j)
  rw [splitCoordinates_basis, splitCoordinates_basis]
  change tensorScalarExtension (R := R) S ((1 : S) ⊗ₜ[K] splitCoordinates F K (zornBasis K j)) = _
  rw [splitCoordinates_basis]
  let : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  change cancelBaseChange R K S S C
      ((1 : S) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] F.toLinearEquiv (zornBasis R j))) = _
  rw [cancelBaseChange_tmul, one_smul]

end SplitCoordinateTower

section ScalarExtendedFrameAction

open PeirceSpecification (ZornIsomorphism)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)
open scoped TensorProduct

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}
  {K : Type u} [CommRing K] [Algebra R K]

local notation "↓" S => (forgetScalars (R := R) S)

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtendedSubgroupPoints_apply
    (A : AutomorphismGroup R C) (S : CommAlgCat.{u} K)
    (g : ringPoint ((scalarExtensionGroup K).obj A.group).X S)
    (x : S ⊗[K] (K ⊗[R] C)) :
    tensorScalarExtension (R := R) S ((scalarExtendedSubgroupPoints A S g).val.val x) =
      (A.subgroupPoints (↓S) (forgetFiberPoint A.group.X S g)).val.val
        (tensorScalarExtension (R := R) S x) := by
  have h := conjugateUnits_apply (tensorScalarExtension (R := R) S)
    (scalarExtendedSubgroupPoints A S g).val x
  have he : tensorScalarExtensionUnits (R := R) (C := C) S ((scalarExtendedSubgroupPoints A S g).val) =
      (A.subgroupPoints (↓S) (forgetFiberPoint A.group.X S g)).val :=
    congrArg Subtype.val ((tensorScalarExtensionStabilizer (R := R) (C := C) S).apply_symm_apply _)
  change (tensorScalarExtensionUnits (R := R) (C := C) S
    (scalarExtendedSubgroupPoints A S g).val).val _ = _ at h
  rw [he] at h
  exact h.symm

variable [Module.Projective R C]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 550000 in
private theorem isFrameTorus_scalarExtension (F : ZornIsomorphism n)
    (A : AutomorphismGroup R C) (i : frameTorus R ⟶ A.group) (hi : IsFrameTorus F A i)
    (e : (scalarExtensionGroup (R := R) K).obj (frameTorus R) ≅ frameTorus K)
    (he : ∀ (S : CommAlgCat.{u} K) (t : ringPoint ((scalarExtensionGroup (R := R) K).obj (frameTorus R)).X S)
      (j : Fin 3), frameCoordinate j S (t ≫ e.hom.hom.hom) =
        frameCoordinate j (↓S) (forgetFiberPoint (frameTorus R).X S t)) :
    IsFrameTorus (zornIsomorphismBaseChange F K) (scalarExtendedAutomorphisms A)
      (e.inv ≫ (scalarExtensionGroup K).map i) := by
  intro S t x
  let q : ringPoint ((scalarExtensionGroup (R := R) K).obj (frameTorus R)).X S := t ≫ e.inv.hom.hom
  let p : framePoint (↓S) := forgetFiberPoint (frameTorus R).X S q
  have hq : q ≫ e.hom.hom.hom = t := by
    change (t ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = t
    rw [Category.assoc]
    have hz := congrArg (fun f : frameTorus K ⟶ frameTorus K => f.hom.hom) e.inv_hom_id
    exact (congrArg (t ≫ ·) hz).trans (Category.comp_id _)
  have hc (j : Fin 3) : frameCoordinate j S t = frameCoordinate j (↓S) p := by
    simpa only [hq] using he S q j
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective x
  change (scalarExtendedSubgroupPoints A S (t ≫ (e.inv ≫ (scalarExtensionGroup K).map i).hom.hom)).val.val
      (splitCoordinates (zornIsomorphismBaseChange F K) S (Zorn.ofCoordinates (a, u, v, b))) =
    splitCoordinates (zornIsomorphismBaseChange F K) S (Zorn.ofCoordinates
      (a, fun j => frameCoordinate j S t * u j,
        fun j => frameCoordinate (j + 1) S t * frameCoordinate (j + 2) S t * v j, b))
  have hpt : forgetFiberPoint A.group.X S (t ≫ (e.inv ≫ (scalarExtensionGroup K).map i).hom.hom) =
      p ≫ i.hom.hom := by
    change forgetFiberPoint A.group.X S (t ≫ e.inv.hom.hom ≫ (scalarExtension K).map i.hom.hom) = _
    rw [← Category.assoc]
    exact forgetFiberPoint_comp i.hom.hom S q
  apply (tensorScalarExtension (R := R) (C := C) S).injective
  rw [scalarExtendedSubgroupPoints_apply, hpt, splitCoordinates_scalarTower, splitCoordinates_scalarTower]
  simp only [hc]
  exact hi (↓S) p (Zorn.ofCoordinates (a, u, v, b))

end ScalarExtendedFrameAction

section FrameGeometricMaximality

open PeirceSpecification (ZornIsomorphism)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)
open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsMaximalTorus IsTorus IsSplitTorus baseChangedSubgroup)
open RankOneFlag (IsGeometricallyMaximal)
open scoped TensorProduct
open private zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}

set_option backward.isDefEq.respectTransparency false in
private theorem framePointMap_eq_of_frame_action (F : ZornIsomorphism n)
    (A : AutomorphismGroup R C) (i : frameTorus R ⟶ A.group) (hi : IsFrameTorus F A i)
    (S : CommAlgCat.{u} R) (t : framePoint S) :
    t ≫ i.hom.hom = framePointMap F A S t := by
  obtain ⟨j, hj, hm⟩ := exists_frameTorusMorphism F A
  rw [← hm S t]
  apply (A.subgroupPoints S).injective
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (splitCoordinates F S).surjective y
  exact (hi S t x).trans (hj S t x).symm

variable [Module.Projective R C]
  {K : Type u} [Field K] [Algebra R K]

set_option backward.isDefEq.respectTransparency false in
private theorem frameMaximality_of_iso {E : Type u} [Field E] {G : GroupScheme E}
    (T : ClosedSubgroup G) (i : frameTorus E ⟶ G) (hi : IsClosedImmersion i.hom.hom.left)
    (e : T.group ≅ frameTorus E) (he : e.inv ≫ T.inclusion = i)
    (hm : IsMaximalTorus (⟨frameTorus E, i, hi⟩ : ClosedSubgroup G)) :
    IsMaximalTorus T := by
  refine ⟨⟨E, inferInstance, inferInstance, inferInstance, ?_⟩, ?_⟩
  · obtain ⟨j, _⟩ := frameTorusBaseChange (R := E) (K := E)
    obtain ⟨r, ⟨k⟩⟩ := frameTorus_isSplit (K := E)
    exact ⟨r, ⟨(groupBaseChange E E).mapIso e ≪≫ j ≪≫ k⟩⟩
  · intro S hS hTS
    obtain ⟨j, hj⟩ := hTS
    obtain ⟨k, hk⟩ := hm.2 S hS ⟨e.inv ≫ j, by rw [Category.assoc, hj]; exact he⟩
    exact ⟨k ≫ e.inv, by rw [Category.assoc, he]; exact hk⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
private theorem scalarExtendedFrameTorus_geometricallyMaximal (F : ZornIsomorphism n)
    (A : AutomorphismGroup R C) (i : frameTorus R ⟶ A.group) (hi : IsFrameTorus F A i)
    (h : IsClosedImmersion ((scalarExtensionGroup K).map i).hom.hom.left) :
    IsGeometricallyMaximal
      (⟨(scalarExtensionGroup K).obj (frameTorus R), (scalarExtensionGroup K).map i, h⟩ :
        ClosedSubgroup ((scalarExtensionGroup K).obj A.group)) := by
  let T : ClosedSubgroup ((scalarExtensionGroup K).obj A.group) :=
    ⟨(scalarExtensionGroup K).obj (frameTorus R), (scalarExtensionGroup K).map i, h⟩
  let E := AlgebraicClosure K
  let B := groupBaseChange K E
  let F' := zornIsomorphismBaseChange F K
  let A' := scalarExtendedAutomorphisms (K := K) A
  let : Module.Free K (K ⊗[R] C) := Module.Free.of_basis ((zornBasis K).map F'.toLinearEquiv)
  let A'' := scalarExtendedAutomorphisms (K := E) A'
  let : IsClosedImmersion T.inclusion.hom.hom.left := h
  have hgeom : IsClosedImmersion (B.map T.inclusion).hom.hom.left :=
    scalarExtension_isClosedImmersion (K := E) T.inclusion.hom.hom
  refine ⟨hgeom, ?_⟩
  let T' := baseChangedSubgroup E T hgeom
  obtain ⟨e, he⟩ := frameTorusBaseChange (R := R) (K := K)
  obtain ⟨e', he'⟩ := frameTorusBaseChange (R := K) (K := E)
  let j : frameTorus K ⟶ A'.group := e.inv ≫ T.inclusion
  let j' : frameTorus E ⟶ A''.group := e'.inv ≫ B.map j
  have hj : IsFrameTorus F' A' j := isFrameTorus_scalarExtension F A i hi e he
  have hj' : IsFrameTorus (zornIsomorphismBaseChange F' E) A'' j' :=
    isFrameTorus_scalarExtension F' A' j hj e' he'
  let e'' : T'.group ≅ frameTorus E := B.mapIso e ≪≫ e'
  have he'' : e''.inv ≫ T'.inclusion = j' := by
    change (e'.inv ≫ B.map e.inv) ≫ B.map T.inclusion = e'.inv ≫ B.map (e.inv ≫ T.inclusion)
    rw [Functor.map_comp, Category.assoc]
  have hjc : IsClosedImmersion j'.hom.hom.left := by
    rw [← he'']
    let FF := Grp.forget (RingScheme E) ⋙ Over.forget _
    have : IsIso e''.inv.hom.hom.left := by
      change IsIso (FF.map e''.inv)
      infer_instance
    let : IsClosedImmersion T'.inclusion.hom.hom.left := hgeom
    change IsClosedImmersion (e''.inv.hom.hom.left ≫ T'.inclusion.hom.hom.left)
    infer_instance
  exact frameMaximality_of_iso T' j' hjc e'' he''
    (frameTorus_maximal_over_algClosed _ A'' j' hjc (framePointMap_eq_of_frame_action _ A'' j' hj'))

end FrameGeometricMaximality

section MarkedGeometricFrame

open PeirceSpecification (ZornIsomorphism)
open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open CharacterPairing (characterValue)

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]

set_option backward.isDefEq.respectTransparency false in
private theorem rootFrameCharacters_eval {G : GroupScheme K} {T : ClosedSubgroup G}
    (e : T.group ≅ frameTorus K) (S : TestAlgebra K) (t : Points T.group.X S)
    (j : Fin 3) :
    characterValue (rootFrameCharacters e j) S t =
      frameCoordinate j S (t ≫ e.hom.hom.hom) := by
  rw [← frameCharacterEquiv_eval]
  unfold characterValue rootFrameCharacters
  have he : (e.hom ≫ frameCharacterEquiv (K := K) (frameExponent j)).hom.hom =
      e.hom.hom.hom ≫ (frameCharacterEquiv (K := K) (frameExponent j)).hom.hom := rfl
  rw [he, Category.assoc]


private theorem scalarExtendedFrameTorus_isSplit :
    IsSplitTorus ((scalarExtensionGroup (R := R) K).obj (frameTorus R)) := by
  obtain ⟨e, _⟩ := frameTorusBaseChange (R := R) (K := K)
  obtain ⟨r, ⟨j⟩⟩ := frameTorus_isSplit (K := K)
  exact ⟨r, ⟨e ≪≫ j⟩⟩

end MarkedGeometricFrame

section DerivationPeirce

open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (IsDerivation)

variable {R : Type u} [CommRing R]
  {D : Module.End R (Zorn R)} (hD : IsDerivation (LinearMap.mul R (Zorn R)) D)
include hD

/-- A derivation can move the first idempotent only in the two vector corners. -/
private theorem derivation_first_scalar_slots :
    (Zorn.coordinates R (D (Zorn.first R))).1 = 0 ∧
      (Zorn.coordinates R (D (Zorn.first R))).2.2.2 = 0 := by
  obtain ⟨⟨a, u, v, b⟩, h⟩ := (Zorn.coordinates R).symm.surjective (D (Zorn.first R))
  have hd := hD (Zorn.first R) (Zorn.first R)
  change D (Zorn.first R * Zorn.first R) =
    D (Zorn.first R) * Zorn.first R + Zorn.first R * D (Zorn.first R) at hd
  rw [(Zorn.complementary_idempotents R).1, ← h] at hd
  change (Zorn.coordinates R).symm (a, u, v, b) =
    (Zorn.coordinates R).symm
      (zornProduct (a, u, v, b) (1, 0, 0, 0) + zornProduct (1, 0, 0, 0) (a, u, v, b)) at hd
  have hc := (Zorn.coordinates R).symm.injective hd
  have ha := congrArg Prod.fst hc
  have hb := congrArg (fun z : ZornCoordinates R => z.2.2.2) hc
  simp only [zornProduct, Prod.mk_add_mk, mul_one, one_mul, dotProduct_zero, zero_dotProduct, add_zero] at ha
  simp only [zornProduct, Prod.mk_add_mk, mul_zero, zero_mul, dotProduct_zero,
    zero_dotProduct, add_zero] at hb
  rw [← h, LinearEquiv.apply_symm_apply]
  exact ⟨add_left_cancel (show a + a = a + 0 by rw [← ha, add_zero]), hb⟩

private theorem derivation_one_zero : D 1 = 0 := by
  have h := hD (1 : Zorn R) 1
  change D ((1 : Zorn R) * 1) = D 1 * 1 + 1 * D 1 at h
  rw [one_mul, mul_one, one_mul] at h
  apply add_left_cancel (a := D 1)
  rw [← h, add_zero]

private theorem derivation_second_zero (h : D (Zorn.first R) = 0) :
    D (Zorn.second R) = 0 := by
  have hu : D (Zorn.first R + Zorn.second R) = 0 := by
    rw [(Zorn.complementary_idempotents R).2.2.2.2, derivation_one_zero hD]
  rwa [map_add, h, zero_add] at hu

private theorem derivation_upper_of_first_zero (h : D (Zorn.first R) = 0)
    (w : Fin 3 → R) :
    ∃ w' : Fin 3 → R, D (Zorn.ofCoordinates (0, w, 0, 0)) =
      Zorn.ofCoordinates (0, w', 0, 0) := by
  let x : Zorn R := Zorn.ofCoordinates (0, w, 0, 0)
  have hx₁ : Zorn.first R * x = x := by
    change Zorn.ofCoordinates (zornProduct (1, 0, 0, 0) (0, w, 0, 0)) = _
    simp [zornProduct, x]
  have hx₂ : x * Zorn.first R = 0 := by
    change Zorn.ofCoordinates (zornProduct (0, w, 0, 0) (1, 0, 0, 0)) = _
    simp [zornProduct]
  have h₁ := hD (Zorn.first R) x
  have h₂ := hD x (Zorn.first R)
  change D (Zorn.first R * x) = D (Zorn.first R) * x + Zorn.first R * D x at h₁
  change D (x * Zorn.first R) = D x * Zorn.first R + x * D (Zorn.first R) at h₂
  rw [hx₁, h, zero_mul, zero_add] at h₁
  rw [hx₂, map_zero, h, mul_zero, add_zero] at h₂
  obtain ⟨⟨a, u, v, b⟩, hd⟩ := (Zorn.coordinates R).symm.surjective (D x)
  rw [← hd] at h₁ h₂
  have hh₁ : (a, u, v, b) = (a, u, (0 : Fin 3 → R), (0 : R)) := by
    apply (Zorn.coordinates R).symm.injective
    change Zorn.ofCoordinates (a, u, v, b) =
      Zorn.ofCoordinates (a, u, 0, 0)
    change Zorn.ofCoordinates (a, u, v, b) =
      Zorn.ofCoordinates (zornProduct (1, 0, 0, 0) (a, u, v, b)) at h₁
    simpa [zornProduct] using h₁
  have hh₂ : ((0, 0, 0, 0) : ZornCoordinates R) = (a, 0, v, 0) := by
    have hh : (0 : Zorn R) = Zorn.ofCoordinates (a, 0, v, 0) := by
      change (0 : Zorn R) =
        Zorn.ofCoordinates (zornProduct (a, u, v, b) (1, 0, 0, 0)) at h₂
      simpa [zornProduct] using h₂
    exact (Zorn.coordinates R).symm.injective
      (show (Zorn.coordinates R).symm (0, 0, 0, 0) = _ from hh)
  refine ⟨u, ?_⟩
  change D x = _
  have ha : (0 : R) = a := congrArg Prod.fst hh₂
  rw [← hd, hh₁, ← ha]

private theorem derivation_lower_of_first_zero (h : D (Zorn.first R) = 0)
    (w : Fin 3 → R) :
    ∃ w' : Fin 3 → R, D (Zorn.ofCoordinates (0, 0, w, 0)) =
      Zorn.ofCoordinates (0, 0, w', 0) := by
  let x : Zorn R := Zorn.ofCoordinates (0, 0, w, 0)
  have hx₁ : x * Zorn.first R = x := by
    change Zorn.ofCoordinates (zornProduct (0, 0, w, 0) (1, 0, 0, 0)) = _
    simp [zornProduct, x]
  have hx₂ : Zorn.first R * x = 0 := by
    change Zorn.ofCoordinates (zornProduct (1, 0, 0, 0) (0, 0, w, 0)) = _
    simp [zornProduct]
  have h₁ := hD x (Zorn.first R)
  have h₂ := hD (Zorn.first R) x
  change D (x * Zorn.first R) = D x * Zorn.first R + x * D (Zorn.first R) at h₁
  change D (Zorn.first R * x) = D (Zorn.first R) * x + Zorn.first R * D x at h₂
  rw [hx₁, h, mul_zero, add_zero] at h₁
  rw [hx₂, map_zero, h, zero_mul, zero_add] at h₂
  obtain ⟨⟨a, u, v, b⟩, hd⟩ := (Zorn.coordinates R).symm.surjective (D x)
  rw [← hd] at h₁ h₂
  have hh₁ : (a, u, v, b) = (a, (0 : Fin 3 → R), v, (0 : R)) := by
    apply (Zorn.coordinates R).symm.injective
    change Zorn.ofCoordinates (a, u, v, b) =
      Zorn.ofCoordinates (a, 0, v, 0)
    change Zorn.ofCoordinates (a, u, v, b) =
      Zorn.ofCoordinates (zornProduct (a, u, v, b) (1, 0, 0, 0)) at h₁
    simpa [zornProduct] using h₁
  have hh₂ : ((0, 0, 0, 0) : ZornCoordinates R) = (a, u, 0, 0) := by
    have hh : (0 : Zorn R) = Zorn.ofCoordinates (a, u, 0, 0) := by
      change (0 : Zorn R) =
        Zorn.ofCoordinates (zornProduct (1, 0, 0, 0) (a, u, v, b)) at h₂
      simpa [zornProduct] using h₂
    exact (Zorn.coordinates R).symm.injective
      (show (Zorn.coordinates R).symm (0, 0, 0, 0) = _ from hh)
  refine ⟨v, ?_⟩
  change D x = _
  have ha : (0 : R) = a := congrArg Prod.fst hh₂
  rw [← hd, hh₁, ← ha]

end DerivationPeirce

section SplitOrbitCoefficients

open Opposite
open PeirceSpecification (ZornIsomorphism)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)
open private pairedFunctions_mapCoordinates zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

variable {K : Type u} [Field K] {C : Type v} [NonAssocRing C] [Module K C]
  [IsScalarTower K C C] [SMulCommClass K C C] {n : QuadraticForm K C}

private def zornFunctionalValue (ℓ : Zorn K →ₗ[K] K)
    (S : Type u) [CommRing S] [Algebra K S] (x : Zorn S) : S :=
  ∑ j, Zorn.pairedFunctions S x j * algebraMap K S (ℓ (zornBasis K j))

private theorem zornFunctionalValue_base (ℓ : Zorn K →ₗ[K] K) (x : Zorn K) :
    zornFunctionalValue ℓ K x = ℓ x := by
  have h (j : Option (Fin 3) ⊕ Option (Fin 3)) :
      (zornBasis K).repr x j = Zorn.pairedFunctions K x j := by
    simp [zornBasis]
  calc
    _ = ∑ j, ℓ ((zornBasis K).repr x j • zornBasis K j) := by
      simp [zornFunctionalValue, h, smul_eq_mul]
    _ = _ := by rw [← map_sum, (zornBasis K).sum_repr]

private theorem zornFunctionalValue_natural (ℓ : Zorn K →ₗ[K] K)
    {S T : CommAlgCat.{u} K} (f : S ⟶ T) (x : Zorn S) :
    f.hom (zornFunctionalValue ℓ S x) =
      zornFunctionalValue ℓ T (ZornSpecification.mapCoordinates f.hom.toRingHom x) := by
  simp only [zornFunctionalValue, map_sum, map_mul, AlgHom.commutes,
    pairedFunctions_mapCoordinates, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

set_option backward.isDefEq.respectTransparency false in
private theorem splitOrbitCoordinate_regular (F : ZornIsomorphism n) (A : AutomorphismGroup K C)
    {D : Type u} [CommRing D] [Algebra K D] (i : affineScheme K D ≅ A.group.X)
    (x : Zorn K) (ℓ : Zorn K →ₗ[K] K) :
    ∃ a : D, ∀ d : D →ₐ[K] K,
      d a = ℓ ((splitPointGroupEquiv F A (affinePointEquiv i (CommAlgCat.of K K) d)).val.val x) := by
  let B := CommAlgCat.of K D
  let p : ((schemePoints K).obj A.group).obj B := i.hom
  let x' := ZornSpecification.mapCoordinates (algebraMap K D) x
  let a := zornFunctionalValue ℓ D ((splitSchemePoints F A B p).val x')
  refine ⟨a, fun d => ?_⟩
  let f : B ⟶ CommAlgCat.of K K := CommAlgCat.ofHom d
  have hn := splitSchemePoints_natural F A f p x'
  change (splitSchemePoints F A (CommAlgCat.of K K)
    (affinePointEquiv i (CommAlgCat.of K K) d)).val
      (ZornSpecification.mapCoordinates d.toRingHom x') = _ at hn
  have hx : ZornSpecification.mapCoordinates d.toRingHom x' = x := by
    obtain ⟨⟨b, u, v, c⟩, rfl⟩ := (Zorn.coordinates K).symm.surjective x
    apply (Zorn.coordinates K).injective
    change (d (algebraMap K D b), (fun j => d (algebraMap K D (u j))),
      (fun j => d (algebraMap K D (v j))), d (algebraMap K D c)) = (b, u, v, c)
    simp [AlgHom.commutes]
  change f.hom (zornFunctionalValue ℓ B ((splitSchemePoints F A B p).val x')) = _
  rw [zornFunctionalValue_natural, ← hn, hx, zornFunctionalValue_base]
  rfl

end SplitOrbitCoefficients

section PeirceTangentWeights

open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (IsDerivation)
open private zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

private abbrev ZornCoordinateIndex := Option (Fin 3) ⊕ Option (Fin 3)

private def zornCoordinateWeight : ZornCoordinateIndex → FrameCharacters.{u}
  | .inl (some i) => frameExponent i
  | .inr (some i) => (frameExponent i)⁻¹
  | .inl none | .inr none => 1

private def IsFrameRootExponent (m : FrameCharacters.{u}) : Prop :=
  (∃ i j : Fin 3, i ≠ j ∧ m = frameExponent i * (frameExponent j)⁻¹) ∨
  (∃ i : Fin 3, m = frameExponent i ∨ m = (frameExponent i)⁻¹)

variable {K : Type u} [CommRing K]

private theorem zornBasis_of_slots (j : ZornCoordinateIndex) :
    zornBasis K j = match j with
      | .inl none => Zorn.first K
      | .inr none => Zorn.second K
      | .inl (some i) => Zorn.ofCoordinates (0, Pi.single i 1, 0, 0)
      | .inr (some i) => Zorn.ofCoordinates (0, 0, -Pi.single i 1, 0) := by
  apply (Zorn.pairedFunctions K).injective
  funext k
  simp only [zornBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  rcases j with (j | j) <;> cases j <;> rcases k with (k | k) <;> cases k
  all_goals
    simp [ZornSpecification.first, ZornSpecification.second, Zorn.pairedFunctions, Zorn.pairedColumns,
      LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd, Pi.single_apply]

private theorem exists_nonzero_zornCoefficient {x : Zorn K} (hx : x ≠ 0) :
    ∃ i : ZornCoordinateIndex, Zorn.pairedFunctions K x i ≠ 0 := by
  by_contra! h
  apply hx
  apply (Zorn.pairedFunctions K).injective
  funext i
  simpa only [map_zero, Pi.zero_apply] using h i

private theorem exists_nonzero_zornEndCoefficient {D : Module.End K (Zorn K)} (hD : D ≠ 0) :
    ∃ j i : ZornCoordinateIndex, Zorn.pairedFunctions K (D (zornBasis K j)) i ≠ 0 := by
  by_contra! h
  apply hD
  apply (zornBasis K).ext
  intro j
  apply (Zorn.pairedFunctions K).injective
  funext i
  simpa only [LinearMap.zero_apply, map_zero, Pi.zero_apply] using h j i

/-- A nonzero nontrivial weight of a Zorn derivation has a short or a long
root exponent. A derivation moving the first idempotent is detected in one
of the two corners. A derivation fixing it preserves the corners. -/
private theorem derivation_weight_is_root {m : FrameCharacters.{u}} (hm : m ≠ 1)
    {D : Module.End K (Zorn K)} (hD : IsDerivation (LinearMap.mul K (Zorn K)) D) (hn : D ≠ 0)
    (h : ∀ i j : ZornCoordinateIndex, Zorn.pairedFunctions K (D (zornBasis K j)) i ≠ 0 →
      m = zornCoordinateWeight i * (zornCoordinateWeight j)⁻¹) :
    IsFrameRootExponent m := by
  by_cases he : D (Zorn.first K) = 0
  · have hf := derivation_second_zero hD he
    obtain ⟨j, i, hij⟩ := exists_nonzero_zornEndCoefficient hn
    have hw := h i j hij
    rw [zornBasis_of_slots] at hij
    rcases j with (j | j) <;> cases j
    · exact (hij (by simp [he])).elim
    · rename_i j
      obtain ⟨w, hw'⟩ := derivation_upper_of_first_zero hD he (Pi.single j 1)
      rw [hw'] at hij
      rcases i with (i | i) <;> cases i
      · exact (hij rfl).elim
      · rename_i i
        refine Or.inl ⟨i, j, ?_, hw⟩
        intro hh
        subst i
        exact hm (hw.trans (mul_inv_cancel _))
      · exact (hij rfl).elim
      · exact (hij (neg_zero)).elim
    · exact (hij (by simp [hf])).elim
    · rename_i j
      obtain ⟨w, hw'⟩ := derivation_lower_of_first_zero hD he (-Pi.single j 1)
      rw [hw'] at hij
      rcases i with (i | i) <;> cases i
      · exact (hij rfl).elim
      · exact (hij rfl).elim
      · exact (hij rfl).elim
      · rename_i i
        have hh : m = frameExponent j * (frameExponent i)⁻¹ := by
          simpa only [zornCoordinateWeight, inv_inv, mul_comm] using hw
        refine Or.inl ⟨j, i, ?_, hh⟩
        intro hj
        subst j
        exact hm (hh.trans (mul_inv_cancel _))
  · obtain ⟨i, hi⟩ := exists_nonzero_zornCoefficient he
    have hi' : Zorn.pairedFunctions K (D (zornBasis K (.inl none))) i ≠ 0 := by
      rw [zornBasis_of_slots]
      exact hi
    have hw := h i (.inl none) hi'
    simp only [zornCoordinateWeight, inv_one, mul_one] at hw
    obtain ⟨hfst, hsnd⟩ := derivation_first_scalar_slots hD
    rcases i with (i | i) <;> cases i
    · exact (hi hfst).elim
    · exact Or.inr ⟨_, Or.inl hw⟩
    · exact (hi hsnd).elim
    · exact Or.inr ⟨_, Or.inr hw⟩

end PeirceTangentWeights

section RootDerivationEquivariance

open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (IsDerivation)

variable {R : Type u} [CommRing R]

/-- The derivation moving the first idempotent in a lower Peirce direction. -/
private def lowerDerivationSlots (p : Fin 3 → R) (x : ZornCoordinates R) : ZornCoordinates R :=
  (-(p ⬝ᵥ x.2.1), p ⨯₃ x.2.2.1, (x.1 - x.2.2.2) • p, p ⬝ᵥ x.2.1)

private def lowerDerivation (p : Fin 3 → R) : Module.End R (Zorn R) :=
  (Zorn.coordinates R).symm.toLinearMap.comp <|
    ({ toFun := lowerDerivationSlots p
       map_add' := by
         rintro ⟨a, x, y, b⟩ ⟨c, u, v, d⟩
         simp only [lowerDerivationSlots, Prod.mk_add_mk, Prod.mk.injEq, dotProduct_add,
           neg_add, map_add, ← add_smul, true_and, and_true]
         congr 1
         abel
       map_smul' := by
         rintro r ⟨a, x, y, b⟩
         simp only [lowerDerivationSlots, Prod.smul_mk, RingHom.id_apply, dotProduct_smul,
           map_smul, smul_neg, Prod.mk.injEq, true_and, and_true]
         rw [smul_smul]
         congr 1
         exact (mul_sub r a b).symm } :
      Module.End R (ZornCoordinates R)).comp (Zorn.coordinates R).toLinearMap

private theorem lowerDerivation_first (p : Fin 3 → R) :
    lowerDerivation p (Zorn.first R) = Zorn.ofCoordinates (0, 0, p, 0) := by
  apply (Zorn.coordinates R).injective
  change lowerDerivationSlots p ((1 : R), 0, 0, 0) = (0, 0, p, 0)
  simp [lowerDerivationSlots]

private theorem lowerDerivation_rule (p : Fin 3 → R) :
    IsDerivation (LinearMap.mul R (Zorn R)) (lowerDerivation p) := by
  intro x y
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
  obtain ⟨⟨c, w, z, d⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective y
  apply (Zorn.coordinates R).injective
  change lowerDerivationSlots p (zornProduct (a, u, v, b) (c, w, z, d)) =
    zornProduct (lowerDerivationSlots p (a, u, v, b)) (c, w, z, d) +
      zornProduct (a, u, v, b) (lowerDerivationSlots p (c, w, z, d))
  simp only [lowerDerivationSlots, zornProduct, Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨?_, funext ?_, funext ?_, ?_⟩
  · simp [cross_apply, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro i
    fin_cases i <;>
      simp [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;> ring
  · intro i
    fin_cases i <;>
      simp [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] <;> ring
  · simp [cross_apply, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

private theorem diagonal_lowerDerivation (d : Fin 3 → Rˣ)
    (h : d 0 * d 1 * d 2 = 1) (p : Fin 3 → R) (x : Zorn R) :
    diagonalLinearEquiv d (lowerDerivation p x) =
      lowerDerivation (scaleVector d⁻¹ p) (diagonalLinearEquiv d x) := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
  apply (Zorn.coordinates R).injective
  change scaleSlots d (lowerDerivationSlots p (a, u, v, b)) =
    lowerDerivationSlots (scaleVector d⁻¹ p) (scaleSlots d (a, u, v, b))
  have hi : d⁻¹ 0 * d⁻¹ 1 * d⁻¹ 2 = 1 := by
    change (d 0)⁻¹ * (d 1)⁻¹ * (d 2)⁻¹ = 1
    rw [← mul_inv, ← mul_inv, h, inv_one]
  simp only [scaleSlots, lowerDerivationSlots, scale_cross d⁻¹ hi, inv_inv, show scaleVector d⁻¹ p ⬝ᵥ scaleVector d u = p ⬝ᵥ u by simpa only [inv_inv] using scale_dot d⁻¹ p u,
    Prod.mk.injEq, true_and, and_true]
  funext i
  simp [scaleVector, smul_eq_mul, mul_left_comm]

private theorem diagonal_elementaryDerivation (d : Fin 3 → Rˣ)
    (i j : Fin 3) (x : Zorn R) :
    diagonalLinearEquiv d (elementaryDerivation i j x) =
      (d i * (d j)⁻¹).val • elementaryDerivation i j (diagonalLinearEquiv d x) := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
  apply (Zorn.coordinates R).injective
  change scaleSlots d (elementaryDerivationSlots i j (a, u, v, b)) =
    (d i * (d j)⁻¹).val • elementaryDerivationSlots i j (scaleSlots d (a, u, v, b))
  simp only [elementaryDerivationSlots, scaleSlots, Prod.smul_mk, smul_zero,
    Prod.mk.injEq, true_and, and_true]
  constructor <;> funext k <;> simp only [scaleVector, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  · split_ifs with h
    · subst k
      rw [Units.val_mul, ← mul_assoc, mul_assoc (d i).val, Units.inv_mul, mul_one]
    · simp
  · split_ifs with h
    · subst k
      change ((d j)⁻¹ : Rˣ).val * -v i =
        (d i * (d j)⁻¹).val * -(((d i)⁻¹ : Rˣ).val * v i)
      rw [Units.val_mul, mul_neg, mul_neg, ← mul_assoc, mul_right_comm (d i).val,
        Units.mul_inv, one_mul]
    · simp

end RootDerivationEquivariance

section SplitInfinitesimalAction

open _root_.LinearAlgebraicGroups.Specs
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints infinitesimal IsDerivation)
open PeirceSpecification (ZornIsomorphism)
open scoped TensorProduct
open private schemeAction schemeAction_map_infinitesimal scalarPerturbation
  from LinearAlgebraicGroups.Albert.AutomorphismScheme

variable {K : Type u} [Field K] {C : Type v} [NonAssocRing C] [Module K C]
  [IsScalarTower K C C] [SMulCommClass K C C] {n : QuadraticForm K C}

private abbrev zornScalarMap (S : Type u) [CommRing S] [Algebra K S] :=
  ZornSpecification.mapCoordinates (algebraMap K S)

omit [IsScalarTower K C C] [SMulCommClass K C C] in
private theorem splitCoordinates_zornScalarMap (F : ZornIsomorphism n)
    (S : Type u) [CommRing S] [Algebra K S] (x : Zorn K) :
    splitCoordinates F S (zornScalarMap S x) = (1 : S) ⊗ₜ[K] F.toLinearEquiv x := by
  have h : ZornSpecification.baseChange K S ((1 : S) ⊗ₜ[K] x) = zornScalarMap S x := by
    rw [Zorn.baseChange_tmul, one_smul]
  rw [← h, splitCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.baseChange_tmul]

private def splitDerivationEndEquiv (F : ZornIsomorphism n) :
    Module.End K C ≃ₗ[K] Module.End K (Zorn K) :=
  F.toLinearEquiv.symm.conj

omit [IsScalarTower K C C] [SMulCommClass K C C] in
private theorem splitDerivationEndEquiv_apply (F : ZornIsomorphism n)
    (D : Module.End K C) (x : Zorn K) :
    F.toLinearEquiv (splitDerivationEndEquiv F D x) = D (F.toLinearEquiv x) :=
  F.toLinearEquiv.apply_symm_apply _

private theorem splitDerivationEndEquiv_iff (F : ZornIsomorphism n) (D : Module.End K C) :
    IsDerivation (LinearMap.mul K (Zorn K)) (splitDerivationEndEquiv F D) ↔
      IsDerivation (octonionAlgebra (R := K) (C := C)).product D := by
  constructor
  · intro h x y
    obtain ⟨x, rfl⟩ := F.toLinearEquiv.surjective x
    obtain ⟨y, rfl⟩ := F.toLinearEquiv.surjective y
    have hh := congrArg F.toLinearEquiv (h x y)
    change F.toLinearEquiv (splitDerivationEndEquiv F D (x * y)) =
      F.toLinearEquiv (splitDerivationEndEquiv F D x * y + x * splitDerivationEndEquiv F D y) at hh
    rw [map_add, F.map_mul, F.map_mul, splitDerivationEndEquiv_apply,
      splitDerivationEndEquiv_apply, splitDerivationEndEquiv_apply, F.map_mul] at hh
    exact hh
  · intro h x y
    apply F.toLinearEquiv.injective
    change F.toLinearEquiv (splitDerivationEndEquiv F D (x * y)) =
      F.toLinearEquiv (splitDerivationEndEquiv F D x * y + x * splitDerivationEndEquiv F D y)
    rw [map_add, F.map_mul, F.map_mul, splitDerivationEndEquiv_apply,
      splitDerivationEndEquiv_apply, splitDerivationEndEquiv_apply, F.map_mul]
    exact h (F.toLinearEquiv x) (F.toLinearEquiv y)

set_option backward.isDefEq.respectTransparency false in
private theorem splitSchemePoints_mul_action (F : ZornIsomorphism n)
    (A : AutomorphismGroup K C) (S : TestAlgebra K) (p q : Points A.group.X S) (x : Zorn S) :
    (splitSchemePoints F A S (p * q)).val x =
      (splitSchemePoints F A S p).val ((splitSchemePoints F A S q).val x) := by
  apply (splitCoordinates F S).injective
  rw [splitSchemePoints_action F A S (p * q),
    splitSchemePoints_action F A S p, splitSchemePoints_action F A S q, map_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem splitSchemePoints_map_infinitesimal (F : ZornIsomorphism n)
    (A : AutomorphismGroup K C) {S : TestAlgebra K}
    (f : CommAlgCat.of K (DualNumber K) ⟶ S)
    (p : Points A.group.X (CommAlgCat.of K (DualNumber K))) (D : Module.End K C)
    (hD : (A.subgroupPoints (CommAlgCat.of K (DualNumber K)) p).val.val = infinitesimal D)
    (x : Zorn K) :
    (splitSchemePoints F A S (mapPoints f p)).val (zornScalarMap S x) =
      zornScalarMap S x + f.hom (DualNumber.eps : DualNumber K) •
        zornScalarMap S (splitDerivationEndEquiv F D x) := by
  have h := schemeAction_map_infinitesimal A f p D hD
  apply (splitCoordinates F S).injective
  rw [map_add, map_smul, splitSchemePoints_action F A S (mapPoints f p),
    splitCoordinates_zornScalarMap, splitCoordinates_zornScalarMap,
    splitDerivationEndEquiv_apply]
  change (schemeAction A S (mapPoints f p)).val ((1 : S) ⊗ₜ[K] F.toLinearEquiv x) = _
  change (schemeAction A S ((((schemePoints K).obj A.group).map f) p)).val
    ((1 : S) ⊗ₜ[K] F.toLinearEquiv x) = _
  rw [h]
  change ((1 : S) ⊗ₜ[K] F.toLinearEquiv x) +
    f.hom (DualNumber.eps : DualNumber K) •
      D.baseChange S ((1 : S) ⊗ₜ[K] F.toLinearEquiv x) = _
  rw [LinearMap.baseChange_tmul]

end SplitInfinitesimalAction

section NormalSolvableSubgroups

open Opposite _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.GeometricRadicals (IsSmoothConnectedNormal IsTrivialSubgroup)
open private sections pointMap Regular Regular.comp solvable_commonEigenvectors orbit_in_eigenspace
  from LinearAlgebraicGroups.Solvable.LieKolchin
open private sections_normal trivial_of_subsingleton_sections rationalSections
  from LinearAlgebraicGroups.Reductive.GeometricRadicals

variable {K : Type u} [Field K] [IsAlgClosed K]

set_option backward.isDefEq.respectTransparency false in
private theorem normalSolvable_isTrivial_of_regularAction (G : AffineAlgebraicGroup K)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Nontrivial W]
    (π : sections G.val →* Module.End K W) (hπ : Regular π)
    (hI : ∀ U : Submodule K W,
      (∀ (p : sections G.val) (x : W), x ∈ U → π p x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hscalar : ∀ g : sections G.val, (∃ c : K, ∀ x : W, π g x = c • x) → g = 1)
    (N : ClosedSubgroup G.val) (hN : IsSmoothConnectedNormal N) (hsol : Specs.SchemeDerivedGroup.IsSolvable N.group) :
    IsTrivialSubgroup N := by
  let G' := Unipotent.closedSubgroupAlgebraicGroup N
  let j := pointMap N.inclusion
  have hj (p : sections N.group) : j p = p ≫ N.inclusion.hom.hom := rfl
  have hnormal := sections_normal hN.2.2 (𝟙_ (SchemeOver K))
  obtain ⟨v, hv, hEig⟩ := solvable_commonEigenvectors G' hN.1 hN.2.1 hsol W
    (π.comp j) (Regular.comp hπ N.inclusion)
  let U := Submodule.span K (Set.range (fun g : sections G.val => π g v))
  have hvU : v ∈ U := Submodule.subset_span (by exact ⟨1, by simp⟩)
  have hinv (g : sections G.val) : U ≤ U.comap (π g) := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨q, rfl⟩ := Set.mem_range.mp hx
    change π g (π q v) ∈ U
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span (Set.mem_range_self (g * q))
  have hU : U = ⊤ := (hI U (fun g _ hx => hinv g hx)).resolve_left
    (fun he => hv (by simpa [he] using hvU))
  have hp (p : sections N.group) : p = 1 := by
    obtain ⟨c, he⟩ := hEig p
    have hconj (g : sections G.val) :
        ∃ c' : K, π (j p) (π g v) = c' • π g v := by
      have hp' : j p ∈ SubgroupSections N (𝟙_ (SchemeOver K)) := ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := hnormal.conj_mem (j p) hp' g⁻¹
      change j q = g⁻¹ * j p * g⁻¹⁻¹ at hq
      rw [inv_inv] at hq
      have hpg : j p * g = g * j q := by rw [hq]; group
      obtain ⟨c', hc'⟩ := hEig q
      refine ⟨c', ?_⟩
      change π (j q) v = c' • v at hc'
      rw [← Module.End.mul_apply, ← map_mul, hpg, map_mul, Module.End.mul_apply, hc', map_smul]
    have he' := orbit_in_eigenspace G hs hc π hπ (π (j p)) hv he hconj
    have hspan : U ≤ (π (j p)).eigenspace c := by
      apply Submodule.span_le.mpr
      intro x hx
      obtain ⟨q, rfl⟩ := Set.mem_range.mp hx
      exact Module.End.mem_eigenspace_iff.mpr (he' q)
    have heq : j p = 1 := hscalar _ ⟨c, fun x => Module.End.mem_eigenspace_iff.mp
      (hspan (by rw [hU]; trivial))⟩
    let : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
    let : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [← hj p, heq, ← hj 1, map_one]
  let : Subsingleton (rationalSections G'.val) := ⟨fun p q => (hp p).trans (hp q).symm⟩
  exact trivial_of_subsingleton_sections G' hN.1

end NormalSolvableSubgroups

section GeometricUnipotentSolvability

open Opposite _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped commutatorElement
open private baseIso from LinearAlgebraicGroups.Solvable.LieKolchin
open private solvable_iff_sections rationalSections from LinearAlgebraicGroups.Reductive.GeometricRadicals

variable {K : Type u} [Field K]

set_option backward.isDefEq.respectTransparency false in
private theorem unipotent_test_points_solvable (G : AffineAlgebraicGroup K)
    (hu : Specs.Unipotent.IsUnipotent G) (R : TestAlgebra K) :
    Group.IsSolvable (Points G.val.X R) := by
  obtain ⟨n, S, hS⟩ := LinearAlgebraicGroups.Unipotent.unipotentNilpotence G hu
  let P := Points G.val.X R
  let f (j : ℕ) : Points (S.term j).val.X R →* P :=
    ((groupPointsFunctor K).map (S.inclusion j) |>.app R).hom
  have hd (j : ℕ) (hj : j ≤ n) : derivedSeries P j ≤ (f j).range := by
    induction j with
    | zero =>
      intro p _
      let e := ((groupPointsFunctor K).mapIso S.top).app R
      have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom e.inv_hom_id) p
      exact ⟨e.inv.hom p, h⟩
    | succ j ih =>
      rw [derivedSeries_succ]
      apply Subgroup.commutator_le.mpr
      intro p _ q hq
      obtain ⟨g, rfl⟩ := ih (Nat.le_of_succ_le hj) hq
      exact hS j (Nat.lt_of_succ_le hj) R p g
  have hbot : (f n).range ≤ ⊥ := by
    intro p hp
    obtain ⟨q, rfl⟩ := hp
    have hq : (q : Points (S.term n).val.X R) = 1 := by
      apply (cancel_mono S.bottom.hom.hom.hom).mp
      exact (isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _
    rw [hq, map_one]
    exact Subgroup.one_mem _
  exact ⟨n, le_bot_iff.mp ((hd n le_rfl).trans hbot)⟩

private theorem geometric_unipotent_isSolvable [IsAlgClosed K] (G : AffineAlgebraicGroup K)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (hu : Specs.Unipotent.IsUnipotent G) : Specs.SchemeDerivedGroup.IsSolvable G.val := by
  let i : rationalSections G.val ≃* Points G.val.X (CommAlgCat.of K K) :=
    ((yonedaGrp.obj G.val).mapIso (baseIso (k := K)).op).groupIsoToMulEquiv
  let : Group.IsSolvable (Points G.val.X (CommAlgCat.of K K)) :=
    unipotent_test_points_solvable G hu _
  exact (solvable_iff_sections G hs hc).mpr (Group.isSolvable_of_isSolvable_injective (f := i.toMonoidHom) i.injective)

end GeometricUnipotentSolvability

section RegularSplitActions

open Opposite _root_.LinearAlgebraicGroups.Specs
open CategoryTheory.MonoidalCategory
open PeirceSpecification (ZornIsomorphism)
open private sections baseIso Regular valueAt from LinearAlgebraicGroups.Solvable.LieKolchin

variable {K : Type u} [Field K] {C : Type v} [NonAssocRing C] [Module K C]
  [IsScalarTower K C C] [SMulCommClass K C C] {n : QuadraticForm K C}

private def fieldPointsOfSections (G : GroupScheme K) :
    sections G ≃* ringPoint G.X (CommAlgCat.of K K) where
  toFun p := (baseIso (k := K)).hom ≫ p
  invFun p := (baseIso (k := K)).inv ≫ p
  left_inv p := Iso.inv_hom_id_assoc (baseIso (k := K)) p
  right_inv p := Iso.hom_inv_id_assoc (baseIso (k := K)) p
  map_mul' p q := MonObj.comp_mul (baseIso (k := K)).hom p q

private def splitSectionGroupEquiv (F : ZornIsomorphism n) (A : AutomorphismGroup K C) :
    sections A.group ≃* ZornPointGroup K :=
  (fieldPointsOfSections A.group).trans (splitPointGroupEquiv F A)

set_option maxHeartbeats 100000 in
private theorem splitSectionCoefficient_regular (F : ZornIsomorphism n) (A : AutomorphismGroup K C)
    (x : Zorn K) (ℓ : Zorn K →ₗ[K] K) :
    ∃ a : Γ(A.group.X.left, ⊤), ∀ p : sections A.group,
      valueAt p a = ℓ ((splitSectionGroupEquiv F A p).val.val x) := by
  obtain ⟨B, ⟨i⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr A.groupAffine
  let j : affineScheme K B.unop ≅ A.group.X := i
  obtain ⟨a, ha⟩ := splitOrbitCoordinate_regular F A j x ℓ
  let e : Spec (CommRingCat.of B.unop) ≅ A.group.X.left :=
    (Over.forget (Spec (CommRingCat.of K))).mapIso j
  let g := (Scheme.ΓSpecIso (CommRingCat.of B.unop)).inv
  refine ⟨e.inv.appTop (g a), fun p => ?_⟩
  let q := (baseIso (k := K)).hom ≫ p
  let d := (affinePointEquiv j (CommAlgCat.of K K)).symm q
  have hq : affinePointEquiv j (CommAlgCat.of K K) d = q :=
    (affinePointEquiv j (CommAlgCat.of K K)).apply_symm_apply _
  have hpLeft : p.left = (Scheme.Spec.map (CommRingCat.ofHom d.toRingHom).op) ≫ e.hom := by
    have hp := congrArg Over.Hom.left hq
    change Scheme.Spec.map (CommRingCat.ofHom d.toRingHom).op ≫ e.hom = 𝟙 _ ≫ p.left at hp
    rw [Category.id_comp] at hp
    exact hp.symm
  have hval : valueAt p (e.inv.appTop (g a)) = d a := by
    let j' := CommRingCat.ofHom d.toRingHom
    let f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B.unop) := Scheme.Spec.map j'.op
    let v : Spec (CommRingCat.of K) ⟶ A.group.X.left := p.left
    have hleft : v = f ≫ e.hom := hpLeft
    have hcomp : v ≫ e.inv = f := by rw [hleft, Category.assoc, e.hom_inv_id, Category.comp_id]
    have hf : e.inv.appTop ≫ v.appTop = f.appTop :=
      (Scheme.Hom.comp_appTop v e.inv).symm.trans (congrArg Scheme.Hom.appTop hcomp)
    have hj : f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
        (Scheme.ΓSpecIso (CommRingCat.of B.unop)).hom ≫ j' :=
      Scheme.ΓSpecIso_naturality j'
    have hh : (g ≫ e.inv.appTop ≫ v.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom) = j' := by
      rw [← Category.assoc e.inv.appTop, hf, hj, Iso.inv_hom_id_assoc]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hh) a
  exact hval.trans ((ha d).trans
    (congrArg (fun r : ringPoint A.group.X (CommAlgCat.of K K) =>
      ℓ ((splitPointGroupEquiv F A r).val.val x)) hq))

set_option backward.isDefEq.respectTransparency false in
private theorem splitTrace_regular (F : ZornIsomorphism n) (A : AutomorphismGroup K C) :
    Regular (traceActionHom.comp (splitSectionGroupEquiv F A).toMonoidHom) := by
  intro x ℓ
  let s := (traceZero K).subtype
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective s
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  obtain ⟨a, ha⟩ := splitSectionCoefficient_regular F A x.val (ℓ.comp r)
  refine ⟨a, fun p => ?_⟩
  rw [ha]
  change ℓ (r (s (traceAction (splitSectionGroupEquiv F A p) x))) =
    ℓ (traceAction (splitSectionGroupEquiv F A p) x)
  exact congrArg ℓ (LinearMap.congr_fun hr _)

set_option backward.isDefEq.respectTransparency false in
private theorem splitTraceQuotient_regular (F : ZornIsomorphism n) (A : AutomorphismGroup K C) :
    Regular (quotientActionHom.comp (splitSectionGroupEquiv F A).toMonoidHom) := by
  intro x ℓ
  let q := (scalarTraceLine K).mkQ
  obtain ⟨x, rfl⟩ := (scalarTraceLine K).mkQ_surjective x
  obtain ⟨a, ha⟩ := splitTrace_regular F A x (ℓ.comp q)
  refine ⟨a, fun p => ?_⟩
  exact ha p

end RegularSplitActions

section DiagonalWeightCoordinates

open _root_.LinearAlgebraicGroups.Specs
open CharacterDescent (Character)
open CharacterPairing (characterValue)
open WithConv
open private zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

variable {K : Type u} [Field K]

private theorem frameTorusCharacters_detect {m n : FrameCharacters.{u}}
    (h : ∀ (S : TestAlgebra K) (t : framePoint S), frameTorusCharacters S t m =
      frameTorusCharacters S t n) : m = n := by
  let S := CommAlgCat.of K (FrameRing (R := K))
  let t : framePoint S := framePointConvolution S (WithConv.toConv (AlgHom.id K S))
  have ht : framePointAlgebraHom S t = AlgHom.id K S :=
    congrArg WithConv.ofConv ((framePointConvolution S).symm_apply_apply _)
  have he := congrArg Units.val (h S t)
  rw [frameTorusCharacters_eval, frameTorusCharacters_eval, ht] at he
  by_contra hn
  have hc := congrArg (fun a : FrameRing (R := K) => a.coeff m) he
  change (MonoidAlgebra.single m (1 : K) : FrameRing (R := K)).coeff m =
    (MonoidAlgebra.single n (1 : K) : FrameRing (R := K)).coeff m at hc
  simp [MonoidAlgebra.coeff_single, Ne.symm hn] at hc

set_option backward.isDefEq.respectTransparency false in
private theorem frameCharacterAlongIso_eval {G : GroupScheme K} {T : ClosedSubgroup G}
    (e : T.group ≅ frameTorus K) (m : FrameCharacters.{u})
    (S : TestAlgebra K) (t : Points T.group.X S) :
    characterValue (charactersAlongIso e (frameCharacterEquiv (K := K) m)) S t =
      (frameTorusCharacters S (t ≫ e.hom.hom.hom) m).val := by
  rw [frameTorusCharacters_eval, ← frameCharacterEquiv_monomial_eval]
  unfold characterValue
  have he : (charactersAlongIso e (frameCharacterEquiv (K := K) m)).hom.hom =
      e.hom.hom.hom ≫ (frameCharacterEquiv (K := K) m).hom.hom := rfl
  rw [he, Category.assoc]

private theorem frameUnits_eq_character (S : TestAlgebra K) (t : framePoint S) (i : Fin 3) :
    frameUnits S t i = frameTorusCharacters S t (frameExponent i) := rfl

private theorem pairedFunctions_diagonal (S : TestAlgebra K) (t : framePoint S)
    (x : Zorn S) (i : ZornCoordinateIndex) :
    Zorn.pairedFunctions S (diagonalLinearEquiv (frameUnits S t) x) i =
      (frameTorusCharacters S t (zornCoordinateWeight i)).val * Zorn.pairedFunctions S x i := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective x
  rcases i with (i | i) <;> cases i
  · change a = (frameTorusCharacters S t 1).val * a
    simp
  · rename_i i
    change (frameUnits S t i).val * u i =
      (frameTorusCharacters S t (frameExponent i)).val * u i
    rw [frameUnits_eq_character]
  · change b = (frameTorusCharacters S t 1).val * b
    simp
  · rename_i i
    change -(((frameUnits S t i)⁻¹ : Sˣ).val * v i) =
      (frameTorusCharacters S t ((frameExponent i)⁻¹)).val * -v i
    rw [frameUnits_eq_character, map_inv, mul_neg]

private theorem diagonal_zornBasis (S : TestAlgebra K) (t : framePoint S)
    (i : ZornCoordinateIndex) :
    diagonalLinearEquiv (frameUnits S t) (zornBasis S i) =
      (frameTorusCharacters S t (zornCoordinateWeight i)).val • zornBasis S i := by
  apply (Zorn.pairedFunctions S).injective
  funext j
  rw [pairedFunctions_diagonal, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, zornBasis, Module.Basis.map_apply,
    LinearEquiv.apply_symm_apply, Pi.basisFun_apply, Pi.single_apply]
  split_ifs with hij
  · subst j
    rfl
  · simp

end DiagonalWeightCoordinates

section TangentCoefficientComparison

open Opposite _root_.LinearAlgebraicGroups.Specs
open AdjointRepresentation (constants dualMap scale)
open PeirceSpecification (ZornIsomorphism)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (infinitesimal schemePoints)
open private zornBasis map_zornBasis pairedFunctions_mapCoordinates
  from LinearAlgebraicGroups.Composition.PeirceFrames

variable {K : Type u} [Field K] {C : Type v} [NonAssocRing C] [Module K C]
  [IsScalarTower K C C] [SMulCommClass K C C] {n : QuadraticForm K C}

private theorem dualMap_eps (S : TestAlgebra K) :
    (dualMap (CommAlgCat.ofHom (Algebra.ofId K S))).hom (DualNumber.eps : DualNumber K) =
      (DualNumber.eps : DualNumber S) := by
  apply TrivSqZeroExt.ext
  · change algebraMap K S 0 = 0
    exact map_zero _
  · change algebraMap K S 1 = 1
    exact map_one _

private theorem scale_eps (S : TestAlgebra K) (a : S) :
    (scale S a).hom (DualNumber.eps : DualNumber S) = (TrivSqZeroExt.inr a : DualNumber S) := by
  apply TrivSqZeroExt.ext
  · rfl
  · change a * 1 = a
    exact mul_one a

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 440000 in
set_option maxRecDepth 2048 in
/-- The coefficients of a tangent endomorphism are compared with the diagonal
action using the square-zero part of an actual group point. -/
private theorem splitTangent_conjugation_iff (F : ZornIsomorphism n) (A : AutomorphismGroup K C)
    (p : Points A.group.X (CommAlgCat.of K (DualNumber K))) (D : Module.End K C)
    (hp : (A.subgroupPoints (CommAlgCat.of K (DualNumber K)) p).val.val = infinitesimal D)
    (S : TestAlgebra K) (t : framePoint S) (a : S) :
    let q := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId K S))) p
    let g := mapPoints (constants S) (framePointMap F A S t)
    g * q * g⁻¹ = mapPoints (scale S a) q ↔
      ∀ i j : ZornCoordinateIndex,
        let c := algebraMap K S (Zorn.pairedFunctions K
          (splitDerivationEndEquiv F D (zornBasis K j)) i)
        (frameTorusCharacters S t (zornCoordinateWeight i)).val * c =
          a * (frameTorusCharacters S t (zornCoordinateWeight j)).val * c := by
  let U := CommAlgCat.of K (DualNumber S)
  let f := dualMap (CommAlgCat.ofHom (Algebra.ofId K S))
  let q := mapPoints f p
  let q' := mapPoints (scale S a) q
  let g := mapPoints (constants S) (framePointMap F A S t)
  let t' : framePoint U := mapPoints (constants S) t
  let E := splitSchemePoints F A U
  let d := diagonalLinearEquiv (frameUnits U t')
  let w (i : ZornCoordinateIndex) := (frameTorusCharacters S t (zornCoordinateWeight i)).val
  let W (i : ZornCoordinateIndex) := (frameTorusCharacters U t' (zornCoordinateWeight i)).val
  let b (j : ZornCoordinateIndex) := zornBasis U j
  let y (j : ZornCoordinateIndex) := zornScalarMap U (splitDerivationEndEquiv F D (zornBasis K j))
  let c (i j : ZornCoordinateIndex) :=
    algebraMap K S (Zorn.pairedFunctions K (splitDerivationEndEquiv F D (zornBasis K j)) i)
  let L := Zorn.pairedFunctions U
  have hcoord (i j : ZornCoordinateIndex) : L (y j) i = (c i j, 0) := by
    rw [show L (y j) i = Zorn.pairedFunctions U
      (zornScalarMap U (splitDerivationEndEquiv F D (zornBasis K j))) i from rfl,
      pairedFunctions_mapCoordinates]
    rfl
  have hW (i : ZornCoordinateIndex) : W i = (w i, 0) := by
    exact congrArg Units.val (frameTorusCharacters_natural (constants S) t (zornCoordinateWeight i))
  have hq (j : ZornCoordinateIndex) : (E q).val (b j) = b j + (DualNumber.eps : DualNumber S) • y j := by
    have h := splitSchemePoints_map_infinitesimal F A f p D hp (zornBasis K j)
    rw [show zornScalarMap U (zornBasis K j) = b j from map_zornBasis (algebraMap K U) j,
      show f.hom (DualNumber.eps : DualNumber K) = (DualNumber.eps : DualNumber S) from dualMap_eps S] at h
    exact h
  have hq' (j : ZornCoordinateIndex) : (E q').val (b j) = b j + (TrivSqZeroExt.inr a : DualNumber S) • y j := by
    have hh : q' = mapPoints (f ≫ scale S a) p := by
      change (testSpec K).map (scale S a).op ≫ (testSpec K).map f.op ≫ p = _
      rw [← Category.assoc, ← Functor.map_comp]
      rfl
    rw [hh]
    have h := splitSchemePoints_map_infinitesimal F A (f ≫ scale S a) p D hp (zornBasis K j)
    have hc : (f ≫ scale S a).hom (DualNumber.eps : DualNumber K) = (TrivSqZeroExt.inr a : DualNumber S) := by
      change (scale S a).hom (f.hom (DualNumber.eps : DualNumber K)) = _
      rw [dualMap_eps, scale_eps]
    rw [show zornScalarMap U (zornBasis K j) = b j from map_zornBasis (algebraMap K U) j, hc] at h
    exact h
  have hg : (E g).val = d := by
    have hg' : g = framePointMap F A U t' := (framePointMap_natural F A (constants S) t).symm
    rw [hg']
    exact congrArg Subtype.val ((splitSchemePoints F A U).apply_symm_apply (frameSplitAutomorphism U t'))
  have hb (j : ZornCoordinateIndex) : d (b j) = W j • b j := diagonal_zornBasis U t' j
  have htest : g * q = q' * g ↔
      ∀ j : ZornCoordinateIndex, (E (g * q)).val (b j) = (E (q' * g)).val (b j) := by
    constructor
    · intro h j
      rw [h]
    · intro h
      apply E.injective
      apply Subtype.ext
      apply LinearEquiv.toLinearMap_injective
      exact (zornBasis U).ext h
  have hd (x : Zorn U) (i : ZornCoordinateIndex) : L (d x) i = W i * L x i :=
    pairedFunctions_diagonal U t' x i
  have hsquare (v w c : S) :
      (DualNumber.eps : DualNumber S) * (TrivSqZeroExt.inl v * TrivSqZeroExt.inl c) =
        (TrivSqZeroExt.inl w * TrivSqZeroExt.inr a) * TrivSqZeroExt.inl c ↔ v * c = a * w * c := by
    constructor
    · intro h
      have hs := congrArg TrivSqZeroExt.snd h
      change 0 * (v * 0 + 0 * c) + 1 * (v * c) =
        (w * 0) * 0 + (w * a + 0 * 0) * c at hs
      simpa only [mul_zero, zero_mul, zero_add, add_zero, one_mul, mul_comm w a] using hs
    · intro h
      apply TrivSqZeroExt.ext
      · change 0 * (v * c) = (w * 0) * c
        simp
      · change 0 * (v * 0 + 0 * c) + 1 * (v * c) =
          (w * 0) * 0 + (w * a + 0 * 0) * c
        simpa only [mul_zero, zero_mul, zero_add, add_zero, one_mul, mul_comm w a] using h
  have hentry (j : ZornCoordinateIndex) :
      (E (g * q)).val (b j) = (E (q' * g)).val (b j) ↔
        ∀ i : ZornCoordinateIndex, w i * c i j = a * w j * c i j := by
    rw [splitSchemePoints_mul_action, splitSchemePoints_mul_action, hg, hq, map_add, map_smul, hb,
      map_smul, hq', smul_add, smul_smul, add_right_inj]
    constructor
    · intro h i
      have hh : L ((DualNumber.eps : DualNumber S) • d (y j)) i =
          L ((W j * (TrivSqZeroExt.inr a : DualNumber S)) • y j) i :=
        congrArg (fun x : Zorn U => L x i) h
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, hd, hW, hcoord] at hh
      exact (hsquare (w i) (w j) (c i j)).mp hh
    · intro h
      apply L.injective
      funext i
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, hd, hW, hcoord]
      exact (hsquare (w i) (w j) (c i j)).mpr (h i)
  change g * q * g⁻¹ = q' ↔ _
  rw [mul_inv_eq_iff_eq_mul, htest]
  exact ⟨fun h i j => (hentry j).mp (h j) i, fun h j => (hentry j).mpr fun i => h i j⟩

end TangentCoefficientComparison

section SplitOctonionRadicals

open _root_.LinearAlgebraicGroups.Specs
open PeirceSpecification (ZornIsomorphism)
open Specs.GeometricRadicals (IsSmoothConnectedNormal IsTrivialSubgroup)
open private sections from LinearAlgebraicGroups.Solvable.LieKolchin
open private zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

variable {K : Type u} [Field K] {C : Type v}
  [NonAssocRing C] [Module K C] [IsScalarTower K C C] [SMulCommClass K C C]
  {n : QuadraticForm K C}

private def automorphismAlgebraicGroup (A : AutomorphismGroup K C) : AffineAlgebraicGroup K :=
  ⟨A.group, A.groupAffine, A.groupFiniteType, A.groupQuasiCompact⟩

variable [IsAlgClosed K]

set_option backward.isDefEq.respectTransparency false in
private theorem split_normalSolvable_isTrivial (F : ZornIsomorphism n) (A : AutomorphismGroup K C)
    (N : ClosedSubgroup (automorphismAlgebraicGroup A).val)
    (hN : IsSmoothConnectedNormal (G := automorphismAlgebraicGroup A) N)
    (hsol : Specs.SchemeDerivedGroup.IsSolvable N.group) : IsTrivialSubgroup N := by
  let G := automorphismAlgebraicGroup A
  let e := splitSectionGroupEquiv F A
  have hs : Smooth G.val.X.hom := splitAutomorphismScheme_smooth F A
  have hc : ConnectedSpace G.val.X.left := splitAutomorphismScheme_connected F A
  let : FiniteDimensional K (Zorn K) := Module.Finite.of_basis (zornBasis K)
  by_cases h2 : (2 : K) = 0
  · let π := quotientActionHom.comp e.toMonoidHom
    let h := quotient_irreducible h2
    let : Nontrivial (traceZeroQuotient K) := h.1
    refine normalSolvable_isTrivial_of_regularAction G hs hc π (splitTraceQuotient_regular F A)
      (fun U hu => h.2 U ?_) (fun g ⟨c, hgc⟩ => ?_) N hN hsol
    · intro g x hx
      have hp := hu (e.symm g) x hx
      change quotientAction (e (e.symm g)) x ∈ U at hp
      rw [e.apply_symm_apply] at hp
      exact hp
    · apply e.injective
      rw [map_one]
      exact point_eq_one_of_scalar_quotient h2 (e g) c (LinearMap.ext hgc)
  · let π := traceActionHom.comp e.toMonoidHom
    let h := trace_irreducible h2
    let : Nontrivial (traceZero K) := h.1
    refine normalSolvable_isTrivial_of_regularAction G hs hc π (splitTrace_regular F A)
      (fun U hu => h.2 U ?_) (fun g ⟨c, hgc⟩ => ?_) N hN hsol
    · intro g x hx
      have hp := hu (e.symm g) x hx
      change traceAction (e (e.symm g)) x ∈ U at hp
      rw [e.apply_symm_apply] at hp
      exact hp
    · apply e.injective
      rw [map_one]
      exact point_eq_one_of_scalar_trace (e g) c (LinearMap.ext hgc)

end SplitOctonionRadicals

section GeometricOctonionRadicals

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals
open scoped TensorProduct

variable {K : Type u} [Field K] {C : Type v} [NonAssocRing C] [Module K C]
  [IsScalarTower K C C] [SMulCommClass K C C] {n : QuadraticForm K C}

set_option backward.isDefEq.respectTransparency false in
private theorem octonionAutomorphismGroup_reductive_semisimple (hn : OctonionNormConditions n)
    (A : AutomorphismGroup K C) :
    IsReductive (automorphismAlgebraicGroup A) ∧ IsSemisimple (automorphismAlgebraicGroup A) := by
  let G := automorphismAlgebraicGroup A
  let E := AlgebraicClosure K
  let B := scalarExtendedAutomorphisms (K := E) A
  obtain ⟨F⟩ := octonion_splits_over_algebraically_closed (octonion_norm_baseChange hn E)
  have hs := octonionAutomorphismScheme_smooth hn A
  have hc := octonionAutomorphismScheme_geometricallyConnected hn A
  let N := geometricUnipotentRadical G
  let S := geometricSolvableRadical G
  have hN := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
  have hS := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  have hsolv := geometric_unipotent_isSolvable (Unipotent.closedSubgroupAlgebraicGroup N)
    hN.1.1 hN.1.2.1 hN.2.1
  exact ⟨⟨hs, hc, split_normalSolvable_isTrivial F B N hN.1 hsolv⟩,
    ⟨hs, hc, split_normalSolvable_isTrivial F B S hS.1 hS.2.1⟩⟩

end GeometricOctonionRadicals

section RootExponentWitnesses

open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (IsDerivation)
open private zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

variable {K : Type u} [Field K]

private theorem rootExponent_ne_one {m : FrameCharacters.{u}} (hm : IsFrameRootExponent m) :
    m ≠ 1 := by
  rcases hm with ⟨i, j, hij, rfl⟩ | ⟨i, h | h⟩
  · fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  · rw [h]
    fin_cases i <;> decide
  · rw [h]
    fin_cases i <;> decide

private theorem pairedFunctions_ofCoordinates (x : ZornCoordinates K) (i : ZornCoordinateIndex) :
    Zorn.pairedFunctions K (Zorn.ofCoordinates x) i =
      match i with
      | .inl none => x.1
      | .inl (some j) => x.2.1 j
      | .inr none => x.2.2.2
      | .inr (some j) => -x.2.2.1 j := by
  rcases i with (i | i) <;> cases i <;> rfl

private theorem upperDerivation_ofCoordinates (p : Fin 3 → K) (x : ZornCoordinates K) :
    upperDerivation p (Zorn.ofCoordinates x) = Zorn.ofCoordinates (upperDerivationSlots p x) :=
  rfl

private theorem lowerDerivation_ofCoordinates (p : Fin 3 → K) (x : ZornCoordinates K) :
    lowerDerivation p (Zorn.ofCoordinates x) = Zorn.ofCoordinates (lowerDerivationSlots p x) :=
  rfl

private theorem elementaryDerivation_ofCoordinates (i j : Fin 3) (x : ZornCoordinates K) :
    elementaryDerivation i j (Zorn.ofCoordinates x) = Zorn.ofCoordinates (elementaryDerivationSlots i j x) :=
  rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 900000 in
private theorem upperDerivation_root_coefficients (k : Fin 3) (i j : ZornCoordinateIndex)
    (h : Zorn.pairedFunctions K (upperDerivation (Pi.single k 1) (zornBasis K j)) i ≠ 0) :
    frameExponent k = zornCoordinateWeight i * (zornCoordinateWeight j)⁻¹ := by
  rw [zornBasis_of_slots] at h
  revert h
  rcases i with (i | i) <;> rcases i with (_ | i) <;>
    rcases j with (j | j) <;> rcases j with (_ | j)
  all_goals fin_cases k
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals first
      | exact fun _ => by decide
      | simp [ZornSpecification.first, ZornSpecification.second, upperDerivation_ofCoordinates,
          pairedFunctions_ofCoordinates, upperDerivationSlots, Pi.single_apply, dotProduct,
          Fin.sum_univ_three, cross_apply, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply,
          smul_eq_mul]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 900000 in
private theorem lowerDerivation_root_coefficients (k : Fin 3) (i j : ZornCoordinateIndex)
    (h : Zorn.pairedFunctions K (lowerDerivation (Pi.single k 1) (zornBasis K j)) i ≠ 0) :
    (frameExponent k)⁻¹ = zornCoordinateWeight i * (zornCoordinateWeight j)⁻¹ := by
  rw [zornBasis_of_slots] at h
  revert h
  rcases i with (i | i) <;> rcases i with (_ | i) <;>
    rcases j with (j | j) <;> rcases j with (_ | j)
  all_goals fin_cases k
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals first
      | exact fun _ => by decide
      | simp [ZornSpecification.first, ZornSpecification.second, lowerDerivation_ofCoordinates,
          pairedFunctions_ofCoordinates, lowerDerivationSlots, Pi.single_apply, dotProduct,
          Fin.sum_univ_three, cross_apply, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply,
          smul_eq_mul]

private theorem elementaryDerivation_root_coefficients (k l : Fin 3) (i j : ZornCoordinateIndex)
    (h : Zorn.pairedFunctions K (elementaryDerivation k l (zornBasis K j)) i ≠ 0) :
    frameExponent k * (frameExponent l)⁻¹ =
      zornCoordinateWeight i * (zornCoordinateWeight j)⁻¹ := by
  rw [zornBasis_of_slots] at h
  rcases i with (i | i) <;> rcases i with (_ | i) <;>
    rcases j with (j | j) <;> rcases j with (_ | j)
  all_goals
    simp [ZornSpecification.first, ZornSpecification.second, elementaryDerivation_ofCoordinates,
      pairedFunctions_ofCoordinates, elementaryDerivationSlots, Pi.single_apply] at h
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · obtain ⟨rfl, rfl⟩ := h
    simp [zornCoordinateWeight, mul_comm]

private theorem rootExponent_has_derivation (m : FrameCharacters.{u}) (hm : IsFrameRootExponent m) :
    ∃ D : Module.End K (Zorn K), IsDerivation (LinearMap.mul K (Zorn K)) D ∧ D ≠ 0 ∧
      ∀ i j : ZornCoordinateIndex, Zorn.pairedFunctions K (D (zornBasis K j)) i ≠ 0 →
        m = zornCoordinateWeight i * (zornCoordinateWeight j)⁻¹ := by
  rcases hm with ⟨i, j, hij, rfl⟩ | ⟨i, rfl | rfl⟩
  · refine ⟨elementaryDerivation i j, elementaryDerivation_rule i j hij, ?_,
      elementaryDerivation_root_coefficients i j⟩
    intro h
    have hh := DFunLike.congr_fun h (Zorn.ofCoordinates (0, Pi.single j 1, 0, 0))
    rw [elementaryDerivation_ofCoordinates] at hh
    have h0 := congrArg (fun x : Zorn K => Zorn.pairedFunctions K x (.inl (some i))) hh
    simp [pairedFunctions_ofCoordinates, elementaryDerivationSlots] at h0
  · refine ⟨upperDerivation (Pi.single i 1), upperDerivation_rule _, ?_,
      upperDerivation_root_coefficients i⟩
    intro h
    have hh := DFunLike.congr_fun h (Zorn.first K)
    rw [upperDerivation_first] at hh
    have h0 := congrArg (fun x : Zorn K => Zorn.pairedFunctions K x (.inl (some i))) hh
    simp [pairedFunctions_ofCoordinates] at h0
  · refine ⟨lowerDerivation (Pi.single i 1), lowerDerivation_rule _, ?_,
      lowerDerivation_root_coefficients i⟩
    intro h
    have hh := DFunLike.congr_fun h (Zorn.first K)
    rw [lowerDerivation_first] at hh
    have h0 := congrArg (fun x : Zorn K => Zorn.pairedFunctions K x (.inr (some i))) hh
    simp [pairedFunctions_ofCoordinates] at h0

end RootExponentWitnesses

section SchemeRootIdentification

open _root_.LinearAlgebraicGroups.Specs
open CharacterDescent (Character)
open CharacterPairing (adjointWeightVectors absoluteRoots characterValue)
open AdjointRepresentation (GroupPoints)
open PeirceSpecification (ZornIsomorphism)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (infinitesimal)
open private zornBasis from LinearAlgebraicGroups.Composition.PeirceFrames

variable {K : Type u} [Field K] {C : Type v} [NonAssocRing C] [Module K C]
  [IsScalarTower K C C] [SMulCommClass K C C] {n : QuadraticForm K C}

set_option maxRecDepth 1500 in
set_option backward.isDefEq.respectTransparency false in
private theorem frameAdjointWeight_iff (F : ZornIsomorphism n) (A : AutomorphismGroup K C)
    (T : ClosedSubgroup A.group) (e : T.group ≅ frameTorus K)
    (hframe : IsFrameTorus F A (e.inv ≫ T.inclusion))
    (p : Lie K A.group) (D : Module.End K C)
    (hp : (A.subgroupPoints (CommAlgCat.of K (DualNumber K)) p.toMul.val).val.val = infinitesimal D)
    (m : FrameCharacters.{u}) :
    p ∈ adjointWeightVectors T (charactersAlongIso e (frameCharacterEquiv (K := K) m)) ↔
      ∀ i j : ZornCoordinateIndex,
        Zorn.pairedFunctions K (splitDerivationEndEquiv F D (zornBasis K j)) i ≠ 0 →
          m = zornCoordinateWeight i * (zornCoordinateWeight j)⁻¹ := by
  let χ := charactersAlongIso e (frameCharacterEquiv (K := K) m)
  let w := zornCoordinateWeight
  let c (i j : ZornCoordinateIndex) :=
    Zorn.pairedFunctions K (splitDerivationEndEquiv F D (zornBasis K j)) i
  have hl (S : TestAlgebra K) (t : GroupPoints T.group S) :
      t ≫ T.inclusion.hom.hom = framePointMap F A S (t ≫ e.hom.hom.hom) := by
    rw [← framePointMap_eq_of_frame_action F A _ hframe]
    change t ≫ T.inclusion.hom.hom =
      (t ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ≫ T.inclusion.hom.hom
    rw [Category.assoc, ← Category.assoc e.hom.hom.hom]
    have h := congrArg (fun a : T.group ⟶ T.group => a.hom.hom) e.hom_inv_id
    change e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ at h
    rw [h, Category.id_comp]
  have hr (S : TestAlgebra K) (t : GroupPoints T.group S) :
      characterValue χ S t = (frameTorusCharacters S (t ≫ e.hom.hom.hom) m).val :=
    frameCharacterAlongIso_eval e m S t
  have hequiv :
      p ∈ adjointWeightVectors T χ ↔
        ∀ (S : TestAlgebra K) (q : framePoint S) i j,
          (frameTorusCharacters S q (w i)).val * algebraMap K S (c i j) =
            (frameTorusCharacters S q m).val * (frameTorusCharacters S q (w j)).val *
              algebraMap K S (c i j) := by
    constructor
    · intro h S q
      let t : GroupPoints T.group S := q ≫ e.inv.hom.hom
      have ht : t ≫ e.hom.hom.hom = q := by
        change (q ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = q
        rw [Category.assoc]
        have h := congrArg (fun a : frameTorus K ⟶ frameTorus K => a.hom.hom) e.inv_hom_id
        exact (congrArg (q ≫ ·) h).trans (Category.comp_id _)
      have hh := h S t
      rw [hl S t, hr S t, ht] at hh
      exact (splitTangent_conjugation_iff F A p.toMul.val D hp S q _).mp hh
    · intro h S t
      rw [hl S t, hr S t]
      exact (splitTangent_conjugation_iff F A p.toMul.val D hp S (t ≫ e.hom.hom.hom) _).mpr (h S _)
  rw [hequiv]
  constructor
  · intro h i j hne
    have hm : w i = m * w j := by
      apply frameTorusCharacters_detect (K := K)
      intro S t
      rw [map_mul]
      apply Units.ext
      have hunit : IsUnit (algebraMap K S (c i j)) :=
        (isUnit_iff_ne_zero.mpr hne).map (algebraMap K S)
      obtain ⟨u, hu⟩ := hunit
      have hh := h S t i j
      rw [← hu] at hh
      simpa only [Units.val_mul, mul_assoc, Units.mul_inv, mul_one] using
        congrArg (fun x : S => x * (u⁻¹ : Sˣ).val) hh
    change m = w i * (w j)⁻¹
    rw [hm, mul_assoc, mul_inv_cancel, mul_one]
  · intro h S t i j
    by_cases hz : c i j = 0
    · simp [hz]
    · have hm : m * w j = w i := by
        rw [h i j hz, mul_assoc, inv_mul_cancel, mul_one]
      rw [← Units.val_mul, ← map_mul, hm]

set_option maxRecDepth 1600 in
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
private theorem splitFrame_absoluteRoots (F : ZornIsomorphism n) (A : AutomorphismGroup K C)
    (T : ClosedSubgroup A.group) (e : T.group ≅ frameTorus K)
    (hframe : IsFrameTorus F A (e.inv ≫ T.inclusion)) :
    let ε := rootFrameCharacters e
    absoluteRoots T =
      {χ | (∃ i j : Fin 3, i ≠ j ∧ χ = ε i * (ε j)⁻¹) ∨
        (∃ i : Fin 3, χ = ε i ∨ χ = (ε i)⁻¹)} := by
  obtain ⟨d, hd, hrange, heval, hadd, _, _⟩ :=
    LinearAlgebraicGroups.Albert.Automorphisms.bilinearLieIdentification (octonionAlgebra (R := K) (C := C)) A
  have hzero : d 0 = 0 := by
    have h := hadd 0 0
    rw [zero_add] at h
    exact add_left_cancel (show d 0 + d 0 = d 0 + 0 by rw [← h, add_zero])
  let E := (frameCharacterEquiv (K := K)).trans (charactersAlongIso e)
  ext χ
  obtain ⟨m, rfl⟩ := E.surjective χ
  change (E m ≠ 1 ∧ ∃ p ∈ adjointWeightVectors T (E m), p ≠ 0) ↔
    (∃ i j : Fin 3, i ≠ j ∧ E m = E (frameExponent i) * (E (frameExponent j))⁻¹) ∨
      (∃ i : Fin 3, E m = E (frameExponent i) ∨ E m = (E (frameExponent i))⁻¹)
  simp only [← E.map_one, ← map_inv, ← map_mul, ne_eq, E.injective.eq_iff]
  change (m ≠ 1 ∧ ∃ p ∈ adjointWeightVectors T (E m), p ≠ 0) ↔ IsFrameRootExponent m
  constructor
  · rintro ⟨hm, p, hweight, hp⟩
    have hD := (splitDerivationEndEquiv_iff F (d p)).mpr ((hrange (d p)).mp ⟨p, rfl⟩)
    have hne : splitDerivationEndEquiv F (d p) ≠ 0 := by
      intro h
      apply hp
      apply hd
      rw [hzero]
      exact (splitDerivationEndEquiv F).injective
        (h.trans ((splitDerivationEndEquiv F).map_zero).symm)
    exact derivation_weight_is_root hm hD hne
      ((frameAdjointWeight_iff F A T e hframe p (d p) (heval p) m).mp hweight)
  · intro hm
    obtain ⟨D, hD, hne, hcoeff⟩ := rootExponent_has_derivation (K := K) m hm
    let D' := (splitDerivationEndEquiv F).symm D
    have heq : splitDerivationEndEquiv F D' = D := (splitDerivationEndEquiv F).apply_symm_apply D
    obtain ⟨p, hp⟩ := (hrange D').mpr ((splitDerivationEndEquiv_iff F D').mp (heq.symm ▸ hD))
    have hh := (frameAdjointWeight_iff F A T e hframe p (d p) (heval p) m).mpr
      (by simpa only [hp, heq] using hcoeff)
    refine ⟨rootExponent_ne_one hm, p, hh, fun h => ?_⟩
    apply hne
    rw [← heq, ← hp, h, hzero, map_zero]

end SchemeRootIdentification

section OctonionGroupConclusions

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsSplitTorus IsMaximalTorus baseChangedSubgroup)
open RankOneFlag (IsGeometricallyMaximal)
open CharacterPairing (characterValue)
open SchemeCentre (CentreFormula)
open PeirceSpecification (ZornIsomorphism)
open scoped TensorProduct

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 360000 in
private theorem frameTorus_geometricallyMaximal {K : Type u} [Field K] {D : Type v}
    [NonAssocRing D] [Module K D] [IsScalarTower K D D] [SMulCommClass K D D]
    {q : QuadraticForm K D} (F : ZornIsomorphism q) (A : AutomorphismGroup K D)
    (i : frameTorus K ⟶ A.group) (hi : IsFrameTorus F A i)
    (hc : IsClosedImmersion i.hom.hom.left) :
    IsGeometricallyMaximal (⟨frameTorus K, i, hc⟩ : ClosedSubgroup A.group) := by
  let T : ClosedSubgroup A.group := ⟨frameTorus K, i, hc⟩
  let E := AlgebraicClosure K
  let B := scalarExtendedAutomorphisms (K := E) A
  let : IsClosedImmersion i.hom.hom.left := hc
  let h := scalarExtension_isClosedImmersion (K := E) i.hom.hom
  refine ⟨h, ?_⟩
  let U := baseChangedSubgroup E T h
  obtain ⟨e, he⟩ := frameTorusBaseChange (R := K) (K := E)
  let j : frameTorus E ⟶ B.group := e.inv ≫ U.inclusion
  let F' := zornIsomorphismBaseChange F E
  have hj : IsFrameTorus F' B j := isFrameTorus_scalarExtension F A i hi e he
  have hcj : IsClosedImmersion j.hom.hom.left := by
    let FF := Grp.forget (RingScheme E) ⋙ Over.forget _
    have : IsIso e.inv.hom.hom.left := by
      change IsIso (FF.map e.inv)
      infer_instance
    let : IsClosedImmersion U.inclusion.hom.hom.left := h
    change IsClosedImmersion (e.inv.hom.hom.left ≫ U.inclusion.hom.hom.left)
    infer_instance
  exact frameMaximality_of_iso U j hcj e rfl
    (frameTorus_maximal_over_algClosed F' B j hcj (framePointMap_eq_of_frame_action F' B j hj))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 750000 in
private theorem splitFrameTorus_of_automorphismScheme (A : AutomorphismGroup R C)
    [Module.Projective R C] : HasSplitFrameTorus (n := n) A := by
  intro F
  obtain ⟨i, hc, hi⟩ := exists_closedFrameTorus F A
  refine ⟨i, hc, hi, ?_⟩
  intro K _ _
  let B := scalarExtendedAutomorphisms (K := K) A
  let F' := zornIsomorphismBaseChange F K
  let : IsClosedImmersion i.hom.hom.left := hc
  let h := scalarExtension_isClosedImmersion (K := K) i.hom.hom
  let T : ClosedSubgroup B.group := ⟨(scalarExtensionGroup K).obj (frameTorus R),
    (scalarExtensionGroup K).map i, h⟩
  obtain ⟨e, he⟩ := frameTorusBaseChange (R := R) (K := K)
  let eT : T.group ≅ frameTorus K := e
  have hF : IsFrameTorus F' B (eT.inv ≫ T.inclusion) :=
    isFrameTorus_scalarExtension F A i hi e he
  have hr : HasG2Roots T (rootFrameCharacters eT) :=
    hasG2Roots_of_tangent_weights (T := T) eT (splitFrame_absoluteRoots F' B T eT hF)
  have hT : IsGeometricallyMaximal T := scalarExtendedFrameTorus_geometricallyMaximal F A i hi h
  have hS : IsSplitTorus T.group := scalarExtendedFrameTorus_isSplit (R := R) (K := K)
  refine ⟨h, hS, hT, rootFrameCharacters eT, hr, ?_⟩
  intro S t j
  exact (rootFrameCharacters_eval eT S t j).trans (he S t j)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 410000 in
private theorem geometricFibers_of_automorphismScheme
    (centre : CentreFormula.{u}) (hn : OctonionNormConditions n) (A : AutomorphismGroup R C) :
    HasGeometricFibers A := by
  intro K _ _ _
  let : Module.Projective R C := hn.projective
  let B := scalarExtendedAutomorphisms (K := K) A
  let G := automorphismAlgebraicGroup B
  have hK := octonion_norm_baseChange hn K
  obtain ⟨F⟩ := octonion_splits_over_algebraically_closed hK
  obtain ⟨hR, hS⟩ := octonionAutomorphismGroup_reductive_semisimple hK B
  obtain ⟨i, hc, hi⟩ := exists_closedFrameTorus F B
  let T : ClosedSubgroup G.val := ⟨frameTorus K, i, hc⟩
  have hm : IsGeometricallyMaximal T := frameTorus_geometricallyMaximal F B i hi hc
  have hsplit : IsSplitTorus T.group := frameTorus_isSplit (K := K)
  let e : T.group ≅ frameTorus K := Iso.refl _
  have hF : IsFrameTorus F B (e.inv ≫ T.inclusion) := by simpa [e, T] using hi
  have hroots := hasG2Roots_of_tangent_weights e (splitFrame_absoluteRoots F B T e hF)
  exact ⟨G.property, hR, hS, trivial_centre_of_root_lattice centre hR T hsplit hm hroots.2.2.2,
    T, rootFrameCharacters e, hsplit, hm, hroots⟩

end OctonionGroupConclusions

/-- The octonion automorphism scheme, conditional on the stated scheme centre formula. -/
theorem octonionAutomorphisms_conditional
    (centre : _root_.LinearAlgebraicGroups.Specs.SchemeCentre.CentreFormula.{u}) :
    OctonionAutomorphisms.{u, v} := by
  intro R _ C _ _ _ _ n hn
  let : Module.Projective R C := hn.projective
  obtain ⟨A, hs, hc⟩ := exists_smooth_connected_automorphismScheme hn
  exact ⟨A, hs, hc, geometricFibers_of_automorphismScheme centre hn A, splitFrameTorus_of_automorphismScheme A⟩

/-- The field formulation of the conditional octonion automorphism theorem. -/
theorem octonionAutomorphismsOverField_conditional
    (centre : _root_.LinearAlgebraicGroups.Specs.SchemeCentre.CentreFormula.{u}) :
    OctonionAutomorphismsOverField.{u, v} :=
  octonionAutomorphismsOverField_of_ring (octonionAutomorphisms_conditional centre)

end

end LinearAlgebraicGroups.Composition.OctonionAutomorphisms

universe v8_closure_07085b37b5026227_u0 v8_closure_07085b37b5026227_u1
theorem _root_.«LinearAlgebraicGroups».«Composition».«OctonionAutomorphisms».«octonionAutomorphisms» : _root_.«LinearAlgebraicGroups».«Composition».«OctonionAutomorphismSpecification».«OctonionAutomorphisms».{v8_closure_07085b37b5026227_u0, v8_closure_07085b37b5026227_u1} :=
  @_root_.«LinearAlgebraicGroups».«Composition».«OctonionAutomorphisms».«octonionAutomorphisms_conditional».{v8_closure_07085b37b5026227_u0, v8_closure_07085b37b5026227_u1} (@_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre».{v8_closure_07085b37b5026227_u0})
theorem _root_.«LinearAlgebraicGroups».«Composition».«OctonionAutomorphisms».«octonionAutomorphismsOverField» : _root_.«LinearAlgebraicGroups».«Composition».«OctonionAutomorphismSpecification».«OctonionAutomorphismsOverField».{v8_closure_07085b37b5026227_u0, v8_closure_07085b37b5026227_u1} :=
  @_root_.«LinearAlgebraicGroups».«Composition».«OctonionAutomorphisms».«octonionAutomorphismsOverField_conditional».{v8_closure_07085b37b5026227_u0, v8_closure_07085b37b5026227_u1} (@_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre».{v8_closure_07085b37b5026227_u0})
theorem _root_.«LinearAlgebraicGroups».«Composition».«OctonionAutomorphisms».«splitGeometricRepresentation» : _root_.«LinearAlgebraicGroups».«Composition».«OctonionAutomorphismSpecification».«SplitGeometricRepresentation».{v8_closure_07085b37b5026227_u0} :=
  @_root_.«LinearAlgebraicGroups».«Composition».«OctonionAutomorphisms».«splitGeometricRepresentation_conditional».{v8_closure_07085b37b5026227_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre».{v8_closure_07085b37b5026227_u0})
