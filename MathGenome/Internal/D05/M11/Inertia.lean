import MathGenome.Internal.Specs.D05.M11.Inertia
import MathGenome.Internal.D05.M11.Inertia.MaximalPositive
import MathGenome.Internal.D05.M11.Nondegenerate
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring

/-! Real Sylvester inertia, including the radical block and dimension zero. -/
noncomputable section
namespace D05.M11.Inertia
open Module
open scoped BigOperators
open Specs.D05.M11.Inertia
open Specs.D05.M11.Inertia.MaximalPositive (Coordinates normalMatrix normalBasis blockBasis)

/-- Partition a finite signed family, retaining every indexed occurrence. -/
private theorem group_weights {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) :
    ∃ p q r : ℕ, ∃ a : (Fin p ⊕ Fin q ⊕ Fin r) ≃ I,
      ∀ k, w (a k) = Sum.elim (fun _ => 1) (Sum.elim (fun _ => -1) (fun _ => 0)) k := by
  classical
  let P := {i : I // w i = 1}
  let O := {i : I // ¬ w i = 1}
  let N := {i : O // w i.val = -1}
  let Z := {i : O // ¬ w i.val = -1}
  let a : (P ⊕ N ⊕ Z) ≃ I :=
    ((Equiv.refl P).sumCongr (Equiv.sumCompl (fun i : O => w i.val = -1))).trans
      (Equiv.sumCompl (fun i : I => w i = 1))
  let t := (Fintype.equivFin P).symm.sumCongr
    ((Fintype.equivFin N).symm.sumCongr (Fintype.equivFin Z).symm)
  refine ⟨Fintype.card P, Fintype.card N, Fintype.card Z, t.trans a, ?_⟩
  rintro (k | (k | k))
  · exact ((Fintype.equivFin P).symm k).property
  · exact ((Fintype.equivFin N).symm k).property
  · let z := (Fintype.equivFin Z).symm k
    change w z.val.val = 0
    exact ((hw z.val.val).resolve_left z.property).resolve_right z.val.property

/-- Flattening and splitting the ordered three blocks are inverse linear maps. -/
private def splitBlocks (p q r : ℕ) :
    ((Fin p ⊕ Fin q ⊕ Fin r) → ℝ) ≃ₗ[ℝ] Coordinates ℝ p q r :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q ⊕ Fin r) ℝ ℝ).trans
    ((LinearEquiv.refl ℝ (Fin p → ℝ)).prodCongr
      (LinearEquiv.sumArrowLequivProdArrow (Fin q) (Fin r) ℝ ℝ))

/-- A quadratic isometry determines the full symmetric bilinear pairing over ℝ. -/
private theorem pairing_of_quadratic_isometry {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (w : I → ℝ)
    (f : B.toQuadraticMap.IsometryEquiv (QuadraticMap.weightedSumSquares ℝ w))
    (x y : V) : B x y = ∑ i, w i * f x i * f y i := by
  have heq : (QuadraticMap.weightedSumSquares ℝ w).comp f.toLinearEquiv.toLinearMap =
      B.toQuadraticMap := by
    ext z
    exact f.map_app z
  have hb := congrArg (QuadraticMap.associatedHom ℝ) heq
  rw [QuadraticMap.associated_comp, QuadraticMap.associated_left_inverse ℝ hB.eq] at hb
  have hxy := congrArg (fun D : LinearMap.BilinForm ℝ V => D x y) hb
  change (QuadraticMap.associatedHom ℝ (QuadraticMap.weightedSumSquares ℝ w))
    (f x) (f y) = B x y at hxy
  rw [← hxy]
  simp only [QuadraticMap.associated_apply, QuadraticMap.weightedSumSquares_apply,
    Pi.add_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, invOf_smul_eq_iff]
  simp only [two_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normal_form_exists : Specs.D05.M11.Inertia.normal_form_exists := by
  intro V _ _ _ B hB
  classical
  obtain ⟨w, hw, ⟨f⟩⟩ :=
    QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared B.toQuadraticMap
  obtain ⟨p, q, r, a, ha⟩ := group_weights w hw
  let e : V ≃ₗ[ℝ] Coordinates ℝ p q r := f.toLinearEquiv.trans
    ((LinearEquiv.piCongrLeft ℝ (fun _ => ℝ) a).symm.trans (splitBlocks p q r))
  refine ⟨p, q, r, e, ?_⟩
  intro x y
  rw [pairing_of_quadratic_isometry B hB w f x y,
    ← a.sum_comp (fun i => w i * f x i * f y i)]
  simp_rw [ha]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul,
    zero_mul, Finset.sum_const_zero, add_zero, neg_mul]
  rw [Finset.sum_neg_distrib]
  rfl

/-- Bridge the original bilinear form to the shared sesquilinear matrix theorem. -/
theorem normal_form_matrix_equiv {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) {p q r : ℕ}
    (e : V ≃ₗ[ℝ] Coordinates ℝ p q r) :
    IsNormalForm B e ↔ HasNormalMatrix B (normalBasis e) := by
  obtain ⟨S, hS, _, _⟩ := MaximalPositive.real_bilinear_bridge B
  have hmat : LinearMap.toMatrix₂ (normalBasis e) (normalBasis e) S =
      LinearMap.toMatrix₂ (normalBasis e) (normalBasis e) B := by
    ext i j
    simp only [LinearMap.toMatrix₂_apply, hS]
  have hm := MaximalPositive.normal_form_matrix S e
  simpa only [Specs.D05.M11.Inertia.MaximalPositive.IsNormalForm, IsNormalForm,
    hS, star_trivial, hmat, HasNormalMatrix] using hm

private theorem normalBasis_coordinates {V : Type*} [AddCommGroup V] [Module ℝ V]
    {p q r : ℕ} (b : Basis (Fin p ⊕ Fin q ⊕ Fin r) ℝ V) :
    normalBasis (b.equivFun.trans (blockBasis ℝ p q r).equivFun.symm) = b := by
  apply Basis.repr_injective
  ext x i
  change (blockBasis ℝ p q r).equivFun
    ((b.equivFun.trans (blockBasis ℝ p q r).equivFun.symm) x) i = b.equivFun x i
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

theorem matrix_iff_coordinates : Specs.D05.M11.Inertia.matrix_iff_coordinates := by
  intro V _ _ B p q r b
  have hm := normal_form_matrix_equiv B
    (b.equivFun.trans (blockBasis ℝ p q r).equivFun.symm)
  rw [normalBasis_coordinates] at hm
  exact hm.symm

theorem matrix_normal_form_exists : Specs.D05.M11.Inertia.matrix_normal_form_exists := by
  intro V _ _ _ B hB
  obtain ⟨p, q, r, e, he⟩ := normal_form_exists B hB
  exact ⟨p, q, r, normalBasis e, (normal_form_matrix_equiv B e).mp he⟩

theorem intrinsic_invariants : Specs.D05.M11.Inertia.intrinsic_invariants := by
  intro V _ _ _ B p q r e he
  obtain ⟨hp, hq, hr⟩ := MaximalPositive.real_invariants B e he
  have hd := e.finrank_eq
  have hn := Nondegenerate.rank_nullity_left B
  have hd' : finrank ℝ V = p + q + r := by
    simpa only [Coordinates, Module.finrank_prod, Module.finrank_pi, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
      Nat.add_assoc] using hd
  refine ⟨hp, hq, hr, hd', ?_⟩
  omega

theorem unique_triple : Specs.D05.M11.Inertia.unique_triple := by
  intro V _ _ _ B p q r p' q' r' e f he hf
  obtain ⟨hp, hq, hr, _, _⟩ := intrinsic_invariants B e he
  obtain ⟨hp', hq', hr', _, _⟩ := intrinsic_invariants B f hf
  exact ⟨hp.unique hp', hq.unique hq', hr.symm.trans hr'⟩

theorem unique_matrix_triple : Specs.D05.M11.Inertia.unique_matrix_triple := by
  intro V _ _ _ B p q r p' q' r' b c hb hc
  exact unique_triple B _ _ ((matrix_iff_coordinates B b).mp hb)
    ((matrix_iff_coordinates B c).mp hc)

theorem congruence_classification : Specs.D05.M11.Inertia.congruence_classification := by
  intro V W _ _ _ _ _ _ B C p q r p' q' r' e f he hf
  constructor
  · rintro ⟨g, hg⟩
    have hfg : IsNormalForm B (g.trans f) := by
      intro x y
      rw [hg, hf]
      rfl
    exact unique_triple B e (g.trans f) he hfg
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨e.trans f.symm, ?_⟩
    intro x y
    rw [he, hf]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

theorem signature_does_not_classify : Specs.D05.M11.Inertia.signature_does_not_classify := by
  let V := Coordinates ℝ 1 1 0
  let B : LinearMap.BilinForm ℝ V := LinearMap.mk₂ ℝ
    (fun x y => x.1 0 * y.1 0 - x.2.1 0 * y.2.1 0)
    (by
      intro x y z
      change (x.1 0 + y.1 0) * z.1 0 - (x.2.1 0 + y.2.1 0) * z.2.1 0 =
        (x.1 0 * z.1 0 - x.2.1 0 * z.2.1 0) + (y.1 0 * z.1 0 - y.2.1 0 * z.2.1 0)
      ring)
    (by
      intro c x y
      change (c * x.1 0) * y.1 0 - (c * x.2.1 0) * y.2.1 0 =
        c * (x.1 0 * y.1 0 - x.2.1 0 * y.2.1 0)
      ring)
    (by
      intro x y z
      change x.1 0 * (y.1 0 + z.1 0) - x.2.1 0 * (y.2.1 0 + z.2.1 0) =
        (x.1 0 * y.1 0 - x.2.1 0 * y.2.1 0) + (x.1 0 * z.1 0 - x.2.1 0 * z.2.1 0)
      ring)
    (by
      intro c x y
      change x.1 0 * (c * y.1 0) - x.2.1 0 * (c * y.2.1 0) =
        c * (x.1 0 * y.1 0 - x.2.1 0 * y.2.1 0)
      ring)
  let f : V ≃ₗ[ℝ] Coordinates ℝ 0 0 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simp [V, Coordinates])
  have he : IsNormalForm B (LinearEquiv.refl ℝ V) := by
    intro x y
    simp [B]
  have hf : IsNormalForm (0 : LinearMap.BilinForm ℝ V) f := by
    intro x y
    simp
  refine ⟨B, 0, ?_, ?_, he, ⟨f, hf⟩, rfl, ?_⟩
  · constructor
    intro x y
    rw [he, he]
    simp only [mul_comm]
  · constructor
    intro x y
    rfl
  · rintro ⟨g, hg⟩
    have hh := hg ((fun _ => 1), 0, 0) ((fun _ => 1), 0, 0)
    rw [he] at hh
    simp at hh

end D05.M11.Inertia
