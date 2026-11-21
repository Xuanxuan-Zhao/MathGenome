import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.PolynomialApproximation
import MathGenome.Internal.PointSetTopology.D10Topology.Ch16.StoneWeierstrassReal

/-! Polynomial approximation on compact Euclidean subsets, including dimension
zero and empty subsets. The range of the restriction homomorphism is the
unital algebra to which the upstream real Stone--Weierstrass theorem applies.
-/

noncomputable section
open Set

namespace D10Topology.Ch16

/-- Restrict a multivariate real polynomial to a subset of coordinate space. -/
def polynomialRestrictionHom {n : ℕ} (K : Set (Fin n → ℝ)) :
    MvPolynomial (Fin n) ℝ →ₐ[ℝ] C(K, ℝ) where
  toFun p := ⟨fun x => MvPolynomial.eval x.val p,
    p.continuous_eval.comp continuous_subtype_val⟩
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' p q := by ext x; simp
  map_mul' p q := by ext x; simp
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem polynomialRestrictionHom_apply {n : ℕ} (K : Set (Fin n → ℝ))
    (p : MvPolynomial (Fin n) ℝ) (x : K) :
    polynomialRestrictionHom K p x = MvPolynomial.eval x.val p := rfl

private theorem polynomial_range_separates {n : ℕ} (K : Set (Fin n → ℝ)) :
    SeparatesPoints ((polynomialRestrictionHom K).range : Set C(K, ℝ)) := by
  classical
  intro x y hxy
  have hcoords : ∃ i, x.val i ≠ y.val i := by
    by_contra h
    apply hxy
    apply Subtype.ext
    funext i
    exact not_not.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hcoords
  refine ⟨polynomialRestrictionHom K (MvPolynomial.X i), ⟨MvPolynomial.X i, rfl⟩, ?_⟩
  simpa using hi

theorem polynomial_uniform_approximation :
    Specs.D10Topology.Ch16.PolynomialApproximation.polynomial_uniform_approximation := by
  intro n K hK f ε hε
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A := (polynomialRestrictionHom K).range.toNonUnitalSubalgebra
  obtain ⟨g, hg, herr⟩ := stone_weierstrass_real A
    (polynomialRestrictionHom K).range.one_mem (polynomial_range_separates K) f ε hε
  obtain ⟨p, rfl⟩ := hg
  refine ⟨p, ?_⟩
  intro x
  have hx := ((f - polynomialRestrictionHom K p).norm_lt_iff hε).mp herr x
  simpa only [ContinuousMap.sub_apply, polynomialRestrictionHom_apply, Real.norm_eq_abs] using hx

theorem polynomial_restrictions_dense :
    Specs.D10Topology.Ch16.PolynomialApproximation.polynomial_restrictions_dense := by
  intro n K hK
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set C(K, ℝ) := {g | ∃ p : MvPolynomial (Fin n) ℝ,
    ∀ x : K, g x = MvPolynomial.eval x.val p}
  apply Set.eq_univ_of_forall
  intro f
  apply (mem_uniformClosure_iff_pointwise_error S f).mpr
  intro ε hε
  obtain ⟨p, hp⟩ := polynomial_uniform_approximation n K hK f ε hε
  refine ⟨polynomialRestrictionHom K p, ⟨p, fun _ => rfl⟩, ?_⟩
  simpa only [polynomialRestrictionHom_apply, Real.norm_eq_abs] using hp

/-- Transfer the coordinate-space result through the coordinate homeomorphism
from the canonical L² Euclidean space. Polynomial values are preserved exactly. -/
theorem euclidean_polynomial_uniform_approximation :
    Specs.D10Topology.Ch16.PolynomialApproximation.euclidean_polynomial_uniform_approximation := by
  intro n K hK f ε hε
  let e := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
  let eK := e.image K
  let f' : C(e '' K, ℝ) := f.comp ⟨eK.symm, eK.symm.continuous⟩
  obtain ⟨p, hp⟩ := polynomial_uniform_approximation n (e '' K)
    (hK.image e.continuous) f' ε hε
  refine ⟨p, fun x => ?_⟩
  have hx := hp (eK x)
  change |f (eK.symm (eK x)) - MvPolynomial.eval (fun i => x.val i) p| < ε at hx
  simpa only [eK.symm_apply_apply] using hx

theorem weierstrass_interval :
    Specs.D10Topology.Ch16.PolynomialApproximation.weierstrass_interval := by
  intro a b f ε hε
  let A := (Polynomial.toContinuousMapOnAlgHom (R := ℝ) (Icc a b)).range.toNonUnitalSubalgebra
  have hsep : SeparatesPoints (A : Set C(Icc a b, ℝ)) := by
    intro x y hxy
    refine ⟨Polynomial.toContinuousMapOnAlgHom (Icc a b) Polynomial.X,
      ⟨Polynomial.X, rfl⟩, ?_⟩
    simpa using (fun h : x.val = y.val => hxy (Subtype.ext h))
  obtain ⟨g, hg, herr⟩ := stone_weierstrass_real A
    (Polynomial.toContinuousMapOnAlgHom (Icc a b)).range.one_mem hsep f ε hε
  obtain ⟨p, rfl⟩ := hg
  refine ⟨p, fun x => ?_⟩
  have hx := ((f - Polynomial.toContinuousMapOnAlgHom (Icc a b) p).norm_lt_iff hε).mp herr x
  simpa only [ContinuousMap.sub_apply, Polynomial.toContinuousMapOnAlgHom_apply,
    Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
    Real.norm_eq_abs] using hx

theorem zero_dimensional_constant :
    Specs.D10Topology.Ch16.PolynomialApproximation.zero_dimensional_constant := by
  intro K f
  by_cases hK : Nonempty K
  · obtain ⟨x₀⟩ := hK
    refine ⟨f x₀, fun x => ?_⟩
    simp only [MvPolynomial.eval_C]
    exact congrArg f (Subsingleton.elim x x₀)
  · exact ⟨0, fun x => False.elim (hK ⟨x⟩)⟩

theorem empty_polynomial_exact :
    Specs.D10Topology.Ch16.PolynomialApproximation.empty_polynomial_exact := by
  intro n f x
  exact False.elim x.property

end D10Topology.Ch16
