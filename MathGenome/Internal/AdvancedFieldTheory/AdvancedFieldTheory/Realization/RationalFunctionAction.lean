import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Realization.RationalFunctionAction

universe u v
noncomputable section

namespace AdvancedFieldTheory.Realization

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- All the quotient components are finite, by compactness. -/
theorem quotient_finite [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenNormalSubgroup G) : Finite (G ⧸ U.toSubgroup) :=
  Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'

/-- The stabilizer of any point in the `U` component is exactly `U`. -/
theorem point_fixed_iff (g : G) (x : CosetPoint G) :
    g • x = x ↔ g ∈ x.1 := by
  rcases x with ⟨U, q⟩
  change ((⟨U, g • q⟩ : CosetPoint G) = ⟨U, q⟩) ↔ g ∈ U
  rw [Sigma.mk.inj_iff]
  simp only [true_and, heq_eq_eq]
  have hmul : g • q = (g : G ⧸ U.toSubgroup) * q := by
    induction q using Quotient.inductionOn' with | h a => rfl
  rw [hmul, mul_eq_right, QuotientGroup.eq_one_iff]
  rfl

/-- Point stabilizers are open, without using compactness. -/
theorem point_stabilizer_open (x : CosetPoint G) :
    IsOpen (MulAction.stabilizer G x : Set G) := by
  have h : (MulAction.stabilizer G x : Set G) = (x.1 : Set G) := by
    ext g
    exact point_fixed_iff g x
  rw [h]
  exact x.1.isOpen'

/-- Open normal subgroups separate elements of a profinite group. -/
theorem eq_one_of_mem_openNormal [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (g : G)
    (h : ∀ U : OpenNormalSubgroup G, g ∈ U) : g = 1 := by
  by_contra hne
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton : IsOpen ({g}ᶜ : Set G))
    (show (1 : G) ∈ ({g}ᶜ : Set G) from fun he => hne (Set.mem_singleton_iff.mp he).symm)
  exact hU (h U) rfl

/-- The quotient-set action is faithful, including for the trivial group. -/
theorem point_faithful [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] : FaithfulSMul G (CosetPoint G) := by
  refine ⟨fun {g h} heq => ?_⟩
  have hk : h⁻¹ * g = 1 := eq_one_of_mem_openNormal _ fun U => by
    apply (point_fixed_iff (h⁻¹ * g) ⟨U, 1⟩).mp
    rw [mul_smul, heq, inv_smul_smul]
  exact (inv_mul_eq_one.mp hk).symm

variable (k : Type v) [Field k]

/-- Variables remain distinct in the fraction field. -/
theorem indeterminate_injective : Function.Injective (indeterminate G k) :=
  (IsFractionRing.injective (PolynomialRing G k) (RationalField G k)).comp
    MvPolynomial.X_injective

/-- The polynomial action is the specified renaming on variables. -/
theorem polynomialAction_X (g : G) (x : CosetPoint G) :
    polynomialAction G k g (MvPolynomial.X x) = MvPolynomial.X (g • x) := by
  simp [polynomialAction, MulAction.toPerm]

/-- Fraction-field automorphisms extend the polynomial automorphisms. -/
theorem rationalAction_algebraMap (g : G) (p : PolynomialRing G k) :
    rationalAction G k g (algebraMap (PolynomialRing G k) (RationalField G k) p) =
      algebraMap (PolynomialRing G k) (RationalField G k) (polynomialAction G k g p) := by
  exact IsFractionRing.fieldEquivOfAlgEquiv_algebraMap k _ _ _ _

/-- This is precisely `t_x ↦ t_{g x}`. -/
theorem rationalAction_indeterminate (g : G) (x : CosetPoint G) :
    rationalAction G k g (indeterminate G k x) = indeterminate G k (g • x) := by
  simp only [indeterminate, rationalAction_algebraMap, polynomialAction_X]

/-- The automorphisms fix the specified coefficient field. -/
theorem rationalAction_coefficient (g : G) (a : k) :
    rationalAction G k g (algebraMap k (RationalField G k) a) =
      algebraMap k (RationalField G k) a :=
  (rationalAction G k g).commutes a

/-- Faithfulness passes from the variables to their rational function field. -/
theorem rationalAction_injective [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] : Function.Injective (rationalAction G k) := by
  let := point_faithful (G := G)
  intro g h heq
  apply eq_of_smul_eq_smul (α := CosetPoint G)
  intro x
  apply indeterminate_injective k
  simpa only [rationalAction_indeterminate] using
    congrArg (fun f : RationalField G k ≃ₐ[k] RationalField G k => f (indeterminate G k x)) heq

/-- A polynomial fixed on all variables in its finite variable set is fixed. -/
theorem polynomialAction_eq_of_vars (g : G) (p : PolynomialRing G k)
    (h : ∀ x ∈ p.vars, g • x = x) : polynomialAction G k g p = p := by
  have hc : (polynomialAction G k g).toRingHom.comp MvPolynomial.C =
      (RingHom.id (PolynomialRing G k)).comp MvPolynomial.C := by
    apply RingHom.ext
    intro a
    exact (polynomialAction G k g).commutes a
  exact MvPolynomial.hom_congr_vars hc (fun x hx _ => by
    change polynomialAction G k g (MvPolynomial.X x) = MvPolynomial.X x
    rw [polynomialAction_X, h x hx]) rfl

/-- Numerator and denominator give an explicit finite set of variables fixing a fraction. -/
theorem fraction_finite_support (z : RationalField G k) :
    ∃ p q : PolynomialRing G k, q ≠ 0 ∧
      z = algebraMap (PolynomialRing G k) (RationalField G k) p /
        algebraMap (PolynomialRing G k) (RationalField G k) q ∧
      ∀ g : G, (∀ x, x ∈ p.vars ∨ x ∈ q.vars → g • x = x) → rationalAction G k g z = z := by
  classical
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (PolynomialRing G k) z
  refine ⟨p, q, mem_nonZeroDivisors_iff_ne_zero.mp hq, rfl, ?_⟩
  intro g hg
  rw [map_div₀, rationalAction_algebraMap, rationalAction_algebraMap,
    polynomialAction_eq_of_vars k g p (fun x hx => hg x (Or.inl hx)),
    polynomialAction_eq_of_vars k g q (fun x hx => hg x (Or.inr hx))]

/-- Each rational function is fixed by the pointwise stabilizer of finitely many variables. -/
theorem rationalField_finite_support (z : RationalField G k) :
    ∃ S : Finset (CosetPoint G), ∀ g : G,
      (∀ x ∈ S, g • x = x) → g • z = z := by
  classical
  obtain ⟨p, q, _, _, h⟩ := fraction_finite_support k z
  exact ⟨p.vars ∪ q.vars, fun g hg => h g (fun x hx => hg x (Finset.mem_union.mpr hx))⟩

/-- The action by field automorphisms is faithful. -/
theorem rationalField_faithful [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] : FaithfulSMul G (RationalField G k) := by
  refine ⟨fun {g h} heq => rationalAction_injective k ?_⟩
  exact AlgEquiv.ext heq

/-- All rational-function stabilizers are open. -/
theorem rationalField_stabilizer_open [IsTopologicalGroup G] (z : RationalField G k) :
    IsOpen (MulAction.stabilizer G z : Set G) := by
  classical
  obtain ⟨S, hS⟩ := rationalField_finite_support k z
  let H : Subgroup G := ⨅ x : S, MulAction.stabilizer G (x : CosetPoint G)
  have hH : IsOpen (H : Set G) := by
    dsimp [H]
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun x => point_stabilizer_open (x : CosetPoint G)
  apply Subgroup.isOpen_mono (H₁ := H) (H₂ := MulAction.stabilizer G z) ?_ hH
  intro g hg
  apply hS g
  intro x hx
  have hmem := (Subgroup.mem_iInf.mp hg) (⟨x, hx⟩ : S)
  exact MulAction.mem_stabilizer_iff.mp hmem

/-- The characteristic of the freely chosen coefficient field is preserved. -/
theorem rationalField_characteristic :
    ringChar (RationalField G k) = ringChar k :=
  (Algebra.ringChar_eq k (RationalField G k)).symm

end AdvancedFieldTheory.Realization
