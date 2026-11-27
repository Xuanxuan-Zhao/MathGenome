import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import Mathlib.Algebra.Exact.Basic

namespace GaloisFormalization.GH.InflationRestrictionModel

open Model

universe u v

noncomputable section

variable {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- Evaluate a degree-one cocycle on a single group element. -/
abbrev value (c : continuousCocycles G M 1) (g : G) : M := c.val.val ![g]

theorem tuple_one {α : Type u} (x : Fin 1 → α) : ![x 0] = x :=
  funext fun i => by rw [Subsingleton.elim i 0]; rfl

theorem cocycle_ext {c d : continuousCocycles G M 1} (h : ∀ g, value c g = value d g) :
    c = d := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  simpa only [value, tuple_one] using h (x 0)

theorem value_mul (c : continuousCocycles G M 1) (g h : G) :
    value c (g * h) = value c g + g • value c h := by
  have hc := congrArg (fun d : continuousCochains G M 2 => d.val ![g, h])
    (LinearMap.mem_ker.mp c.property)
  change (continuousDifferential G M 1 c.val).val ![g, h] = 0 at hc
  rw [continuousDifferential_apply, differentialFormula, Fin.sum_univ_two] at hc
  rw [← tuple_one (fun i : Fin 1 => (![g, h] : Fin 2 → G) i.succ),
    ← tuple_one (Fin.contractNth (0 : Fin 2) (· * ·) (![g, h] : Fin 2 → G)),
    ← tuple_one (Fin.contractNth (1 : Fin 2) (· * ·) (![g, h] : Fin 2 → G))] at hc
  change g • value c h + ((-1 : ℤ) ^ (0 + 1) • value c (g * h) +
    (-1 : ℤ) ^ (1 + 1) • value c g) = 0 at hc
  have he : value c g + g • value c h - value c (g * h) = 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hc
  exact (sub_eq_zero.mp he).symm

private theorem differentialZero_eval (t : continuousCochains G M 0) (g : G) :
    (continuousDifferential G M 0 t).val ![g] =
      g • t.val Fin.elim0 - t.val Fin.elim0 := by
  rw [continuousDifferential_apply]
  have h (x : Fin 0 → G) : t.val x = t.val Fin.elim0 :=
    congrArg t.val (Subsingleton.elim _ _)
  simp [differentialFormula, h, sub_eq_add_neg]

/-- The class equality criterion in single-variable coordinates. -/
theorem class_eq_iff {c d : continuousCocycles G M 1} :
    continuousClass G M 1 c = continuousClass G M 1 d ↔
      ∃ b : M, ∀ g : G, value c g - value d g = g • b - b := by
  rw [show continuousClass G M 1 c = continuousClass G M 1 d ↔
      c - d ∈ continuousCoboundaries G M 1 from Submodule.Quotient.eq _]
  change (∃ t : continuousCochains G M 0, _ = c - d) ↔ _
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t.val Fin.elim0, fun g => ?_⟩
    exact (congrArg (fun a : continuousCocycles G M 1 => value a g) ht).symm.trans
      (differentialZero_eval t g)
  · rintro ⟨b, hb⟩
    refine ⟨cochainZero b, cocycle_ext fun g => ?_⟩
    exact (differentialZero_eval (cochainZero b) g).trans (hb g).symm

theorem conjugation_identity (c : continuousCocycles G M 1) (g h : G) :
    g • value c (g⁻¹ * h * g) = value c h + (h • value c g - value c g) := by
  have he : g * (g⁻¹ * h * g) = h * g := by simp [mul_assoc]
  have hc : value c g + g • value c (g⁻¹ * h * g) = value c h + h • value c g :=
    (value_mul c g _).symm.trans ((congrArg (value c) he).trans (value_mul c h g))
  calc
    _ = (value c g + g • value c (g⁻¹ * h * g)) - value c g := by abel
    _ = _ := by rw [hc]; abel

variable (N : Subgroup G) [N.Normal]

/-- Pull back arguments by inverse conjugation on the normal subgroup. -/
def inverseConjugation (g : G) : N →* N :=
  ((MulAut.conjNormal g : MulAut N).symm).toMonoidHom

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem inverseConjugation_apply (g : G) (n : N) :
    (inverseConjugation N g n : G) = g⁻¹ * (n : G) * g :=
  MulAut.conjNormal_symm_apply g n

private theorem continuous_inverseConjugation (g : G) :
    Continuous (inverseConjugation N g) := by
  apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
  have hc : Continuous (fun n : N => g⁻¹ * (n : G) * g) :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  convert hc using 1
  funext n
  exact inverseConjugation_apply N g n

omit [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] in
private theorem conjugation_compatible (g : G) (n : N) (m : M) :
    DistribSMul.toAddMonoidHom M g (inverseConjugation N g n • m) =
      n • DistribSMul.toAddMonoidHom M g m := by
  change g • ((inverseConjugation N g n : G) • m) = (n : G) • (g • m)
  simp only [inverseConjugation_apply, ← mul_smul, mul_assoc, mul_inv_cancel_left]

/-- Conjugation on degree-one cocycles is the compatible group and coefficient map. -/
def conjugatedCocycle (g : G) : continuousCocycles N M 1 →ₗ[ℤ] continuousCocycles N M 1 :=
  continuousCocycleMap (inverseConjugation N g) (continuous_inverseConjugation N g)
    (DistribSMul.toAddMonoidHom M g) (conjugation_compatible N g) 1

@[simp] theorem conjugatedCocycle_value (g : G) (c : continuousCocycles N M 1) (n : N) :
    value (conjugatedCocycle (M := M) N g c) n = g • value c (inverseConjugation N g n) := by
  change g • c.val.val (fun i => inverseConjugation N g (![n] i)) = _
  apply congrArg (fun m : M => g • m)
  apply congrArg c.val.val
  funext i
  rw [Subsingleton.elim i 0]
  rfl

private def conjugationEnd (g : G) : Module.End ℤ (ContinuousH N M 1) :=
  continuousCohomologyMap (inverseConjugation N g) (continuous_inverseConjugation N g)
    (DistribSMul.toAddMonoidHom M g) (conjugation_compatible N g) 1

private theorem conjugationEnd_class (g : G) (c : continuousCocycles N M 1) :
    conjugationEnd (M := M) N g (continuousClass N M 1 c) =
      continuousClass N M 1 (conjugatedCocycle (M := M) N g c) := rfl

/-- Conjugation induces a left action on the first cohomology group. -/
def conjugationRepresentation : Representation ℤ G (ContinuousH N M 1) where
  toFun := conjugationEnd (M := M) N
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
    change conjugationEnd (M := M) N 1 (continuousClass N M 1 c) = continuousClass N M 1 c
    rw [conjugationEnd_class]
    congr 1
    apply cocycle_ext
    intro n
    rw [conjugatedCocycle_value, one_smul]
    congr 1
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
    change conjugationEnd (M := M) N (g * h) (continuousClass N M 1 c) =
      conjugationEnd (M := M) N g (conjugationEnd (M := M) N h (continuousClass N M 1 c))
    simp only [conjugationEnd_class]
    congr 1
    apply cocycle_ext
    intro n
    simp only [conjugatedCocycle_value, mul_smul]
    congr 3
    apply Subtype.ext
    simp [mul_inv_rev, mul_assoc]

private theorem conjugationRepresentation_inner (g : N) :
    conjugationRepresentation (M := M) N (g : G) = 1 := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  change conjugationEnd (M := M) N (g : G) (continuousClass N M 1 c) = continuousClass N M 1 c
  rw [conjugationEnd_class, class_eq_iff]
  refine ⟨value c g, fun n => ?_⟩
  have hconj : inverseConjugation N (g : G) n = g⁻¹ * n * g := by
    apply Subtype.ext
    exact inverseConjugation_apply N g n
  rw [conjugatedCocycle_value, hconj]
  change g • value c (g⁻¹ * n * g) - value c n = n • value c g - value c g
  rw [conjugation_identity]
  abel

/-- The conjugation action on classes factors through the normal quotient. -/
def quotientConjugation : Representation ℤ (G ⧸ N) (ContinuousH N M 1) :=
  QuotientGroup.lift N (conjugationRepresentation (M := M) N)
    (fun g hg => conjugationRepresentation_inner N ⟨g, hg⟩)

@[simp] theorem quotientConjugation_class (g : G) (c : continuousCocycles N M 1) :
    quotientConjugation (M := M) N (QuotientGroup.mk' N g) (continuousClass N M 1 c) =
      continuousClass N M 1 (conjugatedCocycle (M := M) N g c) := rfl

/-- Restriction before passing to classes. -/
def restrictedCocycle : continuousCocycles G M 1 →ₗ[ℤ] continuousCocycles N M 1 :=
  continuousCocycleMap N.subtype continuous_subtype_val (AddMonoidHom.id M) (fun _ _ => rfl) 1

omit [N.Normal] in
@[simp] theorem restrictedCocycle_value (c : continuousCocycles G M 1) (n : N) :
    value (restrictedCocycle (M := M) N c) n = value c (n : G) := by
  apply congrArg c.val.val
  funext i
  rw [Subsingleton.elim i 0]
  rfl

omit [N.Normal] in
@[simp] theorem continuousRestriction_class (c : continuousCocycles G M 1) :
    continuousRestriction G M N 1 (continuousClass G M 1 c) =
      continuousClass N M 1 (restrictedCocycle (M := M) N c) := rfl

theorem conjugation_restricted_value (g : G) (c : continuousCocycles G M 1) (n : N) :
    value (conjugatedCocycle (M := M) N g (restrictedCocycle (M := M) N c)) n =
      value (restrictedCocycle (M := M) N c) n + ((n : G) • value c g - value c g) := by
  simp only [conjugatedCocycle_value, restrictedCocycle_value, inverseConjugation_apply]
  exact conjugation_identity c g n

/-- The fixed classes under conjugation by the quotient. -/
abbrev invariantH1 : Submodule ℤ (ContinuousH N M 1) :=
  (quotientConjugation (M := M) N).invariants

private theorem restriction_is_invariant (x : ContinuousH G M 1) :
    continuousRestriction G M N 1 x ∈ invariantH1 (M := M) N := by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  change ∀ q : G ⧸ N, quotientConjugation (M := M) N q (continuousRestriction G M N 1
    (continuousClass G M 1 c)) = continuousRestriction G M N 1 (continuousClass G M 1 c)
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  rw [continuousRestriction_class, quotientConjugation_class, class_eq_iff]
  refine ⟨value c g, fun n => ?_⟩
  rw [conjugation_restricted_value]
  change _ = (n : G) • value c g - value c g
  abel

/-- Restriction with its codomain in the actual submodule of fixed classes. -/
def invariantRestriction : ContinuousH G M 1 →ₗ[ℤ] invariantH1 (M := M) N :=
  (continuousRestriction G M N 1).codRestrict _ (restriction_is_invariant N)

end

end GaloisFormalization.GH.InflationRestrictionModel

namespace GaloisFormalization.GH.InflationRestrictionSpecification

open Model InflationRestrictionModel

universe u v w

noncomputable section

private abbrev declarationType {α : Sort w} (_ : α) : Sort w := α

set_option linter.checkUnivs false in
def QuotientConjugationType := declarationType (@quotientConjugation.{u,v})

set_option linter.checkUnivs false in
def InvariantH1Type := declarationType (@invariantH1.{u,v})

set_option linter.checkUnivs false in
def RestrictionToInvariantsType := declarationType (@invariantRestriction.{u,v})

/-- The action on a class is represented by conjugating its cocycle. -/
def ConjugationOnClasses : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
    (N : Subgroup G) [hN : N.Normal] (g : G) (c : continuousCocycles N M 1),
    ∃ d : continuousCocycles N M 1,
      (∀ n : N, value d n = g • value c
        ⟨g⁻¹ * (n : G) * g, by simpa only [inv_inv] using hN.conj_mem n n.property g⁻¹⟩) ∧
      quotientConjugation (M := M) N (QuotientGroup.mk' N g) (continuousClass N M 1 c) =
        continuousClass N M 1 d

/-- The map to fixed classes forgets to the ordinary continuous restriction. -/
def RestrictionToInvariantsFormula : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
    (N : Subgroup G) [N.Normal] (x : ContinuousH G M 1),
    (invariantRestriction (M := M) N x).val = continuousRestriction G M N 1 x

/-- The discrete fixed coefficients carry the continuous quotient action. -/
def ContinuousFixedCoefficientAction : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (N : Subgroup G) [N.Normal],
    Continuous (fun p : (G ⧸ N) × fixedCoefficients G M N => p.1 • p.2)

/-- Inflation has zero kernel. -/
def InflationInjective : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (N : Subgroup G) [N.Normal],
    Function.Injective (continuousInflation G M N 1)

/-- The restriction kernel is the image of inflation. -/
def ExactAtMiddle : Prop :=
  ∀ {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] (N : Subgroup G) [N.Normal],
    Function.Exact (continuousInflation G M N 1) (invariantRestriction (M := M) N)

/-- Proposition GH14 for a profinite group and a closed normal subgroup. -/
def ProfiniteExactSequence : Prop :=
  ∀ (G : Type u) (M : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
    (N : Subgroup G) [N.Normal], IsClosed (N : Set G) →
      Function.Exact (0 : PUnit.{1} →ₗ[ℤ] ContinuousH (G ⧸ N) (fixedCoefficients G M N) 1)
        (continuousInflation G M N 1) ∧
      Function.Exact (continuousInflation G M N 1) (invariantRestriction (M := M) N)

end

end GaloisFormalization.GH.InflationRestrictionSpecification
