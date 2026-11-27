import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.AbelianKernelAction
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.ExtensionClass

namespace GaloisFormalization.IG.FiniteEmbeddingProblem

open scoped IsMulCommutative

noncomputable section

abbrev NormalizedSection := @Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.NormalizedSection
abbrev normalizedSection := @Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.normalizedSection
abbrev factorSet := @Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.factorSet
abbrev kernelCoordinate := @Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.kernelCoordinate
abbrev sectionCoordinates := @Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.sectionCoordinates
abbrev factorCochain := @Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.factorCochain
abbrev factorCocycle := @Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.factorCocycle
abbrev continuousExtensionClass :=
  @Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.continuousExtensionClass
abbrev extensionClass := @Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.extensionClass

universe u v w

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
  (P : FiniteEmbeddingProblem Γ B Q) (s : NormalizedSection P)

local notation "A" => Additive P.kernel

theorem factorSet_coe (q r : Q) :
    ((factorSet P s q r).toMul : B) = s q * s r * (s (q * r))⁻¹ := rfl

private theorem factorSet_mul_section (q r : Q) :
    ((factorSet P s q r).toMul : B) * s (q * r) = s q * s r := by
  rw [factorSet_coe, inv_mul_cancel_right]

theorem factorSet_normalized :
    (∀ q : Q, factorSet P s 1 q = 0) ∧ (∀ q : Q, factorSet P s q 1 = 0) := by
  constructor <;> intro q <;> apply Additive.toMul.injective <;> apply Subtype.ext
  · simp only [factorSet_coe, s.map_one, one_mul, mul_inv_cancel, toMul_zero,
      Subgroup.coe_one]
  · simp only [factorSet_coe, s.map_one, mul_one, mul_inv_cancel, toMul_zero,
      Subgroup.coe_one]

theorem sectionCoordinates_apply (a : A) (q : Q) :
    sectionCoordinates P s (a, q) = (a.toMul : B) * s q := rfl

theorem sectionCoordinates_symm_apply (b : B) :
    (sectionCoordinates P s).symm b = (kernelCoordinate P s b, P.pi b) := rfl

variable [IsMulCommutative P.kernel]

local instance kernelAction : DistribMulAction Q A := P.quotientKernelAction

theorem factorSet_identity (q r t : Q) :
    factorSet P s q r + factorSet P s (q * r) t =
      q • factorSet P s r t + factorSet P s q (r * t) :=
  Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.factorSet_identity P s q r t

theorem factorCocycle_apply (q r : Q) :
    (factorCocycle P s).val.val ![q, r] = factorSet P s q r := rfl

theorem sectionCoordinates_mul (a b : A) (q r : Q) :
    sectionCoordinates P s (a, q) * sectionCoordinates P s (b, r) =
      sectionCoordinates P s (a + q • b + factorSet P s q r, q * r) := by
  have h : ((q • b).toMul : B) = s q * (b.toMul : B) * (s q)⁻¹ := by
    simpa only [s.pi_apply] using P.quotientKernelAction_apply (s q) b
  simp only [sectionCoordinates_apply, toMul_add, Subgroup.coe_mul, h, factorSet_coe]
  group

/-- Translating a section on the left by a kernel-valued function adds its coboundary. -/
theorem factorSet_change (s' : NormalizedSection P) (b : Q → A)
    (hb : ∀ q, s' q = (b q).toMul.val * s q) (q r : Q) :
    factorSet P s' q r = factorSet P s q r + (b q + q • b r - b (q * r)) := by
  have h := calc
    sectionCoordinates P s (b q + q • b r + factorSet P s q r, q * r) =
        sectionCoordinates P s (b q, q) * sectionCoordinates P s (b r, r) :=
      (sectionCoordinates_mul P s (b q) (b r) q r).symm
    _ = s' q * s' r := by rw [sectionCoordinates_apply, sectionCoordinates_apply, ← hb q, ← hb r]
    _ = (factorSet P s' q r).toMul.val * s' (q * r) :=
      (factorSet_mul_section P s' q r).symm
    _ = sectionCoordinates P s (factorSet P s' q r + b (q * r), q * r) := by
      rw [sectionCoordinates_apply, hb (q * r), toMul_add, Subgroup.coe_mul, mul_assoc]
  have hfst := congrArg Prod.fst ((sectionCoordinates P s).injective h)
  rw [← add_sub_assoc, eq_sub_iff_add_eq]
  exact hfst.symm.trans (add_comm (b q + q • b r) _)

/-- Every normalized section represents the same class in the continuous complex. -/
theorem continuousClass_of_section :
    GH.continuousClass Q A 2 (factorCocycle P s) = continuousExtensionClass P := by
  let t := normalizedSection P
  change GH.continuousClass Q A 2 (factorCocycle P s) =
    GH.continuousClass Q A 2 (factorCocycle P t)
  let b (q : Q) := kernelCoordinate P t (s q)
  have hb (q : Q) : s q = (b q).toMul.val * t q := by
    change s q = s q * (t (P.pi (s q)))⁻¹ * t q
    rw [s.pi_apply, inv_mul_cancel_right]
  apply (GH.continuousClass_succ_eq_iff (n := 1) (factorCocycle P s) (factorCocycle P t)).mpr
  let z := GH.cochainOne b continuous_of_discreteTopology
  refine ⟨z, Subtype.ext ?_⟩
  funext x
  have hx : ![x 0, x 1] = x := by
    funext i
    fin_cases i <;> rfl
  rw [← hx]
  change (GH.continuousDifferential Q A 1 z).val ![x 0, x 1] =
    factorSet P s (x 0) (x 1) - factorSet P t (x 0) (x 1)
  rw [GH.differential_one, factorSet_change P t s b hb]
  change b (x 0) + x 0 • b (x 1) - b (x 0 * x 1) = _
  abel

/-- The finite discrete comparison carries the continuous extension class to the ordinary one. -/
theorem ordinaryClass_comparison :
    ∃ e : GH.ContinuousH Q A 2 ≃+ groupCohomology (GH.integralRepresentation.{w,v,max w v} Q A) 2,
    GH.Specification.IsOrdinaryClassComparison.{w,v,0} Q A 2 e ∧
      e (continuousExtensionClass P) = extensionClass P :=
  ⟨GH.ordinaryCohomologyEquiv.{w,v,0} Q A 2, GH.ordinaryCohomologyEquiv_class.{w,v,0} Q A 2,
    GH.ordinaryCohomologyEquiv_class.{w,v,0} Q A 2 (factorCocycle P (normalizedSection P))⟩

/-- The ordinary class also has the cocycle of any normalized section as a representative. -/
theorem ordinaryClass_of_section :
    groupCohomology.π (GH.integralRepresentation.{w,v,max w v} Q A) 2
      (GH.ordinaryCyclesMk.{w,v,0} Q A 2 (factorCocycle P s)) = extensionClass P := by
  obtain ⟨e, he, hclass⟩ := ordinaryClass_comparison P
  rw [← he (factorCocycle P s), continuousClass_of_section, hclass]

/-- The class in the continuous complex vanishes exactly when the quotient map splits. -/
theorem continuousExtensionClass_zero_iff_split :
    continuousExtensionClass P = 0 ↔ P.IsSplit := by
  constructor
  · intro h
    let t := normalizedSection P
    let c := factorCocycle P t
    have hc : GH.continuousClass Q A 2 c = GH.continuousClass Q A 2 0 := by
      change GH.continuousClass Q A 2 (factorCocycle P t) = GH.continuousClass Q A 2 0
      rw [continuousClass_of_section, map_zero]
      exact h
    obtain ⟨z, hz⟩ := (GH.continuousClass_succ_eq_iff (n := 1) c 0).mp hc
    let b (q : Q) := z.val ![q]
    have hb (q r : Q) : b q + q • b r - b (q * r) = factorSet P t q r := calc
      _ = (GH.continuousDifferential Q A 1 z).val ![q, r] :=
        (GH.differential_one z q r).symm
      _ = factorSet P t q r := by
        rw [hz]
        change factorSet P t q r - 0 = factorSet P t q r
        exact sub_zero _
    have hb1 : b 1 = 0 := by
      simpa only [one_smul, mul_one, add_sub_cancel_right,
        (factorSet_normalized P t).1 1] using hb 1 1
    let t' : NormalizedSection P :=
      ⟨fun q => (-(b q)).toMul.val * t q,
        fun q => by
          have hker : P.pi (-(b q)).toMul.val = 1 := (-(b q)).toMul.property
          change P.pi ((-(b q)).toMul.val * t q) = q
          rw [map_mul, hker, t.pi_apply, one_mul],
        by simp only [hb1, neg_zero, toMul_zero, Subgroup.coe_one, t.map_one, mul_one]⟩
    have ht (q r : Q) : factorSet P t' q r = 0 := by
      rw [factorSet_change P t t' (fun q => -b q) (fun _ => rfl), ← hb q r, smul_neg]
      abel
    let f : Q →* B :=
      { toFun := t'.toFun
        map_one' := t'.map_one
        map_mul' := fun q r => by
          have hm := factorSet_mul_section P t' q r
          rw [ht, toMul_zero, Subgroup.coe_one, one_mul] at hm
          exact hm }
    exact ⟨f, MonoidHom.ext t'.pi_apply⟩
  · rintro ⟨f, hf⟩
    let t : NormalizedSection P := ⟨f, DFunLike.congr_fun hf, map_one f⟩
    have ht : factorCocycle P t = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      funext x
      change factorSet P t (x 0) (x 1) = 0
      apply Additive.toMul.injective
      apply Subtype.ext
      change f (x 0) * f (x 1) * (f (x 0 * x 1))⁻¹ = 1
      rw [← map_mul, mul_inv_cancel]
    rw [← continuousClass_of_section P t, ht, map_zero]

/-- A finite abelian extension splits exactly when its ordinary cohomology class vanishes. -/
theorem extensionClass_zero_iff_split :
    extensionClass P = 0 ↔ P.IsSplit := by
  obtain ⟨e, _, he⟩ := ordinaryClass_comparison P
  rw [← he, map_eq_zero_iff e e.injective, continuousExtensionClass_zero_iff_split]

end

end GaloisFormalization.IG.FiniteEmbeddingProblem
