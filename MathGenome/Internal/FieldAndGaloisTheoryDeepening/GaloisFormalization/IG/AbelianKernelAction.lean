import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.EmbeddingProblem
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.AbelianKernelAction

/-!
The continuous actions on the additive kernel of a finite embedding problem.

With `[IsMulCommutative P.kernel]`, opening the `IsMulCommutative` scope also supplies
the `AddCommGroup` instance on `Additive P.kernel` for use in cohomology.
-/

namespace GaloisFormalization.IG.FiniteEmbeddingProblem

universe u v w

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]

variable (P : FiniteEmbeddingProblem Γ B Q)

section Abelian

variable [IsMulCommutative P.kernel]

/-- The quotient group acts on the abelian kernel by conjugation with representatives. -/
noncomputable abbrev quotientKernelAction : DistribMulAction Q (Additive P.kernel) :=
  Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.quotientKernelActionValue P

/-- The action of the profinite group is the restriction along the prescribed quotient map. -/
noncomputable abbrev pullbackKernelAction : DistribMulAction Γ (Additive P.kernel) :=
  letI := P.quotientKernelAction
  DistribMulAction.compHom (Additive P.kernel) P.rho.toMonoidHom

/-- Every representative in the middle group computes the same action. -/
theorem quotientKernelAction_apply :
    letI := P.quotientKernelAction
    ∀ (b : B) (a : Additive P.kernel),
      ((P.pi b • a).toMul : B) = b * (a.toMul : B) * b⁻¹ := by
  let := P.quotientKernelAction
  intro b a
  let conjugation := Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.quotientConjugationValue P
  change ((conjugation (P.pi b) a.toMul : P.kernel) : B) = b * (a.toMul : B) * b⁻¹
  have hb : conjugation (P.pi b) = MulAut.conjNormal b := by
    exact P.pi.toMonoidHom.liftOfRightInverse_comp_apply _
      (Function.rightInverse_surjInv P.pi_surjective) _ b
  rw [hb, MulAut.conjNormal_apply]

/-- The representative formula determines the action as a distributive action. -/
theorem quotientKernelAction_unique (action : DistribMulAction Q (Additive P.kernel))
    (h : letI := action
         ∀ (b : B) (a : Additive P.kernel),
           ((P.pi b • a).toMul : B) = b * (a.toMul : B) * b⁻¹) :
    action = P.quotientKernelAction := by
  ext q a
  obtain ⟨b, rfl⟩ := P.pi_surjective q
  exact (h b a).trans (P.quotientKernelAction_apply b a).symm

/-- The scalar `γ` acts on the kernel by the scalar `ρ γ`. -/
theorem pullbackKernelAction_apply :
    letI := P.quotientKernelAction
    letI := P.pullbackKernelAction
    ∀ (γ : Γ) (a : Additive P.kernel), γ • a = P.rho γ • a := by
  intros
  rfl

/-- The quotient action is jointly continuous on its finite discrete domain. -/
theorem continuousSMul_quotientKernelAction :
    letI := P.quotientKernelAction
    ContinuousSMul Q (Additive P.kernel) := by
  let := P.quotientKernelAction
  exact ⟨continuous_of_discreteTopology⟩

/-- Joint continuity of the pullback follows from continuity of the prescribed map. -/
theorem continuousSMul_pullbackKernelAction :
    letI := P.pullbackKernelAction
    ContinuousSMul Γ (Additive P.kernel) := by
  let := P.quotientKernelAction
  let := P.pullbackKernelAction
  let : ContinuousSMul Q (Additive P.kernel) := P.continuousSMul_quotientKernelAction
  exact ⟨(continuous_smul (M := Q)).comp
    ((P.rho.continuous.comp continuous_fst).prodMk continuous_snd)⟩

end Abelian

/-- The kernel of a central embedding problem is abelian. -/
theorem isMulCommutative_kernel_of_isCentral (h : P.IsCentral) : IsMulCommutative P.kernel :=
  IsMulCommutative.of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (h b.property) a)

/-- A central kernel has trivial quotient action. -/
theorem quotientKernelAction_eq_self_of_isCentral (h : P.IsCentral) :
    letI := P.isMulCommutative_kernel_of_isCentral h
    letI := P.quotientKernelAction
    ∀ (q : Q) (a : Additive P.kernel), q • a = a := by
  let := P.isMulCommutative_kernel_of_isCentral h
  intro q a
  obtain ⟨b, rfl⟩ := P.pi_surjective q
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [P.quotientKernelAction_apply, Subgroup.mem_center_iff.mp (h a.toMul.property) b,
    mul_inv_cancel_right]

/-- A central kernel has trivial action through the prescribed map. -/
theorem pullbackKernelAction_eq_self_of_isCentral (h : P.IsCentral) :
    letI := P.isMulCommutative_kernel_of_isCentral h
    letI := P.pullbackKernelAction
    ∀ (γ : Γ) (a : Additive P.kernel), γ • a = a := by
  let := P.isMulCommutative_kernel_of_isCentral h
  intro γ a
  exact (P.pullbackKernelAction_apply γ a).trans
    (P.quotientKernelAction_eq_self_of_isCentral h (P.rho γ) a)

end GaloisFormalization.IG.FiniteEmbeddingProblem
