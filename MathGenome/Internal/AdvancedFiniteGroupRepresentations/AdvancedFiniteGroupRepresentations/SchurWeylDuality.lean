import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.FirstCentralizer
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.IsotypicMatrixBlocks
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurWeylDuality

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct DirectSum
universe u
namespace AdvancedFiniteGroupRepresentations
variable (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The GL span is the product of all endomorphism algebras on the actual
multiplicity spaces. Zero spaces contribute their one-element algebra. -/
theorem multiplicityFamily_mem_span {n : ℕ}
    (F : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p)) :
    F ∈ Submodule.span ℂ (Set.range (fun g : LinearGroup V =>
      fun p : Partition n => tensorMultiplicityOperator V p g)) := by
  classical
  have hB : tensorB V n = secondFactorBlocks V n := by
    rw [← firstCentralizer V n, tensorA_eq_firstFactorBlocks V n,
      firstFactorBlocks_centralizer V n]
  have hT : secondFactorTransport V F ∈
      Submodule.span ℂ (Set.range (diagonalOperator V n)) := by
    rw [← tensorB_span V n, hB]
    exact secondFactorTransport_mem V F
  have aux : ∀ T ∈ Submodule.span ℂ (Set.range (diagonalOperator V n)),
      ∃ H : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p),
      H ∈ Submodule.span ℂ (Set.range (fun g : LinearGroup V =>
        fun p : Partition n => tensorMultiplicityOperator V p g)) ∧
      ∀ (p : Partition n) (f : TensorMultiplicity V p) (v : SpechtModule p),
        T (f.val v) = (H p f).val v := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨g, rfl⟩ := hT
      exact ⟨fun p => tensorMultiplicityOperator V p g,
        Submodule.subset_span ⟨g, rfl⟩, fun _ _ _ => rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ _ => rfl⟩
    | add T U hT hU ihT ihU =>
      obtain ⟨H, hH, heH⟩ := ihT
      obtain ⟨K, hK, heK⟩ := ihU
      exact ⟨H + K, Submodule.add_mem _ hH hK, fun p f v =>
        (congrArg₂ (· + ·) (heH p f v) (heK p f v))⟩
    | smul c T hT ih =>
      obtain ⟨H, hH, heH⟩ := ih
      exact ⟨c • H, Submodule.smul_mem _ c hH,
        fun p f v => congrArg (c • ·) (heH p f v)⟩
  obtain ⟨H, hH, heH⟩ := aux _ hT
  have he : F = H := by
    funext p
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact (secondFactorTransport_evaluation V F p v f).symm.trans (heH p f v)
  exact he ▸ hH

/-- A GL-invariant subspace of a multiplicity space is stable under every
linear endomorphism. -/
theorem multiplicity_invariant_endomorphism {n : ℕ} (p : Partition n)
    (W : Submodule ℂ (TensorMultiplicity V p))
    (hW : ∀ (g : LinearGroup V) (f : TensorMultiplicity V p),
      f ∈ W → tensorMultiplicityOperator V p g f ∈ W)
    (a : Module.End ℂ (TensorMultiplicity V p)) (f : TensorMultiplicity V p) (hf : f ∈ W) :
    a f ∈ W := by
  classical
  let F : ∀ q : Partition n, Module.End ℂ (TensorMultiplicity V q) := Function.update 0 p a
  have hF := multiplicityFamily_mem_span V F
  have aux : ∀ H ∈ Submodule.span ℂ (Set.range (fun g : LinearGroup V =>
      fun q : Partition n => tensorMultiplicityOperator V q g)), H p f ∈ W := by
    intro H hH
    induction hH using Submodule.span_induction with
    | mem H hH =>
      obtain ⟨g, rfl⟩ := hH
      exact hW g f hf
    | zero => exact W.zero_mem
    | add H K hH hK ihH ihK => exact W.add_mem ihH ihK
    | smul c H hH ih => exact W.smul_mem c ih
  simpa [F] using aux F hF

/-- Every nonzero canonical multiplicity representation is irreducible. -/
theorem tensorMultiplicity_irreducible {n : ℕ} (p : Partition n)
    [Nontrivial (TensorMultiplicity V p)] :
    (tensorMultiplicityRepresentation V p).IsIrreducible := by
  have : Nontrivial (Subrepresentation (tensorMultiplicityRepresentation V p)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro he
    obtain ⟨f, hf⟩ := exists_ne (0 : TensorMultiplicity V p)
    have hmem : f ∈ (⊥ : Subrepresentation (tensorMultiplicityRepresentation V p)) := by
      rw [he]
      trivial
    exact hf (show f = 0 from hmem)
  apply IsSimpleOrder.mk'
  intro W
  by_cases hW : W = ⊥
  · exact Or.inr hW
  · left
    have hex : ∃ f : TensorMultiplicity V p, f ∈ W ∧ f ≠ 0 := by
      by_contra h
      apply hW
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm
      · intro f hf
        exact show f = 0 from by
          by_contra hf0
          exact h ⟨f, hf, hf0⟩
      · exact bot_le
    obtain ⟨f, hf, hf0⟩ := hex
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hf0
    apply top_unique
    intro y _
    have h := multiplicity_invariant_endomorphism V p W.toSubmodule
      (fun g _ hg => W.apply_mem_toSubmodule g hg) (φ.smulRight y) f hf
    change y ∈ W.toSubmodule
    simpa only [LinearMap.smulRight_apply, hφ, one_smul] using h

/-- A group intertwiner also intertwines the independent full matrix families. -/
theorem multiplicity_intertwiner_family {n : ℕ} (p q : Partition n)
    (k : TensorMultiplicity V p →ₗ[ℂ] TensorMultiplicity V q)
    (hk : ∀ (g : LinearGroup V) (f : TensorMultiplicity V p),
      k (tensorMultiplicityOperator V p g f) = tensorMultiplicityOperator V q g (k f))
    (F : ∀ r : Partition n, Module.End ℂ (TensorMultiplicity V r))
    (f : TensorMultiplicity V p) : k (F p f) = F q (k f) := by
  have hF := multiplicityFamily_mem_span V F
  induction hF using Submodule.span_induction with
  | mem H hH =>
    obtain ⟨g, rfl⟩ := hH
    exact hk g f
  | zero => exact map_zero k
  | add H K hH hK ihH ihK => simpa only [Pi.add_apply, LinearMap.add_apply, map_add] using congrArg₂ (· + ·) ihH ihK
  | smul c H hH ih => simpa only [Pi.smul_apply, LinearMap.smul_apply, map_smul] using congrArg (c • ·) ih

/-- Distinct multiplicity spaces have no nonzero GL intertwiner, even if
one or both spaces are zero. -/
theorem tensorMultiplicity_intertwiner_eq_zero {n : ℕ} (p q : Partition n) (hpq : p ≠ q)
    (k : TensorMultiplicity V p →ₗ[ℂ] TensorMultiplicity V q)
    (hk : ∀ (g : LinearGroup V) (f : TensorMultiplicity V p),
      k (tensorMultiplicityOperator V p g f) = tensorMultiplicityOperator V q g (k f)) :
    k = 0 := by
  classical
  let F : ∀ r : Partition n, Module.End ℂ (TensorMultiplicity V r) := Function.update 0 p 1
  apply LinearMap.ext
  intro f
  have h := multiplicity_intertwiner_family V p q k hk F f
  simpa [F, Ne.symm hpq] using h

/-- Distinct nonzero multiplicities are not isomorphic as GL(V) representations. -/
theorem tensorMultiplicity_nonisomorphic {n : ℕ} (p q : Partition n)
    [Nontrivial (TensorMultiplicity V p)] [Nontrivial (TensorMultiplicity V q)]
    (hpq : p ≠ q) :
    ¬ Nonempty (Representation.Equiv (tensorMultiplicityRepresentation V p)
      (tensorMultiplicityRepresentation V q)) := by
  rintro ⟨e⟩
  have he := tensorMultiplicity_intertwiner_eq_zero V p q hpq e.toLinearEquiv.toLinearMap
    (fun g f => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g f)
  obtain ⟨f, hf⟩ := exists_ne (0 : TensorMultiplicity V p)
  apply hf
  apply e.toLinearEquiv.injective
  have h := DFunLike.congr_fun he f
  simpa using h

/-- Evaluation is the canonical product-equivariant isomorphism. -/
theorem schurWeylEvaluation : Specs.AdvancedFiniteGroupRepresentations.schurWeylEvaluationType.{u} :=
  tensorEvaluation_isomorphism

/-- The second centralizer identity holds also in degree zero and on V=0. -/
theorem secondCentralizer (n : ℕ) :
    Subalgebra.centralizer ℂ (tensorB V n : Set (Module.End ℂ (TensorPower V n))) =
      tensorA V n := by
  rw [← firstCentralizer V n, tensorA_eq_firstFactorBlocks V n,
    firstFactorBlocks_centralizer V n, secondFactorBlocks_centralizer V n,
    ← tensorA_eq_firstFactorBlocks V n]

/-- Schur–Weyl duality for every degree and every finite-dimensional complex
vector space, including the zero space and all zero multiplicity summands. -/
theorem schurWeylDuality : Specs.AdvancedFiniteGroupRepresentations.schurWeylDualityType.{u} := by
  intro V _ _ _ n
  refine ⟨tensorEvaluation_isomorphism V n, ?_, ?_, secondCentralizer V n⟩
  · intro p hp
    letI := hp
    exact tensorMultiplicity_irreducible V p
  · intro p q hp hq hpq
    letI := hp
    letI := hq
    exact tensorMultiplicity_nonisomorphic V p q hpq

end AdvancedFiniteGroupRepresentations
