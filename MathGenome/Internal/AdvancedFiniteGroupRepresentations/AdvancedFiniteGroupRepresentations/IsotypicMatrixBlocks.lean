import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.TensorEvaluation
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.IsotypicMatrixBlocks
import Mathlib.RepresentationTheory.Equiv
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct DirectSum BigOperators MonoidAlgebra
universe u
namespace AdvancedFiniteGroupRepresentations

abbrev spechtFamilyAlgebraMap := @Specs.AdvancedFiniteGroupRepresentations.spechtFamilyAlgebraMap
abbrev ActivePartition := @Specs.AdvancedFiniteGroupRepresentations.ActivePartition
abbrev ActsOnFirstFactors := @Specs.AdvancedFiniteGroupRepresentations.ActsOnFirstFactors
abbrev ActsOnSecondFactors := @Specs.AdvancedFiniteGroupRepresentations.ActsOnSecondFactors
abbrev firstFactorBlocks := @Specs.AdvancedFiniteGroupRepresentations.firstFactorBlocks
abbrev secondFactorBlocks := @Specs.AdvancedFiniteGroupRepresentations.secondFactorBlocks

/-- An intertwiner commutes with the entire group-algebra action. -/
theorem intertwining_algebra_action {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (τ : Representation ℂ G Y)
    (f : Representation.IntertwiningMap ρ τ) (a : ℂ[G]) (v : X) :
    f (ρ.asAlgebraHom a v) = τ.asAlgebraHom a (f v) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g c =>
    simp [Representation.asAlgebraHom_def, MonoidAlgebra.lift_single,
      Representation.IntertwiningMap.isIntertwining]

/-- Swapping the two arguments leaves the dimension of intertwining maps
unchanged for finite groups over ℂ. -/
theorem intertwining_finrank_symm {G X Y : Type*} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (ρ : Representation ℂ G X) (τ : Representation ℂ G Y) :
    Module.finrank ℂ (Representation.IntertwiningMap ρ τ) =
      Module.finrank ℂ (Representation.IntertwiningMap τ ρ) := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have he : (∑ g : G, τ.character g * ρ.character g⁻¹) =
      ∑ g : G, ρ.character g * τ.character g⁻¹ := by
    rw [← (Equiv.sum_comp (Equiv.inv G) (fun g => τ.character g * ρ.character g⁻¹))]
    simp [mul_comm]
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ τ
  rw [he, Representation.card_inv_mul_sum_char_mul_char_eq_finrank τ ρ] at h
  exact_mod_cast h.symm

/-- The regular multiplicity of each actual Specht module is its dimension. -/
theorem specht_regular_multiplicity {n : ℕ} (p : Partition n) :
    Module.finrank ℂ (Representation.IntertwiningMap (canonicalSpechtRepresentation p)
      (Representation.leftRegular ℂ (SymmetricGroup n))) =
    Module.finrank ℂ (SpechtModule p) := by
  rw [intertwining_finrank_symm]
  exact (Representation.leftRegularMapEquiv (canonicalSpechtRepresentation p)).finrank_eq

/-- The regular module gives the sum-of-squares dimension identity. -/
theorem specht_sum_dimension_squared (n : ℕ) :
    (∑ p : Partition n, Module.finrank ℂ (SpechtModule p) *
      Module.finrank ℂ (SpechtModule p)) = Module.finrank ℂ (GroupAlgebra n) := by
  simpa only [specht_regular_multiplicity] using
    specht_multiplicity_dimension (GroupAlgebra n) (Representation.leftRegular ℂ (SymmetricGroup n))

/-- An element annihilating every Specht module annihilates the regular module. -/
theorem canonicalSpechtFamilyAlgebraMap_injective (n : ℕ) :
    Function.Injective (spechtFamilyAlgebraMap (n := n) canonicalSpechtRepresentation) := by
  change Function.Injective (spechtFamilyAlgebraMap (n := n) canonicalSpechtRepresentation).toLinearMap
  apply (@LinearMap.ker_eq_bot ℂ ℂ (GroupAlgebra n)
    (∀ p : Partition n, Module.End ℂ (SpechtModule p)) _ _ _ _ _ _ (RingHom.id ℂ)
    (spechtFamilyAlgebraMap (n := n) canonicalSpechtRepresentation).toLinearMap).mp
  apply bot_unique
  intro a ha
  have hz (p : Partition n) : (canonicalSpechtRepresentation p).asAlgebraHom a = 0 :=
    congrFun ha p
  let ρ := Representation.leftRegular ℂ (SymmetricGroup n)
  have hspan : LinearMap.ker (ρ.asAlgebraHom a) = ⊤ := by
    apply specht_images_span (GroupAlgebra n) ρ
    intro p f v
    change ρ.asAlgebraHom a (f v) = 0
    rw [← intertwining_algebra_action, hz]
    simp
  have he : ρ.asAlgebraHom a (1 : GroupAlgebra n) = 0 := by
    exact (LinearMap.mem_ker.mp (hspan ▸ Submodule.mem_top))
  simpa [ρ] using he

/-- The actual action map onto the product of full Specht endomorphism algebras. -/
theorem spechtFamilyAlgebraMap_bijective {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (hσ : ∀ p, InheritedSpechtAction p (σ p)) :
    Function.Bijective (spechtFamilyAlgebraMap σ) := by
  have he : σ = canonicalSpechtRepresentation := by
    funext p
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact hσ p g v
  subst σ
  have hd : Module.finrank ℂ (GroupAlgebra n) =
      Module.finrank ℂ (∀ p : Partition n, Module.End ℂ (SpechtModule p)) := by
    rw [Module.finrank_pi_fintype]
    simp_rw [Module.finrank_linearMap]
    exact (specht_sum_dimension_squared n).symm
  refine ⟨canonicalSpechtFamilyAlgebraMap_injective n, ?_⟩
  change Function.Surjective (spechtFamilyAlgebraMap (n := n) canonicalSpechtRepresentation).toLinearMap
  exact (@LinearMap.injective_iff_surjective_of_finrank_eq_finrank ℂ (GroupAlgebra n) _ _ _
    (∀ p : Partition n, Module.End ℂ (SpechtModule p)) _ _ _ _ hd
    (spechtFamilyAlgebraMap (n := n) canonicalSpechtRepresentation).toLinearMap).mp
      (canonicalSpechtFamilyAlgebraMap_injective n)

theorem spechtFamilyAlgebra_isomorphism {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (hσ : ∀ p, InheritedSpechtAction p (σ p)) :
    ∃ e : GroupAlgebra n ≃ₐ[ℂ] ∀ p : Partition n, Module.End ℂ (SpechtModule p),
      e.toAlgHom = spechtFamilyAlgebraMap σ :=
  ⟨AlgEquiv.ofBijective (spechtFamilyAlgebraMap σ) (spechtFamilyAlgebraMap_bijective σ hσ), rfl⟩

/-- Contract the first tensor factor against a linear functional. -/
def tensorContractLeft {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (φ : Module.Dual ℂ X) : X ⊗[ℂ] Y →ₗ[ℂ] Y :=
  (TensorProduct.lid ℂ Y).toLinearMap.comp (TensorProduct.map φ 1)

@[simp] theorem tensorContractLeft_pure {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : Module.Dual ℂ X) (x : X) (y : Y) :
    tensorContractLeft φ (x ⊗ₜ[ℂ] y) = φ x • y := by
  simp [tensorContractLeft]

/-- Rank-one matrices on the first factor are tensor contraction followed by insertion. -/
theorem tensor_rankOne_left {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : Module.Dual ℂ X) (x : X) (z : X ⊗[ℂ] Y) :
    TensorProduct.map (φ.smulRight x) (1 : Module.End ℂ Y) z =
      x ⊗ₜ[ℂ] tensorContractLeft φ z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add a b ha hb => simp [ha, hb, TensorProduct.tmul_add]

/-- The matrix-unit bridge for the first factor.  Rank-one operators already
force a commuting operator to act only on the second factor. -/
theorem tensor_firstFactor_centralizer {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    [AddCommGroup Y] [Module ℂ Y] (T : Module.End ℂ (X ⊗[ℂ] Y))
    (hT : ∀ a : Module.End ℂ X,
      Commute (TensorProduct.map a (1 : Module.End ℂ Y)) T) :
    ∃ b : Module.End ℂ Y, T = TensorProduct.map (1 : Module.End ℂ X) b := by
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hx₀
  let b := (tensorContractLeft φ).comp (T.comp (TensorProduct.mk ℂ X Y x₀))
  refine ⟨b, ?_⟩
  apply TensorProduct.ext
  ext x y
  change T (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] b y
  let a := φ.smulRight x
  calc
    T (x ⊗ₜ[ℂ] y) = T (TensorProduct.map a 1 (x₀ ⊗ₜ[ℂ] y)) := by
      simp [a, hφ]
    _ = TensorProduct.map a 1 (T (x₀ ⊗ₜ[ℂ] y)) :=
      (DFunLike.congr_fun (hT a).eq (x₀ ⊗ₜ[ℂ] y)).symm
    _ = x ⊗ₜ[ℂ] b y := tensor_rankOne_left φ x _

/-- Contract the second tensor factor. -/
def tensorContractRight {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (φ : Module.Dual ℂ Y) : X ⊗[ℂ] Y →ₗ[ℂ] X :=
  (TensorProduct.rid ℂ X).toLinearMap.comp (TensorProduct.map 1 φ)

@[simp] theorem tensorContractRight_pure {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : Module.Dual ℂ Y) (x : X) (y : Y) :
    tensorContractRight φ (x ⊗ₜ[ℂ] y) = φ y • x := by
  simp [tensorContractRight]

theorem tensor_rankOne_right {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : Module.Dual ℂ Y) (y : Y) (z : X ⊗[ℂ] Y) :
    TensorProduct.map (1 : Module.End ℂ X) (φ.smulRight y) z =
      tensorContractRight φ z ⊗ₜ[ℂ] y := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add a b ha hb => simp [ha, hb, TensorProduct.add_tmul]

/-- The matrix-unit bridge in the opposite direction, on nonzero second factors. -/
theorem tensor_secondFactor_centralizer {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [Nontrivial Y] (T : Module.End ℂ (X ⊗[ℂ] Y))
    (hT : ∀ b : Module.End ℂ Y,
      Commute (TensorProduct.map (1 : Module.End ℂ X) b) T) :
    ∃ a : Module.End ℂ X, T = TensorProduct.map a (1 : Module.End ℂ Y) := by
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : Y)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hy₀
  let a := (tensorContractRight φ).comp
    (T.comp ((TensorProduct.mk ℂ X Y).flip y₀))
  refine ⟨a, ?_⟩
  apply TensorProduct.ext
  ext x y
  change T (x ⊗ₜ[ℂ] y) = a x ⊗ₜ[ℂ] y
  let b := φ.smulRight y
  calc
    T (x ⊗ₜ[ℂ] y) = T (TensorProduct.map 1 b (x ⊗ₜ[ℂ] y₀)) := by
      simp [b, hφ]
    _ = TensorProduct.map 1 b (T (x ⊗ₜ[ℂ] y₀)) :=
      (DFunLike.congr_fun (hT b).eq (x ⊗ₜ[ℂ] y₀)).symm
    _ = a x ⊗ₜ[ℂ] y := tensor_rankOne_right φ y _

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- Evaluation vectors determine an endomorphism, including for the zero space. -/
theorem tensorEvaluation_end_ext [FiniteDimensional ℂ V] {n : ℕ}
    {T U : Module.End ℂ (TensorPower V n)}
    (h : ∀ (p : Partition n) (v : SpechtModule p) (f : TensorMultiplicity V p),
      T (f.val v) = U (f.val v)) : T = U := by
  have he : T.comp (tensorEvaluationMap V n) = U.comp (tensorEvaluationMap V n) := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext
    ext v f
    change T (tensorEvaluationMap V n (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f))) =
      U (tensorEvaluationMap V n (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f)))
    simpa only [tensorEvaluationMap_pure] using h p v f
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := tensorEvaluationMap_surjective V n x
  exact DFunLike.congr_fun he y

/-- Omitted summands have identically zero evaluation. -/
theorem inactive_evaluation {n : ℕ} (p : Partition n)
    (h : ¬ Nontrivial (TensorMultiplicity V p)) (f : TensorMultiplicity V p)
    (v : SpechtModule p) : f.val v = 0 := by
  have : Subsingleton (TensorMultiplicity V p) := not_nontrivial_iff_subsingleton.mp h
  have hf : f = 0 := Subsingleton.elim _ _
  rw [hf]
  rfl

/-- A full first-factor family on the canonical evaluation direct sum. -/
def firstFactorOperator {n : ℕ}
    (F : ∀ p : Partition n, Module.End ℂ (SpechtModule p)) :
    Module.End ℂ (TensorEvaluationSum V n) :=
  DirectSum.lmap (fun p => TensorProduct.map (F p) (1 : Module.End ℂ (TensorMultiplicity V p)))

/-- A full second-factor family on the same direct sum. -/
def secondFactorOperator {n : ℕ}
    (F : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p)) :
    Module.End ℂ (TensorEvaluationSum V n) :=
  DirectSum.lmap (fun p => TensorProduct.map (1 : Module.End ℂ (SpechtModule p)) (F p))

theorem firstFactorOperator_pure {n : ℕ}
    (F : ∀ p : Partition n, Module.End ℂ (SpechtModule p))
    (p : Partition n) (v : SpechtModule p) (f : TensorMultiplicity V p) :
    firstFactorOperator V F (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f)) =
      DirectSum.lof ℂ _ _ p (F p v ⊗ₜ[ℂ] f) := by
  simp [firstFactorOperator]

theorem secondFactorOperator_pure {n : ℕ}
    (F : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p))
    (p : Partition n) (v : SpechtModule p) (f : TensorMultiplicity V p) :
    secondFactorOperator V F (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f)) =
      DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] F p f) := by
  simp [secondFactorOperator]

/-- Every independent first-factor family has a unique transported operator. -/
theorem firstFactorBlocks_realize [FiniteDimensional ℂ V] (n : ℕ)
    (F : ∀ p : ActivePartition V n, Module.End ℂ (SpechtModule p.val)) :
    ∃! T : Module.End ℂ (TensorPower V n), ActsOnFirstFactors V F T := by
  classical
  let F' : ∀ p : Partition n, Module.End ℂ (SpechtModule p) :=
    fun p => if h : Nontrivial (TensorMultiplicity V p) then F ⟨p, h⟩ else 0
  let e := tensorEvaluationEquiv V n
  let T := e.conj (firstFactorOperator V F')
  have hT : ActsOnFirstFactors V F T := by
    intro p v f
    change e (firstFactorOperator V F' (e.symm (f.val v))) = _
    rw [← tensorEvaluationEquiv_pure V p v f, e.symm_apply_apply,
      firstFactorOperator_pure, tensorEvaluationEquiv_pure]
    dsimp [F']
    split
    · rfl
    · simp
  refine ⟨T, hT, ?_⟩
  intro U hU
  apply tensorEvaluation_end_ext V
  intro p v f
  exact (hU p v f).trans (hT p v f).symm

/-- Every independent second-factor family has a unique transported operator. -/
theorem secondFactorBlocks_realize [FiniteDimensional ℂ V] (n : ℕ)
    (F : ∀ p : ActivePartition V n, Module.End ℂ (TensorMultiplicity V p.val)) :
    ∃! T : Module.End ℂ (TensorPower V n), ActsOnSecondFactors V F T := by
  classical
  let F' : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p) :=
    fun p => if h : Nontrivial (TensorMultiplicity V p) then F ⟨p, h⟩ else 0
  let e := tensorEvaluationEquiv V n
  let T := e.conj (secondFactorOperator V F')
  have hT : ActsOnSecondFactors V F T := by
    intro p v f
    change e (secondFactorOperator V F' (e.symm (f.val v))) = _
    rw [← tensorEvaluationEquiv_pure V p v f, e.symm_apply_apply,
      secondFactorOperator_pure, tensorEvaluationEquiv_pure]
    dsimp [F']
    split
    · rfl
    · rfl
  refine ⟨T, hT, ?_⟩
  intro U hU
  apply tensorEvaluation_end_ext V
  intro p v f
  exact (hU p v f).trans (hT p v f).symm

/-- The slot action on an evaluation vector is the Specht action on its input. -/
theorem slotAlgebraMap_evaluation {n : ℕ} (a : GroupAlgebra n)
    (p : Partition n) (v : SpechtModule p) (f : TensorMultiplicity V p) :
    slotAlgebraMap V n a (f.val v) =
      f.val ((canonicalSpechtRepresentation p).asAlgebraHom a v) := by
  exact (intertwining_algebra_action (canonicalSpechtRepresentation p)
    (slotRepresentation V n) (tensorMultiplicityEquivIntertwining V p f) a v).symm

/-- The image A is exactly all independent first-factor blocks. -/
theorem tensorA_eq_firstFactorBlocks [FiniteDimensional ℂ V] (n : ℕ) :
    tensorA V n = firstFactorBlocks V n := by
  classical
  rw [← slotAlgebraMap_range V n]
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    refine ⟨fun p => (canonicalSpechtRepresentation p.val).asAlgebraHom a, ?_⟩
    intro p v f
    change slotAlgebraMap V n a (f.val v) = _
    rw [slotAlgebraMap_evaluation]
    dsimp
    split
    · rfl
    · next h => exact inactive_evaluation V p h f _
  · rintro T ⟨F, hF⟩
    let F' : ∀ p : Partition n, Module.End ℂ (SpechtModule p) :=
      fun p => if h : Nontrivial (TensorMultiplicity V p) then F ⟨p, h⟩ else 0
    obtain ⟨a, ha⟩ := (spechtFamilyAlgebraMap_bijective
      (n := n) canonicalSpechtRepresentation (fun _ _ _ => rfl)).surjective F'
    refine ⟨a, ?_⟩
    apply tensorEvaluation_end_ext V
    intro p v f
    change slotAlgebraMap V n a (f.val v) = T (f.val v)
    rw [slotAlgebraMap_evaluation, hF]
    have hap : (canonicalSpechtRepresentation p).asAlgebraHom a = F' p := congrFun ha p
    rw [hap]
    dsimp [F']
    split
    · rfl
    · simp

/-- First and second factors commute on all evaluation vectors. -/
theorem factorBlocks_commute [FiniteDimensional ℂ V] {n : ℕ}
    (T U : Module.End ℂ (TensorPower V n))
    (hT : T ∈ firstFactorBlocks V n) (hU : U ∈ secondFactorBlocks V n) :
    Commute T U := by
  classical
  obtain ⟨F, hF⟩ := hT
  obtain ⟨G, hG⟩ := hU
  apply tensorEvaluation_end_ext V
  intro p v f
  change T (U (f.val v)) = U (T (f.val v))
  rw [hF, hG]
  by_cases h : Nontrivial (TensorMultiplicity V p)
  · simp only [dite_eq_left h]
    rw [hF, hG]
  · simp [h]

/-- Transport a full second-factor family along the canonical evaluation equivalence. -/
def secondFactorTransport [FiniteDimensional ℂ V] {n : ℕ}
    (F : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p)) :
    Module.End ℂ (TensorPower V n) :=
  (tensorEvaluationEquiv V n).conj (secondFactorOperator V F)

@[simp] theorem secondFactorTransport_evaluation [FiniteDimensional ℂ V] {n : ℕ}
    (F : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p))
    (p : Partition n) (v : SpechtModule p) (f : TensorMultiplicity V p) :
    secondFactorTransport V F (f.val v) = (F p f).val v := by
  change tensorEvaluationEquiv V n (secondFactorOperator V F
    ((tensorEvaluationEquiv V n).symm (f.val v))) = _
  rw [← tensorEvaluationEquiv_pure V p v f,
    LinearEquiv.symm_apply_apply, secondFactorOperator_pure, tensorEvaluationEquiv_pure]

theorem secondFactorTransport_mem [FiniteDimensional ℂ V] {n : ℕ}
    (F : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p)) :
    secondFactorTransport V F ∈ secondFactorBlocks V n := by
  classical
  refine ⟨fun p => F p.val, ?_⟩
  intro p v f
  rw [secondFactorTransport_evaluation]
  dsimp
  split
  · rfl
  · next h => exact inactive_evaluation V p h (F p f) v

/-- Inclusion and projection of a canonical evaluation summand. -/
def evaluationInclusion [FiniteDimensional ℂ V] {n : ℕ} (p : Partition n) :
    SpechtModule p ⊗[ℂ] TensorMultiplicity V p →ₗ[ℂ] TensorPower V n :=
  (tensorEvaluationEquiv V n).toLinearMap.comp (DirectSum.lof ℂ (Partition n)
    (fun q => SpechtModule q ⊗[ℂ] TensorMultiplicity V q) p)

def evaluationProjection [FiniteDimensional ℂ V] {n : ℕ} (p : Partition n) :
    TensorPower V n →ₗ[ℂ] SpechtModule p ⊗[ℂ] TensorMultiplicity V p :=
  (DirectSum.component ℂ (Partition n)
    (fun q => SpechtModule q ⊗[ℂ] TensorMultiplicity V q) p).comp
      (tensorEvaluationEquiv V n).symm.toLinearMap

@[simp] theorem evaluationInclusion_pure [FiniteDimensional ℂ V] {n : ℕ}
    (p : Partition n) (v : SpechtModule p) (f : TensorMultiplicity V p) :
    evaluationInclusion V p (v ⊗ₜ[ℂ] f) = f.val v := tensorEvaluationEquiv_pure V p v f

@[simp] theorem evaluationProjection_inclusion [FiniteDimensional ℂ V] {n : ℕ}
    (p : Partition n) (z : SpechtModule p ⊗[ℂ] TensorMultiplicity V p) :
    evaluationProjection V p (evaluationInclusion V p z) = z := by
  simp [evaluationProjection, evaluationInclusion]

theorem evaluationInclusion_injective [FiniteDimensional ℂ V] {n : ℕ}
    (p : Partition n) : Function.Injective (evaluationInclusion V p) := by
  intro x y h
  have he := congrArg (evaluationProjection V p) h
  simpa using he

/-- The actual projector onto an isotypic summand, transported by evaluation. -/
def isotypicProjector [FiniteDimensional ℂ V] {n : ℕ} (p : Partition n) :
    Module.End ℂ (TensorPower V n) :=
  (evaluationInclusion V p).comp (evaluationProjection V p)

@[simp] theorem isotypicProjector_evaluation [FiniteDimensional ℂ V] {n : ℕ}
    (p q : Partition n) (v : SpechtModule q) (f : TensorMultiplicity V q) :
    isotypicProjector V p (f.val v) = if q = p then f.val v else 0 := by
  classical
  rw [← tensorEvaluationEquiv_pure V q v f]
  simp only [isotypicProjector, evaluationProjection, evaluationInclusion,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    DirectSum.component.of]
  split
  · next h => subst q; rfl
  · simp

theorem isotypicProjector_mem_first [FiniteDimensional ℂ V] {n : ℕ} (p : Partition n) :
    isotypicProjector V p ∈ firstFactorBlocks V n := by
  classical
  refine ⟨fun q => if q.val = p then 1 else 0, ?_⟩
  intro q v f
  rw [isotypicProjector_evaluation]
  dsimp
  by_cases h : Nontrivial (TensorMultiplicity V q)
  · simp only [dite_eq_left h]
    by_cases hqp : q = p <;> simp [hqp]
  · simp [h, inactive_evaluation V q h f v]

theorem isotypicProjector_mem_second [FiniteDimensional ℂ V] {n : ℕ} (p : Partition n) :
    isotypicProjector V p ∈ secondFactorBlocks V n := by
  classical
  refine ⟨fun q => if q.val = p then 1 else 0, ?_⟩
  intro q v f
  rw [isotypicProjector_evaluation]
  dsimp
  by_cases h : Nontrivial (TensorMultiplicity V q)
  · simp only [dite_eq_left h]
    by_cases hqp : q = p <;> simp [hqp]
  · simp [h, inactive_evaluation V q h f v]

theorem isotypicProjector_idempotent [FiniteDimensional ℂ V] {n : ℕ} (p : Partition n) :
    isotypicProjector V p * isotypicProjector V p = isotypicProjector V p := by
  apply LinearMap.ext
  intro z
  change evaluationInclusion V p
    (evaluationProjection V p (evaluationInclusion V p (evaluationProjection V p z))) = _
  rw [evaluationProjection_inclusion]
  rfl

/-- The first centralizer acts on each Hom space by postcomposition. -/
theorem firstFactorBlocks_centralizer [FiniteDimensional ℂ V] (n : ℕ) :
    Subalgebra.centralizer ℂ (firstFactorBlocks V n : Set _) = secondFactorBlocks V n := by
  classical
  apply le_antisymm
  · intro T hT
    have hc (s : SymmetricGroup n) : Commute (slotOperator V n s) T := by
      apply hT
      rw [← tensorA_eq_firstFactorBlocks V n]
      exact Algebra.subset_adjoin ⟨s, rfl⟩
    let F (p : Partition n) : Module.End ℂ (TensorMultiplicity V p) :=
      { toFun f := ⟨T.comp f.val, by
          intro s v w hw
          change T (f.val w) = slotOperator V n s (T (f.val v))
          rw [f.property s v w hw]
          exact (DFunLike.congr_fun (hc s).eq (f.val v)).symm⟩
        map_add' := by intros; apply Subtype.ext; ext v; exact map_add T _ _
        map_smul' := by intros; apply Subtype.ext; ext v; exact map_smul T _ _ }
    refine ⟨fun p => F p.val, ?_⟩
    intro p v f
    dsimp
    split
    · rfl
    · next h => simp [inactive_evaluation V p h f v]
  · intro T hT U hU
    exact factorBlocks_commute V U T hU hT

/-- The diagonal restriction of an operator to an evaluation summand. -/
def evaluationBlock [FiniteDimensional ℂ V] {n : ℕ}
    (T : Module.End ℂ (TensorPower V n)) (p : Partition n) :
    Module.End ℂ (SpechtModule p ⊗[ℂ] TensorMultiplicity V p) :=
  (evaluationProjection V p).comp (T.comp (evaluationInclusion V p))

/-- Commutation with the isotypic projector forces preservation of its summand. -/
theorem evaluationBlock_preserved [FiniteDimensional ℂ V] {n : ℕ}
    (T : Module.End ℂ (TensorPower V n)) (p : Partition n)
    (hT : Commute (isotypicProjector V p) T)
    (z : SpechtModule p ⊗[ℂ] TensorMultiplicity V p) :
    T (evaluationInclusion V p z) = evaluationInclusion V p (evaluationBlock V T p z) := by
  have h := DFunLike.congr_fun hT.eq (evaluationInclusion V p z)
  change evaluationInclusion V p (evaluationBlock V T p z) =
    T (evaluationInclusion V p (evaluationProjection V p (evaluationInclusion V p z))) at h
  rw [evaluationProjection_inclusion] at h
  exact h.symm

theorem secondFactorTransport_inclusion [FiniteDimensional ℂ V] {n : ℕ}
    (F : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p)) (p : Partition n)
    (z : SpechtModule p ⊗[ℂ] TensorMultiplicity V p) :
    secondFactorTransport V F (evaluationInclusion V p z) =
      evaluationInclusion V p (TensorProduct.map 1 (F p) z) := by
  have he : (secondFactorTransport V F).comp (evaluationInclusion V p) =
      (evaluationInclusion V p).comp (TensorProduct.map 1 (F p)) := by
    apply TensorProduct.ext
    ext v f
    change secondFactorTransport V F (evaluationInclusion V p (v ⊗ₜ[ℂ] f)) =
      evaluationInclusion V p (TensorProduct.map 1 (F p) (v ⊗ₜ[ℂ] f))
    simp
  exact DFunLike.congr_fun he z

theorem evaluationProjection_secondFactorTransport [FiniteDimensional ℂ V] {n : ℕ}
    (F : ∀ p : Partition n, Module.End ℂ (TensorMultiplicity V p)) (p : Partition n)
    (z : TensorPower V n) :
    evaluationProjection V p (secondFactorTransport V F z) =
      TensorProduct.map 1 (F p) (evaluationProjection V p z) := by
  change DirectSum.component ℂ (Partition n)
    (fun q => SpechtModule q ⊗[ℂ] TensorMultiplicity V q) p
      ((tensorEvaluationEquiv V n).symm
        (tensorEvaluationEquiv V n (secondFactorOperator V F ((tensorEvaluationEquiv V n).symm z)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Restriction of a commuting operator commutes with every second-factor matrix. -/
theorem evaluationBlock_commute_second [FiniteDimensional ℂ V] {n : ℕ}
    (T : Module.End ℂ (TensorPower V n))
    (hT : T ∈ Subalgebra.centralizer ℂ (secondFactorBlocks V n : Set _))
    (p : Partition n) (b : Module.End ℂ (TensorMultiplicity V p)) :
    Commute (TensorProduct.map (1 : Module.End ℂ (SpechtModule p)) b)
      (evaluationBlock V T p) := by
  classical
  let F : ∀ q : Partition n, Module.End ℂ (TensorMultiplicity V q) := Function.update 0 p b
  have hFp : F p = b := by simp [F]
  have hc := hT (secondFactorTransport V F) (secondFactorTransport_mem V F)
  apply LinearMap.ext
  intro z
  change TensorProduct.map 1 b (evaluationProjection V p (T (evaluationInclusion V p z))) =
    evaluationProjection V p (T (evaluationInclusion V p (TensorProduct.map 1 b z)))
  rw [← hFp, ← evaluationProjection_secondFactorTransport]
  have hc' := DFunLike.congr_fun hc (evaluationInclusion V p z)
  change secondFactorTransport V F (T (evaluationInclusion V p z)) =
    T (secondFactorTransport V F (evaluationInclusion V p z)) at hc'
  rw [hc', secondFactorTransport_inclusion]

/-- The second-factor blocks have precisely A as their centralizer. -/
theorem secondFactorBlocks_centralizer [FiniteDimensional ℂ V] (n : ℕ) :
    Subalgebra.centralizer ℂ (secondFactorBlocks V n : Set _) = tensorA V n := by
  classical
  rw [tensorA_eq_firstFactorBlocks V n]
  apply le_antisymm
  · intro T hT
    have hex (p : ActivePartition V n) : ∃ a : Module.End ℂ (SpechtModule p.val),
        evaluationBlock V T p.val = TensorProduct.map a (1 : Module.End ℂ (TensorMultiplicity V p.val)) := by
      have : Nontrivial (TensorMultiplicity V p.val) := p.property
      exact tensor_secondFactor_centralizer (evaluationBlock V T p.val)
        (evaluationBlock_commute_second V T hT p.val)
    choose F hF using hex
    refine ⟨F, ?_⟩
    intro p v f
    by_cases h : Nontrivial (TensorMultiplicity V p)
    · simp only [dite_eq_left h]
      have hc := hT (isotypicProjector V p) (isotypicProjector_mem_second V p)
      rw [← evaluationInclusion_pure V p v f,
        evaluationBlock_preserved V T p hc, hF ⟨p, h⟩]
      simp
    · simp [h, inactive_evaluation V p h f v]
  · intro T hT U hU
    exact (factorBlocks_commute V T U hT hU).symm

/-- The projectors are orthogonal, not merely invariant block operators. -/
theorem isotypicProjector_mul [FiniteDimensional ℂ V] {n : ℕ} (p q : Partition n) :
    isotypicProjector V p * isotypicProjector V q = if p = q then isotypicProjector V p else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simpa using isotypicProjector_idempotent V p
  · simp only [ite_eq_right hpq]
    apply tensorEvaluation_end_ext V
    intro r v f
    change isotypicProjector V p (isotypicProjector V q (f.val v)) = 0
    rw [isotypicProjector_evaluation]
    by_cases hrq : r = q
    · subst r
      simp [Ne.symm hpq]
    · simp [hrq]

theorem isotypicProjector_sum [FiniteDimensional ℂ V] (n : ℕ) :
    (∑ p : Partition n, isotypicProjector V p) = 1 := by
  classical
  apply tensorEvaluation_end_ext V
  intro q v f
  simp only [LinearMap.sum_apply, isotypicProjector_evaluation, Module.End.one_apply]
  simp

theorem isotypicProjector_zero_of_inactive [FiniteDimensional ℂ V] {n : ℕ}
    (p : Partition n) (hp : ¬ Nontrivial (TensorMultiplicity V p)) :
    isotypicProjector V p = 0 := by
  classical
  apply tensorEvaluation_end_ext V
  intro q v f
  rw [isotypicProjector_evaluation]
  by_cases hqp : q = p
  · subst q
    simp [inactive_evaluation V p hp f v]
  · simp [hqp]

/-- A complete family of concrete block projectors in both block algebras. -/
theorem isotypicProjectors [FiniteDimensional ℂ V] (n : ℕ) :
    ∃ P : Partition n → Module.End ℂ (TensorPower V n),
      (∀ p, P p ∈ firstFactorBlocks V n ∧ P p ∈ secondFactorBlocks V n) ∧
      (∀ (p q : Partition n) (v : SpechtModule q) (f : TensorMultiplicity V q),
        P p (f.val v) = if q = p then f.val v else 0) ∧
      (∀ p q, P p * P q = if p = q then P p else 0) ∧
      (∑ p, P p) = 1 ∧
      (∀ p, ¬ Nontrivial (TensorMultiplicity V p) → P p = 0) := by
  classical
  exact ⟨isotypicProjector V, fun p => ⟨isotypicProjector_mem_first V p,
    isotypicProjector_mem_second V p⟩, isotypicProjector_evaluation V,
    isotypicProjector_mul V, isotypicProjector_sum V n, isotypicProjector_zero_of_inactive V⟩

end AdvancedFiniteGroupRepresentations
