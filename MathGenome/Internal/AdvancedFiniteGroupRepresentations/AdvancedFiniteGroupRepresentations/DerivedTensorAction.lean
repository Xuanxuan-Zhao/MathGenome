import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.TensorEvaluation
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.DerivedTensorAction

noncomputable section
open scoped BigOperators
attribute [local instance] LieRing.ofAssociativeRing
universe u
namespace AdvancedFiniteGroupRepresentations
abbrev tensorSlotInsertion := @Specs.AdvancedFiniteGroupRepresentations.tensorSlotInsertion
abbrev derivedTensorOperator := @Specs.AdvancedFiniteGroupRepresentations.derivedTensorOperator
variable (V : Type u) [AddCommGroup V] [Module ℂ V]

@[simp] theorem tensorSlotInsertion_eq_map (n : ℕ) (i : Fin n) (T : Module.End ℂ V) :
    tensorSlotInsertion V n i T =
      PiTensorProduct.map (Function.update (fun _ : Fin n => (1 : Module.End ℂ V)) i T) := rfl

@[simp] theorem tensorSlotInsertion_pure (n : ℕ) (i : Fin n) (T : Module.End ℂ V)
    (v : Fin n → V) :
    tensorSlotInsertion V n i T (pureTensor V n v) =
      pureTensor V n (Function.update v i (T (v i))) := by
  rw [tensorSlotInsertion_eq_map]
  change (PiTensorProduct.map _) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ _
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]

theorem derivedTensorOperator_eq_sum (n : ℕ) (T : Module.End ℂ V) :
    derivedTensorOperator V n T = ∑ i : Fin n, tensorSlotInsertion V n i T := by
  simp [derivedTensorOperator, Specs.AdvancedFiniteGroupRepresentations.derivedTensorOperator]

@[simp] theorem derivedTensorOperator_pure (n : ℕ) (T : Module.End ℂ V)
    (v : Fin n → V) :
    derivedTensorOperator V n T (pureTensor V n v) =
      ∑ i : Fin n, pureTensor V n (Function.update v i (T (v i))) := by
  simp only [derivedTensorOperator_eq_sum, LinearMap.sum_apply, tensorSlotInsertion_pure]

@[simp] theorem tensorSlotInsertion_mul (n : ℕ) (i : Fin n) (T U : Module.End ℂ V) :
    tensorSlotInsertion V n i (T * U) =
      tensorSlotInsertion V n i T * tensorSlotInsertion V n i U := by
  simp only [tensorSlotInsertion_eq_map, ← PiTensorProduct.map_mul]
  congr 1
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]

theorem tensorSlotInsertion_commute (n : ℕ) (i j : Fin n) (h : i ≠ j)
    (T U : Module.End ℂ V) :
    Commute (tensorSlotInsertion V n i T) (tensorSlotInsertion V n j U) := by
  change _ * _ = _ * _
  simp only [tensorSlotInsertion_eq_map, ← PiTensorProduct.map_mul]
  congr 1
  funext k
  by_cases hi : k = i
  · subst k; simp [Function.update_of_ne h]
  · by_cases hj : k = j
    · subst k; simp [Function.update_of_ne h.symm]
    · simp [Function.update_of_ne hi, Function.update_of_ne hj]

theorem derivedTensorOperator_lie (n : ℕ) (T U : Module.End ℂ V) :
    derivedTensorOperator V n ⁅T, U⁆ =
      ⁅derivedTensorOperator V n T, derivedTensorOperator V n U⁆ := by
  rw [derivedTensorOperator_eq_sum, derivedTensorOperator_eq_sum,
    derivedTensorOperator_eq_sum, sum_lie_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [Ring.lie_def, map_sub, tensorSlotInsertion_mul]
  · intro j _ hji
    exact (tensorSlotInsertion_commute V n i j hji.symm T U).lie_eq
  · simp

/-- Relabeling moves a one-position operator to the relabeled position. -/
theorem slot_tensorSlotInsertion (n : ℕ) (s : SymmetricGroup n) (i : Fin n)
    (T : Module.End ℂ V) :
    slotOperator V n s * tensorSlotInsertion V n i T =
      tensorSlotInsertion V n (s i) T * slotOperator V n s := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change slotOperator V n s (tensorSlotInsertion V n i T (pureTensor V n v)) =
    tensorSlotInsertion V n (s i) T (slotOperator V n s (pureTensor V n v))
  rw [tensorSlotInsertion_pure, slot_pureTensor, slot_pureTensor, tensorSlotInsertion_pure]
  congr 1
  funext j
  by_cases h : j = s i
  · subst j
    change Function.update v i (T (v i)) (s.symm (s i)) =
      Function.update (fun k => v (s.symm k)) (s i) (T (v (s.symm (s i)))) (s i)
    simp only [Equiv.symm_apply_apply, Function.update_self]
    exact congrArg (fun k => T (v k)) (s.symm_apply_apply i).symm
  · have hi : s.symm j ≠ i := by
      intro he
      apply h
      calc
        j = s (s.symm j) := (s.apply_symm_apply j).symm
        _ = s i := congrArg s he
    simp [Function.update_of_ne h, Function.update_of_ne hi]

theorem derivedTensorOperator_commute (n : ℕ) (T : Module.End ℂ V)
    (s : SymmetricGroup n) :
    Commute (slotOperator V n s) (derivedTensorOperator V n T) := by
  change _ * _ = _ * _
  simp only [derivedTensorOperator_eq_sum, Finset.mul_sum, Finset.sum_mul,
    slot_tensorSlotInsertion]
  exact Fintype.sum_equiv s _ _ (fun i => rfl)

/-- The Lie representation on the tensor power. -/
def derivedTensorLieHom (n : ℕ) :
    Module.End ℂ V →ₗ⁅ℂ⁆ Module.End ℂ (TensorPower V n) :=
  { derivedTensorOperator V n with map_lie' := derivedTensorOperator_lie V n _ _ }

/-- All endomorphisms that commute with the slot representation. -/
def tensorSlotCentralizer (n : ℕ) : Subalgebra ℂ (Module.End ℂ (TensorPower V n)) :=
  Subalgebra.centralizer ℂ (Set.range (slotOperator V n))

/-- The derived representation takes its values in the slot centralizer. -/
def derivedTensorCentralizerLieHom (n : ℕ) :
    Module.End ℂ V →ₗ⁅ℂ⁆ tensorSlotCentralizer V n where
  toFun T := ⟨derivedTensorOperator V n T, by
    rintro _ ⟨s, rfl⟩
    exact derivedTensorOperator_commute V n T s⟩
  map_add' T U := Subtype.ext (map_add (derivedTensorOperator V n) T U)
  map_smul' a T := Subtype.ext (map_smul (derivedTensorOperator V n) a T)
  map_lie' := by
    intro T U
    apply Subtype.ext
    exact derivedTensorOperator_lie V n T U

/-- Unital extension, initially valued in the centralizer algebra. -/
def derivedTensorCentralizerEnveloping (n : ℕ) :
    UniversalEnvelopingAlgebra ℂ (Module.End ℂ V) →ₐ[ℂ] tensorSlotCentralizer V n :=
  UniversalEnvelopingAlgebra.lift ℂ (derivedTensorCentralizerLieHom V n)

/-- The actual unital algebra map from U(gl(V)) to End(V^{⊗n}). -/
def derivedTensorEnveloping (n : ℕ) :
    UniversalEnvelopingAlgebra ℂ (Module.End ℂ V) →ₐ[ℂ]
      Module.End ℂ (TensorPower V n) :=
  (tensorSlotCentralizer V n).val.comp (derivedTensorCentralizerEnveloping V n)

@[simp] theorem derivedTensorEnveloping_ι (n : ℕ) (T : Module.End ℂ V) :
    derivedTensorEnveloping V n (UniversalEnvelopingAlgebra.ι ℂ T) =
      derivedTensorOperator V n T := by
  change (derivedTensorCentralizerEnveloping V n
    (UniversalEnvelopingAlgebra.ι ℂ T)).val = _
  rw [derivedTensorCentralizerEnveloping, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

theorem derivedTensorEnveloping_commute (n : ℕ) (s : SymmetricGroup n)
    (a : UniversalEnvelopingAlgebra ℂ (Module.End ℂ V)) :
    Commute (slotOperator V n s) (derivedTensorEnveloping V n a) :=
  (derivedTensorCentralizerEnveloping V n a).property _ ⟨s, rfl⟩

/-- Postcomposition by any element of the slot centralizer acts on the
original equivariant Hom space, preserving its equivariance condition. -/
def tensorMultiplicityCentralizerAction {n : ℕ} (p : Partition n) :
    tensorSlotCentralizer V n →ₐ[ℂ] Module.End ℂ (TensorMultiplicity V p) where
  toFun a :=
    { toFun := fun f => ⟨a.val.comp f.val, by
        intro s v w hw
        change a.val (f.val w) = _
        rw [f.property s v w hw]
        exact congrArg (fun F : Module.End ℂ (TensorPower V n) => F (f.val v))
          (a.property _ ⟨s, rfl⟩).symm⟩
      map_add' := by
        intro f h
        apply Subtype.ext
        ext v
        exact map_add a.val _ _
      map_smul' := by
        intro c f
        apply Subtype.ext
        ext v
        exact map_smul a.val _ _ }
  map_one' := by ext f v; rfl
  map_mul' a b := by ext f v; rfl
  map_zero' := by ext f v; rfl
  map_add' a b := by ext f v; rfl
  commutes' c := by ext f v; rfl

/-- The induced Lie action on L_p(V). -/
def derivedTensorMultiplicityLieHom {n : ℕ} (p : Partition n) :
    Module.End ℂ V →ₗ⁅ℂ⁆ Module.End ℂ (TensorMultiplicity V p) :=
  (tensorMultiplicityCentralizerAction V p).toLieHom.comp
    (derivedTensorCentralizerLieHom V n)

/-- The induced unital enveloping-algebra action on L_p(V). -/
def derivedTensorMultiplicityEnveloping {n : ℕ} (p : Partition n) :
    UniversalEnvelopingAlgebra ℂ (Module.End ℂ V) →ₐ[ℂ]
      Module.End ℂ (TensorMultiplicity V p) :=
  (tensorMultiplicityCentralizerAction V p).comp (derivedTensorCentralizerEnveloping V n)

@[simp] theorem derivedTensorMultiplicityEnveloping_ι {n : ℕ} (p : Partition n)
    (T : Module.End ℂ V) :
    derivedTensorMultiplicityEnveloping V p (UniversalEnvelopingAlgebra.ι ℂ T) =
      derivedTensorMultiplicityLieHom V p T := by
  change tensorMultiplicityCentralizerAction V p
    (derivedTensorCentralizerEnveloping V n (UniversalEnvelopingAlgebra.ι ℂ T)) = _
  rw [derivedTensorCentralizerEnveloping, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

theorem derivedTensorMultiplicityLieHom_apply {n : ℕ} (p : Partition n)
    (T : Module.End ℂ V) (f : TensorMultiplicity V p) (v : SpechtModule p) :
    (derivedTensorMultiplicityLieHom V p T f).val v =
      derivedTensorOperator V n T (f.val v) := rfl

theorem derivedTensorMultiplicityEnveloping_apply {n : ℕ} (p : Partition n)
    (a : UniversalEnvelopingAlgebra ℂ (Module.End ℂ V))
    (f : TensorMultiplicity V p) (v : SpechtModule p) :
    (derivedTensorMultiplicityEnveloping V p a f).val v =
      derivedTensorEnveloping V n a (f.val v) := rfl

/-- The full construction, with no stability or extension hypotheses. -/
theorem derivedTensorAction_exists (n : ℕ) :
    ∃ ρ : Module.End ℂ V →ₗ⁅ℂ⁆ Module.End ℂ (TensorPower V n),
      (∀ T, ρ T = derivedTensorOperator V n T) ∧
      ∃ Φ : UniversalEnvelopingAlgebra ℂ (Module.End ℂ V) →ₐ[ℂ]
          Module.End ℂ (TensorPower V n),
        (∀ T, Φ (UniversalEnvelopingAlgebra.ι ℂ T) = derivedTensorOperator V n T) ∧
        (∀ s a, Commute (slotOperator V n s) (Φ a)) ∧
        ∀ p : Partition n,
          ∃ τ : Module.End ℂ V →ₗ⁅ℂ⁆ Module.End ℂ (TensorMultiplicity V p),
          ∃ Ψ : UniversalEnvelopingAlgebra ℂ (Module.End ℂ V) →ₐ[ℂ]
              Module.End ℂ (TensorMultiplicity V p),
            (∀ T, Ψ (UniversalEnvelopingAlgebra.ι ℂ T) = τ T) ∧
            (∀ T (f : TensorMultiplicity V p) v,
              (τ T f).val v = derivedTensorOperator V n T (f.val v)) ∧
            (∀ a (f : TensorMultiplicity V p) v, (Ψ a f).val v = Φ a (f.val v)) := by
  refine ⟨derivedTensorLieHom V n, fun _ => rfl, derivedTensorEnveloping V n,
    derivedTensorEnveloping_ι V n, derivedTensorEnveloping_commute V n, ?_⟩
  intro p
  exact ⟨derivedTensorMultiplicityLieHom V p, derivedTensorMultiplicityEnveloping V p,
    derivedTensorMultiplicityEnveloping_ι V p,
    derivedTensorMultiplicityLieHom_apply V p, derivedTensorMultiplicityEnveloping_apply V p⟩

@[simp] theorem derivedTensorOperator_zero : derivedTensorOperator V 0 = 0 := by
  simp [derivedTensorOperator, Specs.AdvancedFiniteGroupRepresentations.derivedTensorOperator]

theorem derivedTensor_zero_scalar_image
    (Φ : UniversalEnvelopingAlgebra ℂ (Module.End ℂ V) →ₐ[ℂ]
      Module.End ℂ (TensorPower V 0)) : Φ.range = ⊥ := by
  apply le_antisymm _ bot_le
  rintro F ⟨a, rfl⟩
  apply Algebra.mem_bot.mpr
  let e := tensorPowerZeroEquiv V
  let x := e.symm 1
  refine ⟨e (Φ a x), ?_⟩
  apply LinearMap.ext
  intro y
  have hy : y = e y • x := by
    apply e.injective
    simp [x]
  change e (Φ a x) • y = Φ a y
  rw [hy, map_smul]
  apply e.injective
  simp [x, smul_smul, mul_comm]

end AdvancedFiniteGroupRepresentations
