import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Density.Action
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Density.FiniteRankModule

/-! The module and commutant of the scalar-plus-finite-rank algebra. -/

universe u v

namespace RM03.Density.FiniteRankModule

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

/-- The two-sided ideal of endomorphisms with finite-dimensional range. -/
abbrev finiteRankIdeal : TwoSidedIdeal (Module.End k V) :=
  Specs.Density.FiniteRankModule.finiteRankIdealValue k V

@[simp]
theorem mem_finiteRankIdeal (f : Module.End k V) :
    f ∈ finiteRankIdeal k V ↔ FiniteDimensional k f.range := by
  unfold finiteRankIdeal Specs.Density.FiniteRankModule.finiteRankIdealValue
  rw [TwoSidedIdeal.mem_mk']
  change f.range.FG ↔ Module.Finite k f.range
  exact Module.Finite.iff_fg.symm

/-- The unital algebra of scalar maps plus finite-rank maps. -/
abbrev scalarPlusFiniteRank : Subalgebra k (Module.End k V) :=
  Specs.Density.FiniteRankModule.scalarPlusFiniteRankValue k V

theorem mem_scalarPlusFiniteRank (T : Module.End k V) :
    T ∈ scalarPlusFiniteRank k V ↔
      ∃ c : k, ∃ f ∈ finiteRankIdeal k V, T = algebraMap k (Module.End k V) c + f :=
  Iff.rfl

/-- The action is the restriction of the natural evaluation action. -/
abbrev evaluationModule : Module (scalarPlusFiniteRank k V) V :=
  Specs.Density.FiniteRankModule.evaluationModuleValue k V

local notation "R" => scalarPlusFiniteRank k V

@[simp]
theorem evaluation_smul (r : R) (x : V) : r • x = (r : Module.End k V) x :=
  rfl

/-- Endomorphisms agreeing on every vector are equal. -/
theorem faithful : FaithfulSMul R V :=
  ⟨fun h ↦ Subtype.ext (LinearMap.ext h)⟩

/-- The operator sending a vector to its `i`th coordinate times `w`. -/
private noncomputable def coordinateOperator (b : Module.Basis ℕ k V) (i : ℕ) (w : V) : R := by
  let f : Module.End k V := (LinearMap.toSpanSingleton k V w).comp (b.coord i)
  have hf : f.HasFiniteRange :=
    (LinearMap.HasFiniteRange.of_finite_dom (f := LinearMap.toSpanSingleton k V w)).comp_right _
  exact ⟨f, (mem_scalarPlusFiniteRank k V f).2
    ⟨0, f, (mem_finiteRankIdeal k V f).2 (Module.Finite.of_fg hf.fg_range), by simp⟩⟩

private theorem coordinateOperator_apply (b : Module.Basis ℕ k V) (i : ℕ) (w x : V) :
    (coordinateOperator k V b i w : Module.End k V) x = b.coord i x • w :=
  rfl

/-- Each nonzero vector generates the module using rank-one operators. -/
theorem simple (b : Module.Basis ℕ k V) : IsSimpleModule R V := by
  have : Nontrivial V := ⟨⟨b 0, 0, b.ne_zero 0⟩⟩
  refine isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨inferInstance, ?_⟩
  intro x hx w
  obtain ⟨i, hi⟩ : ∃ i, b.coord i x ≠ 0 := by
    by_contra! h
    exact hx (b.forall_coord_eq_zero_iff.1 h)
  refine ⟨coordinateOperator k V b i ((b.coord i x)⁻¹ • w), ?_⟩
  change (coordinateOperator k V b i ((b.coord i x)⁻¹ • w) : Module.End k V) x = w
  rw [coordinateOperator_apply, smul_smul, mul_inv_cancel₀ hi, one_smul]

/-- Commuting with the coordinate operators out of the first basis vector forces scalar action. -/
private theorem eq_smul_of_commutes (b : Module.Basis ℕ k V) (T : V → V)
    (h : ∀ (r : R) (x : V), T ((r : Module.End k V) x) = (r : Module.End k V) (T x))
    (w : V) : T w = b.coord 0 (T (b 0)) • w := by
  simpa only [coordinateOperator_apply, Module.Basis.coord_apply, b.repr_self, Finsupp.single_eq_same, one_smul] using
    h (coordinateOperator k V b 0 w) (b 0)

/-- The centralizer in the ambient endomorphism algebra consists of the scalar maps. -/
theorem commutant (b : Module.Basis ℕ k V) (T : Module.End k V) :
    (∀ r : R, Commute T (r : Module.End k V)) ↔
      ∃ c : k, T = algebraMap k (Module.End k V) c := by
  constructor
  · intro h
    refine ⟨b.coord 0 (T (b 0)), LinearMap.ext (eq_smul_of_commutes k V b T ?_)⟩
    exact fun r x ↦ LinearMap.congr_fun (h r).eq x
  · rintro ⟨c, rfl⟩ r
    exact Algebra.commutes c (r : Module.End k V)

/-- The canonical scalar map onto the (R)-linear endomorphisms, with the original (k)-action. -/
noncomputable def commutantEquiv (b : Module.Basis ℕ k V) : k ≃ₐ[k] Module.End R V := by
  refine AlgEquiv.ofBijective (Algebra.ofId k (Module.End R V)) ⟨?_, ?_⟩
  · intro c d h
    have h' : c • b 0 = d • b 0 := LinearMap.congr_fun h (b 0)
    simpa only [map_smul, Module.Basis.coord_apply, b.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] using congrArg (b.coord 0) h'
  · intro T
    refine ⟨b.coord 0 (T (b 0)), LinearMap.ext (fun x ↦ ?_)⟩
    exact (eq_smul_of_commutes k V b T (fun r x ↦ T.map_smul r x) x).symm

@[simp]
theorem commutantEquiv_apply (b : Module.Basis ℕ k V) (c : k) (x : V) :
    commutantEquiv k V b c x = c • x :=
  rfl

theorem commutantEquiv_exists (b : Module.Basis ℕ k V) :
    ∃ e : k ≃ₐ[k] Module.End R V, (∀ (c : k) (x : V), e c x = c • x) ∧
      (∀ (c : k) (x : V), rightSMul R x (MulOpposite.op (e c)) = c • x) :=
  ⟨commutantEquiv k V b, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- A right-linear endomorphism for the commutant action is exactly a (k)-linear map. -/
noncomputable def rightEndEquiv (b : Module.Basis ℕ k V) :
    RightEnd R V ≃ₐ[k] Module.End k V where
  toFun T := T.restrictScalars k
  invFun T :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun d x ↦ by
        obtain ⟨c, rfl⟩ := (commutantEquiv k V b).surjective d
        exact T.map_smul c x }
  left_inv T := LinearMap.ext fun _ ↦ rfl
  right_inv T := LinearMap.ext fun _ ↦ rfl
  map_mul' _ _ := LinearMap.ext fun _ ↦ rfl
  map_add' _ _ := LinearMap.ext fun _ ↦ rfl
  commutes' _ := LinearMap.ext fun _ ↦ rfl

@[simp]
theorem rightEndEquiv_apply (b : Module.Basis ℕ k V) (T : RightEnd R V) (x : V) :
    rightEndEquiv k V b T x = T x :=
  rfl

@[simp]
theorem rightEndEquiv_action (b : Module.Basis ℕ k V) (r : R) :
    rightEndEquiv k V b (action R V r) = (r : Module.End k V) :=
  LinearMap.ext fun _ ↦ rfl

theorem rightEndEquiv_exists (b : Module.Basis ℕ k V) :
    ∃ e : RightEnd R V ≃ₐ[k] Module.End k V,
      (∀ (T : RightEnd R V) (x : V), e T x = T x) ∧
      (∀ r : R, e (action R V r) = (r : Module.End k V)) :=
  ⟨rightEndEquiv k V b, rightEndEquiv_apply k V b, rightEndEquiv_action k V b⟩

end RM03.Density.FiniteRankModule
