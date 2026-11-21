import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Basis

open Filter Topology
open scoped BigOperators

noncomputable section

universe u v
namespace ExpandedFA.P1.C15Basis

variable {𝕜 : Type u} {E : Type v} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- The independently specified canonical objects are reused definitionally.
abbrev orderedPartialSum := @Spec.orderedPartialSum
abbrev IsRawSchauderBasis := @Spec.IsRawSchauderBasis
noncomputable abbrev rawCoordinates := @Spec.rawCoordinates
abbrev rawPartialSum := @Spec.rawPartialSum
abbrev finiteSynthesis := @Spec.finiteSynthesis
abbrev IsRawFiniteBasis := @Spec.IsRawFiniteBasis
noncomputable abbrev finiteCoordinates := @Spec.finiteCoordinates
abbrev finitePartialSum := @Spec.finitePartialSum
abbrev emptyFamily := @Spec.emptyFamily

variable {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e)

/-- Choice gives exactly the expansion in the definition. -/
theorem rawCoordinates_tendsto (x : E) :
    Tendsto (orderedPartialSum e (rawCoordinates h x)) atTop (𝓝 x) :=
  Classical.choose_spec (h.2 x).exists

/-- Any convergent expansion has the chosen coefficients. -/
theorem rawCoordinates_unique (x : E) (a : ℕ → 𝕜)
    (ha : Tendsto (orderedPartialSum e a) atTop (𝓝 x)) : a = rawCoordinates h x :=
  (h.2 x).unique ha (rawCoordinates_tendsto h x)

private theorem orderedPartialSum_add (a b : ℕ → 𝕜) (N : ℕ) :
    orderedPartialSum e (fun i => a i + b i) N =
      orderedPartialSum e a N + orderedPartialSum e b N := by
  simp only [orderedPartialSum, Spec.orderedPartialSum, add_smul, Finset.sum_add_distrib]

private theorem orderedPartialSum_smul (c : 𝕜) (a : ℕ → 𝕜) (N : ℕ) :
    orderedPartialSum e (fun i => c * a i) N = c • orderedPartialSum e a N := by
  simp only [orderedPartialSum, Spec.orderedPartialSum, mul_smul, Finset.smul_sum]

/-- Linearity follows from uniqueness and addition of the convergent expansions. -/
theorem rawCoordinates_add (x y : E) :
    rawCoordinates h (x + y) = fun i => rawCoordinates h x i + rawCoordinates h y i := by
  symm
  apply rawCoordinates_unique h
  change Tendsto (fun N => orderedPartialSum e
    (fun i => rawCoordinates h x i + rawCoordinates h y i) N) atTop (𝓝 (x + y))
  simpa only [orderedPartialSum_add] using
    (rawCoordinates_tendsto h x).add (rawCoordinates_tendsto h y)

theorem rawCoordinates_smul (c : 𝕜) (x : E) :
    rawCoordinates h (c • x) = fun i => c * rawCoordinates h x i := by
  symm
  apply rawCoordinates_unique h
  change Tendsto (fun N => orderedPartialSum e
    (fun i => c * rawCoordinates h x i) N) atTop (𝓝 (c • x))
  simpa only [orderedPartialSum_smul] using (rawCoordinates_tendsto h x).const_smul c

/-- The coordinate functional is only an algebraic linear map. -/
noncomputable def rawCoordinateLinearMap (i : ℕ) : E →ₗ[𝕜] 𝕜 where
  toFun x := rawCoordinates h x i
  map_add' x y := congrFun (rawCoordinates_add h x y) i
  map_smul' c x := congrFun (rawCoordinates_smul h c x) i

/-- Truncation is also constructed without a continuity assumption. -/
noncomputable def rawPartialSumLinearMap (N : ℕ) : E →ₗ[𝕜] E where
  toFun := rawPartialSum h N
  map_add' x y := by
    change orderedPartialSum e (rawCoordinates h (x + y)) N = _
    rw [rawCoordinates_add, orderedPartialSum_add]
    rfl
  map_smul' c x := by
    change orderedPartialSum e (rawCoordinates h (c • x)) N = _
    rw [rawCoordinates_smul, orderedPartialSum_smul]
    rfl

theorem rawCoordinateLinearMap_apply (i : ℕ) (x : E) :
    rawCoordinateLinearMap h i x = rawCoordinates h x i := rfl

theorem rawPartialSumLinearMap_apply (N : ℕ) (x : E) :
    rawPartialSumLinearMap h N x = rawPartialSum h N x := rfl

theorem rawPartialSum_zero (x : E) : rawPartialSum h 0 x = 0 := by
  simp [rawPartialSum, Spec.rawPartialSum, Spec.orderedPartialSum]

theorem rawPartialSum_tendsto (x : E) :
    Tendsto (fun N => rawPartialSum h N x) atTop (𝓝 x) := rawCoordinates_tendsto h x

section Finite
variable {d : ℕ} {f : Fin d → E} (hf : IsRawFiniteBasis (𝕜 := 𝕜) f)

theorem finiteCoordinates_expansion (x : E) :
    finiteSynthesis f (finiteCoordinates hf x) = x := Classical.choose_spec (hf.2 x).exists

theorem finiteCoordinates_unique (x : E) (a : Fin d → 𝕜)
    (ha : finiteSynthesis f a = x) : a = finiteCoordinates hf x :=
  (hf.2 x).unique ha (finiteCoordinates_expansion hf x)

theorem finiteCoordinates_add (x y : E) :
    finiteCoordinates hf (x + y) =
      fun i => finiteCoordinates hf x i + finiteCoordinates hf y i := by
  symm
  apply finiteCoordinates_unique hf
  simp only [finiteSynthesis, Spec.finiteSynthesis, add_smul, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) (finiteCoordinates_expansion hf x) (finiteCoordinates_expansion hf y)

theorem finiteCoordinates_smul (c : 𝕜) (x : E) :
    finiteCoordinates hf (c • x) = fun i => c * finiteCoordinates hf x i := by
  symm
  apply finiteCoordinates_unique hf
  simp only [finiteSynthesis, Spec.finiteSynthesis, mul_smul, ← Finset.smul_sum]
  exact congrArg (c • ·) (finiteCoordinates_expansion hf x)

noncomputable def finiteCoordinateLinearMap (i : Fin d) : E →ₗ[𝕜] 𝕜 where
  toFun x := finiteCoordinates hf x i
  map_add' x y := congrFun (finiteCoordinates_add hf x y) i
  map_smul' c x := congrFun (finiteCoordinates_smul hf c x) i

noncomputable def finitePartialSumLinearMap (N : ℕ) : E →ₗ[𝕜] E where
  toFun := finitePartialSum hf N
  map_add' x y := by
    simp only [finitePartialSum, Spec.finitePartialSum,
      finiteCoordinates_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [finitePartialSum, Spec.finitePartialSum,
      finiteCoordinates_smul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem finiteCoordinateLinearMap_apply (i : Fin d) (x : E) :
    finiteCoordinateLinearMap hf i x = finiteCoordinates hf x i := rfl

theorem finitePartialSumLinearMap_apply (N : ℕ) (x : E) :
    finitePartialSumLinearMap hf N x = finitePartialSum hf N x := rfl

theorem finitePartialSum_zero (x : E) : finitePartialSum hf 0 x = 0 := by
  simp [finitePartialSum, Spec.finitePartialSum]

theorem finitePartialSum_of_le (N : ℕ) (hN : d ≤ N) (x : E) :
    finitePartialSum hf N x = x := by
  have hfilter : Finset.univ.filter (fun i : Fin d => i.val < N) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact lt_of_lt_of_le i.isLt hN
  change (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < N),
    finiteCoordinates hf x i • f i) = x
  rw [hfilter]
  exact finiteCoordinates_expansion hf x

end Finite

/-- The empty list is a basis of every zero space, including its unique expansion. -/
theorem emptyFamily_isRawFiniteBasis [Subsingleton E] :
    IsRawFiniteBasis (𝕜 := 𝕜) (emptyFamily (E := E)) := by
  constructor
  · intro i
    exact Fin.elim0 i
  · intro x
    refine ⟨(fun i => Fin.elim0 i), ?_, ?_⟩
    · exact Subsingleton.elim _ _
    · intro a _
      exact Subsingleton.elim _ _

/-- Conversely the empty expansion property forces E to be the zero space. -/
theorem subsingleton_of_emptyFamily_basis
    (hf : IsRawFiniteBasis (𝕜 := 𝕜) (emptyFamily (E := E))) : Subsingleton E := by
  have hz (x : E) : x = 0 := by
    have hx := finiteCoordinates_expansion hf x
    simpa [finiteSynthesis, Spec.finiteSynthesis] using hx.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem emptyPartialSum_eq_zero
    (hf : IsRawFiniteBasis (𝕜 := 𝕜) (emptyFamily (E := E))) (N : ℕ) (x : E) :
    finitePartialSum hf N x = 0 := by
  simp [finitePartialSum, Spec.finitePartialSum]

/-- Explicit construction of all infinite coordinate and truncation linear maps. -/
theorem rawLinearMaps_exist {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e) :
    (∀ i : ℕ, ∃ L : E →ₗ[𝕜] 𝕜, ∀ x, L x = rawCoordinates h x i) ∧
    (∀ N : ℕ, ∃ P : E →ₗ[𝕜] E, ∀ x, P x = rawPartialSum h N x) := by
  exact ⟨fun i => ⟨rawCoordinateLinearMap h i, fun _ => rfl⟩,
    fun N => ⟨rawPartialSumLinearMap h N, fun _ => rfl⟩⟩

/-- The same construction for finite lists, including the empty list. -/
theorem finiteLinearMaps_exist {d : ℕ} {f : Fin d → E}
    (hf : IsRawFiniteBasis (𝕜 := 𝕜) f) :
    (∀ i : Fin d, ∃ L : E →ₗ[𝕜] 𝕜, ∀ x, L x = finiteCoordinates hf x i) ∧
    (∀ N : ℕ, ∃ P : E →ₗ[𝕜] E, ∀ x, P x = finitePartialSum hf N x) := by
  exact ⟨fun i => ⟨finiteCoordinateLinearMap hf i, fun _ => rfl⟩,
    fun N => ⟨finitePartialSumLinearMap hf N, fun _ => rfl⟩⟩

end ExpandedFA.P1.C15Basis
