import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SplittingSystem
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SplitMatrixColumns
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Jacobson.Semiprimary

/-! Simple left columns for ordinary and modular split group algebras. -/

namespace RepTheorySurvey.Modular

open scoped Matrix Matrix.Module

universe uF uA uG uV

section
variable {F : Type uF} [Field F] {A : Type uA} [Ring A] [Algebra F A]
  {r : ℕ} {d : Fin r → ℕ}

@[inherit_doc SplitMatrixColumnsSpec.columnModule]
noncomputable abbrev columnModule
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (i : Fin r) :
    ModuleCat.{uF} A :=
  SplitMatrixColumnsSpec.columnModule q i

@[inherit_doc SplitMatrixColumnsSpec.columnAction]
noncomputable abbrev columnAction
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (i : Fin r) :
    A →ₐ[F] Module.End F (Fin (d i) → F) :=
  SplitMatrixColumnsSpec.columnAction q i

variable (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F))

theorem columnAction_apply (i : Fin r) (a : A) (v : columnModule q i) :
    columnAction q i a v = a • v := rfl

theorem column_lsmul (i : Fin r) (a : A) :
    (columnAction q i a : Module.End F (columnModule q i)) =
      Algebra.lsmul F F (columnModule q i) a :=
  LinearMap.ext (columnAction_apply q i a)

theorem column_finrank (i : Fin r) : Module.finrank F (columnModule q i) = d i := by
  change Module.finrank F (Fin (d i) → F) = d i
  simp

theorem columnAction_surjective (hq : Function.Surjective q) (i : Fin r) :
    Function.Surjective (columnAction q i) := by
  classical
  have hEval : Function.Surjective
      (Pi.evalAlgHom F (fun j : Fin r => Matrix (Fin (d j)) (Fin (d j)) F) i) :=
    fun m => ⟨Pi.single i m, by simp⟩
  exact Matrix.toLinAlgEquiv'.surjective.comp (hEval.comp hq)

private theorem column_simple (hd : ∀ i, 0 < d i) (hq : Function.Surjective q)
    (i : Fin r) : IsSimpleModule A (columnModule q i) := by
  let : Nonempty (Fin (d i)) := ⟨⟨0, hd i⟩⟩
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstanceAs (Nontrivial (Fin (d i) → F)), ?_⟩
  intro v hv w
  obtain ⟨s, hs⟩ : ∃ s : Fin (d i), v s ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨a, ha⟩ := columnAction_surjective q hq i
    ((LinearMap.proj s : (Fin (d i) → F) →ₗ[F] F).smulRight ((v s)⁻¹ • w))
  refine ⟨a, ?_⟩
  change a • v = w
  have he : (columnAction q i a v : columnModule q i) = v s • ((v s)⁻¹ • w) :=
    DFunLike.congr_fun ha v
  have hw : v s • ((v s)⁻¹ • w) = w := by
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
  exact (columnAction_apply q i a v).symm.trans (he.trans hw)

private theorem column_eq_of_iso (hd : ∀ i, 0 < d i) (hq : Function.Surjective q)
    {i j : Fin r} (e : columnModule q i ≃ₗ[A] columnModule q j) : i = j := by
  classical
  by_contra h
  obtain ⟨a, ha⟩ := hq (Pi.single i 1)
  have hi : q a i = 1 := by simp [ha]
  have hj : q a j = 0 := by simp [ha, Ne.symm h]
  let v : columnModule q i := Pi.single (⟨0, hd i⟩ : Fin (d i)) 1
  have hv : v ≠ 0 := by
    intro hv
    have he : v ⟨0, hd i⟩ = (0 : F) := congrFun hv ⟨0, hd i⟩
    simp [v] at he
  have hv' : a • v = v := by
    change (q a i) *ᵥ (v : Fin (d i) → F) = (v : Fin (d i) → F)
    rw [hi, Matrix.one_mulVec]
  have hz : a • e v = 0 := by
    change (q a j) *ᵥ (e v : Fin (d j) → F) = (0 : Fin (d j) → F)
    rw [hj]
    exact Matrix.zero_mulVec (e v : Fin (d j) → F)
  have he := (congrArg e hv').symm.trans ((e.map_smul a v).trans hz)
  exact hv (e.injective (he.trans e.map_zero.symm))

/-- Every simple module is a column of the split quotient, in any universe. -/
theorem column_exhaustive (hd : ∀ i, 0 < d i) (hq : Function.Surjective q)
    (hker : RingHom.ker q.toRingHom ≤ Ring.jacobson A)
    (M : ModuleCat.{uV} A) (hM : IsSimpleModule A M) :
    ∃ i, Nonempty (M ≃ₗ[A] columnModule q i) := by
  classical
  let B := (i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F
  let : Module A B := Module.compHom B q.toRingHom
  let qLinear : A →ₗ[A] B := Module.compHom.toLinearMap q.toRingHom
  let := hM
  have := IsSimpleModule.nontrivial A M
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  let g : A →ₗ[A] M := LinearMap.toSpanSingleton A M x
  have hg : Function.Surjective g :=
    (isSimpleModule_iff_toSpanSingleton_surjective.mp hM).2 _ hx
  -- A cyclic surjection onto the simple module descends to the split quotient.
  have hle : LinearMap.ker qLinear ≤ LinearMap.ker g := by
    intro a ha
    have hann := IsSemisimpleModule.jacobson_le_annihilator A M
    exact LinearMap.mem_ker.mpr (Module.mem_annihilator.mp (hann (hker ha)) x)
  let f : B →ₗ[A] M := qLinear.liftOfSurjective hq ⟨g, hle⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := hg y
    exact ⟨q a, LinearMap.equivOfSurjective_apply hq hle⟩
  -- The regular module of the product is spanned by its individual columns.
  let insert (i : Fin r) (s : Fin (d i)) : columnModule q i →ₗ[A] B :=
    { toFun := fun v => Pi.single i (Matrix.of fun t j => if j = s then v t else 0)
      map_add' := by
        intro v w
        rw [← Pi.single_add]
        congr 1
        ext t j
        change (if j = s then (v + w) t else 0) = (if j = s then v t else 0) +
          (if j = s then w t else 0)
        change (if j = s then v t + w t else 0) = _
        by_cases h : j = s <;> simp [h]
      map_smul' := by
        intro a v
        change Pi.single i (Matrix.of fun t j => if j = s then ((q a i) *ᵥ v) t else 0) =
          q a * Pi.single i (Matrix.of fun t j => if j = s then v t else 0)
        funext k
        by_cases h : k = i
        · subst k
          simp only [Pi.mul_apply, Pi.single_eq_same]
          ext t j
          by_cases h : j = s <;> simp [h, Matrix.mul_apply, Matrix.mulVec, dotProduct]
        · simp [Pi.mul_apply, Pi.single_eq_of_ne h] }
  have hcol : ∃ i s, f.comp (insert i s) ≠ 0 := by
    by_contra! h
    obtain ⟨b, hb⟩ := hf x
    have hsum : (∑ i : Fin r, ∑ s : Fin (d i), insert i s ((b i).col s)) = b := by
      have hpart (i : Fin r) : (∑ s : Fin (d i), insert i s ((b i).col s)) =
          Pi.single i (b i) := by
        funext k
        change (∑ s : Fin (d i), (insert i s ((b i).col s) :
          (j : Fin r) → Matrix (Fin (d j)) (Fin (d j)) F)) k = (Pi.single i (b i) : B) k
        rw [Finset.sum_apply]
        by_cases h : k = i
        · subst k
          ext t j
          simp [insert, Matrix.sum_apply, Matrix.col_apply]
        · simp [insert, Pi.single_eq_of_ne h]
      simp_rw [hpart]
      exact Finset.univ_sum_single b
    apply hx
    rw [← hb, ← hsum, map_sum]
    simp only [map_sum]
    have hz (i : Fin r) (s : Fin (d i)) : f (insert i s ((b i).col s)) = 0 :=
      DFunLike.congr_fun (h i s) ((b i).col s)
    simp [hz]
  obtain ⟨i, s, h⟩ := hcol
  let := column_simple q hd hq i
  exact ⟨i, ⟨(LinearEquiv.ofBijective (f.comp (insert i s))
    (LinearMap.bijective_of_ne_zero h)).symm⟩⟩

/-- The columns give a complete, irredundant finite family of simple modules. -/
theorem column_family (hd : ∀ i, 0 < d i) (hq : Function.Surjective q)
    (hker : RingHom.ker q.toRingHom ≤ Ring.jacobson A) :
    IsSimpleRepresentativeFamily (columnModule q) where
  simple := column_simple q hd hq
  eq_of_iso := fun ⟨e⟩ => column_eq_of_iso q hd hq e
  exhaustive := column_exhaustive q hd hq hker

/-- The algebra map from the ground field to each column's endomorphism algebra is an isomorphism. -/
theorem columnScalar_bijective (hd : ∀ i, 0 < d i) (hq : Function.Surjective q)
    (i : Fin r) : Function.Bijective (algebraMap F (Module.End A (columnModule q i))) := by
  let s : Fin (d i) := ⟨0, hd i⟩
  let v : columnModule q i := Pi.single s 1
  refine ⟨?_, ?_⟩
  · intro c c' h
    have he := congrArg (fun f : Module.End A (columnModule q i) => f v s) h
    change (c • v) s = (c' • v) s at he
    have hs : v s = 1 := by simp [v]
    change c * v s = c' * v s at he
    simpa [hs] using he
  · intro f
    refine ⟨f v s, LinearMap.ext fun w => ?_⟩
    obtain ⟨a, ha⟩ := columnAction_surjective q hq i
      ((LinearMap.proj s : (Fin (d i) → F) →ₗ[F] F).smulRight w)
    have happ (z : columnModule q i) : a • z = z s • w := by
      rw [← columnAction_apply]
      exact DFunLike.congr_fun ha z
    have hv : a • v = w := by
      rw [happ]
      have hs : v s = 1 := by simp [v]
      rw [hs, one_smul]
    calc
      algebraMap F (Module.End A (columnModule q i)) (f v s) w = a • f v :=
        (happ (f v)).symm
      _ = f w := by rw [← f.map_smul, hv]

theorem column_rank (a : A) (i : Fin r) :
    Module.finrank F (LinearMap.range (columnAction q i a)) = (q a i).rank := rfl

theorem column_rank_one (a : A) (i : Fin r) (hi : (q a i).rank = 1)
    (hzero : ∀ j, j ≠ i → q a j = 0) (j : Fin r) :
    Module.finrank F (LinearMap.range (columnAction q j a)) = if j = i then 1 else 0 := by
  rw [column_rank]
  split
  · rename_i h
    subst j
    exact hi
  · rename_i h
    rw [hzero j h, Matrix.rank_zero]

theorem column_trace (a : A) (i : Fin r) :
    LinearMap.trace F (Fin (d i) → F) (columnAction q i a) = Matrix.trace (q a i) :=
  Matrix.trace_toLin'_eq (q a i)

/-- A lift of a diagonal matrix unit tests the trace on its own simple column. -/
theorem column_trace_test (hq : Function.Surjective q) (i : Fin r) (s : Fin (d i)) :
    ∃ a : A, q a = Pi.single i (Matrix.single s s 1) ∧
      ∀ j : Fin r, LinearMap.trace F (Fin (d j) → F) (columnAction q j a) =
        if j = i then 1 else 0 := by
  classical
  obtain ⟨a, ha⟩ := hq (Pi.single i (Matrix.single s s 1))
  refine ⟨a, ha, fun j => ?_⟩
  rw [column_trace, ha]
  by_cases h : j = i
  · subst j
    simp [Matrix.trace_single_eq_same]
  · simp [h]

end

section
variable {F : Type uF} [Field F] {G : Type uG} [Group G]
  {r : ℕ} {d : Fin r → ℕ}

/-- The split modular action map is the actual radical quotient map followed by the presentation. -/
noncomputable abbrev modularColumnMap
    (e : GroupAlgebraRadicalQuotient F G ≃ₐ[F]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) :=
  e.toAlgHom.comp (groupAlgebraRadicalQuotientMap F G)

theorem modularColumnMap_surjective
    (e : GroupAlgebraRadicalQuotient F G ≃ₐ[F]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) :
    Function.Surjective (modularColumnMap e) :=
  e.surjective.comp (Ideal.Quotient.mkₐ_surjective F _)

theorem modularColumnMap_ker
    (e : GroupAlgebraRadicalQuotient F G ≃ₐ[F]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) :
    RingHom.ker (modularColumnMap e).toRingHom = Ring.jacobson (MonoidAlgebra F G) := by
  rw [← Ideal.Quotient.mkₐ_ker F (Ring.jacobson (MonoidAlgebra F G))]
  ext a
  simp only [RingHom.mem_ker]
  exact map_eq_zero_iff e e.injective

theorem ordinary_column_family (hd : ∀ i, 0 < d i)
    (e : MonoidAlgebra F G ≃ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) :
    IsSimpleRepresentativeFamily (columnModule e.toAlgHom) :=
  column_family _ hd e.surjective (by
    intro a ha
    have hz : e a = 0 := RingHom.mem_ker.mp ha
    rw [(map_eq_zero_iff e e.injective).mp hz]
    exact (Ring.jacobson _).zero_mem)

theorem modular_column_family (hd : ∀ i, 0 < d i)
    (e : GroupAlgebraRadicalQuotient F G ≃ₐ[F]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) :
    IsSimpleRepresentativeFamily (columnModule (modularColumnMap e)) :=
  column_family _ hd (modularColumnMap_surjective e) (modularColumnMap_ker e).le

theorem ordinary_columns_exist (h : IsSplitMatrixAlgebra F (MonoidAlgebra F G)) :
    ∃ (n : ℕ) (m : Fin n → ℕ), (∀ i, 0 < m i) ∧
      ∃ e : MonoidAlgebra F G ≃ₐ[F] ((i : Fin n) → Matrix (Fin (m i)) (Fin (m i)) F),
        IsSimpleRepresentativeFamily (columnModule e.toAlgHom) := by
  obtain ⟨n, m, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hm, e, ordinary_column_family hm e⟩

theorem modular_columns_exist (h : IsSplitMatrixAlgebra F (GroupAlgebraRadicalQuotient F G)) :
    ∃ (n : ℕ) (m : Fin n → ℕ), (∀ i, 0 < m i) ∧
      ∃ e : GroupAlgebraRadicalQuotient F G ≃ₐ[F]
        ((i : Fin n) → Matrix (Fin (m i)) (Fin (m i)) F),
        IsSimpleRepresentativeFamily (columnModule (modularColumnMap e)) := by
  obtain ⟨n, m, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hm, e, modular_column_family hm e⟩

end
end RepTheorySurvey.Modular
