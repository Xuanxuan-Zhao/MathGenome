import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.Actions
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.FiniteType

open LinearAlgebraicGroups Polynomial
open scoped TensorProduct

universe u

namespace RepTheorySurvey.Invariants

noncomputable section

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
variable {H : HopfAlgebraCategory k}

private theorem tensor_range_mul {U W : Submodule k A}
    (x : U ⊗[k] H) (y : W ⊗[k] H) :
    U.subtype.rTensor H x * W.subtype.rTensor H y ∈
      LinearMap.range ((U * W).subtype.rTensor H) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ ih₁ ih₂ => simpa only [map_add, add_mul] using add_mem ih₁ ih₂
  | tmul a h =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ ih₁ ih₂ => simpa only [map_add, mul_add] using add_mem ih₁ ih₂
    | tmul b g =>
      exact ⟨(⟨(a : A) * b, Submodule.mul_mem_mul a.property b.property⟩ : U * W)
        ⊗ₜ[k] (h * g), by
          simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply,
            Algebra.TensorProduct.tmul_mul_tmul]⟩

private theorem stable_mul (ρ : RationalAlgebraAction H A) {U W : Submodule k A}
    (hU : ρ.toRightComodule.IsSubcomodule U) (hW : ρ.toRightComodule.IsSubcomodule W) :
    ρ.toRightComodule.IsSubcomodule (U * W) := by
  rintro ⟨a, ha⟩
  change ρ.coaction a ∈ LinearMap.range ((U * W).subtype.rTensor H)
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro x hx y hy
    obtain ⟨tx, htx⟩ := hU ⟨x, hx⟩
    obtain ⟨ty, hty⟩ := hW ⟨y, hy⟩
    change U.subtype.rTensor H tx = ρ.coaction x at htx
    change W.subtype.rTensor H ty = ρ.coaction y at hty
    rw [map_mul, ← htx, ← hty]
    exact tensor_range_mul tx ty
  · intro x y hx hy
    simpa only [map_add] using add_mem hx hy

private theorem stable_pow (ρ : RationalAlgebraAction H A) {V : Submodule k A}
    (hV : ρ.toRightComodule.IsSubcomodule V) (n : ℕ) :
    ρ.toRightComodule.IsSubcomodule (V ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    intro x
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp x.property
    refine ⟨x ⊗ₜ[k] (1 : H), ?_⟩
    change (x : A) ⊗ₜ[k] (1 : H) = ρ.coaction (x : A)
    rw [← hc, ρ.coaction.commutes]
    exact ((Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] H).commutes c)
  | succ n ih =>
    rw [pow_succ]
    exact stable_mul ρ ih hV

/-- Polynomials whose degree n coefficients lie in the nth power of V. -/
private def filteredRees (V : Submodule k A) : Subalgebra k A[X] where
  carrier := { p | ∀ n, p.coeff n ∈ V ^ n }
  zero_mem' n := by simp
  add_mem' hp hq n := by
    rw [coeff_add]
    exact add_mem (hp n) (hq n)
  one_mem' n := by
    rw [coeff_one]
    split_ifs with h
    · subst n
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    · exact zero_mem _
  mul_mem' hp hq n := by
    rw [coeff_mul]
    apply Submodule.sum_mem
    rintro ⟨i,j⟩ hij
    rw [← Finset.mem_antidiagonal.mp hij, pow_add]
    exact Submodule.mul_mem_mul (hp i) (hq j)
  algebraMap_mem' c n := by
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst n
      exact Submodule.mem_one.mpr ⟨c, rfl⟩
    · exact zero_mem _

private theorem monomial_mem_filteredRees (V : Submodule k A) {n : ℕ} {a : A}
    (ha : a ∈ V ^ n) : monomial n a ∈ filteredRees V := by
  intro i
  by_cases h : n = i
  · subst i
    simpa only [coeff_monomial_same] using ha
  · rw [coeff_monomial, ite_eq_right h]
    exact zero_mem _

private theorem filteredRees_eq_adjoin (V : Submodule k A) :
    filteredRees V = Algebra.adjoin k (Submodule.map ((monomial 1 : A →ₗ[A] A[X]).restrictScalars k) V : Set A[X]) := by
  let B := Algebra.adjoin k (Submodule.map ((monomial 1 : A →ₗ[A] A[X]).restrictScalars k) V : Set A[X])
  have monomial_mem {n : ℕ} {a : A} (ha : a ∈ V ^ n) : monomial n a ∈ B := by
    induction n generalizing a with
    | zero =>
      obtain ⟨c, rfl⟩ := Submodule.mem_one.mp (by simpa only [pow_zero] using ha)
      exact B.algebraMap_mem c
    | succ n ih =>
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha ?_ ?_
      · intro a ha b hb
        rw [← monomial_mul_monomial]
        exact B.mul_mem (ih ha) (Algebra.subset_adjoin (Submodule.mem_map_of_mem hb))
      · intro a b ha hb
        rw [map_add]
        exact B.add_mem ha hb
  apply le_antisymm
  · intro p hp
    rw [p.as_sum_support]
    exact B.sum_mem fun n _ ↦ monomial_mem (hp n)
  · apply Algebra.adjoin_le
    rintro _ ⟨a, ha, rfl⟩
    exact monomial_mem_filteredRees V (by simpa only [pow_one] using (show a ∈ V from ha))

private theorem finiteType_filteredRees (V : Submodule k A) [FiniteDimensional k V] :
    Algebra.FiniteType k (filteredRees V) := by
  rw [← Subalgebra.fg_iff_finiteType, filteredRees_eq_adjoin]
  have hV : V.FG := Module.Finite.iff_fg.mp inferInstance
  obtain ⟨s, hs⟩ := hV.map ((monomial 1 : A →ₗ[A] A[X]).restrictScalars k)
  exact ⟨s, by rw [← hs, Algebra.adjoin_span]⟩

private theorem exists_mem_pow (V : Submodule k A) (hV : (1 : A) ∈ V)
    (hgen : Algebra.adjoin k (V : Set A) = ⊤) (a : A) : ∃ n : ℕ, a ∈ V ^ n := by
  have hstep (n : ℕ) : V ^ n ≤ V ^ (n + 1) := by
    intro x hx
    rw [pow_succ, ← mul_one x]
    exact Submodule.mul_mem_mul hx hV
  have hmono : Monotone (fun n : ℕ ↦ V ^ n) := monotone_nat_of_le_succ hstep
  have ha : a ∈ Algebra.adjoin k (V : Set A) := hgen.symm ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (p := fun x _ ↦ ∃ n, x ∈ V ^ n) ?_ ?_ ?_ ?_ ha
  · exact fun x hx ↦ ⟨1, by simpa only [pow_one] using (show x ∈ V from hx)⟩
  · exact fun c ↦ ⟨0, pow_zero V ▸ Submodule.mem_one.mpr ⟨c, rfl⟩⟩
  · rintro x y _ _ ⟨i, hi⟩ ⟨j, hj⟩
    exact ⟨max i j, add_mem (hmono (le_max_left i j) hi) (hmono (le_max_right i j) hj)⟩
  · rintro x y _ _ ⟨i, hi⟩ ⟨j, hj⟩
    exact ⟨i + j, (pow_add V i j).symm ▸ Submodule.mul_mem_mul hi hj⟩

/-- The Hilbert ideal argument on the Rees algebra, with the projection applied to
each extracted coefficient. -/
private theorem finiteType_of_filtered_projection
    (C : Subalgebra k A) (R : A →ₗ[k] C)
    (hMul : ∀ (b : C) (x : A), R ((b : A) * x) = b * R x)
    (hFix : ∀ b : C, R (b : A) = b)
    (V : Submodule k A) [FiniteDimensional k V]
    (hVone : (1 : A) ∈ V) (hVgen : Algebra.adjoin k (V : Set A) = ⊤)
    (hR : ∀ n : ℕ, ∀ a ∈ V ^ n, (R a : A) ∈ V ^ n) :
    Algebra.FiniteType k C := by
  classical
  let B := filteredRees V
  let : Algebra.FiniteType k B := finiteType_filteredRees V
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let S : Set B := {p | ∃ d : ℕ, 0 < d ∧ ∃ b : C, (p : A[X]) = monomial d (b : A)}
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp
    (IsNoetherian.noetherian (Ideal.span S))
  let ev (p : B) : A := (p : A[X]).eval 1
  let D := Algebra.adjoin k (ev '' (s : Set B))
  have hDC : D ≤ C := by
    apply Algebra.adjoin_le
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨d, _, b, hb⟩ := hs hp
    simp [ev, hb]
  have hdegree (n : ℕ) : ∀ a : C, (a : A) ∈ V ^ n → (a : A) ∈ D := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      by_cases hn : n = 0
      · subst n
        rw [pow_zero] at ha
        obtain ⟨c, hc⟩ := Submodule.mem_one.mp ha
        rw [← hc]
        exact D.algebraMap_mem c
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let p : B := ⟨monomial n (a : A), monomial_mem_filteredRees V ha⟩
      have hp : p ∈ Ideal.span (s : Set B) := by
        change p ∈ Submodule.span B (s : Set B)
        rw [← hspan]
        exact Submodule.subset_span ⟨n, hnpos, a, rfl⟩
      -- Allow an arbitrary multiplier so the induction is closed under ideal scalars.
      have hproject : ∀ q : B, (R ((↑(q * p) : A[X]).coeff n) : A) ∈ D := by
        refine Submodule.span_induction
          (p := fun f _ ↦ ∀ q : B, (R ((↑(q * f) : A[X]).coeff n) : A) ∈ D)
          ?_ ?_ ?_ ?_ hp
        · intro f hf q
          obtain ⟨d, hd, b, hb⟩ := hs hf
          have hbD : (b : A) ∈ D := by
            have he : ev f ∈ D := Algebra.subset_adjoin ⟨f, hf, rfl⟩
            simpa [ev, hb] using he
          change (R (((q : A[X]) * (f : A[X])).coeff n) : A) ∈ D
          rw [hb]
          by_cases hdn : d ≤ n
          · have hcoeff : ((q : A[X]) * monomial d (b : A)).coeff n =
                (q : A[X]).coeff (n - d) * b := by
              simpa only [Nat.sub_add_cancel hdn] using
                coeff_mul_monomial (q : A[X]) d (n - d) (b : A)
            rw [hcoeff, mul_comm, hMul]
            exact D.mul_mem hbD (ih (n - d) (Nat.sub_lt hnpos hd) _ (hR _ _ (q.property (n - d))))
          · rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow',
              ite_eq_right hdn, map_zero]
            exact D.zero_mem
        · intro q
          simp
        · intro f g _ _ hf hg q
          rw [mul_add]
          change (R (((↑(q * f) : A[X]) + (↑(q * g) : A[X])).coeff n) : A) ∈ D
          rw [coeff_add, map_add]
          exact D.add_mem (hf q) (hg q)
        · intro r f _ hf q
          change (R ((↑(q * (r * f)) : A[X]).coeff n) : A) ∈ D
          rw [← mul_assoc]
          exact hf (q * r)
      simpa [p, hFix] using hproject 1
  have heq : D = C := by
    apply le_antisymm hDC
    intro a ha
    obtain ⟨n, hn⟩ := exists_mem_pow V hVone hVgen a
    exact hdegree n ⟨a, ha⟩ hn
  rw [← heq]
  exact Algebra.FiniteType.adjoin_of_finite (s.finite_toSet.image ev)

/-- Finite generation of the fixed algebra from a Reynolds operator that preserves
finite-dimensional subcomodules. -/
theorem RationalAlgebraAction.filtered_finite_generation
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    {H : HopfAlgebraCategory k} (ρ : RationalAlgebraAction H A)
    (R : A →ₗ[k] ρ.fixedSubalgebra) (hReynolds : ρ.IsReynolds R)
    (hStable : ∀ W : Submodule k A, ρ.toRightComodule.IsSubcomodule W →
      FiniteDimensional k W → ∀ x ∈ W, (R x : A) ∈ W) :
    Algebra.FiniteType k ρ.fixedSubalgebra := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k A).out
  obtain ⟨W, hW⟩ := ρ.toRightComodule.exists_finiteSubcomodule_containing
    (insert (1 : A) (s : Set A)) (s.finite_toSet.insert 1)
  let : FiniteDimensional k W.val := W.property.2
  have hfg : W.val.FG := Module.Finite.iff_fg.mp inferInstance
  have hVgen : Algebra.adjoin k (W.val : Set A) = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_mono (fun a ha ↦ hW (Set.mem_insert_of_mem 1 ha))
  refine finiteType_of_filtered_projection ρ.fixedSubalgebra R hReynolds.2.1 hReynolds.2.2
    W.val (hW (Set.mem_insert 1 _)) hVgen ?_
  intro n
  have : FiniteDimensional k (W.val ^ n : Submodule k A) :=
    Module.Finite.of_fg (hfg.pow n)
  exact hStable _ (stable_pow ρ W.property.1 n) inferInstance

end

end RepTheorySurvey.Invariants
