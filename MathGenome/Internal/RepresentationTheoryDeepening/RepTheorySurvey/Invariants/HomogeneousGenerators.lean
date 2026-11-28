import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.Actions
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.HomogeneousGenerators
import Mathlib.RingTheory.Ideal.Operations

open DirectSum LinearAlgebraicGroups
open scoped TensorProduct

universe u v w t

namespace RepTheorySurvey.Invariants

variable {k : Type u} {A : Type w} [Field k] [CommRing A] [Algebra k A]

abbrev positiveHomogeneousInvariants := @Specs.positiveHomogeneousInvariants

variable (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

private theorem linearMap_eq_of_grades {M : Type*} [AddCommMonoid M] [Module k M]
    (f g : A →ₗ[k] M) (h : ∀ n x, x ∈ 𝒜 n → f x = g x) : f = g := by
  classical
  apply LinearMap.ext
  intro x
  calc
    f x = ∑ n ∈ (decompose 𝒜 x).support, f (decompose 𝒜 x n : A) := by
      rw [← map_sum, sum_support_decompose]
    _ = ∑ n ∈ (decompose 𝒜 x).support, g (decompose 𝒜 x n : A) :=
      Finset.sum_congr rfl fun n _ ↦ h n _ (decompose 𝒜 x n).2
    _ = g x := by rw [← map_sum, sum_support_decompose]

private theorem isInternal_of_proj_mem (B : Subalgebra k A)
    (hcomp : ∀ n {x : A}, x ∈ B → GradedAlgebra.proj 𝒜 n x ∈ B) :
    DirectSum.IsInternal (fun n ↦ (𝒜 n).comap B.val.toLinearMap) := by
  classical
  let incl : B →ₗ[k] A := B.val.toLinearMap
  let C : ℕ → Submodule k B := fun n ↦ (𝒜 n).comap incl
  change DirectSum.IsInternal C
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · intro n
    have hambient := (Decomposition.isInternal (ℳ := 𝒜)).submodule_iSupIndep n
    have hle : (⨆ i, ⨆ (_ : i ≠ n), C i) ≤ (⨆ i, ⨆ (_ : i ≠ n), 𝒜 i).comap incl :=
      iSup_le fun i ↦ iSup_le fun hi ↦
        Submodule.comap_mono (le_iSup_of_le i (le_iSup (fun _ : i ≠ n ↦ 𝒜 i) hi))
    refine Disjoint.mono_right hle ?_
    change Disjoint ((𝒜 n).comap incl) ((⨆ i, ⨆ (_ : i ≠ n), 𝒜 i).comap incl)
    rw [disjoint_iff, ← Submodule.comap_inf, disjoint_iff.mp hambient, Submodule.comap_bot,
      LinearMap.ker_eq_bot.mpr Subtype.val_injective]
  · apply top_unique
    intro x _
    let part (i : ℕ) : B := ⟨GradedAlgebra.proj 𝒜 i (x : A), hcomp i x.2⟩
    have hsum : ∑ i ∈ (decompose 𝒜 (x : A)).support, part i = x := by
      apply Subtype.ext
      change B.val (∑ i ∈ (decompose 𝒜 (x : A)).support, part i) = (x : A)
      rw [map_sum]
      exact sum_support_decompose 𝒜 (x : A)
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.mem_iSup_of_mem i (show part i ∈ C i from (decompose 𝒜 (x : A) i).2)

private theorem adjoin_eq_of_span (B : Subalgebra k A)
    (hcomp : ∀ n {x : A}, x ∈ B → GradedAlgebra.proj 𝒜 n x ∈ B)
    (R : A →ₗ[k] B) {ι : Type t} [Finite ι] (f : ι → B) (d : ι → ℕ)
    (hzero : 𝒜 0 = (⊥ : Subalgebra k A).toSubmodule)
    (hmul : ∀ (b : B) (x : A), R ((b : A) * x) = b * R x)
    (hfix : ∀ b : B, R (b : A) = b)
    (hR : ∀ (n : ℕ) (x : A), x ∈ 𝒜 n → (R x : A) ∈ 𝒜 n)
    (hpos : ∀ i, 0 < d i) (hf : ∀ i, (f i : A) ∈ 𝒜 (d i))
    (hspan : Ideal.span (Set.range fun i ↦ (f i : A)) =
      Ideal.span (positiveHomogeneousInvariants 𝒜 B)) :
    Algebra.adjoin k (Set.range fun i ↦ (f i : A)) = B := by
  classical
  let := Fintype.ofFinite ι
  let S := Algebra.adjoin k (Set.range fun i ↦ (f i : A))
  have hfS (i : ι) : (f i : A) ∈ S := Algebra.subset_adjoin (Set.mem_range_self i)
  have hhom (n : ℕ) : ∀ x ∈ 𝒜 n, x ∈ B → x ∈ S := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hxB
      by_cases hn : n = 0
      · subst n
        rw [hzero] at hx
        exact (show (⊥ : Subalgebra k A) ≤ S from bot_le) hx
      have hxI : x ∈ Ideal.span (Set.range fun i ↦ (f i : A)) := by
        rw [hspan]
        exact Ideal.subset_span ⟨hxB, n, Nat.pos_of_ne_zero hn, hx⟩
      obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hxI
      have hxR : R x = (⟨x, hxB⟩ : B) := hfix ⟨x, hxB⟩
      have hsum : ∑ i, R (GradedAlgebra.proj 𝒜 n (a i * (f i : A))) = (⟨x, hxB⟩ : B) := by
        have h := congrArg (fun y ↦ R (GradedAlgebra.proj 𝒜 n y)) ha
        simpa only [map_sum, GradedAlgebra.proj_apply, decompose_of_mem_same 𝒜 hx, hxR] using h
      have hsum' : ∑ i, (R (GradedAlgebra.proj 𝒜 n (a i * (f i : A))) : A) = x := by
        have h := congrArg B.val hsum
        rw [map_sum] at h
        exact h
      rw [← hsum']
      refine Subalgebra.sum_mem _ fun i _ ↦ ?_
      by_cases hi : d i ≤ n
      · rw [GradedAlgebra.proj_apply, coe_decompose_mul_of_right_mem_of_le 𝒜 (hf i) hi,
          mul_comm, hmul, Subalgebra.coe_mul]
        exact S.mul_mem (hfS i) (ih (n - d i) (Nat.sub_lt (Nat.pos_of_ne_zero hn) (hpos i)) _
          (hR _ _ (decompose 𝒜 (a i) (n - d i)).2) (R _).2)
      · rw [GradedAlgebra.proj_apply, coe_decompose_mul_of_right_mem_of_not_le 𝒜 (hf i) hi,
          map_zero, Subalgebra.coe_zero]
        exact S.zero_mem
  refine le_antisymm (Algebra.adjoin_le (Set.range_subset_iff.mpr fun i ↦ (f i).2)) ?_
  intro x hx
  rw [← sum_support_decompose 𝒜 x]
  exact Subalgebra.sum_mem S fun n _ ↦ hhom n _ (decompose 𝒜 x n).2 (hcomp n hx)

namespace GroupAlgebraAction

variable {k : Type u} {G : Type v} {A : Type w} [Field k] [Group G] [CommRing A] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (ρ : GroupAlgebraAction k G A)
    (hgraded : ∀ (g : G) (n : ℕ) (x : A), x ∈ 𝒜 n → ρ g x ∈ 𝒜 n)

include hgraded in
private theorem proj_mem (n : ℕ) {x : A} (hx : x ∈ ρ.fixedSubalgebra) :
    GradedAlgebra.proj 𝒜 n x ∈ ρ.fixedSubalgebra := by
  intro g
  let f := (ρ g).toLinearMap
  have hx' : f x = x := hx g
  have hcomm : f.comp (GradedAlgebra.proj 𝒜 n) = (GradedAlgebra.proj 𝒜 n).comp f := by
    apply linearMap_eq_of_grades 𝒜
    intro i y hy
    have hfy : f y ∈ 𝒜 i := hgraded g i y hy
    simp only [LinearMap.comp_apply, GradedAlgebra.proj_apply]
    by_cases h : i = n
    · subst i
      rw [decompose_of_mem_same 𝒜 hy, decompose_of_mem_same 𝒜 hfy]
    · rw [decompose_of_mem_ne 𝒜 hy h, decompose_of_mem_ne 𝒜 hfy h, map_zero]
  exact (LinearMap.congr_fun hcomm x).trans (congrArg (GradedAlgebra.proj 𝒜 n) hx')

include hgraded in
/-- The fixed algebra is the internal direct sum of its homogeneous subspaces. -/
theorem fixedSubalgebra_isInternal :
    DirectSum.IsInternal (fun n ↦ (𝒜 n).comap ρ.fixedSubalgebra.val.toLinearMap) :=
  isInternal_of_proj_mem 𝒜 _ (proj_mem 𝒜 ρ hgraded)

/-- A finite family of positive-degree homogeneous invariants generating their ambient ideal
also generates the fixed algebra. -/
theorem adjoin_homogeneous_eq_fixedSubalgebra
    (R : A →ₗ[k] ρ.fixedSubalgebra) {ι : Type t} [Finite ι]
    (f : ι → ρ.fixedSubalgebra) (d : ι → ℕ)
    (hzero : 𝒜 0 = (⊥ : Subalgebra k A).toSubmodule)
    (hgraded : ∀ (g : G) (n : ℕ) (x : A), x ∈ 𝒜 n → ρ g x ∈ 𝒜 n)
    (hReynolds : ρ.IsReynolds R)
    (hR : ∀ (n : ℕ) (x : A), x ∈ 𝒜 n → (R x : A) ∈ 𝒜 n)
    (hpos : ∀ i, 0 < d i) (hf : ∀ i, (f i : A) ∈ 𝒜 (d i))
    (hspan : Ideal.span (Set.range fun i ↦ (f i : A)) =
      Ideal.span (positiveHomogeneousInvariants 𝒜 ρ.fixedSubalgebra)) :
    Algebra.adjoin k (Set.range fun i ↦ (f i : A)) = ρ.fixedSubalgebra :=
  adjoin_eq_of_span 𝒜 _ (proj_mem 𝒜 ρ hgraded) R f d hzero
    hReynolds.2.1 hReynolds.2.2 hR hpos hf hspan

end GroupAlgebraAction

namespace RationalAlgebraAction

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] {H : HopfAlgebraCategory k}
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (ρ : RationalAlgebraAction H A)
    (hgraded : ∀ n, ρ.toRightComodule.IsSubcomodule (𝒜 n))

include hgraded in
private theorem proj_mem (n : ℕ) {x : A} (hx : x ∈ ρ.fixedSubalgebra) :
    GradedAlgebra.proj 𝒜 n x ∈ ρ.fixedSubalgebra := by
  let c := ρ.coaction.toLinearMap
  let p := GradedAlgebra.proj 𝒜 n
  have hx' : c x = x ⊗ₜ[k] (1 : H) := sub_eq_zero.mp hx
  have hcomm : c.comp p = (p.rTensor H).comp c := by
    apply linearMap_eq_of_grades 𝒜
    intro i y hy
    obtain ⟨z, hz⟩ := hgraded i ⟨y, hy⟩
    change (𝒜 i).subtype.rTensor H z = c y at hz
    simp only [LinearMap.comp_apply]
    rw [← hz, ← LinearMap.rTensor_comp_apply]
    by_cases h : i = n
    · subst i
      have he : p.comp (𝒜 n).subtype = (𝒜 n).subtype :=
        LinearMap.ext fun a ↦ decompose_of_mem_same 𝒜 a.2
      rw [he, hz]
      exact congrArg c (decompose_of_mem_same 𝒜 hy)
    · have he : p.comp (𝒜 i).subtype = 0 :=
        LinearMap.ext fun a ↦ decompose_of_mem_ne 𝒜 a.2 h
      rw [he]
      have hy0 : p y = 0 := decompose_of_mem_ne 𝒜 hy h
      rw [hy0]
      simp
  change c (p x) - p x ⊗ₜ[k] (1 : H) = 0
  apply sub_eq_zero.mpr
  calc
    c (p x) = p.rTensor H (c x) := LinearMap.congr_fun hcomm x
    _ = p x ⊗ₜ[k] (1 : H) := by rw [hx', LinearMap.rTensor_tmul]

include hgraded in
/-- The coaction invariants form the internal direct sum of their homogeneous subspaces. -/
theorem fixedSubalgebra_isInternal :
    DirectSum.IsInternal (fun n ↦ (𝒜 n).comap ρ.fixedSubalgebra.val.toLinearMap) :=
  isInternal_of_proj_mem 𝒜 _ (proj_mem 𝒜 ρ hgraded)

/-- A finite family of positive-degree homogeneous coaction invariants generating their
ambient ideal also generates the fixed algebra. -/
theorem adjoin_homogeneous_eq_fixedSubalgebra
    (R : A →ₗ[k] ρ.fixedSubalgebra) {ι : Type t} [Finite ι]
    (f : ι → ρ.fixedSubalgebra) (d : ι → ℕ)
    (hzero : 𝒜 0 = (⊥ : Subalgebra k A).toSubmodule)
    (hgraded : ∀ n, ρ.toRightComodule.IsSubcomodule (𝒜 n))
    (hReynolds : ρ.IsReynolds R)
    (hR : ∀ (n : ℕ) (x : A), x ∈ 𝒜 n → (R x : A) ∈ 𝒜 n)
    (hpos : ∀ i, 0 < d i) (hf : ∀ i, (f i : A) ∈ 𝒜 (d i))
    (hspan : Ideal.span (Set.range fun i ↦ (f i : A)) =
      Ideal.span (positiveHomogeneousInvariants 𝒜 ρ.fixedSubalgebra)) :
    Algebra.adjoin k (Set.range fun i ↦ (f i : A)) = ρ.fixedSubalgebra :=
  adjoin_eq_of_span 𝒜 _ (proj_mem 𝒜 ρ hgraded) R f d hzero
    hReynolds.2.1 hReynolds.2.2 hR hpos hf hspan

end RationalAlgebraAction

end RepTheorySurvey.Invariants
