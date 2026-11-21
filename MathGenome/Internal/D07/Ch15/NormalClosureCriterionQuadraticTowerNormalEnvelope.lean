import MathGenome.Internal.Specs.D07.Ch15.NormalClosureCriterionQuadraticTowerNormalEnvelope
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

universe u v

namespace D07.Ch15.NormalClosureCriterionQuadraticTowerNormalEnvelope

open IntermediateField Polynomial
open D07.Ch15.StraightedgeCompass D07.Ch15.QuadraticNormalEnvelope
open Specs.D07.Ch15.NormalClosureCriterionQuadraticTowerNormalEnvelope

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- A square root satisfies a monic quadratic, even if it already lies
in the base field or is zero. -/
theorem square_root_integral {x : L} (b : F)
    (hx : x ^ 2 = algebraMap F L b) : IsIntegral F x := by
  refine ⟨X ^ 2 - C b, monic_X_pow_sub_C b (by decide), ?_⟩
  simp [hx]

theorem square_root_degree_le_two {x : L} (b : F)
    (hx : x ^ 2 = algebraMap F L b) :
    Module.finrank F F⟮x⟯ ≤ 2 := by
  rw [adjoin.finrank (square_root_integral b hx)]
  have hd := minpoly.min F x (monic_X_pow_sub_C b (by decide))
    (show aeval x (X ^ 2 - C b) = 0 by simp [hx])
  simpa using Polynomial.natDegree_le_natDegree hd

/-- A finite family of square roots, adjoined one at a time, has
degree a power of two. Degree-one adjunctions are retained. -/
theorem finite_square_roots_degree (s : Finset L)
    (hs : ∀ x ∈ s, ∃ b : F, x ^ 2 = algebraMap F L b) :
    FiniteDimensional F (adjoin F (s : Set L)) ∧
      ∃ n : ℕ, Module.finrank F (adjoin F (s : Set L)) = 2 ^ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, IntermediateField.adjoin_empty]
    exact ⟨inferInstance, 0, by simp⟩
  | @insert x s hxs ih =>
    obtain ⟨hfin, n, hn⟩ := ih (fun y hy => hs y (Finset.mem_insert_of_mem hy))
    let A := adjoin F (s : Set L)
    let : FiniteDimensional F A := hfin
    obtain ⟨b, hb⟩ := hs x (Finset.mem_insert_self x s)
    have hx : x ^ 2 = algebraMap A L (algebraMap F A b) := by
      exact hb
    have hi := square_root_integral (algebraMap F A b) hx
    let : FiniteDimensional A A⟮x⟯ := adjoin.finiteDimensional hi
    have : FiniteDimensional F A⟮x⟯ := FiniteDimensional.trans F A A⟮x⟯
    have hd := square_root_degree_le_two (algebraMap F A b) hx
    have hp : 0 < Module.finrank A A⟮x⟯ := Module.finrank_pos
    have he : Module.finrank A A⟮x⟯ = 1 ∨ Module.finrank A A⟮x⟯ = 2 := by omega
    have ht : (A⟮x⟯).restrictScalars F = adjoin F (↑(insert x s) : Set L) := by
      rw [adjoin_adjoin_left, Finset.coe_insert, Set.union_singleton]
    rw [← ht]
    refine ⟨inferInstanceAs (FiniteDimensional F A⟮x⟯), ?_⟩
    change ∃ m, Module.finrank F A⟮x⟯ = 2 ^ m
    rw [← Module.finrank_mul_finrank F A A⟮x⟯, hn]
    rcases he with he | he
    · exact ⟨n, by rw [he, mul_one]⟩
    · exact ⟨n + 1, by rw [he, pow_succ]⟩

/-- Completing the square gives a square-root generator of every extension
of degree at most two, including the trivial extension. -/
theorem quadratic_square_generator (F L : Type*) [Field F] [CharZero F]
    [Field L] [Algebra F L] [FiniteDimensional F L]
    (hd : Module.finrank F L ≤ 2) :
    ∃ (v : L) (b : F), v ^ 2 = algebraMap F L b ∧ F⟮v⟯ = ⊤ := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  obtain ⟨u, hu⟩ := Field.exists_primitive_element F L
  let f := minpoly F u
  have hi : IsIntegral F u := Algebra.IsIntegral.isIntegral u
  have hm : f.Monic := minpoly.monic hi
  have hp : 0 < f.natDegree := minpoly.natDegree_pos hi
  have hd' : f.natDegree ≤ 2 := (minpoly.natDegree_le u).trans hd
  have hz : aeval u f = 0 := minpoly.aeval F u
  have hcases : f.natDegree = 1 ∨ f.natDegree = 2 := by omega
  rcases hcases with h1 | h2
  · have he := hm.eq_X_add_C h1
    rw [he] at hz
    simp only [aeval_add, aeval_X, aeval_C] at hz
    refine ⟨0, 0, by simp, ?_⟩
    apply top_unique
    rw [← hu]
    apply adjoin_simple_le_iff.mpr
    rw [show u = -algebraMap F L (f.coeff 0) from eq_neg_of_add_eq_zero_left hz]
    exact (F⟮(0 : L)⟯).neg_mem ((F⟮(0 : L)⟯).algebraMap_mem _)
  · have hc2 : f.coeff 2 = 1 := h2 ▸ hm.coeff_natDegree
    have he : f = X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
      conv_lhs => rw [f.as_sum_range_C_mul_X_pow, h2]
      simp [Finset.sum_range_succ, hc2]
      ring
    rw [he] at hz
    simp only [aeval_add, map_pow, aeval_X, aeval_mul, aeval_C] at hz
    let c := algebraMap F L (f.coeff 1)
    let v := 2 * u + c
    refine ⟨v, (f.coeff 1) ^ 2 - 4 * f.coeff 0, ?_, ?_⟩
    · simp only [map_sub, map_pow, map_mul, map_ofNat]
      dsimp [v, c]
      linear_combination 4 * hz
    · apply top_unique
      rw [← hu]
      apply adjoin_simple_le_iff.mpr
      have hv : v ∈ F⟮v⟯ := mem_adjoin_simple_self F v
      have hc : c ∈ F⟮v⟯ := (F⟮v⟯).algebraMap_mem _
      have htwo : (2 : L) ≠ 0 := by norm_num
      have heq : u = (v - c) / 2 := by dsimp [v]; field_simp; ring
      rw [heq]
      exact (F⟮v⟯).div_mem ((F⟮v⟯).sub_mem hv hc) ((F⟮v⟯).natCast_mem 2)

variable (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]

/-- There are finitely many conjugates and at most two roots for each. -/
theorem conjugateRoots_finite (N : IntermediateField K Ω)
    [FiniteDimensional K N] (b : N) : (conjugateRoots K Ω N b).Finite := by
  have h := Set.finite_iUnion (fun σ : N ≃ₐ[K] N =>
    Polynomial.finite_setOfPred_isRoot
      (monic_X_pow_sub_C (algebraMap N Ω (σ b)) (n := 2) (by decide)).ne_zero)
  apply h.subset
  rintro x ⟨σ, hσ⟩
  exact Set.mem_iUnion.mpr ⟨σ, by simpa [Polynomial.IsRoot, sub_eq_zero] using hσ⟩

/-- Ambient embeddings permute the old normal field and the conjugate
radicands, and consequently preserve the generated field. -/
theorem rootEnvelope_normal [IsAlgClosure K Ω]
    (N : IntermediateField K Ω) [Normal K N] (b : N) :
    Normal K (rootEnvelope K Ω N b) := by
  rw [rootEnvelope, restrictScalars_adjoin]
  apply normal_iff_forall_map_le.mpr
  intro τ
  rw [adjoin_map, adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  apply subset_adjoin
  rcases hy with hy | hy
  · left
    have he := τ.restrictNormal_commutes N (⟨y, hy⟩ : N)
    exact he ▸ (τ.restrictNormal N ⟨y, hy⟩).2
  · right
    obtain ⟨σ, hσ⟩ := hy
    refine ⟨σ.trans (τ.restrictNormal' N), ?_⟩
    change (τ y) ^ 2 = algebraMap N Ω (τ.restrictNormal N (σ b))
    rw [τ.restrictNormal_commutes N, ← map_pow, hσ]

/-- One finite normal stage, adjoining square roots of all conjugates.
No ordering or realness is required of the new field. -/
theorem conjugate_root_stage : ConjugateRootStage.{u, v} := by
  intro K Ω _ _ _ _ _ N _ _ b hN
  have hs := conjugateRoots_finite K Ω N b
  obtain ⟨hf, m, hm⟩ := finite_square_roots_degree (F := N) hs.toFinset
    (fun x hx => by
      obtain ⟨σ, hσ⟩ := hs.mem_toFinset.mp hx
      exact ⟨σ b, hσ⟩)
  rw [hs.coe_toFinset] at hf hm
  let A := adjoin N (conjugateRoots K Ω N b)
  have : FiniteDimensional N A := hf
  have : FiniteDimensional K A := FiniteDimensional.trans K N A
  have : Normal K (rootEnvelope K Ω N b) := rootEnvelope_normal K Ω N b
  refine ⟨?_, inferInstanceAs (FiniteDimensional K A), ⟨⟩, ?_, ?_⟩
  · intro x hx
    exact A.algebraMap_mem (⟨x, hx⟩ : N)
  · obtain ⟨n, hn⟩ := hN
    refine ⟨n + m, ?_⟩
    change Module.finrank K A = 2 ^ (n + m)
    rw [← Module.finrank_mul_finrank K N A, hn, hm, pow_add]
  · intro x hx
    exact subset_adjoin N _ ⟨AlgEquiv.refl, hx⟩

/-- Membership in a generated field transports along a specified field map.
The target field need not carry the source's base scalar action. -/
theorem range_mem_of_generator {E T : Type*} [Field E] [Field T]
    [Algebra F E] (v : E) (hv : F⟮v⟯ = ⊤) (ι : E →+* T)
    (A : Subfield T) (hbase : ∀ b : F, ι (algebraMap F E b) ∈ A)
    (hgen : ι v ∈ A) : ∀ x : E, ι x ∈ A := by
  intro x
  have hx : x ∈ F⟮v⟯ := by rw [hv]; trivial
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => simpa only [Set.mem_singleton_iff.mp hx] using hgen
  | algebraMap b => exact hbase b
  | add x y _ _ hx hy => simpa only [map_add] using A.add_mem hx hy
  | inv x _ hx => simpa only [map_inv₀] using A.inv_mem hx
  | mul x y _ _ hx hy => simpa only [map_mul] using A.mul_mem hx hy

/-- The induction respects any chosen compatible embedding of the real top
into the chosen algebraic closure. -/
theorem tower_normal_envelope : TowerNormalEnvelope.{v} := by
  intro K M h
  induction h with
  | base =>
    refine ⟨le_rfl, ?_⟩
    intro Ω _ _ _ ι hι
    refine ⟨⊥, inferInstance, inferInstance, ⟨0, by simp⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [hι x x.2]
    exact (⊥ : IntermediateField K Ω).algebraMap_mem x
  | @step M ht E hf hd ih =>
    obtain ⟨hKM, ih⟩ := ih
    have hME : M ≤ E.restrictScalars ℚ := fun x hx => E.algebraMap_mem ⟨x, hx⟩
    refine ⟨hKM.trans hME, ?_⟩
    intro Ω _ _ _ ι hι
    let ιE : E →+* Ω := ι
    let ιM : M →+* Ω := ιE.comp (algebraMap M E)
    have hιM : ∀ (k : K) (hk : (k : ℝ) ∈ M),
        ιM ⟨(k : ℝ), hk⟩ = algebraMap K Ω k := by
      intro k hk
      exact hι k (hME hk)
    obtain ⟨N, hNfin, hNGal, hNpow, hNmem⟩ := ih Ω ιM hιM
    let : FiniteDimensional K N := hNfin
    let : IsGalois K N := hNGal
    let : FiniteDimensional M E := hf
    obtain ⟨v, b, hv, hgen⟩ := quadratic_square_generator M E hd
    let bN : N := ⟨ιM b, hNmem ⟨b, rfl⟩⟩
    obtain ⟨hNA, hAfin, hAGal, hApow, hroots⟩ :=
      conjugate_root_stage K Ω N bN hNpow
    let A := rootEnvelope K Ω N bN
    refine ⟨A, hAfin, hAGal, hApow, ?_⟩
    rintro _ ⟨x, rfl⟩
    apply range_mem_of_generator v hgen ιE A.toSubfield
    · intro c
      exact hNA (hNmem ⟨c, rfl⟩)
    · apply hroots
      change (ιE v) ^ 2 = ιE (algebraMap M E b)
      exact (ιE.map_pow v 2).symm.trans (congrArg ιE hv)

/-- Algebraic closedness extends a compatible embedding through each finite
step. Only the tower fields, rather than the whole real field, are embedded. -/
theorem exists_tower_embedding (K M : IntermediateField ℚ ℝ)
    (h : QuadraticTower K M) (Ω : Type v) [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] :
    ∃ (hKM : K ≤ M) (ι : M →+* Ω),
      ∀ k : K, ι ⟨(k : ℝ), hKM k.2⟩ = algebraMap K Ω k := by
  induction h with
  | base => exact ⟨le_rfl, algebraMap K Ω, fun _ => rfl⟩
  | @step M ht E hf hd ih =>
    obtain ⟨hKM, ιM, hιM⟩ := ih
    let : Algebra M Ω := ιM.toAlgebra
    let : FiniteDimensional M E := hf
    let f : E →ₐ[M] Ω := IsAlgClosed.lift
    have hME : M ≤ E.restrictScalars ℚ := fun x hx => E.algebraMap_mem ⟨x, hx⟩
    refine ⟨hKM.trans hME, f.toRingHom, ?_⟩
    intro k
    exact (f.commutes (⟨(k : ℝ), hKM k.2⟩ : M)).trans (hιM k)

/-- Existence in every specified algebraic closure, obtained from the
stronger theorem for any compatible embedding. -/
theorem exists_tower_normal_envelope : ExistsTowerNormalEnvelope.{v} := by
  intro K M h Ω _ _ _
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨hKM, ι, hι⟩ := exists_tower_embedding K M h Ω
  obtain ⟨N, hN⟩ := (tower_normal_envelope K M h).2 Ω ι (fun k hk => hι k)
  exact ⟨hKM, ι, N, hι, hN⟩

end D07.Ch15.NormalClosureCriterionQuadraticTowerNormalEnvelope
