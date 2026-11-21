import MathGenome.Internal.Specs.D05.M10.JordanUniqueness
import MathGenome.Internal.D05.M10.JordanExistence
import MathGenome.Internal.D05.M10.KernelStabilization
import MathGenome.Internal.D05.M06.SumDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Logic.Equiv.Basic

noncomputable section
open scoped BigOperators Classical
namespace D05.M10.JordanUniqueness
open Specs.D05.M10.JordanUniqueness

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Iteration along a chain, in the paper's order. -/
lemma chain_pow (N : Module.End K V) (c : Chains N) (j : ℕ)
    (i : Fin c.blocks) (k : Fin (c.length i)) :
    (N ^ j) (c.basis ⟨i, k⟩) =
      if h : j ≤ k.val then c.basis ⟨i, ⟨k.val - j, by omega⟩⟩ else 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    by_cases h : j ≤ k.val
    · rw [dite_eq_left h]
      by_cases hj : j + 1 ≤ k.val
      · rw [dite_eq_left hj]
        exact c.step i _ _ (by dsimp; omega)
      · rw [dite_eq_right hj]
        exact c.zero i _ (by dsimp; omega)
    · rw [dite_eq_right h, dite_eq_right (show ¬ j + 1 ≤ k.val by omega), map_zero]

/-- The image has precisely the initial `length - j` vectors of each chain. -/
lemma range_power (N : Module.End K V) (c : Chains N) (j : ℕ) :
    LinearMap.range (N ^ j) = Submodule.span K
      (Set.range (fun t : Σ i, Fin (c.length i - j) =>
        c.basis ⟨t.1, ⟨t.2.val, lt_of_lt_of_le t.2.isLt (Nat.sub_le _ _)⟩⟩)) := by
  let f := fun t : Σ i, Fin (c.length i - j) =>
    c.basis ⟨t.1, ⟨t.2.val, lt_of_lt_of_le t.2.isLt (Nat.sub_le _ _)⟩⟩
  apply le_antisymm
  · have hr : LinearMap.range (N ^ j) =
        Submodule.span K (Set.range (fun t => (N ^ j) (c.basis t))) := by
      rw [Set.range_comp', ← Submodule.map_span, c.basis.span_eq]
      simp
    rw [hr]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, k⟩, rfl⟩
    dsimp only
    rw [chain_pow]
    split_ifs with h
    · exact Submodule.subset_span ⟨⟨i, ⟨k.val - j, by omega⟩⟩, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, k⟩, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨c.basis ⟨i, ⟨k.val + j, by omega⟩⟩, ?_⟩
    simp [chain_pow]

lemma rank_power (N : Module.End K V) (c : Chains N) (j : ℕ) :
    Module.finrank K (LinearMap.range (N ^ j)) = ∑ i, (c.length i - j) := by
  rw [range_power N c j]
  have hi : Function.Injective (fun t : Σ i, Fin (c.length i - j) =>
      (⟨t.1, ⟨t.2.val, lt_of_lt_of_le t.2.isLt (Nat.sub_le _ _)⟩⟩ : Σ i, Fin (c.length i))) := by
    rintro ⟨i, k⟩ ⟨l, m⟩ h
    have hil : i = l := congrArg Sigma.fst h
    subst l
    have hkm := sigma_mk_injective h
    have : k = m := Fin.ext (congrArg (fun z : Fin (c.length i) => z.val) hkm)
    subst m
    rfl
  exact (finrank_span_eq_card (c.basis.linearIndependent.comp _ hi)).trans (by simp)


theorem kernel_dimensions : Specs.D05.M10.JordanUniqueness.kernel_dimensions := by
  intro K V _ _ _ _ N c j
  have hr := LinearMap.finrank_range_add_finrank_ker (N ^ j)
  rw [rank_power N c j] at hr
  have hd : Module.finrank K V = ∑ i, c.length i := by
    simpa using Module.finrank_eq_card_basis c.basis
  rw [hd] at hr
  have hsum : (∑ i, (c.length i - j)) + (∑ i, min j (c.length i)) =
      ∑ i, c.length i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    omega
  unfold nullity
  omega

theorem single_block_nullity : Specs.D05.M10.JordanUniqueness.single_block_nullity := by
  intro K V _ _ _ _ N c h j
  rw [kernel_dimensions]
  have : Subsingleton (Fin c.blocks) := by rw [h]; infer_instance
  let i : Fin c.blocks := ⟨0, by omega⟩
  exact Finset.sum_eq_single i (by intro b _ hb; exact (hb (Subsingleton.elim _ _)).elim)
    (by simp)



lemma nullity_increment (N : Module.End K V) (c : Chains N) (j : ℕ)
    [FiniteDimensional K V] (hj : 0 < j) :
    nullity N (j - 1) + blocksAtLeast c j = nullity N j := by
  rw [kernel_dimensions N c, kernel_dimensions N c]
  unfold blocksAtLeast
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> omega

theorem blocks_at_least : Specs.D05.M10.JordanUniqueness.blocks_at_least := by
  intro K V _ _ _ _ N c j hj
  have h := nullity_increment N c j hj
  omega

lemma count_partition (N : Module.End K V) (c : Chains N) (j : ℕ) :
    blocksExactly c j + blocksAtLeast c (j + 1) = blocksAtLeast c j := by
  unfold blocksExactly blocksAtLeast
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> omega

theorem blocks_exactly : Specs.D05.M10.JordanUniqueness.blocks_exactly := by
  intro K V _ _ _ _ N c j hj
  have h := count_partition N c j
  rw [blocks_at_least N c j hj, blocks_at_least N c (j + 1) (by omega)] at h
  simp only [Nat.add_sub_cancel] at h
  omega

lemma blocksExactly_zero (N : Module.End K V) (c : Chains N) : blocksExactly c 0 = 0 := by
  simp only [blocksExactly, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ hi
  exact (c.positive i).ne' hi

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Equal multiplicities give a bijection of block occurrences, even with repeats. -/
lemma permutation_of_counts {N : Module.End K V} {M : Module.End K W}
    (c : Chains N) (d : Chains M)
    (h : ∀ j, blocksExactly c j = blocksExactly d j) :
    ∃ e : Fin c.blocks ≃ Fin d.blocks, ∀ i, d.length (e i) = c.length i := by
  let e (j : ℕ) : {i // c.length i = j} ≃ {i // d.length i = j} :=
    Fintype.equivOfCardEq (by simpa only [blocksExactly, Fintype.card_subtype] using h j)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

theorem nilpotent_uniqueness : Specs.D05.M10.JordanUniqueness.nilpotent_uniqueness := by
  intro K V _ _ _ _ N c d
  apply permutation_of_counts c d
  intro j
  cases j with
  | zero => rw [blocksExactly_zero, blocksExactly_zero]
  | succ j => rw [blocks_exactly N c _ (Nat.succ_pos _),
      blocks_exactly N d _ (Nat.succ_pos _)]

theorem kernels_eventually_full :
    Specs.D05.M10.JordanUniqueness.kernels_eventually_full := by
  intro K V _ _ _ _ N hN j hj
  have hn := Nilpotent.kernel_pow_dimension N (Module.finrank K V) rfl hN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact (KernelStabilization.kernel_stabilization N _ rfl k).symm.trans hn

theorem spectral_data_exists : Specs.D05.M10.JordanUniqueness.spectral_data_exists := by
  intro K V _ _ _ _ T
  have h (μ : K) : Nonempty (Chains (nilpotentPart T μ)) := by
    have hn : IsNilpotent (nilpotentPart T μ) :=
      Generalized.restriction_nilpotent T μ _
    obtain ⟨r, a, ha, b, hz, hs, _⟩ := JordanChains.jordan_chain_basis _ hn
    exact ⟨⟨r, a, ha, b, hz, hs⟩⟩
  exact ⟨fun μ => Classical.choice (h μ)⟩

theorem spectral_counts : Specs.D05.M10.JordanUniqueness.spectral_counts := by
  intro K V _ _ _ _ T d μ j hj
  exact blocks_exactly _ (d μ) j hj

theorem spectral_uniqueness : Specs.D05.M10.JordanUniqueness.spectral_uniqueness := by
  intro K V _ _ _ _ T c d μ
  exact nilpotent_uniqueness _ (c μ) (d μ)



/-- Restricting to G_μ does not change any kernel of a power of T - μ I. -/
lemma restricted_nullity [FiniteDimensional K V] (T : Module.End K V) (μ : K) (j : ℕ) :
    nullity (nilpotentPart T μ) j = nullity (T - μ • 1) j := by
  let U := Specs.D05.M10.Generalized.generalizedEigenspace_value K V T μ
  have hle : LinearMap.ker ((T - μ • 1) ^ j) ≤ U := by
    intro x hx
    exact (Generalized.mem_iff T μ x).mpr
      (Module.End.ker_pow_le_ker_pow_finrank (T - μ • 1) j hx)
  have hk : LinearMap.ker (nilpotentPart T μ ^ j) =
      (LinearMap.ker ((T - μ • 1) ^ j)).submoduleOf U := by
    change LinearMap.ker (((T - μ • (1 : Module.End K V)).restrict
      (p := T.genEigenspace μ (Module.finrank K V))
      (q := T.genEigenspace μ (Module.finrank K V)) _) ^ j) = _
    rw [Module.End.pow_restrict, LinearMap.ker_restrict]
    rfl
  unfold nullity
  rw [hk]
  exact (Submodule.submoduleOfEquivOfLe hle).finrank_eq

lemma intertwining_pow (N : Module.End K V) (M : Module.End K W)
    (e : V ≃ₗ[K] W) (h : ∀ x, e (N x) = M (e x)) (j : ℕ) (x : V) :
    e ((N ^ j) x) = (M ^ j) (e x) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [pow_succ', Module.End.mul_apply, h, ih]

lemma nullity_intertwining (N : Module.End K V) (M : Module.End K W)
    (e : V ≃ₗ[K] W) (h : ∀ x, e (N x) = M (e x)) (j : ℕ) :
    nullity N j = nullity M j := by
  have hk : LinearMap.ker (N ^ j) = (LinearMap.ker (M ^ j)).comap e.toLinearMap := by
    ext x
    change (N ^ j) x = 0 ↔ (M ^ j) (e x) = 0
    rw [← intertwining_pow N M e h j x, e.map_eq_zero_iff]
  unfold nullity
  rw [hk]
  exact (e.ofSubmodule' (LinearMap.ker (M ^ j))).finrank_eq

/-- Reorder corresponding chains and take the basis-to-basis isomorphism. -/
lemma chains_intertwiner {N : Module.End K V} {M : Module.End K W}
    (c : Chains N) (d : Chains M)
    (hc : ∀ j, blocksExactly c j = blocksExactly d j) :
    ∃ e : V ≃ₗ[K] W, ∀ x, e (N x) = M (e x) := by
  obtain ⟨f, hf⟩ := permutation_of_counts c d hc
  let F : (Σ i, Fin (c.length i)) ≃ (Σ i, Fin (d.length i)) :=
    Equiv.sigmaCongr f (fun i => finCongr (hf i).symm)
  let e := c.basis.equiv d.basis F
  have he (i : Fin c.blocks) (k : Fin (c.length i)) :
      e (c.basis ⟨i, k⟩) = d.basis ⟨f i, ⟨k.val, by rw [hf]; exact k.isLt⟩⟩ := by
    change c.basis.equiv d.basis F (c.basis ⟨i, k⟩) = _
    rw [Module.Basis.equiv_apply]
    rfl
  refine ⟨e, ?_⟩
  have hmaps : e.toLinearMap.comp N = M.comp e.toLinearMap := by
    apply c.basis.ext
    rintro ⟨i, k⟩
    change e (N (c.basis ⟨i, k⟩)) = M (e (c.basis ⟨i, k⟩))
    rw [he]
    by_cases hk : k.val = 0
    · rw [c.zero i k hk, map_zero, d.zero _ _ hk]
    · let l : Fin (c.length i) := ⟨k.val - 1, by omega⟩
      rw [c.step i k l (by dsimp [l]; omega), he,
        d.step (f i) _ ⟨l.val, by rw [hf]; exact l.isLt⟩ (by dsimp [l]; omega)]
  intro x
  exact congrArg (fun f : V →ₗ[K] W => f x) hmaps

/-- The shared generalized eigenspaces form an internal sum over all scalars.
Only finitely many are nonzero; the direct sum retains finite support. -/
lemma all_eigenspaces_internal [FiniteDimensional K V] (T : Module.End K V)
    (hT : T.charpoly.Splits) : DirectSum.IsInternal
      (fun μ : K => Specs.D05.M10.Generalized.generalizedEigenspace_value K V T μ) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact T.independent_genEigenspace (Module.finrank K V)
  · exact GeneralizedDecomposition.iSup_generalized_eq_top T T.charpoly
      T.charpoly_monic hT (D05.M08.CayleyHamilton.annihilates T)



lemma similarity_of_counts [FiniteDimensional K V] [FiniteDimensional K W]
    (T : Module.End K V) (S : Module.End K W) (hT : T.charpoly.Splits)
    (hS : S.charpoly.Splits) (c : SpectralData T) (d : SpectralData S)
    (hc : ∀ μ j, blocksExactly (c μ) j = blocksExactly (d μ) j) :
    ∃ e : V ≃ₗ[K] W, ∀ x, e (T x) = S (e x) := by
  let U := fun μ => Specs.D05.M10.Generalized.generalizedEigenspace_value K V T μ
  let Q := fun μ => Specs.D05.M10.Generalized.generalizedEigenspace_value K W S μ
  choose f hf using fun μ => chains_intertwiner (c μ) (d μ) (hc μ)
  have hU := all_eigenspaces_internal T hT
  have hQ := all_eigenspaces_internal S hS
  let B := hU.collectedBasis (fun μ => (c μ).basis)
  let C := hQ.collectedBasis (fun μ => (c μ).basis.map (f μ))
  let e : V ≃ₗ[K] W := B.equiv C (Equiv.refl _)
  have he (μ : K) (x : U μ) : e (x : V) = (f μ x : W) := by
    have hh : e.toLinearMap.comp (U μ).subtype =
        (Q μ).subtype.comp (f μ).toLinearMap := by
      apply (c μ).basis.ext
      intro i
      change e ((c μ).basis i : V) = (f μ ((c μ).basis i) : W)
      have hb : B ⟨μ, i⟩ = ((c μ).basis i : V) := by simp [B]
      have hd : C ⟨μ, i⟩ = (f μ ((c μ).basis i) : W) := by simp [C]
      rw [← hb, ← hd]
      exact Module.Basis.equiv_apply _ _ _ _
    exact congrArg (fun g : U μ →ₗ[K] W => g x) hh
  have ht : e.toLinearMap.comp T = S.comp e.toLinearMap := by
    apply B.ext
    rintro ⟨μ, i⟩
    have hb : B ⟨μ, i⟩ = ((c μ).basis i : V) := by simp [B]
    let x : U μ := (c μ).basis i
    have hTx : T (x : V) = μ • (x : V) + (nilpotentPart T μ x : V) := by
      change T (x : V) = μ • (x : V) + (T (x : V) - μ • (x : V))
      abel
    have hSx : S (f μ x : W) = μ • (f μ x : W) +
        (nilpotentPart S μ (f μ x) : W) := by
      change S (f μ x : W) = μ • (f μ x : W) +
        (S (f μ x : W) - μ • (f μ x : W))
      abel
    change e (T (B ⟨μ, i⟩)) = S (e (B ⟨μ, i⟩))
    rw [hb]
    change e (T (x : V)) = S (e (x : V))
    rw [hTx]
    simp only [map_add, map_smul, he, hf μ x]
    exact hSx.symm
  exact ⟨e, fun x => congrArg (fun g : V →ₗ[K] W => g x) ht⟩

theorem similarity_criterion : Specs.D05.M10.JordanUniqueness.similarity_criterion := by
  intro K V W _ _ _ _ _ _ _ T S hT hS c d
  constructor
  · exact similarity_of_counts T S hT hS c d
  · rintro ⟨e, he⟩ μ j
    by_cases hj : j = 0
    · subst j
      rw [blocksExactly_zero, blocksExactly_zero]
    have hn (k : ℕ) : nullity (nilpotentPart T μ) k =
        nullity (nilpotentPart S μ) k := by
      rw [restricted_nullity, restricted_nullity]
      apply nullity_intertwining _ _ e
      intro x
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        map_sub, map_smul, he]
    rw [blocks_exactly _ (c μ) j (by omega), blocks_exactly _ (d μ) j (by omega),
      hn, hn, hn]



theorem jordan_basis_exists : Specs.D05.M10.JordanUniqueness.jordan_basis_exists := by
  intro K V _ _ _ _ T hT
  obtain ⟨r, a, μ, ha, b, hz, hs, _⟩ := JordanExistence.exists_chain_basis T hT
  exact ⟨⟨r, a, μ, ha, b, hz, hs⟩⟩

theorem jordan_basis_matrix : Specs.D05.M10.JordanUniqueness.jordan_basis_matrix := by
  intro K V _ _ _ T c
  exact JordanExistence.matrix_of_chain_basis c.length c.eigenvalue T c.basis c.zero c.step

/-- Each individual chain already lies in its labelled generalized eigenspace. -/
lemma jordan_vector_mem [FiniteDimensional K V] (T : Module.End K V) (c : JordanBasis T)
    (i : Fin c.blocks) (k : Fin (c.length i)) :
    c.basis ⟨i, k⟩ ∈ Specs.D05.M10.Generalized.generalizedEigenspace_value K V T
      (c.eigenvalue i) := by
  let N := T - c.eigenvalue i • 1
  have hz (l : Fin (c.length i)) (hl : l.val = 0) : N (c.basis ⟨i, l⟩) = 0 := by
    change T (c.basis ⟨i, l⟩) - c.eigenvalue i • c.basis ⟨i, l⟩ = 0
    rw [c.zero i l hl, sub_self]
  have hs (l m : Fin (c.length i)) (hl : l.val = m.val + 1) :
      N (c.basis ⟨i, l⟩) = c.basis ⟨i, m⟩ := by
    change T (c.basis ⟨i, l⟩) - c.eigenvalue i • c.basis ⟨i, l⟩ = c.basis ⟨i, m⟩
    rw [c.step i l m hl, add_sub_cancel_left]
  have hp (n : ℕ) : ∀ l : Fin (c.length i), l.val < n → (N ^ n) (c.basis ⟨i, l⟩) = 0 := by
    induction n with
    | zero => intro l hl; omega
    | succ n ih =>
      intro l hl
      rw [pow_succ, Module.End.mul_apply]
      by_cases hl0 : l.val = 0
      · rw [hz l hl0, map_zero]
      · rw [hs l ⟨l.val - 1, by omega⟩ (by dsimp; omega)]
        exact ih _ (by dsimp; omega)
  exact (Generalized.mem_iff T (c.eigenvalue i) _).mpr
    (Module.End.ker_pow_le_ker_pow_finrank N (k.val + 1) (hp _ k (by omega)))

/-- Restrict the block index to a chosen eigenvalue. The selected vectors span
G_μ: independence of all generalized eigenspaces and spanning of the original
basis force equality, without any dimension formula being assumed. -/
lemma jordan_eigenspace_span [FiniteDimensional K V] (T : Module.End K V)
    (c : JordanBasis T) (μ : K) :
    Submodule.span K (Set.range (fun t : Σ i : {i // c.eigenvalue i = μ}, Fin (c.length i.val) =>
      c.basis ⟨t.1.val, t.2⟩)) =
      Specs.D05.M10.Generalized.generalizedEigenspace_value K V T μ := by
  let A (ν : K) := Submodule.span K
    (Set.range (fun t : Σ i : {i // c.eigenvalue i = ν}, Fin (c.length i.val) =>
      c.basis ⟨t.1.val, t.2⟩))
  have hle : A ≤ fun ν => T.genEigenspace ν (Module.finrank K V) := by
    intro ν
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨⟨i, hi⟩, k⟩, rfl⟩
    simpa only [Specs.D05.M10.Generalized.generalizedEigenspace_value,
      SetLike.mem_coe, ← hi] using jordan_vector_mem T c i k
  have htop : iSup A = ⊤ := by
    apply top_unique
    rw [← c.basis.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, k⟩, rfl⟩
    exact (le_iSup A (c.eigenvalue i))
      (Submodule.subset_span ⟨⟨⟨i, rfl⟩, k⟩, rfl⟩)
  have heq := (T.independent_genEigenspace (Module.finrank K V)).le_iff_eq_of_iSup_eq_top htop
  exact congrFun (heq.mp hle) μ



lemma jordan_local_chains [FiniteDimensional K V] (T : Module.End K V)
    (c : JordanBasis T) (μ : K) :
    ∃ d : Chains (nilpotentPart T μ),
      ∃ f : Fin d.blocks ≃ {i // c.eigenvalue i = μ},
        ∀ i, d.length i = c.length (f i).val := by
  let I := {i // c.eigenvalue i = μ}
  let U := Specs.D05.M10.Generalized.generalizedEigenspace_value K V T μ
  let v := fun t : Σ i : I, Fin (c.length i.val) => c.basis ⟨t.1.val, t.2⟩
  have hinj : Function.Injective (fun t : Σ i : I, Fin (c.length i.val) =>
      (⟨t.1.val, t.2⟩ : Σ i, Fin (c.length i))) :=
    by
      rintro ⟨⟨i, hi⟩, k⟩ ⟨⟨l, hl⟩, m⟩ h
      have hil : i = l := congrArg Sigma.fst h
      subst l
      have hkm : k = m := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      subst m
      rfl
  have hli : LinearIndependent K v := c.basis.linearIndependent.comp _ hinj
  let b₀ : Module.Basis (Σ i : I, Fin (c.length i.val)) K U :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ (jordan_eigenspace_span T c μ))
  have hb₀ (i : I) (j : Fin (c.length i.val)) :
      (b₀ ⟨i, j⟩ : V) = c.basis ⟨i.val, j⟩ := by
    simp [b₀, Module.Basis.span_apply, v]
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let a : Fin (Fintype.card I) → ℕ := fun i => c.length (e.symm i).val
  let F : (Σ i : I, Fin (c.length i.val)) ≃ (Σ i, Fin (a i)) := Equiv.sigmaCongrLeft' e
  let b := b₀.reindex F
  have hb (i : Fin (Fintype.card I)) (j : Fin (a i)) :
      (b ⟨i, j⟩ : V) = c.basis ⟨(e.symm i).val, j⟩ := by
    simpa [b, F, Equiv.sigmaCongrLeft', Equiv.sigmaCongrLeft] using hb₀ (e.symm i) j
  refine ⟨⟨Fintype.card I, a, fun i => c.positive _, b, ?_, ?_⟩, e.symm, fun _ => rfl⟩
  · intro i j hj
    apply Subtype.ext
    change T (b ⟨i, j⟩ : V) - μ • (b ⟨i, j⟩ : V) = 0
    rw [hb, c.zero _ _ hj]
    simp only [(e.symm i).property, sub_self]
  · intro i j k hjk
    apply Subtype.ext
    change T (b ⟨i, j⟩ : V) - μ • (b ⟨i, j⟩ : V) = (b ⟨i, k⟩ : V)
    rw [hb, hb, c.step _ _ _ hjk]
    simp only [(e.symm i).property, add_sub_cancel_left]

/-- Convert the selected-chain multiplicity into the fiber of the original
(eigenvalue, length) map. This retains repeated block occurrences. -/
lemma jordan_fiber_count [FiniteDimensional K V] (T : Module.End K V)
    (c : JordanBasis T) (μ : K) (j : ℕ) :
    Fintype.card {i // (c.eigenvalue i, c.length i) = (μ, j)} =
      if j = 0 then 0 else
        (nullity (nilpotentPart T μ) j - nullity (nilpotentPart T μ) (j - 1)) -
        (nullity (nilpotentPart T μ) (j + 1) - nullity (nilpotentPart T μ) j) := by
  obtain ⟨d, f, hf⟩ := jordan_local_chains T c μ
  let e₁ : {i // d.length i = j} ≃
      {i : {i // c.eigenvalue i = μ} // c.length i.val = j} :=
    f.subtypeEquiv (by intro i; rw [hf i])
  let e₂ : {i : {i // c.eigenvalue i = μ} // c.length i.val = j} ≃
      {i // (c.eigenvalue i, c.length i) = (μ, j)} :=
    { toFun := fun i => ⟨i.val.val, Prod.ext i.val.property i.property⟩
      invFun := fun i => ⟨⟨i.val, (Prod.mk.inj i.property).1⟩, (Prod.mk.inj i.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e := e₁.trans e₂
  have hc : Fintype.card {i // (c.eigenvalue i, c.length i) = (μ, j)} =
      blocksExactly d j := by
    simpa only [blocksExactly, Fintype.card_subtype] using (Fintype.card_congr e).symm
  rw [hc]
  split_ifs with hj
  · subst j
    exact blocksExactly_zero _ d
  · exact blocks_exactly _ d j (by omega)

theorem jordan_basis_uniqueness : Specs.D05.M10.JordanUniqueness.jordan_basis_uniqueness := by
  intro K V _ _ _ _ T c d
  let f (p : K × ℕ) : {i // (c.eigenvalue i, c.length i) = p} ≃
      {i // (d.eigenvalue i, d.length i) = p} :=
    Fintype.equivOfCardEq (by rw [jordan_fiber_count, jordan_fiber_count])
  refine ⟨Equiv.ofFiberEquiv f, ?_⟩
  intro i
  exact Prod.mk.inj (Equiv.ofFiberEquiv_map f i)



theorem jordan_similarity_criterion :
    Specs.D05.M10.JordanUniqueness.jordan_similarity_criterion := by
  intro K V W _ _ _ _ _ _ _ T S c d
  constructor
  · rintro ⟨f, hf⟩
    let F : (Σ i, Fin (c.length i)) ≃ (Σ i, Fin (d.length i)) :=
      Equiv.sigmaCongr f (fun i => finCongr (hf i).2.symm)
    let e := c.basis.equiv d.basis F
    have he (i : Fin c.blocks) (k : Fin (c.length i)) :
        e (c.basis ⟨i, k⟩) = d.basis ⟨f i, ⟨k.val, by rw [(hf i).2]; exact k.isLt⟩⟩ := by
      change c.basis.equiv d.basis F (c.basis ⟨i, k⟩) = _
      rw [Module.Basis.equiv_apply]
      rfl
    have ht : e.toLinearMap.comp T = S.comp e.toLinearMap := by
      apply c.basis.ext
      rintro ⟨i, k⟩
      change e (T (c.basis ⟨i, k⟩)) = S (e (c.basis ⟨i, k⟩))
      rw [he]
      by_cases hk : k.val = 0
      · rw [c.zero i k hk, map_smul, he, d.zero _ _ hk]
        simp only [(hf i).1]
      · let l : Fin (c.length i) := ⟨k.val - 1, by omega⟩
        rw [c.step i k l (by dsimp [l]; omega), map_add, map_smul, he, he,
          d.step (f i) _ ⟨l.val, by rw [(hf i).2]; exact l.isLt⟩
            (by dsimp [l]; omega)]
        simp only [(hf i).1]
    exact ⟨e, fun x => congrArg (fun g : V →ₗ[K] W => g x) ht⟩
  · rintro ⟨e, he⟩
    have hn (μ : K) (j : ℕ) : nullity (nilpotentPart T μ) j =
        nullity (nilpotentPart S μ) j := by
      rw [restricted_nullity, restricted_nullity]
      apply nullity_intertwining _ _ e
      intro x
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        map_sub, map_smul, he]
    let f (p : K × ℕ) : {i // (c.eigenvalue i, c.length i) = p} ≃
        {i // (d.eigenvalue i, d.length i) = p} :=
      Fintype.equivOfCardEq (by
        rw [jordan_fiber_count, jordan_fiber_count, hn, hn, hn])
    exact ⟨Equiv.ofFiberEquiv f, fun i => Prod.mk.inj (Equiv.ofFiberEquiv_map f i)⟩

end D05.M10.JordanUniqueness
