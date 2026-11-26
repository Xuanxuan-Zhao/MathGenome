import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FinitePrimeFiltration
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Data.Finset.Max

namespace CommutativeAlgebraNotes.PrimeFiltration

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The prime-filtration theorem. Mathlib constructs the chain by adjoining a cyclic
submodule from an associated prime of each nonzero quotient and uses the ascending
chain condition to terminate. Existence of that prime uses a maximal annihilator. -/
theorem exists_filtration (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Nonempty (PrimeFiltration R M) := by
  classical
  obtain ⟨s, hfirst, hlast⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime R M
  have hstep (i : Fin s.length) :
      (s i.castSucc).IsQuotientEquivQuotientPrime (s i.succ) := s.step i
  choose p e using fun i => (hstep i).2
  refine ⟨⟨s.length, s, hfirst, hlast, ?_, p, fun i => (e i).some⟩⟩
  refine Fin.strictMono_iff_lt_succ.mpr fun i => lt_of_le_of_ne (hstep i).1 ?_
  intro h
  have : Nontrivial (R ⧸ (p i).asIdeal) := Ideal.Quotient.nontrivial_iff.mpr (p i).isPrime.ne_top
  have hn := (e i).some.symm.injective.nontrivial
  exact (Submodule.Quotient.nontrivial_iff.mp hn) (Submodule.submoduleOf_eq_top.mpr h.ge)

theorem inclusion_injective (F : PrimeFiltration R M) ⦃i j : Fin (F.length + 1)⦄
    (h : i ≤ j) : Function.Injective (F.inclusion h) :=
  Submodule.inclusion_injective _

/-- The short exact sequence `0 → Mᵢ → Mᵢ₊₁ → R/𝔭ᵢ → 0`. -/
theorem step_shortExact (F : PrimeFiltration R M) (i : Fin F.length) :
    Function.Injective (F.inclusion (Fin.castSucc_le_succ i)) ∧
      Function.Exact (F.inclusion (Fin.castSucc_le_succ i)) (F.projection i) ∧
      Function.Surjective (F.projection i) := by
  refine ⟨F.inclusion_injective _, ?_, (F.factorEquiv i).surjective.comp
    (Submodule.mkQ_surjective _)⟩
  unfold projection
  rw [(F.factorEquiv i).postcomp_exact_iff_exact, LinearMap.exact_iff,
    Submodule.ker_mkQ, inclusion, Submodule.range_inclusion]
  rfl

private theorem quotient_support (I : Ideal R) :
    Module.support R (R ⧸ I) = PrimeSpectrum.zeroLocus I := by
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

private theorem step_support (F : PrimeFiltration R M) (i : Fin F.length) :
    Module.support R (F.stage i.succ) = Module.support R (F.stage i.castSucc) ∪
      PrimeSpectrum.zeroLocus (F.prime i).asIdeal := by
  obtain ⟨hi, he, hs⟩ := F.step_shortExact i
  rw [Module.support_of_exact he hi hs, quotient_support]

/-- The support of a stage consists of the supports of the factors up to that stage. -/
theorem mem_stageSupport_iff (F : PrimeFiltration R M) (k : Fin (F.length + 1))
    (q : PrimeSpectrum R) :
    q ∈ Module.support R (F.stage k) ↔
      ∃ i : Fin F.length, i.val < k.val ∧ q ∈ PrimeSpectrum.zeroLocus (F.prime i).asIdeal := by
  suffices ∀ (n : ℕ) (hn : n < F.length + 1),
      q ∈ Module.support R (F.stage ⟨n, hn⟩) ↔
        ∃ i : Fin F.length, i.val < n ∧ q ∈ PrimeSpectrum.zeroLocus (F.prime i).asIdeal from
    this k.val k.isLt
  intro n
  induction n with
  | zero =>
    intro hn
    change q ∈ Module.support R (F.stage 0) ↔ _
    rw [F.first_eq_bot, Module.support_eq_empty]
    simp
  | succ n ih =>
    intro hn
    let i : Fin F.length := ⟨n, Nat.lt_of_succ_lt_succ hn⟩
    change q ∈ Module.support R (F.stage i.succ) ↔ _
    have hprev : q ∈ Module.support R (F.stage i.castSucc) ↔
        ∃ j : Fin F.length, j.val < n ∧ q ∈ PrimeSpectrum.zeroLocus (F.prime j).asIdeal :=
      ih (Nat.lt_trans (Nat.lt_succ_self n) hn)
    rw [step_support, Set.mem_union, hprev]
    constructor
    · rintro (⟨j, hj, hq⟩ | hq)
      · exact ⟨j, Nat.lt_succ_of_lt hj, hq⟩
      · exact ⟨i, Nat.lt_succ_self n, hq⟩
    · rintro ⟨j, hj, hq⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
      · exact Or.inl ⟨j, h, hq⟩
      · have he : j = i := Fin.ext h
        exact Or.inr (he ▸ hq)

theorem support_eq (F : PrimeFiltration R M) :
    Module.support R M = ⋃ i : Fin F.length, PrimeSpectrum.zeroLocus (F.prime i).asIdeal := by
  have htop : Module.support R (F.stage (Fin.last F.length)) = Module.support R M := by
    rw [F.last_eq_top]
    exact (Submodule.topEquiv (R := R) (M := M)).support_eq
  ext q
  rw [← htop, F.mem_stageSupport_iff, Set.mem_iUnion]
  exact ⟨fun ⟨i, _, hq⟩ => ⟨i, hq⟩, fun ⟨i, hq⟩ => ⟨i, i.isLt, hq⟩⟩

theorem stage_support_subset (F : PrimeFiltration R M) (k : Fin (F.length + 1)) :
    Module.support R (F.stage k) ⊆ Module.support R M :=
  Module.support_subset_of_injective _ (Submodule.injective_subtype _)

theorem factor_support_subset (F : PrimeFiltration R M) (i : Fin F.length) :
    Module.support R (R ⧸ (F.prime i).asIdeal) ⊆ Module.support R M := by
  rw [quotient_support, F.support_eq]
  exact Set.subset_iUnion (fun j => PrimeSpectrum.zeroLocus (R := R) (F.prime j).asIdeal) i

/-- Every chain in the support lies in the zero locus of a factor containing its bottom
prime. This gives the dimension formula even for unbounded Krull dimension. -/
theorem supportDim_eq (F : PrimeFiltration R M) :
    Module.supportDim R M = ⨆ i : Fin F.length, ringKrullDim (R ⧸ (F.prime i).asIdeal) := by
  refine le_antisymm ?_ (iSup_le fun i => ?_)
  · unfold Module.supportDim Order.krullDim
    refine iSup_le fun s => ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (F.support_eq.le s.head.property)
    have hmem (k : Fin (s.length + 1)) :
        (s k).val ∈ PrimeSpectrum.zeroLocus (F.prime i).asIdeal := by
      have hle : s.head.val.asIdeal ≤ (s k).val.asIdeal := s.head_le k
      have hbot : (F.prime i).asIdeal ≤ s.head.val.asIdeal :=
        (PrimeSpectrum.mem_zeroLocus _ _).mp hi
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (hbot.trans hle)
    let t : LTSeries (PrimeSpectrum.zeroLocus (R := R) (F.prime i).asIdeal) :=
      LTSeries.mk s.length (fun k => ⟨(s k).val, hmem k⟩)
        (fun _ _ h => s.strictMono h)
    have ht := Order.LTSeries.length_le_krullDim t
    rw [← ringKrullDim_quotient] at ht
    exact ht.trans (le_iSup (fun j => ringKrullDim (R ⧸ (F.prime j).asIdeal)) i)
  · rw [← Module.supportDim_quotient_eq_ringKrullDim]
    exact Order.krullDim_le_of_strictMono
      (fun q => ⟨q.val, F.factor_support_subset i q.property⟩) (fun _ _ h => h)

/-- Exactly the zero modules have an empty prime filtration. -/
theorem length_zero (F : PrimeFiltration R M) :
    (F.length = 0 ↔ Subsingleton M) ∧ (F.length = 0 → Module.supportDim R M = ⊥) := by
  have hdim (h : F.length = 0) : Module.supportDim R M = ⊥ := by
    have : IsEmpty (Fin F.length) := h ▸ inferInstanceAs (IsEmpty (Fin 0))
    rw [F.supportDim_eq, iSup_of_empty]
  refine ⟨⟨fun h => (Module.supportDim_eq_bot_iff_subsingleton R M).mp (hdim h), ?_⟩, hdim⟩
  intro hM
  by_contra h
  let i : Fin F.length := ⟨0, Nat.pos_of_ne_zero h⟩
  exact (F.strictMono_stage (Fin.castSucc_lt_succ (i := i))).ne (Subsingleton.elim _ _)

/-- In a nonzero module the common dimension is attained by a prime factor. -/
theorem supportDim_maximum (F : PrimeFiltration R M) (hM : Nontrivial M) :
    ∃ i : Fin F.length, Module.supportDim R M = ringKrullDim (R ⧸ (F.prime i).asIdeal) ∧
      ∀ j : Fin F.length, ringKrullDim (R ⧸ (F.prime j).asIdeal) ≤
        ringKrullDim (R ⧸ (F.prime i).asIdeal) := by
  have hpos := Nat.pos_of_ne_zero (fun h => not_nontrivial_iff_subsingleton.mpr
    (F.length_zero.1.mp h) hM)
  let dim (i : Fin F.length) := ringKrullDim (R ⧸ (F.prime i).asIdeal)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ dim ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
  have hmax (j : Fin F.length) : dim j ≤ dim i := hi j (Finset.mem_univ _)
  exact ⟨i, F.supportDim_eq.trans ((iSup_le hmax).antisymm (le_iSup dim i)), hmax⟩

end CommutativeAlgebraNotes.PrimeFiltration
