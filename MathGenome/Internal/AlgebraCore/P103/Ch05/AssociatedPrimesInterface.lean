import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedPrimesInterface

/-!
Source associated primes, support, cyclic embeddings, and the maximal
annihilator argument (paper.tex:961). These definitions do not use Mathlib's
radical-based associated primes, so all arbitrary-ring statements retain
exact annihilators. No module finiteness is needed for nonemptiness.
-/
namespace P103.Ch05.AssociatedPrimesInterface

universe u v
open P103.Specs.Ch05.AssociatedPrimesInterface
open LinearMap Submodule

def elementAnnihilator : ElementAnnihilatorType.{u,v} := elementAnnihilatorValue

def associatedPrimes : AssociatedPrimesType.{u,v} := associatedPrimesValue

def support : SupportType.{u,v} := supportValue

theorem mem_elementAnnihilator : mem_elementAnnihilatorType.{u,v} := by
  intro R _ M _ _ x r
  simp [elementAnnihilatorValue]

theorem mem_associatedPrimes : mem_associatedPrimesType.{u,v} := by
  intro R _ M _ _ p
  rfl

theorem mem_support : mem_supportType.{u,v} := by
  intro R _ M _ _ p
  rfl

theorem annihilator_witness_ne_zero : annihilator_witness_ne_zeroType.{u,v} := by
  intro R _ M _ _ p x hp he hx
  apply hp.ne_top
  simp [he, hx, elementAnnihilatorValue]

theorem mem_associatedPrimes_iff_embedding : mem_associatedPrimes_iff_embeddingType.{u,v} := by
  intro R _ M _ _ p
  change (p.IsPrime ∧ ∃ x : M, p = (⊥ : Submodule R M).colon {x}) ↔ _
  rw [and_congr_right_iff]
  intro _
  constructor
  · rintro ⟨x, h⟩
    have hk : p = ker (toSpanSingleton R M x) := by
      simp [h, SetLike.ext_iff]
    exact ⟨liftQ _ _ hk.le, ker_eq_bot.mp (ker_liftQ_eq_bot' _ _ hk)⟩
  · rintro ⟨f, hf⟩
    refine ⟨(f ∘ₗ mkQ p) 1, ?_⟩
    conv_lhs => rw [← p.ker_mkQ, ← ker_comp_of_ker_eq_bot (mkQ p) (ker_eq_bot_of_injective hf)]
    simp [SetLike.ext_iff, ← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one]

theorem exists_maximal_annihilator : exists_maximal_annihilatorType.{u,v} := by
  intro R _ hR M _ _ _
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : M)
  obtain ⟨p, ⟨x, hx, he⟩, hm⟩ :=
    set_has_maximal_iff_noetherian.mpr hR
      {p : Ideal R | ∃ x : M, x ≠ 0 ∧ p = elementAnnihilatorValue R M x}
      ⟨elementAnnihilatorValue R M x₀, x₀, hx₀, rfl⟩
  subst p
  refine ⟨x, hx, fun y hy hle => ?_⟩
  exact hle.eq_of_not_lt (hm _ ⟨y, hy, rfl⟩)

theorem maximal_annihilator_isPrime : maximal_annihilator_isPrimeType.{u,v} := by
  intro R _ M _ _ x hx hm
  have hproper : elementAnnihilatorValue R M x ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ elementAnnihilatorValue R M x := h.symm ▸ mem_top
    exact hx (by simpa [elementAnnihilatorValue] using h1)
  refine ⟨hproper, ?_⟩
  intro a b hab
  rw [or_iff_not_imp_right]
  intro hb
  have hbx : b • x ≠ 0 := by
    simpa [elementAnnihilatorValue] using hb
  have hle : elementAnnihilatorValue R M x ≤ elementAnnihilatorValue R M (b • x) := by
    intro c hc
    simp only [elementAnnihilatorValue, mem_colon_singleton, mem_bot] at hc ⊢
    rw [smul_comm, hc, smul_zero]
  rw [hm (b • x) hbx hle]
  simpa only [elementAnnihilatorValue, mem_colon_singleton, mem_bot, smul_smul] using hab

theorem associatedPrimes_nonempty : associatedPrimes_nonemptyType.{u,v} := by
  intro R _ _ M _ _ _
  obtain ⟨x, hx, hm⟩ := exists_maximal_annihilator R M
  exact ⟨elementAnnihilatorValue R M x, maximal_annihilator_isPrime R M x hx hm, x, rfl⟩

theorem associatedPrimes_eq_empty : associatedPrimes_eq_emptyType.{u,v} := by
  intro R _ M _ _ _
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨hp, x, he⟩
  exact annihilator_witness_ne_zero R M p x hp he (Subsingleton.elim x 0)

theorem support_eq_empty : support_eq_emptyType.{u,v} := by
  intro R _ M _ _ _
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hn : Nontrivial (LocalizedModule p.asIdeal.primeCompl M) := hp
  exact not_nontrivial (LocalizedModule p.asIdeal.primeCompl M) hn

end P103.Ch05.AssociatedPrimesInterface
