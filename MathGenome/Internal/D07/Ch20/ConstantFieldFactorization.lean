import MathGenome.Internal.Specs.D07.Ch20.ConstantFieldFactorization
import MathGenome.Internal.D07.Ch13.Existence
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Squarefree.Basic

universe u v w
namespace D07.Ch20.ConstantFieldFactorization
set_option maxHeartbeats 800000
open Polynomial UniqueFactorizationMonoid
open scoped Classical

/-- An irreducible root is fixed by the j-th relative Frobenius exactly when
its degree divides j. This includes j = 0. -/
lemma degree_dvd_iff_frobenius_fixed
    (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω] [Finite K]
    (f : K[X]) (a : Ω) (hf : Irreducible f) (ha : aeval a f = 0) (j : ℕ) :
    f.natDegree ∣ j ↔ a ^ (Nat.card K ^ j) = a := by
  rw [hf.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X,
    ← hf.dvd_iff_aeval_eq_zero ha]
  simp [sub_eq_zero]

/-- Dividing by the gcd gives the least step that closes the cycle. -/
lemma quotient_gcd_dvd_iff (n k j : ℕ) (hn : 0 < n) :
    n / Nat.gcd n k ∣ j ↔ n ∣ k * j := by
  rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left n k)
    (Nat.gcd_pos_of_pos_left k hn),
    Nat.dvd_gcd_mul_iff_dvd_mul]

/-- Every irreducible factor after extending the constants has the same degree.
A common root compares the two Frobenius divisibility tests. -/
lemma factor_degree
    (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω] [Finite K] [Finite L] [IsAlgClosed Ω]
    (k : ℕ) (hcard : Nat.card L = Nat.card K ^ k)
    (f : K[X]) (hf : Irreducible f)
    (g : L[X]) (hg : Irreducible g) (hgf : g ∣ f.map (algebraMap K L)) :
    g.natDegree = f.natDegree / Nat.gcd f.natDegree k := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_aeval_eq_zero Ω g hg.degree_pos.ne'
  have haf : aeval a f = 0 := by
    have h : aeval a (f.map (algebraMap K L)) = 0 :=
      (hg.dvd_iff_aeval_eq_zero ha).mpr hgf
    simpa only [aeval_map_algebraMap] using h
  have htest (j : ℕ) :
      g.natDegree ∣ j ↔ f.natDegree / Nat.gcd f.natDegree k ∣ j := by
    rw [degree_dvd_iff_frobenius_fixed L Ω g a hg ha,
      quotient_gcd_dvd_iff _ _ _ hf.natDegree_pos,
      degree_dvd_iff_frobenius_fixed K Ω f a hf haf, hcard, ← pow_mul]
  exact Nat.dvd_antisymm ((htest _).mpr dvd_rfl) ((htest _).mp dvd_rfl)

/-- The canonical normalized factor set, with its exact number, degrees, and
product. Separability ensures that converting the factor multiset to a set
loses no multiplicities. -/
lemma normalized_factorization_data
    (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω] [Finite K] [Finite L] [IsAlgClosed Ω]
    (k : ℕ) (hcard : Nat.card L = Nat.card K ^ k)
    (f : K[X]) (hm : f.Monic) (hf : Irreducible f) :
    let F := f.map (algebraMap K L)
    let s := (normalizedFactors F).toFinset
    s.card = Nat.gcd f.natDegree k ∧
      (∀ g ∈ s, g.Monic ∧ Irreducible g ∧
        g.natDegree = f.natDegree / Nat.gcd f.natDegree k) ∧
      F = ∏ g ∈ s, g := by
  classical
  let F := f.map (algebraMap K L)
  let s := (normalizedFactors F).toFinset
  have hFm : F.Monic := hm.map _
  have hF0 : F ≠ 0 := hFm.ne_zero
  have hsep : F.Separable :=
    (PerfectField.separable_iff_squarefree.mpr hf.squarefree).map
  have hnodup : (normalizedFactors F).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hF0).mp hsep.squarefree
  have hfac : ∀ g ∈ s, g.Monic ∧ Irreducible g ∧
      g.natDegree = f.natDegree / Nat.gcd f.natDegree k := by
    intro g hg
    have hg' : g ∈ normalizedFactors F := Multiset.mem_toFinset.mp hg
    obtain ⟨hirr, hmonic, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff hF0).mp hg'
    exact ⟨hmonic, hirr, factor_degree K L Ω k hcard f hf g hirr hdvd⟩
  have hprod : F = ∏ g ∈ s, g := by
    have h := leadingCoeff_mul_prod_normalizedFactors F
    rw [hFm.leadingCoeff, C_1, one_mul] at h
    rw [← h]
    change (normalizedFactors F).prod = (s.val.map id).prod
    congr 1
    dsimp [s]
    rw [Multiset.dedup_eq_self.mpr hnodup, Multiset.map_id]
  have hsum : f.natDegree = s.card * (f.natDegree / Nat.gcd f.natDegree k) := by
    calc
      f.natDegree = F.natDegree := (natDegree_map _).symm
      _ = (∏ g ∈ s, g).natDegree := congrArg natDegree hprod
      _ = ∑ g ∈ s, g.natDegree := natDegree_prod_of_monic _ _ (fun g hg => (hfac g hg).1)
      _ = ∑ _g ∈ s, f.natDegree / Nat.gcd f.natDegree k :=
        Finset.sum_congr rfl (fun g hg => (hfac g hg).2.2)
      _ = s.card * (f.natDegree / Nat.gcd f.natDegree k) := by simp
  have hcount : s.card = Nat.gcd f.natDegree k := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.div_gcd_pos_of_pos_left k hf.natDegree_pos)
    rw [← hsum, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
  exact ⟨hcount, hfac, hprod⟩

/-- Existence form of the normalized factorization, hiding its implementation
from consumers of the finite factor set. -/
lemma factorization_exists
    (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω] [Finite K] [Finite L] [IsAlgClosed Ω]
    (k : ℕ) (hcard : Nat.card L = Nat.card K ^ k)
    (f : K[X]) (hm : f.Monic) (hf : Irreducible f) :
    ∃ s : Finset L[X], s.card = Nat.gcd f.natDegree k ∧
      (∀ g ∈ s, g.Monic ∧ Irreducible g ∧
        g.natDegree = f.natDegree / Nat.gcd f.natDegree k) ∧
      f.map (algebraMap K L) = ∏ g ∈ s, g := by
  exact ⟨_, normalized_factorization_data K L Ω k hcard f hm hf⟩

/-- Irreducibility is equivalent to the normalized factor set having one
member, hence to coprimality of the two degrees. -/
lemma irreducible_iff_gcd_degree_eq_one
    (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω] [Finite K] [Finite L] [IsAlgClosed Ω]
    (k : ℕ) (hcard : Nat.card L = Nat.card K ^ k)
    (f : K[X]) (hm : f.Monic) (hf : Irreducible f) :
    Irreducible (f.map (algebraMap K L)) ↔ Nat.gcd f.natDegree k = 1 := by
  classical
  let F := f.map (algebraMap K L)
  let s := (normalizedFactors F).toFinset
  have hdata : s.card = Nat.gcd f.natDegree k ∧
      (∀ g ∈ s, g.Monic ∧ Irreducible g ∧
        g.natDegree = f.natDegree / Nat.gcd f.natDegree k) ∧
      F = ∏ g ∈ s, g := normalized_factorization_data K L Ω k hcard f hm hf
  constructor
  · intro h
    change Irreducible F at h
    have hsingle : s.card = 1 := by
      dsimp only [s]
      rw [normalizedFactors_irreducible h]
      simp
    exact hdata.1.symm.trans hsingle
  · intro h
    obtain ⟨g, hg⟩ := Finset.card_eq_one.mp (hdata.1.trans h)
    have hgin : g ∈ s := by rw [hg]; simp
    have hprod : F = g := by simpa [hg] using hdata.2.2
    change Irreducible F
    rw [hprod]
    exact (hdata.2.1 g hgin).2.1

/-- The complete factorization in the specified constant field in the fixed
algebraic closure. -/
theorem constant_field_factorization :
    Specs.D07.Ch20.ConstantFieldFactorization.Factorization.{u, v} := by
  classical
  intro K Ω _ _ _ _ _ _ q n k hq hn hk f hm hf hdegree
  let E := Specs.D07.Ch13.Existence.rootFieldValue K Ω q k
  have hE := D07.Ch13.Existence.embedded_existence K Ω q k hq hk
  let : Finite E := hE.1
  have hcard : Nat.card E = Nat.card K ^ k := by rw [hq]; exact hE.2.1
  have h := factorization_exists K E Ω k hcard f hm hf
  rw [hdegree] at h
  exact h

/-- The irreducibility criterion, including the linear-polynomial case. -/
theorem remains_irreducible :
    Specs.D07.Ch20.ConstantFieldFactorization.RemainsIrreducible.{u, v} := by
  classical
  intro K Ω _ _ _ _ _ _ q n k hq hn hk f hm hf hdegree
  let E := Specs.D07.Ch13.Existence.rootFieldValue K Ω q k
  have hE := D07.Ch13.Existence.embedded_existence K Ω q k hq hk
  let : Finite E := hE.1
  have hcard : Nat.card E = Nat.card K ^ k := by rw [hq]; exact hE.2.1
  simpa only [hdegree] using irreducible_iff_gcd_degree_eq_one K E Ω k hcard f hm hf

end D07.Ch20.ConstantFieldFactorization
