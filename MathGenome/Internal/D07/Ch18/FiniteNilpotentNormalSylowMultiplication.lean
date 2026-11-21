import MathGenome.Internal.Specs.D07.Ch18.FiniteNilpotentNormalSylowMultiplication

/-!
Normal Sylow subgroups of distinct primes are disjoint, hence commute.
Pairwise coprime factor orders then give independence from the subgroup of all
other factors. Thus multiplication is injective. The product of the Sylow
orders is |G|, so multiplication is also surjective. We construct this actual
multiplication homomorphism directly, avoiding an abstract cardinality-only
isomorphism or a redundant product over all choices of Sylow subgroup.
-/
namespace D07.Ch18.FiniteNilpotentNormalSylowMultiplication

open Specs.D07.Ch18.FiniteNilpotentNormalSylowMultiplication
universe u

variable {G : Type u} [Group G] [Finite G]

local instance prime_fact (p : PrimeDivisors G) : Fact (Nat.Prime p.val) :=
  ⟨Nat.prime_of_mem_primeFactors p.property⟩

/-- Distinct normal Sylow factors commute, even when an individual factor is
nonabelian. -/
theorem commuting_factors (G : Type u) [Group G] [Finite G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G) (hn : AllSylowNormal G) :
    Pairwise (fun p q => ∀ x y : G,
      x ∈ (P p).toSubgroup → y ∈ (P q).toSubgroup → Commute x y) := by
  intro p q hpq
  apply Subgroup.commute_of_normal_of_disjoint _ _
    (hn p.val (Nat.prime_of_mem_primeFactors p.property) (P p))
    (hn q.val (Nat.prime_of_mem_primeFactors q.property) (P q))
  exact IsPGroup.disjoint_of_ne p.val q.val (by simpa using hpq)
    _ _ (P p).isPGroup' (P q).isPGroup'

/-- Independence is stronger than pairwise trivial intersection. -/
theorem independent_factors
    (P : ∀ p : PrimeDivisors G, Sylow p.val G) (hn : AllSylowNormal G) :
    iSupIndep (fun p => (P p).toSubgroup) := by
  classical
  let (p : PrimeDivisors G) : Fintype (P p) := Fintype.ofFinite (P p)
  apply Subgroup.independent_of_coprime_order (commuting_factors G P hn)
  intro p q hpq
  simpa using IsPGroup.coprime_card_of_ne p.val q.val (by simpa using hpq)
    _ _ (P p).isPGroup' (P q).isPGroup'

/-- Each factor has trivial intersection with the product of every other prime. -/
theorem trivial_intersections (G : Type u) [Group G] [Finite G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G) (hn : AllSylowNormal G)
    (p : PrimeDivisors G) :
    (P p).toSubgroup ⊓ (⨆ (q) (_ : q ≠ p), (P q).toSubgroup) = ⊥ :=
  disjoint_iff.mp (independent_factors P hn p)

/-- The full prime-power parts multiply to the original group order. -/
theorem product_cardinality (P : ∀ p : PrimeDivisors G, Sylow p.val G) :
    Nat.card (∀ p, P p) = Nat.card G := by
  classical
  rw [Nat.card_pi]
  calc
    _ = ∏ p : PrimeDivisors G, p.val ^ (Nat.card G).factorization p.val := by
      apply Finset.prod_congr rfl
      intro p _
      exact (P p).card_eq_multiplicity
    _ = Nat.card G := by
      rw [Finset.univ_eq_attach, Finsupp.prod_attach_index]
      exact (Nat.prod_primeFactors_pow_factorization (n := Nat.card G)
        (Nat.card_pos (α := G)).ne').symm

/-- The chosen-family multiplication homomorphism is bijective. -/
theorem multiplication_bijective
    (P : ∀ p : PrimeDivisors G, Sylow p.val G) (hn : AllSylowNormal G) :
    Function.Bijective (Subgroup.noncommPiCoprod (commuting_factors G P hn)) := by
  apply Nat.bijective_iff_injective_and_card _ |>.mpr
  exact ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep (independent_factors P hn),
    product_cardinality P⟩

/-- Exhaustion is equality of the actual generated subgroup with G. -/
theorem exhaustion (G : Type u) [Group G] [Finite G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G) (hn : AllSylowNormal G) :
    (⨆ p, (P p).toSubgroup) = ⊤ := by
  rw [← Subgroup.noncommPiCoprod_range (hcomm := commuting_factors G P hn)]
  exact MonoidHom.range_eq_top.mpr (multiplication_bijective P hn).surjective

/-- The explicit multiplication isomorphism with its formula in ANY enumeration
of the primes and its formula on each coordinate inclusion. -/
theorem multiplication_isomorphism (G : Type u) [Group G] [Finite G]
    (P : ∀ p : PrimeDivisors G, Sylow p.val G) (hn : AllSylowNormal G) :
    ∃ e : (∀ p, P p) ≃* G,
      (∀ (x : ∀ p, P p) (l : List (PrimeDivisors G)),
        l.Nodup → l.toFinset = Finset.univ →
        e x = (l.map (fun p => (x p : G))).prod) ∧
      (∀ (p : PrimeDivisors G) (y : P p),
        e (Pi.mulSingle p y) = (y : G)) := by
  classical
  let f := Subgroup.noncommPiCoprod (commuting_factors G P hn)
  refine ⟨MulEquiv.ofBijective f (multiplication_bijective P hn), ?_, ?_⟩
  · intro x l hl henum
    change f x = _
    rw [Subgroup.noncommPiCoprod_apply, ← henum]
    exact Finset.noncommProd_toFinset l _ _ hl
  · intro p y
    change f (Pi.mulSingle p y) = (y : G)
    exact Subgroup.noncommPiCoprod_mulSingle
      (hcomm := commuting_factors G P hn) p y

/-- The trivial group's product is genuinely indexed by the empty set. -/
theorem empty_product (G : Type u) [Group G] [Finite G] [Subsingleton G] :
    IsEmpty (PrimeDivisors G) ∧
    ∀ P : ∀ p : PrimeDivisors G, Sylow p.val G,
      ∃ e : (∀ p, P p) ≃* G, ∀ x, e x = 1 := by
  have he : IsEmpty (PrimeDivisors G) := by
    simp only [PrimeDivisors, Nat.card_unique, Nat.primeFactors_one]
    infer_instance
  refine ⟨he, ?_⟩
  intro P
  have hn : AllSylowNormal G := by
    intro p hp Q
    have hQ : Q.toSubgroup = ⊤ := Subsingleton.elim _ _
    rw [hQ]
    infer_instance
  obtain ⟨e, _⟩ := multiplication_isomorphism G P hn
  exact ⟨e, fun _ => Subsingleton.elim _ _⟩

end D07.Ch18.FiniteNilpotentNormalSylowMultiplication
