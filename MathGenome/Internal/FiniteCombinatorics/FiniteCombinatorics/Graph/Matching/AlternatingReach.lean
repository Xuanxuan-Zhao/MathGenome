import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.Berge
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Directed.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.AlternatingReach

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Matching.Alternating

variable {V : Type u} [Fintype V] {G : SimpleGraph V} {L R : Set V}
  {M : Set (Sym2 V)} {a b c : V}

omit [Fintype V] in
lemma Bipartition.not_right (hB : Bipartition G L R) (ha : a ∈ L) : a ∉ R :=
  fun hr => Set.disjoint_left.mp hB.disjoint ha hr

omit [Fintype V] in
lemma Bipartition.not_left (hB : Bipartition G L R) (ha : a ∈ R) : a ∉ L :=
  fun hl => hB.not_right hl ha

lemma arc_oriented (e : Directed.Arc (searchDigraph G L R M) a b) :
    Oriented G L R M a b := by
  have h := e.val.property
  simpa only [show e.val.val.1 = a from e.property.1,
    show e.val.val.2 = b from e.property.2] using h

/-- Forgetting arc identities retains each directed dart's orientation. -/
def underlyingWalk {a b : V} (p : Directed.Walk (searchDigraph G L R M) a b) :
    G.Walk a b := by
  induction p with
  | nil => exact .nil
  | cons e p ih => exact .cons (arc_oriented e).1 ih

lemma underlyingWalk_oriented (p : Directed.Walk (searchDigraph G L R M) a b) :
    ∀ d ∈ (underlyingWalk p).darts, Oriented G L R M d.fst d.snd := by
  induction p with
  | nil => simp [underlyingWalk]
  | cons e p ih =>
    intro d hd
    simp only [underlyingWalk, SimpleGraph.Walk.darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact arc_oriented e
    · exact ih d hd

/-- Deleting repeated-vertex segments preserves oriented darts. -/
lemma exists_oriented_path (p : Directed.Walk (searchDigraph G L R M) a b) :
    ∃ q : G.Walk a b, q.IsPath ∧
      ∀ d ∈ q.darts, Oriented G L R M d.fst d.snd := by
  classical
  let q := underlyingWalk p
  exact ⟨q.bypass, q.bypass_isPath, fun d hd =>
    underlyingWalk_oriented p d (q.darts_bypass_subset_darts hd)⟩

/-- Along an oriented walk, the matching status alternates with the starting side. -/
lemma oriented_walk_alternates (hB : Bipartition G L R) (p : G.Walk a b)
    (hp : ∀ d ∈ p.darts, Oriented G L R M d.fst d.snd) :
    (a ∈ L → ∀ i < p.length,
      s(p.getVert i, p.getVert (i + 1)) ∈ M ↔ i % 2 = 1) ∧
    (a ∈ R → ∀ i < p.length,
      s(p.getVert i, p.getVert (i + 1)) ∈ M ↔ i % 2 = 0) := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    have hxy' : Oriented G L R M x y := hp ⟨⟨x, y⟩, hxy⟩ (by simp)
    have htail := ih (fun d hd => hp d (by simp [hd]))
    rcases hxy'.2 with ⟨hx, hy, hm⟩ | ⟨hx, hy, hm⟩
    · refine ⟨?_, fun hr => (hB.not_right hx hr).elim⟩
      intro _ i hi
      cases i with
      | zero => simpa using hm
      | succ i =>
        have hh := htail.2 hy i (by simpa using hi)
        simpa only [SimpleGraph.Walk.getVert_cons_succ,
          show (i + 1) % 2 = 1 ↔ i % 2 = 0 by omega] using hh
    · refine ⟨fun hl => (hB.not_left hx hl).elim, ?_⟩
      intro _ i hi
      cases i with
      | zero => simpa using hm
      | succ i =>
        have hh := htail.1 hy i (by simpa using hi)
        simpa only [SimpleGraph.Walk.getVert_cons_succ,
          show (i + 1) % 2 = 0 ↔ i % 2 = 1 by omega] using hh

/-- Search includes every unmatched left vertex by its empty directed walk. -/
lemma root_mem_leftReach (ha : a ∈ roots L M) : a ∈ leftReach G L R M :=
  ⟨ha.1, a, ha, ⟨Directed.Walk.nil a⟩⟩

lemma reached_step (ha : a ∈ reached G L R M) (hab : Oriented G L R M a b) :
    b ∈ reached G L R M := by
  obtain ⟨x, hx, ⟨p⟩⟩ := ha
  let e : Directed.Arc (searchDigraph G L R M) a b := ⟨⟨(a, b), hab⟩, rfl, rfl⟩
  exact ⟨x, hx, ⟨p.append (.cons e (.nil b))⟩⟩

lemma walk_last (p : Directed.Walk (searchDigraph G L R M) a b) :
    a = b ∨ ∃ c, Nonempty (Directed.Walk (searchDigraph G L R M) a c) ∧
      Oriented G L R M c b := by
  induction p with
  | nil => exact Or.inl rfl
  | @cons x y z e p ih =>
    rcases ih with rfl | ⟨c, ⟨q⟩, hc⟩
    · exact Or.inr ⟨x, ⟨.nil x⟩, arc_oriented e⟩
    · exact Or.inr ⟨c, ⟨.cons e q⟩, hc⟩

lemma reached_cases (ha : a ∈ reached G L R M) :
    a ∈ roots L M ∨ ∃ c, c ∈ reached G L R M ∧ Oriented G L R M c a := by
  obtain ⟨x, hx, ⟨p⟩⟩ := ha
  rcases walk_last p with rfl | ⟨c, hc, hor⟩
  · exact Or.inl hx
  · exact Or.inr ⟨c, ⟨x, hx, hc⟩, hor⟩

lemma reached_right_saturated (hB : Bipartition G L R) (hM : IsMatching G M)
    (hmax : ∀ N : Set (Sym2 V), IsMatching G N → Nat.card N ≤ Nat.card M)
    (hb : b ∈ rightReach G L R M) : Saturated M b := by
  by_contra hfree
  obtain ⟨a, ha, ⟨p⟩⟩ := hb.2
  obtain ⟨q, hq, hdir⟩ := exists_oriented_path p
  have hne : a ≠ b := fun he => hB.not_right ha.1 (he ▸ hb.1)
  have hpos : 0 < q.length := by
    exact SimpleGraph.Walk.not_nil_iff_lt_length.mp (fun hn => hne hn.eq)
  have haug : IsAugmentingPath G M q :=
    ⟨hM, hq, hpos, ha.2, hfree, (oriented_walk_alternates hB q hdir).1 ha.1,
      fun hm => hfree ⟨_, hm, Sym2.mem_mk_right _ _⟩⟩
  exact maximum_has_no_augmenting_path hM hmax ⟨a, b, q, haug⟩

/-- A reached matched left vertex was entered from its matching partner. -/
lemma left_partner_reached (hB : Bipartition G L R)
    (ha : a ∈ leftReach G L R M) (hsat : Saturated M a) :
    ∃ b ∈ rightReach G L R M, s(b, a) ∈ M := by
  rcases reached_cases ha.2 with hroot | ⟨b, hb, hor⟩
  · exact (hroot.2 hsat).elim
  · rcases hor.2 with ⟨_, har, _⟩ | ⟨hbr, _, hm⟩
    · exact (hB.not_right ha.1 har).elim
    · exact ⟨b, ⟨hbr, hb⟩, hm⟩

/-- Every matching partner of a reached right vertex lies in S minus U. -/
lemma right_partner_reached (hB : Bipartition G L R) (hM : IsMatching G M)
    (hb : b ∈ rightReach G L R M) (hba : s(b, a) ∈ M) :
    a ∈ leftReach G L R M \ roots L M := by
  have hadj : G.Adj b a := hM.1 hba
  have haL : a ∈ L := by
    rcases hB.crosses hadj with ⟨hbl, _⟩ | ⟨_, hal⟩
    · exact (hB.not_left hb.1 hbl).elim
    · exact hal
  refine ⟨⟨haL, reached_step hb.2 ⟨hadj, Or.inr ⟨hb.1, haL, hba⟩⟩⟩, ?_⟩
  exact fun hroot => hroot.2 ⟨_, hba, Sym2.mem_mk_right _ _⟩

/-- Matching partners define the required equivalence, with its edge witness. -/
lemma partner_equiv (hB : Bipartition G L R) (hM : IsMatching G M)
    (hsat : ∀ b ∈ rightReach G L R M, Saturated M b) :
    ∃ e : ↥(rightReach G L R M) ≃ ↥(leftReach G L R M \ roots L M),
      ∀ b, s(b.val, (e b).val) ∈ M := by
  classical
  have hp : ∀ b : ↥(rightReach G L R M),
      ∃ a : ↥(leftReach G L R M \ roots L M), s(b.val, a.val) ∈ M := by
    intro b
    obtain ⟨a, hba⟩ := (saturated_iff_neighbor M b.val).mp (hsat b.val b.property)
    exact ⟨⟨a, right_partner_reached hB hM b.property hba⟩, hba⟩
  choose f hf using hp
  have hunique := ((matching_iff_neighbors G M).mp hM).2
  have hinj : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    have hb : s((f b).val, b.val) ∈ M := by simpa only [Sym2.eq_swap] using hf b
    have hc : s((f b).val, c.val) ∈ M := by
      rw [hbc]
      simpa only [Sym2.eq_swap] using hf c
    exact hunique _ _ _ hb hc
  have hsurj : Function.Surjective f := by
    intro a
    have hasat : Saturated M a.val := by
      by_contra hfree
      exact a.property.2 ⟨a.property.1.1, hfree⟩
    obtain ⟨b, hb, hba⟩ := left_partner_reached hB a.property.1 hasat
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    exact hunique _ _ _ (hf ⟨b, hb⟩) hba
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- The reached right vertices are exactly the neighbors of the reached left vertices. -/
lemma rightReach_eq_neighbors (hB : Bipartition G L R) (hM : IsMatching G M) :
    rightReach G L R M = neighbors G R (leftReach G L R M) := by
  ext b
  constructor
  · intro hb
    rcases reached_cases hb.2 with hroot | ⟨a, ha, hor⟩
    · exact (hB.not_left hb.1 hroot.1).elim
    · rcases hor.2 with ⟨hal, _, _⟩ | ⟨_, hbl, _⟩
      · exact ⟨hb.1, a, ⟨hal, ha⟩, hor.1⟩
      · exact (hB.not_left hb.1 hbl).elim
  · rintro ⟨hbr, a, ha, hab⟩
    by_cases hm : s(a, b) ∈ M
    · have hasat : Saturated M a := ⟨_, hm, Sym2.mem_mk_left _ _⟩
      obtain ⟨c, hc, hca⟩ := left_partner_reached hB ha hasat
      have hac : s(a, c) ∈ M := by simpa only [Sym2.eq_swap] using hca
      have hcb : c = b := ((matching_iff_neighbors G M).mp hM).2 _ _ _ hac hm
      exact hcb ▸ hc
    · exact ⟨hbr, reached_step ha.2 ⟨hab, Or.inl ⟨ha.1, hbr, hm⟩⟩⟩

/-- Alternating reachability for every maximum matching, including empty parts
and an empty root set. -/
theorem alternating_reachability :
    Specs.FiniteCombinatorics.Graph.Matching.AlternatingReach.alternating_reachabilityType := by
  intro V _ G L R M hB hM hmax
  have hsat := fun b hb => reached_right_saturated hB hM hmax (b := b) hb
  exact ⟨rightReach_eq_neighbors hB hM, hsat, partner_equiv hB hM hsat⟩

end FiniteCombinatorics.Graph.Matching.Alternating
