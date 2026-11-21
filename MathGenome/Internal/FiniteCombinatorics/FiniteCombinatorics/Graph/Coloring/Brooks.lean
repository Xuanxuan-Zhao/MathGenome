import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.Bipartite
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.BrooksOrder
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.Brooks
import Mathlib.Data.Finset.Max

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Coloring
open SimpleGraph
open scoped Classical

abbrev maximumDegree : Specs.FiniteCombinatorics.Graph.Coloring.Brooks.maximumDegreeType :=
  Specs.FiniteCombinatorics.Graph.Coloring.Brooks.maximumDegreeValue

/-- The maximum includes every local degree; on the empty graph it is zero. -/
lemma degree_le_maximumDegree {V : Type u} [Finite V] (G : SimpleGraph V) (v : V) :
    FiniteCombinatorics.Graph.degree G v ≤ maximumDegree G := by
  classical
  letI := Fintype.ofFinite V
  exact Finset.le_sup (s := @Finset.univ V (Fintype.ofFinite V))
    (f := FiniteCombinatorics.Graph.degree G) (Finset.mem_univ v)

lemma maximumDegree_le {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (h : ∀ v, FiniteCombinatorics.Graph.degree G v ≤ k) : maximumDegree G ≤ k := by
  classical
  exact Finset.sup_le (fun v _ => h v)

section Greedy
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Extend a fixed partial coloring in increasing rank. Ties in the rank are
allowed: the local bound includes every neighbor of the same rank. -/
lemma coloring_extend_of_rank (k : ℕ) (s₀ : Finset V) (f₀ : V → Fin k)
    {R : Type*} [LinearOrder R] (r : V → R)
    (h₀ : ∀ x ∈ s₀, ∀ y ∈ s₀, G.Adj x y → f₀ x ≠ f₀ y)
    (hl : ∀ x ∉ s₀, ∀ f : V → Fin k, (∀ y ∈ s₀, f y = f₀ y) →
      (((G.neighborFinset x).filter (fun y => y ∈ s₀ ∨ r y ≤ r x)).image f).card < k) :
    ∃ c : G.Coloring (Fin k), ∀ x ∈ s₀, c x = f₀ x := by
  classical
  have aux : ∀ s : Finset V, Disjoint s s₀ →
      ∃ f : V → Fin k, (∀ x ∈ s₀, f x = f₀ x) ∧
        ∀ x ∈ s ∪ s₀, ∀ y ∈ s ∪ s₀, G.Adj x y → f x ≠ f y := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hdis
      by_cases hs : s.Nonempty
      · obtain ⟨x, hxs, hmax⟩ := s.exists_max_image r hs
        have hx₀ : x ∉ s₀ := Finset.disjoint_left.mp hdis hxs
        obtain ⟨f, hf, hp⟩ := ih (s.erase x) (Finset.erase_ssubset hxs)
          (hdis.mono_left (Finset.erase_subset _ _))
        let t := ((G.neighborFinset x).filter (fun y => y ∈ s₀ ∨ r y ≤ r x)).image f
        have ht : t.card < (Finset.univ : Finset (Fin k)).card := by
          simpa [t] using hl x hx₀ f hf
        obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card ht
        let f' := Function.update f x a
        have hsame (y : V) (hy : y ≠ x) : f' y = f y := by simp [f', hy]
        have hnew : f' x = a := by simp [f']
        have hav (y : V) (hy : y ∈ s ∪ s₀) (hxy : G.Adj x y) : a ≠ f y := by
          intro he
          apply ha
          apply Finset.mem_image.mpr
          refine ⟨y, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset x y).mpr hxy, ?_⟩, he.symm⟩
          rcases Finset.mem_union.mp hy with hy | hy
          · exact Or.inr (hmax y hy)
          · exact Or.inl hy
        refine ⟨f', ?_, ?_⟩
        · intro y hy
          rw [hsame y (fun he => hx₀ (he ▸ hy))]
          exact hf y hy
        · intro y hy z hz hyz
          by_cases hyx : y = x
          · subst y
            rw [hnew, hsame z hyz.ne.symm]
            exact hav z hz hyz
          by_cases hzx : z = x
          · subst z
            rw [hnew, hsame y hyx]
            exact (hav y hy hyz.symm).symm
          rw [hsame y hyx, hsame z hzx]
          apply hp y _ z _ hyz
          · rcases Finset.mem_union.mp hy with hy | hy
            · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hyx, hy⟩)
            · exact Finset.mem_union_right _ hy
          · rcases Finset.mem_union.mp hz with hz | hz
            · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzx, hz⟩)
            · exact Finset.mem_union_right _ hz
      · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        exact ⟨f₀, fun _ _ => rfl, by simpa using h₀⟩
  obtain ⟨f, hf, hp⟩ := aux (Finset.univ \ s₀) Finset.sdiff_disjoint
  refine ⟨SimpleGraph.Coloring.mk f (fun {x y} hxy => hp x ?_ y ?_ hxy), hf⟩ <;> simp

/-- A first step of a shortest walk moves strictly closer to its target. -/
lemma exists_neighbor_dist_lt (hc : G.Connected) (v root : V) (hv : v ≠ root) :
    ∃ w, G.Adj v w ∧ G.dist w root < G.dist v root := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v root
  cases p with
  | nil => exact (hv rfl).elim
  | cons hvw p =>
    refine ⟨_, hvw, ?_⟩
    have hd := G.dist_le p
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

/-- The rooted greedy observation from W59. The number of colors may be any
upper bound for the degrees, provided one specified vertex has smaller degree. -/
lemma colorable_of_degree_lt (hc : G.Connected) (k : ℕ) (root : V)
    (hd : ∀ v, G.degree v ≤ k) (hr : G.degree root < k) : G.Colorable k := by
  classical
  let f₀ : V → Fin k := fun _ => ⟨0, by omega⟩
  obtain ⟨c, _⟩ := coloring_extend_of_rank (G := G) (R := OrderDual ℕ) k ∅ f₀
    (fun v => (G.dist v root : OrderDual ℕ)) (by simp) (by
      intro v _ f _
      simp only [Finset.notMem_empty, false_or]
      by_cases hv : v = root
      · subst v
        exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans_lt hr
      · obtain ⟨w, hvw, hw⟩ := exists_neighbor_dist_lt hc v root hv
        have hss : ((G.neighborFinset v).filter
            (fun y => G.dist v root ≤ G.dist y root)) ⊂ G.neighborFinset v := by
          apply Finset.filter_ssubset.mpr
          exact ⟨w, (G.mem_neighborFinset v w).mpr hvw, by change ¬ G.dist v root ≤ G.dist w root; omega⟩
        exact (Finset.card_image_le.trans_lt (Finset.card_lt_card hss)).trans_le (hd v))
  exact ⟨c⟩

set_option maxHeartbeats 800000 in
/-- If two nonadjacent neighbors of the last vertex can be deleted while
preserving connectivity, give them the same initial color and color inward. -/
lemma colorable_of_two_initial_vertices (k : ℕ) (hk : 0 < k)
    (root a b : V) (hab : a ≠ b) (hra : G.Adj root a) (hrb : G.Adj root b)
    (hnab : ¬ G.Adj a b)
    (hc : (G.induce {x | x ≠ a ∧ x ≠ b}).Connected)
    (hd : ∀ v, G.degree v ≤ k) : G.Colorable k := by
  classical
  let K := G.induce {x | x ≠ a ∧ x ≠ b}
  let root' : {x : V // x ≠ a ∧ x ≠ b} := ⟨root, hra.ne, hrb.ne⟩
  let s₀ : Finset V := {a, b}
  let f₀ : V → Fin k := fun _ => ⟨0, hk⟩
  let d (x : V) : ℕ := if hx : x ≠ a ∧ x ≠ b then K.dist ⟨x, hx⟩ root' else 0
  have hdkeep (x : V) (hx : x ≠ a ∧ x ≠ b) : d x = K.dist ⟨x, hx⟩ root' := by
    simp [d, hx]
  obtain ⟨c, _⟩ := coloring_extend_of_rank (G := G) (R := OrderDual ℕ) k s₀ f₀ d (by
    intro x hx y hy hxy
    simp only [s₀, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (G.irrefl hxy).elim
    · exact (hnab hxy).elim
    · exact (hnab hxy.symm).elim
    · exact (G.irrefl hxy).elim) (by
    intro x hx f hf
    have hxkeep : x ≠ a ∧ x ≠ b := by simpa [s₀] using hx
    by_cases hxr : x = root
    · subst x
      have heq : f a = f b := (hf a (by simp [s₀])).trans (hf b (by simp [s₀])).symm
      have hlt : ((G.neighborFinset root).image f).card < (G.neighborFinset root).card := by
        apply lt_of_le_of_ne Finset.card_image_le
        intro he
        have hinj := Finset.card_image_iff.mp he
        exact hab (hinj ((G.mem_neighborFinset root a).mpr hra)
          ((G.mem_neighborFinset root b).mpr hrb) heq)
      exact (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))).trans_lt
        (hlt.trans_le (hd root))
    · obtain ⟨y, hxy, hy⟩ := exists_neighbor_dist_lt hc ⟨x, hxkeep⟩ root'
        (fun he => hxr (congrArg Subtype.val he))
      have hykeep : y.val ≠ a ∧ y.val ≠ b := y.property
      have hys : y.val ∉ s₀ := by simp [s₀, hykeep]
      have hdr : d y.val < d x := by rw [hdkeep _ hykeep, hdkeep _ hxkeep]; exact hy
      have hss : ((G.neighborFinset x).filter (fun y => y ∈ s₀ ∨
          @LE.le (OrderDual ℕ) _ (d y) (d x))) ⊂ G.neighborFinset x := by
        apply Finset.filter_ssubset.mpr
        exact ⟨y.val, (G.mem_neighborFinset x y.val).mpr hxy, by
          change ¬ (y.val ∈ s₀ ∨ d x ≤ d y.val)
          exact not_or.mpr ⟨hys, Nat.not_le.mpr hdr⟩⟩
      exact (Finset.card_image_le.trans_lt (Finset.card_lt_card hss)).trans_le (hd x))
  exact ⟨c⟩

/-- In a connected graph of maximum degree two, a copy of a cycle uses
all vertices and all edges. -/
lemma cycle_copy_iso (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 2)
    (n : ℕ) (hn : 3 ≤ n) (f : (cycleGraph n).Copy G) :
    Nonempty (cycleGraph n ≃g G) := by
  classical
  have hdeg (x : Fin n) : (cycleGraph n).degree x = 2 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    have hn' : n = m + 3 := by omega
    clear hm
    subst n
    exact cycleGraph_degree_three_le
  have hlocal (x : Fin n) (y : V) (hxy : G.Adj (f x) y) :
      ∃ z : Fin n, (cycleGraph n).Adj x z ∧ f z = y := by
    have hsub : ((cycleGraph n).neighborFinset x).image f ⊆ G.neighborFinset (f x) := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact (G.mem_neighborFinset _ _).mpr (f.toHom.map_adj ((cycleGraph n).mem_neighborFinset _ _ |>.mp hw))
    have hcard : (((cycleGraph n).neighborFinset x).image f).card = 2 := by
      rw [Finset.card_image_of_injective _ (show Function.Injective (fun x => f x) from f.injective)]
      exact hdeg x
    have heq := Finset.eq_of_subset_of_card_le hsub (show
        (G.neighborFinset (f x)).card ≤ (((cycleGraph n).neighborFinset x).image f).card by
      rw [hcard]; exact hd (f x))
    have hy := (G.mem_neighborFinset _ _).mpr hxy
    rw [← heq] at hy
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hy
    exact ⟨z, (cycleGraph n).mem_neighborFinset _ _ |>.mp hz, he⟩
  let x₀ : Fin n := ⟨0, by omega⟩
  have hsurj : Function.Surjective f := by
    intro y
    exact reachable_mem_of_adj_closed
      (s := Set.range f) (fun x hx z hxz => by
        obtain ⟨w, rfl⟩ := hx
        obtain ⟨w', _, hw'⟩ := hlocal w z hxz
        exact ⟨w', hw'⟩) (hc (f x₀) y) ⟨x₀, rfl⟩
  refine ⟨{
    toEquiv := Equiv.ofBijective (fun x => f x) ⟨f.injective, hsurj⟩
    map_rel_iff' := ?_ }⟩
  intro x y
  constructor
  · intro hxy
    obtain ⟨z, hz, he⟩ := hlocal x (f y) hxy
    exact f.injective he ▸ hz
  · exact f.toHom.map_adj

/-- The small-degree case uses the literal cycle exclusion: any odd cycle
would saturate the connected graph of maximum degree at most two. -/
lemma colorable_two_of_degree_le_two (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 2)
    (hodd : ∀ n : ℕ, 3 ≤ n → Odd n → ¬ Nonempty (G ≃g cycleGraph n)) :
    G.Colorable 2 := by
  apply bipartite_two_coloring G
  apply (bipartite_iff_no_odd_cycle G).mpr
  intro v p hp
  have hlen := p.property.three_le_length
  obtain ⟨f⟩ := (cycleGraph_isContained_iff (by omega : 2 < p.val.length)).mpr
    ⟨v, p.val, p.property, rfl⟩
  obtain ⟨e⟩ := cycle_copy_iso hc hd p.val.length hlen f
  exact hodd p.val.length hlen hp ⟨e.symm⟩

open FiniteCombinatorics.Graph.Blocks

/-- Every component left after deleting a vertex of a connected graph contains
an original neighbor of that vertex. -/
lemma neighbor_in_deleted_component (hc : G.Connected) (v : V)
    (c : (deleteVertex G v).ConnectedComponent) :
    ∃ a : {x : V // x ≠ v}, G.Adj v a.val ∧ (deleteVertex G v).connectedComponentMk a = c := by
  obtain ⟨x, rfl⟩ := c.exists_rep
  obtain ⟨a, hva, hax⟩ := exists_neighbor_reachable_after_delete v ⟨x.val, hc v x.val, x.property⟩
  let f : componentDeleteVertex G v →g deleteVertex G v := {
    toFun := fun a => ⟨a.val, a.property.2⟩
    map_rel' := fun h => h }
  exact ⟨f a, hva, ConnectedComponent.sound (hax.map f)⟩

set_option maxHeartbeats 1200000 in
/-- Color the pieces attached at a cut vertex and permute their colors to agree
there. No regularity or minimum-degree hypothesis is needed. -/
lemma colorable_of_disconnected_delete (hc : G.Connected) (k : ℕ) (hk : 0 < k)
    (v : V) (hdis : ¬ (deleteVertex G v).Preconnected)
    (hd : ∀ x, G.degree x ≤ k) : G.Colorable k := by
  classical
  let K := deleteVertex G v
  let S (c : K.ConnectedComponent) : Set V :=
    {x | x = v ∨ ∃ hx : x ≠ v, K.connectedComponentMk ⟨x, hx⟩ = c}
  let H (c : K.ConnectedComponent) := G.induce (S c)
  let root (c : K.ConnectedComponent) : S c := ⟨v, Or.inl rfl⟩
  have hconn (c : K.ConnectedComponent) : (H c).Connected := by
    obtain ⟨a, hva, ha⟩ := neighbor_in_deleted_component hc v c
    have hreach (x : S c) : (H c).Reachable (root c) x := by
      rcases x.property with hx | ⟨hx, hxc⟩
      · have he : x = root c := Subtype.ext hx
        rw [he]
      · let f : c.toSimpleGraph →g H c := {
          toFun := fun y => ⟨y.val.val, Or.inr ⟨y.val.property, (c.mem_supp_iff _).mp y.property⟩⟩
          map_rel' := fun h => h }
        have hr := c.reachable_toSimpleGraph ((c.mem_supp_iff a).mpr ha)
          ((c.mem_supp_iff _).mpr hxc)
        exact (show (H c).Adj (root c) (f ⟨a, (c.mem_supp_iff a).mpr ha⟩) from hva).reachable.trans
          (hr.map f)
    exact {
      nonempty := ⟨root c⟩
      preconnected := fun x y => (hreach x).symm.trans (hreach y) }
  have hother (c : K.ConnectedComponent) : ∃ d : K.ConnectedComponent, d ≠ c := by
    obtain ⟨x, y, hxy⟩ : ∃ x y, ¬ K.Reachable x y := by
      simpa only [SimpleGraph.Preconnected, not_forall] using hdis
    have hne : K.connectedComponentMk x ≠ K.connectedComponentMk y :=
      fun he => hxy (ConnectedComponent.exact he)
    by_cases hx : K.connectedComponentMk x = c
    · exact ⟨K.connectedComponentMk y, fun hy => hne (hx.trans hy.symm)⟩
    · exact ⟨K.connectedComponentMk x, hx⟩
  have hrootdeg (c : K.ConnectedComponent) : (H c).degree (root c) < k := by
    obtain ⟨d, hdc⟩ := hother c
    obtain ⟨a, hva, ha⟩ := neighbor_in_deleted_component hc v d
    let f : (H c).neighborSet (root c) → G.neighborSet v :=
      fun x => ⟨x.val.val, x.property⟩
    have hfi : Function.Injective f := by
      intro x y he
      have hval : x.val.val = y.val.val := congrArg (fun z : G.neighborSet v => z.val) he
      exact Subtype.ext (Subtype.ext hval)
    have hfn : ¬ Function.Surjective f := by
      intro hs
      obtain ⟨x, he⟩ := hs ⟨a.val, hva⟩
      have hxval : x.val.val = a.val := congrArg Subtype.val he
      have hax : a.val ∈ S c := hxval ▸ x.val.property
      rcases hax with hav | ⟨hav, hac⟩
      · exact a.property hav
      · exact hdc (ha.symm.trans hac)
    have hlt := Fintype.card_lt_of_injective_not_surjective f hfi hfn
    have heq : (H c).degree (root c) < G.degree v := by
      simpa only [SimpleGraph.card_neighborSet_eq_degree] using hlt
    exact heq.trans_le (hd v)
  let zero : Fin k := ⟨0, hk⟩
  have hcolors (c : K.ConnectedComponent) :
      ∃ C : (H c).Coloring (Fin k), C (root c) = zero := by
    obtain ⟨C⟩ := colorable_of_degree_lt (hconn c) k (root c)
      (fun x => ((SimpleGraph.Embedding.induce (S c)).toCopy.degree_le x).trans (hd x.val))
      (hrootdeg c)
    let e := Equiv.swap (C (root c)) zero
    refine ⟨SimpleGraph.Coloring.mk (fun x => e (C x)) (fun {x y} h => e.injective.ne (C.valid h)), ?_⟩
    exact Equiv.swap_apply_left _ _
  choose C hC using hcolors
  have htransport (c d : K.ConnectedComponent) (he : c = d) (z : V)
      (hz : z ∈ S c) (hz' : z ∈ S d) : C c ⟨z, hz⟩ = C d ⟨z, hz'⟩ := by
    subst d
    rfl
  let f (x : V) : Fin k := if hx : x = v then zero else
    C (K.connectedComponentMk ⟨x, hx⟩) ⟨x, Or.inr ⟨hx, rfl⟩⟩
  refine ⟨SimpleGraph.Coloring.mk f ?_⟩
  intro x y hxy
  by_cases hx : x = v
  · subst x
    have hy : y ≠ v := hxy.ne.symm
    have hvalid := (C (K.connectedComponentMk ⟨y, hy⟩)).valid
      (show (H (K.connectedComponentMk ⟨y, hy⟩)).Adj
        (root (K.connectedComponentMk ⟨y, hy⟩)) ⟨y, Or.inr ⟨hy, rfl⟩⟩ from hxy)
    simpa only [f, dite_eq_left rfl, dite_eq_right hy, hC] using hvalid
  by_cases hy : y = v
  · subst y
    have hvalid := (C (K.connectedComponentMk ⟨x, hx⟩)).valid
      (show (H (K.connectedComponentMk ⟨x, hx⟩)).Adj
        ⟨x, Or.inr ⟨hx, rfl⟩⟩ (root (K.connectedComponentMk ⟨x, hx⟩)) from hxy)
    simpa only [f, dite_eq_left rfl, dite_eq_right hx, hC] using hvalid
  · have he : K.connectedComponentMk ⟨y, hy⟩ = K.connectedComponentMk ⟨x, hx⟩ :=
      ConnectedComponent.sound (show K.Adj ⟨y, hy⟩ ⟨x, hx⟩ from hxy.symm).reachable
    simp only [f, dite_eq_right hx, dite_eq_right hy]
    rw [htransport _ _ he y _ (Or.inr ⟨hy, he⟩)]
    exact (C (K.connectedComponentMk ⟨x, hx⟩)).valid hxy

end Greedy

/-- W59, with all connected finite graphs covered by the literal exclusions. -/
theorem brooks : Specs.FiniteCombinatorics.Graph.Coloring.Brooks.brooksType.{u} := by
  intro V _ G hc hn hodd
  classical
  letI := Fintype.ofFinite V
  let k := maximumDegree G
  have hd (x : V) : G.degree x ≤ k := by
    rw [← FiniteCombinatorics.Graph.degree_mathlib G x]
    exact degree_le_maximumDegree G x
  apply (chromaticNumber_minimum G).2 k
  change G.Colorable k
  obtain ⟨v, a, b, hab, hva, hvb, _⟩ := exists_nonadjacent_neighbors hc hn
  have htwo : 2 ≤ k := by
    have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset v := by
      intro x hx
      rcases (show x = a ∨ x = b by simpa using hx) with rfl | rfl
      · exact (G.mem_neighborFinset _ _).mpr hva
      · exact (G.mem_neighborFinset _ _).mpr hvb
    have hcard := Finset.card_le_card hsub
    have hdeg : 2 ≤ G.degree v := by simpa [hab] using hcard
    exact hdeg.trans (hd v)
  by_cases hsmall : k ≤ 2
  · have heq : k = 2 := by omega
    rw [heq]
    exact colorable_two_of_degree_le_two hc (fun x => (hd x).trans hsmall) hodd
  have hk : 3 ≤ k := by omega
  by_cases hlow : ∃ x, G.degree x < k
  · obtain ⟨x, hx⟩ := hlow
    exact colorable_of_degree_lt hc k x hd hx
  have hreg (x : V) : G.degree x = k := by
    have hl := not_exists.mp hlow x
    have hu := hd x
    omega
  by_cases hdel : ∀ x : V, (FiniteCombinatorics.Graph.Blocks.deleteVertex G x).Preconnected
  · have hcard : 3 ≤ Nat.card V := by
      rw [Nat.card_eq_fintype_card]
      have hlt := G.degree_lt_card_verts v
      have heq := hreg v
      omega
    haveI : Nontrivial V := ⟨⟨v, a, hva.ne⟩⟩
    have htwoConn : FiniteCombinatorics.Graph.Blocks.TwoConnected G := by
      refine ⟨hcard, hc, ?_⟩
      intro x
      obtain ⟨y, hy⟩ := exists_ne x
      exact { nonempty := ⟨⟨y, hy⟩⟩, preconnected := hdel x }
    obtain ⟨r, a, b, hab, hra, hrb, hnab, hconn⟩ := two_initial_vertices G htwoConn hn (by
      intro x
      rw [FiniteCombinatorics.Graph.degree_mathlib G x, hreg]
      exact hk)
    exact colorable_of_two_initial_vertices k (by omega) r a b hab hra hrb hnab hconn hd
  · push Not at hdel
    obtain ⟨x, hx⟩ := hdel
    exact colorable_of_disconnected_delete hc k (by omega) x hx hd

end FiniteCombinatorics.Graph.Coloring
