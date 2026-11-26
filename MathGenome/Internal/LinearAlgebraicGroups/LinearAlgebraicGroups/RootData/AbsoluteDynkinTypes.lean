import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.EuclideanComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DynkinExhaustion

noncomputable section

universe u

open Set Module LieAlgebrasAndRepresentations
open LinearAlgebraicGroups.Specs.AbsoluteDynkinTypes

namespace LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

private theorem integralDiagram_edges {ι : Type*} (A : Matrix ι ι ℤ) (i j : ι) :
    (integralDiagram A).edges i j = (@ite _ (i = j) (Classical.propDecidable _) 0
      (A i j * A j i).toNat) := rfl

private theorem integralDiagram_arrow {ι : Type*} (A : Matrix ι ι ℤ) (i j : ι) :
    (integralDiagram A).arrow i j ↔ i ≠ j ∧ A j i < A i j := Iff.rfl

private theorem cartan_diagram_eq {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {R : Set E} {v : E} {b : Basis ι ℝ E}
    (hR : IsRootSystem R) (hv : RootRegular R v) (hb : IsSimpleBasis R v b)
    {A : Matrix ι ι ℤ} (hA : cartanMatrix b = A.map fun z : ℤ => (z : ℝ)) :
    dynkinDiagram b = integralDiagram A := by
  classical
  have hentry i j : cartanMatrix b i j = (A i j : ℝ) := congrFun (congrFun hA i) j
  unfold dynkinDiagram integralDiagram
  apply congrArg₂ DynkinDiagram.mk
  · funext i j
    by_cases h : i = j
    · subst j
      simp only [ite_true]
    rw [hentry, hentry, ← Int.cast_mul, Int.floor_intCast]
  · funext i j
    apply propext
    by_cases h : i = j
    · subst j
      simp
    change (dynkinDiagram b).arrow i j ↔ _
    rw [dynkin_arrow_iff_cartan_lt hR hv hb h, hentry, hentry, Int.cast_lt]
    simp [h]

private def admissiblePair (a b : ℤ) : Prop :=
  (a = 0 ∧ b = 0) ∨ (a = -1 ∧ b = -1) ∨ (a = -1 ∧ b = -2) ∨
    (a = -2 ∧ b = -1) ∨ (a = -1 ∧ b = -3) ∨ (a = -3 ∧ b = -1)

private theorem admissiblePair_cast {a b : ℤ} (h :
    ((a : ℝ), (b : ℝ)) ∈
      ({(0,0),(-1,-1),(-1,-2),(-2,-1),(-1,-3),(-3,-1)} : Set (ℝ × ℝ))) :
    admissiblePair a b := by
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at h
  unfold admissiblePair
  exact_mod_cast h

private theorem e_diagonal (n : ℕ) (i : Fin n) : CartanMatrix.E n i i = 2 := by
  simp [CartanMatrix.E, Matrix.of_apply]

private theorem e_admissible (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    admissiblePair (CartanMatrix.E n i j) (CartanMatrix.E n j i) := by
  have hsym : CartanMatrix.E n j i = CartanMatrix.E n i j :=
    congrFun (congrFun (CartanMatrix.E_isSymm n).eq i) j
  rw [hsym]
  simp only [CartanMatrix.E, Matrix.of_apply]
  simp only [if_neg h]
  split_ifs <;> simp [admissiblePair]

private theorem model_diagonal (t : FiniteDynkinType) (i : Fin t.rank) : t.cartan i i = 2 := by
  cases t with
  | A n hn => exact congrFun (CartanMatrix.A_diag n) i
  | B n hn => exact CartanMatrix.C_diag n i
  | C n hn => exact CartanMatrix.B_diag n i
  | D n hn => exact CartanMatrix.D_diag n i
  | E6 => exact e_diagonal 6 i
  | E7 => exact e_diagonal 7 i
  | E8 => exact e_diagonal 8 i
  | F4 => change Fin 4 at i; fin_cases i <;> decide
  | G2 => change Fin 2 at i; fin_cases i <;> decide

private theorem model_admissible (t : FiniteDynkinType) (i j : Fin t.rank) (h : i ≠ j) :
    admissiblePair (t.cartan i j) (t.cartan j i) := by
  cases t with
  | A n hn =>
    change Fin n at i j
    change admissiblePair (CartanMatrix.A n i j) (CartanMatrix.A n j i)
    simp only [CartanMatrix.A, Matrix.of_apply]
    unfold admissiblePair
    split_ifs <;> omega
  | B n hn =>
    change Fin n at i j
    change admissiblePair (CartanMatrix.C n i j) (CartanMatrix.C n j i)
    simp only [CartanMatrix.C, Matrix.of_apply]
    unfold admissiblePair
    split_ifs <;> omega
  | C n hn =>
    change Fin n at i j
    change admissiblePair (CartanMatrix.B n i j) (CartanMatrix.B n j i)
    simp only [CartanMatrix.B, Matrix.of_apply]
    unfold admissiblePair
    split_ifs <;> omega
  | D n hn =>
    change Fin n at i j
    change admissiblePair (CartanMatrix.D n i j) (CartanMatrix.D n j i)
    have hsym : CartanMatrix.D n j i = CartanMatrix.D n i j :=
      congrFun (congrFun (CartanMatrix.D_transpose n) i) j
    rw [hsym]
    simp only [CartanMatrix.D, Matrix.of_apply]
    unfold admissiblePair
    split_ifs <;> omega
  | E6 => exact e_admissible 6 i j h
  | E7 => exact e_admissible 7 i j h
  | E8 => exact e_admissible 8 i j h
  | F4 =>
    change Fin 4 at i j
    unfold admissiblePair
    fin_cases i <;> fin_cases j <;> first | exact (h rfl).elim | decide
  | G2 =>
    change Fin 2 at i j
    unfold admissiblePair
    fin_cases i <;> fin_cases j <;> first | exact (h rfl).elim | decide

private theorem entry_eq_of_oriented_edge {a b c d : ℤ}
    (h₁ : admissiblePair a b) (h₂ : admissiblePair c d)
    (he : (a * b).toNat = (c * d).toNat) (ha : b < a ↔ d < c) :
    a = c := by
  unfold admissiblePair at h₁ h₂
  rcases h₁ with h | h | h | h | h | h <;> rcases h with ⟨rfl,rfl⟩ <;>
    rcases h₂ with h | h | h | h | h | h <;> rcases h with ⟨rfl,rfl⟩ <;>
    first | rfl | (norm_num at he <;> norm_num at ha)

private theorem classifyCartanOfRootSystem {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {R : Set E} {v : E} {b : Basis ι ℝ E}
    (hR : IsRootSystem R) (hv : RootRegular R v) (hb : IsSimpleBasis R v b)
    {A : Matrix ι ι ℤ} (hA : cartanMatrix b = A.map fun z : ℤ => (z : ℝ))
    (hc : (integralDiagram A).IsConnected) : ∃ t, HasDynkinType A t := by
  have hdiag := cartan_diagram_eq hR hv hb hA
  obtain ⟨t, e, hedges, harrows⟩ := dynkin_exhaustion _ hR v hv b hb (by rw [hdiag]; exact hc)
  refine ⟨t, e, fun i j => ?_⟩
  have hentry i j : cartanMatrix b i j = (A i j : ℝ) :=
    congrFun (congrFun hA i) j
  by_cases hij : i = j
  · subst j
    rw [model_diagonal]
    have h := cartan_diagonal _ hR v hv b hb i
    rw [hentry] at h
    exact_mod_cast h
  have heij : e i ≠ e j := fun h => hij (e.injective h)
  have he := hedges i j
  have ha := harrows i j
  rw [hdiag, integralDiagram_edges, if_neg hij] at he
  rw [hdiag, integralDiagram_arrow] at ha
  change _ = (if e i = e j then 0 else (t.cartan (e i) (e j) * t.cartan (e j) (e i)).toNat) at he
  change (_ ∧ _) ↔ (e i ≠ e j ∧ t.cartan (e j) (e i) < t.cartan (e i) (e j)) at ha
  rw [if_neg heij] at he
  have ha' : A j i < A i j ↔ t.cartan (e j) (e i) < t.cartan (e i) (e j) :=
    ⟨fun h => (ha.mp ⟨hij, h⟩).2, fun h => (ha.mpr ⟨heij, h⟩).2⟩
  have hp := cartan_pair_values hR hv hb hij
  rw [hentry, hentry] at hp
  exact entry_eq_of_oriented_edge (admissiblePair_cast hp) (model_admissible t _ _ heij) he ha'

theorem connectedCartanClassification : ConnectedCartanClassification := by
  intro ι X Y _ _ _ _ _ _ _ P _ B hc
  obtain ⟨_, _, _, _, _, metric, h⟩ := euclideanComparison P B
  letI := metric.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore metric.toCore
  obtain ⟨_, _, _, hR, _, _, hv, _, _, _, hb, hA, _⟩ := h
  exact classifyCartanOfRootSystem hR hv hb hA hc

theorem rankTwoCoincidence : RankTwoCoincidence := by
  refine ⟨Equiv.swap (0 : Fin 2) (1 : Fin 2), ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem cartanTypeUniqueness : CartanTypeUniqueness := by
  rintro ι A t s ⟨e, he⟩ ⟨f, hf⟩
  let g := e.symm.trans f
  have hg (i j : Fin t.rank) : t.cartan i j = s.cartan (g i) (g j) := by
    simpa [g] using (he (e.symm i) (e.symm j)).symm.trans (hf (e.symm i) (e.symm j))
  apply dynkin_uniqueness t s
  refine ⟨g, ?_, ?_⟩
  · intro i j
    change (if i = j then 0 else (t.cartan i j * t.cartan j i).toNat) =
      (if g i = g j then 0 else (s.cartan (g i) (g j) * s.cartan (g j) (g i)).toNat)
    by_cases h : i = j
    · subst j; simp
    · rw [ite_eq_right h, ite_eq_right (fun he => h (g.injective he)), hg, hg]
  · intro i j
    change (i ≠ j ∧ t.cartan j i < t.cartan i j) ↔
      (g i ≠ g j ∧ s.cartan (g j) (g i) < s.cartan (g i) (g j))
    rw [hg, hg, ne_eq, ne_eq, g.apply_eq_iff_eq]

private theorem d4_entry (i j : Fin 4) :
    CartanMatrix.D 4 i j = if i = j then 2 else if i = 1 ∨ j = 1 then -1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide

theorem d4Permutations : D4Permutations := by
  intro σ
  constructor
  · intro h
    by_contra hn
    let j : Fin 4 := if σ 0 = 1 then 2 else 0
    have hj : j ≠ 1 := by dsimp [j]; split_ifs <;> decide
    have hσj : σ j ≠ 1 := by
      dsimp [j]
      split_ifs with h0
      · rw [← h0]
        exact fun h' => (by decide : (2 : Fin 4) ≠ 0) (σ.injective h')
      · exact h0
    have hne : σ 1 ≠ σ j := fun h' => hj (σ.injective h').symm
    have hs := h (1 : Fin 4) j
    change CartanMatrix.D 4 1 j = CartanMatrix.D 4 (σ 1) (σ j) at hs
    rw [d4_entry 1 j, d4_entry (σ 1) (σ j)] at hs
    simp [hj.symm, hne, hn, hσj] at hs
  · intro h
    intro i j
    change Fin 4 at i j
    have hσ (i : Fin 4) : σ i = 1 ↔ i = 1 :=
      ⟨fun he => σ.injective (he.trans h.symm), fun he => (congrArg σ he).trans h⟩
    change CartanMatrix.D 4 i j = CartanMatrix.D 4 (σ i) (σ j)
    rw [d4_entry i j, d4_entry (σ i) (σ j)]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, fun he => hij (σ.injective he), hσ]

theorem d4ActionDichotomy : D4ActionDichotomy := by
  classical
  intro H hH
  have hcenter (σ : Equiv.Perm (Fin 4)) (hσ : σ ∈ H) : σ 1 = 1 :=
    (d4Permutations σ).mp (hH σ hσ)
  have houter (σ : Equiv.Perm (Fin 4)) (hσ : σ ∈ H) (i : D4Outer) : σ i.val ≠ 1 := by
    exact fun h => i.property (σ.injective (h.trans (hcenter σ hσ).symm))
  constructor
  · rintro ⟨i, hi⟩ h
    let j : D4Outer := ⟨if i.val = 0 then 2 else 0, by split_ifs <;> decide⟩
    have hji : j.val ≠ i.val := by
      dsimp [j]
      split_ifs with h0
      · rw [h0]; decide
      · exact Ne.symm h0
    obtain ⟨σ, hσ, hmove⟩ := h i j
    exact hji (hmove.symm.trans (hi σ hσ))
  · contrapose!
    intro h
    intro i j
    by_contra! hij
    obtain ⟨σ, hσ, hσi⟩ := h i
    obtain ⟨τ, hτ, hτj⟩ := h j
    have hij' : i.val ≠ j.val := by simpa using hij 1 H.one_mem
    have hσj := hij σ hσ
    have hτi : τ j.val ≠ i.val := by
      intro he
      exact hij τ⁻¹ (H.inv_mem hτ) (by simpa [← he])
    have hστ : σ i.val ≠ τ j.val := by
      intro he
      exact hij (τ⁻¹ * σ) (H.mul_mem (H.inv_mem hτ) hσ)
        (by change τ.symm (σ i.val) = j.val; rw [he, τ.symm_apply_apply])
    have hi := i.property
    have hj := j.property
    have hk := houter σ hσ i
    have hl := houter τ hτ j
    simp only [← Fin.val_ne_iff] at hi hj hk hl hij' hσi hτj hσj hτi hστ
    omega

theorem d4ActionOrder : D4ActionOrder := by
  intro H hH
  constructor
  · rintro ⟨⟨i, hOuter⟩, hi⟩
    change ∀ σ ∈ H, σ i = i at hi
    let V := {j : Fin 4 // j ≠ 1 ∧ j ≠ i}
    have hV : Fintype.card V = 2 := by
      dsimp [V]
      fin_cases i <;> first | exact False.elim (hOuter rfl) | decide
    have hne (σ : H) (j b : Fin 4) (hb : σ.val b = b) : σ.val j ≠ b ↔ j ≠ b :=
      ⟨fun h he => h ((congrArg σ.val he).trans hb),
        fun h he => h (σ.val.injective (he.trans hb.symm))⟩
    let restrict : H → Equiv.Perm V := fun σ => σ.val.subtypePerm fun j =>
      and_congr (hne σ j 1 ((d4Permutations σ.val).mp (hH σ.val σ.property)))
        (hne σ j i (hi σ.val σ.property))
    have hinj : Function.Injective restrict := by
      intro σ τ h
      apply Subtype.ext
      apply Equiv.ext
      intro j
      by_cases h₁ : j = 1
      · subst j
        rw [(d4Permutations σ.val).mp (hH σ.val σ.property),
          (d4Permutations τ.val).mp (hH τ.val τ.property)]
      by_cases h₂ : j = i
      · rw [h₂, hi σ.val σ.property, hi τ.val τ.property]
      · exact congrArg (fun e : Equiv.Perm V => (e ⟨j, h₁, h₂⟩).val) h
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, hV] using
      Nat.card_le_card_of_injective restrict hinj
  · intro h
    apply (d4ActionDichotomy H hH).mpr
    intro ht
    let v : D4Outer := ⟨0, by decide⟩
    let eval : H → D4Outer := fun σ => ⟨σ.val v.val, fun he =>
      v.property (σ.val.injective (he.trans ((d4Permutations σ.val).mp
        (hH σ.val σ.property)).symm))⟩
    have hsurj : Function.Surjective eval := by
      intro w
      obtain ⟨σ, hσ, he⟩ := ht v w
      exact ⟨⟨σ, hσ⟩, Subtype.ext he⟩
    have hcard : Nat.card D4Outer = 3 := by
      change Nat.card {i : Fin 4 // i ≠ 1} = 3
      rw [Nat.card_eq_fintype_card]
      decide
    have hc := Nat.card_le_card_of_surjective eval hsurj
    omega

theorem d4VectorRelabelling : D4VectorRelabelling := by
  intro i
  refine ⟨Equiv.swap i.val 0, (d4Permutations _).mpr ?_, Equiv.swap_apply_left _ _⟩
  exact Equiv.swap_apply_of_ne_of_ne i.property.symm (by decide)

theorem d4OuterWeights : D4OuterWeights := by
  unfold D4OuterWeights
  refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  all_goals fin_cases i <;> try fin_cases j
  all_goals
    norm_num [-inner_self_eq_norm_sq_to_K, D4Cartan, FiniteDynkinType.cartan, CartanMatrix.D,
      Matrix.of_apply, Fin.ext_iff,
      ClassicalCoordinates.simpleD, ClassicalCoordinates.epsilon, rootCartan, Pi.single_apply,
      inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, real_inner_smul_left,
      EuclideanSpace.inner_single_left, PiLp.single_apply, PiLp.sub_apply, PiLp.add_apply]


theorem cartanCoordinates : CartanCoordinates := by
  classical
  intro ι X Y κ _ _ _ _ _ P _ B h A e he
  have hspan : Submodule.span ℤ (range fun i : B.support => P.coroot i.val) = ⊤ := by
    change Submodule.span ℤ (range fun i : (↑B.support : Set ι) => P.coroot i.val) = ⊤
    rw [← image_eq_range, B.span_int_coroot_support, h]
  let c := (Basis.mk B.linearIndepOn_coroot hspan.ge).reindex e
  have hc (i : κ) : c i = P.coroot (e.symm i).val := by simp [c]
  let x := P.toLinearMap.toPerfPair.trans c.dualBasis.equivFun
  have hx (a : X) (i : κ) : x a i = P.toLinearMap a (c i) := by
    exact Basis.dualBasis_equivFun c _ _
  have hp (a : X) (b : Y) :
      P.toLinearMap a b = ∑ i, c.equivFun b i * x a i := by
    calc
      _ = P.toLinearMap a (∑ i, c.repr b i • c i) :=
        congrArg (P.toLinearMap a) (c.sum_repr b).symm
      _ = _ := by simp only [map_sum, map_smul, Int.zsmul_eq_mul, Basis.equivFun_apply, hx]
  have hsimple (i : κ) : x (P.root (e.symm i).val) = simpleCharacter A i := by
    funext j
    rw [hx, hc]
    simpa [simpleCharacter, integralCartan] using he (e.symm j) (e.symm i)
  have hsimple' (i : κ) : c.equivFun (P.coroot (e.symm i).val) = Pi.single i 1 := by
    rw [← hc]
    funext j
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  let f : ι → (κ → ℤ) × (κ → ℤ) := fun i => (x (P.root i), c.equivFun (P.coroot i))
  have hneg (i : ι) : f (P.reflectionPerm i i) = (-(f i).1, -(f i).2) := by
    dsimp [f]
    simp [← P.reflectionPerm_root, ← P.reflectionPerm_coroot, two_smul]
  have hreflect (i : κ) (j : ι) :
      f (P.reflectionPerm (e.symm i).val j) = reflectCoordinates A i (f j) := by
    have hcoe : P.toLinearMap (P.root j) (P.coroot (e.symm i).val) = x (P.root j) i := by
      rw [hx, hc]
    simp only [f, reflectCoordinates, Prod.fst, Prod.snd]
    rw [← P.reflectionPerm_root, ← P.reflectionPerm_coroot, hcoe,
      hp (P.root (e.symm i).val) (P.coroot j), hsimple]
    simp only [map_sub, map_smul, hsimple, hsimple', simpleCharacter]
  refine ⟨c, x, hc, hp, hsimple, ?_⟩
  change range f = _
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    change CartanRoots A (f i)
    apply B.induction_reflect i (p := fun j => CartanRoots A (f j))
    · intro j hj
      rw [hneg]
      exact .neg hj
    · intro j hj
      let i := e ⟨j, hj⟩
      have h : (e.symm i).val = j := by simp [i]
      change CartanRoots A (f j)
      rw [← h]
      change CartanRoots A (x (P.root (e.symm i).val), c.equivFun (P.coroot (e.symm i).val))
      rw [hsimple, hsimple']
      exact .simple i
    · intro j l hj hl
      let i := e ⟨l, hl⟩
      have h : (e.symm i).val = l := by simp [i]
      rw [← h, hreflect]
      exact .reflect i hj
  · intro hp
    change CartanRoots A p at hp
    induction hp with
    | simple i =>
      exact ⟨(e.symm i).val, Prod.ext (hsimple i) (hsimple' i)⟩
    | neg hp ih =>
      obtain ⟨j, rfl⟩ := ih
      exact ⟨P.reflectionPerm j j, hneg j⟩
    | reflect i hp ih =>
      obtain ⟨j, rfl⟩ := ih
      exact ⟨P.reflectionPerm (e.symm i).val j, hreflect i j⟩

theorem cartanDeterminesBasedDatum : CartanDeterminesBasedDatum.{u} := by
  classical
  intro P Q hP hQ e
  letI := P.finiteRoots
  letI := Q.finiteRoots
  letI := P.reduced
  letI := Q.reduced
  constructor
  · intro h
    let A := integralCartan Q.datum Q.base
    obtain ⟨c, x, _, hPairP, hSimpleP, hRangeP⟩ :=
      cartanCoordinates P.datum P.base hP A e h
    obtain ⟨d, y, _, hPairQ, hSimpleQ, hRangeQ⟩ :=
      cartanCoordinates Q.datum Q.base hQ A (Equiv.refl _) (fun _ _ => rfl)
    let rootsP (i : P.I) := (x (P.datum.root i), c.equivFun (P.datum.coroot i))
    let rootsQ (j : Q.I) := (y (Q.datum.root j), d.equivFun (Q.datum.coroot j))
    let p := Equiv.ofInjective rootsP (fun _ _ heq =>
      P.datum.root.injective (x.injective (congrArg Prod.fst heq)))
    let q := Equiv.ofInjective rootsQ (fun _ _ heq =>
      Q.datum.root.injective (y.injective (congrArg Prod.fst heq)))
    let relabel := Set.equivOfEq (hRangeP.trans hRangeQ.symm)
    let f := p.trans (relabel.trans q.symm)
    have hRoot (i : P.I) : rootsP i = rootsQ (f i) :=
      (congrArg Subtype.val (q.apply_symm_apply (relabel (p i)))).symm
    have hBase (i : P.base.support) : f i.val = (e i).val := by
      apply Q.datum.root.injective
      apply y.injective
      have hSimple : x (P.datum.root i.val) = simpleCharacter A (e i) := by
        simpa only [Equiv.symm_apply_apply] using hSimpleP (e i)
      exact (congrArg Prod.fst (hRoot i.val)).symm.trans (hSimple.trans (hSimpleQ (e i)).symm)
    let xEquiv := x.trans y.symm
    let yEquiv := d.equivFun.trans c.equivFun.symm
    let F : P.datum.Equiv Q.datum :=
      { weightMap := xEquiv
        coweightMap := yEquiv
        indexEquiv := f
        weight_coweight_transpose := by
          ext b a
          change Q.datum.toLinearMap (xEquiv a) b = P.datum.toLinearMap a (yEquiv b)
          rw [hPairP, hPairQ]
          simp only [xEquiv, yEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
        root_weightMap := by
          funext i
          apply y.injective
          simpa only [Function.comp_apply, LinearEquiv.coe_coe, xEquiv, LinearEquiv.trans_apply,
            LinearEquiv.apply_symm_apply] using congrArg Prod.fst (hRoot i)
        coroot_coweightMap := by
          funext j
          obtain ⟨i, rfl⟩ := f.surjective j
          apply c.equivFun.injective
          simpa only [Function.comp_apply, LinearEquiv.coe_coe, yEquiv, LinearEquiv.trans_apply,
            Equiv.symm_apply_apply, LinearEquiv.apply_symm_apply] using (congrArg Prod.snd (hRoot i)).symm
        bijective_weightMap := xEquiv.bijective
        bijective_coweightMap := yEquiv.bijective }
    have hImage : f '' (P.base.support : Set P.I) = Q.base.support := by
      ext j
      constructor
      · rintro ⟨i, hi, rfl⟩
        rw [hBase ⟨i, hi⟩]
        exact (e ⟨i, hi⟩).property
      · intro hj
        let i := e.symm ⟨j, hj⟩
        exact ⟨i.val, i.property, (hBase i).trans (congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩))⟩
    refine ⟨⟨F, hImage⟩, hBase, fun G hG => ?_⟩
    apply Subtype.ext
    have hSpan : Submodule.span ℤ (range fun j : Q.base.support => Q.datum.coroot j.val) = ⊤ := by
      change Submodule.span ℤ (range fun j : (↑Q.base.support : Set Q.I) => Q.datum.coroot j.val) = ⊤
      rw [← image_eq_range, Q.base.span_int_coroot_support, hQ]
    have hCoweight : G.val.toHom.coweightMap = F.toHom.coweightMap := by
      apply LinearMap.ext_on_range hSpan
      intro j
      obtain ⟨i, rfl⟩ := e.surjective j
      rw [G.val.toHom.coroot_coweightMap_apply, F.toHom.coroot_coweightMap_apply,
        G.val.indexEquiv.symm_apply_eq.mpr (hG i).symm, F.indexEquiv.symm_apply_eq.mpr (hBase i).symm]
    have hWeight : G.val.toHom.weightMap = F.toHom.weightMap := by
      ext a
      apply Q.datum.toLinearMap.toPerfPair.injective
      ext b
      calc
        _ = P.datum.toLinearMap a (G.val.toHom.coweightMap b) :=
          LinearMap.congr_fun (G.val.toHom.weight_coweight_transpose_apply _ _ b) a
        _ = P.datum.toLinearMap a (F.toHom.coweightMap b) := by rw [hCoweight]
        _ = _ := (LinearMap.congr_fun (F.toHom.weight_coweight_transpose_apply _ _ b) a).symm
    refine RootPairing.Equiv.ext hWeight hCoweight (Equiv.ext fun i => ?_)
    apply Q.datum.root.injective
    rw [← G.val.toHom.root_weightMap_apply _ _ i, ← F.toHom.root_weightMap_apply _ _ i, hWeight]
  · rintro ⟨f, hf, _⟩ i j
    change P.datum.pairing j.val i.val = Q.datum.pairing (e j).val (e i).val
    rw [← hf j, ← hf i]
    exact f.val.toHom.pairing.symm

theorem cartanRootBlocks : CartanRootBlocks := by
  classical
  intro ι _ _ A S hS
  have hs (V : Set ι) (hV : ∀ i ∈ V, ∀ j ∉ V, A i j = 0 ∧ A j i = 0) (p)
      (hp : SupportedOn V p) (i : ι) :
      (i ∉ V → reflectCoordinates A i p = p) ∧
        (i ∈ V → SupportedOn V (reflectCoordinates A i p)) := by
    constructor
    · intro hi
      have hsum : (∑ j, p.2 j * A j i) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : j ∈ V
        · simp [(hV j hj i hi).1]
        · simp [(hp j hj).2]
      rcases hp i hi with ⟨hx, _⟩
      simp [reflectCoordinates, hx, hsum]
    · intro hi j hj
      rcases hp j hj with ⟨hx, hy⟩
      have hji : j ≠ i := fun he => hj (he ▸ hi)
      simp [reflectCoordinates, simpleCharacter, hx, hy, (hV i hi j hj).2,
        Pi.single_apply, hji, hji.symm]
  have hSc : ∀ i ∈ Sᶜ, ∀ j ∉ Sᶜ, A i j = 0 ∧ A j i = 0 := by
    intro i hi j hj
    exact And.symm (hS j (by simpa using hj) i hi)
  have hsimple (V : Set ι) (hV : ∀ i ∈ V, ∀ j ∉ V, A i j = 0 ∧ A j i = 0)
      (i : ι) (hi : i ∈ V) : SupportedOn V (simpleCharacter A i, Pi.single i 1) := by
    intro j hj
    have hji : j ≠ i := fun he => hj (he ▸ hi)
    exact ⟨(hV i hi j hj).2, by simp [Pi.single_apply, hji, hji.symm]⟩
  have hneg (V : Set ι) (p) (hp : SupportedOn V p) : SupportedOn V (-p.1, -p.2) := by
    intro j hj
    simp [(hp j hj).1, (hp j hj).2]
  have href (V : Set ι) (hV : ∀ i ∈ V, ∀ j ∉ V, A i j = 0 ∧ A j i = 0) (p)
      (hp : SupportedOn V p) (i : ι) : SupportedOn V (reflectCoordinates A i p) := by
    by_cases hi : i ∈ V
    · exact (hs V hV p hp i).2 hi
    · rw [(hs V hV p hp i).1 hi]
      exact hp
  refine ⟨?_, hs S hS⟩
  intro p hp
  induction hp with
  | simple i =>
    by_cases hi : i ∈ S
    · exact Or.inl (hsimple S hS i hi)
    · exact Or.inr (hsimple Sᶜ hSc i hi)
  | neg _ ih => exact ih.imp (hneg S _) (hneg Sᶜ _)
  | reflect i _ ih => exact ih.imp (fun h => href S hS _ h i) (fun h => href Sᶜ hSc _ h i)

theorem disconnectedPartition : DisconnectedPartition := by
  classical
  intro ι X Y _ _ _ _ _ _ _ P _ B hne hn
  obtain ⟨_, _, _, _, _, metric, h⟩ := euclideanComparison P B
  letI := metric.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore metric.toCore
  obtain ⟨_, _, _, hR, v, b, hv, _, _, _, hb, hA, _⟩ := h
  have hdiag := cartan_diagram_eq hR hv hb hA
  let r : B.support → B.support → Prop := fun i j => (dynkinDiagram b).edges i j ≠ 0
  have hconn : ¬ ∀ i j, Relation.EqvGen r i j := by
    intro hc
    apply hn
    rw [← hdiag]
    exact ⟨hne, hc⟩
  push Not at hconn
  obtain ⟨i₀, j₀, hj₀⟩ := hconn
  let S : Set B.support := {j | Relation.EqvGen r i₀ j}
  refine ⟨S, ⟨i₀, .refl _⟩, ⟨j₀, hj₀⟩, ?_⟩
  intro i hi j hj
  have hneq : i ≠ j := fun e => hj (e ▸ hi)
  have hedge : (dynkinDiagram b).edges i j = 0 := by
    by_contra he
    exact hj (.trans _ _ _ hi (.rel _ _ he))
  have hinner : inner ℝ (b i) (b j) = 0 := by
    by_contra h
    exact (dynkin_edges_ne_zero hR hv hb i j).2 ⟨hneq, h⟩ hedge
  have hz (i j : B.support) (hi : inner ℝ (b i) (b j) = 0) :
      integralCartan P B i j = 0 := by
    have hc : cartanMatrix b i j = (integralCartan P B i j : ℝ) := congrFun (congrFun hA i) j
    have hcz : cartanMatrix b i j = 0 := by
      have hi' : inner ℝ (b j) (b i) = 0 := by rwa [real_inner_comm]
      simp [cartanMatrix, rootCartan, hi']
    exact_mod_cast hc.symm.trans hcz
  exact ⟨hz i j hinner, hz j i (by rwa [real_inner_comm])⟩

open private realReflection_root realRoot_injective weyl_roots_faithful
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.EuclideanComparison

private theorem weyl_generator {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum (ι := ι) X Y) (j i : ι) :
    P.weylGroupToPerm (RootPairing.weylGroup.ofIdx P j) i = P.reflectionPerm j i := rfl

theorem weylActionComparison : WeylActionComparison := by
  intro ι X Y _ _ _ P
  constructor
  · rintro ⟨g, hg⟩
    change ∃ w : P.weylGroup, ∀ i, g (realRoot P i) = realRoot P (P.weylGroupToPerm w i)
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨j, rfl⟩
      exact ⟨RootPairing.weylGroup.ofIdx P j, by intro i; exact realReflection_root P j i⟩
    · exact ⟨1, fun i => by simp⟩
    · rintro g h _ _ ⟨v, hv⟩ ⟨w, hw⟩
      refine ⟨v * w, fun i => ?_⟩
      change g (h (realRoot P i)) = _
      rw [hw, hv, map_mul]
      rfl
    · rintro g _ ⟨w, hw⟩
      refine ⟨w⁻¹, fun i => g.injective ?_⟩
      change g (g.symm (realRoot P i)) = g (realRoot P (P.weylGroupToPerm w⁻¹ i))
      rw [g.apply_symm_apply, hw, map_inv]
      exact congrArg (realRoot P) ((P.weylGroupToPerm w).apply_symm_apply i).symm
  · intro w
    refine RootPairing.weylGroup.induction P (pred := fun w hw => ∃ g : realWeylGroup P,
      ∀ i, g.val (realRoot P i) = realRoot P (P.weylGroupToPerm ⟨w, hw⟩ i))
      ?_ ?_ ?_ w.property
    · intro j
      exact ⟨⟨realReflection P j, Subgroup.subset_closure (mem_range_self j)⟩,
        by intro i; exact realReflection_root P j i⟩
    · exact ⟨1, fun i => by simp⟩
    · rintro v w hv hw ⟨g, hg⟩ ⟨h, hh⟩
      refine ⟨g * h, fun i => ?_⟩
      change g.val (h.val (realRoot P i)) = _
      rw [hh, hg]
      rfl

theorem weylGroupComparison : WeylGroupComparison := by
  classical
  intro ι X Y _ _ _ _ P hY
  have hroot := realRoot_injective P
  have hreal := weyl_roots_faithful P
  obtain ⟨hIntegral, hReal⟩ := weylActionComparison P
  choose f hf using hReal
  let φ : P.weylGroup →* realWeylGroup P :=
    { toFun := f
      map_one' := by
        apply hreal
        rintro _ ⟨i, rfl⟩
        rw [hf, map_one]
        rfl
      map_mul' := by
        intro w₁ w₂
        apply hreal
        rintro _ ⟨i, rfl⟩
        change (f (w₁ * w₂)).val (realRoot P i) =
          (f w₁).val ((f w₂).val (realRoot P i))
        rw [hf, hf, hf, map_mul]
        rfl }
  have hperm : Function.Injective P.weylGroupToPerm := by
    intro w₁ w₂ h
    apply Subtype.ext
    apply RootPairing.Equiv.coweightHom_injective P
    apply MulOpposite.unop_injective
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on_range hY
    intro i
    change w₁.val.toHom.coweightMap (P.coroot i) = w₂.val.toHom.coweightMap (P.coroot i)
    rw [RootPairing.Hom.coroot_coweightMap_apply, RootPairing.Hom.coroot_coweightMap_apply]
    exact congrArg (fun g : Equiv.Perm ι => P.coroot (g.symm i)) h
  have hinj : Function.Injective φ := by
    intro w₁ w₂ he
    apply hperm
    ext i
    apply hroot
    rw [← hf, ← hf]
    exact congrArg (fun g : realWeylGroup P => g.val (realRoot P i)) he
  have hsurj : Function.Surjective φ := by
    intro g
    obtain ⟨w, hw⟩ := hIntegral g
    exact ⟨w, hreal _ _ (by rintro _ ⟨i, rfl⟩; exact (hf w i).trans (hw i).symm)⟩
  refine ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, hf, fun i => ?_⟩
  let s : realWeylGroup P := ⟨realReflection P i, Subgroup.subset_closure (mem_range_self i)⟩
  have he : f (RootPairing.weylGroup.ofIdx P i) = s := hreal _ _ (by
    rintro _ ⟨j, rfl⟩
    exact (hf _ j).trans (realReflection_root P i j).symm)
  exact congrArg Subtype.val he

open LinearAlgebraicGroups.Specs
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

theorem splitPinnedComparison : SplitPinnedComparison := by
  intro k _ A P
  obtain ⟨U, ⟨pin⟩⟩ := Classification.Pinning.pinningsExist A P
  obtain ⟨comm, D, ⟨W⟩⟩ :=
    RootData.DatumAndWeyl.datumAndWeyl P.G P.reductive P.T P.split P.maximal
  letI := comm
  letI := D.finiteRoots
  letI := D.freeCharacters
  letI := D.finiteCharacters
  letI := D.reduced
  obtain ⟨c, _, hr, _, hB⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  let f := Specs.SimpleRoots.evaluate D c
  have hf (i : AbstractPairing.Root P.T) :
      f (D.rootDatum.root i) = CharacterPairing.pairing P.T.group i.val c := by
    change D.rootDatum.toLinearMap (D.rootDatum.root i) _ = _
    rw [D.root_eq, D.pairing_eq]
  obtain ⟨b, hb⟩ := RootData.SimpleRoots.baseFor D.rootDatum f (fun i => hf i ▸ hr i)
  have hpos : Specs.SimpleRoots.positive D.rootDatum f = BorelsAndChambers.subgroupRoots P.T P.B := by
    ext i
    rw [hB]
    exact (congrArg (fun z : ℤ => 0 < z) (hf i)).to_iff
  let D' : Pinning.AttachedDatum P := ⟨comm, D, b, fun i => by
    rw [hb.simple_iff, hpos]
    simp only [Pinning.IsSimple, D.root_eq]
    rfl⟩
  exact ⟨U, pin, D', ⟨W⟩⟩

open Specs.GeometricRadicals (GeometricGroup IsSemisimple)
open SimplyConnectedLattice (corootLattice)
open Unipotent (closedSubgroupAlgebraicGroup)
open private unipotent_solvable from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private trivialOfSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private splitBorelPair exists_coroot_cover torusIso_of_isIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

private theorem reductive_of_semisimple {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (h : IsSemisimple G) : Specs.GeometricRadicals.IsReductive G := by
  have hU := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
  have hR := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  let U := Specs.GeometricRadicals.geometricUnipotentRadical G
  refine ⟨h.1, h.2.1, trivialOfSubgroup (hR.2.2 U hU.1 ?_) h.2.2⟩
  exact unipotent_solvable (closedSubgroupAlgebraicGroup U) hU.1.1 hU.1.2.1 hU.2.1

private theorem geometric_coroot_lattice {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (hG : IsSemisimple G) (hsc : SimplyConnectedLattice.GeometricallySimplyConnected G)
    (P : Pinning.SplitBorelPair (AlgebraicClosure k)) (hP : P.G = GeometricGroup G)
    (D : Pinning.AttachedDatum P) : corootLattice D = ⊤ := by
  letI := D.comm
  have hPair : IsSemisimple P.G := hP ▸
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := AlgebraicClosure k)
      G hG.1 hG.2.1).mpr hG
  have hcovers : ∀ (J : AffineAlgebraicGroup (AlgebraicClosure k)), IsSemisimple J →
      ∀ f : J.val ⟶ P.G.val, CentralIsogenies.IsCentralIsogeny f → IsIso f := by
    rw [hP]
    exact hsc
  obtain ⟨S, E, f, τ, hS, _, hf, hτ, _, _, eY, heY⟩ :=
    exists_coroot_cover Classification.IntegralRealization.integralRealization P D hPair
  letI := E.comm
  letI := hcovers S.G hS f hf
  letI := torusIso_of_isIso S P f τ hτ
  apply eq_top_iff.mpr
  intro y _
  have hy := (eY (Additive.ofMul (y.toMul ≫ inv τ))).property
  rwa [heY, Category.assoc, IsIso.inv_hom_id, Category.comp_id] at hy

theorem geometricPinnedDatum : GeometricPinnedDatum := by
  intro k _ G hG hsc A
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  have hH : IsSemisimple H :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  have hRed := reductive_of_semisimple H hH
  letI := hH.2.1
  have hc := GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  obtain ⟨T, ht, hm⟩ := MaximalToriExist.geometricallyMaximalTorusExists H hH.1 hc
  have hs : Specs.GeometricRadicals.IsSplitTorus T.group :=
    split_of_torus ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mp ht)
  let P := splitBorelPair H hRed T hs hm
  obtain ⟨U, pin, D, hW⟩ := splitPinnedComparison A P
  exact ⟨P, rfl, U, pin, D, hW, geometric_coroot_lattice G hG hsc P rfl D⟩

private abbrev PathAdjacent {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

private theorem path_ne {n : ℕ} {i j : Fin n} (h : PathAdjacent i j) : i ≠ j := by
  rintro rfl
  rcases h with h | h <;> omega

private theorem path_perm_eq_id_of_first {n : ℕ} (e : Equiv.Perm (Fin n))
    (h : ∀ i j, PathAdjacent (e i) (e j) ↔ PathAdjacent i j)
    (h0 : ∀ i : Fin n, i.val = 0 → e i = i) :
    e = Equiv.refl _ := by
  apply Equiv.ext
  intro i
  change e i = i
  obtain ⟨m, hm⟩ := i
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hz : m = 0
    · exact h0 _ hz
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
    let j : Fin n := ⟨a, by omega⟩
    have hj : e j = j := ih a (by omega) _
    have hne : PathAdjacent (e j) (e ⟨a + 1, hm⟩) :=
      (h j ⟨a + 1, hm⟩).mpr (Or.inl rfl)
    rw [hj] at hne
    rcases hne with hh | hh
    · exact Fin.ext hh.symm
    · change (e ⟨a + 1, hm⟩).val + 1 = a at hh
      have hp : a - 1 < n := by omega
      let p : Fin n := ⟨a - 1, hp⟩
      have hep : e p = p := ih (a - 1) (by omega) _
      have heqp : e ⟨a + 1, hm⟩ = e p := by
        rw [hep]
        exact Fin.ext (by change _ = a - 1; omega)
      have hfalse : (⟨a + 1, hm⟩ : Fin n) = p := e.injective heqp
      have hval := congrArg Fin.val hfalse
      change a + 1 = a - 1 at hval
      omega

private theorem rev_preserves_path {n : ℕ} (i j : Fin n) :
    PathAdjacent (Fin.revPerm i) (Fin.revPerm j) ↔ PathAdjacent i j := by
  simp only [PathAdjacent, Fin.revPerm_apply, Fin.val_rev]
  omega

private theorem path_automorphisms {n : ℕ} (e : Equiv.Perm (Fin n))
    (h : ∀ i j, PathAdjacent (e i) (e j) ↔ PathAdjacent i j) :
    e = Equiv.refl _ ∨ e = Fin.revPerm := by
  by_cases hn : n = 0
  · subst n
    exact Or.inl (Subsingleton.elim _ _)
  let first : Fin n := ⟨0, by omega⟩
  have hfirst : (e first).val = 0 ∨ (e first).val = n - 1 := by
    by_contra! hh
    let i : Fin n := ⟨(e first).val - 1, by omega⟩
    let j : Fin n := ⟨(e first).val + 1, by omega⟩
    have hi : PathAdjacent first (e.symm i) := (h first (e.symm i)).mp (by
      rw [e.apply_symm_apply]; exact Or.inr (by change (e first).val - 1 + 1 = _; omega))
    have hj : PathAdjacent first (e.symm j) := (h first (e.symm j)).mp (by
      rw [e.apply_symm_apply]; exact Or.inl rfl)
    have hk : e.symm i = e.symm j := Fin.ext (by
      simp only [PathAdjacent, first] at hi hj
      omega)
    have hk' := congrArg Fin.val (e.symm.injective hk)
    change (e first).val - 1 = (e first).val + 1 at hk'
    omega
  rcases hfirst with hfirst | hfirst
  · left
    apply path_perm_eq_id_of_first e h
    intro i hi
    have he : i = first := Fin.ext hi
    subst i
    exact Fin.ext hfirst
  · right
    let f := e.trans Fin.revPerm
    have hf := path_perm_eq_id_of_first f (fun i j => (rev_preserves_path (e i) (e j)).trans (h i j))
      (fun i hi => by
        have he : i = first := Fin.ext hi
        subst i
        apply Fin.ext
        change (Fin.rev (e first)).val = 0
        rw [Fin.val_rev, hfirst]; omega)
    apply Equiv.ext
    intro i
    have hh := congrFun (congrArg Equiv.toFun hf) i
    change Fin.rev (e i) = i at hh
    exact (Fin.rev_rev (e i)).symm.trans (congrArg Fin.rev hh)

private theorem typeA_path {n : ℕ} (i j : Fin n) :
    PathAdjacent i j ↔ i ≠ j ∧ CartanMatrix.A n i j ≠ 0 := by
  by_cases h : PathAdjacent i j
  · have hn := path_ne h
    simp [CartanMatrix.A, Matrix.of_apply, hn, PathAdjacent] at h ⊢
    tauto
  · by_cases hij : i = j
    · subst j; simpa using h
    · have hh : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := h
      simp [CartanMatrix.A, Matrix.of_apply, h, hh, hij]

theorem typeAPermutations : TypeAPermutations := by
  intro n e
  constructor
  · intro he
    apply path_automorphisms
    intro i j
    rw [typeA_path, typeA_path, ← he i j]
    exact and_congr (not_congr e.apply_eq_iff_eq) Iff.rfl
  · rintro (rfl | rfl)
    · intro i j; rfl
    · intro i j
      by_cases hij : i = j
      · subst j; exact (congrFun (CartanMatrix.A_diag n) i).trans
          (congrFun (CartanMatrix.A_diag n) (Fin.revPerm i)).symm
      · have hrev : Fin.revPerm i ≠ Fin.revPerm j := fun h => hij (Fin.revPerm.injective h)
        have hadj := rev_preserves_path i j
        simp only [CartanMatrix.A, Matrix.of_apply]
        rw [if_neg hij, if_neg hrev]
        exact if_congr hadj.symm rfl rfl

private theorem typeB_path {n : ℕ} (i j : Fin n) :
    PathAdjacent i j ↔ i ≠ j ∧ CartanMatrix.B n i j ≠ 0 := by
  simp only [PathAdjacent, CartanMatrix.B, Matrix.of_apply]
  split_ifs <;> omega

theorem typeBCPermutations : TypeBCPermutations := by
  intro n hn e
  have hb : PreservesCartan (CartanMatrix.B n) (CartanMatrix.B n) e ↔ e = Equiv.refl _ := by
    refine ⟨fun he => ?_, fun h => h ▸ (fun i j => rfl)⟩
    have hpath (i j : Fin n) : PathAdjacent (e i) (e j) ↔ PathAdjacent i j := by
      rw [typeB_path, typeB_path, ← he i j]
      exact and_congr (not_congr e.apply_eq_iff_eq) Iff.rfl
    have hterm (i j : Fin n) :
        CartanMatrix.B n i j = -2 ↔ i.val + 1 = j.val ∧ j.val = n - 1 := by
      by_cases hij : i = j
      · subst j; simp [CartanMatrix.B, Matrix.of_apply]
      by_cases hs : i.val + 1 = j.val
      · by_cases ht : j.val = n - 1 <;> simp [CartanMatrix.B, Matrix.of_apply, hij, hs, ht]
      · by_cases hr : j.val + 1 = i.val <;> simp [CartanMatrix.B, Matrix.of_apply, hij, hs, hr]
    rcases path_automorphisms e hpath with h | h
    · exact h
    let i : Fin n := ⟨n - 2, by omega⟩
    let j : Fin n := ⟨n - 1, by omega⟩
    have hsource : CartanMatrix.B n i j = -2 := (hterm i j).mpr
      ⟨by change n - 2 + 1 = n - 1; omega, rfl⟩
    have heJ := ((hterm (e i) (e j)).mp ((he i j).symm.trans hsource)).2
    rw [h] at heJ
    simp only [Fin.revPerm_apply, Fin.val_rev] at heJ
    change n - (n - 1 + 1) = n - 1 at heJ
    omega
  refine ⟨hb, ?_⟩
  have hTranspose : PreservesCartan (CartanMatrix.C n) (CartanMatrix.C n) e ↔
      PreservesCartan (CartanMatrix.B n) (CartanMatrix.B n) e := by
    rw [← CartanMatrix.B_transpose n]
    exact ⟨fun h i j => h j i, fun h i j => h j i⟩
  exact hTranspose.trans hb

private def cartanRowSums {I : Type*} [Fintype I] (A : Matrix I I ℤ) : ℕ → I → ℤ
  | 0 => fun _ => 1
  | n + 1 => fun i => ∑ j, A i j * cartanRowSums A n j

private def cartanProfile {I : Type*} [Fintype I] (A : Matrix I I ℤ) (i : I) :
    ℤ × ℤ × ℤ :=
  (cartanRowSums A 1 i, cartanRowSums A 2 i, cartanRowSums A 3 i)

private theorem cartanProfile_perm {I : Type*} [Fintype I] {A : Matrix I I ℤ}
    {σ : Equiv.Perm I} (h : PreservesCartan A A σ) (i : I) :
    cartanProfile A (σ i) = cartanProfile A i := by
  have hp (n : ℕ) (i : I) : cartanRowSums A n (σ i) = cartanRowSums A n i := by
    induction n generalizing i with
    | zero => rfl
    | succ n ih =>
      change (∑ j, A (σ i) j * cartanRowSums A n j) = _
      rw [← Equiv.sum_comp σ]
      change (∑ j, A (σ i) (σ j) * cartanRowSums A n (σ j)) = _
      simp only [← h i, ih]
      rfl
  simp only [cartanProfile, hp]

private theorem fixes_of_injective_profile {I : Type*} [Fintype I] {A : Matrix I I ℤ}
    (h : Function.Injective (cartanProfile A)) (σ : Equiv.Perm I) :
    PreservesCartan A A σ ↔ σ = Equiv.refl _ :=
  ⟨fun hp => Equiv.ext (fun i => h (cartanProfile_perm hp i)), fun hp => hp ▸ fun _ _ => rfl⟩

set_option maxRecDepth 3000 in
set_option maxHeartbeats 500000 in
private theorem e6_profile_first :
    ∀ i : Fin 6, cartanProfile (CartanMatrix.E 6) i = cartanProfile (CartanMatrix.E 6) 0 →
      i = 0 ∨ i = 5 := by decide +kernel

set_option maxRecDepth 3000 in
set_option maxHeartbeats 500000 in
private theorem e6_profile_with_first :
    ∀ i j : Fin 6, cartanProfile (CartanMatrix.E 6) i = cartanProfile (CartanMatrix.E 6) j →
      CartanMatrix.E 6 0 i = CartanMatrix.E 6 0 j → i = j := by decide +kernel

set_option maxRecDepth 3000 in
set_option maxHeartbeats 500000 in
private theorem e6_profile_with_last :
    ∀ i j : Fin 6, cartanProfile (CartanMatrix.E 6) i = cartanProfile (CartanMatrix.E 6) j →
      CartanMatrix.E 6 5 i = CartanMatrix.E 6 0 j → i = E6Reflection j := by decide +kernel

set_option maxRecDepth 3000 in
set_option maxHeartbeats 500000 in
theorem exceptionalPermutations : ExceptionalPermutations := by
  refine ⟨?_, fixes_of_injective_profile ?_, fixes_of_injective_profile ?_,
    fixes_of_injective_profile ?_, fixes_of_injective_profile ?_⟩
  · intro σ
    constructor
    · intro h
      rcases e6_profile_first (σ 0) (cartanProfile_perm h 0) with h0 | h5
      · exact Or.inl (Equiv.ext fun i => e6_profile_with_first (σ i) i
          (cartanProfile_perm h i) (by simpa only [h0] using (h 0 i).symm))
      · exact Or.inr (Equiv.ext fun i => e6_profile_with_last (σ i) i
          (cartanProfile_perm h i) (by simpa only [h5] using (h 0 i).symm))
    · rintro (rfl | rfl)
      · intro i j; rfl
      · intro i j; fin_cases i <;> fin_cases j <;> decide
  all_goals
    unfold Function.Injective
    decide +kernel

open private splitPresentation charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private isIso_of_schemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory

private theorem trivial_split_torus_of_characters {k : Type u} [Field k] {T : GroupScheme k}
    (h : Specs.GeometricRadicals.IsSplitTorus T) [Subsingleton (CharacterDescent.Character T)] :
    IsZero T := by
  obtain ⟨r, ⟨e⟩⟩ := splitPresentation h
  let M := CharacterDescent.StandardLattice.{u} r
  obtain ⟨χ, _, _, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  let f : M ≃* CharacterDescent.Character T := χ.trans (charactersOfIso e)
  letI : Subsingleton M := ⟨fun _ _ => f.injective (Subsingleton.elim _ _)⟩
  let A := specGroup (Specs.DiagonalizableGroups.groupAlgebra k M)
  let z : A ⟶ Grp.trivial (SchemeOver k) := 0
  have hz : z.hom.hom.left = A.X.hom := by
    have h := z.hom.hom.w
    change z.hom.hom.left ≫ 𝟙 _ = A.X.hom at h
    exact (Category.comp_id _).symm.trans h
  have hr : IsIso A.X.hom := by
    change IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k M))))
    let d : CommRingCat.of k ≅ CommRingCat.of (MonoidAlgebra k M) :=
      (MonoidAlgebra.uniqueAlgEquiv k M).symm.toRingEquiv.toCommRingCatIso
    have hd : d.hom = CommRingCat.ofHom (algebraMap k (MonoidAlgebra k M)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change (MonoidAlgebra.uniqueAlgEquiv k (A := k) M).symm x = _
      exact (MonoidAlgebra.uniqueAlgEquiv k (A := k) M).symm.commutes x
    rw [← hd]
    infer_instance
  letI : IsIso z.hom.hom.left := hz ▸ hr
  letI : IsIso z := isIso_of_schemeIso z
  exact ((Grp.isZero_trivial _).of_iso (asIso z)).of_iso e.symm

private theorem rootless_torus_inclusion {k : Type u} [Field k] (P : Pinning.SplitBorelPair k)
    [IsEmpty (AbstractPairing.Root P.T)] : IsIso P.T.inclusion := by
  let X := P.T.group.X
  let I := (𝟙_ (SchemeOver k))
  let e : I ⊗ (X ⊗ I) ≅ X := (λ_ (X ⊗ I)) ≪≫ (ρ_ X)
  let q : I ⊗ (X ⊗ I) ⟶ X := snd I (X ⊗ I) ≫ fst X I
  have hq : q = e.hom := by
    simp [q, e, I, snd_def, fst_def, toUnit_unit]
  let U : OrderedRootProducts.RootSubgroupFamily P.T := fun α => isEmptyElim α
  have hempty (c : CharacterDescent.Cocharacter P.T.group) :
      OrderedRootProducts.Enumerates [] (BorelsAndChambers.positiveRoots P.T c) :=
    ⟨List.nodup_nil, fun α => isEmptyElim α⟩
  have hcell := RootData.OrderedRootProducts.regularRootCell P.G P.reductive
    P.T P.split P.maximal 0 (fun α => isEmptyElim α) U [] [] (hempty _) (hempty _)
  have he : OrderedRootProducts.rootCellMap P.T U [] [] =
      e.hom ≫ P.T.inclusion.hom.hom := by
    let z := P.T.inclusion.hom.hom
    change (fst I (X ⊗ I) ≫ (1 : I ⟶ P.G.val.X)) *
      (snd I (X ⊗ I) ≫ ((fst X I ≫ z) * (snd X I ≫ (1 : I ⟶ P.G.val.X)))) = e.hom ≫ z
    rw [MonObj.comp_one, MonObj.comp_one, mul_one, one_mul, ← hq, Category.assoc]
  rw [he] at hcell
  have hopen : IsOpenImmersion P.T.inclusion.hom.hom.left := by
    letI : IsIso e.hom.left :=
      inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of k))).map e.hom))
    change IsOpenImmersion (e.hom.left ≫ P.T.inclusion.hom.hom.left) at hcell
    letI := hcell
    have h : IsOpenImmersion (inv e.hom.left ≫ e.hom.left ≫ P.T.inclusion.hom.hom.left) :=
      inferInstance
    simpa only [IsIso.inv_hom_id_assoc] using h
  letI := hopen
  letI := P.T.isClosedImmersion
  letI := P.reductive.2.1
  letI := GeometricallyConnected.connectedSpace_of_subsingleton P.G.val.X.hom
  let f := P.T.inclusion.hom.hom.left
  have hcl : IsClopen (range f) := ⟨f.isClosedEmbedding.isClosed_range, f.isOpenMap.isOpen_range⟩
  have hn : (range f).Nonempty := ⟨_, η[P.T.group.X].left (IsLocalRing.closedPoint k), rfl⟩
  have hf : Surjective f := ⟨Set.range_eq_univ.mp (hcl.eq_univ hn)⟩
  letI : IsIso P.T.inclusion.hom.hom.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hopen, hf⟩
  exact isIso_of_schemeIso P.T.inclusion

theorem nonemptySimpleRoots : NonemptySimpleRoots := by
  classical
  intro k _ P D hD hn
  letI := D.comm
  by_contra h
  letI : IsEmpty (AbstractPairing.Root P.T) := ⟨fun i => by
    letI : Nonempty (AbstractPairing.Root P.T) := ⟨i⟩
    obtain ⟨j, hj⟩ := D.base.support_nonempty
    exact h ⟨⟨j, hj⟩⟩⟩
  let Y := Additive (CharacterDescent.Cocharacter P.T.group)
  have hy : (⊥ : Submodule ℤ Y) = ⊤ := by
    have hr : range D.datum.rootDatum.coroot = ∅ := Set.range_eq_empty _
    simpa [Specs.SimplyConnectedLattice.corootLatticeOf, hr] using hD
  letI : Subsingleton Y := ⟨fun y z => by
    have h0 (a : Y) : a = 0 :=
      by simpa using (hy.symm ▸ (Submodule.mem_top : a ∈ (⊤ : Submodule ℤ Y)) :
        a ∈ (⊥ : Submodule ℤ Y))
    exact (h0 y).trans (h0 z).symm⟩
  letI : Subsingleton (CharacterDescent.Character P.T.group) := by
    let c := D.datum.rootDatum.toLinearMap.toPerfPair
    refine ⟨fun a b => Additive.ofMul.injective (c.injective ?_)⟩
    ext y
    rw [Subsingleton.elim y 0, map_zero, map_zero]
  letI : IsIso P.T.inclusion := rootless_torus_inclusion P
  exact hn ((trivial_split_torus_of_characters P.split).of_iso (asIso P.T.inclusion).symm)

private abbrev DAdjacent {n : ℕ} (i j : Fin n) : Prop :=
  (PathAdjacent i j ∧ i.val + 2 < n ∧ j.val + 2 < n) ∨
  (i.val + 3 = n ∧ n ≤ j.val + 2) ∨
  (j.val + 3 = n ∧ n ≤ i.val + 2)

private theorem typeD_edge {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    CartanMatrix.D n i j = if i = j then 2 else if DAdjacent i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j; simp [CartanMatrix.D_diag]
  rw [if_neg hij]
  simp only [CartanMatrix.D, Matrix.of_apply, if_neg hij, DAdjacent, PathAdjacent]
  split_ifs <;> omega

private theorem typeD_adj_iff {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    DAdjacent i j ↔ i ≠ j ∧ CartanMatrix.D n i j = -1 := by
  rw [typeD_edge hn]
  by_cases hij : i = j
  · subst j; simp [DAdjacent, PathAdjacent]; omega
  · by_cases h : DAdjacent i j <;> simp [hij, h]

private theorem typeD_degree_three {n : ℕ} (hn : 5 ≤ n) (i : Fin n) :
    (∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ DAdjacent i a ∧ DAdjacent i b ∧ DAdjacent i c) ↔
      i.val + 3 = n := by
  constructor
  · rintro ⟨a,b,c,hab,hac,hbc,ha,hb,hc⟩
    by_contra h
    rw [← Fin.val_ne_iff] at hab hac hbc
    simp only [DAdjacent, PathAdjacent] at ha hb hc
    omega
  · intro hi
    let a : Fin n := ⟨n - 4, by omega⟩
    let b : Fin n := ⟨n - 2, by omega⟩
    let c : Fin n := ⟨n - 1, by omega⟩
    refine ⟨a,b,c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [DAdjacent, PathAdjacent, ← Fin.val_ne_iff, a, b, c]
    all_goals omega

private theorem typeD_short_leaf {n : ℕ} (hn : 5 ≤ n) (r i : Fin n)
    (hr : r.val + 3 = n) :
    n ≤ i.val + 2 ↔ DAdjacent r i ∧ (∀ j, DAdjacent i j → j = r) := by
  constructor
  · intro hi
    refine ⟨Or.inr (Or.inl ⟨hr, hi⟩), fun j hj => Fin.ext ?_⟩
    unfold DAdjacent PathAdjacent at hj
    omega
  · rintro ⟨hi, h⟩
    by_contra! hc
    have hstep : i.val + 1 = r.val := by
      unfold DAdjacent PathAdjacent at hi
      omega
    let j : Fin n := ⟨i.val - 1, by omega⟩
    have hJ : i.val - 1 + 1 = i.val := by omega
    have hj : DAdjacent i j :=
      Or.inl ⟨Or.inr hJ, hc, by change i.val - 1 + 2 < n; omega⟩
    have he := congrArg Fin.val (h j hj)
    change i.val - 1 = r.val at he
    omega

theorem typeDPermutations : TypeDPermutations := by
  intro n hn σ
  let r : Fin n := ⟨n - 3, by omega⟩
  let a : Fin n := ⟨n - 2, by omega⟩
  let b : Fin n := ⟨n - 1, by omega⟩
  have hab : a ≠ b := by rw [← Fin.val_ne_iff]; change n - 2 ≠ n - 1; omega
  have hr : r.val + 3 = n := by change n - 3 + 3 = n; omega
  constructor
  · intro h
    have adj (i j : Fin n) : DAdjacent (σ i) (σ j) ↔ DAdjacent i j := by
      rw [typeD_adj_iff (by omega), typeD_adj_iff (by omega), ← h i j]
      exact and_congr (not_congr σ.apply_eq_iff_eq) Iff.rfl
    have hfix : σ r = r := by
      obtain ⟨i,j,k,hij,hik,hjk,hi,hj,hk⟩ := (typeD_degree_three hn r).mpr hr
      have hc := (typeD_degree_three hn (σ r)).mp
        ⟨σ i, σ j, σ k, fun e => hij (σ.injective e), fun e => hik (σ.injective e),
          fun e => hjk (σ.injective e), (adj _ _).mpr hi, (adj _ _).mpr hj, (adj _ _).mpr hk⟩
      exact Fin.ext (by omega)
    have hleaf (i : Fin n) : n ≤ (σ i).val + 2 ↔ n ≤ i.val + 2 := by
      rw [typeD_short_leaf hn r (σ i) hr, typeD_short_leaf hn r i hr]
      have hri := adj r i
      rw [hfix] at hri
      refine and_congr hri ⟨fun h j hj => σ.injective ?_, fun h j hj => ?_⟩
      · rw [hfix]
        exact h (σ j) ((adj _ _).mpr hj)
      · obtain ⟨l, rfl⟩ := σ.surjective j
        rw [h l ((adj _ _).mp hj), hfix]
    let incl : Fin (n-2) → Fin n := fun i => ⟨i.val, by have := i.isLt; omega⟩
    have hincl (i : Fin (n-2)) : (σ (incl i)).val < n-2 := by
      have h := (not_congr (hleaf (incl i)))
      have hi := i.isLt
      change (¬ n ≤ (σ (incl i)).val + 2) ↔ ¬ n ≤ i.val + 2 at h
      omega
    let f : Fin (n-2) → Fin (n-2) := fun i => ⟨(σ (incl i)).val, hincl i⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j hij
        have hval := congrArg (@Fin.val (n - 2)) hij
        have he : σ (incl i) = σ (incl j) := Fin.ext hval
        have hh := congrArg Fin.val (σ.injective he)
        exact Fin.ext hh
      · intro j
        have hi := (σ.symm (incl j)).isLt
        have h := (hleaf (σ.symm (incl j)))
        rw [σ.apply_symm_apply] at h
        have hj := j.isLt
        have hk : (σ.symm (incl j)).val < n - 2 := by
          change n ≤ j.val + 2 ↔ _ at h
          omega
        have hval := congrArg Fin.val (σ.apply_symm_apply (incl j))
        exact ⟨⟨_, hk⟩, Fin.ext hval⟩
    let e := Equiv.ofBijective f hf
    have hchain (i j : Fin (n-2)) :
        PathAdjacent (e i) (e j) ↔ PathAdjacent i j := by
      have h := adj (incl i) (incl j)
      have hi := i.isLt
      have hj := j.isLt
      have hi' := hincl i
      have hj' := hincl j
      change PathAdjacent (f i) (f j) ↔ _
      unfold DAdjacent PathAdjacent at *
      change ((σ (incl i)).val + 1 = (σ (incl j)).val ∨
        (σ (incl j)).val + 1 = (σ (incl i)).val) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val
      have hv₁ : (incl i).val = i.val := rfl
      have hv₂ : (incl j).val = j.val := rfl
      omega
    have he : e = Equiv.refl _ := by
      rcases path_automorphisms e hchain with h | h
      · exact h
      let last : Fin (n - 2) := ⟨n - 3, by omega⟩
      have hval := congrArg Fin.val hfix
      have hl : e last = last := Fin.ext hval
      rw [h, Fin.revPerm_apply] at hl
      have hv := congrArg Fin.val hl
      rw [Fin.val_rev] at hv
      change n - 2 - (n - 3 + 1) = n - 3 at hv
      omega
    have hfixed (i : Fin n) (hi : i.val + 2 < n) : σ i = i := by
      let j : Fin (n - 2) := ⟨i.val, by omega⟩
      have hh := congrFun (congrArg Equiv.toFun he) j
      have hval := congrArg Fin.val hh
      exact Fin.ext hval
    have hcases (i : Fin n) : i.val + 2 < n ∨ i = a ∨ i = b := by
      by_cases hi : i.val + 2 < n
      · exact Or.inl hi
      · right
        by_cases ha : i.val = n - 2
        · exact Or.inl (Fin.ext ha)
        · exact Or.inr (Fin.ext (by change i.val = n - 1; omega))
    have hleaf' (i : Fin n) (hi : n ≤ i.val + 2) : σ i = a ∨ σ i = b :=
      (hcases (σ i)).resolve_left (by have := (hleaf i).mpr hi; omega)
    rcases hleaf' a (by change n ≤ n - 2 + 2; omega) with ha | ha
    · have hb : σ b = b := (hleaf' b (by change n ≤ n - 1 + 2; omega)).resolve_left
        (fun h => hab (σ.injective (ha.trans h.symm)))
      left
      exact Equiv.ext (fun i => (hcases i).elim (hfixed i) (fun h => by rcases h with rfl | rfl <;> assumption))
    · have hb : σ b = a := (hleaf' b (by change n ≤ n - 1 + 2; omega)).resolve_right
        (fun h => hab (σ.injective (ha.trans h.symm)))
      right
      apply Equiv.ext
      intro i
      rcases hcases i with hi | rfl | rfl
      · rw [hfixed i hi, Equiv.swap_apply_of_ne_of_ne]
        · intro h; have hh := congrArg Fin.val h; change i.val = n - 2 at hh; omega
        · intro h; have hh := congrArg Fin.val h; change i.val = n - 1 at hh; omega
      · change σ a = Equiv.swap a b a
        simpa only [Equiv.swap_apply_left] using ha
      · change σ b = Equiv.swap a b b
        simpa only [Equiv.swap_apply_right] using hb
  · rintro (rfl | h)
    · intro i j; rfl
    subst σ
    intro i j
    let e := Equiv.swap a b
    have hle (v : Fin n) : n ≤ (e v).val + 2 ↔ n ≤ v.val + 2 := by
      by_cases ha : v = a
      · subst v; simp [e, a, b]; omega
      by_cases hb : v = b
      · subst v; simp [e, a, b]; omega
      rw [show e v = v from Equiv.swap_apply_of_ne_of_ne ha hb]
    have hfix (v : Fin n) (hv : v.val + 2 < n) : e v = v := by
      apply Equiv.swap_apply_of_ne_of_ne <;> intro h
      · rw [h] at hv; change n - 2 + 2 < n at hv; omega
      · rw [h] at hv; change n - 1 + 2 < n at hv; omega
    have hr' (v : Fin n) : (e v).val + 3 = n ↔ v.val + 3 = n := by
      constructor
      · intro h
        have ht := (not_congr (hle v)).mp (by omega)
        rw [hfix v (by omega)] at h
        exact h
      · intro h
        rw [hfix v (by omega)]
        exact h
    have ha (u v : Fin n) :
        PathAdjacent (e u) (e v) ∧ (e u).val + 2 < n ∧ (e v).val + 2 < n ↔
          PathAdjacent u v ∧ u.val + 2 < n ∧ v.val + 2 < n := by
      constructor
      · rintro ⟨h, hu, hv⟩
        have hu' := (not_congr (hle u)).mp (by omega)
        have hv' := (not_congr (hle v)).mp (by omega)
        rw [hfix u (by omega), hfix v (by omega)] at h
        exact ⟨h, by omega, by omega⟩
      · rintro ⟨h, hu, hv⟩
        rw [hfix u hu, hfix v hv]
        exact ⟨h, hu, hv⟩
    have hAdj : DAdjacent (e i) (e j) ↔ DAdjacent i j :=
      or_congr (ha i j) (or_congr (and_congr (hr' i) (hle j)) (and_congr (hr' j) (hle i)))
    change CartanMatrix.D n i j = CartanMatrix.D n (e i) (e j)
    rw [typeD_edge (by omega) i j, typeD_edge (by omega) (e i) (e j)]
    exact if_congr e.apply_eq_iff_eq.symm rfl (if_congr hAdj.symm rfl rfl)

theorem cartanPermutationTransport : CartanPermutationTransport := by
  intro I J A B e he σ
  constructor
  · intro h i j
    exact ((he (e.symm i) (e.symm j)).trans (by simp)).symm.trans
      ((h (e.symm i) (e.symm j)).trans (he (σ (e.symm i)) (σ (e.symm j))))
  · intro h i j
    have hh := h (e i) (e j)
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hh
    exact (he i j).trans (hh.trans (he (σ i) (σ j)).symm)

private theorem classifyDatum {k : Type u} [Field k] {P : Pinning.SplitBorelPair k}
    (D : Pinning.AttachedDatum P) (W : letI := D.comm; DatumAndWeyl.Identification D.datum)
    (hY : corootLattice D = ⊤)
    (hc : letI := D.comm; (integralDiagram (integralCartan D.datum.rootDatum D.base)).IsConnected) :
    ClassifiedDatum D := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.finiteCocharacters
  letI := D.datum.reduced
  let Q := D.datum.rootDatum
  obtain ⟨hInjective, _, _, _, _, metric, h⟩ := euclideanComparison Q D.base
  letI := metric.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore metric.toCore
  obtain ⟨hInner, hCoroot, hReflection, hR, z, b, hz, _, hPos, hBasis, hb, hCartan, _⟩ := h
  obtain ⟨t, e, he⟩ := classifyCartanOfRootSystem hR hz hb hCartan hc
  obtain ⟨ρ, hρ, hGen⟩ := weylGroupComparison Q hY
  refine ⟨hY, W, W.labelEquiv.symm.trans ρ, ?_, ?_, t, e, he, ?_, ?_⟩
  · intro w i
    change ((ρ (W.labelEquiv.symm w)).val (realRoot Q i)).val = _
    rw [hρ]
    change (1 : ℝ) ⊗ₜ[ℤ] Q.root (Q.weylGroupToPerm (W.labelEquiv.symm w) i) = _
    rw [← Q.weylGroup_apply_root]
    have h := W.characterAction (W.labelEquiv.symm w) i.val
    rw [W.labelEquiv.apply_symm_apply, ← D.datum.root_eq i] at h
    exact congrArg (TensorProduct.mk ℤ ℝ _ (1 : ℝ)) h
  · intro i
    simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hGen i
  · refine ⟨hInjective, ?_, metric, fun w => hInner (ρ (W.labelEquiv.symm w)), hCoroot,
        hReflection, hR, z, b, hz, hPos, hBasis, hb, hCartan, ?_⟩
    · intro i
      change (1 : ℝ) ⊗ₜ[ℤ] Q.root i = _
      rw [D.datum.root_eq]
    · rwa [cartan_diagram_eq hR hz hb hCartan]
  · exact cartanCoordinates Q D.base hY t.cartan e he

open private schemeKernel_exists schemeKernel_sections isMonHom_of_comp_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

theorem noGeometricProduct : NoGeometricProduct := by
  intro k _ G hG H J hH _ hneH hneJ
  refine ⟨fun e => ?_⟩
  let K := AlgebraicClosure k
  let G' := GeometricGroup G
  let p : G'.val ⟶ J.val := e.hom ≫ prod.snd
  let q : G'.val ⟶ H.val := e.hom ≫ prod.fst
  let i : H.val ⟶ G'.val := prod.lift (𝟙 H.val) (0 : H.val ⟶ J.val) ≫ e.inv
  let j : J.val ⟶ G'.val := prod.lift (0 : J.val ⟶ H.val) (𝟙 J.val) ≫ e.inv
  have hip : i ≫ p = 0 := by simp [i, p]
  have hiq : i ≫ q = 𝟙 _ := by simp [i, q]
  have hjp : j ≫ p = 𝟙 _ := by simp [j, p]
  letI := J.property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists p
  letI := N.isClosedImmersion
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  have hi := congrArg (fun f : H.val ⟶ J.val => f.hom.hom) hip
  have hzero : (0 : H.val ⟶ J.val).hom.hom = (1 : H.val.X ⟶ J.val.X) := rfl
  have hni : i.hom.hom ≫ p.hom.hom = 1 := hi.trans hzero
  obtain ⟨a, ha⟩ := (schemeKernel_sections hN i.hom.hom).mpr hni
  letI := isMonHom_of_comp_closed a i N.inclusion ha
  let a' : H.val ⟶ N.group := Grp.homMk a
  have hcomp : a' ≫ N.inclusion = i := Grp.hom_ext _ _ ha
  have hnp : N.inclusion ≫ p = 0 := by
    apply Grp.hom_ext
    exact hN.w
  let b := N.inclusion ≫ q
  have hab : a' ≫ b = 𝟙 _ := by
    rw [show b = N.inclusion ≫ q from rfl, ← Category.assoc, hcomp, hiq]
  have hbi : b ≫ i = N.inclusion := by
    apply (cancel_mono e.hom).mp
    apply prod.hom_ext
    · change (b ≫ i) ≫ e.hom ≫ prod.fst = N.inclusion ≫ e.hom ≫ prod.fst
      rw [Category.assoc]
      change b ≫ i ≫ q = N.inclusion ≫ q
      rw [hiq, Category.comp_id]
    · change (b ≫ i) ≫ e.hom ≫ prod.snd = N.inclusion ≫ e.hom ≫ prod.snd
      rw [Category.assoc]
      change b ≫ i ≫ p = N.inclusion ≫ p
      rw [hip, hnp, comp_zero]
  have hba : b ≫ a' = 𝟙 _ := by
    apply Grp.hom_ext
    apply (cancel_mono N.inclusion.hom.hom).mp
    have h : (b ≫ a') ≫ N.inclusion = N.inclusion := by
      rw [Category.assoc, hcomp, hbi]
    simpa only [Grp.comp_hom_hom, Grp.id_hom_hom, Category.id_comp] using
      congrArg (fun f : N.group ⟶ G'.val => f.hom.hom) h
  let eN : H.val ≅ N.group := ⟨a', b, hab, hba⟩
  have hNo : IsNormalSubgroup N.inclusion := by
    have hn : subgroupConjugation N.inclusion ≫ p.hom.hom = 1 := by
      simp only [subgroupConjugation, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
      have hh : N.inclusion.hom.hom ≫ p.hom.hom = 1 :=
        (congrArg (fun f : N.group ⟶ J.val => f.hom.hom) hnp)
      rw [hh, MonObj.comp_one, mul_one, mul_inv_cancel]
    exact (schemeKernel_sections hN _).mpr hn
  let F := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  let eS := F.mapIso eN
  letI : IsIso eS.inv := inferInstance
  have hs : Smooth N.group.X.hom := by
    have h : eS.inv ≫ H.val.X.hom = N.group.X.hom := eN.inv.hom.hom.w
    rw [← h]
    have hInv : IsOpenImmersion eS.inv := inferInstance
    exact @smooth_comp _ _ eS.inv _ H.val.X.hom (inferInstance : Smooth eS.inv) hH.1
  letI : ConnectedSpace (F.obj H.val) :=
    @GeometricallyConnected.connectedSpace_of_subsingleton _ _ H.val.X.hom hH.2.1
      inferInstance inferInstance
  have hc : ConnectedSpace N.group.X.left :=
    eS.hom.homeomorph.surjective.connectedSpace eS.hom.homeomorph.continuous
  rcases hG.2.2 N ⟨hs, hc, hNo⟩ with ht | hi
  · exact hneH (ht.of_iso eN)
  · letI := hi
    have hp : p = 0 := by
      apply (cancel_epi N.inclusion).mp
      rw [hnp, comp_zero]
    have hj : 𝟙 J.val = 0 := hjp.symm.trans (by rw [hp, comp_zero])
    exact hneJ (((IsZero.iff_id_eq_zero _).mpr hj))

private def splitLattice {J : Type*} (S : Set J) [DecidablePred (· ∈ S)] :
    (J → ℤ) ≃ₗ[ℤ] (S → ℤ) × (↥(Sᶜ) → ℤ) :=
  (LinearEquiv.funCongrLeft ℤ ℤ (Equiv.Set.sumCompl S)).trans
    (LinearEquiv.sumPiEquivProdPi ℤ S (↥(Sᶜ)) (fun _ => ℤ))

private theorem splitLattice_apply {J : Type*} (S : Set J) [DecidablePred (· ∈ S)]
    (a : J → ℤ) :
    splitLattice S a = (fun i => a i.val, fun i => a i.val) := rfl

private theorem restrict_zero_outside {J : Type*} {S : Set J} [DecidablePred (· ∈ S)]
    {a : J → ℤ} (ha : ∀ j ∉ S, a j = 0) :
    splitLattice S a = ((fun i : S => a i.val), 0) := by
  rw [splitLattice_apply]
  exact Prod.ext rfl (funext fun i => ha i.val i.property)

private theorem restrict_zero_inside {J : Type*} {S : Set J} [DecidablePred (· ∈ S)]
    {a : J → ℤ} (ha : ∀ j ∈ S, a j = 0) :
    splitLattice S a = (0, (fun i : ↥(Sᶜ) => a i.val)) := by
  rw [splitLattice_apply]
  exact Prod.ext (funext fun i => ha i.val i.property) rfl

private def coordinatePairing {J : Type*} [Fintype J] [DecidableEq J] :
    (J → ℤ) →ₗ[ℤ] (J → ℤ) →ₗ[ℤ] ℤ :=
  (Pi.basisFun ℤ J).dualBasis.equivFun.symm.toLinearMap

private theorem coordinatePairing_apply {J : Type*} [Fintype J] [DecidableEq J] (a b : J → ℤ) :
    coordinatePairing a b = ∑ j, b j * a j := by
  let c := Pi.basisFun ℤ J
  calc
    coordinatePairing a b = coordinatePairing a (∑ j, c.repr b j • c j) :=
      congrArg (coordinatePairing a) (c.sum_repr b).symm
    _ = _ := by
      simp only [map_sum, map_smul, Int.zsmul_eq_mul, Pi.basisFun_repr, c]
      congr 1
      funext j
      congr 1
      exact (Basis.dualBasis_equivFun c (coordinatePairing a) j).symm.trans
        (congrFun (c.dualBasis.equivFun.apply_symm_apply a) j)

private theorem block_sum {J : Type*} [Fintype J] (S : Set J)
    [DecidablePred (· ∈ S)] (g : J → ℤ) (hg : ∀ j ∉ S, g j = 0) :
    (∑ j : S, g j.val) = ∑ j, g j := by
  have h := Fintype.sum_subtype_add_sum_subtype (· ∈ S) g
  have hz : (∑ j : {j // j ∉ S}, g j.val) = 0 := Finset.sum_eq_zero fun j _ => hg j.val j.property
  rw [hz, add_zero] at h
  exact h

section BlockDatum

variable {I X Y J : Type*} [Finite I] [AddCommGroup X] [AddCommGroup Y] [Fintype J] [DecidableEq J]
variable (P : RootDatum I X Y)
  (x : X ≃ₗ[ℤ] (J → ℤ)) (y : Y ≃ₗ[ℤ] (J → ℤ)) (S : Set J)
  [DecidablePred (· ∈ S)]
  (hpair : ∀ a b, P.toLinearMap a b = ∑ j, y b j * x a j)

private abbrev blockIndex :=
  {i : I // SupportedOn S (x (P.root i), y (P.coroot i))}

private theorem preserveBlock (i j : blockIndex P x y S) :
    SupportedOn S (x (P.root (P.reflectionPerm i.val j.val)),
      y (P.coroot (P.reflectionPerm i.val j.val))) := by
  intro b hb
  rw [← P.reflectionPerm_root, ← P.reflectionPerm_coroot]
  obtain ⟨hi, hi'⟩ := i.property b hb
  obtain ⟨hj, hj'⟩ := j.property b hb
  change x (P.root i.val) b = 0 at hi
  change x (P.root j.val) b = 0 at hj
  change y (P.coroot i.val) b = 0 at hi'
  change y (P.coroot j.val) b = 0 at hj'
  simp [hi, hi', hj, hj']

private def blockDatum : RootDatum (blockIndex P x y S) (S → ℤ) (S → ℤ) where
  toLinearMap := coordinatePairing
  isPerfPair_toLinearMap := LinearMap.IsPerfPair.of_bijective _ <|
    (Pi.basisFun ℤ S).dualBasis.equivFun.symm.bijective
  root := ⟨fun i j => x (P.root i.val) j.val, by
    intro i j h
    apply Subtype.ext
    apply P.root.injective
    apply x.injective
    apply (splitLattice S).injective
    rw [restrict_zero_outside (fun b hb => (i.property b hb).1),
      restrict_zero_outside (fun b hb => (j.property b hb).1)]
    exact Prod.ext h rfl⟩
  coroot := ⟨fun i j => y (P.coroot i.val) j.val, by
    intro i j h
    apply Subtype.ext
    apply P.coroot.injective
    apply y.injective
    apply (splitLattice S).injective
    rw [restrict_zero_outside (fun b hb => (i.property b hb).2),
      restrict_zero_outside (fun b hb => (j.property b hb).2)]
    exact Prod.ext h rfl⟩
  root_coroot_two i := by
    rw [coordinatePairing_apply]
    change (∑ b : S, y (P.coroot i.val) b.val * x (P.root i.val) b.val) = 2
    rw [block_sum S (fun b => y (P.coroot i.val) b * x (P.root i.val) b)
      (fun b hb => mul_eq_zero_of_left (i.property b hb).2 _), ← hpair, P.root_coroot_two]
  reflectionPerm i :=
    { toFun := fun j => ⟨P.reflectionPerm i.val j.val, preserveBlock P x y S i j⟩
      invFun := fun j => ⟨P.reflectionPerm i.val j.val, preserveBlock P x y S i j⟩
      left_inv := fun j => Subtype.ext (P.reflectionPerm_self i.val j.val)
      right_inv := fun j => Subtype.ext (P.reflectionPerm_self i.val j.val) }
  reflectionPerm_root i j := by
    rw [coordinatePairing_apply]
    change (fun b : S => x (P.root j.val) b.val) -
      (∑ b : S, y (P.coroot i.val) b.val * x (P.root j.val) b.val) •
        (fun b : S => x (P.root i.val) b.val) = fun b : S =>
          x (P.root (P.reflectionPerm i.val j.val)) b.val
    rw [block_sum S (fun b => y (P.coroot i.val) b * x (P.root j.val) b)
      (fun b hb => mul_eq_zero_of_left (i.property b hb).2 _), ← hpair, ← P.reflectionPerm_root]
    funext b
    simp
  reflectionPerm_coroot i j := by
    rw [coordinatePairing_apply]
    change (fun b : S => y (P.coroot j.val) b.val) -
      (∑ b : S, y (P.coroot j.val) b.val * x (P.root i.val) b.val) •
        (fun b : S => y (P.coroot i.val) b.val) = fun b : S =>
          y (P.coroot (P.reflectionPerm i.val j.val)) b.val
    rw [block_sum S (fun b => y (P.coroot j.val) b * x (P.root i.val) b)
      (fun b hb => mul_eq_zero_of_left (j.property b hb).2 _), ← hpair,
      ← P.reflectionPerm_coroot]
    funext b
    simp

private theorem blockDatum_reduced [P.IsReduced] : (blockDatum P x y S hpair).IsReduced := by
  constructor
  intro i j hij
  have hf : ¬ LinearIndependent ℤ ![P.root i.val, P.root j.val] := by
    intro h
    apply hij
    let g : (S → ℤ) →ₗ[ℤ] X :=
      (x.trans (splitLattice S)).symm.toLinearMap.comp (LinearMap.inl ℤ _ _)
    apply LinearIndependent.of_comp g
    have he (a : blockIndex P x y S) : g ((blockDatum P x y S hpair).root a) = P.root a.val := by
      apply (x.trans (splitLattice S)).injective
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact (restrict_zero_outside fun b hb => (a.property b hb).1).symm
    convert h using 1
    funext l
    fin_cases l <;> simp [he]
  obtain h | h := RootPairing.IsReduced.eq_or_eq_neg (P := P) i.val j.val hf
  · left
    exact congrArg (fun a => fun t : S => x a t.val) h
  · right
    funext t
    change x (P.root i.val) t.val = -x (P.root j.val) t.val
    rw [h, map_neg, Pi.neg_apply]

private theorem blockDatum_coroot_span (s : J → I)
    (hs : ∀ j, y (P.coroot (s j)) = Pi.single j 1)
    (hm : ∀ j ∈ S, s j ∈ {i | SupportedOn S (x (P.root i), y (P.coroot i))}) :
    Submodule.span ℤ (range (blockDatum P x y S hpair).coroot) = ⊤ := by
  let c := Pi.basisFun ℤ S
  apply top_unique
  rw [← c.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨s j.val, hm j.val j.property⟩, ?_⟩
  funext l
  change y (P.coroot (s j.val)) l.val = c j l
  rw [hs, Pi.basisFun_apply]
  simp [Pi.single_apply, Subtype.ext_iff]

end BlockDatum

section RootEquivalence

variable {I J X Y X' Y' : Type u} [Finite I]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']

/-- A root bijection on the full character lattice also determines the coroot
map when the roots span a sublattice of finite index. -/
private def rootEquivOfRootMap (P : RootDatum I X Y)
    (Q : RootDatum J X' Y')
    [Module.IsTorsionFree ℤ X] (hfin : Finite (X ⧸ Submodule.span ℤ (range P.root)))
    (e : I ≃ J) (f : X ≃ₗ[ℤ] X') (hf : ∀ i, f (P.root i) = Q.root (e i)) :
    P.Equiv Q := by
  let g := Q.flip.toPerfPair.trans (f.dualMap.trans P.flip.toPerfPair.symm)
  have hcor (i : I) : f.toLinearMap.dualMap (Q.coroot' (e i)) = P.coroot' i := by
    let p := P.coroot' i
    let q := f.toLinearMap.dualMap (Q.coroot' (e i))
    let L := Submodule.span ℤ (range P.root)
    have hq : q (P.root i) = 2 := by
      change Q.toLinearMap (f (P.root i)) (Q.coroot (e i)) = 2
      rw [hf, Q.root_coroot_two]
    have hmap : MapsTo (preReflection (P.root i) q) (range P.root) (range P.root) := by
      rintro _ ⟨j, rfl⟩
      refine ⟨e.symm (Q.reflectionPerm (e i) (e j)), f.injective ?_⟩
      rw [hf, e.apply_symm_apply, ← Q.reflectionPerm_root]
      have heval : q (P.root j) = Q.toLinearMap (Q.root (e j)) (Q.coroot (e i)) := by
        change Q.toLinearMap (f (P.root j)) (Q.coroot (e i)) = _
        rw [hf]
      simp only [preReflection_apply, map_sub, map_smul, hf, heval]
    have hpq : L.subtype.dualMap q = L.subtype.dualMap p :=
      Dual.eq_of_preReflection_mapsTo' (Set.finite_range _) (Submodule.subset_span (mem_range_self i))
        hq hmap (P.coroot_root_two i) (P.mapsTo_reflection_root i)
    letI : Finite (X ⧸ L.toAddSubgroup) := hfin
    have hn : (L.toAddSubgroup.index : ℤ) ≠ 0 :=
      Int.ofNat_ne_zero.mpr AddSubgroup.index_ne_zero_of_finite
    ext a
    have ha : L.toAddSubgroup.index • a ∈ L :=
      AddSubgroup.nsmul_index_mem L.toAddSubgroup a
    have heq := LinearMap.congr_fun hpq ⟨_, ha⟩
    change q (L.toAddSubgroup.index • a) = p (L.toAddSubgroup.index • a) at heq
    simp only [map_nsmul, nsmul_eq_mul] at heq
    exact mul_left_cancel₀ hn heq
  exact {
    weightMap := f
    coweightMap := g
    indexEquiv := e
    weight_coweight_transpose := by ext; simp [g]
    root_weightMap := funext hf
    coroot_coweightMap := by
      funext j
      obtain ⟨i, rfl⟩ := e.surjective j
      apply P.flip.toPerfPair.injective
      change P.flip.toPerfPair (g (Q.coroot (e i))) =
        P.flip.toPerfPair (P.coroot (e.symm (e i)))
      rw [e.symm_apply_apply]
      simp only [g, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      ext a
      exact LinearMap.congr_fun (hcor i) a
    bijective_weightMap := f.bijective
    bijective_coweightMap := g.bijective }

private theorem coroot_span_of_equiv (P : RootDatum I X Y)
    (Q : RootDatum J X' Y') (e : P.Equiv Q)
    (h : Submodule.span ℤ (range P.coroot) = ⊤) :
    Submodule.span ℤ (range Q.coroot) = ⊤ := by
  have hset : range Q.coroot = e.coweightEquiv.symm '' range P.coroot := by
    ext b
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, mem_range_self (e.indexEquiv.symm j),
        e.coweightEquiv.symm_apply_eq.mpr
          (e.toHom.coroot_coweightMap_apply P Q j).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨e.indexEquiv i, ?_⟩
      apply e.coweightEquiv.injective
      simpa using e.toHom.coroot_coweightMap_apply P Q (e.indexEquiv i)
  calc
    _ = (Submodule.span ℤ (range P.coroot)).map e.coweightEquiv.symm.toLinearMap := by
      rw [Submodule.map_span, hset]
      rfl
    _ = ⊤ := by rw [h, Submodule.map_top]; exact LinearMap.range_eq_top.mpr e.coweightEquiv.symm.surjective

end RootEquivalence

section GeometricProducts

open Specs.GeometricRadicals
open CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.GrpObj
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.Pinning (SplitBorelPair)
open Specs.CharacterDescent (Character)
open Specs.RankOneFlag (IsGeometricallyMaximal)

open private affineProduct tensorClosedImmersion
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private geometricallyConnected_of_connected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private quotient_smooth_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
open private normalSubgroup_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
open private trivialOfSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private isMonHom_of_comp_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private geometricallyMaximal_of_maximal_split
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private image_of_geometric_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
open private isTorus_iff_coordinates torus_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private pointsFullyFaithful from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]

private abbrev firstInclusion (G H : GroupScheme k) : G ⟶ G ⊗ H :=
  lift (𝟙 G) (0 : G ⟶ H)

private abbrev secondInclusion (G H : GroupScheme k) : H ⟶ G ⊗ H :=
  lift (0 : H ⟶ G) (𝟙 H)

/-- A split projection carries a normal subgroup to a normal image. Closed
factorization descends from the surjective map of smooth schemes. -/
private theorem normal_projected_image
    {G A Q N : GroupScheme k} {i : N ⟶ A} (hi : IsNormalSubgroup i)
    (f : A ⟶ G) (s : G ⟶ A) (hs : s ≫ f = 𝟙 G)
    (p : N ⟶ Q) (j : Q ⟶ G) (hp : p ≫ j = i ≫ f)
    (hj : IsClosedImmersion j.hom.hom.left)
    (hS : Surjective p.hom.hom.left) (hG : Smooth G.X.hom) (hQ : Smooth Q.X.hom) :
    IsNormalSubgroup j := by
  let a := 𝟙 G.X ⊗ₘ p.hom.hom
  let c := subgroupConjugation j
  let x := fst G.X N.X
  let y := snd G.X N.X
  obtain ⟨b, hb⟩ := normalSubgroup_conjugate_sections hi (x ≫ s.hom.hom) y
  have he : p.hom.hom ≫ j.hom.hom = i.hom.hom ≫ f.hom.hom :=
    congrArg (fun l : N ⟶ G => l.hom.hom) hp
  have ht : s.hom.hom ≫ f.hom.hom = 𝟙 G.X :=
    congrArg (fun l : G ⟶ G => l.hom.hom) hs
  have ha : a ≫ c = (b ≫ p.hom.hom) ≫ j.hom.hom := by
    rw [Category.assoc, he, ← Category.assoc, hb]
    simp [a, c, x, y, subgroupConjugation, MonObj.comp_mul, MonObj.mul_comp,
      GrpObj.comp_inv, GrpObj.inv_comp, Category.assoc, ht, he]
  letI : Surjective p.hom.hom.left := hS
  letI : Surjective a.left := by
    change Surjective ((𝟙 G.X ⊗ₘ p.hom.hom).left)
    rw [Over.tensorHom_left, pullback_map_eq_pullbackFstFstIso_inv]
    infer_instance
  have hs : Smooth (G.X ⊗ Q.X).hom := by
    letI : Smooth G.X.hom := hG
    letI : Smooth Q.X.hom := hQ
    rw [Over.tensorObj_hom]
    infer_instance
  letI : Smooth (G.X ⊗ Q.X).hom := hs
  letI : IsReduced (G.X ⊗ Q.X).left := isReduced_of_smooth_over_field (G.X ⊗ Q.X).hom
  letI : IsSchemeTheoreticallyDominant a.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  letI := hj
  have ha' : a.left ≫ c.left = (b ≫ p.hom.hom).left ≫ j.hom.hom.left :=
    congrArg (fun q : G.X ⊗ N.X ⟶ G.X => q.left) ha
  have hak : (a.left ≫ c.left).ker = c.left.ker := by
    rw [Scheme.Hom.ker_comp, a.left.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have hl : j.hom.hom.left.ker ≤ c.left.ker := by
    rw [← hak, ha']
    exact Scheme.Hom.le_ker_comp _ _
  let m := IsClosedImmersion.lift j.hom.hom.left c.left hl
  have hm : m ≫ j.hom.hom.left = c.left := IsClosedImmersion.lift_fac _ _ _
  have hw : m ≫ Q.X.hom = (G.X ⊗ Q.X).hom := by
    rw [← Over.w j.hom.hom, ← Category.assoc, hm, Over.w c]
  exact ⟨Over.homMk m hw, Over.OverMorphism.ext hm⟩

private theorem unipotent_normal_projection_zero
    (G : AffineAlgebraicGroup k) (H : AffineAlgebraicGroup (AlgebraicClosure k))
    (hG : IsReductive G)
    {N : AffineAlgebraicGroup (AlgebraicClosure k)} (i : N.val ⟶ (GeometricGroup G).val ⊗ H.val)
    (hn : IsNormalSubgroup i) (hs : Smooth N.val.X.hom)
    (hc : ConnectedSpace N.val.X.left) (hu : Specs.Unipotent.IsUnipotent N) :
    i ≫ fst (GeometricGroup G).val H.val = 0 := by
  let G' := GeometricGroup G
  let f := fst G'.val H.val
  obtain ⟨Q, p, j, hf, _, _⟩ := schemeImageFactorization N G' (i ≫ f)
  have hq := quotient_smooth_connected p hf.2.1 hf.2.2.1 hs hc
  have hgs : Smooth G'.val.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.val.X.hom
      (fieldSpecMap k (AlgebraicClosure k))) hG.1
  have hj := normal_projected_image hn f (firstInclusion G'.val H.val)
    (lift_fst _ _) p j hf.1 hf.2.2.2.2.2 hf.2.2.1 hgs hq.1
  let J : ClosedSubgroup G'.val := ⟨Q.val, j, hf.2.2.2.2.2⟩
  have huQ : Specs.Unipotent.IsUnipotent Q :=
    Unipotent.faithfullyFlatQuotientsUnipotent N Q p hf.2.1 hf.2.2.1 hu
  have huJ : Specs.Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup (G := G') J) := by
    exact huQ
  have ht := trivialOfSubgroup
    ((GeometricRadicals.geometricUnipotentRadicalLargest G).2.2 J ⟨hq.1, hq.2, hj⟩ huJ) hG.2.2
  obtain ⟨e⟩ := ht
  have hz : IsZero Q.val := (Grp.isZero_trivial _).of_iso e
  exact hf.1.symm.trans (by rw [hz.eq_zero_of_src j, comp_zero])

private theorem productReductive [IsAlgClosed k] (G H : AffineAlgebraicGroup k)
    (hG : IsReductive G) (hH : IsReductive H) : IsReductive (affineProduct G H) := by
  let P := affineProduct G H
  have hGc := @GeometricallyConnected.connectedSpace_of_subsingleton _ _ G.val.X.hom hG.2.1
    inferInstance inferInstance
  have hHc := @GeometricallyConnected.connectedSpace_of_subsingleton _ _ H.val.X.hom hH.2.1
    inferInstance inferInstance
  obtain ⟨hPs, hPc, _⟩ :=
    WordDomainGeometry.smoothConnectedGroupProduct G H hG.1 hGc hH.1 hHc
  letI : ConnectedSpace P.val.X.left := hPc
  refine ⟨hPs, geometricallyConnected_of_connected P, ?_⟩
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let e := (Functor.Monoidal.μIso F G.val H.val).symm
  let N := geometricUnipotentRadical P
  let A := closedSubgroupAlgebraicGroup (G := GeometricGroup P) N
  have hN := GeometricRadicals.geometricUnipotentRadicalLargest P
  let i : A.val ⟶ (GeometricGroup G).val ⊗ (GeometricGroup H).val := N.inclusion ≫ e.hom
  have hn : IsNormalSubgroup i := by
    apply normalSubgroup_of_iso e.symm (Iso.refl N.group) (i := N.inclusion)
    · change (N.inclusion ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ N.inclusion
      simp
    · exact hN.1.2.2
  let d := (BraidedCategory.braiding (GeometricGroup G).val (GeometricGroup H).val)
  have hnd : IsNormalSubgroup (i ≫ d.hom) := by
    apply normalSubgroup_of_iso d.symm (Iso.refl A.val) (i := i)
    · simp
    · exact hn
  have h1 := unipotent_normal_projection_zero G (GeometricGroup H) hG i hn hN.1.1 hN.1.2.1 hN.2.1
  have h2' := unipotent_normal_projection_zero H (GeometricGroup G) hH
    (i ≫ d.hom) hnd hN.1.1 hN.1.2.1 hN.2.1
  have h2 : i ≫ snd (GeometricGroup G).val (GeometricGroup H).val = 0 := by
    simpa [d, Category.assoc] using h2'
  have hiz : i = 0 := CartesianMonoidalCategory.hom_ext _ _ (by simpa using h1) (by simpa using h2)
  have hNz : N.inclusion = 0 := (cancel_mono e.hom).mp (by simpa using hiz)
  letI := N.isClosedImmersion
  letI : Mono N.inclusion :=
    (Grp.forget (SchemeOver K) ⋙ Over.forget _).mono_of_mono_map
      (show Mono N.inclusion.hom.hom.left from inferInstance)
  exact ⟨(IsZero.of_mono_eq_zero N.inclusion hNz).iso (Grp.isZero_trivial _)⟩

private abbrev productTorus (P Q : SplitBorelPair k) : ClosedSubgroup (affineProduct P.G Q.G).val :=
  ⟨P.T.group ⊗ Q.T.group, P.T.inclusion ⊗ₘ Q.T.inclusion, by
    letI := P.T.isClosedImmersion
    letI := Q.T.isClosedImmersion
    exact tensorClosedImmersion P.T.inclusion.hom.hom Q.T.inclusion.hom.hom⟩

private def productPointEquiv (G H : GroupScheme k) (R : TestAlgebra k) :
    AdjointRepresentation.GroupPoints (G ⊗ H) R ≃*
      AdjointRepresentation.GroupPoints G R × AdjointRepresentation.GroupPoints H R where
  toFun t := (t ≫ fst G.X H.X, t ≫ snd G.X H.X)
  invFun q := lift q.1 q.2
  left_inv := lift_comp_fst_snd
  right_inv q := Prod.ext (lift_fst _ _) (lift_snd _ _)
  map_mul' _ _ := Prod.ext (MonObj.mul_comp _ _ _) (MonObj.mul_comp _ _ _)

private theorem splitProductTorus (P Q : SplitBorelPair k) :
    IsSplitTorus (productTorus P Q).group := by
  classical
  obtain ⟨m, ⟨p⟩⟩ := P.split
  obtain ⟨n, ⟨q⟩⟩ := Q.split
  let G := StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin m))
  let H := StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin n))
  let D := StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin (m+n)))
  let e : (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n)) ≃ ULift.{u} (Fin (m+n)) :=
    (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans (finSumFinEquiv.trans Equiv.ulift.symm)
  let C := affineProduct G H
  let ep := LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso k (ULift.{u} (Fin m))
  let eqIso := LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso k (ULift.{u} (Fin n))
  let ed := LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso k (ULift.{u} (Fin (m+n)))
  let ef (R : TestAlgebra k) :
      ((ULift.{u} (Fin m) → Rˣ) × (ULift.{u} (Fin n) → Rˣ)) ≃*
        (ULift.{u} (Fin (m+n)) → Rˣ) :=
    { toEquiv := (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
        (Equiv.arrowCongr e (Equiv.refl _))
      map_mul' := by
        intro a b
        funext j
        change Sum.elim (a.1 * b.1) (a.2 * b.2) (e.symm j) =
          Sum.elim a.1 a.2 (e.symm j) * Sum.elim b.1 b.2 (e.symm j)
        cases e.symm j <;> rfl }
  let ez (R : TestAlgebra k) := (productPointEquiv G.val H.val R).trans
    (((ep.app R).groupIsoToMulEquiv.prodCongr (eqIso.app R).groupIsoToMulEquiv).trans
      ((ef R).trans (ed.app R).symm.groupIsoToMulEquiv))
  have hed (R : TestAlgebra k) (t : AdjointRepresentation.GroupPoints C.val R) :
      (ed.hom.app R) (ez R t) =
        ef R ((ep.hom.app R) (t ≫ fst G.val.X H.val.X),
          (eqIso.hom.app R) (t ≫ snd G.val.X H.val.X)) := by
    exact (ed.app R).groupIsoToMulEquiv.apply_symm_apply _
  have ePoints : (groupPointsFunctor k).obj C.val ≅ (groupPointsFunctor k).obj D.val := by
    refine NatIso.ofComponents (fun R => (ez R).toGrpIso) ?_
    intro R S a
    apply GrpCat.ext
    intro t
    apply (ed.app S).groupIsoToMulEquiv.injective
    have hd := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ed.hom.naturality a)) (ez R t)
    have hp := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ep.hom.naturality a))
      (productPointEquiv G.val H.val R t).1
    have hq := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (eqIso.hom.naturality a))
      (productPointEquiv G.val H.val R t).2
    change (ed.hom.app S) (ez S (mapPoints a t)) =
      (ed.hom.app S) (mapPoints a (ez R t))
    change (ed.hom.app S) (mapPoints a (ez R t)) = _ at hd
    rw [hd, hed]
    change _ = (Specs.StandardGroups.multiplicativePowerPoints k (ULift.{u} (Fin (m+n)))).map a
      ((ed.hom.app R) (ez R t))
    rw [hed]
    change ef S ((ep.hom.app S) (mapPoints a (t ≫ fst G.val.X H.val.X)),
      (eqIso.hom.app S) (mapPoints a (t ≫ snd G.val.X H.val.X))) =
      (Specs.StandardGroups.multiplicativePowerPoints k (ULift.{u} (Fin (m+n)))).map a
        (ef R ((ep.hom.app R) (t ≫ fst G.val.X H.val.X),
          (eqIso.hom.app R) (t ≫ snd G.val.X H.val.X)))
    change (ep.hom.app S) (mapPoints a (t ≫ fst G.val.X H.val.X)) = _ at hp
    change (eqIso.hom.app S) (mapPoints a (t ≫ snd G.val.X H.val.X)) = _ at hq
    rw [hp, hq]
    funext j
    change Sum.elim
      (fun i => Units.map a.hom.toMonoidHom (((ep.hom.app R) (t ≫ fst G.val.X H.val.X)) i))
      (fun i => Units.map a.hom.toMonoidHom (((eqIso.hom.app R) (t ≫ snd G.val.X H.val.X)) i))
      (e.symm j) = Units.map a.hom.toMonoidHom
        (Sum.elim ((ep.hom.app R) (t ≫ fst G.val.X H.val.X))
          ((eqIso.hom.app R) (t ≫ snd G.val.X H.val.X)) (e.symm j))
    cases e.symm j <;> rfl
  let E : C.val ≅ D.val := ((inducedFunctor Subtype.val : AffineAlgebraicGroupCategory k ⥤ _)).mapIso
    ((pointsFullyFaithful k).preimageIso (X := C) (Y := D) ePoints)
  exact ⟨m+n, ⟨(MonoidalCategory.tensorIso p q) ≪≫ E⟩⟩

open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private theorem projection_factors_through_torus
    (P : SplitBorelPair k) {S : GroupScheme k} [IsCommMonObj S.X]
    (f : S ⟶ P.G.val) (s : P.T.group ⟶ S) (hs : s ≫ f = P.T.inclusion) :
    ∃ r : S ⟶ P.T.group, r ≫ P.T.inclusion = f := by
  have hcent := Reductive.TorusCentralizer.maximalTorusCentralizer
    P.G P.reductive P.T (lattice_torus_of_split P.split) P.maximal
  have hf : Centralizes P.T.inclusion f.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro U x y
    have h : Commute x (y ≫ s.hom.hom) := mul_comm _ _
    have h' := h.map (IsMonHom.monoidHom f.hom.hom U)
    change Commute (x ≫ f.hom.hom) (y ≫ s.hom.hom ≫ f.hom.hom) at h'
    rw [show s.hom.hom ≫ f.hom.hom = P.T.inclusion.hom.hom from
      congrArg (fun g : P.T.group ⟶ P.G.val => g.hom.hom) hs] at h'
    exact h'
  obtain ⟨v, hv⟩ := (hcent _ _).mp hf
  letI := P.T.isClosedImmersion
  letI := isMonHom_of_comp_closed v f P.T.inclusion hv
  exact ⟨Grp.homMk v, Grp.hom_ext _ _ hv⟩

private theorem productTorus_geometricallyMaximal [IsAlgClosed k] (P Q : SplitBorelPair k) :
    IsGeometricallyMaximal (productTorus P Q) := by
  let R := affineProduct P.G Q.G
  let T := productTorus P Q
  have hsplit := splitProductTorus P Q
  apply geometricallyMaximal_of_maximal_split R T ?_ hsplit
  refine ⟨lattice_torus_of_split hsplit, ?_⟩
  intro S hS hTS
  obtain ⟨a, ha⟩ := hTS
  change a ≫ S.inclusion = P.T.inclusion ⊗ₘ Q.T.inclusion at ha
  letI : IsCommMonObj S.group.X :=
    torus_commutative (closedSubgroupAlgebraicGroup (G := R) S) hS
  let f := S.inclusion ≫ fst P.G.val Q.G.val
  let g := S.inclusion ≫ snd P.G.val Q.G.val
  let s := firstInclusion P.T.group Q.T.group ≫ a
  let t := secondInclusion P.T.group Q.T.group ≫ a
  have hs : s ≫ f = P.T.inclusion := by
    dsimp only [s, f]
    rw [Category.assoc, ← Category.assoc a, ha]
    simp
  have ht : t ≫ g = Q.T.inclusion := by
    dsimp only [t, g]
    rw [Category.assoc, ← Category.assoc a, ha]
    simp
  obtain ⟨v, hv⟩ := projection_factors_through_torus P f s hs
  obtain ⟨w, hw⟩ := projection_factors_through_torus Q g t ht
  refine ⟨lift v w, ?_⟩
  change lift v w ≫ (P.T.inclusion ⊗ₘ Q.T.inclusion) = S.inclusion
  apply CartesianMonoidalCategory.hom_ext
  · simp [hv, f]
  · simp [hw, g]

open Specs.AdjointRepresentation (GroupPoints dualMap constants scale)
open Specs.CharacterPairing (characterValue adjointWeightVectors absoluteRoots)
open Specs.AbstractPairing (Root)
open private characterValue_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

private abbrev pointPost {G H : GroupScheme k} (f : G ⟶ H) (R : TestAlgebra k) :
    GroupPoints G R →* GroupPoints H R :=
  ((groupPointsFunctor k).map f).app R |>.hom

private theorem characterValue_pullback {G H : GroupScheme k} (f : G ⟶ H)
    (χ : Character H) (R : TestAlgebra k) (t : GroupPoints G R) :
    characterValue (f ≫ χ) R t = characterValue χ R (pointPost f R t) := by
  unfold characterValue
  simp only [Grp.comp_hom_hom, Category.assoc]
  rfl

private def scaledBaseTangent {G : GroupScheme k} (R : TestAlgebra k) (v : Lie k G) (a : R) :
    GroupPoints G (CommAlgCat.of k (DualNumber R)) :=
  mapPoints (scale R a)
    (mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val)

private def tangentEquation {G : GroupScheme k} (R : TestAlgebra k)
    (g : GroupPoints G R) (v : Lie k G) (a : R) : Prop :=
  let p := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val
  let c := mapPoints (constants R) g
  c * p * c⁻¹ = scaledBaseTangent R v a

private theorem tangentEquation_congr {G : GroupScheme k} (R : TestAlgebra k)
    {g g' : GroupPoints G R} {v v' : Lie k G} {a a' : R}
    (hg : g = g') (hv : v = v') (ha : a = a') :
    tangentEquation (G := G) R g v a = tangentEquation (G := G) R g' v' a' := by
  cases hg
  cases hv
  cases ha
  rfl

private theorem changes_one {G : GroupScheme k} {R S : TestAlgebra k} (f : R ⟶ S) :
    mapPoints f (1 : GroupPoints G R) = (1 : GroupPoints G S) :=
  (((groupPointsFunctor k).obj G).map f).hom.map_one

private theorem tangentEquation_zero {G : GroupScheme k} (R : TestAlgebra k)
    (g : GroupPoints G R) (a : R) : tangentEquation R g 0 a := by
  unfold tangentEquation scaledBaseTangent
  change _ * mapPoints _ (1 : GroupPoints G (CommAlgCat.of k (DualNumber k))) * _ =
    mapPoints _ (mapPoints _ (1 : GroupPoints G (CommAlgCat.of k (DualNumber k))))
  simp only [changes_one, mul_one, mul_inv_cancel]

private theorem tangentEquation_one_point {G : GroupScheme k} {R : TestAlgebra k}
    (v : Lie k G) (a : R) (h : tangentEquation R 1 v a) :
    scaledBaseTangent R v a = scaledBaseTangent R v 1 := by
  have hscale : scale R (1 : R) = 𝟙 _ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    exact TrivSqZeroExt.ext rfl (one_mul _)
  unfold tangentEquation at h
  dsimp only at h
  simp only [changes_one, one_mul, inv_one, mul_one] at h
  change scaledBaseTangent R v a = (testSpec k).map (scale R (1 : R)).op ≫ _
  rw [hscale]
  change scaledBaseTangent R v a = (testSpec k).map (𝟙 _) ≫ _
  rw [(testSpec k).map_id, Category.id_comp]
  exact h.symm

/-- A nonzero tangent coordinate over the field stays a unit in every test algebra. -/
private theorem scaledBaseTangent_injective (G : AffineAlgebraicGroup k)
    (v : Lie k G.val) (hv : v ≠ 0) (R : TestAlgebra k) :
    Function.Injective (scaledBaseTangent R v) := by
  classical
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨n, b, C, _, _, _, _, _, _⟩ := adjointRepresentation k G s
  let q := b.equivFun v
  have hh : ∃ j, q j ≠ 0 := by
    by_contra! h
    apply hv
    apply b.equivFun.injective
    have hz := b.equivFun.map_zero
    rw [hz]
    exact funext h
  obtain ⟨j, hj⟩ := hh
  let f : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  let w (i : ULift.{u} (Fin n)) := f.hom (q i)
  have he : (C.equiv R w).toMul.val = mapPoints (dualMap f) v.toMul.val :=
    (C.naturality f q).trans (congrArg (mapPoints (dualMap f)) (C.at_base v))
  intro a b hab
  have ha : (C.equiv R (a • w)).toMul.val = (C.equiv R (b • w)).toMul.val := by
    rw [C.smul, C.smul, he]
    exact hab
  have hb := congrFun ((C.equiv R).injective (Subtype.ext ha)) j
  change a * algebraMap k R (q j) = b * algebraMap k R (q j) at hb
  have hunit : IsUnit (algebraMap k R (q j)) :=
    (isUnit_iff_ne_zero.mpr hj).map (algebraMap k R)
  exact hunit.mul_right_cancel hb

private theorem map_tangentEquation {G H : GroupScheme k} (f : G ⟶ H)
    (R : TestAlgebra k) (g : GroupPoints G R) (v : Lie k G) (a : R) :
    let post := pointPost f (CommAlgCat.of k (DualNumber R))
    let p := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val
    let c := mapPoints (constants R) g
    (post (c * p * c⁻¹) = post (scaledBaseTangent R v a)) ↔
      tangentEquation R (pointPost f R g) (mapPointKernel f v) a := by
  simp only [tangentEquation, map_mul, map_inv]
  rfl

private theorem product_tangentEquation (G H : GroupScheme k) (R : TestAlgebra k)
    (g : GroupPoints (G ⊗ H) R) (v : Lie k (G ⊗ H)) (a : R) :
    tangentEquation R g v a ↔
      tangentEquation R (pointPost (fst G H) R g) (mapPointKernel (fst G H) v) a ∧
      tangentEquation R (pointPost (snd G H) R g) (mapPointKernel (snd G H) v) a := by
  have hp := map_tangentEquation (fst G H) R g v a
  have hq := map_tangentEquation (snd G H) R g v a
  exact ⟨fun h => ⟨hp.mp (congrArg _ h), hq.mp (congrArg _ h)⟩,
    fun ⟨h₁, h₂⟩ => CartesianMonoidalCategory.hom_ext _ _ (hp.mpr h₁) (hq.mpr h₂)⟩

private theorem restrict_product_character {G H : GroupScheme k} (χ : Character (G ⊗ H)) :
    (fst G H ≫ firstInclusion G H ≫ χ) * (snd G H ≫ secondInclusion G H ≫ χ) = χ := by
  apply Grp.hom_ext
  change (fst G.X H.X ≫ (firstInclusion G H).hom.hom ≫ χ.hom.hom) *
    (snd G.X H.X ≫ (secondInclusion G H).hom.hom ≫ χ.hom.hom) = χ.hom.hom
  letI : MonObj (Grp.toMon (G ⊗ H)).X := (G ⊗ H).grp.toMonObj
  letI : IsMonHom χ.hom.hom := χ.hom.isMonHom_hom
  rw [← Category.assoc (fst G.X H.X), ← Category.assoc (snd G.X H.X), ← MonObj.mul_comp]
  let a := (firstInclusion G H).hom.hom
  let b := (secondInclusion G H).hom.hom
  let p := (fst G H).hom.hom
  let q := (snd G H).hom.hom
  letI : IsMonHom p := (fst G H).hom.isMonHom_hom
  letI : IsMonHom q := (snd G H).hom.isMonHom_hom
  have hap : a ≫ p = 𝟙 G.X :=
    congrArg (fun f : G ⟶ G => f.hom.hom) (lift_fst (𝟙 G) (0 : G ⟶ H))
  have haq : a ≫ q = (1 : G.X ⟶ H.X) :=
    congrArg (fun f : G ⟶ H => f.hom.hom) (lift_snd (𝟙 G) (0 : G ⟶ H))
  have hbp : b ≫ p = (1 : H.X ⟶ G.X) :=
    congrArg (fun f : H ⟶ G => f.hom.hom) (lift_fst (0 : H ⟶ G) (𝟙 H))
  have hbq : b ≫ q = 𝟙 H.X :=
    congrArg (fun f : H ⟶ H => f.hom.hom) (lift_snd (0 : H ⟶ G) (𝟙 H))
  have h : (p ≫ a) * (q ≫ b) = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · change ((p ≫ a) * (q ≫ b)) ≫ p = p
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hap, hbp, Category.comp_id,
        MonObj.comp_one, mul_one]
    · change ((p ≫ a) * (q ≫ b)) ≫ q = q
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, haq, hbq, Category.comp_id,
        MonObj.comp_one, one_mul]
  change ((p ≫ a) * (q ≫ b)) ≫ χ.hom.hom = χ.hom.hom
  rw [h, Category.id_comp]

private theorem character_comp_mul {G H : GroupScheme k} (f : G ⟶ H)
    (a b : Character H) : f ≫ (a * b) = (f ≫ a) * (f ≫ b) :=
  Grp.hom_ext _ _ (MonObj.comp_mul _ _ _)

private theorem character_comp_one {G H : GroupScheme k} (f : G ⟶ H) :
    f ≫ (1 : Character H) = 1 :=
  comp_zero

private def productCharacterEquiv (G H : GroupScheme k) :
    (Additive (Character G) × Additive (Character H)) ≃ₗ[ℤ] Additive (Character (G ⊗ H)) := by
  let e : (Character G × Character H) ≃* Character (G ⊗ H) :=
    { toFun := fun c => (fst G H ≫ c.1) * (snd G H ≫ c.2)
      invFun := fun χ => (firstInclusion G H ≫ χ, secondInclusion G H ≫ χ)
      left_inv := by
        intro p
        apply Prod.ext
        · simp only [character_comp_mul, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
            zero_comp]
          change p.1 * 1 = p.1
          exact mul_one _
        · simp only [character_comp_mul, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
            zero_comp]
          change 1 * p.2 = p.2
          exact one_mul _
      right_inv := restrict_product_character
      map_mul' := by intro a b; simp only [Prod.fst_mul, Prod.snd_mul, character_comp_mul]; ac_rfl }
  exact AddEquiv.toIntLinearEquiv
    ({ toEquiv := e.toEquiv, map_add' := e.map_mul } :
      (Additive (Character G) × Additive (Character H)) ≃+ Additive (Character (G ⊗ H)))

private theorem pointPost_comp {G H J : GroupScheme k} (f : G ⟶ H) (g : H ⟶ J)
    (R : TestAlgebra k) (t : GroupPoints G R) :
    pointPost g R (pointPost f R t) = pointPost (f ≫ g) R t :=
  Category.assoc t f.hom.hom g.hom.hom

private theorem pointPost_zero {G H : GroupScheme k} (R : TestAlgebra k)
    (t : GroupPoints G R) : pointPost (0 : G ⟶ H) R t = 1 :=
  MonObj.comp_one t

private theorem project_first_torus (P Q : SplitBorelPair k) (R : TestAlgebra k)
    (t : GroupPoints (P.T.group ⊗ Q.T.group) R) :
    pointPost (fst P.G.val Q.G.val) R (pointPost (productTorus P Q).inclusion R t) =
      pointPost P.T.inclusion R (pointPost (fst P.T.group Q.T.group) R t) := by
  exact (pointPost_comp _ _ R t).trans
    ((congrArg (fun f => pointPost f R t) (tensorHom_fst P.T.inclusion Q.T.inclusion)).trans
      (pointPost_comp _ _ R t).symm)

private theorem project_second_torus (P Q : SplitBorelPair k) (R : TestAlgebra k)
    (t : GroupPoints (P.T.group ⊗ Q.T.group) R) :
    pointPost (snd P.G.val Q.G.val) R (pointPost (productTorus P Q).inclusion R t) =
      pointPost Q.T.inclusion R (pointPost (snd P.T.group Q.T.group) R t) := by
  exact (pointPost_comp _ _ R t).trans
    ((congrArg (fun f => pointPost f R t) (tensorHom_snd P.T.inclusion Q.T.inclusion)).trans
      (pointPost_comp _ _ R t).symm)

private theorem first_tangent (P Q : SplitBorelPair k) (χ : Character (P.T.group ⊗ Q.T.group))
    (v : Lie k (P.G.val ⊗ Q.G.val)) (hv : v ∈ adjointWeightVectors (productTorus P Q) χ) :
    mapPointKernel (fst P.G.val Q.G.val) v ∈
      adjointWeightVectors P.T (firstInclusion P.T.group Q.T.group ≫ χ) := by
  intro R t
  let b := firstInclusion P.T.group Q.T.group
  let w := pointPost b R t
  have he : tangentEquation R (pointPost (productTorus P Q).inclusion R w) v
      (characterValue χ R w) := hv R w
  have hp := ((product_tangentEquation _ _ _ _ _ _).mp he).1
  rw [project_first_torus] at hp
  simp only [w, b, pointPost_comp, lift_fst, Category.id_comp] at hp
  change tangentEquation R (pointPost P.T.inclusion R t) _ _
  rw [characterValue_pullback b]
  exact hp

private theorem second_tangent (P Q : SplitBorelPair k) (χ : Character (P.T.group ⊗ Q.T.group))
    (v : Lie k (P.G.val ⊗ Q.G.val)) (hv : v ∈ adjointWeightVectors (productTorus P Q) χ) :
    mapPointKernel (snd P.G.val Q.G.val) v ∈
      adjointWeightVectors Q.T (secondInclusion P.T.group Q.T.group ≫ χ) := by
  intro R t
  let b := secondInclusion P.T.group Q.T.group
  let w := pointPost b R t
  have he : tangentEquation R (pointPost (productTorus P Q).inclusion R w) v
      (characterValue χ R w) := hv R w
  have hp := ((product_tangentEquation _ _ _ _ _ _).mp he).2
  rw [project_second_torus] at hp
  simp only [w, b, pointPost_comp, lift_snd, Category.id_comp] at hp
  change tangentEquation R (pointPost Q.T.inclusion R t) _ _
  rw [characterValue_pullback b]
  exact hp

private theorem second_character_eq_one (P Q : SplitBorelPair k)
    (χ : Character (P.T.group ⊗ Q.T.group)) (v : Lie k (P.G.val ⊗ Q.G.val))
    (hv : v ∈ adjointWeightVectors (productTorus P Q) χ)
    (h : mapPointKernel (fst P.G.val Q.G.val) v ≠ 0) :
    secondInclusion P.T.group Q.T.group ≫ χ = 1 := by
  apply RootData.CharacterPairing.characterValuesDetectCharacters Q.split
  intro R t
  let b := secondInclusion P.T.group Q.T.group
  let w := pointPost b R t
  have he : tangentEquation R (pointPost (productTorus P Q).inclusion R w) v
      (characterValue χ R w) := hv R w
  have hp := ((product_tangentEquation _ _ _ _ _ _).mp he).1
  rw [project_first_torus] at hp
  simp only [w, b, pointPost_comp, lift_fst, pointPost_zero, map_one] at hp
  rw [characterValue_pullback b, characterValue_one]
  exact scaledBaseTangent_injective P.G _ h R (tangentEquation_one_point _ _ hp)

private theorem first_character_eq_one (P Q : SplitBorelPair k)
    (χ : Character (P.T.group ⊗ Q.T.group)) (v : Lie k (P.G.val ⊗ Q.G.val))
    (hv : v ∈ adjointWeightVectors (productTorus P Q) χ)
    (h : mapPointKernel (snd P.G.val Q.G.val) v ≠ 0) :
    firstInclusion P.T.group Q.T.group ≫ χ = 1 := by
  apply RootData.CharacterPairing.characterValuesDetectCharacters P.split
  intro R t
  let b := firstInclusion P.T.group Q.T.group
  let w := pointPost b R t
  have he : tangentEquation R (pointPost (productTorus P Q).inclusion R w) v
      (characterValue χ R w) := hv R w
  have hp := ((product_tangentEquation _ _ _ _ _ _).mp he).2
  rw [project_second_torus] at hp
  simp only [w, b, pointPost_comp, lift_snd, pointPost_zero, map_one] at hp
  rw [characterValue_pullback b, characterValue_one]
  exact scaledBaseTangent_injective Q.G _ h R (tangentEquation_one_point _ _ hp)

private theorem mapPointKernel_zero_hom {G H : GroupScheme k} (v : Lie k G) :
    mapPointKernel (0 : G ⟶ H) v = 0 :=
  Subtype.ext (MonObj.comp_one v.toMul.val)

private theorem left_root_of_product (P Q : SplitBorelPair k) (a : Root P.T) :
    fst P.T.group Q.T.group ≫ a.val ∈ absoluteRoots (productTorus P Q) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply a.property.1
    have e := congrArg (firstInclusion P.T.group Q.T.group ≫ ·) h
    simpa only [lift_fst_assoc, Category.id_comp, character_comp_one] using e
  · obtain ⟨v, hv, hn⟩ := a.property.2
    let z := mapPointKernel (firstInclusion P.G.val Q.G.val) v
    have h₁ : mapPointKernel (fst P.G.val Q.G.val) z = v := by
      change mapPointKernel (fst P.G.val Q.G.val)
        (mapPointKernel (firstInclusion P.G.val Q.G.val) v) = v
      rw [← (lieFunctoriality k).2.2 _ _ _, lift_fst]
      exact (lieFunctoriality k).2.1 _ v
    have h₂ : mapPointKernel (snd P.G.val Q.G.val) z = 0 := by
      change mapPointKernel (snd P.G.val Q.G.val)
        (mapPointKernel (firstInclusion P.G.val Q.G.val) v) = 0
      rw [← (lieFunctoriality k).2.2 _ _ _, lift_snd]
      exact mapPointKernel_zero_hom v
    have hz : z ≠ 0 := by
      intro he
      apply hn
      rw [he, map_zero] at h₁
      exact h₁.symm
    refine ⟨z, ?_, hz⟩
    intro R t
    change tangentEquation R (pointPost (productTorus P Q).inclusion R t) z
      (characterValue (fst P.T.group Q.T.group ≫ a.val) R t)
    apply (product_tangentEquation _ _ _ _ _ _).mpr
    let r := characterValue (fst P.T.group Q.T.group ≫ a.val) R t
    have hc : r = characterValue a.val R (pointPost (fst P.T.group Q.T.group) R t) :=
      characterValue_pullback (fst P.T.group Q.T.group) a.val R t
    constructor
    · exact (tangentEquation_congr (G := P.G.val) R
        (project_first_torus P Q R t) h₁ hc).mpr
        (hv R (pointPost (fst P.T.group Q.T.group) R t))
    · exact (congrArg (fun v => tangentEquation (G := Q.G.val) R
        (pointPost (snd P.G.val Q.G.val) R (pointPost (productTorus P Q).inclusion R t)) v r)
        h₂).mpr (tangentEquation_zero _ _ _)

private theorem right_root_of_product (P Q : SplitBorelPair k) (a : Root Q.T) :
    snd P.T.group Q.T.group ≫ a.val ∈ absoluteRoots (productTorus P Q) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply a.property.1
    have e := congrArg (secondInclusion P.T.group Q.T.group ≫ ·) h
    simpa only [lift_snd_assoc, Category.id_comp, character_comp_one] using e
  · obtain ⟨v, hv, hn⟩ := a.property.2
    let z := mapPointKernel (secondInclusion P.G.val Q.G.val) v
    have h₁ : mapPointKernel (fst P.G.val Q.G.val) z = 0 := by
      change mapPointKernel (fst P.G.val Q.G.val)
        (mapPointKernel (secondInclusion P.G.val Q.G.val) v) = 0
      rw [← (lieFunctoriality k).2.2 _ _ _, lift_fst]
      exact mapPointKernel_zero_hom v
    have h₂ : mapPointKernel (snd P.G.val Q.G.val) z = v := by
      change mapPointKernel (snd P.G.val Q.G.val)
        (mapPointKernel (secondInclusion P.G.val Q.G.val) v) = v
      rw [← (lieFunctoriality k).2.2 _ _ _, lift_snd]
      exact (lieFunctoriality k).2.1 _ v
    have hz : z ≠ 0 := by
      intro he
      apply hn
      rw [he, map_zero] at h₂
      exact h₂.symm
    refine ⟨z, ?_, hz⟩
    intro R t
    change tangentEquation R (pointPost (productTorus P Q).inclusion R t) z
      (characterValue (snd P.T.group Q.T.group ≫ a.val) R t)
    apply (product_tangentEquation _ _ _ _ _ _).mpr
    let r := characterValue (snd P.T.group Q.T.group ≫ a.val) R t
    have hc : r = characterValue a.val R (pointPost (snd P.T.group Q.T.group) R t) :=
      characterValue_pullback (snd P.T.group Q.T.group) a.val R t
    constructor
    · exact (congrArg (fun v => tangentEquation (G := P.G.val) R
        (pointPost (fst P.G.val Q.G.val) R (pointPost (productTorus P Q).inclusion R t)) v r)
        h₁).mpr (tangentEquation_zero _ _ _)
    · exact (tangentEquation_congr (G := Q.G.val) R
        (project_second_torus P Q R t) h₂ hc).mpr
        (hv R (pointPost (snd P.T.group Q.T.group) R t))

private theorem root_product_cases (P Q : SplitBorelPair k) (a : Root (productTorus P Q)) :
    (∃ l : Root P.T, a.val = fst P.T.group Q.T.group ≫ l.val) ∨
    (∃ r : Root Q.T, a.val = snd P.T.group Q.T.group ≫ r.val) := by
  classical
  let χ := a.val
  obtain ⟨v, hv, hn⟩ := a.property.2
  let f := fst P.G.val Q.G.val
  let g := snd P.G.val Q.G.val
  by_cases h : mapPointKernel f v = 0
  · have hg : mapPointKernel g v ≠ 0 := by
      intro h'
      apply hn
      apply Subtype.ext
      apply CartesianMonoidalCategory.hom_ext
      · have he := congrArg (fun u : Lie k P.G.val => u.toMul.val) h
        change v.toMul.val ≫ fst P.G.val.X Q.G.val.X = 1 at he
        change _ = (1 : GroupPoints (P.G.val ⊗ Q.G.val) _) ≫ _
        rwa [MonObj.one_comp]
      · have he := congrArg (fun u : Lie k Q.G.val => u.toMul.val) h'
        change v.toMul.val ≫ snd P.G.val.X Q.G.val.X = 1 at he
        change _ = (1 : GroupPoints (P.G.val ⊗ Q.G.val) _) ≫ _
        rwa [MonObj.one_comp]
    let r := secondInclusion P.T.group Q.T.group ≫ χ
    have hl := first_character_eq_one P Q χ v hv hg
    have he : χ = snd P.T.group Q.T.group ≫ r := by
      have e := restrict_product_character χ
      rw [hl, character_comp_one, one_mul] at e
      exact e.symm
    have hr : r ≠ 1 := fun t => a.property.1 (he.trans (by rw [t, character_comp_one]))
    exact Or.inr ⟨⟨r, hr, mapPointKernel g v, second_tangent P Q χ v hv, hg⟩, he⟩
  · let l := firstInclusion P.T.group Q.T.group ≫ χ
    have hr := second_character_eq_one P Q χ v hv h
    have he : χ = fst P.T.group Q.T.group ≫ l := by
      have e := restrict_product_character χ
      rw [hr, character_comp_one, mul_one] at e
      exact e.symm
    have hl : l ≠ 1 := fun t => a.property.1 (he.trans (by rw [t, character_comp_one]))
    exact Or.inl ⟨⟨l, hl, mapPointKernel f v, first_tangent P Q χ v hv, h⟩, he⟩

private def productRootEquiv (P Q : SplitBorelPair k) :
    (Root P.T ⊕ Root Q.T) ≃ Root (productTorus P Q) :=
  Equiv.ofBijective
    (Sum.elim (fun a => ⟨fst P.T.group Q.T.group ≫ a.val, left_root_of_product P Q a⟩)
      (fun a => ⟨snd P.T.group Q.T.group ≫ a.val, right_root_of_product P Q a⟩)) (by
    constructor
    · intro a b h
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          apply congrArg Sum.inl
          apply Subtype.ext
          have e := congrArg (fun z : Root (productTorus P Q) =>
            firstInclusion P.T.group Q.T.group ≫ z.val) h
          simpa only [Sum.elim_inl, lift_fst_assoc, Category.id_comp] using e
        | inr b =>
          exfalso
          apply a.property.1
          change a.val = (0 : Character P.T.group)
          have e := congrArg (fun z : Root (productTorus P Q) =>
            firstInclusion P.T.group Q.T.group ≫ z.val) h
          simpa only [Sum.elim_inl, Sum.elim_inr, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
            zero_comp] using e
      | inr a =>
        cases b with
        | inl b =>
          exfalso
          apply b.property.1
          change b.val = (0 : Character P.T.group)
          have e := congrArg (fun z : Root (productTorus P Q) =>
            firstInclusion P.T.group Q.T.group ≫ z.val) h
          simpa only [Sum.elim_inl, Sum.elim_inr, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
            zero_comp] using e.symm
        | inr b =>
          apply congrArg Sum.inr
          apply Subtype.ext
          have e := congrArg (fun z : Root (productTorus P Q) =>
            secondInclusion P.T.group Q.T.group ≫ z.val) h
          simpa only [Sum.elim_inr, lift_snd_assoc, Category.id_comp] using e
    · intro a
      rcases root_product_cases P Q a with ⟨l, hl⟩ | ⟨r, hr⟩
      · exact ⟨Sum.inl l, Subtype.ext hl.symm⟩
      · exact ⟨Sum.inr r, Subtype.ext hr.symm⟩)

private theorem productCharacterEquiv_root_left (P Q : SplitBorelPair k) (a : Root P.T) :
    productCharacterEquiv P.T.group Q.T.group (Additive.ofMul a.val, 0) =
      Additive.ofMul ((productRootEquiv P Q) (Sum.inl a)).val := by
  change Additive.ofMul ((fst P.T.group Q.T.group ≫ a.val) *
    (snd P.T.group Q.T.group ≫ 1)) = Additive.ofMul (fst P.T.group Q.T.group ≫ a.val)
  rw [character_comp_one, mul_one]

private theorem productCharacterEquiv_root_right (P Q : SplitBorelPair k) (a : Root Q.T) :
    productCharacterEquiv P.T.group Q.T.group (0, Additive.ofMul a.val) =
      Additive.ofMul ((productRootEquiv P Q) (Sum.inr a)).val := by
  change Additive.ofMul ((fst P.T.group Q.T.group ≫ 1) *
    (snd P.T.group Q.T.group ≫ a.val)) = Additive.ofMul (snd P.T.group Q.T.group ≫ a.val)
  rw [character_comp_one, one_mul]
open Specs.PinnedEquivalence (ReducedRootDatum)
open private of_fullCorootLattice corootFullRank
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

private theorem nontrivial_of_root (P : SplitBorelPair k) (a : Root P.T) :
    ¬ IsZero P.G.val := by
  intro h
  letI := P.T.isClosedImmersion
  letI : Mono P.T.inclusion :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).mono_of_mono_map
      (show Mono P.T.inclusion.hom.hom.left from inferInstance)
  have ht := IsZero.of_mono_eq_zero P.T.inclusion (h.eq_zero_of_tgt _)
  exact a.property.1 (ht.eq_of_src a.val 1)

private theorem realize_semisimple_datum (D : ReducedRootDatum.{u})
    (h : Submodule.span ℤ (range D.datum.coroot) = ⊤) (hI : Nonempty D.I) :
    ∃ (P : SplitBorelPair k) (E : Pinning.AttachedDatum P),
      Nonempty (D.datum.Equiv E.toBased.datum) ∧ IsSemisimple P.G ∧ ¬ IsZero P.G.val := by
  obtain ⟨P, E, ⟨e⟩⟩ :=
    ((Classification.PinnedEquivalence.pinnedEquivalence.2 k).2.2) D
  letI := E.comm
  letI := D.finiteRoots
  have hs : corootLattice E = ⊤ := coroot_span_of_equiv _ _ e h
  exact ⟨P, E, ⟨e⟩, of_fullCorootLattice P E hs,
    nontrivial_of_root P (e.indexEquiv (Classical.choice hI))⟩

private def blockReducedDatum {I X Y L : Type u}
    [Finite I] [AddCommGroup X] [AddCommGroup Y] [Fintype L] [DecidableEq L]
    (P : RootDatum I X Y) [P.IsReduced]
    (x : X ≃ₗ[ℤ] (L → ℤ)) (y : Y ≃ₗ[ℤ] (L → ℤ))
    (S : Set L) [DecidablePred (· ∈ S)]
    (hpair : ∀ a b, P.toLinearMap a b = ∑ j, y b j * x a j) :
    ReducedRootDatum.{u} where
  I := blockIndex P x y S
  X := S → ℤ
  Y := S → ℤ
  finiteRoots := inferInstance
  freeX := .of_basis (Pi.basisFun ℤ S)
  freeY := .of_basis (Pi.basisFun ℤ S)
  finiteX := .of_basis (Pi.basisFun ℤ S)
  finiteY := .of_basis (Pi.basisFun ℤ S)
  datum := blockDatum P x y S hpair
  reduced := blockDatum_reduced P x y S hpair

private def blockIndexEquiv {I X Y L : Type u} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) (x : X ≃ₗ[ℤ] (L → ℤ)) (y : Y ≃ₗ[ℤ] (L → ℤ))
    (S : Set L)
    (h : ∀ i, SupportedOn S (x (P.root i), y (P.coroot i)) ∨
      SupportedOn Sᶜ (x (P.root i), y (P.coroot i))) :
    (blockIndex P x y S ⊕ blockIndex P x y Sᶜ) ≃ I := by
  classical
  have disjointBlock (i : I) (hl : SupportedOn S (x (P.root i), y (P.coroot i)))
      (hr : SupportedOn Sᶜ (x (P.root i), y (P.coroot i))) : False := by
    apply P.ne_zero i
    apply x.injective
    rw [map_zero]
    funext j
    by_cases hj : j ∈ S
    · exact (hr j (fun h => h hj)).1
    · exact (hl j hj).1
  refine Equiv.ofBijective (Sum.elim Subtype.val Subtype.val) ⟨?_, ?_⟩
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (Subtype.ext hab)
    · change a.val = b.val at hab
      exact (disjointBlock a.val a.property (by rw [hab]; exact b.property)).elim
    · change a.val = b.val at hab
      exact (disjointBlock a.val (by rw [hab]; exact b.property) a.property).elim
    · exact congrArg Sum.inr (Subtype.ext hab)
  · intro i
    rcases h i with hi | hi
    · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
    · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩

private def tensorProductIso (G H : GroupScheme k) : G ⊗ H ≅ Limits.prod G H :=
  (tensorProductIsBinaryProduct G H).conePointUniqueUpToIso (limit.isLimit _)

theorem geometricProductOfBlocks : GeometricProductOfBlocks.{u} := by
  classical
  intro k _ _ P D hY S ⟨i, hi⟩ ⟨j, hj⟩ hcross
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.finiteCocharacters
  letI := D.datum.reduced
  let C := D.datum.rootDatum
  let A := integralCartan C D.base
  let L := D.base.support
  let s : L → Root P.T := Subtype.val
  obtain ⟨c, x, hc, hpair, hx, hroots⟩ :=
    cartanCoordinates C D.base hY A (Equiv.refl _) (fun _ _ => rfl)
  let y := c.equivFun
  have hcoroot (b : L) : y (C.coroot (s b)) = Pi.single b 1 := by
    have he : c b = C.coroot (s b) := hc b
    rw [← he]
    funext a
    simp [y, Basis.equivFun_self, Pi.single_apply, eq_comm]
  have hs (b : L) (hb : b ∈ S) :
      SupportedOn S (x (C.root (s b)), y (C.coroot (s b))) := by
    intro a ha
    have hn : a ≠ b := fun e => ha (e ▸ hb)
    have he : x (C.root (s b)) = simpleCharacter A b := hx b
    rw [he, hcoroot]
    exact ⟨(hcross b hb a ha).2, by simp [Pi.single_apply, hn, hn.symm]⟩
  have ht (b : L) (hb : b ∈ Sᶜ) :
      SupportedOn Sᶜ (x (C.root (s b)), y (C.coroot (s b))) := by
    intro a ha
    have ha' : a ∈ S := by simpa using ha
    have hn : a ≠ b := fun e => hb (e ▸ ha')
    have he : x (C.root (s b)) = simpleCharacter A b := hx b
    rw [he, hcoroot]
    exact ⟨(hcross a ha' b hb).1, by simp [Pi.single_apply, hn, hn.symm]⟩
  have hb (a : Root P.T) : SupportedOn S (x (C.root a), y (C.coroot a)) ∨
      SupportedOn Sᶜ (x (C.root a), y (C.coroot a)) := by
    apply (cartanRootBlocks A S hcross).1
    change (x (C.root a), y (C.coroot a)) ∈ {p | CartanRoots A p}
    rw [← hroots]
    exact mem_range_self a
  let F := blockReducedDatum C x y S hpair
  let E := blockReducedDatum C x y Sᶜ hpair
  have hF : Submodule.span ℤ (range F.datum.coroot) = ⊤ :=
    blockDatum_coroot_span C x y S hpair s hcoroot hs
  have hE : Submodule.span ℤ (range E.datum.coroot) = ⊤ :=
    blockDatum_coroot_span C x y Sᶜ hpair s hcoroot ht
  obtain ⟨P₁, D₁, ⟨e₁⟩, hs₁, hn₁⟩ :=
    realize_semisimple_datum (k := k) F hF ⟨⟨s i, hs i hi⟩⟩
  obtain ⟨P₂, D₂, ⟨e₂⟩, hs₂, hn₂⟩ :=
    realize_semisimple_datum (k := k) E hE ⟨⟨s j, ht j hj⟩⟩
  letI : IsCommMonObj P₁.T.group.X := D₁.comm
  letI : IsCommMonObj P₂.T.group.X := D₂.comm
  let T := productTorus P₁ P₂
  let R := affineProduct P₁.G P₂.G
  let P' := splitBorelPair R (productReductive P₁.G P₂.G P₁.reductive P₂.reductive)
    T (splitProductTorus P₁ P₂) (productTorus_geometricallyMaximal P₁ P₂)
  let D' := Classification.Pinning.attachedDatum P'
  letI := D'.comm
  let f := x.trans ((splitLattice S).trans ((e₁.weightEquiv.prodCongr e₂.weightEquiv).trans
    (productCharacterEquiv P₁.T.group P₂.T.group)))
  let a := blockIndexEquiv C x y S hb
  let b := (Equiv.sumCongr e₁.indexEquiv e₂.indexEquiv).trans (productRootEquiv P₁ P₂)
  let e := a.symm.trans b
  have hf (l : Root P.T) : f (C.root l) = D'.datum.rootDatum.root (e l) := by
    rw [D'.datum.root_eq]
    obtain ⟨r, rfl⟩ := a.surjective l
    have ea : e (a r) = b r := congrArg b (a.symm_apply_apply r)
    rw [ea]
    cases r with
    | inl p =>
      have hcoord : x (C.root (a (Sum.inl p))) = x (C.root p.val) := rfl
      have hsplit := restrict_zero_outside (fun t ht => (p.property t ht).1)
      have hroot := e₁.toHom.root_weightMap_apply F.datum D₁.toBased.datum p
      change e₁.weightEquiv (fun (t : S) => x (C.root p.val) t.val) =
        D₁.datum.rootDatum.root (e₁.indexEquiv p) at hroot
      rw [D₁.datum.root_eq] at hroot
      change productCharacterEquiv P₁.T.group P₂.T.group
        ((e₁.weightEquiv.prodCongr e₂.weightEquiv)
          (splitLattice S (x (C.root (a (Sum.inl p)))))) = _
      rw [hcoord, hsplit]
      simp only [LinearEquiv.prodCongr_apply, map_zero, hroot]
      exact productCharacterEquiv_root_left P₁ P₂ (e₁.indexEquiv p)
    | inr q =>
      have hcoord : x (C.root (a (Sum.inr q))) = x (C.root q.val) := rfl
      have hsplit := restrict_zero_inside (fun t ht => (q.property t (fun h => h ht)).1)
      have hroot := e₂.toHom.root_weightMap_apply E.datum D₂.toBased.datum q
      change e₂.weightEquiv (fun (t : ↥(Sᶜ)) => x (C.root q.val) t.val) =
        D₂.datum.rootDatum.root (e₂.indexEquiv q) at hroot
      rw [D₂.datum.root_eq] at hroot
      change productCharacterEquiv P₁.T.group P₂.T.group
        ((e₁.weightEquiv.prodCongr e₂.weightEquiv)
          (splitLattice S (x (C.root (a (Sum.inr q)))))) = _
      rw [hcoord, hsplit]
      simp only [LinearEquiv.prodCongr_apply, map_zero, hroot]
      exact productCharacterEquiv_root_right P₁ P₂ (e₂.indexEquiv q)
  have hfin : Finite (Additive (Character P.T.group) ⧸ Submodule.span ℤ (range C.root)) := by
    apply (Submodule.finiteQuotient_iff _).mpr
    exact (corootFullRank C D.base).mp (by
      change finrank ℤ (corootLattice D) = _
      rw [hY, finrank_top])
  let equiv : C.Equiv D'.datum.rootDatum := rootEquivOfRootMap C D'.datum.rootDatum hfin e f hf
  obtain ⟨g⟩ := ((Classification.PinnedEquivalence.pinnedEquivalence.2 k).2.1 P P' D D').mpr
    ⟨equiv⟩
  exact ⟨P₁.G, P₂.G, hs₁, hs₂, hn₁, hn₂, ⟨g ≪≫ tensorProductIso _ _⟩⟩

theorem geometricDiagramConnected : GeometricDiagramConnected.{u} := by
  intro k _ G hG P hP D hY
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.finiteCocharacters
  letI := D.datum.reduced
  have hne : Nonempty D.base.support :=
    nonemptySimpleRoots P D hY (hP ▸ hG.2.1)
  by_contra hc
  obtain ⟨S, hs, ht, hcross⟩ := disconnectedPartition D.datum.rootDatum D.base hne hc
  obtain ⟨H, J, hsH, hsJ, hnH, hnJ, ⟨e⟩⟩ := geometricProductOfBlocks P D hY S hs ht hcross
  exact (noGeometricProduct G hG H J hsH hsJ hnH hnJ).false (hP ▸ e)

theorem classificationOfGeometricPair : ClassificationOfGeometricPair.{u} := by
  intro k _ G hG hsc P hP A
  obtain ⟨U, pin, D, ⟨W⟩⟩ := splitPinnedComparison A P
  have hY := geometric_coroot_lattice G hG.1 hsc P hP D
  exact ⟨U, pin, D, classifyDatum D W hY (geometricDiagramConnected G hG P hP D hY)⟩

theorem absoluteClassification : AbsoluteClassification.{u} := by
  intro k _ G hG hsc A
  obtain ⟨P, hP, U, pin, D, ⟨W⟩, hY⟩ := geometricPinnedDatum G hG.1 hsc A
  exact ⟨P, hP, U, pin, D, classifyDatum D W hY (geometricDiagramConnected G hG P hP D hY)⟩

end GeometricProducts

end LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
