import MathGenome.Internal.Specs.D07.Ch19.SturmTheoremLocalSignVariation
import MathGenome.Internal.D07.Ch19.SturmChain
import MathGenome.Internal.D07.Ch11.RootBound
import MathGenome.Internal.D07.Ch11.FactorRemainder
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.IntermediateValue
import Aesop

noncomputable section
namespace D07.Ch19.SturmTheoremLocalSignVariation
open Polynomial Filter SignType
open Specs.D07.Ch19.SturmTheoremLocalSignVariation
open Specs.D07.Ch19.SturmChain (DivisionLaws)
open scoped Topology

/-- Continuity keeps a nonzero polynomial value's sign fixed locally. -/
theorem eventually_sign_eval_eq (p : Poly) {c : ℝ} (hp : p.eval c ≠ 0) :
    ∀ᶠ x in 𝓝 c, sign (p.eval x) = sign (p.eval c) := by
  have h : ContinuousAt (fun x : ℝ => sign (p.eval x)) c :=
    (continuousAt_sign_of_ne_zero hp).comp (f := fun x : ℝ => p.eval x) p.continuousAt
  exact (h.eventually (mem_nhds_discrete.mpr rfl)).mono (fun _ hx => hx.symm)

/-- A triple with opposite nonzero endpoints has exactly one change across its
first two edges, for any middle value, including zero. -/
theorem variations_opposite_endpoints (a b d : ℝ) (tail : List ℝ)
    (ha : a ≠ 0) (hd : d ≠ 0) (hop : sign a = -sign d) :
    (a :: b :: d :: tail).signVariations = (d :: tail).signVariations + 1 := by
  have hne : sign a ≠ sign d := by
    have hs : sign d ≠ 0 := sign_ne_zero.mpr hd
    cases h : sign d <;> simp_all
  by_cases hb : b = 0
  · subst b
    simp only [List.signVariations_cons_zero_cons,
      List.signVariations_cons_cons_of_ne_zero tail ha hd, ite_eq_right hne]
  · rw [List.signVariations_cons_cons_of_ne_zero (d :: tail) ha hb,
      List.signVariations_cons_cons_of_ne_zero tail hb hd]
    have hs : sign b ≠ 0 := sign_ne_zero.mpr hb
    have ht : sign d ≠ 0 := sign_ne_zero.mpr hd
    cases h₁ : sign b <;> cases h₂ : sign d <;> simp_all

/-- Signed division laws pass to a tail. -/
theorem division_laws_tail (p : Poly) (L : List Poly)
    (h : DivisionLaws (p :: L)) : DivisionLaws L := by
  cases L with
  | nil => trivial
  | cons q tail =>
    cases tail with
    | nil => trivial
    | cons r rest => exact h.2.2

/-- Consequently they pass to every suffix, without an assumption on the prefix. -/
theorem division_laws_suffix (pre L : List Poly)
    (h : DivisionLaws (pre ++ L)) : DivisionLaws L := by
  induction pre with
  | nil => exact h
  | cons p pre ih => exact ih (division_laws_tail p (pre ++ L) h)

/-- The recurrence specializes to opposite neighbors at an internal zero. -/
theorem opposite_at_zero {p q r : Poly} {rest : List Poly} {c : ℝ}
    (h : DivisionLaws (p :: q :: r :: rest)) (hq : q.eval c = 0) :
    p.eval c = -r.eval c := by
  have he := congrArg (fun t : Poly => t.eval c) h.2.1
  simpa only [eval_sub, eval_mul, hq, mul_zero, zero_sub] using he

/-- Local constancy for an arbitrary suffix starting at a nonzero value.
The recursion skips a vanishing middle member together with the two edges
around it. Thus distinct internal zeros are handled in one induction. -/
theorem variation_eventually_eq (L : List Poly) (c : ℝ)
    (hd : DivisionLaws L)
    (hn : L.IsChain (fun p q => ∀ c : ℝ, ¬ (p.eval c = 0 ∧ q.eval c = 0)))
    (hl : ∀ q, L.getLast? = some q → q.eval c ≠ 0)
    (hh : ∀ p tail, L = p :: tail → p.eval c ≠ 0) :
    ∀ᶠ x in 𝓝 c, variation L x = variation L c := by
  induction L using List.twoStepInduction with
  | nil => exact Eventually.of_forall (fun _ => rfl)
  | singleton p => simp [variation]
  | cons_cons p q rest ihrest ih =>
    have hp := hh p (q :: rest) rfl
    have htail := division_laws_tail p (q :: rest) hd
    have hntail : (q :: rest).IsChain
        (fun p q => ∀ c : ℝ, ¬ (p.eval c = 0 ∧ q.eval c = 0)) := hn.tail
    have hltail : ∀ t, (q :: rest).getLast? = some t → t.eval c ≠ 0 := by
      intro t ht
      exact hl t (by simpa only [List.getLast?_cons_cons] using ht)
    by_cases hq : q.eval c = 0
    · cases rest with
      | nil => exact (hltail q rfl hq).elim
      | cons r rest =>
        have hr : r.eval c ≠ 0 := by
          intro hr
          exact (List.isChain_cons_cons.mp hntail).1 c ⟨hq, hr⟩
        have hop := opposite_at_zero hd hq
        have hrec := ihrest (division_laws_tail q (r :: rest) htail) hntail.tail
          (fun t ht => hltail t (by simpa only [List.getLast?_cons_cons] using ht))
          (by intro t tail heq; cases heq; exact hr)
        filter_upwards [eventually_sign_eval_eq p hp, eventually_sign_eval_eq r hr, hrec]
          with x hpx hrx hrec
        have hp' : p.eval x ≠ 0 := sign_ne_zero.mp (hpx ▸ sign_ne_zero.mpr hp)
        have hr' : r.eval x ≠ 0 := sign_ne_zero.mp (hrx ▸ sign_ne_zero.mpr hr)
        have hs : sign (p.eval c) = -sign (r.eval c) := by rw [hop, Left.sign_neg]
        have hsx : sign (p.eval x) = -sign (r.eval x) := by rw [hpx, hrx, hs]
        simp only [variation, List.map_cons] at hrec ⊢
        rw [variations_opposite_endpoints _ _ _ _ hp' hr' hsx,
          variations_opposite_endpoints _ _ _ _ hp hr hs, hrec]
    · have hrec := ih q htail hntail hltail
        (by intro t tail heq; cases heq; exact hq)
      filter_upwards [eventually_sign_eval_eq p hp, eventually_sign_eval_eq q hq, hrec]
        with x hpx hqx hrec
      have hp' : p.eval x ≠ 0 := sign_ne_zero.mp (hpx ▸ sign_ne_zero.mpr hp)
      have hq' : q.eval x ≠ 0 := sign_ne_zero.mp (hqx ▸ sign_ne_zero.mpr hq)
      simp only [variation, List.map_cons] at hrec ⊢
      rw [List.signVariations_cons_cons_of_ne_zero _ hp' hq',
        List.signVariations_cons_cons_of_ne_zero _ hp hq, hpx, hqx, hrec]

theorem canonical_chain : CanonicalChain := by
  intro s hdeg hsq hgcd
  obtain ⟨hshape, hnonzero, hdiv, _, _, hlast, hchain⟩ :=
    SturmChain.chain_of_coprime_derivative s hdeg hgcd
  exact ⟨hdeg, hsq, hshape, hnonzero, hdiv, hlast, hchain⟩

theorem finite_chain_zeros : FiniteChainZeros := by
  intro s L hL
  have hnonzero := hL.2.2.2.1
  clear hL
  induction L with
  | nil => simp [chainZeros]
  | cons p L ih =>
    have htail : ∀ q ∈ L, q ≠ 0 := fun q hq => hnonzero q (List.mem_cons_of_mem p hq)
    have hzeros : chainZeros (p :: L) = {x : ℝ | p.eval x = 0} ∪ chainZeros L := by
      ext x
      simp only [chainZeros, List.mem_cons, Set.mem_ofPred_eq, Set.mem_union]
      aesop
    rw [hzeros]
    exact (Ch11.RootBound.roots_finite ℝ p (hnonzero p List.mem_cons_self)).union
      (ih htail)

theorem signs_locally_constant : SignsLocallyConstant := by
  intro s L _ c hc
  apply (L.finite_toSet.eventually_all).mpr
  intro p hp
  exact eventually_sign_eval_eq p (fun h => hc ⟨p, hp, h⟩)

theorem signs_constant_on_interval : SignsConstantOnInterval := by
  intro s L _ a b h p hp
  have hn : ∀ x ∈ Set.uIcc a b, p.eval x ≠ 0 :=
    fun x hx hz => h x hx ⟨p, hp, hz⟩
  have hs : ContinuousOn (fun x : ℝ => sign (p.eval x)) (Set.uIcc a b) := by
    intro x hx
    exact ((continuousAt_sign_of_ne_zero (hn x hx)).comp
      (f := fun x : ℝ => p.eval x) p.continuousAt).continuousWithinAt
  exact isPreconnected_uIcc.constant hs Set.left_mem_uIcc Set.right_mem_uIcc

theorem tail_local_constancy : TailLocalConstancy := by
  intro s L hL pre p tail c heq hp
  obtain ⟨_, _, _, _, hdiv, ⟨a, ha, hlast⟩, hchain⟩ := hL
  subst L
  apply variation_eventually_eq (p :: tail) c (division_laws_suffix pre _ hdiv)
    hchain.right_of_append
  · intro q hq
    have hlast' : (p :: tail).getLast? = some (C a) := by
      simpa only [List.getLast?_append_cons] using hlast
    have he : q = C a := Option.some.inj (hq.symm.trans hlast')
    simpa only [he, eval_C] using ha
  · intro q rest h
    cases h
    exact hp

theorem nonroot_local_constancy : NonrootLocalConstancy := by
  intro s L hL c hc
  obtain ⟨tail, heq⟩ := hL.2.2.1
  simpa only [heq] using
    tail_local_constancy s L hL [] s (s.derivative :: tail) c heq hc

theorem internal_zero_cancellation : InternalZeroCancellation := by
  intro s L hL pre p q r post c heq hq
  obtain ⟨_, _, _, _, hdiv, _, hchain⟩ := hL
  subst L
  have hd := division_laws_suffix pre (p :: q :: r :: post) hdiv
  have hn := hchain.right_of_append
  have hp : p.eval c ≠ 0 := fun hp =>
    (List.isChain_cons_cons.mp hn).1 c ⟨hp, hq⟩
  have hr : r.eval c ≠ 0 := fun hr =>
    (List.isChain_cons_cons.mp hn.tail).1 c ⟨hq, hr⟩
  have hop := opposite_at_zero hd hq
  refine ⟨hp, hr, hop, ?_⟩
  filter_upwards [eventually_sign_eval_eq p hp, eventually_sign_eval_eq r hr]
    with x hpx hrx
  have hp' : p.eval x ≠ 0 := sign_ne_zero.mp (hpx ▸ sign_ne_zero.mpr hp)
  have hr' : r.eval x ≠ 0 := sign_ne_zero.mp (hrx ▸ sign_ne_zero.mpr hr)
  have hs : sign (p.eval x) = -sign (r.eval x) := by
    rw [hpx, hrx, hop, Left.sign_neg]
  refine ⟨hs, ?_⟩
  simpa only [variation, List.map_cons, List.map_nil, List.signVariations_singleton,
    zero_add] using variations_opposite_endpoints (p.eval x) (q.eval x) (r.eval x) [] hp' hr' hs

/-- Factorization at a root identifies the value of the remaining factor with
the derivative. Its locally fixed sign determines the crossing direction. -/
theorem root_jump : RootJump := by
  intro s L hL c hc
  obtain ⟨tail, heq⟩ := hL.2.2.1
  have hd : s.derivative.eval c ≠ 0 := by
    have hn := hL.2.2.2.2.2.2
    rw [heq, List.isChain_cons_cons] at hn
    exact fun hd => hn.1 c ⟨hc, hd⟩
  have htail := tail_local_constancy s L hL [s] s.derivative tail c heq hd
  obtain ⟨u, hu⟩ := (Ch11.FactorRemainder.factor_iff ℝ s c).mp hc
  have huval : u.eval c = s.derivative.eval c := by
    rw [hu, derivative_mul, derivative_X_sub_C]
    simp
  have hun : u.eval c ≠ 0 := huval ▸ hd
  have hf (x : ℝ) : s.eval x = (x - c) * u.eval x := by
    rw [hu]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
  have hcommon : ∀ᶠ x in 𝓝 c,
      s.derivative.eval x ≠ 0 ∧ sign (u.eval x) = sign (s.derivative.eval x) ∧
      variation (s.derivative :: tail) x = variation (s.derivative :: tail) c := by
    filter_upwards [eventually_sign_eval_eq u hun,
      eventually_sign_eval_eq s.derivative hd, htail] with x hux hdx htx
    refine ⟨sign_ne_zero.mp (hdx ▸ sign_ne_zero.mpr hd), ?_, htx⟩
    rw [hux, hdx, huval]
  have hcvar : variation L c = variation (s.derivative :: tail) c := by
    simp only [heq, variation, List.map_cons, hc, List.signVariations_zero_cons]
  constructor
  · filter_upwards [hcommon.filter_mono nhdsWithin_le_nhds,
      (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[<] c, x < c)] with x hx hxc
    have hs : sign (s.eval x) = -sign (s.derivative.eval x) := by
      rw [hf, sign_mul, sign_neg (sub_neg.mpr hxc), hx.2.1, neg_one_mul]
    have hs0 : s.eval x ≠ 0 := by
      apply sign_ne_zero.mp
      rw [hs]
      exact SignType.neg_eq_zero_iff.not.mpr (sign_ne_zero.mpr hx.1)
    have hne : sign (s.eval x) ≠ sign (s.derivative.eval x) := by
      rw [hs]
      exact SignType.neg_eq_self_iff.not.mpr (sign_ne_zero.mpr hx.1)
    rw [hcvar, heq]
    simp only [variation, List.map_cons]
    rw [List.signVariations_cons_cons_of_ne_zero _ hs0 hx.1, ite_eq_right hne]
    exact congrArg (· + 1) hx.2.2
  · filter_upwards [hcommon.filter_mono nhdsWithin_le_nhds,
      (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] c, c < x)] with x hx hxc
    have hs : sign (s.eval x) = sign (s.derivative.eval x) := by
      rw [hf, sign_mul, sign_pos (sub_pos.mpr hxc), hx.2.1, one_mul]
    have hs0 : s.eval x ≠ 0 := sign_ne_zero.mp (hs ▸ sign_ne_zero.mpr hx.1)
    rw [hcvar, heq]
    simp only [variation, List.map_cons]
    rw [List.signVariations_cons_cons_of_ne_zero _ hs0 hx.1, ite_eq_left hs, add_zero]
    exact hx.2.2

end D07.Ch19.SturmTheoremLocalSignVariation
