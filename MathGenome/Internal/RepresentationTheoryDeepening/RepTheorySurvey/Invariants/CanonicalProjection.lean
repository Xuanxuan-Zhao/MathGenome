import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.CanonicalProjection
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.Actions
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.LinearAlgebra.TensorProduct.Basis

open LinearAlgebraicGroups
open scoped TensorProduct

universe u v w z

namespace RepTheorySurvey.Invariants

noncomputable section

/- The same argument applies to the operators (g-1) for abstract groups and to
the slices of the difference between the coaction and the trivial coaction. -/
namespace Deviations

variable {k V W ι : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

private def Stable (d : ι → Module.End k V) (S : Submodule k V) : Prop :=
  ∀ i, S ≤ S.comap (d i)

private def Simple (d : ι → Module.End k V) (S : Submodule k V) : Prop :=
  Stable d S ∧ S ≠ ⊥ ∧ ∀ T ≤ S, Stable d T → T = ⊥ ∨ T = S

private def Spans (d : ι → Module.End k V) : Prop :=
  ∀ B : Submodule k V, (∀ S, Simple d S → S ≤ B) → B = ⊤

variable {d : ι → Module.End k V} {e : ι → Module.End k W}
  {I : Submodule k V} {J : Submodule k W}

private theorem stable_iSup {α : Sort*} {S : α → Submodule k V}
    (hS : ∀ a, Stable d (S a)) : Stable d (⨆ a, S a) :=
  fun i ↦ iSup_le fun a ↦ (hS a i).trans (Submodule.comap_mono (le_iSup S a))

private theorem stable_inf {S T : Submodule k V} (hS : Stable d S) (hT : Stable d T) :
    Stable d (S ⊓ T) :=
  fun i _ hx ↦ ⟨hS i hx.1, hT i hx.2⟩

private theorem stable_map (f : V →ₗ[k] W) (hf : ∀ i x, f (d i x) = e i (f x))
    {S : Submodule k V} (hS : Stable d S) : Stable e (S.map f) := by
  intro i _ hx
  obtain ⟨x, hxS, rfl⟩ := Submodule.mem_map.mp hx
  exact ⟨d i x, hS i hxS, hf i x⟩

private theorem simple_map (f : V →ₗ[k] W) (hinj : Function.Injective f)
    (hf : ∀ i x, f (d i x) = e i (f x)) {S : Submodule k V} (hS : Simple d S) :
    Simple e (S.map f) := by
  refine ⟨stable_map f hf hS.1, ?_, ?_⟩
  · intro h
    have hh := congrArg (Submodule.comap f) h
    rw [Submodule.comap_map_eq_of_injective hinj, ← LinearMap.ker,
      LinearMap.ker_eq_bot.mpr hinj] at hh
    exact hS.2.1 hh
  · intro T hT hstable
    have hpre : T.comap f ≤ S := by
      simpa only [Submodule.comap_map_eq_of_injective hinj] using Submodule.comap_mono (f := f) hT
    have hpreStable : Stable d (T.comap f) := by
      intro i x hx
      change f (d i x) ∈ T
      rw [hf]
      exact hstable i hx
    have hmap : (T.comap f).map f = T :=
      Submodule.map_comap_eq_self (hT.trans LinearMap.map_le_range)
    rcases hS.2.2 _ hpre hpreStable with h | h
    · left
      rw [← hmap, h, Submodule.map_bot]
    · right
      rw [← hmap, h]

private theorem span_local_piece (B : Submodule k V) (hB : ∀ S, Simple d S → S ≤ B)
    (S : Submodule k V) (e : ι → Module.End k S)
    (hf : ∀ i x, S.subtype (e i x) = d i (S.subtype x))
    {n : ℕ} (T : Fin n → Submodule k S) (hs : ∀ i, Simple e (T i))
    (ht : (⨆ i, T i) = ⊤) : S ≤ B := by
  have hh : (⨆ i, T i) ≤ B.comap S.subtype :=
    iSup_le fun i ↦ Submodule.map_le_iff_le_comap.mp
      (hB _ (simple_map S.subtype S.injective_subtype hf (hs i)))
  intro x hx
  exact hh (ht ▸ Submodule.mem_top (x := (⟨x, hx⟩ : S)))

private def nontrivialSum (d : ι → Module.End k V) (I : Submodule k V) : Submodule k V :=
  ⨆ S : {S : Submodule k V // Simple d S ∧ ¬ S ≤ I}, S.val

private theorem sup_nontrivialSum (hspan : Spans d) : I ⊔ nontrivialSum d I = ⊤ := by
  classical
  apply hspan
  intro S hs
  by_cases h : S ≤ I
  · exact h.trans le_sup_left
  · exact (le_iSup (fun T : {T : Submodule k V // Simple d T ∧ ¬ T ≤ I} ↦ T.val)
      ⟨S, hs, h⟩).trans le_sup_right

private theorem disjoint_nontrivialSum (hI : ∀ x, x ∈ I ↔ ∀ i, d i x = 0) :
    Disjoint I (nontrivialSum d I) := by
  classical
  have hstableI : Stable d I := by
    intro i x hx
    change d i x ∈ I
    rw [(hI x).mp hx i]
    exact I.zero_mem
  let α := {S : Submodule k V // Simple d S ∧ ¬ S ≤ I}
  let S : α → Submodule k V := Subtype.val
  have stable_finset (s : Finset α) : Stable d (s.sup S) := by
    rw [Finset.sup_eq_iSup]
    exact stable_iSup fun a ↦ stable_iSup fun _ ↦ a.property.1.1
  -- A simple summand is either already in the preceding sum or intersects it trivially.
  have hfin (s : Finset α) : Disjoint I (s.sup S) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih =>
      rw [Finset.sup_insert]
      have hs := stable_finset s
      have ha : Simple d (S a) := a.property.1
      rcases ha.2.2 (S a ⊓ s.sup S) inf_le_left (stable_inf ha.1 hs) with h | h
      · have hdis : Disjoint (S a) (s.sup S) := disjoint_iff.mpr h
        apply Submodule.disjoint_def.mpr
        intro x hx hsum
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hsum
        have hyI : y ∈ I := (hI y).mpr fun i ↦ by
          have hz' := hs i hz
          have hzero : d i y + d i z = 0 := by simpa only [map_add] using (hI _).mp hx i
          have hyz : d i y = -(d i z) := eq_neg_of_add_eq_zero_left hzero
          exact Submodule.disjoint_def.mp hdis _ (ha.1 i hy)
            (hyz ▸ (s.sup S).neg_mem hz')
        have hzI : z ∈ I := by
          simpa only [add_sub_cancel_left] using I.sub_mem hx hyI
        have haI : Disjoint (S a) I := by
          rcases ha.2.2 (S a ⊓ I) inf_le_left (stable_inf ha.1 hstableI) with h' | h'
          · exact disjoint_iff.mpr h'
          · exact (a.property.2 (show S a ≤ I from h' ▸ inf_le_right)).elim
        rw [Submodule.disjoint_def.mp haI _ hy hyI, Submodule.disjoint_def.mp ih _ hzI hz, add_zero]
      · rw [sup_eq_right.mpr (h ▸ inf_le_right)]
        exact ih
  apply Submodule.disjoint_def.mpr
  intro x hx hxN
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hxN
  rw [← Finset.sup_eq_iSup] at hs
  exact Submodule.disjoint_def.mp (hfin s) x hx hs

private def ranges (d : ι → Module.End k V) : Submodule k V :=
  ⨆ i, LinearMap.range (d i)

private theorem deviation_mem_ranges (i : ι) (x : V) : d i x ∈ ranges d :=
  le_iSup (fun j ↦ LinearMap.range (d j)) i ⟨x, rfl⟩

-- On a nontrivial simple subspace the images of the deviations span the whole subspace.
private theorem simple_le_ranges (hI : ∀ x, x ∈ I ↔ ∀ i, d i x = 0)
    {S : Submodule k V} (hS : Simple d S) (hnt : ¬ S ≤ I) : S ≤ ranges d := by
  have hr : Stable d (ranges d) := fun i x _ ↦ deviation_mem_ranges i x
  rcases hS.2.2 (S ⊓ ranges d) inf_le_left (stable_inf hS.1 hr) with h | h
  · exact (hnt fun x hx ↦ (hI x).mpr fun i ↦
      (Submodule.mem_bot (R := k)).mp (h ▸ (show d i x ∈ S ⊓ ranges d from
        ⟨hS.1 i hx, deviation_mem_ranges i x⟩))).elim
  · exact h ▸ inf_le_right

private theorem exists_projection (hspan : Spans d) (hI : ∀ x, x ∈ I ↔ ∀ i, d i x = 0) :
    ∃ P : V →ₗ[k] I, (∀ x : I, P (x : V) = x) ∧
      (∀ S, Simple d S → ¬ S ≤ I → ∀ x : S, P (x : V) = 0) ∧
      ∀ i x, P (d i x) = 0 := by
  let N := nontrivialSum d I
  have hsup : I ⊔ N = ⊤ := sup_nontrivialSum hspan
  have hcompl : IsCompl I N := ⟨disjoint_nontrivialSum hI, codisjoint_iff.mpr hsup⟩
  let P := I.projectionOnto N hcompl
  have zeroOnN (x : V) (hx : x ∈ N) : P x = 0 :=
    (Submodule.projectionOnto_apply_eq_zero_iff hcompl).mpr hx
  refine ⟨P, Submodule.projectionOnto_apply_left hcompl, ?_, ?_⟩
  · intro S hs hn x
    apply zeroOnN
    exact le_iSup (fun T : {T : Submodule k V // Simple d T ∧ ¬ T ≤ I} ↦ T.val)
      ⟨S, hs, hn⟩ x.property
  · intro i x
    apply zeroOnN
    have stableN : Stable d N := stable_iSup fun S ↦ S.property.1.1
    have h : I ⊔ N ≤ N.comap (d i) :=
      sup_le (fun y hy ↦ by
        change d i y ∈ N
        rw [(hI y).mp hy i]
        exact N.zero_mem) (stableN i)
    exact h (hsup ▸ Submodule.mem_top)

private theorem projection_unique (hspan : Spans d) {P Q : V →ₗ[k] I}
    (hP : ∀ x : I, P (x : V) = x) (hQ : ∀ x : I, Q (x : V) = x)
    (hnP : ∀ S, Simple d S → ¬ S ≤ I → ∀ x : S, P (x : V) = 0)
    (hnQ : ∀ S, Simple d S → ¬ S ≤ I → ∀ x : S, Q (x : V) = 0) : P = Q := by
  classical
  have h : LinearMap.ker (P - Q) = ⊤ := by
    apply hspan
    intro S hs x hx
    change P x - Q x = 0
    apply sub_eq_zero.mpr
    by_cases he : S ≤ I
    · exact (hP ⟨x, he hx⟩).trans (hQ ⟨x, he hx⟩).symm
    · exact (hnP S hs he ⟨x, hx⟩).trans (hnQ S hs he ⟨x, hx⟩).symm
  apply LinearMap.ext
  intro x
  have hh : x ∈ LinearMap.ker (P - Q) := h ▸ Submodule.mem_top
  exact sub_eq_zero.mp hh

-- Equivariant maps preserve invariants and carry each deviation to a deviation.
private theorem projection_natural (hspan : Spans d)
    (hI : ∀ x, x ∈ I ↔ ∀ i, d i x = 0) (hJ : ∀ x, x ∈ J ↔ ∀ i, e i x = 0)
    {P : V →ₗ[k] I} {Q : W →ₗ[k] J}
    (hP : ∀ x : I, P (x : V) = x) (hQ : ∀ x : J, Q (x : W) = x)
    (hdP : ∀ i x, P (d i x) = 0) (hdQ : ∀ i x, Q (e i x) = 0)
    (f : V →ₗ[k] W) (hf : ∀ i x, f (d i x) = e i (f x)) (x : V) :
    (Q (f x) : W) = f (P x : V) := by
  have htop : I ⊔ ranges d = ⊤ := by
    classical
    apply hspan
    intro S hs
    by_cases he : S ≤ I
    · exact he.trans le_sup_left
    · exact (simple_le_ranges hI hs he).trans le_sup_right
  let D := J.subtype.comp (Q.comp f) - f.comp (I.subtype.comp P)
  suffices hh : I ⊔ ranges d ≤ LinearMap.ker D by
    have hx : x ∈ LinearMap.ker D := hh (htop ▸ Submodule.mem_top)
    exact sub_eq_zero.mp hx
  apply sup_le
  · intro y hy
    have hfy : f y ∈ J := (hJ _).mpr fun i ↦ by rw [← hf, (hI y).mp hy i, map_zero]
    change (Q (f y) : W) - f (P y : V) = 0
    rw [hQ ⟨f y, hfy⟩, hP ⟨y, hy⟩]
    exact sub_self _
  · apply iSup_le
    rintro i _ ⟨y, rfl⟩
    change (Q (f (d i y)) : W) - f (P (d i y) : V) = 0
    rw [hf, hdQ, hdP]
    simp

end Deviations

namespace GroupRepresentation

open Deviations

variable {k : Type u} {G : Type v} {V : Type w} {W : Type z}
  [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private def deviation (ρ : Representation k G V) (g : G) : Module.End k V :=
  ρ g - LinearMap.id

private theorem deviation_apply (ρ : Representation k G V) (g : G) (x : V) :
    deviation ρ g x = ρ g x - x := rfl

private theorem mem_invariants_iff_deviation (ρ : Representation k G V) (x : V) :
    x ∈ ρ.invariants ↔ ∀ g, deviation ρ g x = 0 := by
  simp only [Representation.mem_invariants, deviation_apply, sub_eq_zero]

private theorem stable_iff (ρ : Representation k G V) (S : Submodule k V) :
    Stable (deviation ρ) S ↔ ∀ g x, x ∈ S → ρ g x ∈ S := by
  constructor
  · intro h g x hx
    simpa only [deviation_apply, sub_add_cancel] using S.add_mem (h g hx) hx
  · intro h g x hx
    exact S.sub_mem (h g x hx) hx

private theorem simple_iff_atom (ρ : Representation k G V) (S : Subrepresentation ρ) :
    Simple (deviation ρ) S.toSubmodule ↔ IsAtom S := by
  constructor
  · intro h
    refine ⟨fun he ↦ h.2.1 (congrArg Subrepresentation.toSubmodule he), ?_⟩
    intro T hT
    rcases h.2.2 T.toSubmodule hT.le
      ((stable_iff ρ T.toSubmodule).mpr (fun g _ hx ↦ T.apply_mem_toSubmodule g hx)) with ht | ht
    · exact Subrepresentation.toSubmodule_injective ht
    · exact (hT.ne (Subrepresentation.toSubmodule_injective ht)).elim
  · intro h
    refine ⟨(stable_iff ρ _).mpr (fun g _ hx ↦ S.apply_mem_toSubmodule g hx),
      fun he ↦ h.1 (Subrepresentation.toSubmodule_injective he), ?_⟩
    intro T hT ht
    let U : Subrepresentation ρ := ⟨T, fun g _ hx ↦ (stable_iff ρ T).mp ht g _ hx⟩
    exact ((h.le_iff (x := U)).mp hT).imp
      (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)

private theorem intertwining_iff_deviation {ρ : Representation k G V}
    {σ : Representation k G W} (f : V →ₗ[k] W) :
    ρ.IsIntertwiningMap σ f ↔ ∀ g x, f (deviation ρ g x) = deviation σ g (f x) := by
  simp only [Representation.isIntertwiningMap_iff, deviation_apply, map_sub, sub_left_inj]

private theorem intertwining_trivial_iff_deviation (ρ : Representation k G V) {X : Type w}
    [AddCommGroup X] [Module k X] (P : V →ₗ[k] X) :
    ρ.IsIntertwiningMap (Representation.trivial k G X) P ↔ ∀ g x, P (deviation ρ g x) = 0 := by
  simp only [Representation.isIntertwiningMap_iff, Representation.trivial_apply,
    deviation_apply, map_sub, sub_eq_zero]

private theorem deviations_span (h : LinearlyReductive.{u,v,w} k G) (ρ : Representation k G V)
    (hρ : LocallyFinite ρ) : Spans (deviation ρ) := by
  intro B hB
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨S, hx, hfin⟩ := hρ x
  let : FiniteDimensional k S.toSubmodule := hfin
  obtain ⟨n, T, hs, hsum⟩ := h S.toSubmodule S.toRepresentation
  exact span_local_piece B hB S.toSubmodule (deviation S.toRepresentation)
    (fun g y ↦ by
      rw [deviation_apply, map_sub, deviation_apply]
      rfl)
    (fun i ↦ (T i).toSubmodule)
    (fun i ↦ (simple_iff_atom _ (T i)).mpr (hs i))
    hsum.submodule_iSup_eq_top hx

theorem canonicalProjection : Specs.GroupProjection.{u,v,w} := by
  intro k G V _ _ _ _ h ρ hρ
  have hspan := deviations_span h ρ hρ
  obtain ⟨P, hP, hnP, hdP⟩ := exists_projection hspan (mem_invariants_iff_deviation ρ)
  have zeroOnSimple (Q : V →ₗ[k] ρ.invariants) (hQ : Specs.HasGroupProjectionBehavior ρ Q)
      (S : Submodule k V) (hs : Simple (deviation ρ) S) (hnt : ¬ S ≤ ρ.invariants) (x : S) :
      Q (x : V) = 0 := by
    let T : Subrepresentation ρ :=
      ⟨S, fun g _ hx ↦ (stable_iff ρ S).mp hs.1 g _ hx⟩
    exact hQ.2 T ((simple_iff_atom ρ T).mp hs) hnt x
  refine ⟨P, ⟨(intertwining_trivial_iff_deviation ρ P).mpr hdP, hP, ?_⟩, ?_⟩
  · intro S hs hnt x
    exact hnP _ ((simple_iff_atom ρ S).mpr hs) hnt x
  · intro Q hQ
    exact projection_unique hspan hQ.1 hP (zeroOnSimple Q hQ) hnP

theorem canonicalProjection_natural : Specs.GroupProjectionNatural.{u,v,w,z} := by
  intro k G V W _ _ _ _ _ _ h ρ σ hρ _ P Q hP hQ f hf x
  exact projection_natural (deviations_span h ρ hρ)
    (mem_invariants_iff_deviation ρ) (mem_invariants_iff_deviation σ) hP.2.1 hQ.2.1
    ((intertwining_trivial_iff_deviation ρ P).mp hP.1)
    ((intertwining_trivial_iff_deviation σ Q).mp hQ.1) f
    ((intertwining_iff_deviation f).mp hf) x

theorem canonicalProjection_restriction : Specs.GroupProjectionRestriction.{u,v,w} := by
  intro k G V _ _ _ _ h ρ hρ S _ P Q hP hQ x
  have hS : LocallyFinite S.toRepresentation :=
    fun y ↦ ⟨⊤, Submodule.mem_top (x := y), inferInstance⟩
  exact canonicalProjection_natural h S.toRepresentation ρ hS hρ Q P hQ hP
    S.toSubmodule.subtype ⟨fun _ _ ↦ rfl⟩ x

theorem canonicalProjection_reynolds : Specs.GroupProjectionReynolds.{u,v,w} := by
  intro k G A _ _ _ _ h ρ hρ P hP
  refine ⟨hP.1, ?_, hP.2.1⟩
  intro a x
  let f : A →ₗ[k] A := Algebra.lmul k A (a : A)
  let σ := GroupAlgebraAction.toRepresentation ρ
  have hf : σ.IsIntertwiningMap σ f := by
    constructor
    intro g y
    change (a : A) * ρ g y = ρ g ((a : A) * y)
    rw [map_mul, show ρ g (a : A) = (a : A) from a.property g]
  apply Subtype.ext
  exact canonicalProjection_natural h σ σ hρ hρ P P hP hP f hf x

end GroupRepresentation

namespace RationalRepresentation

open Deviations RationalRepresentations

variable {k V W : Type u} [Field k] {H : HopfAlgebraCategory k}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private def slice (l : H →ₗ[k] k) : V ⊗[k] H →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap.comp (l.lTensor V)

@[simp]
private theorem slice_tmul (l : H →ₗ[k] k) (v : V) (a : H) :
    slice l (v ⊗ₜ[k] a) = l a • v := by
  simp [slice]

private theorem slice_natural (l : H →ₗ[k] k) (f : V →ₗ[k] W) (t : V ⊗[k] H) :
    f (slice l t) = slice l (f.rTensor H t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v a => simp
  | add t s ht hs => simp only [map_add, ht, hs]

private theorem tensor_eq_of_slices {t s : V ⊗[k] H}
    (h : ∀ l : H →ₗ[k] k, slice l t = slice l s) : t = s := by
  classical
  let b := Module.Free.chooseBasis k H
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  apply Finsupp.ext
  intro i
  rw [TensorProduct.equivFinsuppOfBasisRight_apply, TensorProduct.equivFinsuppOfBasisRight_apply]
  exact h (b.coord i)

private theorem tensor_mem_range_iff (S : Submodule k V) (t : V ⊗[k] H) :
    t ∈ LinearMap.range (S.subtype.rTensor H) ↔ ∀ l : H →ₗ[k] k, slice l t ∈ S := by
  constructor
  · rintro ⟨s, rfl⟩ l
    rw [← slice_natural]
    exact (slice l s).property
  · intro h
    classical
    let b := Module.Free.chooseBasis k H
    let c := TensorProduct.equivFinsuppOfBasisRight b t
    have hc (i) : c i ∈ S := by
      change TensorProduct.equivFinsuppOfBasisRight b t i ∈ S
      rw [TensorProduct.equivFinsuppOfBasisRight_apply]
      exact h (b.coord i)
    refine ⟨∑ i ∈ c.support, (⟨c i, hc i⟩ : S) ⊗ₜ[k] b i, ?_⟩
    rw [map_sum]
    simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
    simpa only [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum] using
      (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply t

private def deviation (ρ : RightComodule k H V) (l : H →ₗ[k] k) : Module.End k V :=
  (slice l).comp (invariantDifference H ρ)

private theorem deviation_apply (ρ : RightComodule k H V) (l : H →ₗ[k] k) (x : V) :
    deviation ρ l x = slice l (ρ.coaction x) - l 1 • x := by
  change slice l (ρ.coaction x - x ⊗ₜ[k] (1 : H)) = _
  rw [map_sub, slice_tmul]

private theorem mem_invariants_iff_deviation (ρ : RightComodule k H V) (x : V) :
    x ∈ invariants H ρ ↔ ∀ l, deviation ρ l x = 0 := by
  change invariantDifference H ρ x = 0 ↔ _
  constructor
  · intro hx l
    change slice l (invariantDifference H ρ x) = 0
    rw [hx, map_zero]
  · intro hx
    apply tensor_eq_of_slices
    intro l
    rw [map_zero]
    exact hx l

private theorem stable_iff (ρ : RightComodule k H V) (S : Submodule k V) :
    Stable (deviation ρ) S ↔ ρ.IsSubcomodule S := by
  constructor
  · intro h x
    apply (tensor_mem_range_iff S _).mpr
    intro l
    have hx : deviation ρ l x ∈ S := h l x.property
    simpa only [deviation_apply, sub_add_cancel] using S.add_mem hx (S.smul_mem (l 1) x.property)
  · intro h l x hx
    change deviation ρ l x ∈ S
    rw [deviation_apply]
    exact S.sub_mem ((tensor_mem_range_iff S _).mp (h ⟨x, hx⟩) l) (S.smul_mem _ hx)

private theorem simple_iff (ρ : RightComodule k H V) (S : Submodule k V) :
    Simple (deviation ρ) S ↔ IsSimpleSubcomodule ρ S := by
  simp only [Simple, IsSimpleSubcomodule, Specs.rationalIsSimpleSubcomodule, stable_iff]

private theorem comoduleMap_iff_deviation {ρ : RightComodule k H V} {σ : RightComodule k H W}
    (f : V →ₗ[k] W) :
    IsComoduleMap ρ σ f ↔ ∀ l x, f (deviation ρ l x) = deviation σ l (f x) := by
  constructor
  · intro hf l x
    have h : f.rTensor H (ρ.coaction x) = σ.coaction (f x) := DFunLike.congr_fun hf x
    rw [deviation_apply, deviation_apply, map_sub, map_smul, slice_natural, h]
  · intro hf
    apply LinearMap.ext
    intro x
    change f.rTensor H (ρ.coaction x) = σ.coaction (f x)
    apply tensor_eq_of_slices
    intro l
    have h := hf l x
    rw [deviation_apply, deviation_apply, map_sub, map_smul, slice_natural] at h
    exact sub_left_inj.mp h

private theorem trivial_deviation {X : Type u} [AddCommGroup X] [Module k X]
    (l : H →ₗ[k] k) (x : X) : deviation (trivial H) l x = 0 := by
  rw [deviation_apply]
  change slice l (x ⊗ₜ[k] (1 : H)) - l 1 • x = 0
  rw [slice_tmul, sub_self]

private theorem comoduleMap_trivial_iff_deviation (ρ : RightComodule k H V)
    {X : Type u} [AddCommGroup X] [Module k X] (P : V →ₗ[k] X) :
    IsComoduleMap ρ (trivial H) P ↔ ∀ l x, P (deviation ρ l x) = 0 := by
  rw [comoduleMap_iff_deviation]
  simp only [trivial_deviation]

private theorem deviations_span (h : LinearlyReductive H) (ρ : RightComodule k H V) :
    Spans (deviation ρ) := by
  intro B hB
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨S, hx⟩ := locallyFinite ρ x
  let : FiniteDimensional k S.val := S.property.2
  obtain ⟨σ, hσ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction ρ S.val).mp S.property.1
  obtain ⟨n, T, hs, hsum⟩ := h S.val σ
  exact span_local_piece B hB S.val (deviation σ) ((comoduleMap_iff_deviation S.val.subtype).mp hσ)
    T (fun i ↦ (simple_iff σ (T i)).mpr (hs i)) hsum.submodule_iSup_eq_top hx

theorem canonicalProjection : Specs.RationalProjection.{u} := by
  intro k V _ H _ _ h ρ
  have hspan := deviations_span h ρ
  obtain ⟨P, hP, hnP, hdP⟩ := exists_projection hspan (mem_invariants_iff_deviation ρ)
  refine ⟨P, ⟨(comoduleMap_trivial_iff_deviation ρ P).mpr hdP, hP, ?_⟩, ?_⟩
  · intro S hs hnt x
    exact hnP S ((simple_iff ρ S).mpr hs) hnt x
  · intro Q hQ
    exact projection_unique hspan hQ.1 hP
      (fun S hs ↦ hQ.2 S ((simple_iff ρ S).mp hs)) hnP

theorem canonicalProjection_natural : Specs.RationalProjectionNatural.{u} := by
  intro k V W _ H _ _ _ _ h ρ σ P Q hP hQ f hf x
  exact projection_natural (deviations_span h ρ)
    (mem_invariants_iff_deviation ρ) (mem_invariants_iff_deviation σ) hP.2.1 hQ.2.1
    ((comoduleMap_trivial_iff_deviation ρ P).mp hP.1)
    ((comoduleMap_trivial_iff_deviation σ Q).mp hQ.1) f
    ((comoduleMap_iff_deviation f).mp hf) x

theorem canonicalProjection_restriction : Specs.RationalProjectionRestriction.{u} := by
  intro k V _ H _ _ h ρ S _ σ hσ P Q hP hQ x
  exact canonicalProjection_natural h σ ρ Q P hQ hP S.subtype hσ x

theorem canonicalProjection_reynolds : Specs.RationalProjectionReynolds.{u} := by
  intro k A _ H _ _ h ρ P hP
  refine ⟨hP.1, ?_, hP.2.1⟩
  intro a x
  let f : A →ₗ[k] A := Algebra.lmul k A (a : A)
  have ha : ρ.coaction (a : A) = (a : A) ⊗ₜ[k] (1 : H) := sub_eq_zero.mp a.property
  have hr (t : A ⊗[k] H) : f.rTensor H t = ((a : A) ⊗ₜ[k] (1 : H)) * t := by
    induction t using TensorProduct.inductionOn with
    | tmul y b =>
      rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rfl
    | add t s ht hs => rw [map_add, mul_add, ht, hs]
  have hf : IsComoduleMap (RationalAlgebraAction.toRightComodule ρ)
      (RationalAlgebraAction.toRightComodule ρ) f := by
    apply LinearMap.ext
    intro y
    change f.rTensor H (ρ.coaction y) = ρ.coaction ((a : A) * y)
    rw [hr, map_mul, ha]
  apply Subtype.ext
  exact canonicalProjection_natural h (RationalAlgebraAction.toRightComodule ρ)
    (RationalAlgebraAction.toRightComodule ρ) P P hP hP f hf x

end RationalRepresentation

end

end RepTheorySurvey.Invariants
