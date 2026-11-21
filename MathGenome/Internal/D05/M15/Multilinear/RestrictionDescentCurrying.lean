import MathGenome.Internal.Specs.D05.M15.Multilinear.RestrictionDescentCurrying
import MathGenome.Internal.D05.M15.Multilinear
import MathGenome.Internal.D05.M06.QuotientLift
import MathGenome.Internal.D05.M06.Complement
import MathGenome.Internal.D05.M02.BasisExtension.Choice
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.FinCases

/-! Restriction, two-sided quotient descent, extension by complements, and
currying, without finite-dimensional or characteristic assumptions. -/
namespace D05.M15.Multilinear.RestrictionDescentCurrying

theorem restriction : Specs.D05.M15.Multilinear.RestrictionDescentCurrying.restriction := by
  intro K I V H _ _ _ _ _ b U
  exact ⟨b.compLinearMap (fun i => (U i).subtype), fun _ => rfl⟩

theorem bilinear_restriction : Specs.D05.M15.Multilinear.RestrictionDescentCurrying.bilinear_restriction := by
  intro K V W H _ _ _ _ _ _ _ U S b
  exact ⟨b.domRestrict₁₂ U S, fun _ _ => rfl⟩

theorem descent_iff : Specs.D05.M15.Multilinear.RestrictionDescentCurrying.descent_iff := by
  intro K V W H _ _ _ _ _ _ _ U S b
  constructor
  · rintro ⟨d, hd, _⟩
    constructor
    · intro u hu w
      rw [← hd, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hu]
      simp
    · intro v s hs
      rw [← hd]
      have hz : S.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hs
      rw [hz]
      simp
  · rintro ⟨hU, hS⟩
    have hU' : U ≤ b.ker := by
      intro u hu
      exact LinearMap.ext (hU u hu)
    have hS' : S ≤ b.flip.ker := by
      intro s hs
      exact LinearMap.ext (fun v => hS v s hs)
    refine ⟨b.liftQ₂ U S hU' hS', fun _ _ => rfl, ?_⟩
    intro d hd
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    obtain ⟨v, rfl⟩ := U.mkQ_surjective x
    obtain ⟨w, rfl⟩ := S.mkQ_surjective y
    exact hd v w

theorem descent_mod_iff : Specs.D05.M15.Multilinear.RestrictionDescentCurrying.descent_mod_iff := by
  intro K V W H _ _ _ _ _ _ _ U S L b
  have h := descent_iff U S (b.compr₂ L.mkQ)
  simpa only [LinearMap.compr₂_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] using h

theorem extension_with_complements : Specs.D05.M15.Multilinear.RestrictionDescentCurrying.extension_with_complements := by
  intro K V W H _ _ _ _ _ _ _ U U' S S' hU hS b
  let p := U.projectionOnto U' hU
  let q := S.projectionOnto S' hS
  let B := b.compl₁₂ p q
  have hB :
      (∀ (u : U) (s : S), B (u : V) (s : W) = b u s) ∧
      (∀ v ∈ U', ∀ w, B v w = 0) ∧ (∀ v, ∀ w ∈ S', B v w = 0) := by
    refine ⟨?_, ?_, ?_⟩
    · intro u s
      simp [B, p, q]
    · intro v hv w
      simp [B, p, Submodule.projectionOnto_apply_of_mem_right hU hv]
    · intro v w hw
      simp [B, q, Submodule.projectionOnto_apply_of_mem_right hS hw]
  refine ⟨B, hB, ?_⟩
  rintro C ⟨hC, hCU, hCS⟩
  ext v w
  have hv : v ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
  have hw : w ∈ S ⊔ S' := by rw [hS.sup_eq_top]; trivial
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨s, hs, s', hs', rfl⟩ := Submodule.mem_sup.mp hw
  simp only [map_add, LinearMap.add_apply]
  rw [hCU u' hu', hCU u' hu', hCS u s' hs', hC ⟨u, hu⟩ ⟨s, hs⟩,
    hB.2.1 u' hu', hB.2.1 u' hu', hB.2.2 u s' hs', hB.1 ⟨u, hu⟩ ⟨s, hs⟩]

theorem extension : Specs.D05.M15.Multilinear.RestrictionDescentCurrying.extension := by
  intro K V W H _ _ _ _ _ _ _ U S b
  obtain ⟨U', hU⟩ := U.exists_isCompl
  obtain ⟨S', hS⟩ := S.exists_isCompl
  obtain ⟨B, hB, _⟩ := extension_with_complements U U' S S' hU hS b
  exact ⟨U', S', hU, hS, B, hB⟩

theorem extension_can_differ :
    Specs.D05.M15.Multilinear.RestrictionDescentCurrying.extension_can_differ := by
  intro K _
  dsimp only
  let U := Submodule.span K ({(1, 0)} : Set (K × K))
  let B₀ : (K × K) →ₗ[K] K →ₗ[K] K :=
    (LinearMap.lsmul K K).comp (LinearMap.fst K K K)
  let B₁ : (K × K) →ₗ[K] K →ₗ[K] K :=
    (LinearMap.lsmul K K).comp (LinearMap.fst K K K - LinearMap.snd K K K)
  let b := B₀.comp U.subtype
  refine ⟨b, B₀, B₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have he := congrArg (fun B : (K × K) →ₗ[K] K →ₗ[K] K => B (1, 1) 1) h
    simp [B₀, B₁] at he
  · simpa using D05.M06.Complement.coordinate_line_isCompl (0 : K)
  · exact D05.M06.Complement.coordinate_line_isCompl (1 : K)
  · intro u w
    refine ⟨rfl, ?_⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp u.property
    have hy : (u : K × K).2 = 0 := by
      simpa using (congrArg Prod.snd ha).symm
    change ((u : K × K).1 - (u : K × K).2) * w = (u : K × K).1 * w
    rw [hy, sub_zero]
  · intro v hv w
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp [B₀]
  · intro v hv w
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp [B₁]

/-- Uncurrying into the prerequisite's actual two-slot multilinear type. -/
def uncurryTwo {K : Type*} {M : Fin 2 → Type*} {H : Type*} [Field K]
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [AddCommGroup H] [Module K H] (f : M 0 →ₗ[K] M 1 →ₗ[K] H) :
    MultilinearMap K M H :=
  MultilinearMap.mk' (fun m => f (m 0) (m 1))
    (by intro m i x y; fin_cases i <;> simp)
    (by intro m i c x; fin_cases i <;> simp)

private theorem snoc_pair {M : Fin 2 → Type*} (x : M 0) (y : M 1) :
    Fin.snoc (Fin.cons x finZeroElim) y = (piFinTwoEquiv M).symm (x, y) := by
  funext i
  fin_cases i
  · simp
  · exact Fin.snoc_last _ _

/-- Currying is built slotwise, rather than identifying the two types by fiat. -/
def curryTwo {K : Type*} {M : Fin 2 → Type*} {H : Type*} [Field K]
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [AddCommGroup H] [Module K H] (b : MultilinearMap K M H) :
    M 0 →ₗ[K] M 1 →ₗ[K] H :=
  LinearMap.mk₂ K (fun x y => b ((piFinTwoEquiv M).symm (x, y)))
    (by intro x x' y; simpa using b.cons_add (Fin.cons y finZeroElim) x x')
    (by intro c x y; simpa using b.cons_smul (Fin.cons y finZeroElim) c x)
    (by intro x y y'; simpa only [snoc_pair] using b.snoc_add (Fin.cons x finZeroElim) y y')
    (by intro c x y; simpa only [snoc_pair] using b.snoc_smul (Fin.cons x finZeroElim) c y)

theorem currying : Specs.D05.M15.Multilinear.RestrictionDescentCurrying.currying := by
  intro K M H _ _ _ _ _
  let E : MultilinearMap K M H ≃ₗ[K] (M 0 →ₗ[K] M 1 →ₗ[K] H) :=
    { toFun := curryTwo
      invFun := uncurryTwo
      left_inv := by
        intro b
        ext m
        change b ((piFinTwoEquiv M).symm (m 0, m 1)) = b m
        exact congrArg b ((piFinTwoEquiv M).symm_apply_apply m)
      right_inv := by intro f; ext x y; rfl
      map_add' := by intro b c; ext x y; rfl
      map_smul' := by intro c b; ext x y; rfl }
  refine ⟨E, ?_, fun _ _ => rfl⟩
  intro b m
  change b ((piFinTwoEquiv M).symm (m 0, m 1)) = b m
  exact congrArg b ((piFinTwoEquiv M).symm_apply_apply m)

end D05.M15.Multilinear.RestrictionDescentCurrying
