import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

section ReverseAdvice

  /-- The reverse advice maps each word to its reverse. -/
  def Advice.rev (α : Type) : Advice α α :=
    ⟨fun w => w.reverse, by simp⟩

end ReverseAdvice

section LTClosed

  variable {α : Type} [Alphabet α]
  variable {Γ : Type} [Alphabet Γ]

  -- Advice.weak_lt_closed and Advice.lt_closed are defined in defs.lean

  lemma lt_closed_implies_weak_lt_closed {f : Advice α Γ} (h : f.lt_closed) : f.weak_lt_closed := by
    have := h id
    simp [Advice.lift] at this
    exact this


  /-- If an advice is weak-LT-closed and C ∈ CA_lt(α × Γ), then (C + adv).L ∈ ℒ(CA_lt α). -/
  lemma L_mem_ℒ_of_weak_lt_closed {adv : Advice α Γ} (h : adv.weak_lt_closed)
      {C : tCellAutomaton (α × Γ)} (hC : C ∈ CA_lt (α × Γ)) :
      (C + adv).L ∈ ℒ (CA_lt α) := by
    rw [← h]
    exact ⟨_, ⟨C, hC, rfl⟩, rfl⟩

end LTClosed

section RevLTClosed

  variable (α : Type) [Alphabet α]

  /-- map_embed preserves CA_lt membership. -/
  @[simp]
  private lemma c_map_embed_in_ca_lt_iff_c_in_ca_lt (C: tCellAutomaton α) (f: β → α):
      C.map_embed f ∈ CA_lt β ↔ C ∈ CA_lt α := by rfl

  /--
    proof idea: send characters left, mirror them at cell 0
    using firing squad sync to start main CA at n steps
  -/
  theorem rev_lt_closed : (Advice.rev α).lt_closed := by
    sorry


  private lemma rev_weak_lt_closed : (Advice.rev α).weak_lt_closed :=
    lt_closed_implies_weak_lt_closed (rev_lt_closed α)

  /-- Key fact: zip w w^R and projecting Prod.snd gives w^R -/
  @[simp]
  private lemma zip_rev_map_snd {α : Type} (w : Word α) :
      List.map Prod.snd (w ⨂ w.reverse) = w.reverse := by
    simp [List.map_snd_zip]


  private lemma lt_rev_mem :
      ∀ L ∈ ℒ (CA_lt α), Language.rev L ∈ ℒ (CA_lt α) := by
    intro _ ⟨C, hC, hL⟩
    subst hL
    let C_proj : tCellAutomaton (α ⨉ α) := C.map_embed Prod.snd
    -- Key: (C_proj + rev).L = Language.rev C.L
    have key : (C_proj + Advice.rev α).L = Language.rev C.L := by
      ext w
      calc w ∈ (C_proj + Advice.rev α).L
          ↔ (w ⨂ w.reverse) ∈ C_proj.L := Iff.rfl
        _ ↔ w.reverse ∈ C.L := by rw [map_embed_L, zip_rev_map_snd]
        _ ↔ w ∈ Language.rev C.L := Iff.rfl
    -- By weak-lt-closure, (C_proj + rev).L ∈ ℒ(CA_lt α)
    change Language.rev C.L ∈ _
    rw [← key]
    exact L_mem_ℒ_of_weak_lt_closed (rev_weak_lt_closed α) hC


  theorem lt_closed_under_rev : ℒ (CA_lt α) = ℒ_rev (CA_lt α) := by
    ext L
    simp only [ℒ_rev, LanguageClass.rev]
    constructor
    · show L ∈ ℒ (CA_lt α) → L ∈ Language.rev '' ℒ (CA_lt α)
      intro hL
      exact ⟨Language.rev L, lt_rev_mem α _ hL, Language.rev_rev L⟩
    · show L ∈ Language.rev '' ℒ (CA_lt α) → L ∈ ℒ (CA_lt α)
      intro ⟨M, hM, hL⟩
      rw [← hL]
      exact lt_rev_mem α M hM

end RevLTClosed

section LTRTEquivalence

  variable (α : Type) [Alphabet α]

  /-! ### Direction theorems -/

  /-- (A) ⟹ (B): ℒ(CA_lt) is closed under spatial flip,
      so if lt = rt, then rt inherits closure under reversal. -/
  theorem lt_eq_rt_implies_rt_closed_under_rev :
      ℒ (CA_lt α) = ℒ (CA_rt α) → ℒ (CA_rt α) = ℒ_rev (CA_rt α) := by
    intro h
    -- ℒ(CA_lt) is closed under reversal; transfer via h to CA_rt
    unfold ℒ_rev LanguageClass.rev
    rw [← h]
    exact lt_closed_under_rev α

  /-- (B) ⟹ (A): The classical hard direction.
      By double reversal over Option β: lift L to Option β, pad with none^m,
      apply reversal closure twice (over Option β) and lx_rt_implies_rt, project back.
      See `proofs/rt_rev_implies_lt_eq_rt.lean` for the detailed proof. -/
  theorem rt_closed_under_rev_implies_lt_eq_rt (β : Type) [Alphabet β]
      (h : ℒ (CA_rt β) = ℒ_rev (CA_rt β)) : ℒ (CA_lt β) = ℒ (CA_rt β) := by
    sorry

  /-- (C) ⟹ (B): From weak-RT-closure of rev,
      derive closure of ℒ(CA_rt) under reversal. -/
  theorem rev_weak_rt_closed_implies_rt_closed_under_rev :
      (Advice.rev α).weak_rt_closed → ℒ (CA_rt α) = ℒ_rev (CA_rt α) := by
    intro h
    -- Helper: reversal preserves membership in ℒ(CA_rt α)
    have rt_rev_mem : ∀ L ∈ ℒ (CA_rt α), Language.rev L ∈ ℒ (CA_rt α) := by
      intro _ ⟨C, hC, hL⟩
      subst hL
      let C_proj : tCellAutomaton (α ⨉ α) := C.map_embed Prod.snd
      -- (C_proj + rev).L = Language.rev C.L
      have key : (C_proj + Advice.rev α).L = Language.rev C.L := by
        ext w
        calc w ∈ (C_proj + Advice.rev α).L
            ↔ (w ⨂ w.reverse) ∈ C_proj.L := Iff.rfl
          _ ↔ w.reverse ∈ C.L := by rw [map_embed_L, zip_rev_map_snd]
          _ ↔ w ∈ Language.rev C.L := Iff.rfl
      -- By weak-rt-closure, (C_proj + rev).L ∈ ℒ(CA_rt α)
      change Language.rev C.L ∈ _
      rw [← key, ← h]
      exact ⟨_, ⟨C_proj, hC, rfl⟩, rfl⟩
    -- Main proof: set equality (same structure as lt_closed_under_rev)
    ext L
    simp only [ℒ_rev, LanguageClass.rev]
    constructor
    · show L ∈ ℒ (CA_rt α) → L ∈ Language.rev '' ℒ (CA_rt α)
      intro hL
      exact ⟨Language.rev L, rt_rev_mem _ hL, Language.rev_rev L⟩
    · show L ∈ Language.rev '' ℒ (CA_rt α) → L ∈ ℒ (CA_rt α)
      intro ⟨M, hM, hL⟩
      rw [← hL]
      exact rt_rev_mem M hM

  /-- (B) ⟹ (C): From closure under reversal,
      derive that rev is weak-RT-closed. -/
  theorem rt_closed_under_rev_implies_rev_weak_rt_closed :
      ℒ (CA_rt α) = ℒ_rev (CA_rt α) → (Advice.rev α).weak_rt_closed := by
    sorry

  /-- The full equivalence: (A) ⟺ (B). -/
  theorem lt_rt_equivalence :
      ℒ (CA_lt α) = ℒ (CA_rt α) ↔ ℒ (CA_rt α) = ℒ_rev (CA_rt α) := by
    constructor
    · exact lt_eq_rt_implies_rt_closed_under_rev α
    · exact rt_closed_under_rev_implies_lt_eq_rt α

  /-- The full equivalence: (B) ⟺ (C). -/
  theorem rt_rev_equivalence :
      ℒ (CA_rt α) = ℒ_rev (CA_rt α) ↔ (Advice.rev α).weak_rt_closed := by
    constructor
    · exact rt_closed_under_rev_implies_rev_weak_rt_closed α
    · exact rev_weak_rt_closed_implies_rt_closed_under_rev α

end LTRTEquivalence

end CellularAutomatas
