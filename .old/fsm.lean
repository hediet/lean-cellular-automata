
  structure FiniteStateMachine (α: Type) where
    Q: Type
    [decQ: DecidableEq Q]
    [finQ: Fintype Q]
    δ: Q → α → Q
    q0: Q


  namespace FiniteStateMachine

    instance (M : FiniteStateMachine α) : DecidableEq M.Q := M.decQ
    instance (M : FiniteStateMachine α) : Fintype M.Q   := M.finQ
    instance (M : FiniteStateMachine α) : Inhabited M.Q := ⟨ M.q0 ⟩

    instance Qalpha (M: FiniteStateMachine α): Alphabet M.Q := ⟨⟩

    def scanr_step {M: FiniteStateMachine α} q a
    | []   => [M.δ q a]
    | qs@(q::_) => (M.δ q a :: qs)

    def scanr_q {M: FiniteStateMachine α} (w: Word α) (q: M.Q): Word M.Q :=
      w.foldr (scanr_step q) []

    def scanr {M: FiniteStateMachine α} w := M.scanr_q w M.q0

    def scanr_reduce {M: FiniteStateMachine α} (w: Word α): M.Q :=
      match M.scanr w with
      | []   => M.q0
      | q::_ => q

    @[simp, grind =]
    lemma scanr_q_len {M: FiniteStateMachine α} (q: M.Q) (w: List α):
      (M.scanr_q w q).length = w.length := by
      induction w with
      | nil => simp [scanr_q]
      | cons a ws ih =>
        simp [scanr_q]
        unfold scanr_step
        split
        · next h =>
          change M.scanr_q ws q = [] at h
          rw [← ih]
          rw [h]
          simp
        · next q' tail h =>
          change M.scanr_q ws q = q' :: tail at h
          rw [← ih]
          rw [h]
          simp


    @[simp, grind =]
    lemma scanr_len (M: FiniteStateMachine α) (w: List α): (M.scanr w).length = w.length := by
      simp [scanr, scanr_q_len]



  end FiniteStateMachine
