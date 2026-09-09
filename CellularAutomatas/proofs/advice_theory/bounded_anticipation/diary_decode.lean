import CellularAutomatas.proofs.advice_theory.bounded_anticipation.diary
import Mathlib.Data.Finset.Max

namespace CellularAutomatas.BoundedAnticipation

open CellAutomaton

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

abbrev Samples (a : ℕ) (Γ : Type) :=
  Fin (a + 1) → Option ((Fin (a + 1) → Option Γ) × Bool)

def activeSlots {a : ℕ} (samples : Samples a Γ) : Finset (Fin (a + 1)) :=
  Finset.univ.filter fun j => (samples j).any (fun entry => !entry.2) = true

/-- Select the most recent diary that still belongs to the input, then
extract the symbol at the start of the fixed-width history window. -/
def decode {a : ℕ} (samples : Samples a Γ) : Γ :=
  if h : (activeSlots samples).Nonempty then
    let latest := (activeSlots samples).max' h
    ((samples latest).bind (fun entry => entry.1 latest)).getD default
  else default

def selectedSlot (a n i : ℕ) : Fin (a + 1) :=
  ⟨min a (n - 1 - i), Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩

omit [Alphabet Γ] in
theorem activeSlots_mem (a n i : ℕ)
    (values : Fin (a + 1) → Fin (a + 1) → Option Γ) (j : Fin (a + 1)) :
    j ∈ activeSlots (fun k => some (values k, decide (n ≤ i + k.val))) ↔
      i + j.val < n := by
  simp [activeSlots]

theorem decode_samples (a n i : ℕ) (hi : i < n)
    (values : Fin (a + 1) → Fin (a + 1) → Option Γ) :
    decode (fun k => some (values k, decide (n ≤ i + k.val))) =
      (values (selectedSlot a n i) (selectedSlot a n i)).getD default := by
  let samples : Samples a Γ := fun k => some (values k, decide (n ≤ i + k.val))
  have hselected : selectedSlot a n i ∈ activeSlots samples := by
    rw [activeSlots_mem]
    dsimp only [selectedSlot]
    omega
  have hexists : (activeSlots samples).Nonempty := ⟨_, hselected⟩
  have hmax : (activeSlots samples).max' hexists = selectedSlot a n i := by
    apply (Finset.max'_eq_iff _ _ _).mpr
    refine ⟨hselected, ?_⟩
    intro j hj
    have hinside := (activeSlots_mem a n i values j).mp hj
    show j.val ≤ min a (n - 1 - i)
    have hjbound := j.isLt
    omega
  change decode samples = _
  simp only [decode, dif_pos hexists]
  rw [hmax]
  rfl

def taggedDiary (advice : Advice α Γ) (a : ℕ) (hclosed : advice.weak_rt_closed) :
    CArtTransducer α ((Fin (a + 1) → Option Γ) × Bool) :=
  diary advice a hclosed ⨂
    ({ C_orig := diary advice a hclosed } : TraceToTraceRtAndBorder).C_mark_border

abbrev diaryHistory (advice : Advice α Γ) (a : ℕ) [NeZero a]
    (hclosed : advice.weak_rt_closed) : TraceKx where
  k := a
  α := Option α
  β := (Fin (a + 1) → Option Γ) × Bool
  C_orig := taggedDiary advice a hclosed

theorem diaryHistory_spec (advice : Advice α Γ) (a : ℕ) [NeZero a]
    (hclosed : advice.weak_rt_closed) (word : Word α) (i : ℕ) :
    (diaryHistory advice a hclosed).C.trace (word_to_config word) (a + i) =
      fun j => some ((diary advice a hclosed).trace word (i + j.val),
        decide (word.length ≤ i + j.val)) := by
  rw [Nat.add_comm a i]
  change (diaryHistory advice a hclosed).C.comp (word_to_config word) (i + a) 0 = _
  rw [(diaryHistory advice a hclosed).spec_at (word_to_config word) i (0 : ℤ)]
  funext j
  apply congrArg some
  change (taggedDiary advice a hclosed).trace word (i + j.val) = _
  simp only [taggedDiary, CellAutomaton.trace, ca_zip_comp]
  have hborder := ({ C_orig := diary advice a hclosed } :
    TraceToTraceRtAndBorder).spec_mark_border2 word (i + j.val)
  simpa only [Nat.not_lt_zero, decide_false, Bool.false_or, ge_iff_le] using
    congrArg (fun border => ((diary advice a hclosed).trace word (i + j.val), border)) hborder

omit [Alphabet Γ] in
theorem suffix_at (a i : ℕ) (word : Word Γ) (j : Fin (a + 1))
    (hlength : word.length = i + j.val + 1) :
    suffix a word j = word[i]? := by
  have hj : j.val < word.length := by omega
  have hindex : word.length - 1 - j.val = i := by omega
  simp only [suffix, List.getElem?_reverse, hj, hindex]

/-- Interior outputs use bounded anticipation. Near the end, the last
complete diary already contains the desired symbol. -/
theorem latest_diary_symbol (advice : Advice α Γ) (a : ℕ)
    (hclosed : advice.weak_rt_closed) (hanticipation : advice.HasAnticipation a)
    (word : Word α) (i : ℕ) (hi : i < word.length) :
    let j := selectedSlot a word.length i
    (diary advice a hclosed).trace word (i + j.val) j = (advice word)[i]? := by
  let j := selectedSlot a word.length i
  have htime : i + j.val < word.length := by
    dsimp only [j, selectedSlot]
    omega
  change (diary advice a hclosed).trace word (i + j.val) j = _
  rw [diary_spec advice a hclosed word (i + j.val) htime,
    suffix_at a i (advice (word.take (i + j.val + 1))) j
      (by rw [advice_len, List.length_take_of_le (by omega)])]
  by_cases hinterior : i + a < word.length
  · show (advice (word.take (i + j.val + 1)))[i]? = (advice word)[i]?
    have hj : j.val = a := by
      dsimp only [j, selectedSlot]
      exact Nat.min_eq_left (by omega)
    rw [hj]
    exact (hanticipation word i hi).symm
  · show (advice (word.take (i + j.val + 1)))[i]? = (advice word)[i]?
    have hend : i + j.val + 1 = word.length := by
      dsimp only [j, selectedSlot]
      omega
    rw [hend, List.take_length]

def decodedDiary (advice : Advice α Γ) (a : ℕ) [NeZero a]
    (hclosed : advice.weak_rt_closed) : CArtTransducer α Γ :=
  (diaryHistory advice a hclosed).C.map_project decode

theorem decodedDiary_spec (advice : Advice α Γ) (a : ℕ) [NeZero a]
    (hclosed : advice.weak_rt_closed) (hanticipation : advice.HasAnticipation a)
    (word : Word α) (i : ℕ) (hi : i < word.length) :
    (decodedDiary advice a hclosed).trace word (a + i) =
      (advice word)[i]'(by simpa using hi) := by
  rw [decodedDiary, trace_of_map_project]
  change decode ((diaryHistory advice a hclosed).C.trace (word_to_config word) (a + i)) = _
  rw [diaryHistory_spec, decode_samples a word.length i hi,
    latest_diary_symbol advice a hclosed hanticipation word i hi,
    List.getElem?_eq_getElem (by simpa using hi)]
  rfl

end CellularAutomatas.BoundedAnticipation

namespace CellularAutomatas

noncomputable def Advice.delayedTrace_of_weak_rt_closed {α Γ : Type}
    [Alphabet α] [Alphabet Γ] (advice : Advice α Γ) (a : ℕ) (ha : 0 < a)
    (hanticipation : advice.HasAnticipation a) (hclosed : advice.weak_rt_closed) :
    advice.DelayedTrace a := by
  letI : NeZero a := ⟨by omega⟩
  exact {
    C := BoundedAnticipation.decodedDiary advice a hclosed
    spec := BoundedAnticipation.decodedDiary_spec advice a hclosed hanticipation
  }

end CellularAutomatas
