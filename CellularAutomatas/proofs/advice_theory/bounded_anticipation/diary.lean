import CellularAutomatas.proofs.advice_theory.bounded_anticipation.defs
import CellularAutomatas.proofs.advice_theory.rt_disclosure_observability
import CellularAutomatas.proofs.advice_theory.compose_trace_rt.compose_cart

namespace CellularAutomatas.BoundedAnticipation

open CellAutomaton

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

def suffix (a : ℕ) (word : Word Γ) : Fin (a + 1) → Option Γ :=
  fun j => word.reverse[j.val]?

def suffixDFA (a : ℕ) : DFA (α × Γ) (Fin (a + 1) → Option Γ) where
  start := fun _ => none
  step history letter := Fin.cases (some letter.2) (fun j => history j.castSucc)
  accept := Set.univ

omit [Alphabet α] [Alphabet Γ] in
theorem suffix_step (a : ℕ) (word : Word Γ) (letter : α × Γ) :
    (suffixDFA a).step (suffix a word) letter = suffix a (word ++ [letter.2]) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · show some letter.2 = (word ++ [letter.2]).reverse[0]?
    simp
  · show suffix a word k.castSucc = (word ++ [letter.2]).reverse[k.succ.val]?
    simp [suffix, List.reverse_append]

omit [Alphabet α] [Alphabet Γ] in
theorem suffix_evalFrom (a : ℕ) (word : Word Γ) (input : Word (α × Γ)) :
    (suffixDFA a).evalFrom (suffix a word) input =
      suffix a (word ++ input.map Prod.snd) := by
  induction input generalizing word with
  | nil =>
      show suffix a word = suffix a (word ++ [].map Prod.snd)
      simp
  | cons letter rest ih =>
      show (suffixDFA a).evalFrom ((suffixDFA a).step (suffix a word) letter) rest =
        suffix a (word ++ (letter :: rest).map Prod.snd)
      rw [suffix_step, ih]
      simp [List.append_assoc]

def probe (advice : Advice α Γ) (a : ℕ) :
    advice.RtProbe (Fin (a + 1) → Option Γ) :=
  Advice.RtProbe.ofAnnotatedDFA advice (suffixDFA a) id

theorem probe_value (advice : Advice α Γ) (a : ℕ) (word : Word α) :
    (probe advice a).value word = suffix a (advice word) := by
  change (suffixDFA a).evalFrom (suffix a []) (advice.annotate word) = _
  rw [suffix_evalFrom]
  simp [Advice.annotate, List.map_snd_zip, advice_len]

def diary (advice : Advice α Γ) (a : ℕ) (hclosed : advice.weak_rt_closed) :
    CArtTransducer α (Fin (a + 1) → Option Γ) :=
  (probe advice a).cart hclosed

theorem diary_spec (advice : Advice α Γ) (a : ℕ)
    (hclosed : advice.weak_rt_closed) (word : Word α) (s : ℕ) (hs : s < word.length) :
    (diary advice a hclosed).trace word s =
      suffix a (advice (word.take (s + 1))) := by
  have htrace := (probe advice a).cart_trace_spec hclosed word
  have hentry := congrArg (fun values => values[s]?) htrace
  simp only [trace_rt, List.getElem?_map, List.getElem?_range hs,
    Option.map_some, Advice.RtProbe.disclosure, Advice.FreeProbe.disclosure] at hentry
  simpa only [List.getElem?_map, List.getElem?_range hs, Option.map_some,
    Option.some.injEq, probe_value] using hentry

end CellularAutomatas.BoundedAnticipation
