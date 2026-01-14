import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Lemmas
import Mathlib.Tactic

namespace CellularAutomatas

lemma Int.ediv_sub_one_of_emod_eq_zero {a b : ℤ} (hb : 0 < b) (h : a % b = 0) :
    (a - 1) / b = a / b - 1 := by
  have h_dvd : b ∣ a := Int.dvd_of_emod_eq_zero h
  nth_rewrite 1 [←Int.mul_ediv_cancel' h_dvd]
  rw [show b * (a / b) - 1 = (b - 1) + b * (a / b - 1) by ring]
  rw [Int.add_mul_ediv_left]
  · rw [Int.ediv_eq_zero_of_lt] <;> linarith
  · linarith

lemma Int.emod_sub_one_of_emod_eq_zero {a b : ℤ} (hb : 0 < b) (h : a % b = 0) :
    (a - 1) % b = b - 1 := by
  have h_dvd : b ∣ a := Int.dvd_of_emod_eq_zero h
  nth_rewrite 1 [←Int.mul_ediv_cancel' h_dvd]
  rw [show b * (a / b) - 1 = (b - 1) + b * (a / b - 1) by ring]
  rw [Int.add_mul_emod_self_left]
  rw [Int.emod_eq_of_lt] <;> linarith

lemma Int.ediv_sub_one_of_emod_pos {a b : ℤ} (hb : 0 < b) (h : 0 < a % b) :
    (a - 1) / b = a / b := by
  have H1 : a = b * (a / b) + a % b := (Int.mul_ediv_add_emod a b).symm
  have H2 : a - 1 = (a % b - 1) + b * (a / b) := by
    nth_rewrite 1 [H1]
    ring
  rw [H2]
  rw [Int.add_mul_ediv_left]
  · have H3 : 0 ≤ a % b - 1 := by linarith
    have H4 : a % b - 1 < b := by
       have : a % b < b := Int.emod_lt_of_pos a hb
       linarith
    rw [Int.ediv_eq_zero_of_lt H3 H4]
    simp
  · linarith

lemma Int.emod_sub_one_of_emod_pos {a b : ℤ} (hb : 0 < b) (h : 0 < a % b) :
    (a - 1) % b = a % b - 1 := by
  have H1 : a = b * (a / b) + a % b := (Int.mul_ediv_add_emod a b).symm
  have H2 : a - 1 = (a % b - 1) + b * (a / b) := by
    nth_rewrite 1 [H1]
    ring
  rw [H2]
  rw [Int.add_mul_emod_self_left]
  have H3 : 0 ≤ a % b - 1 := by linarith
  have H4 : a % b - 1 < b := by
      have : a % b < b := Int.emod_lt_of_pos a hb
      linarith
  rw [Int.emod_eq_of_lt H3 H4]

lemma Int.ediv_add_one_of_emod_lt_sub_one {a b : ℤ} (hb : 0 < b) (h : a % b < b - 1) :
    (a + 1) / b = a / b := by
  have H1 : a = b * (a / b) + a % b := (Int.mul_ediv_add_emod a b).symm
  have H2 : a + 1 = (a % b + 1) + b * (a / b) := by
    nth_rewrite 1 [H1]
    ring
  rw [H2]
  rw [Int.add_mul_ediv_left]
  · have H3 : 0 ≤ a % b + 1 := by
      have : 0 ≤ a % b := Int.emod_nonneg a (by linarith)
      linarith
    have H4 : a % b + 1 < b := by linarith
    rw [Int.ediv_eq_zero_of_lt H3 H4]
    simp
  · linarith

lemma Int.emod_add_one_of_emod_lt_sub_one {a b : ℤ} (hb : 0 < b) (h : a % b < b - 1) :
    (a + 1) % b = a % b + 1 := by
  have H1 : a = b * (a / b) + a % b := (Int.mul_ediv_add_emod a b).symm
  have H2 : a + 1 = (a % b + 1) + b * (a / b) := by
    nth_rewrite 1 [H1]
    ring
  rw [H2]
  rw [Int.add_mul_emod_self_left]
  have H3 : 0 ≤ a % b + 1 := by
      have : 0 ≤ a % b := Int.emod_nonneg a (by linarith)
      linarith
  have H4 : a % b + 1 < b := by linarith
  rw [Int.emod_eq_of_lt H3 H4]

lemma Int.ediv_add_one_of_emod_eq_sub_one {a b : ℤ} (hb : 0 < b) (h : a % b = b - 1) :
    (a + 1) / b = a / b + 1 := by
  have H1 : a = b * (a / b) + a % b := (Int.mul_ediv_add_emod a b).symm
  have H2 : a + 1 = b + b * (a / b) := by
    nth_rewrite 1 [H1]
    rw [h]
    trans b * (a/b) + b
    · ring
    · rw [add_comm]
  rw [H2]
  rw [Int.add_mul_ediv_left _ _ (ne_of_gt hb)]
  rw [Int.ediv_self (ne_of_gt hb)]
  ring

lemma Int.emod_add_one_of_emod_eq_sub_one {a b : ℤ} (h : a % b = b - 1) :
    (a + 1) % b = 0 := by
  have H1 : a = b * (a / b) + a % b := (Int.mul_ediv_add_emod a b).symm
  have H2 : a + 1 = b + b * (a / b) := by
    nth_rewrite 1 [H1]
    rw [h]
    trans b * (a/b) + b
    · ring
    · rw [add_comm]
  rw [H2]
  rw [Int.add_mul_emod_self_left]
  simp

end CellularAutomatas
