import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MIL.Common
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

variable (a b c d e x y z w : ℝ)
open Real

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_right

example (h : a ≤ b) : exp a ≤ exp b := by
  linarith [exp_le_exp.mpr h]

example (h : a ≤ b) : exp a ≤ exp b := by
  rw[ exp_le_exp]
  exact h

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_rfl
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  linarith [exp_lt_exp.mpr h₁]
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_left
  · apply exp_le_exp.mpr
    apply add_le_add_left
    exact h₀
example : (0 : ℝ) < 1 := by
  norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
   apply add_pos
   · norm_num
   · apply exp_pos
  apply log_le_log h₀
  apply add_le_add_left
  apply exp_le_exp.mpr h

  example : 0 ≤ a ^ 2 := by
  exact sq_nonneg a

  example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  refine sub_le_sub ?_ ?_
  apply le_refl
  apply exp_le_exp.mpr h

  example (h : a ≤ b) : c - exp b ≤ c - exp a := by
    linarith[exp_le_exp.mpr h]

 example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2-2*a*b+b^2
  calc
    a^2-2*a*b+b^2=(a-b)^2 := by ring
    _ ≥ 0 := by exact sq_nonneg (a - b)
  calc
    2 * a * b = 2 * a * b + 0 :=by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := by exact (add_le_add_iff_left (2 * a * b)).mpr h
    _ = a^2 + b^2 := by ring

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a*b| ≤ (a^2 + b^2)/2 := by
  apply abs_le.mpr
  constructor
  case left =>  refine le_of_sub_nonneg ?_
                rw [sub_neg_eq_add]
                linarith[sq_nonneg (a + b)]
  case right => refine (le_div_iff₀ ?_).mpr ?_
                norm_num
                rw[mul_assoc,  mul_comm b 2, ← mul_assoc, mul_comm a ]
                have h: 0 ≤ a^2 - 2*a*b + b^2
                calc
                  a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
                  _ ≥ 0 := by apply pow_two_nonneg
                linarith
example : |a*b| ≤ (a^2 + b^2)/2 := by
  apply abs_le.mpr
  constructor
  case left =>  refine le_of_sub_nonneg ?_
                rw [sub_neg_eq_add]
                linarith[sq_nonneg (a + b)]
  case right => refine le_of_sub_nonneg ?_
                linarith[sq_nonneg (a - b)]
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
#check ( le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c →  max a b ≤ c)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h: ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    · apply le_max_right
    apply le_max_left
  · show max b a ≤ max a b
    apply max_le
    · apply le_max_right
    apply le_max_left

example : max a b = max b a := by
  have g :  ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  apply g
  apply g
example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    · refine inf_le_of_left_le ?_
      apply min_le_left
    · refine min_le_min ?_ ?_
      · show min a b ≤ b
        apply min_le_right
      · show c ≤ c
        apply le_refl
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · refine inf_le_inf ?_ ?_
      · show a ≤ a
        apply le_refl
      · show min b c ≤ b
        apply min_le_left
    · refine inf_le_of_right_le ?_
      apply min_le_right

example : min (min a b) c = min a (min b c) := by
  have h: ∀ x y z : ℝ, min (min x y) z ≤  min x (min y z) := by
    intro x y z
    apply le_min
    have g :min (min x y) z ≤ min x y := by apply min_le_left (min x y) z
    have j :min x y ≤ x := by apply min_le_left
    apply le_trans g j
    have h₀: min (min x y ) z ≤ min x y := by apply min_le_left (min x y) z
    have h₀₀: min x y ≤ y := by apply min_le_right
    have h₁:min (min x y ) z ≤ z := by apply min_le_right
    have h₀₀₀ : min (min x y) z ≤ y := by apply le_trans h₀ h₀₀
    apply le_min
    apply h₀₀₀
    apply h₁
  have h': ∀ x y z : ℝ, min x (min y z) ≤ min (min x y) z := by
    intro x y z
    apply le_min
    have h₂: min x (min y z ) ≤ min y z := by apply min_le_right
    have h₃: min y z  ≤ z :=by apply min_le_right
    have h₄ : min x (min y z) ≤ x := by apply min_le_left
    have h₅ : min y z ≤ y := by apply min_le_left
    have h₆ : min x (min y z) ≤ y := by apply le_trans h₂ h₅
    apply le_min
    exact h₄
    apply le_trans h₂ h₅
    have h₂: min x (min y z ) ≤ min y z := by apply min_le_right
    have h₃: min y z  ≤ z :=by apply min_le_right
    apply le_trans h₂ h₃

  apply le_antisymm
  apply h
  apply h'
example: max (max a b ) c = max a (max b c) := by
    apply le_antisymm
    · apply max_le
      · refine sup_le_sup_left ?_ a
        apply le_max_left
      have h: (max b c) ≤ max a (max b c) := by apply le_max_right
      have g: c ≤ max b c := by apply le_max_right
      apply le_trans g h
    · apply max_le
      · have h:a ≤ max a b := by apply le_max_left
        have g: max a b ≤ max (max a b) c := by apply le_max_left
        apply le_trans h g
      · refine sup_le_sup_right ?_ c
        apply le_max_right
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
 apply le_min
 · apply add_le_add_right
   apply min_le_left
 · apply add_le_add_right
   apply min_le_right
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  ·  refine tsub_le_iff_right.mp ?_
     ring
     rw[add_comm c b, add_comm]
     nth_rw 2 [← add_neg_cancel_right a c, ← add_neg_cancel_right b c]
     apply aux (a + c) (b+c) (-c)

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  · rw[← add_le_add_iff_right (-c), add_assoc, add_neg_cancel, add_zero ]
    nth_rw 2 [← add_neg_cancel_right a c, ← add_neg_cancel_right b c ]
    apply aux

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  · have key := aux (a+c) (b+c) (-c)
    rw [add_neg_cancel_right, add_neg_cancel_right] at key   -- a+c+-c ↦ a,  b+c+-c ↦ b
    linarith [key]

#check abs_add_le
example : |a| - |b| ≤ |a - b| := by
  --|(a-b)+b| ≤ |(a-b)| + |b| --> |a| ≤ |a-b| + |b| --> |a| - |b| ≤ |a-b|
  rw[← add_le_add_iff_right |b| ]
  nth_rw 1 [ sub_add_cancel, ← sub_add_cancel a b ]
  apply abs_add_le (a-b) b

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · rw[← mul_assoc]
      apply dvd_mul_of_dvd_left
      apply dvd_mul_left
    · apply dvd_mul_left
  · apply dvd_trans h
    apply dvd_mul_left
variable (m n : ℕ )
#check Nat.gcd_zero_right
#check Nat.gcd_zero_left
#check Nat.lcm_zero_right
#check Nat.lcm_zero_left
example : Nat.gcd m n = Nat.gcd n m := by
  apply _root_.dvd_antisymm
  · apply dvd_gcd
    · apply Nat.gcd_dvd_right m n
    · apply Nat.gcd_dvd_left m n
  · apply dvd_gcd
    · apply Nat.gcd_dvd_right n m
    · apply Nat.gcd_dvd_left n m
