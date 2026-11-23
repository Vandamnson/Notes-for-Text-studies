import MIL.Common
#check 2 + 2
def f(x : Nat) :=
  x+3
#check f
#check 2 + 2 = 4
def FermatsLastTheorem :=
 ∀ x y z n : Nat, n>2 ∧ x * y * z ≠ 0 → x^n + y^n ≠ z^n
#check FermatsLastTheorem
theorem easy: 2 + 2 =4 :=
rfl
#check easy
theorem hard: FermatsLastTheorem :=
  sorry
#check hard
example : ∀ m n : Nat, Even n → Even (m * n) :=
  fun m n ⟨k, (hk : n = k + k)⟩ ↦
    have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
    show ∃ l, m * n = l + l from ⟨_, hmn⟩

example: ∀ m n : Nat, Even n → Even (m * n) :=
  fun m n ⟨k, hk⟩ ↦ ⟨ m * k, by rw [hk, mul_add] ⟩

example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk]
  ring

example: ∀ m n : Nat, Even n → Even (m * n) := by rintro  m n ⟨k, hk ⟩; use m * k ; rw [hk]; ring

example: ∀ m n : Nat, Even n → Even (m * n) := by intros; simp[*,parity_simps ]

example (a b c : ℝ ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw[mul_assoc b c a]
  rw[mul_comm a c]



example (a b c : ℝ ) : a * (b * c) = b * (a * c) := by
  rw[← mul_assoc b a c]
  rw[mul_comm b a]
  rw[mul_assoc ]


example (a b c: ℝ ) : a * b * c = b * c * a := by
  rw[mul_assoc]
  rw[mul_comm]

example (a b c : ℝ ): a*(b*c)=b*(c*a):= by rw[mul_comm]; rw[mul_assoc]
example (a b c : ℝ ): a*(b*c)=b*(a*c):= by rw[mul_comm]; rw[mul_assoc]; rw[mul_comm c a]

example (a b c d e f : ℝ) (h: a*b = c*d)(h':e = f): a*(b*e)=c*(d*f) := by
  rw [h']
  rw  [← mul_assoc]
  rw [h]
  rw[mul_assoc]

  example(a b c d e f: ℝ) (h:b*c=e*f):a*b*c*d = a*e*f*d := by
    rw[mul_assoc a b c, h, ← mul_assoc a e f ]

  example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
    rw[hyp]
    rw[hyp']
    rw[mul_comm b a]
    rw[sub_self]
  example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
    rw[h',←  mul_assoc, h, mul_assoc]

example(a b c d e f: ℝ) (h:b*c=e*f):a*b*c*d = a*e*f*d := by rw[mul_assoc, mul_assoc, ← mul_assoc b c d, h, mul_assoc, mul_assoc, mul_assoc]

variable (a b c d e f : ℝ )

example (h: a*b=c*d)(h':e=f):a * (b * e) = c * (d * f) := by
  rw[← mul_assoc, h, mul_assoc, h' ]

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a: ℝ )
#check mul_comm a
#check (mul_comm a b : a*b=b*a)

end
section
variable (a b : ℝ)
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw[ mul_add,add_mul,add_mul]
  rw[← add_assoc, add_assoc (a*a) (b*a) (a*b), mul_comm b a, ← two_mul  ]
end

#check two_mul
#check mul_add
#check add_mul
#check add_assoc


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw[mul_add,add_mul,add_mul, add_assoc, add_comm, ← add_assoc, add_comm, ← add_assoc, add_comm (b*c),add_assoc,add_assoc, add_assoc,add_assoc  ]
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = a * c + b * c + (a * d + b * d) := by
      rw[mul_add, add_mul,add_mul]
    _= a * c + (a * d + b * c + b * d) := by
      rw[add_assoc, ← add_assoc (b*c), add_comm (b*c)]
    _= a * c + a * d + b * c + b * d := by
      rw[← add_assoc, ← add_assoc (a*c)]
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw[mul_add, add_mul, add_mul, add_assoc, ← add_assoc (b * c), add_comm (b * c), ← add_assoc, ← add_assoc (a*c)]
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
    rw[mul_sub,add_mul,add_mul, ← sub_sub, mul_comm b a, ← add_sub (a*a) (a*b) (a*b), sub_self, add_zero (a*a), ← pow_two a, ← pow_two b ]

#check pow_two a
#check mul_sub a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a


example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [pow_two a, pow_two b, ← add_zero (a*a), ← sub_self (a*b),  add_sub, ← mul_add, mul_comm a b, sub_sub, ← mul_add, mul_comm b (a + b), mul_comm a, ← mul_sub (a+b) a b  ]

example (a b c d : ℝ ) (hyp : c = d * a + b) (hyp':b=a*d): c=2*a*d := by
  rw[hyp'] at hyp
  rw[mul_comm] at hyp
  rw[hyp, ← mul_add, ← two_mul, ← mul_assoc, mul_comm 2 a ]
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example : c*b*a=b*(a*c) :=by
  ring
example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw[hyp, hyp']
  ring
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
    nth_rw 2[h]
    rw[add_mul]
variable (R : Type*) [Ring R]

#check (add_assoc: ∀ a b c : R, a+b+c=a+(b+c))
#check (add_zero: ∀ a : R, a+0=a)
#check (neg_add_cancel : ∀ a : R, -a + a =0 )
#check (sub_self : ∀ a : R, a-a=0)
#check(mul_one : ∀ a : R, a * 1 =a)

namespace MyRing
variable{R : Type*} [Ring R]
theorem add_zero (a:R) : a + 0 = a := by rw[add_comm, zero_add]
theorem add_neg_cancel (a : R) : a + -a =0 := by rw[add_comm,neg_add_cancel]

#check MyRing.add_zero
#check add_zero


theorem neg_add_cancel_left (a b : R): -a + (a + b)=b := by rw[← add_assoc, neg_add_cancel, zero_add]
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw[add_assoc, add_neg_cancel, add_zero]
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw[← neg_add_cancel_left a b, h, neg_add_cancel_left ]
  --rw[ ← zero_add b, ← neg_add_cancel a, add_assoc, h, ← add_assoc, neg_add_cancel, zero_add    ]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw[← add_neg_cancel_right a b, h, add_neg_cancel_right ]

end MyRing
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h: a * 0 + a * 0 = a * 0 + 0 := by
    rw[← mul_add, add_zero, add_zero]
  rw[add_left_cancel h]


theorem zero_mul (a : R) : 0 * a = 0 := by
    have h: 0*a + 0*a = 0 + 0*a := by
      rw[← add_mul, add_zero, zero_add]
    rw [add_right_cancel h]


theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw[ ← add_zero b, ← neg_add_cancel a, ← add_assoc, add_comm, ← add_assoc, h, add_comm, add_zero   ]
theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw[← add_zero a, ← neg_add_cancel b,add_comm, add_assoc, add_comm, add_comm b a,h, zero_add ]
  theorem neg_zero_a : (-0 : R) = 0 := by
    apply neg_eq_of_add_eq_zero
    rw[add_zero]
theorem neg_neg_a (a : R) : - -a = a := by
    apply neg_eq_of_add_eq_zero
    apply neg_add_cancel

example (a b : R) : a - b = a + -b := by
  rw[sub_eq_add_neg a b]


#check sub_eq_add_neg a b
example (a b : ℝ) : a - b = a + -b :=
  rfl
example (a b : ℝ) : a - b = a + -b := by
  rfl
theorem self_sub (a : R) : a - a = 0 := by
  rw[sub_eq_add_neg, add_comm, neg_add_cancel]

theorem one_add_one_eq_two_a : 1 + 1 = (2 : R) := by
  norm_num

#check norm_num

theorem two_mul_a (a : R) : 2 * a = a + a := by
  rw[ ← one_add_one_eq_two_a, add_mul, one_mul]


variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

theorem mul_inv_cancel_a (a : G) : a * a⁻¹ = 1 := by
  nth_rw 1 [← one_mul a, ← inv_mul_cancel a⁻¹]
  rw[mul_assoc, mul_assoc, ← mul_assoc a⁻¹, inv_mul_cancel, one_mul, inv_mul_cancel]

theorem mul_one_a (a : G) : a * 1 = a := by
  rw[← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel_a, one_mul ]


theorem mul_eq_cancel (a b c : G ) (h: a*b=a*c) : b = c := by
  rw[← one_mul b, ← inv_mul_cancel a, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul      ]

theorem mul_inv_rev_a (a b : G) :  (a * b)⁻¹= b⁻¹ * a⁻¹ := by
  have h : (a*b)*(a*b)⁻¹=(a*b)*(b⁻¹*a⁻¹) := by
    rw [ mul_inv_cancel_a, ← mul_assoc,  mul_assoc a, mul_inv_cancel, mul_one, mul_inv_cancel    ]
  apply mul_eq_cancel at h
  exact h

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)
#check (le_refl : ∀ a :  ℝ , a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a≤ c)
#check (le_trans h: b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

example (x y z : ℝ ) (h₀ : x ≤ y ) (h₁: y ≤ z) : x ≤ z := by
  apply le_trans h₀ h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

 example (x : ℝ) : x ≤ x :=
  le_refl x

#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

end
section
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  have h_a  : a < c := by
    apply lt_of_le_of_lt h₀ h₁
  have h_b : a < d := by
    apply lt_of_lt_of_le h_a h₂
  apply lt_trans h_b h₃


example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e :=
  lt_trans (lt_of_lt_of_le (lt_of_le_of_lt h₀ h₁) h₂) h₃

 example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e :=
  calc a ≤ b := h₀
    _ < c := h₁
    _ ≤ d := h₂
    _ < e := h₃

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith
end
section
open Real
#check exp_le_exp.mpr

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_left : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_right : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_left : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_right
