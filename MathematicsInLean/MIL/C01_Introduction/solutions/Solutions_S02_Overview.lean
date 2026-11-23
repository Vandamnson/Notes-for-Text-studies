import MIL.Common

open Nat
open Real 
-- There are no exercises in this section.
#check 2 + 2 

def f(x: Nat ): Real := 
  x + 4.2

#check f

example : ∀ m n : Nat, Even n → Even (m * n) := 
fun m n ⟨k, hk⟩ ↦ ⟨ m * k, by rw [hk, mul_add]⟩

example : ∀ m n : Nat, Even n → Even (m * n) := by 
  rintro m n ⟨k, hk ⟩
  use m * k 
  rw [hk]
  ring 

example : ∀ m n : Nat, Even n → Even (m * n) := by 
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring


