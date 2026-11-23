import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)
#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)


example (h : a < b) : ¬b < a := by
  intro h'
  have: a < a := lt_trans h h'
  apply lt_irrefl a this


def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a
variable (f : ℝ → ℝ)
example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨ a, fnuba ⟩
  rcases h a with ⟨x, hx⟩
  have: f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨ a, fnlba ⟩
  rcases h a with ⟨ x, hx ⟩
  have: a ≤ f x := fnlba x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  intro fnub
  rcases fnub with ⟨ a, fnuba ⟩
  have: a + 2.5 ≤ a := fnuba (a + 2.5)
  linarith

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro bleqa
  apply h at bleqa
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro monf
  have: f a ≤ f b := by apply monf h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ  ↦ (0 : ℝ )
  have monof: Monotone f := by intro a b _; apply le_refl
  have h' : f 1 ≤ f 0 := le_refl _
  have: (1 : ℝ ) ≤ 0 := by apply h monof h'
  linarith
--consider montone f then 1 ≤ 0 contradiciton, basically.
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro g
  have: x < x := by apply h; exact g
  linarith

variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  exact ⟨ x, Px ⟩

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro g
  rcases g with ⟨ x, Px ⟩
  exact h x Px





example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra Px
  apply h'
  exact ⟨ x, Px ⟩


example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  rcases h with ⟨ x, Px⟩
  intro g
  apply Px
  apply g

section practice
variable {α : Type*} (P Q : α → Prop) (p q : Prop)

-- ░░ Tier 1 — constructive: intro / rcases / exact only, no by_contra ░░

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  exact ⟨ x, Px⟩


example (h : ∀ x, P x → Q x) (h₂ : ∃ x, P x) : ∃ x, Q x := by
  rcases h₂ with ⟨ x, Px⟩
  exact ⟨ x, h x Px ⟩



example (h : ¬∃ x, P x ∧ Q x) : ∀ x, P x → ¬Q x := by
  intro x Px Qx
  apply h
  exact ⟨ x, Px, Qx⟩

example (h : ∃ x, ¬P x) (h₂ : ∀ x, P x ∨ Q x) : ∃ x, Q x := by
  rcases h with ⟨ x, Px ⟩
  rcases h₂ x with Pxx | Qxx
  · exact absurd Pxx Px
  · exact ⟨ x, Qxx⟩

example (h : ¬(p ∨ q)) : ¬p ∧ ¬q := by
  apply And.intro
  · intro hp
    apply h
    apply Or.inl
    apply hp
  · intro hq
    apply h
    apply Or.inr
    apply hq


example (h : p ∧ ¬q) : ¬(p → q) := by
  intro hpq
  rcases h with ⟨ hp, hq ⟩
  apply hq
  apply hpq
  apply hp

-- ░░ Tier 2 — classical: intro/rcases stall; reach for by_contra (and maybe a nested one) ░░

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
    by_contra h'
    apply h
    intro x
    by_contra h''
    apply h'
    exact ⟨ x, h'' ⟩

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q := by
  by_contra h'
  apply h
  rw[not_or, not_not, not_not] at h'
  exact h'

example (h : ¬(p → q)) : p ∧ ¬q := by
  by_contra h''
  rw[not_and, not_not] at h''
  apply h
  exact h''

example (h : ¬¬p) : p := by
  by_contra h'
  apply h
  exact h'

example : p ∨ ¬p := by
  by_contra h''
  rw[not_or, not_not] at h''
  rcases h'' with ⟨ hp, hnotp ⟩
  exact absurd hnotp hp
                            -- excluded middle, from scratch

-- ░░ Tier 3 — quantifiers + negation in the wild (your analysis instincts apply) ░░

example (f : ℝ → ℝ) (h : ∀ a, ∃ x, a < f x) : ¬∃ a, ∀ x, f x ≤ a := by
  intro g
  rcases g with ⟨ a, ga ⟩
  rcases h a with ⟨ x, hx ⟩
  have k : f x ≤ a := by apply ga x
  linarith



example : ¬∃ n : ℕ, ∀ m : ℕ, m ≤ n := by
  by_contra h
  rcases h with ⟨ n , hn⟩
  have: (n + 1 : ℕ ) ≤ n := by apply hn
  linarith


end practice

example (h : ¬¬ Q  ) : Q := by
  by_contra h'
  apply h
  exact h'

example (h : Q) : ¬¬Q := by
  by_contra h'
  apply h'
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  push_neg at h'
  apply h
  exact ⟨ a, h' ⟩

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb]at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [ Monotone ] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h
example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

example (h : 0 < 0) : a > 37 := by
  apply False.elim
  apply lt_irrefl at h
  exact h
example (h : 0 < 0) : a > 37 := by
  exfalso
  exact lt_irrefl 0 h

example (h : 0 < 0) : a > 37 := by
have h': ¬0 < 0 := lt_irrefl 0
contradiction
example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw[h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
⟨ h₀, fun h ↦ h₁ (by rw[h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw[h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨ h₁,h₂⟩
  contrapose! h₂
  exact le_antisymm h₁ h₂

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨ h₀, h₁⟩ h
  exact h₁ (le_antisymm h₀ h )

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h ↦ h₁ (le_antisymm h₀ h )

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h₁
  apply h.right
  exact le_antisymm h.left h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦  h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  rcases h with ⟨ h₀, h₁ ⟩
  contrapose! h₁
  exact dvd_antisymm h₀ (h₁ h₀)

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  by_contra g
  apply h.2
  rw[not_and, not_not] at g
  apply dvd_antisymm h.left (g h.left)

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  have ⟨ h₀, h₁ ⟩ := h
  contrapose! h
  intro g
  apply dvd_antisymm g (h g)

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
  ⟨ h.left, fun g ↦ h.right (dvd_antisymm h.left g) ⟩ 

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
⟨ 5 / 2 , by norm_num ⟩  

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨ z, xltz, zlty ⟩ 
  apply lt_trans xltz zlty

