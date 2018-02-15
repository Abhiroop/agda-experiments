module Day1 where

  data Maybe {α} (A : Set α) : Set α where
    just : (a : A) → Maybe A
    nothing : Maybe A

  data Nat : Set where
    zero : Nat
    succ : Nat → Nat

  data Bool : Set where
    true  : Bool
    false : Bool

  _<_ : Nat → Nat → Bool
  zero < zero = false
  zero < succ b = true
  succ a < zero = false
  succ a < succ b = a < b

  _+_ : Nat → Nat → Nat
  zero + b = b
  succ a + b = succ (a + b)

  if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
  if true then y else z = y
  if false then y else z = z

  data Type : Set where
    nat : Type
    bool : Type

  data Expr : Type → Set where
    lit : (n : Nat) → Expr nat
    true : Expr bool
    false : Expr bool
    less : (a b : Expr nat) → Expr bool
    plus : (a b : Expr nat) → Expr nat
    if   : ∀ {t} → (a : Expr bool) (b c : Expr t) → Expr t

  Value : Type → Set
  Value nat = Nat
  Value bool = Bool

  eval : ∀ {t} → Expr t → Value t
  eval (lit n) = n
  eval true = true
  eval false = false
  eval (less e e₁) = eval e < eval e₁
  eval (plus e e₁) = eval e + eval e₁
  eval (if e e₁ e₂) = if eval e then eval e₁ else eval e₂
