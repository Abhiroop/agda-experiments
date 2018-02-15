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

  data List {α} (A : Set α) : Set α where
    [] : List A
    _::_ : (a : A) → List A → List A

  _<_ : Nat → Nat → Bool
  zero < zero = false
  zero < succ b = true
  succ a < zero = false
  succ a < succ b = a < b

  _+_ : Nat → Nat → Nat
  zero + b = b
  succ a + b = succ (a + b)

  infix 0 if_then_else_

  if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
  if true then y else z = y
  if false then y else z = z

  data Type : Set where
    nat : Type
    bool : Type

  Cxt = List Type

  data Expr (Γ : Cxt) : Type → Set where
    lit : (n : Nat) → Expr Γ nat
    true : Expr Γ bool
    false : Expr Γ bool
    less : (a b : Expr Γ nat) → Expr Γ bool
    plus : (a b : Expr Γ nat) → Expr Γ nat
    if   : ∀ {t} → (a : Expr Γ bool) (b c : Expr Γ t) → Expr Γ t

  Value : Type → Set
  Value nat = Nat
  Value bool = Bool

  eval : ∀ {Γ t} → Expr Γ t → Value t
  eval (lit n) = n
  eval true = true
  eval false = false
  eval (less e e₁) = eval e < eval e₁
  eval (plus e e₁) = eval e + eval e₁
  eval (if e e₁ e₂) = if eval e then eval e₁ else eval e₂
