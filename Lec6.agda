module Lec6 where

   data Expr : Set where
     t : Expr
     f : Expr
     z : Expr
     iz : Expr → Expr
     s  : Expr → Expr
     p  : Expr → Expr
     if_then_else_ : Expr → Expr → Expr → Expr

   data _→1_ : Expr → Expr → Set where
     izz : iz z →1 t
     izs : {e : Expr} → iz (s e) →1 f
     ift : {e₂ e₃ : Expr} → (if t then e₂ else e₃) →1 e₂
     iff : {e₂ e₃ : Expr} → (if f then e₂ else e₃) →1 e₃
     ps  : {e : Expr} → p (s e) →1 e
     pz  : p z →1 z

   data _↝_ : Expr → Expr → Set where
     from→1 : {e₁ e₂ : Expr} → (e₁ →1 e₂) → (e₁ ↝ e₂)
     inside-s : {e₁ e₂ : Expr} → (e₁ ↝ e₂) → (s e₁ ↝ s e₂)
     inside-p : {e₁ e₂ : Expr} → (e₁ ↝ e₂) → (p e₁ ↝ p e₂)
     inside-iz : ∀ {e₁} {e₂} → (e₁ ↝ e₂) → (iz e₁ ↝ iz e₂)
     inside-ite1 : ∀ {e₁ e₁' e₂ e₃} → (e₁ ↝ e₁')
       → (if e₁ then e₂ else e₃) ↝ (if e₁' then e₂ else e₃)
     inside-ite2 : ∀ {e₁ e₂ e₂' e₃} → (e₂ ↝ e₂')
       → (if e₁ then e₂ else e₃) ↝ (if e₁ then e₂' else e₃)
     inside-ite3 : ∀ {e₁ e₂ e₃ e₃'} → (e₃ ↝ e₃')
       → (if e₁ then e₂ else e₃) ↝ (if e₁ then e₂ else e₃')

   data _↝*_ : Expr → Expr → Set where
     start : ∀ {e} → e ↝* e
     step  : ∀ {e₁ e₂ e₃} → (e₁ ↝ e₂) → (e₂ ↝* e₃)
             → (e₁ ↝* e₃)

   compose : {e₁ e₂ e₃ : Expr} → (e₁ ↝* e₂)
             → (e₂ ↝* e₃)
             → (e₁ ↝* e₃)
   compose start s₂ = s₂
   compose (step x s₁) s₂ = step x (compose s₁ s₂)

   data ∅ : Set where

   is-normal : Expr → Set
   is-normal e = (e₁ : Expr) → (e →1 e₁) → ∅
