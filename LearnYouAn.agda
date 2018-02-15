module LearnYouAn where


  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ


  _+_ : ℕ → ℕ → ℕ
  zero + m = m
  (suc n) + m = suc (n + m)

  data _even : ℕ → Set where
    ZERO : zero even
    STEP : ∀ {x} → x even → suc (suc x) even

  proof₁ : suc (suc (suc (suc zero))) even
  proof₁ = STEP (STEP ZERO)

  proof₂ : ℕ → ℕ
  proof₂ ν = ν

  proof₂' : (A : Set) → A → A
  proof₂' _ x = x

  proof₃ : ℕ → ℕ
  proof₃ = proof₂' ℕ
