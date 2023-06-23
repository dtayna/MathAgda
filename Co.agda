{-# OPTIONS --guardedness #-}

module Co where

open import Data.Nat
  renaming (zero to O; suc to S)

open import Data.Product
  renaming (proj₁ to outl; proj₂ to outr)
  hiding (zip; map)

open import Data.Sum
  renaming (inj₁ to inl; inj₂ to inr)
  hiding (map)

open import Data.Bool

open import Data.List
  using (List; [_]; []; _∷_)

----------------------------------------------------------------

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A

open Stream


map : {A B : Set} → (f : A → B) → Stream A → Stream B
hd (map f σ) = f (hd σ)
tl (map f σ) = map f (tl σ)

only : {A : Set} → (a : A) → Stream A
hd (only a) = a
tl (only a) = only a

genfibs : ℕ → ℕ → Stream ℕ
hd (genfibs n m) = {!   !}
tl (genfibs n m) = {!   !}

fibs : Stream ℕ
fibs = {!!}

lucs : Stream ℕ
lucs = {!!}

interleaved mutual

  evens : {A : Set} → Stream A → Stream A
  odds  : {A : Set} → Stream A → Stream A

  hd (evens σ) = hd σ
  tl (evens σ) = odds (tl σ)
  hd (odds σ) = hd (tl σ)
  tl (odds σ) = evens (tl  σ)

merge : {A : Set} → Stream A → Stream A → Stream A
hd (merge σ α) = hd σ
tl (merge σ α) = merge α (tl σ)

merge₃ : {A : Set} → Stream A → Stream A → Stream A → Stream A
hd (merge₃ α ϕ σ) = hd α
tl (merge₃ α ϕ σ) = merge₃ ϕ σ (tl α)

merge₂,₁ : {A : Set} → Stream A → Stream A → Stream A
merge₂,₁ ϕ σ = merge₃ (evens ϕ) (odds ϕ) σ

drop : {A : Set} → ℕ → Stream A → Stream A
hd (drop O σ) = hd σ
tl (drop O σ) = tl σ
hd (drop (S n) σ) = hd (drop n (tl σ))
tl (drop (S n) σ) = tl (drop n (tl σ))

takeList : {A : Set} → ℕ → Stream A → List A
takeList O σ  = []
takeList (S n) σ = (hd σ) ∷ (takeList n (tl σ))

zip : {A B : Set} → Stream A → Stream B → Stream (A × B)
hd (zip ϕ σ) = ( hd ϕ , hd σ )
tl (zip ϕ σ) = zip (tl ϕ)  (tl σ)

zipWith : {A B C : Set} → (f : A → B → C) → Stream A → Stream B → Stream C
hd (zipWith f ϕ σ) = f (hd ϕ) (hd σ)
tl (zipWith f ϕ σ) = zipWith f (tl ϕ) (tl σ)

takeStep : {A : Set} → ℕ → Stream A → Stream A
takeStep n σ = {!   !}

upFrom : ℕ → Stream ℕ
hd (upFrom n) = n
tl (upFrom n) = upFrom (S n)


downFrom : ℕ → Stream ℕ
hd (downFrom O) = 0
hd (downFrom (S n)) = (S n)
tl (downFrom O) = downFrom O
tl (downFrom (S n)) = downFrom n

preConcat : {A : Set} → ℕ → Stream A → Stream A → Stream A
preConcat O σ ϕ = ϕ
hd (preConcat (S n) σ ϕ) = hd σ
tl (preConcat (S n) σ ϕ) = preConcat n (tl σ) ϕ

insertAt : {A : Set} → ℕ → (w : A) → Stream A → Stream A
hd (insertAt O w σ) = w
tl (insertAt O w σ) = σ
hd (insertAt (S n) w σ) = hd σ
tl (insertAt (S n) w σ) = insertAt n w (tl σ)

 