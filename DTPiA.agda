module DTPiA where
-- Exercises for:
-- Dependently Typed Programming in Agda

module AgdaBasics where
  data Bool : Set where
    true  : Bool
    false : Bool
  
  not : Bool → Bool
  not true  = false
  not false = true
  
  infixr 20 _or_
  _or_ : Bool → Bool → Bool
  false or x = x
  true  or _ = true
  
  infix 5 if_then_else_
  if_then_else_ : {A : Set} → Bool → A → A → A
  if true  then x else y = x
  if false then x else y = y
  
  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat
  
  infixl 40 _+_
  _+_ : Nat → Nat → Nat
  zero  + m = m
  suc n + m = suc (n + m)
  
  infixl 60 _*_
  _*_ : Nat → Nat → Nat
  zero  * m = zero
  suc n * m = m + (n * m)
  
  infixr 40 _::_
  data List (A : Set) : Set where
    []   : List A
    _::_ : A → List A → List A
  
  identity : (A : Set) → A → A
  identity A x = x
  
  zero' : Nat
  zero' = identity Nat zero
  
  apply : (A : Set)(B : A → Set) →
          ((x : A) → B x) → (a : A) → B a
  apply A B f a = f a
  
  identity₂ : (A : Set) → A → A
  identity₂ = \A x → x
  
  identity₃ : (A : Set) → A → A
  identity₃ = \(A : Set)(x : A) → x
  
  identity₄ : (A : Set) → A → A
  identity₄ = \(A : Set) x → x
  
  id : {A : Set} → A → A
  id x = x
  
  true' : Bool
  true' = id true
  
  silly : {A : Set}{x : A} → A
  silly {_}{x} = x
  
  false' : Bool
  false' = silly {x = false}
  
  one : Nat
  one = identity _ (suc zero)
  
  _∘_ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set}
        (f : {x : A}(y : B x) → C x y)(g : (x : A) → B x)
        (x : A) → C x (g x)
  (f ∘ g) x = f (g x)
  
  plus-two = suc ∘ suc
  
  map : {A B : Set} → (A → B) → List A → List B
  map f []        = []
  map f (x :: xs) = f x :: map f xs
  
  data Vec (A : Set) : Nat → Set where
    []   : Vec A zero
    _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)
  
  head : {A : Set}{n : Nat} → Vec A (suc n) → A
  head (x :: xs) = x
  
  vmap : {A B : Set}{n : Nat} → (A → B) → Vec A n → Vec B n
  vmap f []        = []
  vmap f (x :: xs) = f x :: vmap f xs
  
  data Vec₂ (A : Set) : Nat → Set where
    nil  : Vec₂ A zero
    cons : (n : Nat) → A → Vec₂ A n → Vec₂ A (suc n)
  
  vmap₂ : {A B : Set}(n : Nat) → (A → B) → Vec₂ A n → Vec₂ B n
  vmap₂ .zero    f nil           = nil
  vmap₂ .(suc n) f (cons n x xs) = cons n (f x) (vmap₂ n f xs)
  
  vmap₃ : {A B : Set}(n : Nat) → (A → B) → Vec₂ A n → Vec₂ B n
  vmap₃ zero    f nil            = nil
  vmap₃ (suc n) f (cons .n x xs) = cons n (f x) (vmap₃ n f xs)
  
  data Image_∋_ {A B : Set}(f : A → B) : B → Set where
    im : (x : A) → Image f ∋ f x
  
  inv : {A B : Set}(f : A → B)(y : B) → Image f ∋ y → A
  inv f .(f x) (im x) = x
  
  data Fin : Nat → Set where
    fzero : {n : Nat} → Fin (suc n)
    fsuc  : {n : Nat} → Fin n → Fin (suc n)
  
  magic : {A : Set} → Fin zero → A
  magic ()
  
  data Empty : Set where
    empty : Fin zero → Empty
  
  magic' : {A : Set} → Empty → A
  magic' (empty ())
  -- magic' () -- not accepted
  
  _!_ : {n : Nat}{A : Set} → Vec A n → Fin n → A
  []        ! ()
  (x :: xs) ! fzero    = x
  (x :: xs) ! (fsuc i) = xs ! i
  
  tabulate : {n : Nat}{A : Set} → (Fin n → A) → Vec A n
  tabulate {zero}  f = []
  tabulate {suc n} f = f fzero :: tabulate (f ∘ fsuc)
  
  data   False : Set where
  record True  : Set where
  
  trivial : True
  trivial = _
  
  isTrue : Bool → Set
  isTrue true  = True
  isTrue false = False
  
  _<_ : Nat → Nat → Bool
  _     < zero  = false
  zero  < suc n = true
  suc m < suc n = m < n
  
  length : {A : Set} → List A → Nat
  length []        = zero
  length (x :: xs) = suc (length xs)
  
  lookup : {A : Set}(xs : List A)(n : Nat) →
           isTrue (n < length xs) → A
  lookup []        n       ()
  lookup (x :: xs) zero    p = x
  lookup (x :: xs) (suc n) p = lookup xs n p
  
  data _==_ {A : Set}(x : A) : A → Set where
    refl : x == x
  
  data _≤_ : Nat → Nat → Set where
    leq-zero : {n : Nat} → zero ≤ n
    leq-suc  : {m n : Nat} → m ≤ n → suc m ≤ suc n
  
  leq-trans : {l m n : Nat} → l ≤ m → m ≤ n → l ≤ n
  leq-trans leq-zero    _           = leq-zero
  leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)
  
  min : Nat → Nat → Nat
  min x y with x < y
  min x y | true  = x
  min x y | false = y
  
  filter : {A : Set} → (A → Bool) → List A → List A
  filter p [] = []
  filter p (x :: xs) with p x
  ... | true  = x :: filter p xs
  ... | false = filter p xs
  
  data _≠_ : Nat → Nat → Set where
    z≠s : {n : Nat} → zero ≠ suc n
    s≠z : {n : Nat} → suc n ≠ zero
    s≠s : {m n : Nat} → m ≠ n → suc m ≠ suc n
  
  data Equal? (n m : Nat) : Set where
    eq  : n == m → Equal? n m
    neq : n ≠ m → Equal? n m
  
  equal? : (n m : Nat) → Equal? n m
  equal? zero   zero     = eq refl
  equal? zero    (suc m) = neq z≠s
  equal? (suc n) zero    = neq s≠z
  equal? (suc n) (suc m) with equal? n m
  equal? (suc n) (suc .n) | eq refl = eq refl
  equal? (suc n) (suc m)  | neq p   = neq (s≠s p)
  
  infix 20 _⊆_
  data _⊆_ {A : Set} : List A → List A → Set where
    stop : [] ⊆ []
    drop : ∀ {xs y ys} → xs ⊆ ys →      xs ⊆ y :: ys
    keep : ∀ {x xs ys} → xs ⊆ ys → x :: xs ⊆ x :: ys
  
  lem-filter : {A : Set}(p : A → Bool)(xs : List A) →
               filter p xs ⊆ xs
  lem-filter p []        = stop
  lem-filter p (x :: xs) with p x
  ... | true  = keep (lem-filter p xs)
  ... | false = drop (lem-filter p xs)
  
  lem-plus-zero : (n : Nat) → n + zero == n
  lem-plus-zero zero = refl
  lem-plus-zero (suc n) with n + zero | lem-plus-zero n
  ... | .n | refl = refl
  
  module M where
    data Maybe (A : Set) : Set where
      nothing : Maybe A
      just    : A → Maybe A
    maybe : {A B : Set} → B → (A → B) → Maybe A → B
    maybe z f nothing  = z
    maybe z f (just x) = f x
  
  module A where
    private
      internal : Nat
      internal = zero
  
    exported : Nat → Nat
    exported n = n + internal
  
  mapMaybe₁ : {A B : Set} → (A → B) → M.Maybe A → M.Maybe B
  mapMaybe₁ f M.nothing  = M.nothing
  mapMaybe₁ f (M.just x) = M.just (f x)
  
  mapMaybe₂ : {A B : Set} → (A → B) → M.Maybe A → M.Maybe B
  mapMaybe₂ f m = let open M in maybe nothing (just ∘ f) m
  
  open M
  
  mapMaybe₃ : {A B : Set} → (A → B) → Maybe A → Maybe B
  mapMaybe₃ f m = maybe nothing (just ∘ f) m
  
  open M hiding (maybe)
                renaming (Maybe to _option; nothing to none; just to some)
  
  mapOption : {A B : Set} → (A → B) → A option → B option
  mapOption f none     = none
  mapOption f (some x) = some (f x)
  
  mtrue : Maybe Bool
  mtrue = mapOption not (just false)
  
  module Sort (A : Set)(_<_ : A → A → Bool) where
    insert : A → List A → List A
    insert y [] = y :: []
    insert y (x :: xs) with x < y
    ... | true  = x :: insert y xs
    ... | false = y :: x :: xs
  
    sort : List A → List A
    sort []        = []
    sort (x :: xs) = insert x (sort xs)
  
  sort₁ : (A : Set)(_<_ : A → A → Bool) → List A → List A
  sort₁ = Sort.sort
  
  module SortNat = Sort Nat _<_
  
  sort₂ : List Nat → List Nat
  sort₂ = SortNat.sort
  
  open Sort Nat _<_ renaming (insert to insertNat; sort to sortNat)
  
  module Lists (A : Set)(_<_ : A → A → Bool) where
    open Sort A _<_ public
    minimum : List A → Maybe A
    minimum xs with sort xs
    ... | []      = nothing
    ... | y :: ys = just y
  
  record Point : Set where
    field x : Nat
          y : Nat
  
  mkPoint : Nat → Nat → Point
  mkPoint a b = record{ x = a; y = b }
  
  getX : Point → Nat
  getX = Point.x
  
  abs² : Point → Nat
  abs² p = let open Point p in x * x + y * y
  
  record Monad (M : Set → Set) : Set1 where
    field
      return : {A : Set} → A → M A
      _>>=_  : {A B : Set} → M A → (A → M B) → M B
  
    mapM : {A B : Set} → (A → M B) → List A → M (List B)
    mapM f [] = return []
    mapM f (x :: xs) = f x       >>= \y  →
                       mapM f xs >>= \ys →
                       return (y :: ys)
  
  mapM' : {M : Set → Set} → Monad M →
          {A B : Set} → (A → M B) → List A → M (List B)
  mapM' Mon f xs = Monad.mapM Mon f xs
  
  -- Extra functions
  
  tail : {A : Set}{n : Nat} → Vec A (suc n) → Vec A n
  tail (x :: xs) = xs
  
  
  -- 2.9 Exercises
  -- Ex 2.1 Matrix Transposition
  -- We can model an *n × m* matrix as a vector of vectors:
  
  Matrix : Set → Nat → Nat → Set
  Matrix A n m = Vec (Vec A n) m
  
  -- (a) Define a function to compute a vector containing *n* copies of an
  --     element *x*.
  
  vec : {n : Nat}{A : Set} → A → Vec A n
  vec {zero}  x = []
  vec {suc n} x = x :: vec x
  
  -- (b) Define point-wise application of a vector of function to a vector
  --     of arguments.
  
  infixl 90 _$_
  _$_ : {n : Nat}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
  [] $ [] = []
  (f :: fs) $ (x :: xs) = f x :: fs $ xs
  
  -- (c) Define matrix transposition in terms of these two functions.
  transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
  transpose {_}{zero}{zero} xss = []
  transpose {_}{zero}{_} xss = []
  transpose {_}{_}{zero} xss = vec []
  transpose {_}{suc n}{suc m} xss = vec head $ xss :: transpose (vec tail $ xss)
  
  
  
  -- Ex 2.2 Vector Lookup
  -- Remember tabulate and _!_ from Section 2.4. Prove that they are
  -- indeed each other's inverses.
  
  -- (a) ← This direction should be relatively easy.
  
  lem-!-tab : ∀ {A n} (f : Fin n → A)(i : Fin n) → (tabulate f ! i) == f i
  lem-!-tab f fzero = refl
  lem-!-tab f (fsuc i) = lem-!-tab (f ∘ fsuc) i
  
  -- (b) → This direction might be trickier.
  
  lem-tab-! : ∀ {A n} (xs : Vec A n) → tabulate (_!_ xs) == xs
  lem-tab-! [] = refl
  lem-tab-! (x :: xs) with tabulate (_!_ xs) | lem-tab-! xs
  lem-tab-! (x :: xs) | .xs | refl = refl
  
  
  
  -- Ex 2.3 Sublists
  -- Remember the representation of sublists from Section 2.4:
  -- data _⊆_ {A : Set} : List A → List A → Set where
  --     stop : [] ⊆ []
  --     drop : ∀ {x xs ys} → xs ⊆ ys →      xs ⊆ x :: ys
  --     keep : ∀ {x xs ys} → xs ⊆ ys → x :: xs ⊆ x :: ys
  
  -- (a) Prove the reflexivity and transitivity of _⊆_:
  
  ⊆-refl : {A : Set}{xs : List A} → xs ⊆ xs
  ⊆-refl {xs = []} = stop
  ⊆-refl {xs = x :: xs} = keep ⊆-refl
  
  ⊆-trans : {A : Set}{xs ys zs : List A} →
            xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
  ⊆-trans p stop = p
  ⊆-trans p (drop q) = drop (⊆-trans p q)
  ⊆-trans (drop p) (keep q) = drop (⊆-trans p q)
  ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
  
  -- Instead of defining the sublist relation we can define the type of sublists
  -- of a given list as follows:
  
  data SubList {A : Set} : List A → Set where
    []   : SubList []
    _::_ : ∀ x {xs} → SubList xs → SubList (x :: xs)
    skip : ∀ {x xs} → SubList xs → SubList (x :: xs)
  
  -- (b) Define a function to extract the list corresponding to a sublist.
  
  forget : {A : Set}{xs : List A} → SubList xs → List A
  forget {xs = xs} _ = xs
  
  -- (c) Now, prove that a SubList is a sublist in the sense of _⊆_.
  
  lem-forget : {A : Set}{xs : List A}(zs : SubList xs) → forget zs ⊆ xs
  lem-forget [] = stop
  lem-forget (x :: zs) = keep (lem-forget zs)
  lem-forget (skip zs) = keep (lem-forget zs)
  
  -- (d) Give an alternative definition of filter which satisfies the sublist
  --     property by construction.
  
  filter' : {A : Set} → (A → Bool) → (xs : List A) → SubList xs
  filter' p [] = []
  filter' p (x :: xs) with p x
  ... | true  = x :: filter' p xs
  ... | false = skip (filter' p xs)
  
  -- (e) Define the complement of a sublist
  
  complement : {A : Set}{xs : List A} → SubList xs → SubList xs
  complement [] = []
  complement (x :: zs) = skip (complement zs)
  complement (skip {x = x} zs) = x :: (complement zs)
  
  -- (f) Compute all sublists of a given list
  
  sublists : {A : Set}(xs : List A) → List (SubList xs)
  sublists [] = []
  sublists (x :: xs) = map skip sxs ++ map (_::_ x) sxs
           where
             sxs = sublists xs
             _++_ : {A : Set} → List A → List A → List A
             [] ++ bs = bs
             (a :: as) ++ bs = a :: (as ++ bs)

module Views where
  open import Data.Nat renaming (ℕ to Nat)

  data Parity : Nat → Set where
    even : (k : Nat) → Parity (k * 2)
    odd  : (k : Nat) → Parity (1 + k * 2)

  parity : (n : Nat) → Parity n
  parity zero = even zero
  parity (suc n) with parity n
  parity (suc .(k * 2))     | even k = odd k
  parity (suc .(1 + k * 2)) | odd  k = even (suc k)

  half : Nat -> Nat
  half n with parity n
  half .(k * 2)     | even k = k
  half .(1 + k * 2) | odd k  = k

  open import Function hiding (_$_)
  open import Data.List
  open import Data.Bool renaming (T to isTrue)

  infixr 30 _:all:_
  data All {A : Set}(P : A → Set) : List A → Set where
    all[]   : All P []
    _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

  satisfies : {A : Set} → (A → Bool) → A → Set
  satisfies p x = isTrue (p x)

  data Find {A : Set}(p : A → Bool) : List A → Set where
    found : (xs : List A)(y : A) → satisfies p y → (ys : List A) →
            Find p (xs ++ y ∷ ys)
    not-found : ∀ {xs} → All (satisfies (not ∘ p)) xs →
                Find p xs

  find₁ : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
  find₁ p [] = not-found all[]
  find₁ p (x ∷ xs) with p x
  ... | true  = found [] x {!!} xs
  ... | false = {!!}

  data _==_ {A : Set}(x : A) : A → Set where
    refl : x == x

  data Inspect {A : Set}(x : A) : Set where
    it : (y : A) → x == y → Inspect x

  inspect : {A : Set}(x : A) → Inspect x
  inspect x = it x refl

  trueIsTrue : {x : Bool} → x == true → isTrue x
  trueIsTrue refl = _

  isFalse : Bool → Set
  isFalse = isTrue ∘ not
  falseIsFalse : {x : Bool} → x == false → isFalse x
  falseIsFalse refl = _

  find : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
  find p [] = not-found all[]
  find p (x ∷ xs) with inspect (p x)
  ... | it true prf = found [] x (trueIsTrue prf) xs
  ... | it false prf with find p xs
  find p (x ∷ ._) | it false _   | found xs y py ys =
    found (x ∷ xs) y py ys
  find p (x ∷ xs) | it false prf | not-found npxs =
    not-found (falseIsFalse prf :all: npxs)

  data _∈_ {A : Set}(x : A) : List A → Set where
    hd : ∀ {xs}   → x ∈ (x ∷ xs)
    tl : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

  index : ∀ {A}{x : A}{xs} → x ∈ xs → Nat
  index hd    = zero
  index (tl p) = suc (index p)

  data Lookup {A : Set}(xs : List A) : Nat → Set where
    inside  : (x : A)(p : x ∈ xs) → Lookup xs (index p)
    outside : (m : Nat) → Lookup xs (length xs + m)

  _!_ : {A : Set}(xs : List A)(n : Nat) → Lookup xs n
  [] ! n = outside n
  (x ∷ xs) ! zero  = inside x hd
  (x ∷ xs) ! suc n with xs ! n
  (x ∷ xs) ! suc .(index p)       | inside y p = inside y (tl p)
  (x ∷ xs) ! suc .(length xs + n) | outside n = outside n

  infixr 30 _⇒_
  data Type : Set where
    ı   : Type
    _⇒_ : Type → Type → Type

  data Equal? : Type → Type → Set where
    yes : ∀ {τ} → Equal? τ τ
    no  : ∀ {σ τ} → Equal? σ τ

  _=?=_ : (σ τ : Type) → Equal? σ τ
  ı         =?= ı       = yes
  ı         =?= (_ ⇒ _) = no
  (_ ⇒ _)   =?= ı       = no
  (σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
  (σ ⇒ τ)   =?= (.σ ⇒ .τ) | yes | yes = yes
  (σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) | _   | _   = no

  infixl 80 _$_
  data Raw : Set where
    var : Nat → Raw
    _$_ : Raw → Raw → Raw
    lam : Type → Raw → Raw

  Cxt = List Type

  data Term (Γ : Cxt) : Type → Set where
    var : ∀ {τ} → τ ∈ Γ → Term Γ τ
    _$_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
    lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

  erase : ∀ {Γ τ} → Term Γ τ → Raw
  erase (var x)   = var (index x)
  erase (t $ u)   = erase t $ erase u
  erase (lam σ t) = lam σ (erase t)

  data Infer (Γ : Cxt) : Raw → Set where
    ok  : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
    bad : {e : Raw} → Infer Γ e

  infer : (Γ : Cxt)(e : Raw) → Infer Γ e
  infer Γ (var n)   with Γ ! n
  infer Γ (var .(length Γ + n)) | outside n  = bad
  infer Γ (var .(index x))      | inside σ x = ok σ (var x)

  infer Γ (e₁ $ e₂)                   with infer Γ e₁
  infer Γ (e₁ $ e₂)                   | bad     = bad
  infer Γ (.(erase t₁) $ e₂)          | ok ı t₁ = bad
  infer Γ (.(erase t₁) $ e₂)          | ok (σ ⇒ τ) t₁
        with infer Γ e₂
  infer Γ (.(erase t₁) $ e₂)          | ok (σ ⇒ τ) t₁
        | bad = bad
  infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁
        | ok σ′ t₂ with σ =?= σ′
  infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁
        | ok .σ t₂ | yes = ok τ (t₁ $ t₂)
  infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁
        | ok σ′ t₂ | no = bad

  infer Γ (lam σ e) with infer (σ ∷ Γ) e
  infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
  infer Γ (lam σ e)          | bad    = bad



module Universes where
  data   False : Set where
  record True  : Set where

  data Bool : Set where
    true  : Bool
    false : Bool

  isTrue : Bool → Set
  isTrue true  = True
  isTrue false = False

  infix  30 not_
  infixr 25 _and_

  not_ : Bool → Bool
  not true  = false
  not false = true

  _and_ : Bool → Bool → Bool
  true  and x = x
  false and _ = false

  notNotId : (a : Bool) → isTrue (not not a) → isTrue a
  notNotId true  p = p
  notNotId false ()

  andIntro : (a b : Bool) → isTrue a → isTrue b → isTrue (a and b)
  andIntro true  _ _  p = p
  andIntro false _ () _

  open import Data.Nat hiding (fold) renaming (ℕ to Nat)
  
  nonZero : Nat → Bool
  nonZero zero    = false
  nonZero (suc _) = true

  postulate _div_ : Nat → (m : Nat){p : isTrue (nonZero m)} → Nat

  three = 16 div 5

  data Functor : Set1 where
    |Id|  : Functor
    |K|   : Set → Functor
    _|+|_ : Functor → Functor → Functor
    _|x|_ : Functor → Functor → Functor

  data _⊕_ (A B : Set) : Set where
    inl : A → A ⊕ B
    inr : B → A ⊕ B

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  infixr 50 _|+|_ _⊕_
  infixr 60 _|x|_ _×_

  [_] : Functor → Set → Set
  [ |Id|    ] X = X
  [ |K| A   ] X = A
  [ F |+| G ] X = [ F ] X ⊕ [ G ] X
  [ F |x| G ] X = [ F ] X × [ G ] X

  map : (F : Functor){X Y : Set} → (X → Y) → [ F ] X → [ F ] Y
  map |Id|      f x       = f x
  map (|K| A)   f c       = c
  map (F |+| G) f (inl x) = inl (map F f x)
  map (F |+| G) f (inr y) = inr (map G f y)
  map (F |x| G) f (x , y) = map F f x , map G f y

  data μ_ (F : Functor) : Set where
    <_> : [ F ] (μ F) → μ F

  -- Doesn't terminate (salmon color)
  -- fold : (F : Functor){A : Set} → ([ F ] A → A) → μ F → A
  -- fold F φ < x > = φ (map F (fold F φ) x)

  mapFold : ∀ {X} F G → ([ G ] X → X) → [ F ] (μ G) → [ F ] X
  mapFold |Id|        G φ < x >   = φ (mapFold G G φ x)
  mapFold (|K| A)     G φ c       = c
  mapFold (F₁ |+| F₂) G φ (inl x) = inl (mapFold F₁ G φ x)
  mapFold (F₁ |+| F₂) G φ (inr y) = inr (mapFold F₂ G φ y)
  mapFold (F₁ |x| F₂) G φ (x , y) = mapFold F₁ G φ x , mapFold F₂ G φ y

  fold : {F : Functor}{A : Set} → ([ F ] A → A) → μ F → A
  fold {F} φ < x > = φ (mapFold F F φ x)

  NatF = |K| True |+| |Id|
  NAT  = μ NatF

  Z : NAT
  Z = < inl _ >

  S : NAT → NAT
  S n = < inr n >

  ListF = \A → |K| True |+| |K| A |x| |Id|
  LIST  = \A → μ (ListF A)
  
  nil : {A : Set} → LIST A
  nil = < inl _ >

  cons : {A : Set} → A → LIST A → LIST A
  cons x xs = < inr (x , xs) >

  [_||_] : {A B C : Set} → (A → C) → (B → C) → A ⊕ B → C
  [ f || g ] (inl x) = f x
  [ f || g ] (inr y) = g y

  uncurry : {A B C : Set} → (A → B → C) → A × B → C
  uncurry f (x , y) = f x y

  const : {A B : Set} → A → B → A
  const x y = x

  foldr : {A B : Set} → (A → B → B) → B → LIST A → B
  foldr {A}{B} f z = fold [ const z || uncurry f ]

  plus : NAT → NAT → NAT
  plus n m = fold [ const m || S ] n

  open import Data.List

  data Type : Set where
    bool : Type
    nat  : Type
    list : Type → Type
    pair : Type → Type → Type

  El : Type → Set
  El nat        = Nat
  El bool       = Bool
  El (list a)   = List (El a)
  El (pair a b) = El a × El b

  infix 30 _==_
  _==_ : {a : Type} → El a → El a → Bool

  _==_ {nat} zero    zero    = true
  _==_ {nat} (suc _) zero    = false
  _==_ {nat} zero    (suc _) = false
  _==_ {nat} (suc n) (suc m) = n == m

  _==_ {bool} true  x = x
  _==_ {bool} false x = not x

  _==_ {list a} [] []      = true
  _==_ {list a} (_ ∷ _) [] = false
  _==_ {list a} [] (_ ∷ _) = false
  _==_ {list a} (x ∷ xs) (y ∷ ys) = x == y and xs == ys

  
  _==_ {pair a b} (x₁ , y₁) (x₂ , y₂) = x₁ == x₂ and y₁ == y₂

  example₁ : isTrue ((2 + 2) == 4)
  example₁ = _

  example₂ : isTrue (not ((true ∷ false ∷ []) == (true ∷ true ∷ [])))
  example₂ = _
