{- Module: Leios.Base.Praos.BlockTree

   A block tree for the Praos node whose chain selection is incremental, for
   chains of node-log size, with the 'Protocol.Tree' laws proved.

   Every block of the pool has an entry with the longest valid chain the
   pool holds that ends in it, if there is one.  A block that comes in with
   a slot no lower than any block before it ('top') extends the longest
   chain of a parent: no chain of an earlier block can pass through it,
   since the slots of a valid chain fall strictly towards genesis, so no
   earlier entry changes.  The tree also keeps the longest chain of all,
   which answers every query at or past 'top' at once.  A block that comes
   in out of order makes the tree rebuild its entries from the pool in slot
   order; the converters deliver blocks in order, so that is rare.

   Of equally long chains the tree takes the one whose tip it adopted last,
   since the node adopts blocks in the order it selects them.  Every entry
   records the adoption number of its block, so a rebuild in slot order
   still breaks ties by adoption.

   The chains of the entries share their tails, so an entry costs one cell.
   The invariant 'Inv' travels with the tree; the laws follow from it.
-}

open import Protocol.Prelude
open import Protocol.Params using (Params)
open import Protocol.Crypto using (Hashable)
open import Protocol.Block using (Block)

module Leios.Base.Praos.BlockTree
  ⦃ params : _ ⦄ (open Params params)
  ⦃ _ : Hashable Block ⦄
  ⦃ _ : Default Block ⦄
  where

open import Protocol.BaseTypes using (Slot)
open import Protocol.Block ⦃ params ⦄ hiding (Block)
open import Protocol.Chain ⦃ params ⦄
open import Protocol.Tree ⦃ params ⦄
open Hashable ⦃ ... ⦄ using (hash)

open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; <⇒≤; <-irrefl; ≤-<-trans; <-≤-trans; n≮0)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ⊆×⊇⇒≡ˢ)
import Data.List.Relation.Unary.Linked as Lkd

open import Leios.Base.Praos.ListLemmas using (module MaxBy; module SortDesc)

------------------------------------------------------------------------------
-- Valid chains

opaque
  unfolding _✓

  -- A valid chain is not empty, so it has a block at its tip.
  ✓-tip∈ : ∀ {c} → c ✓ → tip c ∈ c
  ✓-tip∈ {_ ∷ _} _ = here refl

  ✓-single : ∀ {b} → [ b ] ✓ → b ≡ genesisBlock
  ✓-single (_ , pl , _) = pl

  ✓-uncons : ∀ {b b′ c} → (b ∷ b′ ∷ c) ✓
           → CorrectBlock b × b ⟵ b′ × b′ .slot < b .slot × (b′ ∷ c) ✓
  ✓-uncons (cb ∷ cbs , (lk , pl) , (lt Lkd.∷ ds)) = cb , lk , lt , (cbs , pl , ds)

  ✓-cons : ∀ {b c} → CorrectBlock b → b ⟵ tip c → tip c .slot < b .slot → c ✓ → (b ∷ c) ✓
  ✓-cons {c = _ ∷ _} cb lk lt (cbs , pl , ds) = cb ∷ cbs , (lk , pl) , (lt Lkd.∷ ds)

  -- Every block of a valid chain is its tip or lies in an earlier slot.
  ✓-below : ∀ {c x} → c ✓ → x ∈ c → x ≡ tip c ⊎ x .slot < tip c .slot
  ✓-below {_ ∷ _} _ (here refl) = inj₁ refl
  ✓-below {b ∷ c} (_ , _ , ds) (there x∈) = inj₂ (go ds x∈)
    where
      go : ∀ {b c x} → Lkd.Linked _>ˢ_ (b ∷ c) → x ∈ c → x .slot < b .slot
      go (lt Lkd.∷ _)  (here refl) = lt
      go (lt Lkd.∷ ds) (there x∈)  = <-trans (go ds x∈) lt
        where open import Data.Nat.Properties using (<-trans)

✓-slot≤ : ∀ {c x} → c ✓ → x ∈ c → x .slot ≤ tip c .slot
✓-slot≤ c✓ x∈ with ✓-below c✓ x∈
... | inj₁ refl = ≤-refl
... | inj₂ lt   = <⇒≤ lt

------------------------------------------------------------------------------
-- The tree, given that genesis is a valid chain of slot 0

module _
  (gb-correct : CorrectBlock genesisBlock)
  (gb-slot    : genesisBlock .slot ≡ 0)
  where

  opaque
    unfolding _✓

    gb✓ : [ genesisBlock ] ✓
    gb✓ = gb-correct ∷ [] , refl , Lkd.[-]

  -- No valid chain within genesis alone is longer than genesis.
  only-genesis : ∀ {c} → c ✓ → c ⊆ˢ [ genesisBlock ] → length c ≤ 1
  only-genesis {[]}         _  _ = z≤n
  only-genesis {_ ∷ []}     _  _ = s≤s z≤n
  only-genesis {b ∷ b′ ∷ c} c✓ c⊆ with ✓-uncons c✓ | c⊆ (here refl) | c⊆ (there (here refl))
  ... | _ , _ , lt , _ | here refl | here refl = contradiction lt (<-irrefl refl)

  ----------------------------------------------------------------------------
  -- Entries and the invariant

  lenM : Maybe Chain → ℕ
  lenM nothing  = 0
  lenM (just c) = length c

  record Entry : Type where
    constructor ⟪_,_,_⟫
    field blk     : Block
          chainOf : Maybe Chain
          -- the adoption number of 'blk': the k-th block added has k
          seq     : ℕ

  open Entry public

  -- What an entry's chain is: valid, ending in the entry's block, within the
  -- pool.
  Sound : List Block → Block → Maybe Chain → Type
  Sound P b nothing  = ⊤
  Sound P b (just c) = c ✓ × tip c ≡ b × c ⊆ˢ P

  -- And no valid chain within the pool that ends in the block is longer.
  Longest : List Block → Block → Maybe Chain → Type
  Longest P b m = ∀ c → c ✓ → tip c ≡ b → c ⊆ˢ P → length c ≤ lenM m

  record Inv (P : List Block) (es : List Entry) (top : Slot) (bc : Chain) : Type where
    field
      inPool  : ∀ {e} → e ∈ es → blk e ∈ P
      covers  : ∀ {b} → b ∈ P → ∃[ e ] e ∈ es × blk e ≡ b
      sound   : ∀ {e} → e ∈ es → Sound P (blk e) (chainOf e)
      longest : ∀ {e} → e ∈ es → Longest P (blk e) (chainOf e)
      below   : ∀ {b} → b ∈ P → b .slot ≤ top
      bc✓     : bc ✓
      bc⊆     : bc ⊆ˢ P
      bc≥     : ∀ {e} → e ∈ es → lenM (chainOf e) ≤ length bc

  record TreeImpl : Type where
    constructor mkTree
    field
      -- the blocks added, latest first; the pool is genesis and these
      blocks  : List Block
      entries : List Entry
      -- the highest slot in the pool
      top     : Slot
      -- the longest chain of all entries, with the adoption number of its
      -- tip
      best    : ℕ × Chain
      inv     : Inv (genesisBlock ∷ blocks) entries top (proj₂ best)

  open TreeImpl

  bestC : TreeImpl → Chain
  bestC = proj₂ ∘ best

  pool : TreeImpl → List Block
  pool t = genesisBlock ∷ blocks t

  ----------------------------------------------------------------------------
  -- The empty tree

  opaque
    unfolding gb✓

    inv₀ : Inv [ genesisBlock ] [ ⟪ genesisBlock , just [ genesisBlock ] , 0 ⟫ ] 0 [ genesisBlock ]
    inv₀ = record
      { inPool  = λ where (here refl) → here refl
      ; covers  = λ where (here refl) → _ , here refl , refl
      ; sound   = λ where (here refl) → gb✓ , refl , id
      ; longest = λ where (here refl) c c✓ _ c⊆ → only-genesis c✓ c⊆
      ; below   = λ where (here refl) → subst (_≤ 0) (sym gb-slot) ≤-refl
      ; bc✓     = gb✓
      ; bc⊆     = id
      ; bc≥     = λ where (here refl) → ≤-refl
      }

  tree₀′ : TreeImpl
  tree₀′ = mkTree [] [ ⟪ genesisBlock , just [ genesisBlock ] , 0 ⟫ ] 0 (0 , [ genesisBlock ]) inv₀

  ----------------------------------------------------------------------------
  -- Adding a block in slot order

  -- Parent chains have no tie-break; best chains break ties by adoption.
  open MaxBy {B = Chain} length (λ _ → 0)
  module Latest = MaxBy {B = ℕ × Chain} (length ∘ proj₂) proj₁

  -- The chains of the entries that can be the parent of 'b': their block is
  -- the one 'b' points to, in an earlier slot.
  parents : Block → List Entry → List Chain
  parents b [] = []
  parents b (e ∷ es) with b .prev ≟ hash (blk e) | blk e .slot <? b .slot | chainOf e
  ... | yes _ | yes _ | just c = c ∷ parents b es
  ... | _     | _     | _      = parents b es

  parents-sound : ∀ {b c} es → c ∈ parents b es
                → ∃[ e ] e ∈ es × chainOf e ≡ just c × b ⟵ blk e × blk e .slot < b .slot
  parents-sound {b} (e ∷ es) c∈ with b .prev ≟ hash (blk e) | blk e .slot <? b .slot | chainOf e in eq
  ... | yes lk | yes lt | just c′ with c∈
  ...   | here refl = e , here refl , eq , lk , lt
  ...   | there c∈′ = let (e′ , e∈ , rest) = parents-sound es c∈′ in e′ , there e∈ , rest
  parents-sound (e ∷ es) c∈ | yes _ | no _  | _ = let (e′ , e∈ , rest) = parents-sound es c∈ in e′ , there e∈ , rest
  parents-sound (e ∷ es) c∈ | no _  | _     | _ = let (e′ , e∈ , rest) = parents-sound es c∈ in e′ , there e∈ , rest
  parents-sound (e ∷ es) c∈ | yes _ | yes _ | nothing = let (e′ , e∈ , rest) = parents-sound es c∈ in e′ , there e∈ , rest

  parents-complete : ∀ {b e c} es → e ∈ es → chainOf e ≡ just c → b ⟵ blk e → blk e .slot < b .slot
                   → c ∈ parents b es
  parents-complete {b} (e ∷ es) e∈ eq lk lt
    with b .prev ≟ hash (blk e) | blk e .slot <? b .slot | chainOf e in eq′ | e∈
  ... | yes _ | yes _ | just _  | here refl with refl ← trans (sym eq′) eq = here refl
  ... | yes _ | yes _ | just _  | there e∈′ = there (parents-complete es e∈′ eq lk lt)
  ... | no ¬lk | _    | _       | here refl = contradiction lk ¬lk
  ... | no _  | _     | _       | there e∈′ = parents-complete es e∈′ eq lk lt
  ... | yes _ | no ¬lt | _      | here refl = contradiction lt ¬lt
  ... | yes _ | no _  | _       | there e∈′ = parents-complete es e∈′ eq lk lt
  ... | yes _ | yes _ | nothing | here refl with () ← trans (sym eq′) eq
  ... | yes _ | yes _ | nothing | there e∈′ = parents-complete es e∈′ eq lk lt

  -- The longest of the candidate parent chains, extended by 'b'.
  extendWith : Block → List Chain → Maybe Chain
  extendWith b []       = nothing
  extendWith b (c ∷ cs) = just (b ∷ maxBy c cs)

  extendWith-mem : ∀ {b c} cs → extendWith b cs ≡ just c → ∃[ m ] m ∈ cs × c ≡ b ∷ m
  extendWith-mem (c₀ ∷ cs) refl with maxBy-mem c₀ cs
  ... | inj₁ eq = _ , here eq , refl
  ... | inj₂ m∈ = _ , there m∈ , refl

  extendWith-len : ∀ {b m} cs → m ∈ cs → suc (length m) ≤ lenM (extendWith b cs)
  extendWith-len (c₀ ∷ cs) (here refl) = s≤s (maxBy-base c₀ cs)
  extendWith-len (c₀ ∷ cs) (there m∈)  = s≤s (maxBy-≥ c₀ cs m∈)

  -- The chain of a new block 'b': genesis is its own chain, any other block
  -- extends the longest chain of a parent, if it is a correct block.
  chainFor : Block → List Entry → Maybe Chain
  chainFor b es with b ≟ genesisBlock | ¿ CorrectBlock b ¿
  ... | yes _ | _     = just [ genesisBlock ]
  ... | no _  | yes _ = extendWith b (parents b es)
  ... | no _  | no _  = nothing

  -- The longer of the best chain so far and the chain of a new block 'b'
  -- with adoption number 'n'; of equally long ones, the one adopted last.
  -- A node adopts the blocks it is given in the order it selects them, so
  -- of equally long chains the latest is its tip.
  pick : ℕ × Chain → ℕ → Maybe Chain → ℕ × Chain
  pick bp n nothing  = bp
  pick bp n (just c) = Latest.maxBy bp [ (n , c) ]

  pick-mem : ∀ bp n m → proj₂ (pick bp n m) ≡ proj₂ bp ⊎ m ≡ just (proj₂ (pick bp n m))
  pick-mem bp n nothing  = inj₁ refl
  pick-mem bp n (just c) with Latest.maxBy-mem bp [ (n , c) ]
  ... | inj₁ eq        = inj₁ (cong proj₂ eq)
  ... | inj₂ (here eq) = inj₂ (cong just (sym (cong proj₂ eq)))

  pick-≥bc : ∀ bp n m → length (proj₂ bp) ≤ length (proj₂ (pick bp n m))
  pick-≥bc bp n nothing  = ≤-refl
  pick-≥bc bp n (just c) = Latest.maxBy-base bp [ (n , c) ]

  pick-≥m : ∀ bp n m → lenM m ≤ length (proj₂ (pick bp n m))
  pick-≥m bp n nothing  = z≤n
  pick-≥m bp n (just c) = Latest.maxBy-≥ bp [ (n , c) ] (here refl)

  -- Adding 'b', with adoption number 'n', to the pool 'genesis ∷ bs', at or
  -- past every slot in it.
  module Insert {bs es top} {bp : ℕ × Chain} (b : Block) (n : ℕ) (top≤ : top ≤ b .slot)
                (I : Inv (genesisBlock ∷ bs) es top (proj₂ bp)) where

    open Inv I

    bc : Chain
    bc = proj₂ bp

    P P′ : List Block
    P  = genesisBlock ∷ bs
    P′ = genesisBlock ∷ b ∷ bs

    split : ∀ {x} → x ∈ P′ → x ≡ b ⊎ x ∈ P
    split (here refl)         = inj₂ (here refl)
    split (there (here refl)) = inj₁ refl
    split (there (there q))   = inj₂ (there q)

    widen : ∀ {x} → x ∈ P → x ∈ P′
    widen (here refl) = here refl
    widen (there q)   = there (there q)

    m : Maybe Chain
    m = chainFor b es

    soundW : ∀ {x n} → Sound P x n → Sound P′ x n
    soundW {n = nothing} _               = tt
    soundW {n = just _}  (c✓ , tc , c⊆) = c✓ , tc , widen ∘ c⊆

    sound-new : Sound P′ b m
    sound-new with b ≟ genesisBlock | ¿ CorrectBlock b ¿
    ... | yes refl | _ = gb✓ , refl , λ where (here refl) → here refl
    ... | no _ | no _  = tt
    ... | no _ | yes cb with parents b es in eqp
    ...   | []      = tt
    ...   | c₀ ∷ cs with extendWith-mem {b} (c₀ ∷ cs) refl
    ...     | m′ , m∈ , refl with parents-sound es (subst (m′ ∈_) (sym eqp) m∈)
    ...       | e , e∈ , eq , lk , lt with subst (Sound P (blk e)) eq (sound e∈)
    ...         | m✓ , refl , m⊆ =
                  ✓-cons cb lk lt m✓
                , refl
                , λ where (here refl) → there (here refl)
                          (there x∈)  → widen (m⊆ x∈)

    -- A chain within the new pool that ends before 'b' does not hold 'b'.
    narrow : ∀ {c} → c ✓ → tip c ∈ P → tip c .slot < b .slot ⊎ tip c .slot ≤ top
           → c ⊆ˢ P′ → c ⊆ˢ P
    narrow {c} c✓ t∈ bound c⊆ {x} x∈ with split (c⊆ x∈)
    ... | inj₂ q    = q
    ... | inj₁ refl with ✓-below c✓ x∈
    ...   | inj₁ eq = subst (_∈ P) (sym eq) t∈
    ...   | inj₂ lt with bound
    ...     | inj₁ lt′ = contradiction (<-trans lt lt′) (<-irrefl refl)
      where open import Data.Nat.Properties using (<-trans)
    ...     | inj₂ ≤t  = contradiction (<-≤-trans lt (≤-trans ≤t top≤)) (<-irrefl refl)

    longest-new : Longest P′ b m
    longest-new []           c✓ _    _  with () ← ✓-tip∈ c✓
    longest-new (b₀ ∷ [])    c✓ refl _  with ✓-single c✓
    ... | refl with b ≟ genesisBlock
    ...   | yes refl = ≤-refl
    ...   | no ¬g    = contradiction refl ¬g
    longest-new (b₀ ∷ b′ ∷ rest) c✓ refl c⊆ with ✓-uncons c✓
    ... | cb , lk , lt , tl✓ =
      let tl⊆ = narrow tl✓ (b′∈) (inj₁ lt) (c⊆ ∘ there)
          (e , e∈ , be) = covers (tl⊆ (here refl))
          lenTl = longest e∈ (b′ ∷ rest) tl✓ (sym be) tl⊆
      in go e e∈ be lenTl
      where
        b′∈ : b′ ∈ P
        b′∈ with split (c⊆ (there (here refl)))
        ... | inj₂ q    = q
        ... | inj₁ refl = contradiction lt (<-irrefl refl)

        go : ∀ e → e ∈ es → blk e ≡ b′ → length (b′ ∷ rest) ≤ lenM (chainOf e)
           → length (b₀ ∷ b′ ∷ rest) ≤ lenM m
        go e e∈ refl lenTl with chainOf e in eq
        ... | nothing with () ← lenTl
        ... | just c″ with b ≟ genesisBlock | ¿ CorrectBlock b ¿
        ...   | yes refl | _ = contradiction (subst (b′ .slot <_) gb-slot lt) n≮0
        ...   | no _ | no ¬cb = contradiction cb ¬cb
        ...   | no _ | yes _ =
                ≤-trans (s≤s lenTl)
                        (extendWith-len (parents b es) (parents-complete es e∈ eq lk lt))

    longest-old : ∀ {e} → e ∈ es → Longest P′ (blk e) (chainOf e)
    longest-old e∈ c c✓ tc c⊆ =
      longest e∈ c c✓ tc (narrow c✓ (subst (_∈ P) (sym tc) (inPool e∈))
                                    (inj₂ (subst (λ y → y .slot ≤ top) (sym tc) (below (inPool e∈))))
                                    c⊆)

    pick-sound : proj₂ (pick bp n m) ✓ × proj₂ (pick bp n m) ⊆ˢ P′
    pick-sound with pick-mem bp n m
    ... | inj₁ eq rewrite eq = bc✓ , widen ∘ bc⊆
    ... | inj₂ eq with subst (Sound P′ b) eq sound-new
    ...   | c✓ , _ , c⊆ = c✓ , c⊆

    inv′ : Inv P′ (⟪ b , m , n ⟫ ∷ es) (b .slot) (proj₂ (pick bp n m))
    inv′ = record
      { inPool  = λ where (here refl) → there (here refl)
                          (there e∈)  → widen (inPool e∈)
      ; covers  = λ x∈ → case split x∈ of λ where
                    (inj₁ refl) → _ , here refl , refl
                    (inj₂ q)    → let (e , e∈ , eq) = covers q in e , there e∈ , eq
      ; sound   = λ where (here refl) → sound-new
                          (there e∈)  → soundW (sound e∈)
      ; longest = λ where (here refl) → longest-new
                          (there e∈)  → longest-old e∈
      ; below   = λ x∈ → case split x∈ of λ where
                    (inj₁ refl) → ≤-refl
                    (inj₂ q)    → ≤-trans (below q) top≤
      ; bc✓     = pick-sound .proj₁
      ; bc⊆     = pick-sound .proj₂
      ; bc≥     = λ where (here refl) → pick-≥m bp n m
                          (there e∈)  → ≤-trans (bc≥ e∈) (pick-≥bc bp n m)
      }

  insert : (t : TreeImpl) (b : Block) (n : ℕ) → top t ≤ b .slot → TreeImpl
  insert t b n top≤ =
    mkTree (b ∷ blocks t) (⟪ b , I.m , n ⟫ ∷ entries t) (b .slot) (pick (best t) n I.m) I.inv′
    where module I = Insert {bp = best t} b n top≤ (inv t)

  ----------------------------------------------------------------------------
  -- Adding a block out of slot order: rebuild the entries in slot order

  -- The blocks added, latest first, each with its adoption number.
  numbered : List Block → List (Block × ℕ)
  numbered []       = []
  numbered (x ∷ xs) = (x , suc (length xs)) ∷ numbered xs

  blocksOf : List (Block × ℕ) → List Block
  blocksOf = map proj₁

  numbered-blocks : ∀ xs → blocksOf (numbered xs) ≡ xs
  numbered-blocks []       = refl
  numbered-blocks (x ∷ xs) = cong (x ∷_) (numbered-blocks xs)

  open import Data.Product.Properties using (≡-dec)
  import Data.Nat.Properties as ℕ

  open SortDesc (≡-dec _≟_ ℕ._≟_) (slot ∘ proj₁) using (sortDesc; sortDesc-∈; sortDesc-∈⁻; Sorted; ltail≤; sortDesc-sorted)

  mutual
    -- The tree of a pool sorted latest first, built from its earliest block;
    -- every block keeps its adoption number.
    build : (xs : List (Block × ℕ)) → Sorted xs → TreeImpl
    build []             _ = tree₀′
    build ((x , n) ∷ xs) s = insert (build xs (ltail≤ s)) x n (build-top≤ x n xs s)

    build-top≤ : ∀ x n xs (s : Sorted ((x , n) ∷ xs)) → top (build xs (ltail≤ s)) ≤ x .slot
    build-top≤ x n []       _             = z≤n
    build-top≤ x n (y ∷ ys) (y≤x Lkd.∷ _) = y≤x

  build-blocks : ∀ xs (s : Sorted xs) → blocks (build xs s) ≡ blocksOf xs
  build-blocks []             _ = refl
  build-blocks ((x , n) ∷ xs) s = cong (x ∷_) (build-blocks xs (ltail≤ s))

  -- The blocks of a list of numbered blocks follow its membership.
  ∈-blocks : ∀ {ys zs : List (Block × ℕ)} → (∀ {p} → p ∈ ys → p ∈ zs)
           → ∀ {x} → x ∈ blocksOf ys → x ∈ blocksOf zs
  ∈-blocks f x∈ with ∈-map⁻ proj₁ x∈
  ... | _ , p∈ , refl = ∈-map⁺ proj₁ (f p∈)

  -- The invariant only sees the pool through membership.
  Inv-cong : ∀ {P Q es top bc} → (∀ {x} → x ∈ P → x ∈ Q) → (∀ {x} → x ∈ Q → x ∈ P)
           → Inv P es top bc → Inv Q es top bc
  Inv-cong {P} {Q} to from I = record
    { inPool  = to ∘ inPool
    ; covers  = covers ∘ from
    ; sound   = λ e∈ → soundC (sound e∈)
    ; longest = λ e∈ c c✓ tc c⊆ → longest e∈ c c✓ tc (from ∘ c⊆)
    ; below   = below ∘ from
    ; bc✓     = bc✓
    ; bc⊆     = to ∘ bc⊆
    ; bc≥     = bc≥
    }
    where
      open Inv I
      soundC : ∀ {x n} → Sound P x n → Sound Q x n
      soundC {n = nothing} _               = tt
      soundC {n = just _}  (c✓ , tc , c⊆) = c✓ , tc , to ∘ c⊆

  rebuild : TreeImpl → Block → TreeImpl
  rebuild t b =
    mkTree (b ∷ blocks t) (entries t′) (top t′) (best t′) (Inv-cong to from (inv t′))
    where
      ns = numbered (b ∷ blocks t)
      xs = sortDesc ns
      s  = sortDesc-sorted ns
      t′ = build xs s

      to : ∀ {x} → x ∈ genesisBlock ∷ blocks t′ → x ∈ genesisBlock ∷ b ∷ blocks t
      to     (here refl) = here refl
      to {x} (there q)   = there (subst (x ∈_) (numbered-blocks (b ∷ blocks t))
                                    (∈-blocks (sortDesc-∈⁻ ns) (subst (x ∈_) (build-blocks xs s) q)))

      from : ∀ {x} → x ∈ genesisBlock ∷ b ∷ blocks t → x ∈ genesisBlock ∷ blocks t′
      from     (here refl) = here refl
      from {x} (there q)   = there (subst (x ∈_) (sym (build-blocks xs s))
                                      (∈-blocks (sortDesc-∈ ns)
                                        (subst (x ∈_) (sym (numbered-blocks (b ∷ blocks t))) q)))

  extend : TreeImpl → Block → TreeImpl
  extend t b with top t ≤? b .slot
  ... | yes top≤ = insert t b (suc (length (blocks t))) top≤
  ... | no  _    = rebuild t b

  ----------------------------------------------------------------------------
  -- The longest chain up to a slot

  -- The chains of the blocks up to a slot, each with its adoption number.
  chainsUpTo : Slot → List Entry → List (ℕ × Chain)
  chainsUpTo sl [] = []
  chainsUpTo sl (e ∷ es) with blk e .slot ≤? sl | chainOf e
  ... | yes _ | just c = (seq e , c) ∷ chainsUpTo sl es
  ... | _     | _      = chainsUpTo sl es

  chainsUpTo-sound : ∀ {sl p} es → p ∈ chainsUpTo sl es
                   → ∃[ e ] e ∈ es × chainOf e ≡ just (proj₂ p) × blk e .slot ≤ sl
  chainsUpTo-sound {sl} (e ∷ es) c∈ with blk e .slot ≤? sl | chainOf e in eq
  ... | yes ≤sl | just _ with c∈
  ...   | here refl = e , here refl , eq , ≤sl
  ...   | there c∈′ = let (e′ , e∈ , rest) = chainsUpTo-sound es c∈′ in e′ , there e∈ , rest
  chainsUpTo-sound (e ∷ es) c∈ | yes _ | nothing = let (e′ , e∈ , rest) = chainsUpTo-sound es c∈ in e′ , there e∈ , rest
  chainsUpTo-sound (e ∷ es) c∈ | no _  | _       = let (e′ , e∈ , rest) = chainsUpTo-sound es c∈ in e′ , there e∈ , rest

  chainsUpTo-complete : ∀ {sl e c} es → e ∈ es → chainOf e ≡ just c → blk e .slot ≤ sl
                      → (seq e , c) ∈ chainsUpTo sl es
  chainsUpTo-complete {sl} (e ∷ es) e∈ eq ≤sl with blk e .slot ≤? sl | chainOf e in eq′ | e∈
  ... | yes _ | just _  | here refl with refl ← trans (sym eq′) eq = here refl
  ... | yes _ | just _  | there e∈′ = there (chainsUpTo-complete es e∈′ eq ≤sl)
  ... | yes _ | nothing | here refl with () ← trans (sym eq′) eq
  ... | yes _ | nothing | there e∈′ = chainsUpTo-complete es e∈′ eq ≤sl
  ... | no ¬≤ | _       | here refl = contradiction ≤sl ¬≤
  ... | no _  | _       | there e∈′ = chainsUpTo-complete es e∈′ eq ≤sl

  -- At or past the highest slot it is the longest chain of all; before
  -- that, the longest chain of a block up to the slot.  Either way, of
  -- equally long chains the one adopted last.
  bestChainT : Slot → TreeImpl → Chain
  bestChainT sl t with top t ≤? sl
  ... | yes _ = bestC t
  ... | no  _ = proj₂ (Latest.maxBy (0 , [ genesisBlock ]) (chainsUpTo sl (entries t)))

  ----------------------------------------------------------------------------
  -- The laws

  UpTo : Slot → TreeImpl → List Block
  UpTo sl t = filter ((_≤? sl) ∘ slot) (pool t)

  extendable′ : ∀ t b → pool (extend t b) ≡ˢ pool t ++ [ b ]
  extendable′ t b = ⊆×⊇⇒≡ˢ to from
    where
      same : pool (extend t b) ≡ genesisBlock ∷ b ∷ blocks t
      same with top t ≤? b .slot
      ... | yes _ = refl
      ... | no  _ = refl

      to : pool (extend t b) ⊆ˢ pool t ++ [ b ]
      to {x} x∈ with subst (x ∈_) same x∈
      ... | here refl         = here refl
      ... | there (here refl) = there (∈-++⁺ʳ (blocks t) (here refl))
        where open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
      ... | there (there q)   = there (∈-++⁺ˡ q)
        where open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)

      from : pool t ++ [ b ] ⊆ˢ pool (extend t b)
      from {x} (here refl) = subst (x ∈_) (sym same) (here refl)
      from {x} (there q) with ∈-++⁻ (blocks t) q
        where open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
      ... | inj₁ p           = subst (x ∈_) (sym same) (there (there p))
      ... | inj₂ (here refl) = subst (x ∈_) (sym same) (there (here refl))

  valid′ : ∀ t sl → bestChainT sl t ✓
  valid′ t sl with top t ≤? sl
  ... | yes _ = Inv.bc✓ (inv t)
  ... | no  _ with Latest.maxBy-mem (0 , [ genesisBlock ]) (chainsUpTo sl (entries t))
  ...   | inj₁ eq = subst _✓ (sym (cong proj₂ eq)) gb✓
  ...   | inj₂ c∈ with chainsUpTo-sound (entries t) c∈
  ...     | e , e∈ , eq , _ = subst (Sound (pool t) (blk e)) eq (Inv.sound (inv t) e∈) .proj₁

  selfContained′ : ∀ t sl → bestChainT sl t ⊆ˢ UpTo sl t
  selfContained′ t sl with top t ≤? sl
  ... | yes top≤ = λ x∈ →
        let x∈P = Inv.bc⊆ (inv t) x∈
        in ∈-filter⁺ ((_≤? sl) ∘ slot) x∈P (≤-trans (Inv.below (inv t) x∈P) top≤)
  ... | no  _ with Latest.maxBy-mem (0 , [ genesisBlock ]) (chainsUpTo sl (entries t))
  ...   | inj₁ eq = λ x∈ → case subst (_ ∈_) (cong proj₂ eq) x∈ of λ where
            (here refl) → ∈-filter⁺ ((_≤? sl) ∘ slot) (here refl) (subst (_≤ sl) (sym gb-slot) z≤n)
  ...   | inj₂ c∈ with chainsUpTo-sound (entries t) c∈
  ...     | e , e∈ , eq , ≤sl with subst (Sound (pool t) (blk e)) eq (Inv.sound (inv t) e∈)
  ...       | c✓ , tc , c⊆ = λ x∈ →
              ∈-filter⁺ ((_≤? sl) ∘ slot) (c⊆ x∈)
                (≤-trans (✓-slot≤ c✓ x∈) (subst (λ y → y .slot ≤ sl) (sym tc) ≤sl))

  optimal′ : ∀ c t sl → c ✓ → c ⊆ˢ UpTo sl t → length c ≤ length (bestChainT sl t)
  optimal′ c t sl c✓ c⊆ =
    let (t∈P , t≤sl) = ∈-filter⁻ ((_≤? sl) ∘ slot) {xs = pool t} (c⊆ (✓-tip∈ c✓))
        (e , e∈ , be) = Inv.covers (inv t) t∈P
        lenC = Inv.longest (inv t) e∈ c c✓ (sym be) c⊆P
    in go e e∈ (subst (λ y → y .slot ≤ sl) (sym be) t≤sl) lenC
    where
      c⊆P : c ⊆ˢ pool t
      c⊆P x∈ = ∈-filter⁻ ((_≤? sl) ∘ slot) {xs = pool t} (c⊆ x∈) .proj₁

      go : ∀ e → e ∈ entries t → blk e .slot ≤ sl → length c ≤ lenM (chainOf e)
         → length c ≤ length (bestChainT sl t)
      go e e∈ ≤sl lenC with top t ≤? sl
      ... | yes _ = ≤-trans lenC (Inv.bc≥ (inv t) e∈)
      ... | no  _ with chainOf e in eq
      ...   | just c″ = ≤-trans lenC (Latest.maxBy-≥ (0 , [ genesisBlock ]) _ (chainsUpTo-complete (entries t) e∈ eq ≤sl))
      ...   | nothing = contradiction (≤-trans (nonempty (✓-tip∈ c✓)) lenC) λ ()
        where
          nonempty : ∀ {x} {xs : List Block} → x ∈ xs → 1 ≤ length xs
          nonempty (here _)  = s≤s z≤n
          nonempty (there _) = s≤s z≤n

  blockTree : Tree TreeImpl
  blockTree = record
    { tree₀         = tree₀′
    ; extendTree    = extend
    ; allBlocks     = pool
    ; bestChain     = bestChainT
    ; instantiated  = refl
    ; extendable    = extendable′
    ; valid         = valid′
    ; optimal       = optimal′
    ; selfContained = selfContained′
    }
