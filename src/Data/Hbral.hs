{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A library for heterogeneous collections with logarithmic lookup time
module Data.Hbral (Data.Hbral.lookup, cons, nil, top, pop) where

import Data.Proxy

data Nat = Zero | Succ Nat

data Vec (a :: *) :: Nat -> * where
  Nil  :: Vec a Zero
  Cons :: a -> Vec a n -> Vec a (Succ n)

data Dir = L | R

data Tree (a :: *) :: Nat -> * where
  Leaf :: a -> Tree a Zero
  Node :: Tree a n -> Tree a n -> Tree a (Succ n)

data Bin =
    End
    | I Bin
    | O Bin

type family Bsucc (b :: Bin) :: Bin where
  Bsucc End  = I End
  Bsucc (O b) = I b
  Bsucc (I b) = O (Bsucc b)

data BRAL (a :: *) :: Nat -> Bin -> * where
  RNil :: BRAL a n End
  ConsI :: Tree a n -> BRAL a (Succ n) b -> BRAL a n (I b)
  ConsO :: BRAL a (Succ n) b -> BRAL a n (O b)

type family ConsTree (t :: Tree a n) (ral :: BRAL a n b) :: BRAL a n (Bsucc b) where
  ConsTree t RNil = ConsI t RNil
  ConsTree t (ConsI t' r) = ConsO (ConsTree (Node t t') r)
  ConsTree t (ConsO r) = ConsI t r

type Cons a ral = ConsTree (Leaf a) ral

data HTree (n :: Nat) :: Tree * n -> * where
  HLeaf :: a -> HTree 'Zero (Leaf a)
  HNode :: HTree n us -> HTree n vs -> HTree ('Succ n) (Node us vs)

data HTreePath (t :: Tree * n) (u :: *) :: * where
  HHere :: HTreePath (Leaf u) u
  HLeft :: forall us vs u . HTreePath us u -> HTreePath (Node us vs) u
  HRight :: HTreePath vs u -> HTreePath (Node us vs) u  

htreeLookup :: HTree n ut -> HTreePath ut u -> u
htreeLookup (HLeaf x)   HHere       = x
htreeLookup (HNode l r) (HLeft p)   = htreeLookup l p
htreeLookup (HNode l r) (HRight p)  = htreeLookup r p

data HBRAL (n :: Nat) (b :: Bin) :: BRAL * n b -> * where
  HNil   :: HBRAL n End RNil
  HCons1 :: HTree n t -> HBRAL (Succ n) b ral -> HBRAL n (I b) (ConsI t ral)
  HCons0 :: HBRAL (Succ n) b ral -> HBRAL n (O b) (ConsO ral)  

data Pos (n :: Nat) (b :: Bin) (ral :: BRAL * n b) (a :: *) :: * where
   HFound  :: HTreePath t a -> Pos n (I b) (ConsI t ral) a
   HThere0 :: Pos (Succ n) b ral a -> Pos n (O b) (ConsO ral) a
   HThere1 :: Pos (Succ n) b ral a -> Pos n (I b) (ConsI t ral) a

-- | Lookup the value at an argument position in a heterogenous collection
lookup :: HBRAL n b ral -> Pos n b ral a -> a
lookup (HCons1 t hral) (HFound p) = htreeLookup t p
lookup (HCons1 t hral) (HThere1 p) = Data.Hbral.lookup hral p
lookup (HCons0 hral) (HThere0 p) = Data.Hbral.lookup hral p

hconsTree :: HTree n t -> HBRAL n b ral -> HBRAL n (Bsucc b)  (ConsTree t ral)
hconsTree t HNil = HCons1 t HNil
hconsTree t (HCons0 hral) = HCons1 t hral
hconsTree t (HCons1 t' hral) = HCons0 (hconsTree (HNode t t') hral)

-- | Add one element to a heterogeneous collection 
cons :: a -> HBRAL Zero b ral -> HBRAL Zero (Bsucc b) (ConsTree (Leaf a) ral)
cons x hral = hconsTree (HLeaf x) hral

-- | An empty heterogeneous collection
nil :: HBRAL n End RNil
nil = HNil


class Top (ral :: BRAL * n b) a where
  -- | The first element of a non-empty heterogeneous collection  
  top :: Pos n b ral a

instance Top ral a => Top (ConsO ral) a where
   top = HThere0 top  

instance TopTree t a => Top (ConsI t ral) a where
   top = HFound topTreePath

class TopTree (t :: Tree * n) a | t -> a where
   topTreePath :: HTreePath t a

instance TopTree (Leaf a) a where
   topTreePath = HHere

instance TopTree l a => TopTree (Node l r) a where
   topTreePath = HLeft topTreePath

class Pop (ral :: BRAL * n b) (ral' :: BRAL * n b') | ral' -> ral where
  -- | Weaken an existing position in a heterogeneous collection    
  pop :: Pos n b ral a -> Pos n b' ral' a
  
instance (Pop (ral :: BRAL * (Succ n) b) (ral' :: BRAL * (Succ n) b')
         , PopTree ral' (Node t' t)) =>
         Pop (ConsI t ral) (ConsO ral') where
  pop (HFound p)  = HThere0 (popTree @(Succ n) @b' @ral' @(Node t' t) (HRight p))
  pop (HThere1 p) = HThere0 (pop p)

instance Pop (ConsO ral) (ConsI t ral) where
  pop (HThere0 p) = HThere1 p

class PopTree (ral :: BRAL * n b) (t :: Tree * n ) | ral -> t where
  popTree :: HTreePath t a -> Pos n b ral a
instance PopTree (ConsI t ral) t where
  popTree tp = HFound tp
instance PopTree ral (Node t t') => PopTree (ConsO ral) t where
  popTree tp = HThere0  (popTree (HLeft @t @t' tp))

test :: Int
test = Data.Hbral.lookup (cons True $ cons 'a' $ cons (3 :: Int) $ cons (3 :: Int) $ HNil) (pop $ pop top)

test2 :: Char
test2 = Data.Hbral.lookup (cons True $ cons 'a' $ cons (3 :: Int) $ cons (3 :: Int) $ HNil) (pop top)

test3 :: Bool
test3 = Data.Hbral.lookup (cons True $ cons 'a' $ cons (3 :: Int) $ cons (3 :: Int) $ HNil) top

hralTest = cons True $ cons 'a' $ cons (3 :: Int) $ cons (3 :: Int) $ HNil
