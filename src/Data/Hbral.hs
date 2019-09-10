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

module Data.Hbral where

import Prelude 
import Data.Proxy

data Nat = Zero | Succ Nat

data Vec (a :: *) :: Nat -> * where
  Nil  :: Vec a Zero
  Cons :: a -> Vec a n -> Vec a (Succ n)

data Dir = L | R

data Tree (a :: *) :: Nat -> * where
  Leaf :: a -> Tree a Zero
  Node :: Tree a n -> Tree a n -> Tree a (Succ n)

treeLookup :: Tree a n -> Vec Dir n -> a
treeLookup (Node l r) (Cons L ds) = treeLookup l ds
treeLookup (Node l r) (Cons R ds) = treeLookup r ds
treeLookup (Leaf x) Nil = x

data Bin =
    End
    | I Bin
    | O Bin

bsucc :: Bin -> Bin
bsucc End = I End
bsucc (I b) = O (bsucc b)
bsucc (O b) = I b

type family Bsucc (b :: Bin) :: Bin where
  Bsucc End  = I End
  Bsucc (O b) = I b
  Bsucc (I b) = O (Bsucc b)

data RAL (a :: *) :: Nat -> Bin -> * where
  RNil :: RAL a n End
  ConsI :: Tree a n -> RAL a (Succ n) b -> RAL a n (I b)
  ConsO :: RAL a (Succ n) b -> RAL a n (O b)

data Pos :: Nat -> Bin -> * where
  Here :: Vec Dir n -> Pos n (I b)
  ThereO :: Pos (Succ n) b -> Pos n (O b)
  ThereI :: Pos (Succ n) b -> Pos n (I b)  

ralLookup :: RAL a n b -> Pos n b -> a
ralLookup (ConsI t _) (Here ds) = treeLookup t ds
ralLookup (ConsO ral) (ThereO p) = ralLookup ral p
ralLookup (ConsI _ ral) (ThereI p) = ralLookup ral p

consTree :: Tree a n -> RAL a n b -> RAL a n (Bsucc b)
consTree t RNil = ConsI t RNil
consTree t (ConsI t' r) = ConsO (consTree (Node t t') r)
consTree t (ConsO r) = ConsI t r

cons :: a -> RAL a Zero b -> RAL a Zero (Bsucc b)
cons x r = consTree (Leaf x) r

data HTree (n :: Nat) :: Tree * n -> * where
  HLeaf :: a -> HTree 'Zero (Leaf a)
  HNode :: HTree n us -> HTree n vs -> HTree ('Succ n) (Node us vs)

data HTreePath (t :: Tree * n) (u :: *) :: * where
  HHere :: HTreePath (Leaf u) u
  HLeft :: forall us vs u . HTreePath us u -> HTreePath (Node us vs) u
  HRight :: HTreePath vs u -> HTreePath (Node us vs) u  

htreeLookup :: HTree n ut -> HTreePath ut u -> u
htreeLookup (HLeaf x) HHere = x
htreeLookup (HNode l r) (HLeft p) = htreeLookup l p
htreeLookup (HNode l r) (HRight p) = htreeLookup r p

data HRAL (n :: Nat) (b :: Bin) :: RAL * n b -> * where
  HNil :: HRAL n End RNil
  HCons1 :: HTree n t -> HRAL (Succ n) b ral -> HRAL n (I b) (ConsI t ral)
  HCons0 :: HRAL (Succ n) b ral -> HRAL n (O b) (ConsO ral)  

data HPos (n :: Nat) (b :: Bin) (ral :: RAL * n b) (a :: *) :: * where
   HFound :: HTreePath t a -> HPos n (I b) (ConsI t ral) a
   HThere0 :: HPos (Succ n) b ral a -> HPos n (O b) (ConsO ral) a
   HThere1 :: HPos (Succ n) b ral a -> HPos n (I b) (ConsI t ral) a

hralLookup :: HRAL n b ral -> HPos n b ral a -> a
hralLookup (HCons1 t hral) (HFound p) = htreeLookup t p
hralLookup (HCons1 t hral) (HThere1 p) = hralLookup hral p
hralLookup (HCons0 hral) (HThere0 p) = hralLookup hral p

type family ConsTree (t :: Tree a n) (ral :: RAL a n b) :: RAL a n (Bsucc b) where
  ConsTree t RNil = ConsI t RNil
  ConsTree t (ConsI t' r) = ConsO (ConsTree (Node t t') r)
  ConsTree t (ConsO r) = ConsI t r

type Cons a ral = ConsTree (Leaf a) ral

hconsTree :: HTree n t -> HRAL n b ral -> HRAL n (Bsucc b)  (ConsTree t ral)
hconsTree t HNil = HCons1 t HNil
hconsTree t (HCons0 hral) = HCons1 t hral
hconsTree t (HCons1 t' hral) = HCons0 (hconsTree (HNode t t') hral)

hcons :: a -> HRAL Zero b ral -> HRAL Zero (Bsucc b) (ConsTree (Leaf a) ral)
hcons x hral = hconsTree (HLeaf x) hral

class Top (ral :: RAL * n b) a where
  top :: HPos n b ral a

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

class Pop (ral :: RAL * n b) (ral' :: RAL * n b') | ral' -> ral where
   pop :: HPos n b ral a -> HPos n b' ral' a
  
instance (Pop (ral :: RAL * (Succ n) b) (ral' :: RAL * (Succ n) b')
         , PopTree ral' (Node t' t)) =>
         Pop (ConsI t ral) (ConsO ral') where
  pop (HFound p)  = HThere0 (popTree @(Succ n) @b' @ral' @(Node t' t) (HRight p))
  pop (HThere1 p) = HThere0 (pop p)

instance Pop (ConsO ral) (ConsI t ral) where
  pop (HThere0 p) = HThere1 p

class PopTree (ral :: RAL * n b) (t :: Tree * n ) | ral -> t where
  popTree :: HTreePath t a -> HPos n b ral a
instance PopTree (ConsI t ral) t where
  popTree tp = HFound tp
instance PopTree ral (Node t t') => PopTree (ConsO ral) t where
  popTree tp = HThere0  (popTree (HLeft @t @t' tp))

test :: Int
test = hralLookup (hcons True $ hcons 'a' $ hcons (3 :: Int) $ hcons (3 :: Int) $ HNil) (pop $ pop top)

test2 :: Char
test2 = hralLookup (hcons True $ hcons 'a' $ hcons (3 :: Int) $ hcons (3 :: Int) $ HNil) (pop top)

test3 :: Bool
test3 = hralLookup (hcons True $ hcons 'a' $ hcons (3 :: Int) $ hcons (3 :: Int) $ HNil) top

hralTest = hcons True $ hcons 'a' $ hcons (3 :: Int) $ hcons (3 :: Int) $ HNil
