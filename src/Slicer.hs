{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Slicer where

import Data.Distributive
import Data.Functor.Rep
import Data.List ((!!))
import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.TH (promote, (:~:)(..))
import Data.Singletons.Prelude.List
import Data.Singletons.TypeLits
import GHC.Exts
import GHC.Show
import GHC.TypeLits
import GHC.TypeLits.Compare
import qualified Data.Vector as V
import Data.Foldable
import Data.Kind
import Data.Maybe

data ProdMap :: (a -> b -> Type) -> [a] -> [b] -> Type where
    PMZ :: ProdMap f '[] '[]
    PMS :: f a b -> ProdMap f as bs -> ProdMap f (a ': as) (b ': bs)

data Slice :: Nat -> Nat -> Type where
    Slice :: Sing l -> Sing c -> Sing r -> Slice (l + c + r) c

slice
    :: (SingI ns, SingI ms)
    => ProdMap Slice ns ms
    -> Tensor ns a
    -> Tensor ms a
slice pms = undefined

data IsLTE :: Nat -> Nat -> Type where
    IsLTE :: (n <= m) => Sing n -> Sing m -> IsLTE n m 

-- given a type-level list `ns` of the number of items from each dimension to take,
-- returns the `ProdMap Slice ms ns` that encodes that.
sliceHeads :: forall ms ns. ProdMap IsLTE ns ms -> ProdMap Slice ms ns
sliceHeads = \case
    PMZ -> PMZ
    IsLTE sN sM `PMS` ltes ->
      Slice (SNat @0) sN (sM %:- sN) `PMS` sliceHeads ltes

data CurrySing :: k1 -> k2 -> Type where
    CurrySing :: Sing a -> Sing b -> CurrySing a b

mkLTE :: ProdMap CurrySing ns ms -> Maybe (ProdMap IsLTE ns ms)
mkLTE = \case
    PMZ -> Just PMZ
    CurrySing (n :: Sing n) (m :: Sing m) `PMS` pms -> case 
    -- %<=? from http://hackage.haskell.org/package/typelits-witnesses-0.2.3.0/docs/GHC-TypeLits-Compare.html
     (Proxy @n) %<=? (Proxy @m) of
       LE Refl -> IsLTE n m <$> mkLTE pms
       _       -> Nothing

zipSings
    :: Sing as
    -> Sing bs
    -> Maybe (ProdMap CurrySing as bs)
zipSings = \case
    SNil -> \case
      SNil -> Just PMZ
      _ `SCons` _ -> Nothing
    sA `SCons` sAs -> \case
      SNil        -> Nothing
      sB `SCons` sBs ->
        (CurrySing sA sB `PMS`) <$> zipSings sAs sBs

headsFromList
    :: SingI ms
    => [Integer]
    -> Tensor ms a
    -> (forall ns. SingI ns => Tensor ns a -> r)
    -> r
headsFromList ns t f = withSomeSing ns $ \nsSing ->
                       withSingI nsSing $
    case zipSings nsSing (sing @_ @_) of
      Nothing -> error "dimensions don't line up"
      Just nsms -> case mkLTE nsms of
        Nothing -> error "dimensions out of range"
        Just lte -> f (slice (sliceHeads lte) t)

newtype Tensor (r::[Nat]) a = Tensor { v :: V.Vector a }
    deriving (Functor, Eq, Foldable)

shape :: forall (r::[Nat]) a. (SingI r) => Tensor r a -> [Int]
shape _ = case (sing :: Sing r) of
            SNil -> []
            (SCons x xs) -> fromIntegral <$> (fromSing x: fromSing xs)

instance forall r. (SingI r) => Distributive (Tensor (r::[Nat])) where
    distribute f = Tensor $ V.generate n
        $ \i -> fmap (\(Tensor v) -> V.unsafeIndex v i) f
      where
        n = case (sing :: Sing r) of
          SNil -> 1
          (SCons x xs) -> product $ fromInteger <$> (fromSing x: fromSing xs)

instance forall (r :: [Nat]). (SingI r) => Representable (Tensor r) where
    type Rep (Tensor r) = [Int]
    tabulate f = Tensor $ V.generate (product ns) (f . unind ns)
      where
        ns = case (sing :: Sing r) of
          SNil -> []
          (SCons x xs) -> fromIntegral <$> (fromSing x: fromSing xs)
        unfoldI :: forall t. Integral t => [t] -> t -> ([t], t)
        unfoldI ns x =
            foldr
            (\a (acc, r) -> let (d,m) = divMod r a in (m:acc,d))
            ([],x)
            ns
        unind :: [Int] -> Int -> [Int]
        unind ns x= fst $ unfoldI ns x

    index (Tensor xs) rs = xs V.! ind ns rs
      where
        ns = case (sing :: Sing r) of
          SNil -> []
          (SCons x xs') -> fromIntegral <$> (fromSing x: fromSing xs')
        ind :: [Int] -> [Int] -> Int
        ind ns xs = sum $ zipWith (*) xs (drop 1 $ scanr (*) 1 ns)
