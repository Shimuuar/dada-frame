{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
-- |
module Dada.Frame where

import Control.Applicative
import Control.Lens
import           Data.Typeable (Proxy(..))
import           Data.Functor.Compose
import           Data.Monoid
import qualified Data.Vector.Generic         as G
import qualified Data.Vector.Generic.Mutable as M
import qualified Data.Vector                 as V
import qualified Data.Vector.HFixed          as H
import           Data.Vector.HFixed               (HVector,Elems)
import           Data.Vector.HFixed.Functor.HVecF (HVecF)
-- import           Data.Vector.HFixed.HVec          (HVec)

import GHC.TypeLits
import GHC.OverloadedLabels
import GHC.Generics (Generic)

import Dada.Internal.Lens


----------------------------------------------------------------
-- Data frames
----------------------------------------------------------------

-- | Data frame for newtype. Internally it's implemented as structure
--   of arrays.
data DF    a = DF  Int (HVecF (Elems a) V.Vector)

-- | Mutable variant of data frame
data MDF s a = MDF Int (HVecF (Elems a) (G.Mutable V.Vector s))

instance (HVector a, Show a) => Show (DF a) where
  show = unlines . map show . G.toList 

----------------------------------------------------------------
-- Vector API
----------------------------------------------------------------

type instance G.Mutable DF = MDF

instance HVector a => M.MVector MDF a where
  basicLength          (MDF i _)   = i
  --
  basicUnsafeSlice i n (MDF _ hv)
    = MDF n
    $ H.mapFunctor (M.basicUnsafeSlice i n) hv
  --
  basicOverlaps (MDF _ hv1) (MDF _ hv2)
    = getAny
    $ getConst
    $ H.sequence_
    $ H.zipNatF (\v1 v2 -> Const (Any (M.basicOverlaps v1 v2))) hv1 hv2
  --
  basicUnsafeNew n = do
    hv <- H.sequenceF
        $ H.replicateF (Compose (M.basicUnsafeNew n))
    return $ MDF n hv
  --
  basicInitialize _ = return ()
  --
  basicUnsafeRead (MDF _ hv) i =    
    H.sequence $ H.mapFunctor (\v -> M.basicUnsafeRead v i) hv
  --
  basicUnsafeWrite (MDF _ hv) i a = do
    let vecA = H.wrap Identity a :: HVecF (Elems a) Identity
    fmap getConst
      $ getCompose
      $ H.sequence_
      $ H.zipNatF (\v (Identity x) -> Compose (Const <$> M.basicUnsafeWrite v i x)) hv vecA

instance HVector a => G.Vector DF a where
  basicLength (DF i _) = i
  --
  basicUnsafeSlice i n (DF _ vs)
    = DF n
    $ H.mapFunctor (G.basicUnsafeSlice i n) vs
  --
  basicUnsafeIndexM (DF _ vs) i
    = H.sequence
    $ H.mapFunctor (\v -> G.basicUnsafeIndexM v i) vs
  --
  basicUnsafeFreeze (MDF i mv) = do
    vs <- H.sequenceF $ H.mapFunctor (Compose . G.basicUnsafeFreeze) mv
    return $ DF i vs
  --
  basicUnsafeThaw (DF i vs) = do
    mv <- H.sequenceF $ H.mapFunctor (Compose . G.basicUnsafeThaw) vs
    return $ MDF i mv


----------------------------------------------------------------
-- Labeled lenses
----------------------------------------------------------------

-- | List of labels which is associated with fields of data type
type family Labels a :: [Symbol]

-- | Type of field of data type
type Field a sym = LabelTy sym (Labels a) (Elems a)

-- | Proxy type which is used to create overloaded labels
data L sym = L

instance (sym ~ sym') => IsLabel sym' (L sym) where
  fromLabel = L


-- | Lens which gives access to individual columns of data type
le :: forall sym f a. ( SymIndex sym (Labels a) (Elems a)
                      , HVector a
                      , Functor f
                      )
   => L sym
   -> (V.Vector (Field a sym) -> f (V.Vector (Field a sym)))
   -> DF a -> f (DF a)
le _ f (DF i vs)
  = fmap (DF i)
  $ H.inspectF vs
  $ lensTF (Proxy @ sym) (Proxy @ (Labels a)) f' H.constructF
  where
    f' v = let check u | V.length u == V.length v = u
                       | otherwise                = error "Length mismatch!"
           in check <$> f v

-- | Lens which gives access to individual values in labeled tuple
lev :: forall sym f a. ( SymIndex sym (Labels a) (Elems a)
                       , HVector a
                       , Functor f
                       )
    => L sym
--    -> (LabelTy sym (Labels a) (Elems a) -> f (LabelTy sym (Labels a) (Elems a)))
    -> (Field a sym -> f (Field a sym))
    -> a -> f a
lev _ f v = H.inspect v
          $ lensF (Proxy @ sym) (Proxy @ (Labels a)) f H.construct
