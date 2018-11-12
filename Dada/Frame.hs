{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import qualified Data.Vector.HFixed.Cont     as C
import qualified Data.Vector.HFixed.Class    as C
import           Data.Vector.HFixed.Cont          (Arity)
import           Data.Vector.HFixed.TypeFuns
import           Data.Vector.HFixed               (HVector,Elems)
import           Data.Vector.HFixed.HVec          (HVecF)

import GHC.TypeLits
import GHC.OverloadedLabels

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

-- -- | Index
-- data Idx i a = Idx
--   { idxIdxVec :: V.Vector i     -- Mapping int to number
--   , idxIdxMap :: Map i Int
--   , idxBuffer :: DF a
--   }

-- innerJoin
--   :: Ord i
--   => Idx i a -> Idx i b -> Idx i (a :+: b)
-- innnerJoin = undefined

-- leftJoin
--   :: Ord i
--   => Idx i a -> Idx i b -> Idx i (a :+: Maybe b) -- How to deal with Maybes???
-- leftJoin = undefined

-- rightJoin
--   :: Ord i
--   => Idx i a -> Idx i b -> Idx i (Maybe a :+: b) -- How to deal with Maybes???
-- rightJoin = undefined



----------------------------------------------------------------
-- Vector API
----------------------------------------------------------------

type instance G.Mutable DF = MDF

instance HVector a => M.MVector MDF a where
  {-# INLINE basicLength #-}
  basicLength          (MDF i _)   = i
  --
  {-# INLINE basicUnsafeSlice #-}
  basicUnsafeSlice i n (MDF _ hv)
    = MDF n
    $ H.mapNat (M.basicUnsafeSlice i n) hv
  --
  {-# INLINE basicOverlaps #-}
  basicOverlaps (MDF _ hv1) (MDF _ hv2)
    = getAny
    $ getConst
    $ H.sequence_
    $ H.zipWithNatF (\v1 v2 -> Const (Any (M.basicOverlaps v1 v2))) hv1 hv2
  --
  {-# INLINE basicUnsafeNew #-}
  basicUnsafeNew n = do
    hv <- H.sequenceF
        $ H.replicateNatF (Compose (M.basicUnsafeNew n))
    return $ MDF n hv
  --
  {-# INLINE basicInitialize #-}
  basicInitialize _ = return ()
  --
  {-# INLINE basicUnsafeRead #-}
  basicUnsafeRead (MDF _ hv) i =
    H.sequence $ H.mapNat (\v -> M.basicUnsafeRead v i) hv
  --
  {-# INLINE basicUnsafeWrite #-}
  basicUnsafeWrite (MDF _ hv) i a
    = fmap getConst
    $ getCompose
    $ H.sequence_
    $ H.zipWithNatF (\v (Identity x) -> Compose (Const <$> M.basicUnsafeWrite v i x))
        hv
       (H.wrap Identity a)



instance HVector a => G.Vector DF a where
  {-# INLINE basicLength #-}
  basicLength (DF i _) = i
  --
  {-# INLINE basicUnsafeSlice #-}
  basicUnsafeSlice i n (DF _ vs)
    = DF n
    $ H.mapNat (G.basicUnsafeSlice i n) vs
  --
  {-# INLINE basicUnsafeIndexM #-}
  basicUnsafeIndexM (DF _ vs) i
    = H.sequence
    $ H.mapNat (\v -> G.basicUnsafeIndexM v i) vs
  --
  {-# INLINE basicUnsafeFreeze #-}
  basicUnsafeFreeze (MDF i mv) = do
    vs <- H.sequenceF $ H.mapNat (Compose . G.basicUnsafeFreeze) mv
    return $ DF i vs
  --
  {-# INLINE basicUnsafeThaw #-}
  basicUnsafeThaw (DF i vs) = do
    mv <- H.sequenceF $ H.mapNat (Compose . G.basicUnsafeThaw) vs
    return $ MDF i mv


----------------------------------------------------------------
-- Labeled lenses
----------------------------------------------------------------

-- | List of labels which is associated with fields of data type
type family Labels a :: [Symbol]

-- | Type of field of data type
type Field a sym = LabelTy sym (Labels a) (Elems a)

-- | Proxy type which is used to create overloaded labels
data L (sym :: Symbol) = L

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

-- | Lens which gives access to individual columns of data type
le' :: forall sym f a b x. ( SymIndex sym (Labels a) (Elems a)
                           , HVector a
                           , HVector b
                           , Elems b ~ UpdatedTypes sym (Labels a) (Elems a) x
                           , Functor f
                           )
    => L sym
    -> (V.Vector (Field a sym) -> f (V.Vector x))
    -> DF a -> f (DF b)
le' _ f (DF i vs)
  = fmap (DF i)
  $ H.inspectF vs
  $ lensChTF (Proxy @ sym) (Proxy @ (Labels a)) f' H.constructF
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
    -> (Field a sym -> f (Field a sym))
    -> a -> f a
lev _ f v = H.inspect v
          $ lensF (Proxy @ sym) (Proxy @ (Labels a)) f H.construct

-- | Lens which gives access to individual values in labeled tuple
lev' :: forall sym f a b x. ( SymIndex sym (Labels a) (Elems a)
                            , HVector a
                            , HVector b
                            , Elems b ~ UpdatedTypes sym (Labels a) (Elems a) x
                            , Functor f
                            )
     => L sym
     -> (Field a sym -> f x)
     -> a -> f b
lev' _ f v = H.inspect v
           $ lensChF (Proxy @ sym) (Proxy @ (Labels a)) f H.construct

subtype
  :: forall a b. ( Subtype (Labels b) (Elems b) (Labels a) (Elems a)
                 , HVector a
                 , HVector b
                 )
  => a -> b
subtype v
  = H.inspect v
  $ fmap C.vector (subtypeF (Proxy @ (Labels b)) (Proxy @ (Labels a)))

subtypeDF
  :: forall a b. ( Subtype (Labels b) (Elems b) (Labels a) (Elems a)
                 , HVector a
                 , HVector b
                 )
  => DF a -> DF b
subtypeDF (DF i v)
  = DF i
  $ H.inspectF v
  $ fmap C.vectorF (subtypeTF (Proxy @ (Labels b)) (Proxy @ (Labels a)))


----------------------------------------------------------------
-- Data types
----------------------------------------------------------------

data a :+: b = a :+: b
  deriving (Show,Eq)

type instance Labels (a :+: b) = Labels a ++ Labels b

instance ( Arity (Elems a ++ Elems b)
         , HVector a
         , HVector b
         ) => HVector (a :+: b) where
  type Elems (a :+: b) = Elems a ++ Elems b
  inspect (a :+: b) f = H.inspect b
                      $ H.inspect a
                      $ C.curryMany f
  construct = C.uncurryMany $ do
    a <- H.construct
    return $ (a :+:) <$> H.construct
