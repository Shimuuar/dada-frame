{-# LANGUAGE TypeApplications #-}
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
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
-- |
module Dada.Frame where

import Control.Applicative
import Control.Lens
import           Data.Typeable (Proxy(..))
import           Data.Functor.Compose
import           Data.Functor.Identity
import           Data.Monoid
import qualified Data.Vector.Generic         as G
import qualified Data.Vector.Generic.Mutable as M
import qualified Data.Vector                 as V
import qualified Data.Vector.HFixed          as H
import           Data.Vector.HFixed               (HVector,Elems)
import           Data.Vector.HFixed.Functor.HVecF (HVecF)
import           Data.Vector.HFixed.HVec          (HVec)
import           Data.Vector.HFixed.Class (lensWorkerF,lensWorkerTF,stepFun,stepTFun,Fun,TFun)

import GHC.TypeLits
import Data.Type.Equality( type  (==))
import GHC.OverloadedLabels


import GHC.Generics (Generic)

----------------------------------------------------------------
-- Data frames
----------------------------------------------------------------

-- | Data frame for newtype
data DF    a = DF  Int (HVecF (Elems a) V.Vector)
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

type family Labels a :: [Symbol]


-- | Indexing of vectors
class SymIndex (sym :: Symbol) (labels :: [Symbol]) (xs :: [*]) where
  type LabelTy sym labels xs :: *
  lensF  :: (Functor f)
         => Proxy sym
         -> Proxy labels
         -> (LabelTy sym labels xs -> f (LabelTy sym labels xs))
         -> (Fun xs r -> Fun xs (f r))
  lensTF :: (Functor f)
         => Proxy sym
         -> Proxy labels
         -> (g (LabelTy sym labels xs) -> f (g (LabelTy sym labels xs)))
         -> (TFun g xs r -> TFun g xs (f r))

instance (SymIndexEq (sym == l) sym (l ': ls) xs) => SymIndex sym (l ': ls) xs where
  type LabelTy sym (l ': ls) xs = LabelEqTy (sym == l) sym (l ': ls) xs
  lensF  = lensEqF  (Proxy @ (sym == l))
  lensTF = lensEqTF (Proxy @ (sym == l))

class SymIndexEq (eq :: Bool)  (sym :: Symbol) (labels :: [Symbol]) (xs :: [*]) where
  type LabelEqTy eq sym labels xs :: *
  lensEqF  :: (Functor f)
           => Proxy eq
           -> Proxy sym
           -> Proxy labels
           -> (LabelEqTy eq sym labels xs -> f (LabelEqTy eq sym labels xs))
           -> (Fun xs r -> Fun xs (f r))
  lensEqTF :: (Functor f)
           => Proxy eq
           -> Proxy sym
           -> Proxy labels
           -> (g (LabelEqTy eq sym labels xs) -> f (g (LabelEqTy eq sym labels xs)))
           -> (TFun g xs r -> TFun g xs (f r))

instance (H.Arity xs) => SymIndexEq 'True sym labels (x ': xs) where
  type LabelEqTy 'True sym labels (x ': xs) = x
  lensEqF  _ _ _ = lensWorkerF
  lensEqTF _ _ _ = lensWorkerTF

instance (SymIndex sym labels xs) => SymIndexEq 'False sym labels (x ': xs) where
  type LabelEqTy 'False sym labels (x ': xs) = LabelTy sym labels xs
  lensEqF  _ ps pl f = stepFun  (lensF  ps pl f) 
  lensEqTF _ ps pl f = stepTFun (lensTF ps pl f)

le
  :: forall sym f a. ( SymIndex sym (Labels a) (Elems a)
                     , HVector a
                     , Functor f
                     )
  => L sym
  -> (LabelTy sym (Labels a) (Elems a) -> f (LabelTy sym (Labels a) (Elems a)))
  -> a -> f a
le _ f v = H.inspect v
         $ lensF (Proxy :: Proxy sym) (Proxy :: Proxy (Labels a)) f H.construct

data L sym = L

instance (sym ~ sym') => IsLabel sym (L sym') where
  fromLabel = L

----------------------------------------

lev
  :: forall sym f a. ( SymIndex sym (Labels a) (Elems a)
                     , HVector a
                     , Functor f
                     )
  => L sym
  -> (V.Vector (LabelTy sym (Labels a) (Elems a)) -> f (V.Vector ((LabelTy sym (Labels a) (Elems a)))))
  -> DF a -> f (DF a)
lev _ f (DF i vs)
  = fmap (DF i)
  $ H.inspectF vs
  $ lensTF (Proxy @ sym) (Proxy @ (Labels a)) f H.constructF




-- newtype Label (sym :: Symbol) a = Label
--   { le :: forall f. Functor f
--        =3> (LabelTy sym (Labels a) (Elems a) -> f (LabelTy sym (Labels a) (Elems a)))
--        -> a -> f a
--   }
-- instance ( SymIndex sym (Labels a) (Elems a)
--          , HVector a
--          , sym ~ sym'
--          ) => IsLabel sym (Label sym' a) where
--   fromLabel = Label (labelLens (Proxy @ sym'))

----------------------------------------------------------------
-- Example
----------------------------------------------------------------

data Foo = Foo Int String
  deriving (Show,Generic)
instance HVector Foo
type instance Labels Foo = '[ "num", "txt" ]
