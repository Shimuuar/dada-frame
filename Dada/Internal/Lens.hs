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
-- Helper function for lookup by label
module Dada.Internal.Lens
  ( SymIndex(..)
  , Subtype(..)
  ) where

import           Data.Type.Equality       (type  (==))
import           Data.Typeable            (Proxy(..))
import           Data.Vector.HFixed       (Arity)
import           Data.Vector.HFixed.Class ( Fun(..),TFun(..)
                                          , constFun, constTFun, uncurryFun, uncurryTFun
                                          , lensWorkerF,lensWorkerTF,stepFun,stepTFun
                                          )
import           Data.Vector.HFixed.Cont  ( ContVec(..), cons, vector
                                          , ContVecF(..),consF,vectorF
                                          )
import qualified Data.Vector.HFixed.Cont as C
import GHC.TypeLits


----------------------------------------------------------------
-- Type preserving lenses
----------------------------------------------------------------

-- | Implementation of lookup in list by label
class SymIndex (sym :: Symbol) (labels :: [Symbol]) (xs :: [*]) where
  type LabelTy sym labels xs :: *
  -- | Simple getter
  getF   :: Proxy sym
         -> Proxy labels
         -> Fun xs (LabelTy sym labels xs)
  -- | Simple getter
  getTF  :: Proxy sym
         -> Proxy labels
         -> TFun f xs (f (LabelTy sym labels xs))
  -- | Helper for lens over tuple
  lensF  :: (Functor f)
         => Proxy sym
         -> Proxy labels
         -> (LabelTy sym labels xs -> f (LabelTy sym labels xs))
         -> (Fun xs r -> Fun xs (f r))
  -- | Helper for lens over tuple
  lensTF :: (Functor f)
         => Proxy sym
         -> Proxy labels
         -> (g (LabelTy sym labels xs) -> f (g (LabelTy sym labels xs)))
         -> (TFun g xs r -> TFun g xs (f r))

instance (SymIndexEq (sym == l) sym (l ': ls) xs) => SymIndex sym (l ': ls) xs where
  type LabelTy sym (l ': ls) xs = LabelEqTy (sym == l) sym (l ': ls) xs
  getF   = getEqF   (Proxy @ (sym == l))
  getTF  = getEqTF  (Proxy @ (sym == l))
  lensF  = lensEqF  (Proxy @ (sym == l))
  lensTF = lensEqTF (Proxy @ (sym == l))


-- | Helper type class for dispatching whether label is equal to list of labels
class SymIndexEq (eq :: Bool) (sym :: Symbol) (labels :: [Symbol]) (xs :: [*]) where
  type LabelEqTy eq sym labels xs :: *
  getEqF   :: Proxy eq
           -> Proxy sym
           -> Proxy labels
           -> Fun xs (LabelTy sym labels xs)
  getEqTF  :: Proxy eq
           -> Proxy sym
           -> Proxy labels
           -> TFun f xs (f (LabelTy sym labels xs))
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

instance ( Arity xs
         , LabelTy sym labels (x ': xs) ~ x
         ) => SymIndexEq 'True sym labels (x ': xs) where
  type LabelEqTy 'True sym labels (x ': xs) = x
  getEqF   _ _ _ = uncurryFun pure
  getEqTF  _ _ _ = uncurryTFun pure
  lensEqF  _ _ _ = lensWorkerF
  lensEqTF _ _ _ = lensWorkerTF

instance ( SymIndex sym ls xs
         , LabelTy sym (l ': ls) (x ': xs) ~ LabelTy sym ls xs
         ) => SymIndexEq 'False sym (l ': ls) (x ': xs) where
  type LabelEqTy 'False sym (l ': ls) (x ': xs) = LabelTy sym ls xs
  getEqF   _ p _   = constFun  $ getF   p (Proxy @ ls)
  getEqTF  _ p _   = constTFun $ getTF  p (Proxy @ ls)
  lensEqF  _ p _ f = stepFun   $ lensF  p (Proxy @ ls) f
  lensEqTF _ p _ f = stepTFun  $ lensTF p (Proxy @ ls) f


----------------------------------------------------------------
-- Subtyping
----------------------------------------------------------------

-- | Implementation of subtyping for labeled tuples
class Subtype (to :: [Symbol]) (xs :: [*]) (from :: [Symbol]) (ys :: [*]) where
  subtypeF  :: Proxy to
            -> Proxy from
            -> Fun ys (ContVec xs)
  subtypeTF :: Proxy to
            -> Proxy from
            -> TFun f ys (ContVecF xs f)

instance Arity ys => Subtype '[] '[] from ys where
  subtypeF  _ _ = pure C.mk0
  subtypeTF _ _ = pure (ContVecF unTFun)

instance ( Arity ys
         , SymIndex l from ys
         , x ~ LabelTy l from ys
         , Subtype ls xs from ys
         ) => Subtype (l ': ls) (x ': xs) from ys where
  subtypeF _ _ = do
    x  <- getF     (Proxy @ l)  (Proxy @ from)
    cv <- subtypeF (Proxy @ ls) (Proxy @ from)
    return $ cons x cv
  subtypeTF _ _ = do
    x  <- getTF     (Proxy @ l)  (Proxy @ from)
    cv <- subtypeTF (Proxy @ ls) (Proxy @ from)
    return $ consF x cv

