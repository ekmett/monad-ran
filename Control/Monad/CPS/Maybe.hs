{-# LANGUAGE Rank2Types #-}

module Control.Monad.CPS.Maybe
    ( Maybe'(..)
    , maybe'
    ) where

newtype Maybe' a = Maybe' { getMaybe' :: forall o. (a -> o) -> o -> o } 

instance Functor Maybe' where
    fmap f (Maybe' m) = Maybe' (\k -> m (k . f))

instance Monad Maybe' where
    return a = Maybe' (\k _ -> k a)
    Maybe' g >>= f = Maybe' (\k z -> g (\a -> getMaybe' (f a) k z) z)
    
maybe' :: a -> (b -> a) -> Maybe' b -> a
maybe' a b (Maybe' m) = m b a
