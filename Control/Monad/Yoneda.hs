{-# LANGUAGE Rank2Types, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
-- Finding the right Kan extension

module Control.Monad.Yoneda
    ( -- * The Yoneda Lemma
      Yoneda(..)
    , runYoneda
    ) where

import Data.Monoid
import Data.Maybe (maybe)
import Control.Applicative
import Control.Functor.Pointed
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Fix
import Control.Monad.Cont.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.RWS.Class

data Yoneda f a = Yoneda { getYoneda :: forall b. (a -> b) -> f b } 

instance Functor (Yoneda f) where
    fmap f m = Yoneda (\k -> getYoneda m (k . f))

instance Pointed f => Pointed (Yoneda f) where
    point a = Yoneda (\f -> point (f a))

instance Applicative f => Applicative (Yoneda f) where
    pure a = Yoneda (\f -> pure (f a))
    m <*> n = Yoneda (\f -> getYoneda m (f .) <*> getYoneda n id)

instance Alternative f => Alternative (Yoneda f) where
    empty = Yoneda (const empty)
    Yoneda m <|> Yoneda n = Yoneda (\f -> m f <|> n f)

instance Monad f => Monad (Yoneda f) where
    return a = Yoneda (\f -> return (f a))
    m >>= k = Yoneda (\f -> getYoneda m id >>= \a -> getYoneda (k a) f)

instance MonadPlus f => MonadPlus (Yoneda f) where
    mzero = Yoneda (const mzero)
    Yoneda m `mplus` Yoneda n = Yoneda (\f -> m f `mplus` n f)

instance MonadTrans Yoneda where
    lift m = Yoneda (\f -> liftM f m)

instance MonadReader r f => MonadReader r (Yoneda f) where
    ask = lift ask
    local f = lift . local f . runYoneda 

instance MonadWriter w f => MonadWriter w (Yoneda f) where
    tell = lift . tell
    listen = lift . listen . runYoneda
    pass = lift . pass . runYoneda

instance MonadState s f => MonadState s (Yoneda f) where
    get = lift get
    put = lift . put

instance MonadIO f => MonadIO (Yoneda f) where
    liftIO = lift . liftIO

instance MonadRWS r w s f => MonadRWS r w s (Yoneda f)

instance MonadError e f => MonadError e (Yoneda f) where
    throwError = lift . throwError

instance MonadFix m => MonadFix (Yoneda m)
    
runYoneda :: Yoneda f a -> f a 
runYoneda (Yoneda f) = f id

