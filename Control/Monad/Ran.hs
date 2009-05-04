{-# LANGUAGE RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies, MultiParamTypeClasses, MagicHash, UnboxedTuples, UndecidableInstances  #-}
-- Finding the right Kan extension

module Control.Monad.Ran 
    ( 
      -- * The Yoneda Lemma
      Yoneda(..)
      -- * The codensity monad of a functor
    , Codensity(..)
      -- * A right Kan extension monad transformer
    , Ran(..)
      -- * Representing monads as right Kan extensions
    , RMonad
    , G
    , H
    , liftRan
    , lowerRan
    ) where

import Data.Monoid
import Data.Maybe (maybe)
import Control.Applicative
import Control.Functor.Pointed
import Control.Monad
import Control.Monad.Yoneda
import Control.Monad.Codensity
import Control.Monad.Identity
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS

import GHC.Prim
import GHC.IOBase hiding (liftIO)
import GHC.Conc
import GHC.ST


-- | A right Kan extension transformer for a monad
data Ran m a = Ran { getRan :: forall b. (a -> G m b) -> H m b } 

class RanIso f where
    type G f    :: * -> *
    type H f    :: * -> *
    liftRan       :: f a -> Ran f a
    lowerRan      :: Ran f a -> f a

instance RanIso f => Functor (Ran f) where
    fmap f m = Ran (\k -> getRan m (k . f))

returnCodensity :: (RanIso m, G m ~ H m) => a -> Ran m a
returnCodensity a = Ran (\k -> k a)

bindCodensity :: (RanIso m, G m ~ H m) => Ran m a -> (a -> Ran m b) -> Ran m b
bindCodensity (Ran m) k = Ran (\c -> m (\a -> getRan (k a) c))

class (Monad (Ran f), Monad f, RanIso f) => RMonad f 
instance (Monad (Ran f), Monad f, RanIso f) => RMonad f

class (Applicative (Ran f), Applicative f, RanIso f) => RApplicative f 
instance (Applicative (Ran f), Applicative f, RanIso f) => RApplicative f

-- The codensity monad as a right Kan extension of a functor along itself
instance RanIso (Codensity f) where
    type G (Codensity f) = f
    type H (Codensity f) = f
    liftRan (Codensity f) = Ran f
    lowerRan (Ran f) = Codensity f

ranCodensity :: Ran (Codensity f) a -> Codensity f a
ranCodensity = lowerRan

codensityRan :: Codensity f a -> Ran (Codensity f) a
codensityRan = liftRan

instance Pointed (Ran (Codensity f)) where
    point = codensityRan . point

instance Applicative (Ran (Codensity f)) where
    pure = codensityRan . pure
    m <*> n = liftRan (lowerRan m <*> lowerRan n)

instance Monad (Ran (Codensity f)) where
    return = liftRan . return
    m >>= k = liftRan (lowerRan m >>= lowerRan . k)

instance MonadPlus f => Alternative (Ran (Codensity f)) where
    empty = liftRan mzero
    m <|> n = liftRan (lowerRan m `mplus` lowerRan n)
    
instance MonadPlus f => MonadPlus (Ran (Codensity f)) where
    mzero = liftRan mzero
    m `mplus` n = liftRan (lowerRan m `mplus` lowerRan n)



-- TODO: the other instances for Ran (Codensity f)
-- MonadIO, MonadState, etc.

-- Yoneda Identity a ~ Codensity Identity a ~ forall o. (a -> o) -> o
instance RanIso Identity where
    type G Identity = Identity
    type H Identity = Identity
    liftRan m = Ran (m >>=)
    lowerRan = flip getRan Identity

instance Pointed (Ran Identity) where
    point = return

instance Applicative (Ran Identity) where
    pure = return
    (<*>) = ap

instance Monad (Ran Identity) where
    return a = Ran (\k -> k a)
    Ran m >>= k = Ran (\c -> m (\a -> getRan (k a) c))


newtype World w a = World { runWorld :: State# w -> a } 

-- homegrown STret with flopped arguments
data STret' s a = STret' a (State# s)

liftRanWorld :: (G m ~ World w, H m ~ World w) => (State# w -> (# State# w, a #)) -> Ran m a
liftRanWorld f = Ran (\k -> World (\w -> case f w of (# w', a #) -> runWorld (k a) w'))

-- viewpatterned to eliminate named temporaries:
-- liftRanWorld f = Ran (\k -> World (\(f -> (# w, (runWorld . k -> j) #)) -> j w))

lowerRanWorld :: (G m ~ World w, H m ~ World w) => Ran m a -> State# w -> (# State# w, a #)
lowerRanWorld (Ran r) w = case runWorld (r (World . STret')) w of 
    STret' b w'' -> (# w'', b #)

-- Represent IO as the codensity of the RealWorld
instance RanIso IO where
    type G IO = World RealWorld
    type H IO = World RealWorld
    liftRan (IO s) = liftRanWorld s
    lowerRan s = IO (lowerRanWorld s)

instance Applicative (Ran IO) where
    pure = return
    (<*>) = ap

instance Monad (Ran IO) where
    return = returnCodensity
    (>>=) = bindCodensity

instance MonadIO (Ran IO) where
    liftIO = liftRan

-- Represent ST s as the codensity of the world s
instance RanIso (ST s) where
    type G (ST s) = World s
    type H (ST s) = World s
    liftRan (ST s) = liftRanWorld s
    lowerRan r = ST (lowerRanWorld r)

instance Applicative (Ran (ST s)) where
    pure = return
    (<*>) = ap

instance Monad (Ran (ST s)) where
    return = returnCodensity
    (>>=) = bindCodensity

-- todo make a MonadST class

-- Represent STM as the codensity of the RealWorld
instance RanIso STM where
    type G STM = World RealWorld
    type H STM = World RealWorld
    liftRan (STM s) = liftRanWorld s
    lowerRan r = STM (lowerRanWorld r)

instance Applicative (Ran STM) where
    pure = return
    (<*>) = ap

instance Monad (Ran STM) where
    return = returnCodensity
    (>>=) = bindCodensity

-- TODO: make a MonadSTM class

-- Yoneda Endo a ~ forall o. (a -> o) -> o -> o ~ forall o. (a -> Identity o) -> Endo o
-- note Endo is not a Hask Functor!
instance RanIso Maybe where
    type G Maybe = Identity
    type H Maybe = Endo
    liftRan Nothing  = mzero
    liftRan (Just x) = return x
    lowerRan f = appEndo (getRan f (Identity . return)) mzero

instance Monad (Ran Maybe) where
    return x = Ran (\k -> Endo (\_ -> runIdentity (k x)))
    Ran g >>= f = Ran (\k -> Endo (\z -> appEndo (g (\a -> Identity (appEndo (getRan (f a) k) z))) z))
    fail _ = mzero

instance MonadPlus (Ran Maybe) where
    mzero = Ran (\_ -> Endo id)
--  Ran m `mplus` n = Ran (\k -> Endo (\z -> appEndo (getRan m k) (appEndo (getRan n k) z)))

instance Monoid (Ran Maybe a) where
    mempty = mzero
    mappend = mplus

type (:->) = ReaderT

data ErrorH b r  = ErrorH { getErrorH :: (b -> r) -> r } 
data ErrorTH b m r = ErrorTH { getErrorTH :: (b -> G m r) -> H m r }


-- Yoneda (ErrorH e) ~ forall o. (a -> o) -> (e -> o) -> o
instance Error e => RanIso (Either e) where
    type G (Either e) = Identity
    type H (Either e) = ErrorH e
    liftRan (Right x) = Ran (\k -> ErrorH (\_ -> runIdentity (k x)))
    liftRan (Left x) = Ran (\_ -> ErrorH (\e -> e x))
    lowerRan (Ran f) = getErrorH (f (Identity . Right)) Left

instance Error e => Monad (Ran (Either e)) where
    return x = Ran (\k -> ErrorH (\_ -> runIdentity (k x)))
    fail = throwError . strMsg
--  m >>= k = Ran (\c -> ErrorH (\e -> m (\a -> getErrorH (getRan (k a) c) e)))

instance Error e => MonadError e (Ran (Either e)) where
    throwError x = Ran (\_ -> ErrorH (\e -> e x))
--  catchError f h = Ran (\k -> ErrorH (\e -> getErrorH (getRan f k) e))

instance Error e => MonadPlus (Ran (Either e)) where
    mzero = throwError noMsg
        
{-
-- Yoneda (ErrorTH b m)
-- forall o. (a -> G m o) -> (b -> G m o) -> H m o
-- forall o. (a -> G m o) -> H m ((b -> G m o) -> o) ?
instance (RMonad m, Error b) => RMonad (ErrorT b m) where
    type G (ErrorT b m) = G m 
    type H (ErrorT b m) = ErrorTH b m


-- Codensity f
-- forall o. (a -> f o) -> f o 
instance RMonad (Codensity f) where
    type G (Codensity f) = f
    type H (Codensity f) = f
    liftRan (Codensity f) = Ran f
    lowerRan (Ran f) = Codensity f

-- Yoneda (Reader r)
-- forall o. (a -> o) -> r -> o
instance RMonad (Reader e) where
    type G (Reader e) = Identity
    type H (Reader e) = Reader e
    liftRan m = Ran (\f -> liftM (runIdentity . f) m)
    lowerRan (Ran f) = f Identity

-- embedded as CPS'd State to avoid superfluous 'mappend mempty' calls
-- specialized Codensity (Reader w)
-- forall o. (a -> w -> o) -> w -> o
instance Monoid w => RMonad (Writer w) where
    type G (Writer w) = (->) w
    type H (Writer w) = (->) w
    liftRan (Writer (a,w'))  = Ran (\f w -> f a (w `mappend` w'))
    lowerRan (Ran f) = Writer (f (,) mempty)
    -- forall o. (a -> w -> o) -> o
    -- type H (Writer w) = Identity

-- Codensity (Reader s)
-- forall o. (a -> s -> o) -> s -> o
instance RMonad (State s) where
    type G (State s) = (->) s
    type H (State s) = (->) s
    liftRan (State g)  = Ran (\f -> uncurry f . g)
    lowerRan (Ran f)  = State (f (,))

-- Codensity (Const r)
-- (a -> r) -> r
instance RMonad (Cont r) where
    type G (Cont r) = Const r
    type H (Cont r) = Const r

-- forall o. (a -> G m o) -> r -> H m o 
instance RMonad m => RMonad (ReaderT e m) where
    type G (ReaderT e m) = G m
    type H (ReaderT e m) = e :-> H m

-- forall o. (a -> w -> G m o) -> H m o
-- forall o. (a -> G m (w -> o)) -> H m (w -> o) ?
instance (Monoid w, RMonad m) => RMonad (WriterT w m) where
    type G (WriterT w m) = w :-> G m
    type H (WriterT w m) = H m

-- forall o. (a -> s -> G m o) -> s -> H m o 
-- forall o. (a -> G m (s -> o)) -> H m (s -> o) ?
instance RMonad m => RMonad (StateT s m) where
    type G (StateT s m) = s :-> G m
    type H (StateT s m) = s :-> H m

-- (a -> G m r) -> H m r
data ConstT r f a = ConstT { getConstT :: f r } 
instance RMonad m => RMonad (ContT r m) where
    type G (ContT r m) = ConstT r (G m)
    type H (ContT r m) = ConstT r (H m)
-}



-- Yoneda lemma as a right Kan extension along the identity functor
instance RanIso (Yoneda f) where
    type G (Yoneda f) = Identity
    type H (Yoneda f) = f
    liftRan (Yoneda f) = Ran (\b -> f (runIdentity . b))
    lowerRan (Ran f) = Yoneda (\b -> f (Identity . b))

ranYoneda :: Ran (Yoneda f) a -> Yoneda f a
ranYoneda = lowerRan

yonedaRan :: Yoneda f a -> Ran (Yoneda f) a
yonedaRan = liftRan

instance Pointed f => Pointed (Ran (Yoneda f)) where
    point = liftRan . point

instance Applicative f => Applicative (Ran (Yoneda f)) where
    pure = liftRan . pure
    m <*> n = liftRan (lowerRan m <*> lowerRan n)

instance Alternative f => Alternative (Ran (Yoneda f)) where
    empty = liftRan empty
    m <|> n = liftRan (lowerRan m <|> lowerRan n) 

instance Monad f => Monad (Ran (Yoneda f)) where
    return = liftRan . return
    m >>= k = liftRan (lowerRan m >>= lowerRan . k)

instance MonadPlus f => MonadPlus (Ran (Yoneda f)) where
    mzero = liftRan mzero
    m `mplus` n = liftRan (lowerRan m `mplus` lowerRan n)

instance MonadReader r f => MonadReader r (Ran (Yoneda f)) where
    ask = liftRan ask
    local f = liftRan . local f . lowerRan

instance MonadWriter w f => MonadWriter w (Ran (Yoneda f)) where
    tell = liftRan . tell
    listen = liftRan . listen . lowerRan
    pass = liftRan . pass . lowerRan

instance MonadState s f => MonadState s (Ran (Yoneda f)) where
    get = liftRan get
    put = liftRan . put

instance MonadIO f => MonadIO (Ran (Yoneda f)) where
    liftIO = liftRan . liftIO

instance MonadRWS r w s f => MonadRWS r w s (Ran (Yoneda f))

instance MonadError e f => MonadError e (Ran (Yoneda f)) where
    throwError = liftRan . throwError
--    Ran f `catchError` h = Yoneda (liftRan . (`catchError` h) . f)

-- instance MonadFix m => MonadFix (Ran (Yoneda m)) where
--    mfix = liftRan . mfix . lowerRan

