-- Finding the right Kan extension

module Control.Monad.Ran 
    ( Yoneda(..)
    , Codensity(..)
    , Ran(..)
    , RMonad
    , G
    , H
    , toRan
    , fromRan
    ) where

import Data.Monoid
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS

data Yoneda f a = Yoneda { getYoneda :: forall b. (a -> b) -> f b } 

instance Functor (Yoneda f) where
    fmap f m = Yoneda (\k -> getYoneda m (k . f))

instance Applicative f => Applicative (Yoneda f) where
    pure a = Yoneda (\f -> pure (f a))
    m <*> n = Yoneda (\f -> getYoneda m (f .) <*> getYoneda n id)

instance Monad f => Monad (Yoneda f) where
    return a = Yoneda (\f -> return (f a))
    m >>= k = Yoneda (\f -> getYoneda m id >>= \a -> getYoneda (k a) f)

instance MonadTrans Yoneda where
    lift m = Yoneda (\f -> liftM f m)

data Codensity f a = Codensity { getCodensity :: forall b. (a -> f b) -> f b }

instance Functor (Codensity k) where
    fmap f m = Codensity (\k -> getCodensity m (k . f))

instance Applicative (Codensity f) where
    pure = return
    (<*>) = ap

instance Monad (Codensity f) where
    return x = Codensity (\k -> k x)
    m >>= k = Codensity (\c -> getCodensity m (\a -> getCodensity (k a) c))

instance MonadTrans Codensity where
    lift m = Codensity (m >>=)

runCodensity :: Monad m => Codensity m a -> m a
runCodensity = flip getCodensity return

runCodensityApp :: Applicative f => Codensity f a -> f a
runCodensityApp = flip getCodensity pure

-- .. Pointed

data Ran m a = Ran { getRan :: forall b. (a -> G m b) -> H m b } 

class Monad f => RMonad f where
    type G f    :: * -> *
    type H f    :: * -> *
    toRan      :: f a -> Ran f a
    fromRan    :: Ran f a -> f a

--class RMonadTrans t where
--    liftR :: RMonad m => RanT m a -> RanT (t m) a

-- utility bifunctors for definitions below
type Hom = (->)
type (:->) = ReaderT

data ErrorH b r  = ErrorH { getErrorH :: (b -> r) -> r } 
data ErrorTH b m r = ErrorTH { getErrorTH :: (b -> G m r) -> H m r }

-- Yoneda Identity
-- forall o. (a -> o) -> o
instance RMonad Identity where
    type G Identity = Identity
    type H Identity = Identity
    toRan m = Ran (m >>=)
    fromRan = flip getRan Identity

-- Yoneda Endo
-- forall o. (a -> o) -> o -> o
instance RMonad Maybe where
    type G Maybe = Identity
    type H Maybe = Endo
    toRan (Just x) = Ran (\k -> Endo (\_ -> runIdentity (k x)))
    toRan Nothing = Ran (\_ -> Endo id)
    fromRan (Ran f) = appEndo (f (Identity . Just)) Nothing

-- Yoneda (ErrorH b)
-- forall o. (a -> o) -> (b -> o) -> o
instance Error b => RMonad (Either b) where
    type G (Either b) = Identity
    type H (Either b) = ErrorH b
    toRan (Right x) = Ran (\k -> ErrorH (\_ -> runIdentity (k x)))
    toRan (Left x) = Ran (\_ -> ErrorH (\k -> k x))
    fromRan (Ran f) = getErrorH (f (Identity . Right)) Left

-- Yoneda (ErrorTH b m)
-- forall o. (a -> G m o) -> (b -> G m o) -> H m o
instance (RMonad m, Error b) => RMonad (ErrorT b m) where
   type G (ErrorT b m) = G m 
   type H (ErrorT b m) = ErrorTH b m

-- Yoneda f
-- forall o. (a -> o) -> f o 
instance Monad f => RMonad (Yoneda f) where
    type G (Yoneda f) = Identity
    type H (Yoneda f) = f

-- Codensity f
-- forall o. (a -> f o) -> f o 
instance RMonad (Codensity f) where
    type G (Codensity f) = f
    type H (Codensity f) = f

-- Yoneda (Reader r)
-- forall o. (a -> o) -> r -> o
instance RMonad (Reader e) where
    type G (Reader e) = Identity
    type H (Reader e) = Hom e

-- embedded as CPS'd State to avoid superfluous 'mappend mempty' calls
-- specialized Codensity (Reader w)
-- forall o. (a -> w -> o) -> w -> o
instance Monoid w => RMonad (Writer w) where
    type G (Writer w) = Hom w
    type H (Writer w) = Hom w
    -- forall o. (a -> w -> o) -> o
    -- type H (Writer w) = Identity

-- Codensity (Reader s)
-- forall o. (a -> s -> o) -> s -> o
instance RMonad (State s) where
    type G (State s) = Hom s
    type H (State s) = Hom s

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
instance (Monoid w, RMonad m) => RMonad (WriterT w m) where
    type G (WriterT w m) = w :-> G m
    type H (WriterT w m) = H m

-- forall o. (a -> s -> G m o) -> s -> H m o 
instance RMonad m => RMonad (StateT s m) where
    type G (StateT s m) = s :-> G m
    type H (StateT s m) = s :-> H m

-- (a -> G m r) -> H m r
data ConstT r f a = ConstT { getConstT :: f r } 
instance RMonad m => RMonad (ContT r m) where
    type G (ContT r m) = ConstT r (G m)
    type H (ContT r m) = ConstT r (H m)
