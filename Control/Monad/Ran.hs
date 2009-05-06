{-# LANGUAGE 
    RankNTypes, 
    FlexibleInstances, 
    FlexibleContexts, 
    TypeFamilies, 
    MultiParamTypeClasses, 
    MagicHash, 
    UnboxedTuples, 
    UndecidableInstances, 
    IncoherentInstances,
    TypeSynonymInstances, 
    TypeOperators #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Ran
-- Copyright   :  (c) Edward Kmett 2009
-- License     :  BSD-style
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (type families, GHC internals)
--
-- A fast right Kan extension based "Monad Transformer" that can be used to 
-- generate an efficient CPS representation from any combination of monads
-- from the Monad Transformer Library. 
--
-- To use, just wrap the type of your monad in 'Ran':
-- i.e. @Ran (StateT MyState ReaderT MyEnv IO) Bool@ 
-- and use @liftRan :: RanFunctor m => m a -> Ran m a@ and
-- and @lowerRan :: RanFunctor m => Ran m a -> m a@ to extract
-- your original monad.
-- 
-- This is really just a fancy way of saying that m a is isomorphic to 
-- forall o. (a -> f o) -> g o for some definition of f and g that is chosen by m.
-- In practice f and g are built up out of newtypes.
--
-- Ran m a is often more efficient than the straightforward monad m because
-- CPS transforming can yield additional optimization opportunities. There
-- are a few caveats to be aware of however. If you inspect the result
-- multiple times then 'Ran m a' may have to recompute its result for each
-- usage. To prevent this, either, use 'Ran m a' once, as in most straight-line
-- monadic code, or explicitly call 'lowerRan' on it and perform your repeated
-- tests against the unlifted monad.
--
-- Since Ran m is a data type that depends on type families, Ran cannot be
-- made an instance of 'MonadTrans', use 'liftRanT' or 'inRan' in place of 'lift'
-- as needed.
--
-----------------------------------------------------------------------------

module Control.Monad.Ran 
    ( -- * A right Kan extension monad transformer
      Ran(..)
      -- * Representing monads as right Kan extensions
    , RanApplicative
    , RanMonad
    , RanFunctor
    , G
    , H
    , liftRan
    , lowerRan
      -- * Ran Monad Transformers
    , RanTrans
    , liftRanT
    , outRan
    , inRan
      -- * Default definitions for common extensions
    , returnRanCodensity
    , bindRanCodensity
    , apRanCodensity
    , ranCodensity
    , codensityRan
    , liftRanCodensity
    , lowerRanCodensity
      -- * IO, ST s, STM
    , liftRanWorld
    , lowerRanWorld
      -- * The Yoneda Lemma is a right-Kan extension
    , Yoneda(..)
    , lowerYoneda
      -- * The codensity monad of a functor is a right-Kan extension
    , Codensity(..)
    , lowerCodensity
    , lowerCodensityApp
    ) where

-- All you need to do is find the right Kan extension.
--
-- TODO: MonadError e (Ran (StateT s m)),     MonadCont (Ran (StateT s m))
-- TODO: MonadError e (Ran (SS.StateT s m)),  MonadCont (Ran (SS.StateT s m))
-- TODO: MonadError e (Ran (WriterT w m)),    MonadCont (Ran (WriterT w m)),    Eq,Ord,Show,etc. instance for Ran (WriterT w m)
-- TODO: MonadError e (Ran (SW.WriterT w m)), MonadCont (Ran (SW.WriterT w m)), Eq,Ord,Show,etc. instance for Ran (SW.WriterT w m)
-- TODO: MonadError e (Ran (ReaderT e m)),    MonadCont (ReaderT e m), MonadFix (ReaderT e m), MonadPlus (ReaderT e m)

import Control.Applicative

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.List
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS

import qualified Control.Monad.Writer.Strict as SW
import qualified Control.Monad.State.Strict as SS
import qualified Control.Monad.RWS.Strict as SR

import Data.Monoid
import Data.Maybe (maybe)

import GHC.Prim
import GHC.IOBase hiding (liftIO)
import GHC.Conc
import GHC.ST

import Text.Read hiding (get, lift)
import Text.Show

-- | A right Kan extension transformer for a monad
data Ran m a = Ran { getRan :: forall b. (a -> G m b) -> H m b } 

class RanFunctor f where
    type G f :: * -> *
    type H f :: * -> *
    liftRan  :: f a -> Ran f a
    lowerRan :: Ran f a -> f a

class RanTrans t where
    liftRanT :: (RanFunctor m, RanFunctor (t m)) => Ran m a -> Ran (t m) a
    outRan :: (RanFunctor m, RanFunctor (t m)) => Ran (t m) a -> t (Ran m) a
    inRan :: (RanFunctor m, RanFunctor (t m)) => t (Ran m) a -> Ran (t m) a

instance RanFunctor f => Functor (Ran f) where
    fmap f m = Ran (\k -> getRan m (k . f))

class    (Monad (Ran f), Monad f, RanFunctor f) => RanMonad f 
instance (Monad (Ran f), Monad f, RanFunctor f) => RanMonad f

class    (Applicative (Ran f), Applicative f, RanFunctor f) => RanApplicative f 
instance (Applicative (Ran f), Applicative f, RanFunctor f) => RanApplicative f

returnRanCodensity :: (RanFunctor m, G m ~ H m) => a -> Ran m a
returnRanCodensity a = Ran (\k -> k a)

bindRanCodensity :: (RanFunctor m, G m ~ H m) => Ran m a -> (a -> Ran m b) -> Ran m b
bindRanCodensity (Ran m) k = Ran (\c -> m (\a -> getRan (k a) c))

apRanCodensity :: (RanFunctor m, G m ~ H m) => Ran m (a -> b) -> Ran m a -> Ran m b
apRanCodensity (Ran f) (Ran x) = Ran (\k -> f (\f' -> x (\x' -> k (f' x'))))

liftRanCodensity :: (RanFunctor m, G m ~ H m, Monad (G m)) => G m a -> Ran m a
liftRanCodensity f = Ran (f >>=)

lowerRanCodensity :: (RanFunctor m, G m ~ H m, Monad (G m)) => Ran m a -> G m a 
lowerRanCodensity (Ran f) = f return

mfixRanCodensity :: (RanFunctor m, G m ~ H m, MonadFix (G m)) => (a -> Ran m a) -> Ran m a
mfixRanCodensity f = liftRanCodensity $ mfix (lowerRanCodensity . f)

mfixRan :: (RanFunctor m, MonadFix m) => (a -> Ran m a) -> Ran m a
mfixRan f = liftRan $ mfix (lowerRan . f)

-- | Yoneda Identity a ~ Codensity Identity a ~ forall o. (a -> o) -> o
instance RanFunctor Identity where
    type G Identity = Identity
    type H Identity = Identity
    liftRan m = Ran (m >>=)
    lowerRan  = flip getRan Identity

instance Applicative (Ran Identity) where
    pure = returnRanCodensity
    (<*>) = apRanCodensity

instance Monad (Ran Identity) where
    return = returnRanCodensity
    (>>=) = bindRanCodensity

instance Eq a => Eq (Ran Identity a) where
    Ran f == Ran g = runIdentity (f Identity) == runIdentity (g Identity)

instance Ord a => Ord (Ran Identity a) where
    Ran f `compare` Ran g = runIdentity (f Identity) `compare` runIdentity (g Identity)

instance Show a => Show (Ran Identity a) where
    showsPrec d (Ran f) = showParen (d > 10) $
        showString "return " . showsPrec 11 (runIdentity (f Identity))
    
instance Read a => Read (Ran Identity a) where
    readPrec = parens $ prec 10 $ do
        Ident "return" <- lexP
        return <$> step readPrec

-- State s a ~ Codensity (Reader s) a ~ forall o. (a -> s -> o) -> s -> o
instance RanFunctor (State s) where
    type G (State s) = (->) s
    type H (State s) = (->) s
    liftRan (State g)  = Ran (\f -> uncurry f . g)
    lowerRan (Ran f)  = State (f (,))

instance Applicative (Ran (State s)) where
    pure = returnRanCodensity
    (<*>) = apRanCodensity

instance Monad (Ran (State s)) where
    return = returnRanCodensity
    (>>=) = bindRanCodensity

instance MonadState s (Ran (State s)) where
    get = Ran (\k s -> k s s)
    put s = Ran (\k _ -> k () s)

-- Embedded into CPS'd State rather than directly to avoid superfluous 'mappend mempty' calls for expensive monoids
-- forall o. (a -> w -> o) -> w -> o
instance Monoid w => RanFunctor (Writer w) where
    type G (Writer w) = (->) w
    type H (Writer w) = (->) w
    liftRan (Writer (a,w')) = Ran (\f w -> f a (w `mappend` w'))
    lowerRan (Ran f) = Writer (f (,) mempty)

instance Monoid w => Applicative (Ran (Writer w)) where
    pure = returnRanCodensity
    (<*>) = apRanCodensity

instance Monoid w => Monad (Ran (Writer w)) where
    return = returnRanCodensity
    (>>=) = bindRanCodensity

instance Monoid w => MonadWriter w (Ran (Writer w)) where
    tell w'        = Ran (\f w -> f () (w `mappend` w'))
    listen (Ran f) = Ran (\g -> f (\a w -> g (a,w) w))
    pass (Ran f)   = Ran (\g -> f (\(a,p) w -> g a (p w)))

newtype World w a = World { runWorld :: State# w -> a } 

liftRanWorld :: (G m ~ World w, H m ~ World w) => (State# w -> (# State# w, a #)) -> Ran m a
liftRanWorld f = Ran (\k -> World (\w -> case f w of (# w', a #) -> runWorld (k a) w'))

-- homegrown STret with flopped arguments
data STret' s a = STret' a (State# s)

lowerRanWorld :: (G m ~ World w, H m ~ World w) => Ran m a -> State# w -> (# State# w, a #)
lowerRanWorld (Ran r) w = case runWorld (r (World . STret')) w of 
    STret' b w'' -> (# w'', b #)

-- Represent IO as the codensity of the RealWorld
instance RanFunctor IO where
    type G IO = World RealWorld
    type H IO = World RealWorld
    liftRan (IO a) = liftRanWorld a
    lowerRan a     = IO (lowerRanWorld a)

instance Applicative (Ran IO) where
    pure = returnRanCodensity
    (<*>) = apRanCodensity

instance Monad (Ran IO) where
    return = returnRanCodensity
    (>>=) = bindRanCodensity

instance MonadIO (Ran IO) where
    liftIO = liftRan

instance MonadPlus (Ran IO) where
    mzero = liftIO mzero
    m `mplus` n = m `catchError` const n

instance MonadError IOError (Ran IO) where
    throwError = liftIO . ioError
    catchError m h = liftRan (lowerRan m `catch` (lowerRan . h))

instance MonadFix (Ran IO) where
    mfix = mfixRan

-- Represent ST s as the codensity of the world s
instance RanFunctor (ST s) where
    type G (ST s) = World s
    type H (ST s) = World s
    liftRan (ST s) = liftRanWorld s
    lowerRan r     = ST (lowerRanWorld r)

instance Applicative (Ran (ST s)) where
    pure = returnRanCodensity
    (<*>) = apRanCodensity

instance Monad (Ran (ST s)) where
    return = returnRanCodensity
    (>>=) = bindRanCodensity

instance MonadFix (Ran (ST s)) where
    mfix f = liftRan $ fixST (lowerRan . f)

-- todo make a MonadST class

-- Represent STM as the codensity of the RealWorld
instance RanFunctor STM where
    type G STM = World RealWorld
    type H STM = World RealWorld
    liftRan (STM s) = liftRanWorld s
    lowerRan r = STM (lowerRanWorld r)

instance Applicative (Ran STM) where
    pure = returnRanCodensity
    (<*>) = apRanCodensity

instance Monad (Ran STM) where
    return = returnRanCodensity
    (>>=) = bindRanCodensity

-- why is there no MonadFix instance for STM?
-- TODO: a MonadSTM class?

-- Yoneda-like embeddings

-- Yoneda lemma as a right Kan extension along the identity functor
instance RanFunctor (Yoneda f) where
    type G (Yoneda f) = Identity
    type H (Yoneda f) = f
    liftRan (Yoneda f) = Ran (\b -> f (runIdentity . b))
    lowerRan (Ran f) = Yoneda (\b -> f (Identity . b))

ranYoneda :: Ran (Yoneda f) a -> Yoneda f a
ranYoneda = lowerRan

yonedaRan :: Yoneda f a -> Ran (Yoneda f) a
yonedaRan = liftRan

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
    Ran f `catchError` h = Ran (\k -> f k `catchError` \e -> getRan (h e) k)

instance MonadFix m => MonadFix (Ran (Yoneda m)) where
    mfix f = Ran (\k -> liftM (runIdentity . k) $ mfix (\a -> getRan (f a) Identity))

-- Yoneda Endo a ~ forall o. (a -> o) -> o -> o ~ forall o. (a -> Identity o) -> Endo o
-- note Endo is not a Hask Functor and Maybe is not a Codensity monad, so this is trickier the what has come above

instance RanFunctor Maybe where
    type G Maybe = Identity
    type H Maybe = Endo
    liftRan = maybe mzero return
    lowerRan f = appEndo (getRan f (Identity . return)) mzero

instance Monad (Ran Maybe) where
    return x = Ran (\k -> Endo (\_ -> runIdentity (k x)))
    Ran g >>= f = Ran (\k -> Endo (\z -> appEndo (g (\a -> Identity (appEndo (getRan (f a) k) z))) z))
    fail _ = mzero

instance Applicative (Ran Maybe) where
    pure x = Ran (\k -> Endo (\_ -> runIdentity (k x)))
    Ran f <*> Ran g = Ran (\k -> Endo (\z -> appEndo (f (\f' -> Identity (appEndo (g (k . f')) z))) z))

instance MonadPlus (Ran Maybe) where
    mzero = Ran (\_ -> Endo id)
    Ran m `mplus` Ran n = Ran (\k -> Endo (\z -> appEndo (m k) (appEndo (n k) z)))

instance Monoid a => Monoid (Ran Maybe a) where
    mempty = mzero
    Ran a `mappend` Ran b = Ran (\k -> Endo (\z -> appEndo (a (\a' -> Identity (appEndo (b (k . mappend a')) z))) z))

instance MonadFix (Ran Maybe) where
    mfix f = m where
        m = f (unJust m)
        unJust (Ran r) = appEndo (r Identity) (error "mfix (Ran Maybe): Nothing")

instance Eq a => Eq (Ran Maybe a) where
    f == g = lowerRan f == lowerRan g

instance Ord a => Ord (Ran Maybe a) where
    f `compare` g = lowerRan f `compare` lowerRan g

instance Show a => Show (Ran Maybe a) where
    showsPrec d f = showParen (d > 10) $
        showString "liftRan " . showsPrec 11 (lowerRan f)
    
instance Read a => Read (Ran Maybe a) where
    readPrec = parens $ prec 10 $ do
        Ident "liftRan" <- lexP
        liftRan <$> step readPrec

type (:->) = ReaderT

data ErrorH e o  = ErrorH { getErrorH :: (e -> o) -> o } 

-- Yoneda (ErrorH e) ~ forall o. (a -> o) -> (e -> o) -> o ~ forall o. (a -> Identity o) -> (e -> o) -> o ~ forall o. (a -> Identity o) -> ErrorH e o
instance RanFunctor (Either e) where
    type G (Either e) = Identity
    type H (Either e) = ErrorH e
    liftRan (Right a) = Ran (\k -> ErrorH (\_ -> runIdentity (k a)))
    liftRan (Left x)  = Ran (\_ -> ErrorH (\e -> e x))
    lowerRan          = eitherRan Left Right

eitherRan :: (e -> b) -> (a -> b) -> Ran (Either e) a -> b
eitherRan f g (Ran m) = getErrorH (m (Identity . g)) f

instance Error e => Monad (Ran (Either e)) where
    return x = Ran (\k -> ErrorH (\_ -> runIdentity (k x)))
    fail = throwError . strMsg
    Ran g >>= f = Ran (\k -> ErrorH (\z -> getErrorH (g (\a -> Identity (getErrorH (getRan (f a) k) z))) z))

instance Error e => MonadError e (Ran (Either e)) where
    throwError x = Ran (\_ -> ErrorH (\e -> e x))
    Ran m `catchError` h = Ran (\k -> ErrorH (\z -> getErrorH (m k) (\e -> getErrorH (getRan (h e) k) z)))

instance Error e => MonadPlus (Ran (Either e)) where
    mzero = throwError noMsg
    Ran m `mplus` Ran n = Ran (\k -> ErrorH (\z -> getErrorH (m k) (\_ -> getErrorH (n k) z)))

instance Error e => MonadFix (Ran (Either e)) where
    mfix f = m where
        m = f (fromRight m)
        fromRight (Ran r) = getErrorH (r Identity) (\_ -> error "mfix (Ran (Either e)): empty mfix argument")

instance (Eq a, Eq b) => Eq (Ran (Either a) b) where
    f == g = lowerRan f == lowerRan g

instance (Ord a, Ord b) => Ord (Ran (Either a) b) where
    f `compare` g = lowerRan f `compare` lowerRan g

instance (Show a, Show b) => Show (Ran (Either a) b) where
    showsPrec d f = showParen (d > 10) $
        showString "liftRan " . showsPrec 11 (lowerRan f)
    
instance (Read a, Read b) => Read (Ran (Either a) b) where
    readPrec = parens $ prec 10 $ do
        Ident "liftRan" <- lexP
        liftRan <$> step readPrec

-- Anonymous Reader

-- Yoneda (Reader r) ~ forall o. (a -> o) -> r -> o ~ forall o. (a -> Identity o) -> r -> o
instance RanFunctor ((->)e) where
    type G ((->) e) = Identity
    type H ((->) e) = (->) e
    liftRan m = Ran (\f -> liftM (runIdentity . f) m)
    lowerRan (Ran f) = f Identity

instance Applicative (Ran ((->)e)) where
    pure = return
    Ran f <*> Ran g = Ran (\k r -> runIdentity (k (f Identity r (g Identity r))))

instance Monad (Ran ((->)e)) where
    return a = Ran (\f _ -> runIdentity (f a))
    Ran f >>= h = Ran (\k r -> getRan (h (f Identity r)) k r)
    
instance MonadReader e (Ran ((->)e)) where 
    ask = Ran (\k r -> runIdentity (k r))
    local f (Ran m) = Ran (\k r -> m k (f r))

instance Monoid m => Monoid (Ran ((->)e) m) where
    mempty = return mempty
    Ran a `mappend` Ran b = Ran (\k r -> runIdentity (k (a Identity r `mappend` b Identity r)))

-- Reader

-- Yoneda (Reader r) ~ forall o. (a -> o) -> r -> o ~ forall o. (a -> Identity o) -> r -> o
instance RanFunctor (Reader e) where
    type G (Reader e) = Identity
    type H (Reader e) = Reader e
    liftRan m = Ran (\f -> liftM (runIdentity . f) m)
    lowerRan (Ran f) = f Identity

instance Applicative (Ran (Reader e)) where
    pure = return
    Ran f <*> Ran g = Ran (\k -> Reader (\r -> runIdentity (k (runReader (f Identity) r (runReader (g Identity) r)))))

instance Monad (Ran (Reader e)) where
    return a = Ran (\f -> Reader (\_ -> runIdentity (f a)))
    Ran f >>= h = Ran (\k -> Reader (\r -> runReader(getRan (h (runReader (f Identity) r)) k) r))
    
instance MonadReader e (Ran (Reader e)) where 
    ask = Ran (\k -> Reader (\r -> runIdentity (k r)))
    local f (Ran m) = Ran (\k -> Reader (\r -> runReader (m k) (f r)))

instance Monoid m => Monoid (Ran (Reader e) m) where
    mempty = return mempty
    Ran a `mappend` Ran b = Ran (\k -> Reader (\r -> runIdentity (k (runReader (a Identity) r `mappend` runReader (b Identity) r))))



-- ReaderT 

-- ReaderT m a ~ forall o. (a -> G m o) -> ReaderT r (H m) o
instance RanFunctor m => RanFunctor (ReaderT e m) where
    type G (ReaderT e m) = G m
    type H (ReaderT e m) = e :-> H m
    liftRan (ReaderT f) = Ran (\k -> ReaderT (\e -> getRan (liftRan (f e)) k))
    lowerRan (Ran f) = ReaderT (\e -> lowerRan (Ran (\k -> runReaderT (f k) e)))

instance RanTrans (ReaderT e) where
    liftRanT (Ran m) = Ran (ReaderT . const . m)
    outRan (Ran m) = ReaderT (\e -> Ran (\k -> runReaderT (m k) e))
    inRan (ReaderT f) = Ran (\k -> ReaderT (\e -> getRan (f e) k))

instance RanMonad m => Applicative (Ran (ReaderT e m)) where
    pure = inRan . return
    f <*> g = inRan (outRan f `ap` outRan g)

instance (RanMonad m, MonadPlus (Ran m)) => Alternative (Ran (ReaderT e m)) where
    empty = inRan mzero
    f <|> g = inRan (outRan f `mplus` outRan g)

instance RanMonad m => Monad (Ran (ReaderT e m)) where
    return = inRan . return
    m >>= f = inRan (outRan m >>= outRan . f)

instance (RanMonad m, MonadState s (Ran m)) => MonadState s (Ran (ReaderT e m)) where
    get = inRan get
    put = inRan . put
    
instance RanMonad m => MonadReader r (Ran (ReaderT r m)) where
    ask     = inRan (ReaderT return)
    local f = inRan . local f . outRan

instance (RanMonad m, MonadWriter w (Ran m)) => MonadWriter w (Ran (ReaderT e m)) where
    tell = inRan . tell
    listen = inRan . listen . outRan
    pass = inRan . pass . outRan

instance (RanMonad m, MonadIO (Ran m)) => MonadIO (Ran (ReaderT e m)) where
    liftIO = inRan . liftIO

instance (RanMonad m, MonadPlus (Ran m)) => MonadPlus (Ran (ReaderT e m)) where
    mzero = inRan mzero
    a `mplus` b = inRan (outRan a `mplus` outRan b)

instance (RanMonad m, MonadFix (Ran m)) => MonadFix (Ran (ReaderT e m)) where
    mfix f = inRan $ mfix (outRan . f)


-- ErrorT 

-- @ErrorT e (Ran_g h) a = Ran_g (ErrorTH e h) a@

-- m (Either a b) ~ (Either a b -> G m o) -> H m o ~ forall o. (a -> G m o) -> (b -> G m o) -> H m o
data ErrorTH e m o = ErrorTH { getErrorTH :: (e -> G m o) -> H m o }
instance (RanFunctor m, Error e) => RanFunctor (ErrorT e m) where
    type G (ErrorT e m) = G m 
    type H (ErrorT e m) = ErrorTH e m
    liftRan (ErrorT m) = Ran (\k -> ErrorTH (\e -> getRan (liftRan m) (either e k)))
    lowerRan (Ran m) = ErrorT (lowerRan (Ran (\k -> getErrorTH (m (k . Right)) (k . Left))))

unwrapErrorT :: (RanFunctor m) => Ran (ErrorT a m) b -> Ran m (Either a b)
unwrapErrorT (Ran m) = Ran (\k -> getErrorTH (m (k . Right)) (k . Left))

wrapErrorT :: (RanFunctor m) => Ran m (Either a b) -> Ran (ErrorT a m) b
wrapErrorT (Ran m) = Ran (\k -> ErrorTH (\e -> m (either e k)))

instance RanTrans (ErrorT e) where
    liftRanT (Ran m) = Ran (\k -> ErrorTH (\_ -> m k))
    outRan (Ran m) = ErrorT (Ran (\k -> getErrorTH (m (k . Right)) (k . Left)))
    inRan (ErrorT m) = Ran (\k -> ErrorTH (\e -> getRan m (either e k)))

instance (RanMonad m, Error e) => Applicative (Ran (ErrorT e m)) where
    pure = inRan . return
    f <*> g = inRan (outRan f `ap` outRan g)

instance (RanMonad m, Error e, MonadPlus (Ran m)) => Alternative (Ran (ErrorT e m)) where
    empty = inRan mzero
    f <|> g = inRan (outRan f `mplus` outRan g)

instance (RanMonad m, Error e)  => Monad (Ran (ErrorT e m)) where
    return = inRan . return
    m >>= f = inRan (outRan m >>= outRan . f)

instance (RanMonad m, Error e, MonadState s (Ran m)) => MonadState s (Ran (ErrorT e m)) where
    get = inRan get
    put = inRan . put
    
instance (RanMonad m, Error e, MonadReader r (Ran m)) => MonadReader r (Ran (ErrorT e m)) where
    ask     = inRan ask
    local f = inRan . local f . outRan

instance (RanMonad m, Error e, MonadWriter w (Ran m)) => MonadWriter w (Ran (ErrorT e m)) where
    tell = inRan . tell
    listen = inRan . listen . outRan
    pass = inRan . pass . outRan

instance (RanMonad m, Error e, MonadRWS r w s (Ran m)) => MonadRWS r w s (Ran (ErrorT e m))

instance (RanMonad m, Error e, MonadIO (Ran m)) => MonadIO (Ran (ErrorT e m)) where
    liftIO = inRan . liftIO

instance (RanMonad m, Error e, MonadFix (Ran m)) => MonadFix (Ran (ErrorT e m)) where
    mfix f = inRan $ mfix (outRan . f)

instance (RanFunctor m, Eq (Ran m (Either a b))) => Eq (Ran (ErrorT a m) b) where
    f == g = unwrapErrorT f == unwrapErrorT g

instance (RanFunctor m, Ord (Ran m (Either a b))) => Ord (Ran (ErrorT a m) b) where
    f `compare` g = unwrapErrorT f `compare` unwrapErrorT g

instance (RanFunctor m, Show (Ran m (Either a b))) => Show (Ran (ErrorT a m) b) where
    showsPrec d f = showParen (d > 10) $
        showString "wrapErrorT " . showsPrec 11 (unwrapErrorT f)

instance (RanFunctor m, Read (Ran m (Either a b))) => Read (Ran (ErrorT a m) b) where
    readPrec = parens $ prec 10 $ do
        Ident "wrapErrorT" <- lexP
        wrapErrorT <$>  step readPrec

-- Lazy Writer as State

instance (Monoid w, RanFunctor m) => RanFunctor (WriterT w m) where
    type G (WriterT w m) = ReaderT w (G m)
    type H (WriterT w m) = ReaderT w (H m)

    liftRan (WriterT m) 
        = Ran (\k -> ReaderT (\w -> getRan (liftRan m) (\ ~(a,w') -> runReaderT (k a) (w `mappend` w'))))

    lowerRan (Ran m) 
        = WriterT (lowerRan (Ran (\k -> runReaderT (m (\a -> ReaderT (\w' -> k (a,w')))) mempty)))

instance Monoid w => RanTrans (WriterT w) where
    liftRanT (Ran m) = Ran (\k -> ReaderT (\w -> m (\a -> runReaderT (k a) w)))
    outRan (Ran m)   = WriterT (Ran (\k -> runReaderT (m (\a -> ReaderT (\w -> k (a,w)))) mempty))
    inRan (WriterT m) = Ran (\k -> ReaderT (\w -> getRan m (\ ~(a,w') -> runReaderT (k a) (w `mappend` w'))))
    
instance (Monoid w, RanMonad m) => Applicative (Ran (WriterT w m)) where
    pure = inRan . return
    f <*> g = inRan (outRan f `ap` outRan g)

instance (Monoid w, RanMonad m, MonadPlus (Ran m)) => Alternative (Ran (WriterT w m)) where
    empty = inRan mzero
    f <|> g = inRan (outRan f `mplus` outRan g)

instance (Monoid w, RanMonad m) => Monad (Ran (WriterT w m)) where
    return = inRan . return
    m >>= f = inRan (outRan m >>= outRan . f)

instance (Monoid w, RanMonad m, MonadState s (Ran m)) => MonadState s (Ran (WriterT w m)) where
    get = inRan get
    put = inRan . put

instance (Monoid w, RanMonad m) => MonadWriter w (Ran (WriterT w m)) where
    tell = inRan . tell
    listen = inRan . listen . outRan
    pass = inRan . pass . outRan

instance (Monoid w, RanMonad m, MonadReader e (Ran m)) => MonadReader e (Ran (WriterT w m)) where
    ask = inRan ask
    local f = inRan . local f . outRan

instance (Monoid w, RanMonad m, MonadIO (Ran m)) => MonadIO (Ran (WriterT w m)) where
    liftIO = inRan . liftIO

instance (Monoid w, RanMonad m, MonadPlus (Ran m)) => MonadPlus (Ran (WriterT w m)) where
    mzero = inRan mzero
    a `mplus` b = inRan (outRan a `mplus` outRan b)

instance (Monoid w, RanMonad m, MonadFix (Ran m)) => MonadFix (Ran (WriterT w m)) where
    mfix f = inRan $ mfix (outRan . f)

-- Strict Writer as State

instance (Monoid w, RanFunctor m) => RanFunctor (SW.WriterT w m) where
    type G (SW.WriterT w m) = ReaderT w (G m)
    type H (SW.WriterT w m) = ReaderT w (H m)

    liftRan (SW.WriterT m) 
        = Ran (\k -> ReaderT (\w -> getRan (liftRan m) (\ ~(a,w') -> runReaderT (k a) (w `mappend` w'))))

    lowerRan (Ran m) 
        = SW.WriterT (lowerRan (Ran (\k -> runReaderT (m (\a -> ReaderT (\w' -> k (a,w')))) mempty)))

instance Monoid w => RanTrans (SW.WriterT w) where
    liftRanT (Ran m) = Ran (\k -> ReaderT (\w -> m (\a -> runReaderT (k a) w)))
    outRan (Ran m)   = SW.WriterT (Ran (\k -> runReaderT (m (\a -> ReaderT (\w -> k (a,w)))) mempty))
    inRan (SW.WriterT m) = Ran (\k -> ReaderT (\w -> getRan m (\ ~(a,w') -> runReaderT (k a) (w `mappend` w'))))
    
instance (Monoid w, RanMonad m) => Applicative (Ran (SW.WriterT w m)) where
    pure = inRan . return
    f <*> g = inRan (outRan f `ap` outRan g)

instance (Monoid w, RanMonad m, MonadPlus (Ran m)) => Alternative (Ran (SW.WriterT w m)) where
    empty = inRan mzero
    f <|> g = inRan (outRan f `mplus` outRan g)

instance (Monoid w, RanMonad m) => Monad (Ran (SW.WriterT w m)) where
    return = inRan . return
    m >>= f = inRan (outRan m >>= outRan . f)

instance (Monoid w, RanMonad m, MonadState s (Ran m)) => MonadState s (Ran (SW.WriterT w m)) where
    get = inRan get
    put = inRan . put

instance (Monoid w, RanMonad m) => MonadWriter w (Ran (SW.WriterT w m)) where
    tell = inRan . tell
    listen = inRan . listen . outRan
    pass = inRan . pass . outRan

instance (Monoid w, RanMonad m, MonadReader e (Ran m)) => MonadReader e (Ran (SW.WriterT w m)) where
    ask = inRan ask
    local f = inRan . local f . outRan

instance (Monoid w, RanMonad m, MonadIO (Ran m)) => MonadIO (Ran (SW.WriterT w m)) where
    liftIO = inRan . liftIO

instance (Monoid w, RanMonad m, MonadPlus (Ran m)) => MonadPlus (Ran (SW.WriterT w m)) where
    mzero = inRan mzero
    a `mplus` b = inRan (outRan a `mplus` outRan b)

instance (Monoid w, RanMonad m, MonadFix (Ran m)) => MonadFix (Ran (SW.WriterT w m)) where
    mfix f = inRan $ mfix (outRan . f)

-- Lazy State

instance RanFunctor m => RanFunctor (StateT s m) where
    type G (StateT s m) = ReaderT s (G m)
    type H (StateT s m) = ReaderT s (H m)

    liftRan (StateT m) 
        = Ran (\k -> ReaderT (\s -> getRan (liftRan (m s)) (\ ~(a,s') -> runReaderT (k a) s')))
    lowerRan (Ran m) 
        = StateT (\s -> lowerRan (Ran (\k -> runReaderT (m (\a -> ReaderT (\s' -> k (a,s')))) s)))

instance RanTrans (StateT s) where
    liftRanT (Ran m) = Ran (\k -> ReaderT (\s -> m (\a -> runReaderT (k a) s)))
    outRan (Ran m)   = StateT (\s -> Ran (\k -> runReaderT (m (\a -> ReaderT (\s' -> k (a,s')))) s))
    inRan (StateT m) = Ran (\k -> ReaderT (\s -> getRan (m s) (\ ~(a,s') -> runReaderT (k a) s')))
    
instance RanMonad m => Applicative (Ran (StateT e m)) where
    pure = inRan . return
    f <*> g = inRan (outRan f `ap` outRan g)

instance (RanMonad m, MonadPlus (Ran m)) => Alternative (Ran (StateT s m)) where
    empty = inRan mzero
    f <|> g = inRan (outRan f `mplus` outRan g)

instance RanMonad m => Monad (Ran (StateT s m)) where
    return = inRan . return
    m >>= f = inRan (outRan m >>= outRan . f)

instance RanMonad m => MonadState s (Ran (StateT s m)) where
    get = inRan get
    put = inRan . put

instance (RanMonad m, MonadWriter w (Ran m)) => MonadWriter w (Ran (StateT s m)) where
    tell = inRan . tell
    listen = inRan . listen . outRan
    pass = inRan . pass . outRan

instance (RanMonad m, MonadReader e (Ran m)) => MonadReader e (Ran (StateT s m)) where
    ask = inRan ask
    local f = inRan . local f . outRan

instance (RanMonad m, MonadIO (Ran m)) => MonadIO (Ran (StateT s m)) where
    liftIO = inRan . liftIO

instance (RanMonad m, MonadPlus (Ran m)) => MonadPlus (Ran (StateT s m)) where
    mzero = inRan mzero
    a `mplus` b = inRan (outRan a `mplus` outRan b)

instance (RanMonad m, MonadFix (Ran m)) => MonadFix (Ran (StateT s m)) where
    mfix f = inRan $ mfix (outRan . f)

-- Strict State

instance RanFunctor m => RanFunctor (SS.StateT s m) where
    type G (SS.StateT s m) = ReaderT s (G m)
    type H (SS.StateT s m) = ReaderT s (H m)

    liftRan (SS.StateT m) 
        = Ran (\k -> ReaderT (\s -> getRan (liftRan (m s)) (\(a,s') -> runReaderT (k a) s')))
    lowerRan (Ran m) 
        = SS.StateT (\s -> lowerRan (Ran (\k -> runReaderT (m (\a -> ReaderT (\s' -> k (a,s')))) s)))

instance RanTrans (SS.StateT s) where
    liftRanT (Ran m)    = Ran (\k -> ReaderT (\s -> m (\a -> runReaderT (k a) s)))
    outRan (Ran m)      = SS.StateT (\s -> Ran (\k -> runReaderT (m (\a -> ReaderT (\s' -> k (a,s')))) s))
    inRan (SS.StateT m) = Ran (\k -> ReaderT (\s -> getRan (m s) (\(a,s') -> runReaderT (k a) s')))
    
instance RanMonad m => Applicative (Ran (SS.StateT e m)) where
    pure = inRan . return
    f <*> g = inRan (outRan f `ap` outRan g)

instance (RanMonad m, MonadPlus (Ran m)) => Alternative (Ran (SS.StateT s m)) where
    empty = inRan mzero
    f <|> g = inRan (outRan f `mplus` outRan g)

instance RanMonad m => Monad (Ran (SS.StateT s m)) where
    return = inRan . return
    m >>= f = inRan (outRan m >>= outRan . f)

instance RanMonad m => MonadState s (Ran (SS.StateT s m)) where
    get = inRan get
    put = inRan . put

instance (RanMonad m, MonadWriter w (Ran m)) => MonadWriter w (Ran (SS.StateT s m)) where
    tell = inRan . tell
    listen = inRan . listen . outRan
    pass = inRan . pass . outRan

instance (RanMonad m, MonadReader e (Ran m)) => MonadReader e (Ran (SS.StateT s m)) where
    ask = inRan ask
    local f = inRan . local f . outRan

instance (RanMonad m, MonadIO (Ran m)) => MonadIO (Ran (SS.StateT s m)) where
    liftIO = inRan . liftIO

instance (RanMonad m, MonadPlus (Ran m)) => MonadPlus (Ran (SS.StateT s m)) where
    mzero = inRan mzero
    a `mplus` b = inRan (outRan a `mplus` outRan b)

instance (RanMonad m, MonadFix (Ran m)) => MonadFix (Ran (SS.StateT s m)) where
    mfix f = inRan $ mfix (outRan . f)

-- Lazy RwS Transformer

newtype RWSTG w s m o = RWSTG { getRWSTG :: s -> w -> G m o } 
newtype RWSTH r w s m o = RWSTH { getRWSTH :: r -> s -> w -> H m o }

-- forall o. (a -> w -> s -> G m o) -> r -> w -> s -> H m o
instance (Monoid w, RanFunctor m) => RanFunctor (RWST r w s m) where
    type G (RWST r w s m) = RWSTG w s m
    type H (RWST r w s m) = RWSTH r w s m
    liftRan (RWST m) = Ran (\k -> RWSTH (\r s w -> getRan (liftRan (m r s)) (\ ~(a, s', w') -> getRWSTG (k a) s' (w `mappend` w'))))
    lowerRan (Ran m) = RWST (\r s -> lowerRan (Ran (\k -> getRWSTH (m (\a -> RWSTG (\s' w -> k (a, s', w)))) r s mempty)))

instance Monoid w => RanTrans (RWST r w s) where
    inRan (RWST m) = Ran (\k -> RWSTH (\r s w -> getRan (m r s) (\ ~(a, s', w') -> getRWSTG (k a) s' (w `mappend` w'))))
    outRan (Ran m) = RWST (\r s -> Ran (\k -> getRWSTH (m (\a -> RWSTG (\s' w -> k (a, s', w)))) r s mempty))
    liftRanT (Ran m) = Ran (\k -> RWSTH (\_ s w -> m (\a -> getRWSTG (k a) s w)))

instance (RanMonad m, Monoid w) => Applicative (Ran (RWST r w s m)) where
    pure = inRan . return
    f <*> g = inRan (outRan f `ap` outRan g)

instance (RanMonad m, MonadPlus (Ran m), Monoid w) => Alternative (Ran (RWST r w s m)) where
    empty = inRan mzero
    f <|> g = inRan (outRan f `mplus` outRan g)

instance (RanMonad m, Monoid w) => Monad (Ran (RWST r w s m)) where
    return = inRan . return
    m >>= f = inRan (outRan m >>= outRan . f)

instance (RanMonad m, Monoid w) => MonadState s (Ran (RWST r w s m)) where
    get = inRan get
    put = inRan . put

instance (RanMonad m, Monoid w) => MonadWriter w (Ran (RWST r w s m)) where
    tell = inRan . tell
    listen = inRan . listen . outRan
    pass = inRan . pass . outRan

instance (RanMonad m, Monoid w) => MonadReader r (Ran (RWST r w s m)) where
    ask = inRan ask
    local f = inRan . local f . outRan

instance (RanMonad m, Monoid w, MonadIO (Ran m)) => MonadIO (Ran (RWST r w s m)) where
    liftIO = inRan . liftIO

instance (RanMonad m, Monoid w, MonadPlus (Ran m)) => MonadPlus (Ran (RWST r w s m)) where
    mzero = inRan mzero
    a `mplus` b = inRan (outRan a `mplus` outRan b)

instance (RanMonad m, Monoid w, MonadFix (Ran m)) => MonadFix (Ran (RWST r w s m)) where
    mfix f = inRan $ mfix (outRan . f)

-- Strict RWS Transformer

-- forall o. (a -> w -> s -> G m o) -> r -> w -> s -> H m o
instance (Monoid w, RanFunctor m) => RanFunctor (SR.RWST r w s m) where
    type G (SR.RWST r w s m) = RWSTG w s m
    type H (SR.RWST r w s m) = RWSTH r w s m
    liftRan (SR.RWST m) = Ran (\k -> RWSTH (\r s w -> getRan (liftRan (m r s)) (\ (a, s', w') -> getRWSTG (k a) s' (w `mappend` w'))))
    lowerRan (Ran m) = SR.RWST (\r s -> lowerRan (Ran (\k -> getRWSTH (m (\a -> RWSTG (\s' w -> k (a, s', w)))) r s mempty)))

instance Monoid w => RanTrans (SR.RWST r w s) where
    inRan (SR.RWST m) = Ran (\k -> RWSTH (\r s w -> getRan (m r s) (\ (a, s', w') -> getRWSTG (k a) s' (w `mappend` w'))))
    outRan (Ran m) = SR.RWST (\r s -> Ran (\k -> getRWSTH (m (\a -> RWSTG (\s' w -> k (a, s', w)))) r s mempty))
    liftRanT (Ran m) = Ran (\k -> RWSTH (\_ s w -> m (\a -> getRWSTG (k a) s w)))

instance (RanMonad m, Monoid w) => Applicative (Ran (SR.RWST r w s m)) where
    pure = inRan . return
    f <*> g = inRan (outRan f `ap` outRan g)

instance (RanMonad m, MonadPlus (Ran m), Monoid w) => Alternative (Ran (SR.RWST r w s m)) where
    empty = inRan mzero
    f <|> g = inRan (outRan f `mplus` outRan g)

instance (RanMonad m, Monoid w) => Monad (Ran (SR.RWST r w s m)) where
    return = inRan . return
    m >>= f = inRan (outRan m >>= outRan . f)

instance (RanMonad m, Monoid w) => MonadState s (Ran (SR.RWST r w s m)) where
    get = inRan get
    put = inRan . put

instance (RanMonad m, Monoid w) => MonadWriter w (Ran (SR.RWST r w s m)) where
    tell = inRan . tell
    listen = inRan . listen . outRan
    pass = inRan . pass . outRan

instance (RanMonad m, Monoid w) => MonadReader r (Ran (SR.RWST r w s m)) where
    ask = inRan ask
    local f = inRan . local f . outRan

instance (RanMonad m, Monoid w, MonadIO (Ran m)) => MonadIO (Ran (SR.RWST r w s m)) where
    liftIO = inRan . liftIO

instance (RanMonad m, Monoid w, MonadPlus (Ran m)) => MonadPlus (Ran (SR.RWST r w s m)) where
    mzero = inRan mzero
    a `mplus` b = inRan (outRan a `mplus` outRan b)

instance (RanMonad m, Monoid w, MonadFix (Ran m)) => MonadFix (Ran (SR.RWST r w s m)) where
    mfix f = inRan $ mfix (outRan . f)




-- | The Codensity monad of a functor/monad generated by a functor

data Codensity f a = Codensity { getCodensity :: forall b. (a -> f b) -> f b }

instance Functor (Codensity k) where
    fmap f m = Codensity (\k -> getCodensity m (k . f))

instance Applicative (Codensity f) where
    pure x = Codensity (\k -> k x)
    Codensity f <*> Codensity x = Codensity (\k -> f (\f' -> x (k . f')))

instance Monad (Codensity f) where
    return x = Codensity (\k -> k x)
    Codensity m >>= k = Codensity 
        (\c -> m (\a -> getCodensity (k a) c))

instance MonadIO m => MonadIO (Codensity m) where
    liftIO = lift . liftIO

instance MonadPlus m => MonadPlus (Codensity m) where
    mzero = Codensity (const mzero)
    a `mplus` b = lift (lowerCodensity a `mplus` lowerCodensity b)

instance MonadReader r m => MonadReader r (Codensity m) where
    ask = lift ask
    local f m = Codensity (\c -> do r <- ask; local f (getCodensity m (local (const r) . c)))

instance MonadWriter w m => MonadWriter w (Codensity m) where
    tell = lift . tell
    listen = lift . listen . lowerCodensity
    pass = lift . pass . lowerCodensity

instance MonadState s m => MonadState s (Codensity m) where
    get = lift get
    put = lift . put

instance MonadRWS r w s m => MonadRWS r w s (Codensity m)

instance MonadFix f => MonadFix (Codensity f) where
    mfix f = lift $ mfix (lowerCodensity . f)

instance MonadError e m => MonadError e (Codensity m) where
    throwError = lift . throwError
    f `catchError` h = lift $ lowerCodensity f `catchError` (lowerCodensity . h)

instance MonadTrans Codensity where
    lift m = Codensity (m >>=)

lowerCodensity :: Monad m => Codensity m a -> m a
lowerCodensity = flip getCodensity return

lowerCodensityApp :: Applicative f => Codensity f a -> f a
lowerCodensityApp = flip getCodensity pure

-- The codensity monad as a right Kan extension of a functor along itself
-- Many state-like monads can be CPS transformed into a codensity monad.
instance RanFunctor (Codensity f) where
    type G (Codensity f) = f
    type H (Codensity f) = f
    liftRan  = codensityRan
    lowerRan = ranCodensity

ranCodensity :: Ran (Codensity f) a -> Codensity f a
ranCodensity (Ran f) = Codensity f

codensityRan :: Codensity f a -> Ran (Codensity f) a
codensityRan (Codensity f) = Ran f

instance Applicative (Ran (Codensity f)) where
    pure = returnRanCodensity
    (<*>) = apRanCodensity

instance Monad (Ran (Codensity f)) where
    return = returnRanCodensity
    (>>=) = bindRanCodensity

instance Alternative (Codensity f) => Alternative (Ran (Codensity f)) where
    empty = liftRan empty
    m <|> n = liftRan (lowerRan m <|> lowerRan n)

instance MonadPlus f => MonadPlus (Ran (Codensity f)) where
    mzero = liftRan mzero
    m `mplus` n = liftRan (lowerRan m `mplus` lowerRan n)

instance MonadIO f => MonadIO (Ran (Codensity f)) where
    liftIO f = Ran (liftIO f >>=)

instance MonadState s m => MonadState s (Ran (Codensity m)) where
    get = Ran (get >>=)
    put s = Ran (put s >>=)

instance MonadWriter w m => MonadWriter w (Ran (Codensity m)) where
    tell w = Ran (tell w >>=) 
    listen = liftRanCodensity . listen . lowerRanCodensity
    pass = liftRanCodensity . pass . lowerRanCodensity

instance MonadReader r m => MonadReader r (Ran (Codensity m)) where
    ask = Ran (ask >>=)
    local f = liftRanCodensity . local f . lowerRanCodensity

instance MonadRWS r w s m => MonadRWS r w s (Ran (Codensity m))
    
instance MonadFix m => MonadFix (Ran (Codensity m)) where
    mfix f = liftRanCodensity $ mfix (lowerRanCodensity . f)

instance MonadError e m => MonadError e (Ran (Codensity m)) where
    throwError e = Ran (throwError e >>=)
    m `catchError` h = liftRanCodensity (lowerRanCodensity m `catchError` (lowerRanCodensity . h))



-- | The Covariant Yoneda lemma applied to a functor. Note that @f@ need not be a Hask 'Functor'!

data Yoneda f a = Yoneda { getYoneda :: forall b. (a -> b) -> f b } 

lowerYoneda :: Yoneda f a -> f a 
lowerYoneda (Yoneda f) = f id

instance Functor (Yoneda f) where
    fmap f m = Yoneda (\k -> getYoneda m (k . f))

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
    local f = lift . local f . lowerYoneda 

instance MonadWriter w f => MonadWriter w (Yoneda f) where
    tell = lift . tell
    listen = lift . listen . lowerYoneda
    pass = lift . pass . lowerYoneda

instance MonadState s f => MonadState s (Yoneda f) where
    get = lift get
    put = lift . put

instance MonadIO f => MonadIO (Yoneda f) where
    liftIO = lift . liftIO

instance MonadRWS r w s f => MonadRWS r w s (Yoneda f)

instance MonadError e f => MonadError e (Yoneda f) where
    throwError = lift . throwError
    catchError m h = lift $ lowerYoneda m `catchError` (lowerYoneda . h)

instance MonadFix m => MonadFix (Yoneda m) where
    mfix f = lift $ mfix (lowerYoneda . f)
    
-- Cont

-- (a -> r) -> r ~ forall o. (a -> Const r o) -> Const r o
instance RanFunctor (Cont r) where
    type G (Cont r) = Const r
    type H (Cont r) = Const r
    liftRan (Cont f) = Ran (\k -> Const (f (getConst . k)))
    lowerRan (Ran f) = Cont (\k -> getConst (f (Const . k)))
    
instance Applicative (Ran (Cont r)) where
    pure = returnRanCodensity
    (<*>) = apRanCodensity

instance Monad (Ran (Cont r)) where
    return = returnRanCodensity
    (>>=) = bindRanCodensity

instance MonadCont (Ran (Cont r)) where
    callCC f = Ran (\c -> getRan (f (\a -> Ran (\_ -> Const (getConst (c a))))) c)

-- (a -> m r) -> m r 
data ConstT r f a = ConstT { getConstT :: f r } 
instance RanFunctor (ContT r m) where
    type G (ContT r m) = ConstT r m
    type H (ContT r m) = ConstT r m
    liftRan (ContT f) = Ran (\k -> ConstT (f (getConstT . k)))
    lowerRan (Ran f) = ContT (\k -> getConstT (f (ConstT . k)))

instance Monad (Ran (ContT r m)) where
    return = returnRanCodensity
    (>>=) = bindRanCodensity

instance MonadCont (Ran (ContT r m)) where
    callCC f = Ran (\c -> getRan (f (\a -> Ran (\_ -> ConstT (getConstT (c a))))) c)
