-------------------------------------------------------------------------------------------
-- | 
-- Module       : Control.Functor.Pointed
-- Copyright    : 2008 Edward Kmett
-- License      : BSD
--
-- Maintainer   : Edward Kmett <ekmett@gmail.com>
-- Stability    : experimental
-- Portability  : portable
--
-------------------------------------------------------------------------------------------

module Control.Functor.Pointed 
    ( Pointed(..)
    ) where

import Control.Monad.Identity
import Control.Monad.Reader
import qualified Control.Monad.Writer.Lazy as LW
import qualified Control.Monad.Writer.Strict as SW
import qualified Control.Monad.State.Lazy as LS
import qualified Control.Monad.State.Strict as SS
import qualified Control.Monad.RWS.Lazy as LR
import qualified Control.Monad.RWS.Strict as SR
import Control.Monad.Error
import Control.Monad.Cont
import Control.Monad.List
import Data.Monoid

-- return
class Functor f => Pointed f where
    point :: a -> f a

instance Pointed Maybe where point = Just
instance Pointed [] where point = return

instance Pointed (Cont r) where point = return
instance Monad m => Pointed (ContT r m) where point = return

instance Pointed Identity where point = Identity

instance Pointed (Either a) where point = Right
instance (Error e, Monad m) => Pointed (ErrorT e m) where point = return

instance Pointed (Reader r) where point = return
instance Monad m => Pointed (ReaderT r m) where point = return
instance Pointed ((->)r) where point = return

instance Pointed (SS.State w) where point = return
instance Pointed (LS.State w) where point = return
instance Monad m => Pointed (SS.StateT w m) where point = return
instance Monad m => Pointed (LS.StateT w m) where point = return

instance Monoid w => Pointed (SW.Writer w) where point = return
instance Monoid w => Pointed (LW.Writer w) where point = return
instance (Monoid w, Monad m) => Pointed (SW.WriterT w m) where point = return
instance (Monoid w, Monad m) => Pointed (LW.WriterT w m) where point = return

instance Monoid w => Pointed (SR.RWS r w s) where point = return
instance Monoid w => Pointed (LR.RWS r w s) where point = return
instance (Monoid w, Monad m) => Pointed (SR.RWST r w s m) where point = return
instance (Monoid w, Monad m) => Pointed (LR.RWST r w s m) where point = return

instance Monad m => Pointed (ListT m) where point = return
