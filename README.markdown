monad-ran
=========

A large number of monads written in the form of right Kan extensions and "right Kan extension transformers". This includes the entire monad-transformer library, IO, ST s, and STM.

Some of these perform nicely on certain benchmarks.

Others could stand to be rewritten to provide strictness guarantees that are more inline with the behavior of the MTL.

More information on right Kan extensions in Haskell can be found here:

* <http://comonad.com/reader/2008/kan-extensions/>

* <http://comonad.com/reader/2008/kan-extensions-ii/>

* <http://comonad.com/reader/2008/kan-extension-iii/>
