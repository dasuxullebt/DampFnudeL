{-# LANGUAGE BangPatterns #-}

module DiffStackT where

import Data.Maybe

import qualified Data.Array.Diff as D
import Data.Maybe

-- DS1
data DiffStack a = DiffStack
    { size :: Int
    , sp :: Int
    , array :: D.DiffArray Int (Maybe a)
    }
-- DS2
                 
initialStackSize :: Int
initialStackSize = 32769
                 
newDiffStack :: DiffStack a
newDiffStack = DiffStack
               { size = initialStackSize
               , sp = 0
               , array = D.listArray (0, initialStackSize - 1) (repeat Nothing)
               }

extend :: DiffStack a -> DiffStack a
extend da =
    let newsize = 2 * (size da)
    in DiffStack { size = newsize
                 , sp = sp da
                 , array = D.listArray (0, newsize - 1)
                           ((map ((array da) D.!) [0..(size da)-1])
                            ++ (repeat Nothing))
                 }

reset :: DiffStack a -> DiffStack a
reset da = DiffStack { size = size da
                     , sp = 0
                     , array = array da
                     }

push :: a -> DiffStack a -> DiffStack a
push a ds =
    let dt = if size ds > sp ds then ds else extend ds
    in DiffStack { size = size dt
                 , sp = 1 + sp dt
                 , array = (array dt) D.// [(sp dt, Just a)]
                 }

nth_maybe :: Int -> DiffStack a -> (Maybe a, DiffStack a)
nth_maybe i ds = if i >= sp ds then (Nothing, ds)
                 else ((array ds) D.! ((sp ds) - i - 1), ds)

nth :: Int -> DiffStack a -> a -> (a, DiffStack a)
nth i ds q = case nth_maybe i ds of
               (Nothing, ds2) -> (q, ds2)
               (Just k, ds2) -> (k, ds2)

-- TL1
readArray arr index = (arr D.! index, arr)
                      
toList' :: D.DiffArray Int (Maybe a) -> Int -> Int ->
           [a] -> ([a], D.DiffArray Int (Maybe a))
toList' ds n sp l =
    if n < sp
    then case DiffStackT.readArray ds n of
           (Nothing, ds_) -> toList' ds_ (n+1) sp l
           (Just x, ds_) -> toList' ds_ (n+1) sp (x : l)
    else (l, ds)

toList :: DiffStack a -> ([a], DiffStack a)
toList ds = let (l, narr) = toList' (array ds) 0 (sp ds) []
                    in (l, DiffStack { size = size ds
                                     , sp = sp ds
                                     , array = narr
                                     })
--TL2
toReverseList :: DiffStack a -> ([a], DiffStack a)
toReverseList ds = let (l, dt) = toList ds
            in (reverse l, dt)


{-

import System.IO.Unsafe
import Data.IORef
import Data.Array.IO
import Data.Maybe

data LinearArray_ a = Invalid | Valid (IOArray Int a)
type LinearArray a = IORef (LinearArray_ a)
newArray :: (Int, Int) -> a -> LinearArray a
newArray (start, end) init =
    unsafePerformIO $
    do
      t <- Data.Array.IO.newArray (start, end) init
      r <- newIORef (Valid t)
      return $ r

overwriteArray :: LinearArray a -> Int -> a -> LinearArray a
overwriteArray old index value =
    unsafePerformIO $
    do ior <- readIORef old
       case ior of
         Invalid -> error "nonlinear use of linear array!"
         Valid a -> do
                  writeArray a index value
                  writeIORef old Invalid
                  new <- newIORef (Valid a)
                  return new


    unsafePerformIO $
    do ior <- readIORef arr
       case ior of
         Invalid -> error "nonlinear use of linear array!"
         Valid a -> do
                  r <- Data.Array.IO.readArray a index
                  return (r, arr)

arrayCopy :: Int -> LinearArray a -> Int -> LinearArray a -> Int -> (LinearArray a, LinearArray a)
arrayCopy _ src _ dst 0 = (dst, src)
arrayCopy srcstart src dststart dst n =
    let !(rd, src_) = DiffStack.readArray src srcstart
    in
      arrayCopy (1 + srcstart) src_ (1 + dststart)
                    (overwriteArray dst dststart rd)
                    (n - 1)

data DiffStack a = DiffStack
    { size :: Int
    , sp :: Int
    , array :: LinearArray (Maybe a)
    }

initialStackSize :: Int
initialStackSize = 32769

newDiffStack :: DiffStack a
newDiffStack = DiffStack
               { size = initialStackSize
               , sp = 0
               , array = DiffStack.newArray (0, initialStackSize - 1) Nothing
               }

extend :: DiffStack a -> DiffStack a
extend da =
    let !newsize = 2 * (size da)
        !nar1 = (DiffStack.newArray (0, newsize - 1) Nothing) :: LinearArray (Maybe a)
        !(narf, _) = arrayCopy 0 (array da) 0 nar1 (size da)
    in DiffStack { size = newsize
                 , sp = sp da
                 , array = narf
                 }

reset :: DiffStack a -> DiffStack a
reset da = DiffStack { size = size da
                     , sp = 0
                     , array = array da
                     }


push :: a -> DiffStack a -> DiffStack a
push a !ds =
    let dt = if size ds > sp ds then ds else extend ds
        !newarray = overwriteArray (array dt) (sp dt) (Just a)
    in DiffStack { size = size dt
                 , sp = 1 + sp dt
                 , array = newarray
                 }

nth_maybe :: Int -> DiffStack a -> (Maybe a, DiffStack a)
nth_maybe i ds = if i >= sp ds then (Nothing, ds)
                 else
                     let !(x, narr) = DiffStack.readArray (array ds) ((sp ds) - i - 1)
                     in (x, DiffStack { size = size ds
                                      , sp = sp ds
                                      , array = narr
                                      })

nth :: Int -> DiffStack a -> a -> (a, DiffStack a)
nth i ds q = case nth_maybe i ds of
               (Nothing, x) -> (q, x)
               (Just k, x) -> (k, x)

toReverseList' :: LinearArray (Maybe a) -> Int -> Int -> [a] -> ([a], LinearArray (Maybe a))
toReverseList' !ds n sp l = if n < sp
                         then case DiffStack.readArray ds n of
                                (Nothing, ds_) -> toReverseList' ds_ (n+1) sp l
                                (Just x, ds_) -> toReverseList' ds_ (n+1) sp (x : l)
                         else (l, ds)

toReverseList :: DiffStack a -> ([a], DiffStack a)
toReverseList !ds = let (l, narr) = toReverseList' (array ds) 0 (sp ds) []
                    in (l, DiffStack { size = size ds
                                     , sp = sp ds
                                     , array = narr
                                     })

toList :: DiffStack a -> ([a], DiffStack a)
toList ds = let (l, dt) = toReverseList ds
            in (reverse l, dt)
-}
