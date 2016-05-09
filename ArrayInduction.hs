import Data.Function.ArrayMemoize
import Data.Array
import Data.Array.Base (unsafeAt)
        
cov_ :: (Int -> (Int -> () -> a) -> a) -> (Int -> a) -> Int -> a
cov_ f g n = f n (\ m _ -> g m)
    
cov :: ArrayMemoizable a =>
       Int -> (Int -> (Int -> () -> a) -> a) -> Int -> () -> a
cov limit g n _ =
    arrayMemoFix (0, limit) (cov_ g) n

--(Nat -> (Nat -> () -> a) -> a) -> Nat -> a

listToArray :: [a] -> Array Int a
listToArray a = listArray (0, length a - 1) a

arrayLen :: Array Int a -> Int
arrayLen a =
    let (s, e) = bounds a
    in (e - s + 1)

maybeArrayNth :: Array Int a -> Int -> Maybe a
maybeArrayNth a n =
    let (s, e) = bounds a
    in if (s <= n) && (n <= e)
       then
           -- we are allowed to use unsafeAt here, because we just
           -- checked the bounds.
           Just $ unsafeAt a n
       else Nothing
       
