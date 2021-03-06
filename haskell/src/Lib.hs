{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE DataKinds, GADTs, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Lib
    ( someFunc
    ) where

--import Data.List hiding (reverse, (!!))
import Data.ListLike.FoldableLL
import Control.Monad (join)
import Prelude hiding (reverse, (!!),foldl,foldr)
import Data.Ord
import Data.Monoid

type family Max (a :: Nat) (b :: Nat) :: Nat where
	Max Zero    m = m
	Max n    Zero = n
	Max (Succ n) (Succ m) = Succ (Max n m)

type family Min (a :: Nat) (b :: Nat) :: Nat where
	Min Zero    m = Zero
	Min n    Zero = Zero
	Min (Succ n) (Succ m) = Succ (Min n m)

data Nat where
	Zero :: Nat
	Succ :: Nat -> Nat

data SBool (b :: Bool) where
	STrue :: SBool True
	SFalse :: SBool False

data SNat (n :: Nat) where
	SZ :: SNat Zero
	SS :: SNat k -> SNat (Succ k)

pred :: SNat (Succ n) -> SNat n
pred (SS n) = n

data Ordinal (n :: Nat) where
	OZ :: Ordinal (Succ n)
	OS :: Ordinal n -> Ordinal (Succ n)

type One = Succ Zero
type Two = Succ One
type Three = Succ Two
type Four = Succ Three

{-
type OOne = OS OZ
type OTwo = OS OOne
type OThree = OS OTwo
type OFour = OS OThree
-}

zero = OZ
one = OS OZ
two = OS one
three = OS two
four = OS three
five = OS four
six = OS five
seven = OS six
eight = OS seven
nine = OS eight
ten = OS nine
eleven = OS ten


instance Show (Ordinal n) where
	show OZ = "0"
	show (OS OZ) = "1"
	show (OS (OS OZ)) = "2"
	show (OS (OS (OS (OZ)))) = "3"
	show (OS some) = "OS (" ++ show some ++ ")"

instance Eq (Ordinal n) where
	(==) OZ     OZ     = True
	(==) (OS m) (OS n) = m == n
	(==) _      _      = False

data Vector (n :: Nat) a where
	VNil :: Vector Zero a
	(:-) :: a -> Vector n a -> Vector (Succ n) a

infixr 6 :-

instance FoldableLL (Vector n a) a where
	foldr f ini VNil = ini
	foldr f ini (x :- xs) = f x (foldr f ini xs)
	foldl f ini VNil = ini
	foldl f ini (x :- xs) = f (foldl f ini xs) x

vhead :: Vector (Succ n) a -> a
vhead (a :- _) = a

vtail :: Vector (Succ n) a -> Vector n a
vtail (_ :- xs) = xs

(!!) :: Vector n a -> Ordinal n -> a
(!!) (a :- _) OZ = a
(!!) (_ :- xs) (OS n) = xs !! n

vlength :: Vector n a -> SNat n
vlength VNil = SZ
vlength (_ :- xs) = SS $ vlength xs

vindexOf :: (Eq a) => Vector n a -> a -> Ordinal n
vindexOf (a :- xs) a' | a == a' = OZ
                      | otherwise = OS $ vindexOf xs a'

vToList :: Vector n a -> [a]
vToList VNil = []
vToList (x :- xs) = x : vToList xs

-- vfilter :: (a -> Bool) -> Vector n a -> Vector m a
-- vfilter p VNil = VNil
-- vfilter p (x :- xs) = if p x then x :- vfilter p xs else vfilter p xs

--ta Subst where
--	S ::(Vector Four Int) -> (Ordinal Four) -> Int -> Subst
{-
instance (Show (Vector Four Int)) => Show Subst where
	show (S f) = show v
-}

-- v = (VCons OZ (VCons (OS (Succ Zero)) (VCons (OS (Succ (Succ Zero))) (VCons (OS (Succ (Succ (Succ Zero)))) VNil)))) :: Vector Four (Ordinal (Succ (Succ (Succ (Succ Zero)))))

type Subs4Vec = Vector Four (Ordinal Four)
type Subs3Vec = Vector Three (Ordinal Three)

v0 = zero :- one :- two :- three :- VNil :: Subs4Vec

v1 = zero :- two :- three :- one :- VNil :: Subs4Vec
v2 = zero :- three :- one :- two :- VNil :: Subs4Vec
v3 = two :- one :- three :- zero :- VNil :: Subs4Vec
v4 = three :- one :- zero :- two :- VNil :: Subs4Vec
v5 = one :- three :- two :- zero :- VNil :: Subs4Vec
v6 = three :- zero :- two :- one :- VNil :: Subs4Vec
v7 = one :- two :- zero :- three :- VNil :: Subs4Vec
v8 = two :- zero :- one :- three :- VNil :: Subs4Vec

v9 = one :- zero :- three :- two :- VNil :: Subs4Vec
v10 = two :- three :- zero :- one :- VNil :: Subs4Vec
v11 = three :- two :- one :- zero :- VNil :: Subs4Vec

vs4 = v0 :- v1 :- v2 :- v3 :- v4 :- v5 :- v6 :- v7 :- v8 :- v9 :- v10 :- v11 :- VNil

v3_0 = zero :- one :- two :- VNil :: Subs3Vec
v3_1 = zero :- two :- one :- VNil :: Subs3Vec
v3_2 = one :- zero :- two :- VNil :: Subs3Vec
v3_3 = one :- two :- zero :- VNil :: Subs3Vec
v3_4 = two :- zero :- one :- VNil :: Subs3Vec
v3_5 = two :- one :- zero :- VNil :: Subs3Vec

vs3 = v3_0 :- v3_1 :- v3_2 :- v3_3 :- v3_4 :- v3_5 :- VNil

--sa0 = \i S (\i v -> vindex i v)

--instance Show (Vector Zero a) where
--	showsPrec p _ = \s -> "[" ++ s ++ "]"

instance Functor (Vector n) where
	fmap f VNil = VNil
	fmap f (x :- xs) = f x :- fmap f xs

showVec :: Show a => Vector n a -> String
showVec VNil = ""
showVec (x :- xs) = ", " ++ show x ++ showVec xs

instance (Show a) => Show (Vector n a) where
	show VNil = "[]"
	show (x :- xs) = "[" ++ show x ++ showVec xs ++ "]"

--data Substitution where
--	Subs :: Subs4Vec -> Ordinal Four -> Ordinal Four -> Substitution

--instance Show Substitution where
--	show f = show (fmap f [zero, one, two, free])

newtype Substitution = S ((Ordinal Four) -> (Ordinal Four))

instance Monoid Substitution where
	mempty = a0
	(S f) `mappend` (S g) = S $ f . g

instance Show Substitution where
	show (S f) = show (fmap f v0)

instance Eq Substitution where
	(S a) == (S a') = getAll . mconcat . vToList . fmap (\i -> All $ a i == a' i) $ v0

subs :: Subs4Vec -> Substitution
subs v = S $ (v !!)

--subsr :: Subs4Vec -> Substitution
--subsr v = S $ \i -> vindex i $ reverseSubs v

as = fmap subs vs4

--class8 = take 8 $ drop 1 $ vToList as
class3 = drop 9 $ vToList as

a0 = as !! zero 
a1 = as !! one
a2 = as !! two
a3 = as !! three
a4 = as !! four
a5 = as !! five
a6 = as !! six
a7 = as !! seven
a8 = as !! eight
a9 = as !! nine
a10 = as !! ten
a11 = as !! eleven

reverseSubs4Vec :: Subs4Vec -> Subs4Vec
reverseSubs4Vec v@(e0 :- e1 :- e2 :- e3 :- VNil) = v !! e0 :- v !! e1 :- v !! e2 :- v !! e3 :- VNil

rev :: Substitution -> Substitution
rev (S f) = S f' where
	f' i = vindexOf (fmap f v0) i

transformSubs :: Substitution -> Substitution -> Substitution
transformSubs a b = rev b <> a <> b

-- tra9 = transformSubs a9
-- a9transformed = fmap tra9 . filter (\a -> a /= a9) . vToList $ as

transformByAll a = fmap (transformSubs a) . filter (\a' -> a /= a') . vToList $ as
a9transformted = transformByAll a9

isInClass a c = getAny . mconcat . fmap (\a' -> Any $ a == a') $ c
isInGroup = isInClass
allInClass c as = getAll . mconcat . fmap (All . (flip isInClass $ c)) $ as

isAClass c = getAll . mconcat . fmap (All . allInClass c . transformByAll) $ c

gen ys [] = []
gen ys (x:xs) = [x:ys] ++ gen (x:ys) xs ++ gen ys xs

allClassPretendents = gen [] $ drop 1 $ vToList as -- without those which contain [0,1,2,3]

classes = filter isAClass allClassPretendents

-- we just know it from the book, no magic
-- and we could see on results (there are just few of them) by eyes
-- and notice that long-length items just contain the short-length ones
trueclasses = filter (\xs -> length xs < 5) classes

isInvariantSubgroup subgroup = isAClass subgroup && isAGroup subgroup
isAGroup g = getAll $ mconcat $ fmap (All . isElemOfGroupG) g where
	isElemOfGroupG = isElemOfGroup g

isElemOfGroup :: [Substitution] -> Substitution -> Bool
isElemOfGroup g a = getAll $ mconcat $ fmap (\a' -> All $ isInGroup (a <> a') g && isInGroup (a' <> a) g) g

isCommutative :: [Substitution] -> Bool
isCommutative [] = True
isCommutative (x:xs) = (getAll . mconcat . fmap (\x' -> All $ x <> x' == x' <> x) $ xs) && isCommutative xs
	

someFunc :: IO ()
someFunc = undefined -- putStrLn "someFunc"


