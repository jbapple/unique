module BraunUnique(Unique, 
                   empty, size,
                   fromList, toList,
                   glb, insert, delete)
       where

-- A dynamic predecessor data structure that is uniquely represented;
-- any two structures with the same elements have the same size and
-- shape. Unlike the structure designed in Sundar and Tarjan's "Unique
-- binary search tree representations and equality-testing of sets and
-- sequences", this structure uses only O(n) space.
--
-- Updates are \sqrt{n \log n}, while searches are \log^2 n.

import qualified Braun as B

data Unique a = Unique Int (B.Braun (B.Braun a))
                deriving (Show)

empty = Unique 0 B.empty

size (Unique n _) = n

-- The ith Braun tree has size \sqrt{i \log i}, though the last Braun
-- tree may be smaller.
sizes = [max 1 (round (j * sqrt((log j)/(log 2)))) | i <- [1..], let j = fromIntegral i]
        
-- fromList is O(n)
fromList xs =
  let n = length xs
      takeGroups [] _ = []
      takeGroups xs (k:ks) =
        let (y,ys) = splitAt k xs
        in y:(takeGroups ys ks)
      ys = B.fromList $ map B.fromList $ takeGroups xs sizes
  in Unique n ys

-- toList is O(n)
toList (Unique _ xs) = concatMap B.toList (B.toList xs)

comp y b = let (h,_) = B.popFront b
           in compare y h

-- Each search in a Braun tree is O(\log^2 n). This method uses two,
-- so is also O(\log^2 n).
glb x (Unique n xs) = 
  do b <- B.glb comp x xs
     B.glb compare x b

fixupList :: [B.Braun a] -> [Int] -> [B.Braun a]
fixupList [] _ = []
fixupList [x] _ = 
  if B.size x == 0
  then []
  else [x]
fixupList (x:y:ys) (z:zs) =
  case compare (B.size x) z of
    EQ -> x:(fixupList (y:ys) zs)
    LT -> let (p,ps) = B.popFront y
          in fixupList ((B.pushBack p x):ps:ys) (z:zs)
    GT -> let (q,qs) = B.popBack x
          in fixupList (qs:(B.pushFront q y):ys) (z:zs)

-- insert performes one insert in a Braun tree and then some
-- cascasding deque operations on the other Braun trees. Since insert
-- on a Braun tree is O(n), and since the largest Braun tree in the
-- structure has size \sqrt{n \log n}, that part of insert costs at
-- most \sqrt{n \log n}. The deque operations take at most \log n time
-- each, and a constant number are performed for each Braun
-- tree. Since there are at most \sqrt{n / \log n} Braun trees, the
-- total time is \sqrt{n \log n}.
insert :: Ord a => a -> Unique a -> Unique a
insert x (Unique 0 _) = Unique 1 (B.fromList [B.fromList [x]])
insert x (Unique n xs) =
  let ltx y = comp x y == LT
      (lte,gt) = break ltx $ B.toList xs
      final ps = let qs = fixupList ps sizes
                     m = sum $ map B.size qs
                 in Unique m (B.fromList qs)
  in final $
     case (reverse lte,gt) of
       ([],gt1:gts) -> (B.pushFront x gt1):gts
       (eq:rev_lt,_) -> (reverse rev_lt) ++ [B.insert x eq] ++ gt
       
-- delete is just insert in reverse, and so has the same time
-- complexity
delete :: Ord a => a -> Unique a -> Unique a
delete x (Unique 0 _) = empty
delete x (Unique n xs) =
  let ltx y = comp x y == LT
      (lte,gt) = break ltx $ B.toList xs
      final ps = let qs = fixupList ps sizes
                     m = sum $ map B.size qs
                 in Unique m (B.fromList qs)
  in final $
     case reverse lte of
       [] -> gt
       (eq:rev_lt) -> (reverse rev_lt) ++ [B.delete x eq] ++ gt