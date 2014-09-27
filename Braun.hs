module Braun (Braun
             ,empty, size
             ,fromList, toList
             ,pushFront, pushBack, popFront, popBack
             ,glb, insert, delete
             ) 
       where
       
data Pre a = Nil
           | More a (Pre a) (Pre a)
           deriving (Show)

data Braun a = Braun Int (Pre a) deriving (Show)

empty = Braun 0 Nil

size (Braun n _) = n

-- Okasaki:
fromList xs = head $ foldr build [empty] $ rows 1 xs

rows :: Int -> [a] -> [(Int,[a])]
rows k [] = []
rows k xs = (k, take k xs) : rows (2*k) (drop k xs)

build (k, xs) ts = zipWith3 makeNode xs ts1 ts2
  where (ts1, ts2) = splitAt k (ts ++ repeat empty)
        makeNode x (Braun n s) (Braun m t) = Braun (n+m+1) (More x s t)

preToList Nil = []
preToList (More x ys zs) = x:(go [ys,zs] [] [])
  where go [] [] [] = []
        go [] r s = go ((reverse r) ++ (reverse s)) [] []
        go (Nil:ps) l r = go ps l r
        go ((More p qs rs):ss) l r = p:(go ss (qs:l) (rs:r))
        
toList (Braun _ p) = preToList p

prePushFront x Nil = More x Nil Nil
prePushFront x (More y p q) = More x (prePushFront y q) p

pushFront x (Braun n p) = Braun (n+1) (prePushFront x p)

pushBack x (Braun 0 Nil) = Braun 1 (More x Nil Nil)
pushBack x (Braun n (More y z w)) = 
  let (m,r) = n`quotRem`2
  in if r == 0
     then let Braun _ w2 = pushBack x (Braun (m-1) w)
          in Braun (n+1) (More y z w2)
     else let Braun _ z2 = pushBack x (Braun m z)
          in Braun (n+1) (More y z2 w)

prePopFront (More x Nil Nil) = (x,Nil)
prePopFront (More x y z) = 
  let (p,q) = prePopFront y
  in (x,More p z q)

popFront (Braun n p) = 
  let (x,p2) = prePopFront p
  in (x,Braun (n-1) p2)

popBack (Braun 1 (More x Nil Nil)) = (x,empty)
popBack (Braun n (More x y z)) = 
  let (m,r) = n`quotRem`2
  in if r == 0
     then let (p,Braun _ q) = popBack (Braun (m-1) z)
          in (p,Braun (n-1) (More x y q))
     else let (p,Braun _ q) = popBack (Braun m y)
          in (p,Braun (n-1) (More x q z))
                  
nth 0 (More x _ _) = x
nth i (More _ y z) =
  let (j,r) = (i-1)`quotRem`2
  in if r == 0
     then nth j y
     else nth j z

glb :: (a -> b -> Ordering) -> a -> Braun b -> Maybe b
glb f _ (Braun 0 Nil) = Nothing
glb f x xs@(Braun n ys@(More h _ _)) = 
  case f x h of
    LT -> Nothing
    EQ -> Just h
    GT -> 
      let final = nth (n-1) ys 
      in case f x final of
           LT -> go 0 (n-1)
           _ -> Just final
  where go i j = if j <= i
                 then if 0 == j
                      then Nothing
                      else Just $ nth (j-1) ys
                 else if i+1 == j
                      then Just $ nth i ys
                      else let k = (i+j)`div`2
                               middle = nth k ys
                           in case f x middle of
                               LT -> go i k
                               EQ -> Just middle
                               GT -> go k j

insert x xs =
  let (lt, gte) = break (>=x) $ toList xs
  in case gte of
       [] -> pushBack x xs
       (y:ys) -> if x == y
                 then xs
                 else fromList (lt ++ [x] ++ gte)
                      
delete x xs = 
  let (lt, gte) = break (>=x) $ toList xs
  in case gte of
       [] -> xs
       (y:ys) -> if x == y
                 then fromList (lt ++ ys)
                 else xs