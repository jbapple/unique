module Kickstart where

{-

This module shows an implementation of Braun trees in which the
structural invariant is enforced by the type system. These kind of
guarantees are availble via dependent types, as shown for Braun trees
in the Dependent ML work of Hongwei Xi, and in GADTs, which are now
available in GHC and OCaml, and even in languages like C++ and Java
via the curiously recurring template pattern. This module instead uses
a more arcane method of "nested" datatypes, sometimes called
"non-regular" or "non-uniform" or heterogeneous.

This implementation strategy is more similar to the one of Stefan
Kahrs's "Red-black trees with types" (Implementation:
http://www.cs.kent.ac.uk/people/staff/smk/redblack/rb.html). That work
has been called "complex"
(http://matt.might.net/articles/red-black-delete/), "all-too-clever",
and "miraculous" (Appel, "Efficient Verified Red-Black Trees",
https://www.cs.princeton.edu/~appel/papers/redblack.pdf). There is no
question that this implementation of Braun trees is significantly more
complex than the standard one without nested types.

-}

type Sym a b = (b,a,b)
                      
{-               

Ralf Hinze, in "Manufacturing Datatypes", has designed a nested data
type for enforcing Braun tree structural invariants, but it doesn't
seem to actually support efficient deque operations, because the shape
of a tree of size n and size n+1 can differ in \Omega(n) locations, as
subtrees of size 1 can have the shape "a" or the shape ((),a,()).

To fix that problem, this type stores, in addition to the "big" tree
type and the "small" tree type, a type of trees where each child
subtree of the root is a small tree. When small is (), this is a,
rather than ((),a,()).

-}

data B b s sas a = P b
                 | Q (B (b,a,b) (b,a,s) (Sym a (b,a,s)) a)
                 | R (B (b,a,s) sas (Sym a sas) a)
                   deriving (Show)

data Braun a = Braun (B a () a a)
             | Nil
               deriving (Show)
  

popFront Nil = Nothing
popFront (Braun (P x)) = Just (x,Nil)
popFront (Braun (Q xs)) = 
  let (y,ys) = popFrontQ xs popOne
  in Just (y,case ys of
         Left same -> Braun (Q same)
         Right dif -> Braun (R dif))
popFront (Braun (R (P (x,y,())))) = Just (y,Braun (P x))     
popFront (Braun (R (R xs))) =
  let (y,ys) = popFrontRR xs popTwo
  in Just (y,case ys of
         Left same -> Braun $ R $ R same
         Right dif -> Braun $ Q dif)
popFront (Braun (R (Q xs))) =
  let (y,ys) = popFrontQ xs popTwo
  in Just (y,case ys of
         Left same -> Braun $ R $ Q same
         Right dif -> Braun $ R $ R dif)

popFrontQ :: B (Sym a b) (b,a,s) (Sym a (b,a,s)) a ->
             (b -> (a,s)) ->
             (a,Either (B (Sym a b) (b,a,s) (Sym a (b,a,s)) a)
                       (B (b,a,s) sas (Sym a sas) a))
popFrontQ (P (bb,aa,ss)) f = 
  let (x,xs) = f bb
  in  (aa,Right $ P (ss,x,xs))
popFrontQ (R (P xs)) f = 
  let (y,ys) = popFrontRR (P xs) (popKid f)
  in (y,case ys of
         Left same -> Left $ R same
         Right dif -> Right $ Q dif)
popFrontQ (R (R xs)) f =
  let (y,ys) = popFrontRR (R xs) (popKid f)
  in (y,case ys of
         Left same -> Left $ R same
         Right dif -> Right $ Q dif)
popFrontQ (R (Q xs)) f =
  let (y,ys) = popFrontQ xs (popKid $ popKid f)
  in (y,case ys of
         Left same -> Left $ R $ Q same
         Right dif -> Left $ R $ R dif)
popFrontQ (Q xs) f =
  let (y,ys) = popFrontQ xs (popKid f)
  in (y,case ys of
         Left same -> Left $ Q same
         Right dif -> Left $ R dif)

popFrontRR :: B (b,a,s) (s,a,s) (Sym a (s,a,s)) a ->
              (b -> (a,s)) -> 
             (a,Either (B (b,a,s) (s,a,s) (Sym a (s,a,s)) a)
                       (B (s,a,s) (s,a,t) (Sym a (s,a,t)) a))
popFrontRR (P (bb,aa,ss)) f = 
  let (x,xs) = f bb
  in  (aa,Right $ P (ss,x,xs))
popFrontRR (R (P xs)) f = 
  let (y,ys) = popFrontRR (P xs) (popKid f)
  in (y,case ys of
         Left same -> Left $ R same
         Right dif -> Right $ Q dif)
popFrontRR (R (R xs)) f =
  let (y,ys) = popFrontRR (R xs) (popKid f)
  in (y,case ys of
         Left same -> Left $ R same
         Right dif -> Right $ Q dif)
popFrontRR (R (Q xs)) f =
  let (y,ys) = popFrontQ xs (popKid $ popKid f)
  in (y,case ys of
         Left same -> Left $ R $ Q same
         Right dif -> Left $ R $ R dif)
popFrontRR (Q xs) f =
  let (y,ys) = popFrontQ xs (popKid f)
  in (y,case ys of
         Left same -> Left $ Q same
         Right dif -> Left $ R dif)

popKid :: (t -> (t3, t4)) -> (t, t1, t2) -> (t1, (t2, t3, t4))
popKid f (x,y,z) =
  let (b,bs) = f x
  in (y,(z,b,bs))
     
popOne x = (x,())
popTwo (x,y,()) = (y,x)     

pushFrontB :: a -> Braun a -> Braun a
pushFrontB x Nil = Braun $ P x
pushFrontB x (Braun xs) =
  let f y z = (z,y,())
      g y _ = y
      h y z = (z,y,())
  in case pushFront x f g h xs of
       Left ans -> Braun $ R ans
       Right ans -> Braun ans

pushFront :: a -> 
             (a -> big -> huge) -> 
             (a -> small -> big) -> 
             (a -> sas -> (big,a,small)) -> 
             B big small sas a -> 
             Either (B huge big (big,a,big) a)
                    (B big small sas a)
pushFront z f _ _ (P x) = Left $ P (f z x)
pushFront z f j m (Q x) = 
  let g :: (ee -> bb -> cc) -> ee -> (dd,ee,bb) -> (cc,ee,dd)
      g k y (p,q,r) = 
        let r2 = k q r
        in (r2,y,p)
  in case pushFront z (g f) (g j) (g (g j)) x
     of Left ans -> Left $ R ans
        Right ans -> Right $ Q ans
pushFront z f j m (R x) = 
  let g :: (ee -> bb -> cc) -> ee -> (dd,ee,bb) -> (cc,ee,dd)
      g k y (p,q,r) = 
        let r2 = k q r
        in (r2,y,p)
  in case pushFront z (g j) m (g m) x
     of Left ans -> Right $ Q ans
        Right ans -> Right $ R ans
        
{-

{-

fromList and toList code that has yet to be rewritten for the nested
style. These are substantially different than the Okasaki fromList and
it's companion toList; these use polymorphic recursion and are also
lezier, in that they can produce values near the front of the output
without having to read the whole input. As a result, they are also
suitable for stream, though that isn't directly relevant in this
nested construction.

-}

data T a = T
         | B a (T a) (T a)
           deriving (Show)

toList :: T a -> [a]
toList T = []
toList (B hd od ev) = 
  let rest = unPair $ toList $ zipT od ev
  in hd:rest

unPair :: [(a,Maybe a)] -> [a]
unPair [] = []
unPair [(x,Nothing)] = [x]
unPair ((x,Just y):ys) = x:y:(unPair ys)

zipT T T = T                    
zipT (B x T T) T = B (x,Nothing) T T
zipT (B x odx evx) (B y ody evy) = 
  let od = zipT odx ody
      ev = zipT evx evy
  in B (x,Just y) od ev

fromList :: [a] -> T a
fromList [] = T
fromList (x:xs) = 
  let (od,ev) = unLink $ fromList $ pairUp xs
  in B x od ev
     
pairUp :: [a] -> [(a, Maybe a)]
pairUp [] = []
pairUp [x] = [(x,Nothing)]
pairUp (x:y:ys) = (x,Just y):pairUp ys

unLink :: T (a,Maybe b) -> (T a,T b)
unLink T = (T,T)
unLink (B (x,Nothing) T T) = (B x T T,T)
unLink (B (x,Just y) od ev) =
  let (odx,ody) = unLink od
      (evx,evy) = unLink ev
  in (B x odx evx, B y ody evy)
-}
