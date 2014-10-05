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

data Kids b c a = Kids (b a) a (c a)
                  deriving (Show)
                      
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

data B b s sas a = P (b a)
                 | Q (B (Kids b b) (Kids b s) (Kids (Kids b s) (Kids b s)) a)
                 | R (B (Kids b s) sas (Kids sas sas) a)
                   deriving (Show)

newtype Id a = Id a deriving (Show)
data K a = K deriving (Show)

data Braun a = Braun (B Id K Id a)
             | Nil
               deriving (Show)

popFront :: Braun a -> Maybe (a,Braun a)
popFront Nil = Nothing
popFront (Braun (P (Id x))) = Just (x,Nil)
popFront (Braun (Q xs)) = 
  let (y,ys) = popFrontQ xs popOne
  in Just (y,case ys of
         Left same -> Braun (Q same)
         Right dif -> Braun (R dif))
popFront (Braun (R (P (Kids x y K)))) = Just (y,Braun (P x))     
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

popFrontQ :: B (Kids b b) (Kids b s) (Kids (Kids b s) (Kids b s)) a ->
             (b a -> (a,s a)) ->
             (a,Either (B (Kids b b) (Kids b s) (Kids (Kids b s) (Kids b s)) a)
                       (B (Kids b s) sas (Kids sas sas) a))
popFrontQ (P (Kids bb aa ss)) f = 
  let (x,xs) = f bb
  in  (aa,Right $ P (Kids ss x xs))
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

popFrontRR :: B (Kids b s) (Kids s s) (Kids (Kids s s) (Kids s s)) a ->
              (b a -> (a,s a)) -> 
             (a,Either (B (Kids b s) (Kids s s) (Kids (Kids s s) (Kids s s)) a)
                       (B (Kids s s) (Kids s t) (Kids (Kids s t) (Kids s t)) a))
popFrontRR (P (Kids bb aa ss)) f = 
  let (x,xs) = f bb
  in  (aa,Right $ P (Kids ss x xs))
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

--popKid :: (t -> (t3, t4)) -> (t, t1, t2) -> (t1, (t2, t3, t4))
popKid f (Kids x y z) =
  let (b,bs) = f x
  in (y,(Kids z b bs))
     
popOne (Id x) = (x,K)
popTwo (Kids x y K) = (y,x)     

pushFront :: a -> Braun a -> Braun a
pushFront x Nil = Braun $ P $ Id x
pushFront x (Braun xs) =
  let f y z = (Kids z y K)
      g y _ = Id y
      h y z = (Kids z y K)
  in case pushFrontB x f g h xs of
       Left ans -> Braun $ R ans
       Right ans -> Braun ans

pushFrontB :: a -> 
             (a -> big a -> huge a) -> 
             (a -> small a -> big a) -> 
             (a -> sas a -> Kids big small a) -> 
             B big small sas a -> 
             Either (B huge big (Kids big big) a)
                    (B big small sas a)
pushFrontB z f _ _ (P x) = Left $ P (f z x)
pushFrontB z f j m (Q x) = 
  let --g :: (ee -> bb -> cc) -> ee -> (dd,ee,bb) -> (cc,ee,dd)
      g k y (Kids p q r) = 
        let r2 = k q r
        in Kids r2 y p
  in case pushFrontB z (g f) (g j) (g (g j)) x
     of Left ans -> Left $ R ans
        Right ans -> Right $ Q ans
pushFrontB z f j m (R x) = 
  let --g :: (ee -> bb -> cc) -> ee -> (dd,ee,bb) -> (cc,ee,dd)
      g k y (Kids p q r) = 
        let r2 = k q r
        in Kids r2 y p
  in case pushFrontB z (g j) m (g m) x
     of Left ans -> Right $ Q ans
        Right ans -> Right $ R ans
        
{-

fromListT and toListT are code that has yet to be rewritten for the
nested style. These are substantially different than the Okasaki's
fromList and its companion toList; these use polymorphic
recursion. The fromList is also lazier, in that it can produce values
near the front of the output without having to read the whole
input. As a result, it are also suitable for streams, though that
isn't directly relevant in this nested construction.

We can use them to bootstrap fromList and toList for the nested type,
though there are a lof of missing match cases here, which should make
the reader wary.

-}
{-
toList Nil = []
toList (Braun x) = 
  let fb x = B x T T
      fs () = T
      fsas x = B x T T
  in toListT $ toT x fb fs fsas

toT :: B b s sas a -> (b -> T a) -> (s -> T a) -> (sas -> T a) -> T a
toT (P xs) fb _ _ = fb xs
toT (Q xs) fb fs _ = 
  let gb (p,q,r) = B q (fb p) (fb r)
      gs (p,q,r) = B q (fb p) (fs r)
      gsas (p,q,r) = B q (gs p) (gs r)
  in toT xs gb gs gsas
toT (R xs) fb fs fsas =
  let gb (p,q,r) = B q (fb p) (fs r)
      gs = fsas
      gsas (p,q,r) = B q (gs p) (gs r)
  in toT xs gb gs gsas


smartQ :: (b -> sas) -> a -> B b s sas a -> B b s sas a -> B b s sas a
smartQ _ h (P od) (P ev) = Q $ P (od,h,ev)
smartQ _ h (Q od) (Q ev) = Q $ smartQ undefined h od ev
smartQ _ h (Q od) (R ev) = Q $ smartR h od ev
smartQ _ h (R od) (R ev) = R $ smartQ undefined h od ev
smartQ f h (R od) (Q ev) = 
  let g (x,y,z) = (f x,y,f z)
  in R $ smartZ g h od ev
smartQ f h (R (P od)) (P ev) = R $ R $ P (od,h,f ev)

smartZ :: (b -> tat) -> a -> B s t tat a -> B b s' sas a -> B s t tat a
smartZ f h (R (P od)) (P ev) = R $ R $ P (od,h,f ev)
smartZ f h (R od) (Q ev) = 
  let g (x,y,z) = (f x,y,f z) -- does this recursion make it very expensive?
  in R $ smartZ g h od ev

smartR :: a -> B b s (s,a,s) a -> B s t tat a -> B b s (s,a,s) a
smartR h (P od) (P ev) = R $ P (od,h,ev)
smartR h (R od) (Q ev) = R $ smartR h od ev

fromT :: T a -> B a () a a
fromT (B hd T T) = P hd
fromT (B hd (B od T T) T) = R $ P (od,hd,())
fromT (B hd od ev) =
  let od' = fromT od
      ev' = fromT ev
  in smartQ id hd od' ev'

fromList [] = Nil
fromList xs = Braun $ fromT $ fromListT xs

data T a = T
         | B a (T a) (T a)
           deriving (Show)

toListT :: T a -> [a]
toListT T = []
toListT (B hd od ev) = 
  let rest = unPair $ toListT $ zipT od ev
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

fromListT :: [a] -> T a
fromListT [] = T
fromListT (x:xs) = 
  let (od,ev) = unLink $ fromListT $ pairUp xs
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