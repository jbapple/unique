-- {-# LANGUAGE RankNTypes,ExistentialQuantification #-}

module Kickstart where

type Sym a b = (b,a,b)
                      
data B b s sas a = P b
                 | Q (B (Sym a b) (b,a,s) (Sym a (b,a,s)) a)
                 | R (B (b,a,s) sas (Sym a sas) a)
                   deriving (Show)

--instance Show (

--instance (Show a, Show b, Show (b,a,s), Show sas) => Show B b s sas a where

data Braun a = Braun (B a () a a)
             | Nil
  
instance Show a => Show (Braun a) where
  show Nil = "Nil"
  show (Braun x) = "Braun " ++ (show x)

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

{-
popFrontQ :: B (b,a,s) (s,a,s) z (s,a,t) y a ->
             Either (B (s,a,s) (s,a,t) (Sym a (s,a,t)) (t,a,t)
-}
{-
popFrontQS :: B (a,a,a) (a,a,()) bam2 a ->
             (a -> (a,())) -> 
             (a,Either (B (a,a,a) (a,a,()) bam2 a)
                       (B (a,a,()) a (a,a,a) a)
popFrontQL :: B (b,a,b) (b,a,(m1,a,m2)) bam2 a ->
             (b -> (a,(m1,a,m2))) -> 
             (a,Either (B (b,a,b) (b,a,(m1,a,m2)) bam2 a)
                       (B (b,a,(m1,a,m2)) (Sym a (m1,a,m2)) (Sym a (Sym a (m1,a,m2))) a))
-}
{-
popFrontQ :: B (b,a,b) (b,a,m) bam2 a ->
             (b -> (a,m)) -> 
             (a,Either (B (b,a,b) (b,a,m) bam2 a)
                       (B b m (m,a,m) a)
-}
{-
popFrontR :: B (b,a,m) (m,a,m) mam2 a ->
             (b -> (a,m)) -> 
             (a,Either (B (b,a,m) (m,a,m) mam2 a)
                       (B (m,a,m) (m,a,s) (m,a,m) a)
popFrontR :: B (b,a,m) (m,a,m) mam2 a ->
             (b -> (a,m)) -> 
             (a,Either (B (b,a,m) (m,a,m) mam2 a)
                       (B m s sas (m,a,m) a)
popFrontR :: B (b,a,m) (m,a,m) mam2 a ->
             (b -> (a,m)) -> 
             (a,Either (B (b,a,m) (m,a,m) mam2 a)
                       (B m s sas (m,a,m) a)
-}

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