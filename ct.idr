
import Prelude

record Cat where
 constructor MkCat
 obj : Type
 hom : (obj,obj) -> Type
 id : (x: obj) -> hom (x,x)
 comp : (x , y , z : obj) -> ( f : hom (x,y)) -> (g : hom (y,z)) -> hom (x,z)
 id_ax : (x , y : obj) -> (f : hom (x,y)) -> ((comp x x y (id x) f) =  f, (comp x y y f (id y)) = f )
 ass : (x , y, z, w : obj) -> ( f: hom (x,y)) -> (g : hom (y,z)) -> (h : hom (z,w)) -> comp x z w (comp x y z f g) h = comp x y w f (comp y z w g h)


terminal : (c : Cat) -> (t : obj c) -> Type 
terminal c t =  (x: obj c) -> (g: hom c (x,t) ** (f : hom c (x,t)) -> f = g)

iso : (c : Cat) -> (x , y : obj c) -> Type
iso c x y = (f : hom c (x,y) ** (g : hom c (y,x) **  ((comp c x y x f g) =  (id c x), (comp c y x y g f) = (id c y) )    )    )

lemma1 : (c : Cat) -> (a : obj c) -> (t : terminal c a) ->  id c a = fst ( t a)
lemma1 c a t = (snd(t a)) (id c a)

-- Given a category c and an object a of c such that a is a terminal object of c let fst (t a) be the canonical morphism
-- a -> a associated to a. Then for any morphism  f: a -> a we must have that f = fst (t a) and in particular for id : a -> a
-- we must have that id = fst (t a) 


lemma2 : (c : Cat) -> (a : obj c) -> (t : terminal c a) -> ( f: hom c (a,a)) -> f = id c a
lemma2 c a t f =  trans   ( (snd (t a)) f)   (sym  (lemma1 c a t) ) 

terminal_iso : (c :Cat) -> (a , b : obj c) -> ( t1 : terminal c a) -> (t2 : terminal c b) -> iso c a b
terminal_iso c a b t1 t2 =  ( fst (t2 a) **( (fst (t1 b) ** (lemma2 c a t1 (comp c a b a (fst (t2 a)) (fst (t1 b))),    ?foo ) )))

record Functor (X : (Cat,Cat)) where
 constructor MkFunctor
 f_obj : obj (fst X) -> obj (snd X)
 arr : (x , y : obj (fst X)) ->  (hom (fst X) (x,y)) -> (hom (snd X) (f_obj x, f_obj y))
 f_id : (x : obj (fst X)) ->  (arr x x (id (fst X) x))  = (id (snd X) (f_obj x))     
 f_comp : (x , y , z : obj (fst X)) -> (f : hom (fst X) (x,y)) -> (g : hom (fst X) (y,z)) ->
 (arr x z (comp (fst X) x y z f g)) = (comp (snd X) (f_obj x) (f_obj y)(f_obj z) (arr x y f) (arr y z g)) 
     
record NatTrans (X : (Cat, Cat)) (F, G :Functor X) where
 constructor MkNatTrans
 eta : (x: obj (fst X)) -> hom (snd X) ((f_obj F x),(f_obj G x))
 com : ( x, y : obj (fst X)) -> ( f : hom (fst X) (x,y)) -> 
comp (snd X) (f_obj F  x) (f_obj G x) (f_obj G y) (eta x) (arr G x y f) = 
comp (snd X) (f_obj F x) (f_obj F y) (f_obj G y) (arr F x y f) (eta y)
 
  





 



