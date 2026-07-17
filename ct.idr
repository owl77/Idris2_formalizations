
import Prelude


record Cat where
 constructor MkCat
 obj : Type
 hom : (obj,obj) -> Type
 id : (x: obj) -> hom (x,x)
 comp : (x , y , z : obj) -> ( f : hom (x,y)) -> (g : hom (y,z)) -> hom (x,z)
 id_ax : (x , y : obj) -> (f : hom (x,y)) -> ((comp x x y (id x) f) =  f, (comp x y y f (id y)) = f )
 ass : (x , y, z, w : obj) -> ( f: hom (x,y)) -> (g : hom (y,z)) -> (h : hom (z,w)) -> 
comp x z w (comp x y z f g) h = comp x y w f (comp y z w g h)

set_hom : (Type, Type) -> Type
set_hom (a,b) = a -> b
set_id: (t : Type) -> set_hom (t,t)
set_id t = \x => x
set_comp : (x,y,z :Type) -> (f : set_hom (x,y)) -> (g : set_hom (y,z)) -> set_hom (x,z)
set_comp x y z f g a = g (f a)
pre_set_id_ax_l: (x, y : Type) -> (f : set_hom (x,y)) -> (a : x) -> (set_comp x x y (set_id x) f) a =  f a

 -- to define the category of sets we need extensionality, FunExt
funExt : (a,b : Type) -> (f, g: a -> b) -> ((x :a ) -> (f x = g x)) -> (f = g) 

pre_set_id_ax_l x y f a = Refl

set_id_ax_l :( x, y : Type) -> (f : set_hom (x,y)) -> (set_comp x x y (set_id x) f = f)
set_id_ax_l x y f = funExt x y (\a => set_comp x x y (set_id x) f a) f (pre_set_id_ax_l x y f)

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
 
   
NatId_eta: (X : (Cat,Cat)) -> (F : Functor X) -> (x: obj (fst X)) -> hom (snd X) ((f_obj F x),(f_obj F x))

NatId_eta c f x = id (snd c) (f_obj f x)

NatId_com:  (X : (Cat,Cat)) -> (F : Functor X) -> ( x, y : obj (fst X)) -> ( f : hom (fst X) (x,y)) ->
comp (snd X) (f_obj F  x) (f_obj F x) (f_obj F y) (NatId_eta X F x) (arr F x y f) = comp (snd X) (f_obj F x) (f_obj F y) (f_obj F y) (arr F x y f) (NatId_eta X F y)
NatId_com c fu x y f = let aux = id_ax (snd c) (f_obj fu x) (f_obj fu y) (arr fu x y f) in trans (fst aux) (sym (snd aux))

natId : (X : (Cat,Cat)) -> (F: Functor X) -> NatTrans X F F
natId x f = MkNatTrans  (NatId_eta x f) (NatId_com x f)


-- hom_eq : (c : Cat) -> ( x, y, z : obj c) -> (f, g : hom c (x,y)) -> (h : hom c (y,z)) ->
--  (j : hom c (x,z)) -> (g = f ) -> (comp c x y z f h = j ) -> (comp c x y z g h = j)
-- hom_eq c x y z f g h j eq p = rewrite eq in p

-- hom_prop : (c : Cat) -> (x , y , z : obj c) -> (h : hom c (y,z)) -> (j : hom c (x,z)) -> (f: hom c (x,y)) ->  Type
-- hom_prop c x y z h j f =  (comp c x y z f h = j )

-- hom_eq : (c : Cat) -> (x , y , z : obj c) -> (h : hom c (y,z)) -> (j : hom c (x,z)) -> (f, g : hom c (x,y)) -> (g = f) ->
-- (hom_prop c x y z h j f) -> (hom_prop c x y z h j g)
-- hom_eq c x y z h j f g eq p = rewrite eq in  p

diag_chase1 : (c : Cat) -> (x1,x2,x3,y1,y2,y3 : obj c) -> (f1 : hom c (x1,x2)) -> (f2 : hom c (x2,x3)) -> (g1 : hom c (x1,y1))
-> (g2 : hom c (x2,y2)) -> (g3: hom c (x3,y3)) ->  (h1 : hom c (y1,y2)) -> (h2 : hom c (y2,y3)) -> 
(p1 : comp c x1 x2 y2 f1 g2 = comp c x1 y1 y2 g1 h1) -> (p2 : comp c x2 x3 y3 f2 g3 = comp c x2 y2 y3 g2 h2)
-> comp c x1 x3 y3 (comp c x1 x2 x3 f1 f2) g3 = comp c x1 y1 y3 g1 (comp c y1 y2 y3 h1 h2)

diag_chase1 c x1 x2 x3 y1 y2 y3 f1 f2 g1 g2 g3 h1 h2 p1 p2 = let ass1 = ass c x1 x2 x3 y3 f1 f2 g3
 in let aux = rewrite (sym p2) in ass1 in let ass2 = ass c x1 x2 y2 y3 f1 g2 h2 in let aux2 = rewrite ass2 in aux in let aux3 = rewrite (sym p1) in aux2 in let ass3 = ass c x1 y1 y2 y3 g1 h1 h2 in rewrite (sym ass3) in aux3

-- test : (c: Cat) -> (x,y,z,w : obj c) -> ( f : hom c (x,y)) -> (g: hom c (y,z)) -> (h : hom c (z, w)) -> ( j : hom c (x, w)) ->
-- (comp c x z w ( comp c x y z f g) h = j ) -> ( comp c x y w f (comp c y z w g h) = j)
-- test c x y z w f g h j pr = rewrite (sym (ass c x y z w f g h)) in pr

natComp_eta :(X : (Cat, Cat)) -> (F, G, H : Functor X) -> (a : NatTrans X F G) -> (b : NatTrans X G H) -> (x : obj (fst X)) ->
 hom (snd X) (f_obj F x, f_obj H x)

natComp_eta x f g h a b o = comp (snd x) (f_obj f o) (f_obj g o) (f_obj h o) (eta a o) (eta b o)

aux : (X : (Cat,Cat)) -> (F,G,H : Functor X) -> (a : NatTrans X F G) -> (b : NatTrans X G H) -> (x : obj (fst X)) ->
 natComp_eta X F G H a b x =  comp (snd X) (f_obj F x) (f_obj G x) (f_obj H x) (eta a x) (eta b x)
aux x fu gu hu a b o = Refl

natComp_com :(X : (Cat, Cat)) -> (F, G, H : Functor X) -> (a : NatTrans X F G) -> (b : NatTrans X G H) -> (x, y : obj(fst X)) 
-> (f: hom (fst X) (x,y)) -> comp (snd X) (f_obj F  x) (f_obj H x) (f_obj H y) (natComp_eta X F G H a b x) (arr H x y f) = 
comp (snd X) (f_obj F x) (f_obj F y) (f_obj H y) (arr F x y f) (natComp_eta X F G H a b y)

natComp_com cs fu gu hu a b x y f = let left = com a x y f in let right = com b x y f in 
 rewrite (aux cs fu gu hu a b x) in
 (diag_chase1 (snd cs) (f_obj fu x) (f_obj gu x) (f_obj hu x) (f_obj fu y) (f_obj gu y) (f_obj hu y) (eta a x) (eta b x) (arr fu x y f) (arr gu x y f) (arr hu x y f) (eta a y) (eta b y) left right)	

-- I tried using let x1 = f_obj fu x in...but this did not work for rewrite. One has to understand how expressions are evaluated and unified to use rewrite 

natComp : (X : (Cat, Cat)) -> (F, G, H : Functor X) -> (a : NatTrans X F G) -> (b : NatTrans X G H) -> NatTrans X F H
natComp cs fu gu hu a b = MkNatTrans  (natComp_eta cs fu gu hu a b) (natComp_com cs fu gu hu a b)

natCompId_left : (X : (Cat,Cat)) -> (F, G : Functor X) -> (a : NatTrans X F G) ->  natComp X F F G (natId X F) a = a 
natCompId_right : (X : (Cat,Cat)) -> (F, G : Functor X) -> (a : NatTrans X F G) ->  natComp X F G G a (natId X G) = a

-- here is the big problem: when are two natural transformations a b between two categories C and D equal? We must postulate that this happens when
-- for any object x of C we have that the morphisms a. eta x and b. eta x are equal. 

natTrans_equal : (X : (Cat,Cat)) -> (F, G : Functor) -> (a, b : NatTrans X F G) -> ((x : fst X) -> eta a x = eta b x) -> a = b
