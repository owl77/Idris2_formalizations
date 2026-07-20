

import Prelude
import Data.Singleton
import Data.Fin

-- In this module we define general categories, opposite categories, the category of "sets", the empty, singleton and canonical category with two elements, terminal objects, functors and natural transformations, 
-- point out the necessity of extensionality to define the category of sets and the need to postulate  identity conditions for
-- natural transformations. We prove that functors between categories A and B and their natural transformations form a category.
-- As a result we can define the category of presheaves over a given category A and the yoneda embedding. We define the composition of functors, the identity functors
-- and the "whiskering operations" (Godement product) and use this to define adjunctions in terms of the triangle identities.

-- We believe that Iris 2 is the best (and most efficient) dependent-type based proof assistant for this task, once one understands how to use rewrite and Refl.

-- Much of the formalization below could be rewritten using implicit arguments. 

record Cat where
 constructor MkCat
 obj : Type
 hom : (obj,obj) -> Type
 id : (x: obj) -> hom (x,x)
 comp : (x , y , z : obj) -> ( f : hom (x,y)) -> (g : hom (y,z)) -> hom (x,z)
 id_ax : (x , y : obj) -> (f : hom (x,y)) -> ((comp x x y (id x) f) =  f, (comp x y y f (id y)) = f )
 ass : (x , y, z, w : obj) -> ( f: hom (x,y)) -> (g : hom (y,z)) -> (h : hom (z,w)) -> 
comp x z w (comp x y z f g) h = comp x y w f (comp y z w g h)

op_cat : Cat -> Cat
op_cat c = MkCat (obj c) (\obpair => hom c (snd obpair, fst obpair)) (id c) (\x,y,z => \f,g => comp c z y x g f)
 (\x,y => (\f => (snd(id_ax c y x f), fst(id_ax c y x f) ))) (\x,y,z,w =>( \f,g,h => sym (ass c w z y x h g f)))  

-- the empty category

empty_cat : Cat
empty_cat = MkCat Void (\x => Void) (\x => x) (\x,y,z,f,g => absurd f) (\x,y,f => (absurd f, absurd f)) (\x,y,z,w,f,g,h => absurd f)

-- singleton category
star: Type
star = Singleton 0

-- we need this obvious property of singleton and equality types.

singleton_id : (f : Singleton x ) -> f = Val x
singleton_id (Val x) = Refl

singleton_cat : Cat
singleton_cat = MkCat (Singleton 0) (\x => (Singleton 1)) (\x => Val 1) (\x,y,z,f,g => Val 1) (\x,y,f:Singleton 1 => rewrite (singleton_id f) in (Refl, Refl)) (\x,y,z,w,f,g,h => Refl)

-- category with 2 objects and no non-trivial morphisms

-- data Fin : Nat -> Type where
--   FZ : Fin (S k)
--   FS : Fin k -> Fin (S k)

two_hom: (Fin 2, Fin 2) -> Type

two_hom (FZ, FZ) = Singleton 0
two_hom (FS FZ, FS FZ) = Singleton 0
two_hom (_,_) = Void

two_id : (x: Fin 2) -> two_hom (x,x)
two_id FZ = Val 0
two_id (FS FZ) = Val 0

two_comp : (x,y,z : Fin 2) -> (f : two_hom(x,y)) -> (g : two_hom(y,z)) -> two_hom(x,z)
two_comp FZ FZ FZ f g = Val 0
two_comp (FS FZ) (FS FZ) (FS FZ) f g = Val 0

two_ass : (x,y,z,w : Fin 2) -> (f : two_hom(x,y)) -> (g : two_hom (y,z)) -> (h : two_hom (z,w)) -> 
 two_comp x z w (two_comp x y z f g) h = two_comp x y w f (two_comp y z w g h)

two_ass FZ FZ FZ FZ _ _ _ = Refl
two_ass (FS FZ) (FS FZ) (FS FZ) (FS FZ)  _ _ _ = Refl

two_id_ax : (x,y : Fin 2) -> (f : two_hom(x,y)) -> ((two_comp x x y (two_id x) f) =  f, (two_comp x y y f (two_id y)) = f )

two_id_ax FZ FZ (Val 0) = (Refl, Refl)
two_id_ax (FS FZ) (FS FZ) (Val 0)  = (Refl, Refl)

two_cat = MkCat (Fin 2) (two_hom) (two_id) (two_comp) (two_id_ax) (two_ass)

-- the category of sets is the category of types + extensionality. 

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

pre_set_id_ax_r: (x, y : Type) -> (f : set_hom (x,y)) -> (a : x) -> (set_comp x y y f (set_id y)) a  =  f a
pre_set_id_ax_r x y f a = Refl

set_id_ax_r :( x, y : Type) -> (f : set_hom (x,y)) -> (set_comp x y y f (set_id y) = f)
set_id_ax_r x y f = funExt x y (\a => set_comp x y y f (set_id y) a)  f (pre_set_id_ax_r x y f)

set_id_ax : (x, y : Type) -> (f : set_hom (x,y)) -> (set_comp x x y  (set_id x) f = f, set_comp x y y f (set_id y) = f)
set_id_ax x y f = (set_id_ax_l x y f, set_id_ax_r x y f)

pre_set_ass : (x,y,z,w : Type) -> (f : set_hom (x,y)) -> (g : set_hom (y,z)) -> (h : set_hom (z,w)) -> (a : x) ->
 (set_comp x z w (set_comp x y z f g) h) a = (set_comp x y w f (set_comp y z w g h)) a
pre_set_ass x y z w f g h a = Refl
 
set_ass : (x,y,z,w : Type) -> (f : set_hom (x,y)) -> (g : set_hom (y,z)) -> (h : set_hom (z,w)) ->
 (set_comp x z w (set_comp x y z f g) h)  = (set_comp x y w f (set_comp y z w g h)) 
set_ass x y z w f g h = funExt x w (\a => (set_comp x z w (set_comp x y z f g) h)a  ) (\a => (set_comp x y w f (set_comp y z w g h)) a ) (pre_set_ass x y z w f g h)

set: Cat
set = MkCat Type set_hom set_id set_comp set_id_ax set_ass

-- setOp : Cat
-- setOp = op_cat set


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


diag_chase1 : (c : Cat) -> (x1,x2,x3,y1,y2,y3 : obj c) -> (f1 : hom c (x1,x2)) -> (f2 : hom c (x2,x3)) -> (g1 : hom c (x1,y1))
-> (g2 : hom c (x2,y2)) -> (g3: hom c (x3,y3)) ->  (h1 : hom c (y1,y2)) -> (h2 : hom c (y2,y3)) -> 
(p1 : comp c x1 x2 y2 f1 g2 = comp c x1 y1 y2 g1 h1) -> (p2 : comp c x2 x3 y3 f2 g3 = comp c x2 y2 y3 g2 h2)
-> comp c x1 x3 y3 (comp c x1 x2 x3 f1 f2) g3 = comp c x1 y1 y3 g1 (comp c y1 y2 y3 h1 h2)

diag_chase1 c x1 x2 x3 y1 y2 y3 f1 f2 g1 g2 g3 h1 h2 p1 p2 = let ass1 = ass c x1 x2 x3 y3 f1 f2 g3
 in let aux = rewrite (sym p2) in ass1 in let ass2 = ass c x1 x2 y2 y3 f1 g2 h2 in let aux2 = rewrite ass2 in aux in let aux3 = rewrite (sym p1) in aux2 in let ass3 = ass c x1 y1 y2 y3 g1 h1 h2 in rewrite (sym ass3) in aux3

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


-- here is the big problem: when are two natural transformations a b between two categories C and D equal? We must postulate that this happens when
-- for any object x of C we have that the morphisms a. eta x and b. eta x are equal. 

natTrans_equal : (X : (Cat,Cat)) -> (F, G : Functor X) -> (a, b : NatTrans X F G) -> ((x : obj (fst X)) -> (eta a) x = (eta b) x) -> a = b

pre_natCompId_left : (X : (Cat,Cat)) -> (F, G : Functor X) -> (a : NatTrans X F G) -> (x : obj (fst X)) -> eta (natComp X F F G (natId X F) a) x = (eta a) x

pre_natCompId_left cs fu gu a x =  fst ( id_ax (snd cs) (f_obj fu x) (f_obj gu x) (eta a x)  )

pre_natCompId_right : (X : (Cat,Cat)) -> (F, G : Functor X) -> (a : NatTrans X F G) -> (x : obj (fst X)) -> eta (natComp X F G G a (natId X G) ) x = (eta a ) x

pre_natCompId_right cs fu gu a x =  snd ( id_ax (snd cs) (f_obj fu x) (f_obj gu x) (eta a x)  )

natCompId_left : (X : (Cat,Cat)) -> (F, G : Functor X) -> (a : NatTrans X F G) ->  natComp X F F G (natId X F) a = a
natCompId_left cs fu gu a = natTrans_equal cs fu gu (natComp cs fu fu gu (natId cs fu) a)  a (pre_natCompId_left cs fu gu a)

natCompId_right : (X : (Cat,Cat)) -> (F, G : Functor X) -> (a : NatTrans X F G) ->  natComp X F G G a (natId X G) = a
natCompId_right cs fu gu a = natTrans_equal cs fu gu (natComp cs fu gu gu a (natId cs gu)) a (pre_natCompId_right cs fu gu a)

natCompId : (X : (Cat,Cat)) -> (F, G : Functor X) -> (a : NatTrans X F G) -> ( natComp X F F G (natId X F) a = a,  natComp X F G G a (natId X G) = a)
natCompId cs fu gu a = (natCompId_left cs fu gu a, natCompId_right cs fu gu a)

pre_natAss : (X : (Cat,Cat)) -> (F, G, H, J : Functor X) -> (a : NatTrans X F G) -> (b : NatTrans X G H) -> (c : NatTrans X H J) ->
 (x : obj (fst X)) ->  eta (natComp X F H J (natComp X F G H a b) c) x = eta (natComp X F G J a (natComp X G H J b c)) x
pre_natAss cs fu gu hu ju a b c x = ass (snd cs) (f_obj fu x) (f_obj gu x) (f_obj hu x) (f_obj ju x)(eta a x)(eta b x)(eta c x)

natAss : (X : (Cat,Cat)) -> (F, G, H, J : Functor X) -> (a : NatTrans X F G) -> (b : NatTrans X G H) -> (c : NatTrans X H J) ->
 natComp X F H J (natComp X F G H a b) c  = natComp X F G J a (natComp X G H J b c)
natAss cs fu gu hu ju a b c = natTrans_equal cs fu ju (natComp cs fu hu ju (natComp cs fu gu hu a b) c) (natComp cs fu gu ju a (natComp cs gu hu ju b c)) (pre_natAss cs fu gu hu ju a b c)

functorCat: (X : (Cat,Cat)) -> Cat
functorCat cs = MkCat (Functor cs)(\p => NatTrans cs (fst p) (snd p)) (natId cs)(natComp cs)(natCompId cs) (natAss cs)

presheaves : (X : Cat) -> Cat
presheaves c = functorCat (op_cat c, Main.set)

-- the yoneda functor C_b: C^op -> Set,  a -> set_hom (a,b)

yoneda_obj : (X : Cat) -> (b : obj X) -> (a : obj X) -> Type
yoneda_obj c b a = hom c (a,b)

yoneda_arr : (X : Cat ) -> (b : obj X) -> (x, y : obj X) -> ( f: hom X (y,x)) -> set_hom (yoneda_obj X b x, yoneda_obj X b y)
yoneda_arr c b x y f = \g => comp c y x b f g
 
pre_yoneda_id : (X : Cat ) -> ( b : obj X) -> ( x: obj X) -> (f : hom X (x,b)) ->
 (yoneda_arr X b x x (id X x)) f = set_id (yoneda_obj X b x) f

pre_yoneda_id c b x f = rewrite fst(id_ax c x b f) in Refl

yoneda_id : (X : Cat) -> ( b : obj X) -> (x : obj X) -> (yoneda_arr X b x x (id X x))  = set_id (yoneda_obj X b x) 
yoneda_id c b x = funExt (yoneda_obj c b x) (yoneda_obj c b x) (yoneda_arr c b x x (id c x)) (set_id (yoneda_obj c b x)) (pre_yoneda_id c b x)

pre_yoneda_comp : (X :Cat) -> (b : obj X) -> (x,y,z : obj X) -> (f : hom X (y,x)) -> (g: hom X (z,y)) -> (j : hom X (x,b)) ->
  (yoneda_arr X b x z (comp X z y x g f)) j =  (set_comp (yoneda_obj X b x) (yoneda_obj X b y)(yoneda_obj X b z)
  (yoneda_arr X b x y f) (yoneda_arr X b y z g)) j
 
pre_yoneda_comp c b x y z f g j = rewrite  (ass c z y x b g f j ) in Refl

yoneda_comp : (X :Cat) -> (b : obj X) -> (x,y,z : obj X) -> (f : hom X (y,x)) -> (g: hom X (z,y)) -> 
 (yoneda_arr X b x z (comp X z y x  g f)) =  (set_comp (yoneda_obj X b x) (yoneda_obj X b y)(yoneda_obj X b z) (yoneda_arr X b x y f) (yoneda_arr X b y z g))

yoneda_comp c b x y z f g = funExt (yoneda_obj c b x ) (yoneda_obj c b z )
 (yoneda_arr c b x z (comp c z y x g f))  (set_comp (yoneda_obj c b x) (yoneda_obj c b y)(yoneda_obj c b z)
 (yoneda_arr c b x y f) (yoneda_arr c b y z g))(pre_yoneda_comp c b x y z f g)

yoneda: (X : Cat) -> (b : obj X) -> Functor (op_cat X, Main.set)
yoneda c b = MkFunctor (yoneda_obj c b) (yoneda_arr c b ) (yoneda_id c b) (yoneda_comp c b)

-- this is part of the construction of the yoneda embedding y : C -> Psh(C) 

arrow_yoneda: (X :Cat) -> ( a: obj X) -> ( b : obj X) -> ( f: hom X (a,b)) -> NatTrans (op_cat X, Main.set) (yoneda X a) (yoneda X b)

-- (to be continued)

-- diagrams, cones and limits

delta: (X : (Cat,Cat))-> ( d : obj (snd X)) -> Functor X

delta_obj : (X : (Cat,Cat)) -> (d : obj (snd X)) -> (obj (fst X)) -> (obj (snd X))
delta_obj c d a = d

delta_arr : (X : (Cat,Cat)) -> (d : obj (snd X)) ->
 (x, y : obj (fst X)) -> (hom (fst X) (x,y)) -> (hom (snd X)(delta_obj X d x, delta_obj X d y))
delta_arr c d x y f = id (snd c) d

delta_id : (X : (Cat,Cat)) -> (d : obj (snd X)) -> ( a : obj (fst X)) -> delta_arr X d a a (id (fst X) a) = id (snd X)(delta_obj X d a)
delta_id c d a = Refl

delta_comp : (X : (Cat, Cat)) -> (d : obj (snd X)) -> (x,y,z : obj (fst X)) ->
 (f : hom (fst X) (x,y)) -> (g : hom (fst X) (y,z)) ->
 delta_arr X d x z (comp (fst X) x y z f g) = comp (snd X) (delta_obj X d x) (delta_obj X d y)(delta_obj X d z)(delta_arr X d x y f)(delta_arr X d y z g)
delta_comp c d x y z f g = rewrite fst ( id_ax (snd c) d d (id (snd c) d) ) in Refl
 
delta c d = MkFunctor (delta_obj c d) (delta_arr c d) (delta_id c d) (delta_comp c d)

cone : (X : (Cat,Cat)) -> (F : Functor X) -> (d : obj (snd X)) -> Type
cone c f d = NatTrans c (delta c d) f

limit : (X : (Cat,Cat)) -> (F : Functor X) -> (d : obj (snd X) ) -> ( l: cone X F d) -> Type

limit cs fu d l = (e : obj (snd cs)) -> (m : cone cs fu e) -> 
 (n : NatTrans cs (delta cs e) (delta cs d) ** (natComp cs (delta cs e)(delta cs d) fu n l = m,
 (t : NatTrans cs (delta cs e) (delta cs d)) -> (natComp cs (delta cs e)(delta cs d) fu t l = m) -> t = n) )
 
-- Preliminaries for Adjunctions

FunCompose : {X,Y,Z :Cat} -> (F : Functor (X,Y)) -> (G : Functor (Y,Z)) -> Functor (X,Z)

FunCompose_obj : {X,Y,Z :Cat} -> (F : Functor (X,Y)) -> (G : Functor (Y,Z)) -> (x : obj X) -> (obj Z)
FunCompose_obj fu gu x = f_obj gu (f_obj fu x)

FunCompose_arr : {X,Y,Z :Cat} -> (F : Functor (X,Y)) -> (G : Functor (Y,Z)) -> (x,y : obj X) -> (f : hom X (x,y)) -> hom Z (FunCompose_obj F G x, FunCompose_obj F G y)
FunCompose_arr fu gu x y f = arr gu (f_obj fu x) (f_obj fu y) (arr fu x y f)

FunCompose_id : {X,Y,Z : Cat} -> (F : Functor (X,Y)) -> (G : Functor (Y,Z)) -> (x : obj X) -> FunCompose_arr F G x x (id X x) = id Z (FunCompose_obj F G x) 
FunCompose_id fu gu x =  rewrite (f_id fu x) in (rewrite (f_id gu (f_obj fu x)) in Refl)

FunCompose_arr_ax : {X,Y,Z :Cat} -> (F : Functor (X,Y)) -> (G : Functor (Y,Z)) -> (x,y,z : obj X) -> (f : hom X (x,y)) -> (g: hom X (y,z)) ->
 FunCompose_arr F G x z (comp X x y z f g) = comp Z (FunCompose_obj F G x) (FunCompose_obj F G y) (FunCompose_obj F G z)(FunCompose_arr F G x y f)(FunCompose_arr F G y z g)

FunCompose_arr_ax fu gu x y z f g = rewrite (f_comp fu x y z f g) in (rewrite f_comp gu (f_obj fu x)(f_obj fu y)(f_obj fu z) (arr fu x y f) (arr fu y z g) in Refl)

FunCompose fu gu = MkFunctor (FunCompose_obj fu gu) (FunCompose_arr fu gu)(FunCompose_id fu gu)(FunCompose_arr_ax fu gu)

FunctorId : (X :Cat) -> Functor (X,X)
FunctorId c = MkFunctor (\x => x) (\x,y,f => f) (\x => Refl) (\x,y,z,f,g => Refl) 

-- Whiskerings

RightWhisker : {X,Y,Z :Cat} -> (F,G : Functor (X,Y)) -> (H: Functor (Y,Z)) -> (a : NatTrans (X,Y) F G) -> NatTrans(X,Z) (FunCompose F H) (FunCompose G H)

RightWhisker_eta: {X,Y,Z :Cat} -> (F,G : Functor (X,Y)) -> (H: Functor (Y,Z)) -> (a : NatTrans (X,Y) F G) -> (x : obj X) -> 
 hom Z ((f_obj (FunCompose F H) x), (f_obj (FunCompose G H) x))

RightWhisker_eta fu gu hu a x = arr hu (f_obj fu x) (f_obj gu x) (eta a x)
 
RightWhisker_com : {X,Y,Z :Cat} -> (F,G : Functor (X,Y)) -> (H: Functor (Y,Z)) -> (a : NatTrans (X,Y) F G) -> (x,y : obj X) -> (f : hom X (x,y))->
 comp Z (FunCompose_obj F H x) (FunCompose_obj G H x) (FunCompose_obj G H y) (RightWhisker_eta F G H a x) (arr (FunCompose G H ) x y f)
 = comp Z (FunCompose_obj F H x) (FunCompose_obj F H y) (FunCompose_obj G H y) (arr (FunCompose F H) x y f) (RightWhisker_eta F G H a y)

RightWhisker_com fu gu hu a x y f = rewrite sym (f_comp hu (f_obj fu x) (f_obj gu x) (f_obj gu y)(eta a x)(arr gu x y f)) in (rewrite sym (f_comp hu (f_obj fu x) (f_obj fu y) (f_obj gu y) (arr fu x y f)(eta a y)) in (rewrite (com a x y f) in Refl ) )

RightWhisker fu gu hu a = MkNatTrans (RightWhisker_eta fu gu hu a) (RightWhisker_com fu gu hu a)

LeftWhisker : {Z, X, Y  : Cat} -> ( H : Functor (Z,X)) -> (F,G : Functor (X,Y)) -> (a : NatTrans (X,Y) F G) -> NatTrans(Z,Y) (FunCompose H F) (FunCompose H G)

LeftWhisker_eta : {Z,X,Y : Cat} ->  ( H : Functor (Z,X)) -> (F,G : Functor (X,Y)) -> (a : NatTrans (X,Y) F G) -> (z : obj Z) -> 
 hom Y ((f_obj (FunCompose H F) z), (f_obj (FunCompose H G) z))

LeftWhisker_eta hu fu gu a z = eta a (f_obj hu z)

LeftWhisker_com : {Z,X,Y :Cat} -> (H : Functor (Z,X)) -> (F,G : Functor (X,Y)) -> (a : NatTrans (X,Y) F G) -> (y,z : obj Z) -> (f : hom Z (y,z))->
 comp Y (FunCompose_obj H F y) (FunCompose_obj H G y) (FunCompose_obj H G z) (LeftWhisker_eta H F G a y) (arr (FunCompose H G ) y z f)
 = comp Y (FunCompose_obj  H F y) (FunCompose_obj  H F z) (FunCompose_obj H G z) (arr (FunCompose H F ) y z f) (LeftWhisker_eta H F G a z)

LeftWhisker_com hu fu gu a y z f = com a (f_obj hu y) (f_obj hu z) (arr hu y z f) 

LeftWhisker hu fu gu a = MkNatTrans (LeftWhisker_eta hu fu gu a)(LeftWhisker_com hu fu gu a)

-- Adjunctions

record Adjunction (X, Y : Cat) (L: Functor (X,Y)) (R: Functor (Y,X)) where
  constructor MkAdjunction
  eta : NatTrans (X,X) (FunctorId X) (FunCompose L R) 
  epsilon : NatTrans (Y,Y) (FunCompose R L) (FunctorId Y)
--  triangle1:
--  triangle2:



