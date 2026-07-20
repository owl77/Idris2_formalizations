# Idris2_formalizations
Investigations into the Idris2 proof assistant and some formalizations

 
Is there a proof assistant which combines the best aspects of Coq/Rocq and Agda? We would like the construction of proof-terms be done in a natural deduction style, close to actual mathematical practice (at least for the proofs of category theory). This is different at once from the top-down method of constructing proofs in Coq/Rocq and from the emacs interface of Agda and its system of refinement, filling holes, etc.

Dependent type theory - extensions of type theories such as used in Ocaml and Haskell - seems to us philosophically, computationally, logically and practically the best foundation for mathematics. The elegant Idris 2 proof assistant - which we could call an idealized version of Agda (but with linear types!) - seems to be  most promising. It is simple and versatile and can work with emacs, vim or nano. Could we use it as a basis to develop our natural deduction style interactive theorem proving?

Idris 2 with its REPL in facy feel like a enhanced version of Ocaml or Haskell (upon which it is based) - but it is not so easy to install (we are running it on an Ubuntu virtual machine in whih we need rlwrap to get command history). 

We can seemlessly formalize category theory in Idris 2 (it seems this can be done in a simpler and more direct way than in Coq/Rocq) - a fact which is already of logico-philosophical significance. 

https://github.com/owl77/Idris2_formalizations/blob/main/ct.idr

As an exercise we prove that any two terminal objects in a category are isomorphic. To do this we show first that given a terminal object T its canonical morphism to itself must be id_T (this is the lemma1 term). This is how in our natural deduction extension of Idris we would construct the lemma1 term in the way a mathematician would prove the result.

1.  c : Cat      Hyp
2.  a : obj C   Hyp 
3.   t : terminal c a   Hyp
4.   t :  forall (x: obj c), exists (g : hom c (x,a)), forall (h: hom c (x,a)), h = g   Expand 3
5.   t a   :  exists (g : hom c(a,a)), forall (h : hom c(a,a)), h = g   Inst 4,2 
6.  snd (ta) :  forall (h : hom c (a,a)), h = fst (ta)           Sigma type stuff
7.  id c a : hom c (a,a) By def
8.  (snd (ta)) (id c a) :  id c a = fst (ta)  Inst 6,7
9. \(c : Cat)(a : obj c)(t : terminal ca),  (snd (ta)) (id c a) : (c: Cat) -> (a : obj c) -> (t : terminal c a) -> h = fst (ta)  QED

