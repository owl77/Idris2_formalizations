# Idris2_formalizations
Investigations into the Idris2 proof assistant and some formalizations


Our dream is to devise a proof assistant which combines the best aspects of Coq/Rocq and Agda.  The idea is to have a core minimalist version of dependent type theory in which the construction of proof-terms be done in a natural deduction style which corresponds closely to actual mathematical practice (we are taking the proofs of category theory as our guide - so our conclusions might not hold in general).  Thus our philosophy is different at once from the top-down method of constructing proofs in Coq/Rocq and from the complicated emacs interface of Agda and its system of inference.

Dependent type theory - extensions of the type theories such as those of Ocaml and Haskell - seem to us to be philosophically, computationally, logically and practically the best foundation of mathematics. The Idris 2 proof assistant - which is versatile and elegant, a kind of idealized version of Agda - seems to be the most promising basis for achieving our goal.  The convenient interface for constructing of proof terms in Idris 2 is a good basis for investigating the possibility of our natural deduction project. Idris 2 with its REPL feels like a enhanced version of Ocaml or Haskell (upon which it is based). It is however not so easy to install (we managed to do it after some difficulties on an Ubuntu virtual machine) and at the moment one has to use rlwrap to get the command history in the REPL.

We can easily and naturally formalize category theory in Idris 2 (as we can do in Coq/Rocq) - a fact which is already of huge logico-philosophical significance - and we can study simple concrete examples of how our proof term construction which follows natural deduction should look like. Consider the fragment 

https://github.com/owl77/Idris2_formalizations/blob/main/ct.idr

in which we wish to prove that any two terminal objects in a category are isomorphic. To do this we show first that given a terminal object T its canonical morphism to itself must be id_T (this is the lemma1 term). This is how in our modified version of Idris we would construct the lemma1 term in the (natural deduction) way a mathematician would prove the result.

1.  c : Cat      Hyp
2.  a : obj C   Hyp 
3.   t : terminal c a   Hyp
4.   t :  forall (x: obj c), exists (g : hom c (x,a)), forall (h: hom c (x,a)), h = g   Expand 3
5.   t a   :  exists (g : hom c(a,a)), forall (h : hom c(a,a)), h = g   Inst 4,2 
6.  snd (ta) :  forall (h : hom c (a,a)), h = fst (ta)           Sigma type stuff
7.  id c a : hom c (a,a)              By def.
8  (snd (ta)) (id c a) :  id c a = fst (ta)  Inst 6,7
9 \(c : Cat)(a : obj c)(t : terminal ca),  (snd (ta)) (id c a) : (c: Cat) -> (a : obj c) -> (t : terminal c a) -> h = fst (ta)  QED

