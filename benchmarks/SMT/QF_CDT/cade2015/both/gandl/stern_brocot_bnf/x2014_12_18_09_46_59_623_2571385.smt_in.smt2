; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 595
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort Nat$ 0)
(declare-datatypes () ((Nat_nat_prod$ (pair$ (fst$ Nat$) (snd$ Nat$)))
  (Nat_nat_prod_nat_nat_prod_prod$ (pair$a (fst$a Nat_nat_prod$) (snd$a Nat_nat_prod$)))
  (Dir$ (l$) (r$))))
(declare-codatatypes () ((Nat_nat_prod_nat_nat_prod_prod_tree$ (node$ (root$ Nat_nat_prod_nat_nat_prod_prod$) (left$ Nat_nat_prod_nat_nat_prod_prod_tree$) (right$ Nat_nat_prod_nat_nat_prod_prod_tree$)))))
(declare-datatypes () ((Dir_list$ (nil$) (cons$ (hd$ Dir$) (tl$ Dir_list$)))))
(declare-codatatypes () ((Nat_tree$ (node$a (root$a Nat$) (left$a Nat_tree$) (right$a Nat_tree$)))
  (Nat_tree_tree$ (node$b (root$b Nat_tree$) (left$b Nat_tree_tree$) (right$b Nat_tree_tree$)))
  (Nat_tree_tree_tree$ (node$c (root$c Nat_tree_tree$) (left$c Nat_tree_tree_tree$) (right$c Nat_tree_tree_tree$)))))
(declare-fun d$ () Dir$)
(declare-fun m$ () Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun d$a () Dir$)
(declare-fun pm$ () Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun det$ (Nat_nat_prod_nat_nat_prod_prod$) Nat$)
(declare-fun one$ () Nat$)
(declare-fun imat$ () Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun one$a () Nat_tree_tree$)
(declare-fun one$b () Nat_tree$)
(declare-fun one$c () Nat_tree_tree_tree$)
(declare-fun path$ () Dir_list$)
(declare-fun lLmat$ () Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun uRmat$ () Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun mulmat$ (Nat_nat_prod_nat_nat_prod_prod$ Nat_nat_prod_nat_nat_prod_prod$) Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun of_nat$ (Nat$) Nat_tree_tree$)
(declare-fun of_nat$a (Nat$) Nat_tree$)
(declare-fun of_nat$b (Nat$) Nat$)
(declare-fun tree_pure$ (Nat_tree_tree$) Nat_tree_tree_tree$)
(declare-fun tree_pure$a (Nat_tree$) Nat_tree_tree$)
(declare-fun tree_pure$b (Nat$) Nat_tree$)
(declare-fun traverse_tree$ (Dir_list$ Nat_nat_prod_nat_nat_prod_prod_tree$) Nat_nat_prod_nat_nat_prod_prod_tree$)
(declare-fun stern_brocot_iterate_aux$ (Nat_nat_prod_nat_nat_prod_prod$) Nat_nat_prod_nat_nat_prod_prod_tree$)
(assert (! (not (= (det$ pm$) one$)) :named a0))
(assert (! (not (= d$ d$a)) :named a1))
(assert (! (= pm$ (root$ (traverse_tree$ path$ (stern_brocot_iterate_aux$ imat$)))) :named a2))
(assert (! (= (det$ m$) one$) :named a3))
(assert (! (= (det$ imat$) one$) :named a4))
(assert (! (= (det$ lLmat$) one$) :named a5))
(assert (! (= (det$ uRmat$) one$) :named a6))
(assert (! (= one$ one$) :named a7))
(assert (! (forall ((?v0 Nat_tree_tree$)) (= (= one$a ?v0) (= ?v0 one$a))) :named a8))
(assert (! (forall ((?v0 Nat_tree$)) (= (= one$b ?v0) (= ?v0 one$b))) :named a9))
(assert (! (forall ((?v0 Nat$)) (= (= one$ ?v0) (= ?v0 one$))) :named a10))
(assert (! (forall ((?v0 Nat_nat_prod_nat_nat_prod_prod$)) (=> (= (det$ ?v0) one$) (= (det$ (mulmat$ ?v0 lLmat$)) one$))) :named a11))
(assert (! (forall ((?v0 Nat_nat_prod_nat_nat_prod_prod$)) (=> (= (det$ ?v0) one$) (= (det$ (mulmat$ ?v0 uRmat$)) one$))) :named a12))
(assert (! (forall ((?v0 Nat_nat_prod_nat_nat_prod_prod$)) (=> (= (det$ ?v0) one$) (= (det$ (mulmat$ lLmat$ ?v0)) one$))) :named a13))
(assert (! (forall ((?v0 Nat_nat_prod_nat_nat_prod_prod$)) (=> (= (det$ ?v0) one$) (= (det$ (mulmat$ uRmat$ ?v0)) one$))) :named a14))
(assert (! (forall ((?v0 Nat_nat_prod_nat_nat_prod_prod$) (?v1 Dir_list$)) (exists ((?v2 Nat_nat_prod_nat_nat_prod_prod$)) (and (= (mulmat$ ?v0 ?v2) (root$ (traverse_tree$ ?v1 (stern_brocot_iterate_aux$ ?v0)))) (= (det$ ?v2) one$)))) :named a15))
(assert (! (= (of_nat$ one$) one$a) :named a16))
(assert (! (= (of_nat$a one$) one$b) :named a17))
(assert (! (= (of_nat$b one$) one$) :named a18))
(assert (! (= one$c (tree_pure$ one$a)) :named a19))
(assert (! (= one$a (tree_pure$a one$b)) :named a20))
(assert (! (= one$b (tree_pure$b one$)) :named a21))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (of_nat$a ?v0) (of_nat$a ?v1)) (= ?v0 ?v1))) :named a22))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (of_nat$b ?v0) (of_nat$b ?v1)) (= ?v0 ?v1))) :named a23))
(check-sat)
;(get-unsat-core)
