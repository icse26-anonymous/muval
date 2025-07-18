; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 477
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_a_a_fun_fun$ 0)
(declare-sort A_a_fun_a_fun$ 0)
(declare-sort A_tree_a_tree_fun$ 0)
(declare-sort A_a_fun_a_a_fun_fun$ 0)
(declare-sort A_a_fun_a_fun_a_fun$ 0)
(declare-sort A_a_a_fun_fun_a_a_fun_fun$ 0)
(declare-sort A_a_fun_a_a_fun_fun_a_fun$ 0)
(declare-sort A_a_fun_a_fun_a_a_fun_fun$ 0)
(declare-sort A_tree_tree_a_tree_tree_fun$ 0)
(declare-sort A_tree_a_tree_fun_a_tree_fun$ 0)
(declare-sort A_a_fun_tree_a_a_fun_tree_fun$ 0)
(declare-sort A_a_fun_a_a_fun_fun_a_a_fun_fun$ 0)
(declare-sort A_a_fun_a_fun_a_a_fun_a_fun_fun$ 0)
(declare-sort A_a_fun_a_a_fun_fun_a_a_fun_a_fun_fun$ 0)
(declare-sort A_a_fun_a_fun_a_a_fun_a_a_fun_fun_fun$ 0)
(declare-sort A_tree_tree_tree_a_tree_tree_tree_fun$ 0)
(declare-sort A_a_fun_tree_tree_a_a_fun_tree_tree_fun$ 0)
(declare-sort A_tree_a_tree_fun_a_tree_a_tree_fun_fun$ 0)
(declare-sort A_a_fun_a_fun_tree_a_a_fun_a_fun_tree_fun$ 0)
(declare-sort A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ 0)
(declare-sort A_a_fun_a_fun_a_fun_a_a_fun_a_fun_a_fun_fun$ 0)
(declare-sort A_tree_tree_a_tree_tree_fun_a_tree_tree_fun$ 0)
(declare-sort A_a_fun_tree_a_a_fun_tree_fun_a_a_fun_tree_fun$ 0)
(declare-sort A_a_fun_a_fun_a_a_fun_a_fun_fun_a_a_fun_a_fun_fun$ 0)
(declare-sort A_a_fun_a_fun_a_a_fun_fun_a_a_fun_a_fun_a_fun_fun$ 0)
(declare-sort A_tree_tree_a_tree_tree_fun_a_tree_tree_a_tree_tree_fun_fun$ 0)
(declare-sort A_tree_a_tree_fun_a_tree_fun_a_tree_a_tree_fun_a_tree_fun_fun$ 0)
(declare-sort A_a_fun_tree_a_a_fun_tree_fun_a_a_fun_tree_a_a_fun_tree_fun_fun$ 0)
(declare-sort A_a_fun_a_fun_a_a_fun_a_fun_fun_a_a_fun_a_fun_a_a_fun_a_fun_fun_fun$ 0)
(declare-codatatypes () ((A_tree$ (node$ (root$ A$) (left$ A_tree$) (right$ A_tree$)))
  (A_a_fun_tree$ (node$a (select$ A_a_fun$) (selecta$ A_a_fun_tree$) (selectb$ A_a_fun_tree$)))
  (A_tree_tree$ (node$b (root$a A_tree$) (left$a A_tree_tree$) (right$a A_tree_tree$)))
  (A_a_fun_tree_tree$ (node$c (root$b A_a_fun_tree$) (left$b A_a_fun_tree_tree$) (right$b A_a_fun_tree_tree$)))
  (A_tree_tree_tree$ (node$d (root$c A_tree_tree$) (left$c A_tree_tree_tree$) (right$c A_tree_tree_tree$)))
  (A_a_fun_a_fun_tree$ (node$e (selectc$ A_a_fun_a_fun$) (selectd$ A_a_fun_a_fun_tree$) (selecte$ A_a_fun_a_fun_tree$)))))
(declare-fun l$ () A_a_fun$)
(declare-fun r$ () A_a_fun$)
(declare-fun x$ () A$)
(declare-fun id$ () A_a_fun$)
(declare-fun uu$ () A_a_fun_a_fun$)
(declare-fun id$a () A_a_fun_tree_a_a_fun_tree_fun$)
(declare-fun id$b () A_tree_tree_a_tree_tree_fun$)
(declare-fun id$c () A_a_fun_a_fun_a_a_fun_a_fun_fun$)
(declare-fun id$d () A_tree_a_tree_fun$)
(declare-fun id$e () A_a_fun_a_a_fun_fun$)
(declare-fun id$f () A_a_fun_tree_tree_a_a_fun_tree_tree_fun$)
(declare-fun id$g () A_tree_tree_tree_a_tree_tree_tree_fun$)
(declare-fun id$h () A_a_fun_a_fun_tree_a_a_fun_a_fun_tree_fun$)
(declare-fun id$i () A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$)
(declare-fun id$j () A_tree_a_tree_fun_a_tree_a_tree_fun_fun$)
(declare-fun uua$ () A_a_fun_a_a_fun_fun$)
(declare-fun uub$ () A_a_fun_a_a_fun_fun$)
(declare-fun uuc$ (A_a_fun$) A_a_fun_a_a_fun_fun_a_a_fun_fun$)
(declare-fun uud$ (A_a_fun_a_a_fun_fun$) A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$)
(declare-fun uue$ (A_tree$) A_tree_a_tree_fun_a_tree_fun$)
(declare-fun uuf$ (A_tree_a_tree_fun$) A_tree_a_tree_fun_a_tree_a_tree_fun_fun$)
(declare-fun uug$ (A_a_fun$) A_a_fun_a_fun_a_fun$)
(declare-fun uuh$ (A_a_fun_a_a_fun_fun$) A_a_fun_a_fun_a_a_fun_a_fun_fun$)
(declare-fun uui$ (A$) A_a_fun_a_fun$)
(declare-fun uuj$ (A_a_fun$) A_a_fun_a_a_fun_fun$)
(declare-fun uuk$ () A_a_fun_a_a_fun_fun$)
(declare-fun uul$ () A_tree_a_tree_fun$)
(declare-fun uum$ () A_a_fun$)
(declare-fun uun$ (A_a_fun_tree$) A_a_fun_tree_a_a_fun_tree_fun_a_a_fun_tree_fun$)
(declare-fun uuo$ (A_a_fun_tree_a_a_fun_tree_fun$) A_a_fun_tree_a_a_fun_tree_fun_a_a_fun_tree_a_a_fun_tree_fun_fun$)
(declare-fun uup$ (A_tree_tree$) A_tree_tree_a_tree_tree_fun_a_tree_tree_fun$)
(declare-fun uuq$ (A_tree_tree_a_tree_tree_fun$) A_tree_tree_a_tree_tree_fun_a_tree_tree_a_tree_tree_fun_fun$)
(declare-fun uur$ (A_a_fun_a_fun$) A_a_fun_a_fun_a_a_fun_a_fun_fun_a_a_fun_a_fun_fun$)
(declare-fun uus$ (A_a_fun_a_fun_a_a_fun_a_fun_fun$) A_a_fun_a_fun_a_a_fun_a_fun_fun_a_a_fun_a_fun_a_a_fun_a_fun_fun_fun$)
(declare-fun comp$ (A_a_fun$) A_a_fun_a_a_fun_fun$)
(declare-fun comp$a (A_tree_tree_a_tree_tree_fun$) A_tree_tree_a_tree_tree_fun_a_tree_tree_a_tree_tree_fun_fun$)
(declare-fun comp$b (A_a_fun_tree_a_a_fun_tree_fun$) A_a_fun_tree_a_a_fun_tree_fun_a_a_fun_tree_a_a_fun_tree_fun_fun$)
(declare-fun comp$c (A_tree_a_tree_fun$) A_tree_a_tree_fun_a_tree_a_tree_fun_fun$)
(declare-fun comp$d (A_a_fun_a_fun_a_a_fun_a_fun_fun$) A_a_fun_a_fun_a_a_fun_a_fun_fun_a_a_fun_a_fun_a_a_fun_a_fun_fun_fun$)
(declare-fun comp$e (A_a_fun_a_a_fun_fun$) A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$)
(declare-fun comp$f (A_a_fun_a_fun$) A_a_fun_a_a_fun_fun_a_a_fun_a_fun_fun$)
(declare-fun comp$g (A_a_fun$) A_a_fun_a_fun_a_a_fun_a_fun_fun$)
(declare-fun comp$h (A_a_fun_a_fun$) A_a_a_fun_fun_a_a_fun_fun$)
(declare-fun comp$i (A_a_fun$) A_a_fun_a_fun_a_fun_a_a_fun_a_fun_a_fun_fun$)
(declare-fun comp$j (A_a_fun_a_fun$) A_a_fun_a_fun_a_a_fun_fun_a_a_fun_a_fun_a_fun_fun$)
(declare-fun comp$k (A_tree_a_tree_fun$) A_tree_a_tree_fun_a_tree_fun_a_tree_a_tree_fun_a_tree_fun_fun$)
(declare-fun comp$l (A_a_fun_a_fun$ A_a_fun_a_a_fun_fun_a_a_fun_fun$) A_a_fun_a_a_fun_fun_a_fun$)
(declare-fun comp$m (A_a_a_fun_fun$) A_a_fun_a_fun_a_a_fun_a_a_fun_fun_fun$)
(declare-fun fun_app$ (A_a_fun_a_a_fun_fun$ A_a_fun$) A_a_fun$)
(declare-fun fun_app$a (A_a_fun_a_fun$ A_a_fun$) A$)
(declare-fun fun_app$b (A_a_fun$ A$) A$)
(declare-fun fun_app$c (A_tree_tree_a_tree_tree_fun_a_tree_tree_a_tree_tree_fun_fun$ A_tree_tree_a_tree_tree_fun$) A_tree_tree_a_tree_tree_fun$)
(declare-fun fun_app$d (A_a_fun_tree_a_a_fun_tree_fun_a_a_fun_tree_a_a_fun_tree_fun_fun$ A_a_fun_tree_a_a_fun_tree_fun$) A_a_fun_tree_a_a_fun_tree_fun$)
(declare-fun fun_app$e (A_tree_a_tree_fun_a_tree_a_tree_fun_fun$ A_tree_a_tree_fun$) A_tree_a_tree_fun$)
(declare-fun fun_app$f (A_a_fun_a_fun_a_a_fun_a_fun_fun_a_a_fun_a_fun_a_a_fun_a_fun_fun_fun$ A_a_fun_a_fun_a_a_fun_a_fun_fun$) A_a_fun_a_fun_a_a_fun_a_fun_fun$)
(declare-fun fun_app$g (A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun_a_a_fun_fun$) A_a_fun_a_a_fun_fun$)
(declare-fun fun_app$h (A_a_fun_a_fun_a_a_fun_a_fun_fun$ A_a_fun_a_fun$) A_a_fun_a_fun$)
(declare-fun fun_app$i (A_a_fun_a_a_fun_fun_a_a_fun_a_fun_fun$ A_a_fun_a_a_fun_fun$) A_a_fun_a_fun$)
(declare-fun fun_app$j (A_tree_tree_a_tree_tree_fun_a_tree_tree_fun$ A_tree_tree_a_tree_tree_fun$) A_tree_tree$)
(declare-fun fun_app$k (A_tree_tree_a_tree_tree_fun$ A_tree_tree$) A_tree_tree$)
(declare-fun fun_app$l (A_a_fun_tree_a_a_fun_tree_fun_a_a_fun_tree_fun$ A_a_fun_tree_a_a_fun_tree_fun$) A_a_fun_tree$)
(declare-fun fun_app$m (A_a_fun_tree_a_a_fun_tree_fun$ A_a_fun_tree$) A_a_fun_tree$)
(declare-fun fun_app$n (A_tree_a_tree_fun_a_tree_fun$ A_tree_a_tree_fun$) A_tree$)
(declare-fun fun_app$o (A_tree_a_tree_fun$ A_tree$) A_tree$)
(declare-fun fun_app$p (A_a_fun_a_fun_a_a_fun_a_fun_fun_a_a_fun_a_fun_fun$ A_a_fun_a_fun_a_a_fun_a_fun_fun$) A_a_fun_a_fun$)
(declare-fun fun_app$q (A_a_fun_a_a_fun_fun_a_a_fun_fun$ A_a_fun_a_a_fun_fun$) A_a_fun$)
(declare-fun fun_app$r (A_a_fun_a_fun_a_fun$ A_a_fun_a_fun$) A$)
(declare-fun fun_app$s (A_a_a_fun_fun_a_a_fun_fun$ A_a_a_fun_fun$) A_a_fun$)
(declare-fun fun_app$t (A_a_fun_a_fun_a_fun_a_a_fun_a_fun_a_fun_fun$ A_a_fun_a_fun_a_fun$) A_a_fun_a_fun_a_fun$)
(declare-fun fun_app$u (A_a_fun_a_fun_a_a_fun_fun_a_a_fun_a_fun_a_fun_fun$ A_a_fun_a_fun_a_a_fun_fun$) A_a_fun_a_fun_a_fun$)
(declare-fun fun_app$v (A_tree_a_tree_fun_a_tree_fun_a_tree_a_tree_fun_a_tree_fun_fun$ A_tree_a_tree_fun_a_tree_fun$) A_tree_a_tree_fun_a_tree_fun$)
(declare-fun fun_app$w (A_a_fun_a_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun_a_fun$) A_a_fun_a_a_fun_fun$)
(declare-fun fun_app$x (A_a_fun_tree_tree_a_a_fun_tree_tree_fun$ A_a_fun_tree_tree$) A_a_fun_tree_tree$)
(declare-fun fun_app$y (A_tree_tree_tree_a_tree_tree_tree_fun$ A_tree_tree_tree$) A_tree_tree_tree$)
(declare-fun fun_app$z (A_a_fun_a_fun_tree_a_a_fun_a_fun_tree_fun$ A_a_fun_a_fun_tree$) A_a_fun_a_fun_tree$)
(declare-fun map_tree$ (A_a_fun$) A_tree_a_tree_fun$)
(declare-fun map_tree$a (A_a_fun_a_a_fun_fun$) A_a_fun_tree_a_a_fun_tree_fun$)
(declare-fun map_tree$b (A_tree_a_tree_fun$) A_tree_tree_a_tree_tree_fun$)
(declare-fun map_tree$c (A_a_fun_a_fun$ A_a_fun_tree$) A_tree$)
(declare-fun map_tree$d (A_a_a_fun_fun$ A_tree$) A_a_fun_tree$)
(declare-fun map_tree$e (A_a_fun_tree_a_a_fun_tree_fun$) A_a_fun_tree_tree_a_a_fun_tree_tree_fun$)
(declare-fun map_tree$f (A_tree_tree_a_tree_tree_fun$) A_tree_tree_tree_a_tree_tree_tree_fun$)
(declare-fun map_tree$g (A_a_fun_a_fun_a_a_fun_a_fun_fun$) A_a_fun_a_fun_tree_a_a_fun_a_fun_tree_fun$)
(declare-fun unfold_tree$ (A_a_fun_a_fun$ A_a_fun_a_a_fun_fun$ A_a_fun_a_a_fun_fun$ A_a_fun$) A_tree$)
(declare-fun tree_recurse$ (A_a_fun_tree_a_a_fun_tree_fun$ A_a_fun_tree_a_a_fun_tree_fun$ A_a_fun_tree$) A_a_fun_tree_tree$)
(declare-fun unfold_tree$a (A_a_fun_a_a_fun_fun_a_a_fun_fun$ A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun_a_a_fun_fun$) A_a_fun_tree$)
(declare-fun unfold_tree$b (A_tree_a_tree_fun_a_tree_fun$ A_tree_a_tree_fun_a_tree_a_tree_fun_fun$ A_tree_a_tree_fun_a_tree_a_tree_fun_fun$ A_tree_a_tree_fun$) A_tree_tree$)
(declare-fun unfold_tree$c (A_a_fun_a_fun_a_fun$ A_a_fun_a_fun_a_a_fun_a_fun_fun$ A_a_fun_a_fun_a_a_fun_a_fun_fun$ A_a_fun_a_fun$) A_tree$)
(declare-fun unfold_tree$d (A_a_fun$ A_a_fun$ A_a_fun$ A$) A_tree$)
(declare-fun unfold_tree$e (A_a_a_fun_fun$ A_a_fun$ A_a_fun$ A$) A_a_fun_tree$)
(declare-fun unfold_tree$f (A_tree_a_tree_fun$ A_tree_a_tree_fun$ A_tree_a_tree_fun$ A_tree$) A_tree_tree$)
(declare-fun unfold_tree$g (A_a_fun_a_a_fun_fun$ A_a_fun_a_a_fun_fun$ A_a_fun_a_a_fun_fun$ A_a_fun$) A_a_fun_tree$)
(declare-fun unfold_tree$h (A_a_fun_a_fun_a_a_fun_fun$ A_a_fun_a_fun_a_a_fun_a_fun_fun$ A_a_fun_a_fun_a_a_fun_a_fun_fun$ A_a_fun_a_fun$) A_a_fun_tree$)
(declare-fun unfold_tree$i (A_a_fun_a_a_fun_fun_a_fun$ A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun_a_a_fun_fun$) A_tree$)
(declare-fun unfold_tree$j (A_a_fun_tree_a_a_fun_tree_fun_a_a_fun_tree_fun$ A_a_fun_tree_a_a_fun_tree_fun_a_a_fun_tree_a_a_fun_tree_fun_fun$ A_a_fun_tree_a_a_fun_tree_fun_a_a_fun_tree_a_a_fun_tree_fun_fun$ A_a_fun_tree_a_a_fun_tree_fun$) A_a_fun_tree_tree$)
(declare-fun unfold_tree$k (A_tree_tree_a_tree_tree_fun_a_tree_tree_fun$ A_tree_tree_a_tree_tree_fun_a_tree_tree_a_tree_tree_fun_fun$ A_tree_tree_a_tree_tree_fun_a_tree_tree_a_tree_tree_fun_fun$ A_tree_tree_a_tree_tree_fun$) A_tree_tree_tree$)
(declare-fun unfold_tree$l (A_a_fun_a_fun_a_a_fun_a_fun_fun_a_a_fun_a_fun_fun$ A_a_fun_a_fun_a_a_fun_a_fun_fun_a_a_fun_a_fun_a_a_fun_a_fun_fun_fun$ A_a_fun_a_fun_a_a_fun_a_fun_fun_a_a_fun_a_fun_a_a_fun_a_fun_fun_fun$ A_a_fun_a_fun_a_a_fun_a_fun_fun$) A_a_fun_a_fun_tree$)
(declare-fun tree_recurse$a (A_tree_tree_a_tree_tree_fun$ A_tree_tree_a_tree_tree_fun$ A_tree_tree$) A_tree_tree_tree$)
(declare-fun tree_recurse$b (A_a_fun_a_fun_a_a_fun_a_fun_fun$ A_a_fun_a_fun_a_a_fun_a_fun_fun$ A_a_fun_a_fun$) A_a_fun_a_fun_tree$)
(declare-fun tree_recurse$c (A_tree_a_tree_fun$ A_tree_a_tree_fun$ A_tree$) A_tree_tree$)
(declare-fun tree_recurse$d (A_a_fun_a_a_fun_fun$ A_a_fun_a_a_fun_fun$ A_a_fun$) A_a_fun_tree$)
(declare-fun tree_recurse$e (A_a_fun$ A_a_fun$ A$) A_tree$)
(assert (! (forall ((?v0 A_a_fun$)) (! (= (fun_app$ uub$ ?v0) (fun_app$ (comp$ ?v0) r$)) :pattern ((fun_app$ uub$ ?v0)))) :named a0))
(assert (! (forall ((?v0 A_a_fun$)) (! (= (fun_app$ uua$ ?v0) (fun_app$ (comp$ ?v0) l$)) :pattern ((fun_app$ uua$ ?v0)))) :named a1))
(assert (! (forall ((?v0 A_a_fun$)) (! (= (fun_app$a uu$ ?v0) (fun_app$b ?v0 x$)) :pattern ((fun_app$a uu$ ?v0)))) :named a2))
(assert (! (forall ((?v0 A_tree_tree_a_tree_tree_fun$) (?v1 A_tree_tree_a_tree_tree_fun$)) (! (= (fun_app$c (uuq$ ?v0) ?v1) (fun_app$c (comp$a ?v1) ?v0)) :pattern ((fun_app$c (uuq$ ?v0) ?v1)))) :named a3))
(assert (! (forall ((?v0 A_a_fun_tree_a_a_fun_tree_fun$) (?v1 A_a_fun_tree_a_a_fun_tree_fun$)) (! (= (fun_app$d (uuo$ ?v0) ?v1) (fun_app$d (comp$b ?v1) ?v0)) :pattern ((fun_app$d (uuo$ ?v0) ?v1)))) :named a4))
(assert (! (forall ((?v0 A_tree_a_tree_fun$) (?v1 A_tree_a_tree_fun$)) (! (= (fun_app$e (uuf$ ?v0) ?v1) (fun_app$e (comp$c ?v1) ?v0)) :pattern ((fun_app$e (uuf$ ?v0) ?v1)))) :named a5))
(assert (! (forall ((?v0 A_a_fun_a_fun_a_a_fun_a_fun_fun$) (?v1 A_a_fun_a_fun_a_a_fun_a_fun_fun$)) (! (= (fun_app$f (uus$ ?v0) ?v1) (fun_app$f (comp$d ?v1) ?v0)) :pattern ((fun_app$f (uus$ ?v0) ?v1)))) :named a6))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$) (?v1 A_a_fun_a_a_fun_fun$)) (! (= (fun_app$g (uud$ ?v0) ?v1) (fun_app$g (comp$e ?v1) ?v0)) :pattern ((fun_app$g (uud$ ?v0) ?v1)))) :named a7))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$) (?v1 A_a_fun_a_fun$)) (! (= (fun_app$h (uuh$ ?v0) ?v1) (fun_app$i (comp$f ?v1) ?v0)) :pattern ((fun_app$h (uuh$ ?v0) ?v1)))) :named a8))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$)) (! (= (fun_app$ (uuj$ ?v0) ?v1) (fun_app$ (comp$ ?v1) ?v0)) :pattern ((fun_app$ (uuj$ ?v0) ?v1)))) :named a9))
(assert (! (forall ((?v0 A_tree_tree$) (?v1 A_tree_tree_a_tree_tree_fun$)) (! (= (fun_app$j (uup$ ?v0) ?v1) (fun_app$k ?v1 ?v0)) :pattern ((fun_app$j (uup$ ?v0) ?v1)))) :named a10))
(assert (! (forall ((?v0 A_a_fun_tree$) (?v1 A_a_fun_tree_a_a_fun_tree_fun$)) (! (= (fun_app$l (uun$ ?v0) ?v1) (fun_app$m ?v1 ?v0)) :pattern ((fun_app$l (uun$ ?v0) ?v1)))) :named a11))
(assert (! (forall ((?v0 A_tree$) (?v1 A_tree_a_tree_fun$)) (! (= (fun_app$n (uue$ ?v0) ?v1) (fun_app$o ?v1 ?v0)) :pattern ((fun_app$n (uue$ ?v0) ?v1)))) :named a12))
(assert (! (forall ((?v0 A_a_fun_a_fun$) (?v1 A_a_fun_a_fun_a_a_fun_a_fun_fun$)) (! (= (fun_app$p (uur$ ?v0) ?v1) (fun_app$h ?v1 ?v0)) :pattern ((fun_app$p (uur$ ?v0) ?v1)))) :named a13))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun_a_a_fun_fun$)) (! (= (fun_app$q (uuc$ ?v0) ?v1) (fun_app$ ?v1 ?v0)) :pattern ((fun_app$q (uuc$ ?v0) ?v1)))) :named a14))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun_a_fun$)) (! (= (fun_app$r (uug$ ?v0) ?v1) (fun_app$a ?v1 ?v0)) :pattern ((fun_app$r (uug$ ?v0) ?v1)))) :named a15))
(assert (! (forall ((?v0 A$) (?v1 A_a_fun$)) (! (= (fun_app$a (uui$ ?v0) ?v1) (fun_app$b ?v1 ?v0)) :pattern ((fun_app$a (uui$ ?v0) ?v1)))) :named a16))
(assert (! (forall ((?v0 A_tree$)) (! (= (fun_app$o uul$ ?v0) ?v0) :pattern ((fun_app$o uul$ ?v0)))) :named a17))
(assert (! (forall ((?v0 A_a_fun$)) (! (= (fun_app$ uuk$ ?v0) ?v0) :pattern ((fun_app$ uuk$ ?v0)))) :named a18))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$b uum$ ?v0) ?v0) :pattern ((fun_app$b uum$ ?v0)))) :named a19))
(assert (! (not (= (unfold_tree$ uu$ uua$ uub$ id$) (node$ x$ (fun_app$o (map_tree$ l$) (unfold_tree$ uu$ uua$ uub$ id$)) (fun_app$o (map_tree$ r$) (unfold_tree$ uu$ uua$ uub$ id$))))) :named a20))
(assert (! (forall ((?v0 A$) (?v1 A_tree$) (?v2 A_tree$) (?v3 A$) (?v4 A_tree$) (?v5 A_tree$)) (= (= (node$ ?v0 ?v1 ?v2) (node$ ?v3 ?v4 ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))) :named a21))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$) (?v1 A_a_fun$) (?v2 A_a_fun_a_a_fun_fun$) (?v3 A_a_fun_a_a_fun_fun$) (?v4 A_a_fun_a_a_fun_fun$)) (= (fun_app$m (map_tree$a ?v0) (unfold_tree$a (uuc$ ?v1) (uud$ ?v2) (uud$ ?v3) ?v4)) (unfold_tree$a (uuc$ ?v1) (uud$ ?v2) (uud$ ?v3) (fun_app$g (comp$e ?v0) ?v4)))) :named a22))
(assert (! (forall ((?v0 A_tree_a_tree_fun$) (?v1 A_tree$) (?v2 A_tree_a_tree_fun$) (?v3 A_tree_a_tree_fun$) (?v4 A_tree_a_tree_fun$)) (= (fun_app$k (map_tree$b ?v0) (unfold_tree$b (uue$ ?v1) (uuf$ ?v2) (uuf$ ?v3) ?v4)) (unfold_tree$b (uue$ ?v1) (uuf$ ?v2) (uuf$ ?v3) (fun_app$e (comp$c ?v0) ?v4)))) :named a23))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_a_fun_a_a_fun_fun$) (?v3 A_a_fun_a_a_fun_fun$) (?v4 A_a_fun_a_fun$)) (= (fun_app$o (map_tree$ ?v0) (unfold_tree$c (uug$ ?v1) (uuh$ ?v2) (uuh$ ?v3) ?v4)) (unfold_tree$c (uug$ ?v1) (uuh$ ?v2) (uuh$ ?v3) (fun_app$h (comp$g ?v0) ?v4)))) :named a24))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$) (?v2 A_a_fun$) (?v3 A_a_fun$) (?v4 A_a_fun$)) (= (fun_app$o (map_tree$ ?v0) (unfold_tree$ (uui$ ?v1) (uuj$ ?v2) (uuj$ ?v3) ?v4)) (unfold_tree$ (uui$ ?v1) (uuj$ ?v2) (uuj$ ?v3) (fun_app$ (comp$ ?v0) ?v4)))) :named a25))
(assert (! (forall ((?v0 A_a_fun_a_fun_a_fun$) (?v1 A_a_fun_a_fun_a_a_fun_a_fun_fun$) (?v2 A_a_fun_a_fun_a_a_fun_a_fun_fun$) (?v3 A_a_fun_a_fun$)) (= (unfold_tree$c ?v0 ?v1 ?v2 ?v3) (node$ (fun_app$r ?v0 ?v3) (unfold_tree$c ?v0 ?v1 ?v2 (fun_app$h ?v1 ?v3)) (unfold_tree$c ?v0 ?v1 ?v2 (fun_app$h ?v2 ?v3))))) :named a26))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun_a_a_fun_fun$) (?v1 A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$) (?v2 A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$) (?v3 A_a_fun_a_a_fun_fun$)) (= (unfold_tree$a ?v0 ?v1 ?v2 ?v3) (node$a (fun_app$q ?v0 ?v3) (unfold_tree$a ?v0 ?v1 ?v2 (fun_app$g ?v1 ?v3)) (unfold_tree$a ?v0 ?v1 ?v2 (fun_app$g ?v2 ?v3))))) :named a27))
(assert (! (forall ((?v0 A_tree_a_tree_fun_a_tree_fun$) (?v1 A_tree_a_tree_fun_a_tree_a_tree_fun_fun$) (?v2 A_tree_a_tree_fun_a_tree_a_tree_fun_fun$) (?v3 A_tree_a_tree_fun$)) (= (unfold_tree$b ?v0 ?v1 ?v2 ?v3) (node$b (fun_app$n ?v0 ?v3) (unfold_tree$b ?v0 ?v1 ?v2 (fun_app$e ?v1 ?v3)) (unfold_tree$b ?v0 ?v1 ?v2 (fun_app$e ?v2 ?v3))))) :named a28))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_a_fun$) (?v3 A$)) (= (unfold_tree$d ?v0 ?v1 ?v2 ?v3) (node$ (fun_app$b ?v0 ?v3) (unfold_tree$d ?v0 ?v1 ?v2 (fun_app$b ?v1 ?v3)) (unfold_tree$d ?v0 ?v1 ?v2 (fun_app$b ?v2 ?v3))))) :named a29))
(assert (! (forall ((?v0 A_a_fun_a_fun$) (?v1 A_a_fun_a_a_fun_fun$) (?v2 A_a_fun_a_a_fun_fun$) (?v3 A_a_fun$)) (= (unfold_tree$ ?v0 ?v1 ?v2 ?v3) (node$ (fun_app$a ?v0 ?v3) (unfold_tree$ ?v0 ?v1 ?v2 (fun_app$ ?v1 ?v3)) (unfold_tree$ ?v0 ?v1 ?v2 (fun_app$ ?v2 ?v3))))) :named a30))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_a_fun$) (?v3 A_a_fun$) (?v4 A$)) (= (fun_app$o (map_tree$ ?v0) (unfold_tree$d ?v1 ?v2 ?v3 ?v4)) (unfold_tree$d (fun_app$ (comp$ ?v0) ?v1) ?v2 ?v3 ?v4))) :named a31))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun_a_fun$) (?v2 A_a_fun_a_a_fun_fun$) (?v3 A_a_fun_a_a_fun_fun$) (?v4 A_a_fun$)) (= (fun_app$o (map_tree$ ?v0) (unfold_tree$ ?v1 ?v2 ?v3 ?v4)) (unfold_tree$ (fun_app$h (comp$g ?v0) ?v1) ?v2 ?v3 ?v4))) :named a32))
(assert (! (forall ((?v0 A_a_fun_a_fun$) (?v1 A_a_a_fun_fun$) (?v2 A_a_fun$) (?v3 A_a_fun$) (?v4 A$)) (= (map_tree$c ?v0 (unfold_tree$e ?v1 ?v2 ?v3 ?v4)) (unfold_tree$d (fun_app$s (comp$h ?v0) ?v1) ?v2 ?v3 ?v4))) :named a33))
(assert (! (forall ((?v0 A_tree_a_tree_fun$) (?v1 A_tree_a_tree_fun$) (?v2 A_tree_a_tree_fun$) (?v3 A_tree_a_tree_fun$) (?v4 A_tree$)) (= (fun_app$k (map_tree$b ?v0) (unfold_tree$f ?v1 ?v2 ?v3 ?v4)) (unfold_tree$f (fun_app$e (comp$c ?v0) ?v1) ?v2 ?v3 ?v4))) :named a34))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun_a_fun_a_fun$) (?v2 A_a_fun_a_fun_a_a_fun_a_fun_fun$) (?v3 A_a_fun_a_fun_a_a_fun_a_fun_fun$) (?v4 A_a_fun_a_fun$)) (= (fun_app$o (map_tree$ ?v0) (unfold_tree$c ?v1 ?v2 ?v3 ?v4)) (unfold_tree$c (fun_app$t (comp$i ?v0) ?v1) ?v2 ?v3 ?v4))) :named a35))
(assert (! (forall ((?v0 A_a_fun_a_fun$) (?v1 A_a_fun_a_a_fun_fun$) (?v2 A_a_fun_a_a_fun_fun$) (?v3 A_a_fun_a_a_fun_fun$) (?v4 A_a_fun$)) (= (map_tree$c ?v0 (unfold_tree$g ?v1 ?v2 ?v3 ?v4)) (unfold_tree$ (fun_app$i (comp$f ?v0) ?v1) ?v2 ?v3 ?v4))) :named a36))
(assert (! (forall ((?v0 A_a_fun_a_fun$) (?v1 A_a_fun_a_fun_a_a_fun_fun$) (?v2 A_a_fun_a_fun_a_a_fun_a_fun_fun$) (?v3 A_a_fun_a_fun_a_a_fun_a_fun_fun$) (?v4 A_a_fun_a_fun$)) (= (map_tree$c ?v0 (unfold_tree$h ?v1 ?v2 ?v3 ?v4)) (unfold_tree$c (fun_app$u (comp$j ?v0) ?v1) ?v2 ?v3 ?v4))) :named a37))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$) (?v1 A_a_fun_a_a_fun_fun$) (?v2 A_a_fun_a_a_fun_fun$) (?v3 A_a_fun_a_a_fun_fun$) (?v4 A_a_fun$)) (= (fun_app$m (map_tree$a ?v0) (unfold_tree$g ?v1 ?v2 ?v3 ?v4)) (unfold_tree$g (fun_app$g (comp$e ?v0) ?v1) ?v2 ?v3 ?v4))) :named a38))
(assert (! (forall ((?v0 A_tree_a_tree_fun$) (?v1 A_tree_a_tree_fun_a_tree_fun$) (?v2 A_tree_a_tree_fun_a_tree_a_tree_fun_fun$) (?v3 A_tree_a_tree_fun_a_tree_a_tree_fun_fun$) (?v4 A_tree_a_tree_fun$)) (= (fun_app$k (map_tree$b ?v0) (unfold_tree$b ?v1 ?v2 ?v3 ?v4)) (unfold_tree$b (fun_app$v (comp$k ?v0) ?v1) ?v2 ?v3 ?v4))) :named a39))
(assert (! (forall ((?v0 A_a_fun_a_fun$) (?v1 A_a_fun_a_a_fun_fun_a_a_fun_fun$) (?v2 A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$) (?v3 A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$) (?v4 A_a_fun_a_a_fun_fun$)) (= (map_tree$c ?v0 (unfold_tree$a ?v1 ?v2 ?v3 ?v4)) (unfold_tree$i (comp$l ?v0 ?v1) ?v2 ?v3 ?v4))) :named a40))
(assert (! (forall ((?v0 A_a_fun_a_fun$) (?v1 A_a_fun$) (?v2 A_a_fun_tree$) (?v3 A_a_fun_tree$)) (! (= (map_tree$c ?v0 (node$a ?v1 ?v2 ?v3)) (node$ (fun_app$a ?v0 ?v1) (map_tree$c ?v0 ?v2) (map_tree$c ?v0 ?v3))) :pattern ((map_tree$c ?v0 (node$a ?v1 ?v2 ?v3))))) :named a41))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$) (?v1 A_a_fun$) (?v2 A_a_fun_tree$) (?v3 A_a_fun_tree$)) (! (= (fun_app$m (map_tree$a ?v0) (node$a ?v1 ?v2 ?v3)) (node$a (fun_app$ ?v0 ?v1) (fun_app$m (map_tree$a ?v0) ?v2) (fun_app$m (map_tree$a ?v0) ?v3))) :pattern ((fun_app$m (map_tree$a ?v0) (node$a ?v1 ?v2 ?v3))))) :named a42))
(assert (! (forall ((?v0 A_tree_a_tree_fun$) (?v1 A_tree$) (?v2 A_tree_tree$) (?v3 A_tree_tree$)) (! (= (fun_app$k (map_tree$b ?v0) (node$b ?v1 ?v2 ?v3)) (node$b (fun_app$o ?v0 ?v1) (fun_app$k (map_tree$b ?v0) ?v2) (fun_app$k (map_tree$b ?v0) ?v3))) :pattern ((fun_app$k (map_tree$b ?v0) (node$b ?v1 ?v2 ?v3))))) :named a43))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$) (?v2 A_tree$) (?v3 A_tree$)) (! (= (fun_app$o (map_tree$ ?v0) (node$ ?v1 ?v2 ?v3)) (node$ (fun_app$b ?v0 ?v1) (fun_app$o (map_tree$ ?v0) ?v2) (fun_app$o (map_tree$ ?v0) ?v3))) :pattern ((fun_app$o (map_tree$ ?v0) (node$ ?v1 ?v2 ?v3))))) :named a44))
(assert (! (forall ((?v0 A_a_a_fun_fun$) (?v1 A_a_fun_a_fun$) (?v2 A_a_fun_tree$)) (= (map_tree$d ?v0 (map_tree$c ?v1 ?v2)) (fun_app$m (map_tree$a (fun_app$w (comp$m ?v0) ?v1)) ?v2))) :named a45))
(assert (! (forall ((?v0 A_a_fun_a_fun$) (?v1 A_a_a_fun_fun$) (?v2 A_tree$)) (= (map_tree$c ?v0 (map_tree$d ?v1 ?v2)) (fun_app$o (map_tree$ (fun_app$s (comp$h ?v0) ?v1)) ?v2))) :named a46))
(assert (! (forall ((?v0 A_a_fun_a_fun$) (?v1 A_a_fun_a_a_fun_fun$) (?v2 A_a_fun_tree$)) (= (map_tree$c ?v0 (fun_app$m (map_tree$a ?v1) ?v2)) (map_tree$c (fun_app$i (comp$f ?v0) ?v1) ?v2))) :named a47))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$) (?v1 A_a_fun_a_a_fun_fun$) (?v2 A_a_fun_tree$)) (= (fun_app$m (map_tree$a ?v0) (fun_app$m (map_tree$a ?v1) ?v2)) (fun_app$m (map_tree$a (fun_app$g (comp$e ?v0) ?v1)) ?v2))) :named a48))
(assert (! (forall ((?v0 A_tree_a_tree_fun$) (?v1 A_tree_a_tree_fun$) (?v2 A_tree_tree$)) (= (fun_app$k (map_tree$b ?v0) (fun_app$k (map_tree$b ?v1) ?v2)) (fun_app$k (map_tree$b (fun_app$e (comp$c ?v0) ?v1)) ?v2))) :named a49))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun_a_fun$) (?v2 A_a_fun_tree$)) (= (fun_app$o (map_tree$ ?v0) (map_tree$c ?v1 ?v2)) (map_tree$c (fun_app$h (comp$g ?v0) ?v1) ?v2))) :named a50))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_tree$)) (= (fun_app$o (map_tree$ ?v0) (fun_app$o (map_tree$ ?v1) ?v2)) (fun_app$o (map_tree$ (fun_app$ (comp$ ?v0) ?v1)) ?v2))) :named a51))
(assert (! (forall ((?v0 A_a_fun_tree$)) (= (fun_app$m (map_tree$a uuk$) ?v0) ?v0)) :named a52))
(assert (! (forall ((?v0 A_tree_tree$)) (= (fun_app$k (map_tree$b uul$) ?v0) ?v0)) :named a53))
(assert (! (forall ((?v0 A_tree$)) (= (fun_app$o (map_tree$ uum$) ?v0) ?v0)) :named a54))
(assert (! (forall ((?v0 A_a_fun_tree_tree$)) (= (fun_app$x (map_tree$e id$a) ?v0) ?v0)) :named a55))
(assert (! (forall ((?v0 A_tree_tree_tree$)) (= (fun_app$y (map_tree$f id$b) ?v0) ?v0)) :named a56))
(assert (! (forall ((?v0 A_a_fun_a_fun_tree$)) (= (fun_app$z (map_tree$g id$c) ?v0) ?v0)) :named a57))
(assert (! (forall ((?v0 A_tree_tree$)) (= (fun_app$k (map_tree$b id$d) ?v0) ?v0)) :named a58))
(assert (! (forall ((?v0 A_a_fun_tree$)) (= (fun_app$m (map_tree$a id$e) ?v0) ?v0)) :named a59))
(assert (! (forall ((?v0 A_tree$)) (= (fun_app$o (map_tree$ id$) ?v0) ?v0)) :named a60))
(assert (! (= (map_tree$e id$a) id$f) :named a61))
(assert (! (= (map_tree$f id$b) id$g) :named a62))
(assert (! (= (map_tree$g id$c) id$h) :named a63))
(assert (! (= (map_tree$b id$d) id$b) :named a64))
(assert (! (= (map_tree$a id$e) id$a) :named a65))
(assert (! (= (map_tree$ id$) id$d) :named a66))
(assert (! (forall ((?v0 A_tree$)) (=> (forall ((?v1 A$) (?v2 A_tree$) (?v3 A_tree$)) (=> (= ?v0 (node$ ?v1 ?v2 ?v3)) false)) false)) :named a67))
(assert (! (forall ((?v0 A_a_fun_a_fun$)) (= (fun_app$i (comp$f ?v0) id$e) ?v0)) :named a68))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$)) (= (fun_app$g (comp$e ?v0) id$e) ?v0)) :named a69))
(assert (! (forall ((?v0 A_tree_a_tree_fun$)) (= (fun_app$e (comp$c ?v0) id$d) ?v0)) :named a70))
(assert (! (forall ((?v0 A_a_fun$)) (= (fun_app$ (comp$ ?v0) id$) ?v0)) :named a71))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$)) (= (fun_app$g (comp$e id$e) ?v0) ?v0)) :named a72))
(assert (! (forall ((?v0 A_tree_a_tree_fun$)) (= (fun_app$e (comp$c id$d) ?v0) ?v0)) :named a73))
(assert (! (forall ((?v0 A_a_fun_a_fun$)) (= (fun_app$h (comp$g id$) ?v0) ?v0)) :named a74))
(assert (! (forall ((?v0 A_a_fun$)) (= (fun_app$ (comp$ id$) ?v0) ?v0)) :named a75))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$)) (= (fun_app$g (comp$e id$e) ?v0) ?v0)) :named a76))
(assert (! (forall ((?v0 A_tree_a_tree_fun$)) (= (fun_app$e (comp$c id$d) ?v0) ?v0)) :named a77))
(assert (! (forall ((?v0 A_a_fun_a_fun$)) (= (fun_app$h (comp$g id$) ?v0) ?v0)) :named a78))
(assert (! (forall ((?v0 A_a_fun$)) (= (fun_app$ (comp$ id$) ?v0) ?v0)) :named a79))
(assert (! (forall ((?v0 A_a_fun_tree_a_a_fun_tree_fun$) (?v1 A_a_fun_tree_a_a_fun_tree_fun$) (?v2 A_a_fun_tree$)) (= (tree_recurse$ ?v0 ?v1 ?v2) (unfold_tree$j (uun$ ?v2) (uuo$ ?v0) (uuo$ ?v1) id$a))) :named a80))
(assert (! (forall ((?v0 A_tree_tree_a_tree_tree_fun$) (?v1 A_tree_tree_a_tree_tree_fun$) (?v2 A_tree_tree$)) (= (tree_recurse$a ?v0 ?v1 ?v2) (unfold_tree$k (uup$ ?v2) (uuq$ ?v0) (uuq$ ?v1) id$b))) :named a81))
(assert (! (forall ((?v0 A_a_fun_a_fun_a_a_fun_a_fun_fun$) (?v1 A_a_fun_a_fun_a_a_fun_a_fun_fun$) (?v2 A_a_fun_a_fun$)) (= (tree_recurse$b ?v0 ?v1 ?v2) (unfold_tree$l (uur$ ?v2) (uus$ ?v0) (uus$ ?v1) id$c))) :named a82))
(assert (! (forall ((?v0 A_tree_a_tree_fun$) (?v1 A_tree_a_tree_fun$) (?v2 A_tree$)) (= (tree_recurse$c ?v0 ?v1 ?v2) (unfold_tree$b (uue$ ?v2) (uuf$ ?v0) (uuf$ ?v1) id$d))) :named a83))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$) (?v1 A_a_fun_a_a_fun_fun$) (?v2 A_a_fun$)) (= (tree_recurse$d ?v0 ?v1 ?v2) (unfold_tree$a (uuc$ ?v2) (uud$ ?v0) (uud$ ?v1) id$e))) :named a84))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A$)) (= (tree_recurse$e ?v0 ?v1 ?v2) (unfold_tree$ (uui$ ?v2) (uuj$ ?v0) (uuj$ ?v1) id$))) :named a85))
(assert (! (forall ((?v0 A_a_fun_tree$)) (! (= (fun_app$m id$a ?v0) ?v0) :pattern ((fun_app$m id$a ?v0)))) :named a86))
(assert (! (forall ((?v0 A_tree_tree$)) (! (= (fun_app$k id$b ?v0) ?v0) :pattern ((fun_app$k id$b ?v0)))) :named a87))
(assert (! (forall ((?v0 A_a_fun_a_fun$)) (! (= (fun_app$h id$c ?v0) ?v0) :pattern ((fun_app$h id$c ?v0)))) :named a88))
(assert (! (forall ((?v0 A_tree$)) (! (= (fun_app$o id$d ?v0) ?v0) :pattern ((fun_app$o id$d ?v0)))) :named a89))
(assert (! (forall ((?v0 A_a_fun$)) (! (= (fun_app$ id$e ?v0) ?v0) :pattern ((fun_app$ id$e ?v0)))) :named a90))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$b id$ ?v0) ?v0) :pattern ((fun_app$b id$ ?v0)))) :named a91))
(assert (! (forall ((?v0 A_a_fun_a_fun$) (?v1 A_a_fun_a_a_fun_fun$) (?v2 A_a_fun$)) (! (= (fun_app$a (fun_app$i (comp$f ?v0) ?v1) ?v2) (fun_app$a ?v0 (fun_app$ ?v1 ?v2))) :pattern ((fun_app$a (fun_app$i (comp$f ?v0) ?v1) ?v2)))) :named a92))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$) (?v1 A_a_fun_a_a_fun_fun$) (?v2 A_a_fun$)) (! (= (fun_app$ (fun_app$g (comp$e ?v0) ?v1) ?v2) (fun_app$ ?v0 (fun_app$ ?v1 ?v2))) :pattern ((fun_app$ (fun_app$g (comp$e ?v0) ?v1) ?v2)))) :named a93))
(assert (! (forall ((?v0 A_tree_a_tree_fun$) (?v1 A_tree_a_tree_fun$) (?v2 A_tree$)) (! (= (fun_app$o (fun_app$e (comp$c ?v0) ?v1) ?v2) (fun_app$o ?v0 (fun_app$o ?v1 ?v2))) :pattern ((fun_app$o (fun_app$e (comp$c ?v0) ?v1) ?v2)))) :named a94))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun_a_fun$) (?v2 A_a_fun$)) (! (= (fun_app$a (fun_app$h (comp$g ?v0) ?v1) ?v2) (fun_app$b ?v0 (fun_app$a ?v1 ?v2))) :pattern ((fun_app$a (fun_app$h (comp$g ?v0) ?v1) ?v2)))) :named a95))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A$)) (! (= (fun_app$b (fun_app$ (comp$ ?v0) ?v1) ?v2) (fun_app$b ?v0 (fun_app$b ?v1 ?v2))) :pattern ((fun_app$b (fun_app$ (comp$ ?v0) ?v1) ?v2)))) :named a96))
(assert (! (= (comp$e id$e) id$i) :named a97))
(assert (! (= (comp$c id$d) id$j) :named a98))
(assert (! (= (comp$g id$) id$c) :named a99))
(assert (! (= (comp$ id$) id$e) :named a100))
(check-sat)
;(get-unsat-core)
