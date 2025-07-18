; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 5
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort A_a_bool_fun_fun$ 0)
(declare-sort B_b_bool_fun_fun$ 0)
(declare-sort B_llist_bool_fun$ 0)
(declare-sort B_llist_a_prod_set$ 0)
(declare-sort B_a_tllist_bool_fun$ 0)
(declare-sort B_llist_a_bool_fun_fun$ 0)
(declare-sort B_llist_b_a_tllist_fun$ 0)
(declare-sort B_llist_a_prod_bool_fun$ 0)
(declare-sort B_llist_b_llist_a_prod_fun$ 0)
(declare-sort A_b_llist_b_a_tllist_fun_fun$ 0)
(declare-sort B_llist_b_llist_bool_fun_fun$ 0)
(declare-sort B_llist_b_a_tllist_fun_bool_fun$ 0)
(declare-sort A_b_llist_b_llist_a_prod_fun_fun$ 0)
(declare-sort B_llist_a_prod_b_a_tllist_bool_fun_fun$ 0)
(declare-sort B_llist_b_llist_a_prod_fun_b_llist_b_a_tllist_fun_bool_fun_fun$ 0)
(declare-codatatypes () ((B_llist$ (lNil$) (lCons$ (lhd$ B$) (ltl$ B_llist$)))))
(declare-datatypes () ((B_llist_a_prod$ (pair$ (fst$ B_llist$) (snd$ A$)))))
(declare-codatatypes () ((B_a_tllist$ (tNil$ (terminal$ A$)) (tCons$ (thd$ B$) (ttl$ B_a_tllist$)))))
(declare-fun uu$ () A_a_bool_fun_fun$)
(declare-fun uua$ () B_llist_b_llist_bool_fun_fun$)
(declare-fun uub$ () B_b_bool_fun_fun$)
(declare-fun uuc$ () A_b_llist_b_llist_a_prod_fun_fun$)
(declare-fun uud$ (B_llist_a_prod_set$) B_llist_a_bool_fun_fun$)
(declare-fun member$ (B_llist_a_prod$ B_llist_a_prod_set$) Bool)
(declare-fun fun_app$ (B_llist_b_llist_a_prod_fun$ B_llist$) B_llist_a_prod$)
(declare-fun rel_fun$ (A_a_bool_fun_fun$ B_llist_b_llist_a_prod_fun_b_llist_b_a_tllist_fun_bool_fun_fun$ A_b_llist_b_llist_a_prod_fun_fun$ A_b_llist_b_a_tllist_fun_fun$) Bool)
(declare-fun fun_app$a (A_b_llist_b_llist_a_prod_fun_fun$ A$) B_llist_b_llist_a_prod_fun$)
(declare-fun fun_app$b (B_llist_bool_fun$ B_llist$) Bool)
(declare-fun fun_app$c (B_llist_b_llist_bool_fun_fun$ B_llist$) B_llist_bool_fun$)
(declare-fun fun_app$d (B_bool_fun$ B$) Bool)
(declare-fun fun_app$e (B_b_bool_fun_fun$ B$) B_bool_fun$)
(declare-fun fun_app$f (A_bool_fun$ A$) Bool)
(declare-fun fun_app$g (A_a_bool_fun_fun$ A$) A_bool_fun$)
(declare-fun fun_app$h (B_llist_a_bool_fun_fun$ B_llist$) A_bool_fun$)
(declare-fun fun_app$i (B_llist_b_a_tllist_fun_bool_fun$ B_llist_b_a_tllist_fun$) Bool)
(declare-fun fun_app$j (B_llist_b_llist_a_prod_fun_b_llist_b_a_tllist_fun_bool_fun_fun$ B_llist_b_llist_a_prod_fun$) B_llist_b_a_tllist_fun_bool_fun$)
(declare-fun fun_app$k (A_b_llist_b_a_tllist_fun_fun$ A$) B_llist_b_a_tllist_fun$)
(declare-fun fun_app$l (B_a_tllist_bool_fun$ B_a_tllist$) Bool)
(declare-fun fun_app$m (B_llist_a_prod_b_a_tllist_bool_fun_fun$ B_llist_a_prod$) B_a_tllist_bool_fun$)
(declare-fun fun_app$n (B_llist_b_a_tllist_fun$ B_llist$) B_a_tllist$)
(declare-fun fun_app$o (B_llist_a_prod_bool_fun$ B_llist_a_prod$) Bool)
(declare-fun rel_fun$a (B_llist_b_llist_bool_fun_fun$ B_llist_a_prod_b_a_tllist_bool_fun_fun$) B_llist_b_llist_a_prod_fun_b_llist_b_a_tllist_fun_bool_fun_fun$)
(declare-fun cr_tllist$ () B_llist_a_prod_b_a_tllist_bool_fun_fun$)
(declare-fun pcr_tllist$ (B_b_bool_fun_fun$ A_a_bool_fun_fun$) B_llist_a_prod_b_a_tllist_bool_fun_fun$)
(declare-fun tllist_of_llist$ () A_b_llist_b_a_tllist_fun_fun$)
(assert (! (forall ((?v0 A$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a uuc$ ?v0) ?v1) (pair$ ?v1 ?v0)) :pattern ((fun_app$ (fun_app$a uuc$ ?v0) ?v1)))) :named a0))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (! (= (fun_app$b (fun_app$c uua$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$b (fun_app$c uua$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 B$) (?v1 B$)) (! (= (fun_app$d (fun_app$e uub$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$d (fun_app$e uub$ ?v0) ?v1)))) :named a2))
(assert (! (forall ((?v0 A$) (?v1 A$)) (! (= (fun_app$f (fun_app$g uu$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$f (fun_app$g uu$ ?v0) ?v1)))) :named a3))
(assert (! (forall ((?v0 B_llist_a_prod_set$) (?v1 B_llist$) (?v2 A$)) (! (= (fun_app$f (fun_app$h (uud$ ?v0) ?v1) ?v2) (member$ (pair$ ?v1 ?v2) ?v0)) :pattern ((fun_app$f (fun_app$h (uud$ ?v0) ?v1) ?v2)))) :named a4))
(assert (! (not (rel_fun$ uu$ (rel_fun$a uua$ (pcr_tllist$ uub$ uu$)) uuc$ tllist_of_llist$)) :named a5))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_llist_b_llist_a_prod_fun_b_llist_b_a_tllist_fun_bool_fun_fun$) (?v2 A_b_llist_b_llist_a_prod_fun_fun$) (?v3 A_b_llist_b_a_tllist_fun_fun$)) (=> (forall ((?v4 A$) (?v5 A$)) (=> (fun_app$f (fun_app$g ?v0 ?v4) ?v5) (fun_app$i (fun_app$j ?v1 (fun_app$a ?v2 ?v4)) (fun_app$k ?v3 ?v5)))) (rel_fun$ ?v0 ?v1 ?v2 ?v3))) :named a6))
(assert (! (forall ((?v0 B_llist_b_llist_bool_fun_fun$) (?v1 B_llist_a_prod_b_a_tllist_bool_fun_fun$) (?v2 B_llist_b_llist_a_prod_fun$) (?v3 B_llist_b_a_tllist_fun$)) (=> (forall ((?v4 B_llist$) (?v5 B_llist$)) (=> (fun_app$b (fun_app$c ?v0 ?v4) ?v5) (fun_app$l (fun_app$m ?v1 (fun_app$ ?v2 ?v4)) (fun_app$n ?v3 ?v5)))) (fun_app$i (fun_app$j (rel_fun$a ?v0 ?v1) ?v2) ?v3))) :named a7))
(assert (! (forall ((?v0 B_llist$) (?v1 A$) (?v2 B_llist$) (?v3 A$)) (= (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a8))
(assert (! (forall ((?v0 B_llist$) (?v1 A$) (?v2 B_llist$) (?v3 A$)) (= (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a9))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_llist_b_llist_bool_fun_fun$) (?v2 B_llist_a_prod_b_a_tllist_bool_fun_fun$) (?v3 A_b_llist_b_llist_a_prod_fun_fun$) (?v4 A_b_llist_b_a_tllist_fun_fun$)) (= (rel_fun$ ?v0 (rel_fun$a ?v1 ?v2) ?v3 ?v4) (forall ((?v5 A$) (?v6 A$)) (=> (fun_app$f (fun_app$g ?v0 ?v5) ?v6) (fun_app$i (fun_app$j (rel_fun$a ?v1 ?v2) (fun_app$a ?v3 ?v5)) (fun_app$k ?v4 ?v6)))))) :named a10))
(assert (! (forall ((?v0 B_llist_a_prod_set$) (?v1 B_llist_a_prod_set$)) (= (= (uud$ ?v0) (uud$ ?v1)) (= ?v0 ?v1))) :named a11))
(assert (! (= (pcr_tllist$ uub$ uu$) cr_tllist$) :named a12))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_llist_b_llist_a_prod_fun_b_llist_b_a_tllist_fun_bool_fun_fun$) (?v2 A_b_llist_b_llist_a_prod_fun_fun$) (?v3 A_b_llist_b_a_tllist_fun_fun$) (?v4 A$) (?v5 A$)) (=> (and (rel_fun$ ?v0 ?v1 ?v2 ?v3) (and (fun_app$f (fun_app$g ?v0 ?v4) ?v5) (=> (fun_app$i (fun_app$j ?v1 (fun_app$a ?v2 ?v4)) (fun_app$k ?v3 ?v5)) false))) false)) :named a13))
(assert (! (forall ((?v0 B_llist_b_llist_bool_fun_fun$) (?v1 B_llist_a_prod_b_a_tllist_bool_fun_fun$) (?v2 B_llist_b_llist_a_prod_fun$) (?v3 B_llist_b_a_tllist_fun$) (?v4 B_llist$) (?v5 B_llist$)) (=> (and (fun_app$i (fun_app$j (rel_fun$a ?v0 ?v1) ?v2) ?v3) (and (fun_app$b (fun_app$c ?v0 ?v4) ?v5) (=> (fun_app$l (fun_app$m ?v1 (fun_app$ ?v2 ?v4)) (fun_app$n ?v3 ?v5)) false))) false)) :named a14))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_llist_b_llist_a_prod_fun_b_llist_b_a_tllist_fun_bool_fun_fun$) (?v2 A_b_llist_b_llist_a_prod_fun_fun$) (?v3 A_b_llist_b_a_tllist_fun_fun$) (?v4 A$)) (=> (and (rel_fun$ ?v0 ?v1 ?v2 ?v3) (fun_app$f (fun_app$g ?v0 ?v4) ?v4)) (fun_app$i (fun_app$j ?v1 (fun_app$a ?v2 ?v4)) (fun_app$k ?v3 ?v4)))) :named a15))
(assert (! (forall ((?v0 B_llist_b_llist_bool_fun_fun$) (?v1 B_llist_a_prod_b_a_tllist_bool_fun_fun$) (?v2 B_llist_b_llist_a_prod_fun$) (?v3 B_llist_b_a_tllist_fun$) (?v4 B_llist$)) (=> (and (fun_app$i (fun_app$j (rel_fun$a ?v0 ?v1) ?v2) ?v3) (fun_app$b (fun_app$c ?v0 ?v4) ?v4)) (fun_app$l (fun_app$m ?v1 (fun_app$ ?v2 ?v4)) (fun_app$n ?v3 ?v4)))) :named a16))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_llist_b_llist_a_prod_fun_b_llist_b_a_tllist_fun_bool_fun_fun$) (?v2 A_b_llist_b_llist_a_prod_fun_fun$) (?v3 A_b_llist_b_a_tllist_fun_fun$) (?v4 A$) (?v5 A$)) (=> (and (rel_fun$ ?v0 ?v1 ?v2 ?v3) (fun_app$f (fun_app$g ?v0 ?v4) ?v5)) (fun_app$i (fun_app$j ?v1 (fun_app$a ?v2 ?v4)) (fun_app$k ?v3 ?v5)))) :named a17))
(assert (! (forall ((?v0 B_llist_b_llist_bool_fun_fun$) (?v1 B_llist_a_prod_b_a_tllist_bool_fun_fun$) (?v2 B_llist_b_llist_a_prod_fun$) (?v3 B_llist_b_a_tllist_fun$) (?v4 B_llist$) (?v5 B_llist$)) (=> (and (fun_app$i (fun_app$j (rel_fun$a ?v0 ?v1) ?v2) ?v3) (fun_app$b (fun_app$c ?v0 ?v4) ?v5)) (fun_app$l (fun_app$m ?v1 (fun_app$ ?v2 ?v4)) (fun_app$n ?v3 ?v5)))) :named a18))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_llist_b_llist_a_prod_fun_b_llist_b_a_tllist_fun_bool_fun_fun$) (?v2 A_b_llist_b_llist_a_prod_fun_fun$) (?v3 A_b_llist_b_a_tllist_fun_fun$) (?v4 A$) (?v5 A$)) (=> (and (rel_fun$ ?v0 ?v1 ?v2 ?v3) (fun_app$f (fun_app$g ?v0 ?v4) ?v5)) (fun_app$i (fun_app$j ?v1 (fun_app$a ?v2 ?v4)) (fun_app$k ?v3 ?v5)))) :named a19))
(assert (! (forall ((?v0 B_llist_b_llist_bool_fun_fun$) (?v1 B_llist_a_prod_b_a_tllist_bool_fun_fun$) (?v2 B_llist_b_llist_a_prod_fun$) (?v3 B_llist_b_a_tllist_fun$) (?v4 B_llist$) (?v5 B_llist$)) (=> (and (fun_app$i (fun_app$j (rel_fun$a ?v0 ?v1) ?v2) ?v3) (fun_app$b (fun_app$c ?v0 ?v4) ?v5)) (fun_app$l (fun_app$m ?v1 (fun_app$ ?v2 ?v4)) (fun_app$n ?v3 ?v5)))) :named a20))
(assert (! (forall ((?v0 B_llist_a_prod$)) (exists ((?v1 B_llist$) (?v2 A$)) (= ?v0 (pair$ ?v1 ?v2)))) :named a21))
(assert (! (forall ((?v0 B_llist$) (?v1 A$) (?v2 B_llist$) (?v3 A$)) (=> (and (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (=> (and (= ?v0 ?v2) (= ?v1 ?v3)) false)) false)) :named a22))
(assert (! (forall ((?v0 B_llist_a_prod$)) (=> (forall ((?v1 B_llist$) (?v2 A$)) (=> (= ?v0 (pair$ ?v1 ?v2)) false)) false)) :named a23))
(assert (! (forall ((?v0 B_llist_a_prod_bool_fun$) (?v1 B_llist_a_prod$)) (=> (forall ((?v2 B_llist$) (?v3 A$)) (fun_app$o ?v0 (pair$ ?v2 ?v3))) (fun_app$o ?v0 ?v1))) :named a24))
(check-sat)
;(get-unsat-core)
