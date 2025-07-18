; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 19
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_llist_a_fun$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-sort A_llist_a_llist_prod_a_fun$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun$ 0)
(declare-sort A_llist_a_llist_prod_bool_fun$ 0)
(declare-sort A_llist_a_llist_prod_a_llist_fun$ 0)
(declare-sort A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ 0)
(declare-sort A_llist_a_llist_prod_a_llist_fun_a_llist_a_llist_prod_a_fun_fun$ 0)
(declare-sort A_llist_a_llist_fun_a_llist_a_llist_prod_a_llist_a_llist_prod_fun_fun$ 0)
(declare-sort A_llist_a_llist_prod_a_llist_fun_a_llist_a_llist_prod_a_llist_fun_fun$ 0)
(declare-sort A_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun$ 0)
(declare-sort A_llist_a_llist_prod_a_fun_a_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-datatypes () ((A_llist_a_llist_prod$ (pair$ (fst$ A_llist$) (snd$ A_llist$)))))
(declare-fun uu$ () A_llist_a_llist_bool_fun_fun$)
(declare-fun xs$ () A_llist$)
(declare-fun inf$ (A_llist$) A_llist_a_llist_fun$)
(declare-fun uua$ () A_llist_a_fun$)
(declare-fun uub$ () A_llist_a_llist_prod_a_llist_fun$)
(declare-fun uuc$ () A_llist_a_llist_fun$)
(declare-fun uud$ () A_llist_a_llist_fun$)
(declare-fun uue$ (Bool A_llist_a_llist_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun comp$ (A_llist_a_fun$) A_llist_a_llist_prod_a_llist_fun_a_llist_a_llist_prod_a_fun_fun$)
(declare-fun comp$a (A_llist_a_llist_prod_a_llist_fun$) A_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun$)
(declare-fun comp$b (A_llist_a_llist_fun$) A_llist_a_llist_prod_a_llist_fun_a_llist_a_llist_prod_a_llist_fun_fun$)
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun fun_app$a (A_llist_a_fun$ A_llist$) A$)
(declare-fun fun_app$b (A_llist_a_llist_prod_a_llist_fun$ A_llist_a_llist_prod$) A_llist$)
(declare-fun fun_app$c (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun fun_app$d (A_llist_a_llist_bool_fun_fun$ A_llist$) A_llist_bool_fun$)
(declare-fun fun_app$e (A_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun$ A_llist_a_llist_prod_a_llist_a_llist_prod_fun$) A_llist_a_llist_prod_a_llist_fun$)
(declare-fun fun_app$f (A_llist_a_llist_prod_a_fun_a_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun_fun$ A_llist_a_llist_prod_a_fun$) A_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun$)
(declare-fun fun_app$g (A_llist_a_llist_prod_a_llist_fun_a_llist_a_llist_prod_a_fun_fun$ A_llist_a_llist_prod_a_llist_fun$) A_llist_a_llist_prod_a_fun$)
(declare-fun fun_app$h (A_llist_a_llist_fun_a_llist_a_llist_prod_a_llist_a_llist_prod_fun_fun$ A_llist_a_llist_fun$) A_llist_a_llist_prod_a_llist_a_llist_prod_fun$)
(declare-fun fun_app$i (A_llist_a_llist_prod_a_llist_fun_a_llist_a_llist_prod_a_llist_fun_fun$ A_llist_a_llist_prod_a_llist_fun$) A_llist_a_llist_prod_a_llist_fun$)
(declare-fun fun_app$j (A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ A_llist_a_llist_prod$) A_llist_a_llist_prod$)
(declare-fun fun_app$k (A_llist_a_llist_prod_bool_fun$ A_llist_a_llist_prod$) Bool)
(declare-fun fun_app$l (A_llist_a_llist_prod_a_fun$ A_llist_a_llist_prod$) A$)
(declare-fun map_prod$ (A_llist_a_llist_fun$) A_llist_a_llist_fun_a_llist_a_llist_prod_a_llist_a_llist_prod_fun_fun$)
(declare-fun case_prod$ (A_llist_a_llist_bool_fun_fun$) A_llist_a_llist_prod_bool_fun$)
(declare-fun unfold_llist$ (A_llist_a_llist_prod_bool_fun$) A_llist_a_llist_prod_a_fun_a_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun_fun$)
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ uuc$ ?v0) (ltl$ ?v0)) :pattern ((fun_app$ uuc$ ?v0)))) :named a0))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$a uua$ ?v0) (lhd$ ?v0)) :pattern ((fun_app$a uua$ ?v0)))) :named a1))
(assert (! (forall ((?v0 A_llist_a_llist_prod$)) (! (= (fun_app$b uub$ ?v0) (snd$ ?v0)) :pattern ((fun_app$b uub$ ?v0)))) :named a2))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (= (fun_app$c (fun_app$d uu$ ?v0) ?v1) (=> (and (not (= ?v0 lNil$)) (not (= ?v1 lNil$))) (not (= (lhd$ ?v0) (lhd$ ?v1))))) :pattern ((fun_app$c (fun_app$d uu$ ?v0) ?v1)))) :named a3))
(assert (! (forall ((?v0 Bool) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$c (fun_app$d (uue$ ?v0 ?v1) ?v2) ?v3) (and ?v0 (fun_app$c (fun_app$d ?v1 ?v2) ?v3))) :pattern ((fun_app$c (fun_app$d (uue$ ?v0 ?v1) ?v2) ?v3)))) :named a4))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ uud$ ?v0) ?v0) :pattern ((fun_app$ uud$ ?v0)))) :named a5))
(assert (! (not (= (fun_app$b (fun_app$e (fun_app$f (unfold_llist$ (case_prod$ uu$)) (fun_app$g (comp$ uua$) uub$)) (fun_app$h (map_prod$ uuc$) uuc$)) (pair$ lNil$ xs$)) lNil$)) :named a6))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (fun_app$ (inf$ ?v0) ?v1) (fun_app$b (fun_app$e (fun_app$f (unfold_llist$ (case_prod$ uu$)) (fun_app$g (comp$ uua$) uub$)) (fun_app$h (map_prod$ uuc$) uuc$)) (pair$ ?v0 ?v1)))) :named a7))
(assert (! (forall ((?v0 A_llist_a_llist_fun$) (?v1 A_llist_a_llist_fun$)) (= (fun_app$e (comp$a uub$) (fun_app$h (map_prod$ ?v0) ?v1)) (fun_app$i (comp$b ?v1) uub$))) :named a8))
(assert (! (forall ((?v0 A_llist_a_llist_fun$) (?v1 A_llist_a_llist_fun$) (?v2 A_llist_a_llist_prod$)) (= (snd$ (fun_app$j (fun_app$h (map_prod$ ?v0) ?v1) ?v2)) (fun_app$ ?v1 (snd$ ?v2)))) :named a9))
(assert (! (forall ((?v0 A_llist_a_llist_fun$) (?v1 A_llist_a_llist_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$j (fun_app$h (map_prod$ ?v0) ?v1) (pair$ ?v2 ?v3)) (pair$ (fun_app$ ?v0 ?v2) (fun_app$ ?v1 ?v3))) :pattern ((fun_app$j (fun_app$h (map_prod$ ?v0) ?v1) (pair$ ?v2 ?v3))))) :named a10))
(assert (! (forall ((?v0 A_llist_a_llist_prod$) (?v1 A_llist_a_llist_bool_fun_fun$)) (=> (forall ((?v2 A_llist$) (?v3 A_llist$)) (=> (= ?v0 (pair$ ?v2 ?v3)) (fun_app$c (fun_app$d ?v1 ?v2) ?v3))) (fun_app$k (case_prod$ ?v1) ?v0))) :named a11))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$)) (=> (fun_app$c (fun_app$d ?v0 ?v1) ?v2) (fun_app$k (case_prod$ ?v0) (pair$ ?v1 ?v2)))) :named a12))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$)) (=> (fun_app$c (fun_app$d ?v0 ?v1) ?v2) (fun_app$k (case_prod$ ?v0) (pair$ ?v1 ?v2)))) :named a13))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (fun_app$ (inf$ ?v0) ?v1) (fun_app$b (fun_app$e (fun_app$f (unfold_llist$ (case_prod$ uu$)) (fun_app$g (comp$ uua$) uub$)) (fun_app$h (map_prod$ uuc$) uuc$)) (pair$ ?v0 ?v1)))) :named a14))
(assert (! (forall ((?v0 A_llist_a_llist_prod$)) (= (fun_app$j (fun_app$h (map_prod$ uud$) uud$) ?v0) ?v0)) :named a15))
(assert (! (forall ((?v0 Bool) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$k (case_prod$ (uue$ ?v0 ?v1)) ?v2) (and ?v0 (fun_app$k (case_prod$ ?v1) ?v2)))) :named a16))
(assert (! (forall ((?v0 A_llist_a_llist_prod_bool_fun$) (?v1 A_llist_a_llist_prod_a_fun$) (?v2 A_llist_a_llist_prod_a_llist_a_llist_prod_fun$) (?v3 A_llist_a_llist_prod$)) (= (ltl$ (fun_app$b (fun_app$e (fun_app$f (unfold_llist$ ?v0) ?v1) ?v2) ?v3)) (ite (fun_app$k ?v0 ?v3) lNil$ (fun_app$b (fun_app$e (fun_app$f (unfold_llist$ ?v0) ?v1) ?v2) (fun_app$j ?v2 ?v3))))) :named a17))
(assert (! (forall ((?v0 A_llist_a_llist_prod_a_llist_fun$) (?v1 A_llist_a_llist_prod_a_llist_a_llist_prod_fun$) (?v2 A_llist_a_llist_prod$)) (! (= (fun_app$b (fun_app$e (comp$a ?v0) ?v1) ?v2) (fun_app$b ?v0 (fun_app$j ?v1 ?v2))) :pattern ((fun_app$b (fun_app$e (comp$a ?v0) ?v1) ?v2)))) :named a18))
(assert (! (forall ((?v0 A_llist_a_llist_fun$) (?v1 A_llist_a_llist_prod_a_llist_fun$) (?v2 A_llist_a_llist_prod$)) (! (= (fun_app$b (fun_app$i (comp$b ?v0) ?v1) ?v2) (fun_app$ ?v0 (fun_app$b ?v1 ?v2))) :pattern ((fun_app$b (fun_app$i (comp$b ?v0) ?v1) ?v2)))) :named a19))
(assert (! (forall ((?v0 A_llist_a_fun$) (?v1 A_llist_a_llist_prod_a_llist_fun$) (?v2 A_llist_a_llist_prod$)) (! (= (fun_app$l (fun_app$g (comp$ ?v0) ?v1) ?v2) (fun_app$a ?v0 (fun_app$b ?v1 ?v2))) :pattern ((fun_app$l (fun_app$g (comp$ ?v0) ?v1) ?v2)))) :named a20))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_llist$)) (= (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a21))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_llist$)) (= (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a22))
(assert (! (forall ((?v0 A_llist_a_llist_prod$)) (exists ((?v1 A_llist$) (?v2 A_llist$)) (= ?v0 (pair$ ?v1 ?v2)))) :named a23))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_llist$)) (=> (and (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (=> (and (= ?v0 ?v2) (= ?v1 ?v3)) false)) false)) :named a24))
(assert (! (forall ((?v0 A_llist_a_llist_prod$)) (=> (forall ((?v1 A_llist$) (?v2 A_llist$)) (=> (= ?v0 (pair$ ?v1 ?v2)) false)) false)) :named a25))
(assert (! (forall ((?v0 A_llist_a_llist_prod_bool_fun$) (?v1 A_llist_a_llist_prod$)) (=> (forall ((?v2 A_llist$) (?v3 A_llist$)) (fun_app$k ?v0 (pair$ ?v2 ?v3))) (fun_app$k ?v0 ?v1))) :named a26))
(check-sat)
;(get-unsat-core)
