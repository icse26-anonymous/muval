; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 582
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort A_llist_set$ 0)
(declare-sort B_llist_set$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort B_llist_bool_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-sort B_llist_b_llist_fun$ 0)
(declare-sort A_llist_b_llist_prod_set$ 0)
(declare-sort A_llist_b_llist_bool_fun_fun$ 0)
(declare-sort A_llist_b_llist_prod_bool_fun$ 0)
(declare-sort A_llist_b_llist_prod_a_llist_fun$ 0)
(declare-sort A_llist_b_llist_prod_a_llist_b_llist_prod_fun$ 0)
(declare-sort B_llist_b_llist_fun_a_llist_b_llist_bool_fun_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))
  (B_llist$ (lNil$a) (lCons$a (lhd$a B$) (ltl$a B_llist$)))))
(declare-datatypes () ((A_llist_b_llist_prod$ (pair$ (fst$ A_llist$) (snd$ B_llist$)))))
(declare-fun uu$ () A_llist_a_llist_fun$)
(declare-fun xs$ () A_llist$)
(declare-fun ya$ () A_llist_b_llist_prod_set$)
(declare-fun ys$ () B_llist$)
(declare-fun inf$ (A_llist_set$ A_llist_set$) A_llist_set$)
(declare-fun uua$ () A_llist_b_llist_prod_a_llist_fun$)
(declare-fun uub$ () A_llist_bool_fun$)
(declare-fun uuc$ () B_llist_b_llist_fun$)
(declare-fun uud$ () A_llist_b_llist_bool_fun_fun$)
(declare-fun uue$ () A_llist_a_llist_fun$)
(declare-fun uuf$ () B_llist_b_llist_fun$)
(declare-fun uug$ (Bool A_llist_b_llist_bool_fun_fun$) A_llist_b_llist_bool_fun_fun$)
(declare-fun uuh$ () A_llist_b_llist_prod_a_llist_b_llist_prod_fun$)
(declare-fun uui$ (A_llist_b_llist_bool_fun_fun$ A_llist_a_llist_fun$) B_llist_b_llist_fun_a_llist_b_llist_bool_fun_fun_fun$)
(declare-fun inf$a (A_llist_b_llist_prod_set$ A_llist_b_llist_prod_set$) A_llist_b_llist_prod_set$)
(declare-fun inf$b (B_llist_set$ B_llist_set$) B_llist_set$)
(declare-fun lSup$ (A_llist_set$) A_llist$)
(declare-fun image$ (A_llist_a_llist_fun$ A_llist_set$) A_llist_set$)
(declare-fun lnull$ (A_llist$) Bool)
(declare-fun image$a (A_llist_b_llist_prod_a_llist_fun$ A_llist_b_llist_prod_set$) A_llist_set$)
(declare-fun image$b (A_llist_b_llist_prod_a_llist_b_llist_prod_fun$ A_llist_b_llist_prod_set$) A_llist_b_llist_prod_set$)
(declare-fun lnull$a (B_llist$) Bool)
(declare-fun member$ (A_llist$ A_llist_set$) Bool)
(declare-fun collect$ (A_llist_bool_fun$) A_llist_set$)
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun member$a (B_llist$ B_llist_set$) Bool)
(declare-fun member$b (A_llist_b_llist_prod$ A_llist_b_llist_prod_set$) Bool)
(declare-fun collect$a (A_llist_b_llist_prod_bool_fun$) A_llist_b_llist_prod_set$)
(declare-fun fun_app$a (B_llist_b_llist_fun$ B_llist$) B_llist$)
(declare-fun fun_app$b (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun fun_app$c (A_llist_b_llist_prod_a_llist_fun$ A_llist_b_llist_prod$) A_llist$)
(declare-fun fun_app$d (B_llist_bool_fun$ B_llist$) Bool)
(declare-fun fun_app$e (A_llist_b_llist_bool_fun_fun$ A_llist$) B_llist_bool_fun$)
(declare-fun fun_app$f (B_llist_b_llist_fun_a_llist_b_llist_bool_fun_fun_fun$ B_llist_b_llist_fun$) A_llist_b_llist_bool_fun_fun$)
(declare-fun fun_app$g (A_llist_b_llist_prod_a_llist_b_llist_prod_fun$ A_llist_b_llist_prod$) A_llist_b_llist_prod$)
(declare-fun fun_app$h (A_llist_b_llist_prod_bool_fun$ A_llist_b_llist_prod$) Bool)
(declare-fun map_prod$ (A_llist_a_llist_fun$ B_llist_b_llist_fun$) A_llist_b_llist_prod_a_llist_b_llist_prod_fun$)
(declare-fun case_prod$ (A_llist_b_llist_bool_fun_fun$) A_llist_b_llist_prod_bool_fun$)
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ uub$ ?v0) (not (lnull$ ?v0))) :pattern ((fun_app$ uub$ ?v0)))) :named a0))
(assert (! (forall ((?v0 B_llist$)) (! (= (fun_app$a uuc$ ?v0) (ltl$a ?v0)) :pattern ((fun_app$a uuc$ ?v0)))) :named a1))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$b uu$ ?v0) (ltl$ ?v0)) :pattern ((fun_app$b uu$ ?v0)))) :named a2))
(assert (! (forall ((?v0 A_llist_b_llist_prod$)) (! (= (fun_app$c uua$ ?v0) (fst$ ?v0)) :pattern ((fun_app$c uua$ ?v0)))) :named a3))
(assert (! (forall ((?v0 A_llist$) (?v1 B_llist$)) (! (= (fun_app$d (fun_app$e uud$ ?v0) ?v1) (and (not (lnull$ ?v0)) (not (lnull$a ?v1)))) :pattern ((fun_app$d (fun_app$e uud$ ?v0) ?v1)))) :named a4))
(assert (! (forall ((?v0 Bool) (?v1 A_llist_b_llist_bool_fun_fun$) (?v2 A_llist$) (?v3 B_llist$)) (! (= (fun_app$d (fun_app$e (uug$ ?v0 ?v1) ?v2) ?v3) (and ?v0 (fun_app$d (fun_app$e ?v1 ?v2) ?v3))) :pattern ((fun_app$d (fun_app$e (uug$ ?v0 ?v1) ?v2) ?v3)))) :named a5))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist_a_llist_fun$) (?v2 B_llist_b_llist_fun$) (?v3 A_llist$) (?v4 B_llist$)) (! (= (fun_app$d (fun_app$e (fun_app$f (uui$ ?v0 ?v1) ?v2) ?v3) ?v4) (fun_app$d (fun_app$e ?v0 (fun_app$b ?v1 ?v3)) (fun_app$a ?v2 ?v4))) :pattern ((fun_app$d (fun_app$e (fun_app$f (uui$ ?v0 ?v1) ?v2) ?v3) ?v4)))) :named a6))
(assert (! (forall ((?v0 B_llist$)) (! (= (fun_app$a uuf$ ?v0) ?v0) :pattern ((fun_app$a uuf$ ?v0)))) :named a7))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$b uue$ ?v0) ?v0) :pattern ((fun_app$b uue$ ?v0)))) :named a8))
(assert (! (forall ((?v0 A_llist_b_llist_prod$)) (! (= (fun_app$g uuh$ ?v0) ?v0) :pattern ((fun_app$g uuh$ ?v0)))) :named a9))
(assert (! (not (= (image$ uu$ (inf$ (image$a uua$ ya$) (collect$ uub$))) (image$a uua$ (image$b (map_prod$ uu$ uuc$) (inf$a ya$ (collect$a (case_prod$ uud$))))))) :named a10))
(assert (! (not (lnull$ xs$)) :named a11))
(assert (! (not (lnull$a ys$)) :named a12))
(assert (! (not (lnull$ (lSup$ (image$a uua$ ya$)))) :named a13))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (=> (or (lnull$ ?v0) (lnull$ ?v1)) false) (=> (and (not (lnull$ ?v0)) (not (lnull$ ?v1))) false)) false)) :named a14))
(assert (! (forall ((?v0 A_llist$) (?v1 B_llist$)) (=> (and (=> (or (lnull$ ?v0) (lnull$a ?v1)) false) (=> (and (not (lnull$ ?v0)) (not (lnull$a ?v1))) false)) false)) :named a15))
(assert (! (forall ((?v0 B_llist$) (?v1 A_llist$)) (=> (and (=> (or (lnull$a ?v0) (lnull$ ?v1)) false) (=> (and (not (lnull$a ?v0)) (not (lnull$ ?v1))) false)) false)) :named a16))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (=> (and (=> (or (lnull$a ?v0) (lnull$a ?v1)) false) (=> (and (not (lnull$a ?v0)) (not (lnull$a ?v1))) false)) false)) :named a17))
(assert (! (forall ((?v0 A_llist_set$)) (=> (and (=> (forall ((?v1 A_llist$)) (=> (member$ ?v1 ?v0) (lnull$ ?v1))) false) (=> (not (forall ((?v1 A_llist$)) (=> (member$ ?v1 ?v0) (lnull$ ?v1)))) false)) false)) :named a18))
(assert (! (forall ((?v0 B_llist_set$)) (=> (and (=> (forall ((?v1 B_llist$)) (=> (member$a ?v1 ?v0) (lnull$a ?v1))) false) (=> (not (forall ((?v1 B_llist$)) (=> (member$a ?v1 ?v0) (lnull$a ?v1)))) false)) false)) :named a19))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (=> (and (lnull$ ?v0) (lnull$ ?v1)) false) (=> (or (not (lnull$ ?v0)) (not (lnull$ ?v1))) false)) false)) :named a20))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (=> (and (=> (and (lnull$a ?v0) (lnull$a ?v1)) false) (=> (or (not (lnull$a ?v0)) (not (lnull$a ?v1))) false)) false)) :named a21))
(assert (! (forall ((?v0 A_llist$)) (=> (and (=> (lnull$ ?v0) false) (=> (not (lnull$ ?v0)) false)) false)) :named a22))
(assert (! (forall ((?v0 B_llist$)) (=> (and (=> (lnull$a ?v0) false) (=> (not (lnull$a ?v0)) false)) false)) :named a23))
(assert (! (forall ((?v0 A_llist$)) (=> (lnull$ ?v0) (lnull$ (ltl$ ?v0)))) :named a24))
(assert (! (forall ((?v0 B_llist$)) (=> (lnull$a ?v0) (lnull$a (ltl$a ?v0)))) :named a25))
(assert (! (forall ((?v0 A_llist_a_llist_fun$) (?v1 B_llist_b_llist_fun$) (?v2 A_llist_b_llist_prod$)) (= (fst$ (fun_app$g (map_prod$ ?v0 ?v1) ?v2)) (fun_app$b ?v0 (fst$ ?v2)))) :named a26))
(assert (! (=> (forall ((?v0 A_llist$) (?v1 B_llist$)) (=> (and (member$b (pair$ ?v0 ?v1) ya$) (and (not (lnull$ ?v0)) (not (lnull$a ?v1)))) false)) false) :named a27))
(assert (! (forall ((?v0 A_llist_b_llist_prod$)) (= (fun_app$g (map_prod$ uue$ uuf$) ?v0) ?v0)) :named a28))
(assert (! (forall ((?v0 Bool) (?v1 A_llist_b_llist_bool_fun_fun$) (?v2 A_llist_b_llist_prod$)) (= (fun_app$h (case_prod$ (uug$ ?v0 ?v1)) ?v2) (and ?v0 (fun_app$h (case_prod$ ?v1) ?v2)))) :named a29))
(assert (! (forall ((?v0 A_llist_set$)) (= (image$ uue$ ?v0) ?v0)) :named a30))
(assert (! (forall ((?v0 A_llist_b_llist_prod_set$)) (= (image$b uuh$ ?v0) ?v0)) :named a31))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist_set$) (?v2 B_llist_set$)) (= (member$a ?v0 (inf$b ?v1 ?v2)) (and (member$a ?v0 ?v1) (member$a ?v0 ?v2)))) :named a32))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_set$) (?v2 A_llist_set$)) (= (member$ ?v0 (inf$ ?v1 ?v2)) (and (member$ ?v0 ?v1) (member$ ?v0 ?v2)))) :named a33))
(assert (! (forall ((?v0 A_llist_b_llist_prod$) (?v1 A_llist_b_llist_prod_set$) (?v2 A_llist_b_llist_prod_set$)) (= (member$b ?v0 (inf$a ?v1 ?v2)) (and (member$b ?v0 ?v1) (member$b ?v0 ?v2)))) :named a34))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist_set$) (?v2 B_llist_set$)) (=> (and (member$a ?v0 ?v1) (member$a ?v0 ?v2)) (member$a ?v0 (inf$b ?v1 ?v2)))) :named a35))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_set$) (?v2 A_llist_set$)) (=> (and (member$ ?v0 ?v1) (member$ ?v0 ?v2)) (member$ ?v0 (inf$ ?v1 ?v2)))) :named a36))
(assert (! (forall ((?v0 A_llist_b_llist_prod$) (?v1 A_llist_b_llist_prod_set$) (?v2 A_llist_b_llist_prod_set$)) (=> (and (member$b ?v0 ?v1) (member$b ?v0 ?v2)) (member$b ?v0 (inf$a ?v1 ?v2)))) :named a37))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist_a_llist_fun$) (?v2 B_llist_b_llist_fun$) (?v3 A_llist_b_llist_prod$)) (= (fun_app$h (case_prod$ ?v0) (fun_app$g (map_prod$ ?v1 ?v2) ?v3)) (fun_app$h (case_prod$ (fun_app$f (uui$ ?v0 ?v1) ?v2)) ?v3))) :named a38))
(check-sat)
;(get-unsat-core)
