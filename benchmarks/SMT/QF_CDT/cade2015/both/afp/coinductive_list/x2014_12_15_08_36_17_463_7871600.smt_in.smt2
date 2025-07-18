; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 559
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort B_set$ 0)
(declare-sort Nat_a_fun$ 0)
(declare-sort Nat_b_fun$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort A_a_bool_fun_fun$ 0)
(declare-sort A_b_bool_fun_fun$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort B_a_bool_fun_fun$ 0)
(declare-sort B_b_bool_fun_fun$ 0)
(declare-sort B_llist_bool_fun$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun$ 0)
(declare-sort B_llist_b_llist_bool_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))
  (B_llist$ (lNil$a) (lCons$a (lhd$a B$) (ltl$a B_llist$)))))
(declare-datatypes () ((A_list$ (nil$) (cons$ (hd$ A$) (tl$ A_list$)))
  (B_list$ (nil$a) (cons$a (hd$a B$) (tl$a B_list$)))))
(declare-fun f$ () Nat_b_fun$)
(declare-fun p$ () A_b_bool_fun_fun$)
(declare-fun uu$ () B_b_bool_fun_fun$)
(declare-fun xs$ () A_list$)
(declare-fun uua$ () B_llist_b_llist_bool_fun_fun$)
(declare-fun uub$ () A_a_bool_fun_fun$)
(declare-fun uuc$ () A_llist_a_llist_bool_fun_fun$)
(declare-fun lnth$ (A_llist$) Nat_a_fun$)
(declare-fun lset$ (B_llist$) B_set$)
(declare-fun lnth$a (B_llist$) Nat_b_fun$)
(declare-fun lset$a (A_llist$) A_set$)
(declare-fun member$ (B$ B_set$) Bool)
(declare-fun transp$ (B_b_bool_fun_fun$) Bool)
(declare-fun fun_app$ (B_llist_bool_fun$ B_llist$) Bool)
(declare-fun lappend$ (A_llist$ A_llist$) A_llist$)
(declare-fun list_of$ (B_llist$) B_list$)
(declare-fun lprefix$ (A_llist$ A_llist$) Bool)
(declare-fun member$a (A$ A_set$) Bool)
(declare-fun transp$a (A_a_bool_fun_fun$) Bool)
(declare-fun fun_app$a (B_llist_b_llist_bool_fun_fun$ B_llist$) B_llist_bool_fun$)
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun fun_app$c (A_llist_a_llist_bool_fun_fun$ A_llist$) A_llist_bool_fun$)
(declare-fun fun_app$d (B_bool_fun$ B$) Bool)
(declare-fun fun_app$e (B_b_bool_fun_fun$ B$) B_bool_fun$)
(declare-fun fun_app$f (A_bool_fun$ A$) Bool)
(declare-fun fun_app$g (A_a_bool_fun_fun$ A$) A_bool_fun$)
(declare-fun fun_app$h (B_a_bool_fun_fun$ B$) A_bool_fun$)
(declare-fun fun_app$i (Nat_b_fun$ Nat$) B$)
(declare-fun fun_app$j (Nat_a_fun$ Nat$) A$)
(declare-fun fun_app$k (A_b_bool_fun_fun$ A$) B_bool_fun$)
(declare-fun lappend$a (B_llist$ B_llist$) B_llist$)
(declare-fun list_of$a (A_llist$) A_list$)
(declare-fun llist_of$ (A_list$) A_llist$)
(declare-fun lprefix$a (B_llist$ B_llist$) Bool)
(declare-fun inf_llist$ (Nat_b_fun$) B_llist$)
(declare-fun list_all2$ (B_a_bool_fun_fun$ B_list$ A_list$) Bool)
(declare-fun llist_of$a (B_list$) B_llist$)
(declare-fun inf_llist$a (Nat_a_fun$) A_llist$)
(declare-fun list_all2$a (B_b_bool_fun_fun$ B_list$ B_list$) Bool)
(declare-fun list_all2$b (A_a_bool_fun_fun$ A_list$ A_list$) Bool)
(declare-fun list_all2$c (A_b_bool_fun_fun$ A_list$ B_list$) Bool)
(declare-fun llist_all2$ (A_b_bool_fun_fun$ A_llist$) B_llist_bool_fun$)
(declare-fun llist_all2$a (B_a_bool_fun_fun$ B_llist$) A_llist_bool_fun$)
(declare-fun llist_all2$b (A_a_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun llist_all2$c (B_b_bool_fun_fun$) B_llist_b_llist_bool_fun_fun$)
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a uua$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$ (fun_app$a uua$ ?v0) ?v1)))) :named a0))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$c uuc$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$b (fun_app$c uuc$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 B$) (?v1 B$)) (! (= (fun_app$d (fun_app$e uu$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$d (fun_app$e uu$ ?v0) ?v1)))) :named a2))
(assert (! (forall ((?v0 A$) (?v1 A$)) (! (= (fun_app$f (fun_app$g uub$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$f (fun_app$g uub$ ?v0) ?v1)))) :named a3))
(assert (! (not (not (fun_app$ (llist_all2$ p$ (llist_of$ xs$)) (inf_llist$ f$)))) :named a4))
(assert (! (forall ((?v0 B_list$) (?v1 B_list$)) (= (= (llist_of$a ?v0) (llist_of$a ?v1)) (= ?v0 ?v1))) :named a5))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (= (= (llist_of$ ?v0) (llist_of$ ?v1)) (= ?v0 ?v1))) :named a6))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 Nat_a_fun$)) (= (= (inf_llist$a ?v0) (inf_llist$a ?v1)) (= ?v0 ?v1))) :named a7))
(assert (! (forall ((?v0 Nat_b_fun$) (?v1 Nat_b_fun$)) (= (= (inf_llist$ ?v0) (inf_llist$ ?v1)) (= ?v0 ?v1))) :named a8))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 Nat_b_fun$) (?v2 Nat_a_fun$)) (= (fun_app$b (llist_all2$a ?v0 (inf_llist$ ?v1)) (inf_llist$a ?v2)) (forall ((?v3 Nat$)) (fun_app$f (fun_app$h ?v0 (fun_app$i ?v1 ?v3)) (fun_app$j ?v2 ?v3))))) :named a9))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 Nat_a_fun$) (?v2 Nat_a_fun$)) (= (fun_app$b (fun_app$c (llist_all2$b ?v0) (inf_llist$a ?v1)) (inf_llist$a ?v2)) (forall ((?v3 Nat$)) (fun_app$f (fun_app$g ?v0 (fun_app$j ?v1 ?v3)) (fun_app$j ?v2 ?v3))))) :named a10))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 Nat_b_fun$) (?v2 Nat_b_fun$)) (= (fun_app$ (fun_app$a (llist_all2$c ?v0) (inf_llist$ ?v1)) (inf_llist$ ?v2)) (forall ((?v3 Nat$)) (fun_app$d (fun_app$e ?v0 (fun_app$i ?v1 ?v3)) (fun_app$i ?v2 ?v3))))) :named a11))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 Nat_a_fun$) (?v2 Nat_b_fun$)) (= (fun_app$ (llist_all2$ ?v0 (inf_llist$a ?v1)) (inf_llist$ ?v2)) (forall ((?v3 Nat$)) (fun_app$d (fun_app$k ?v0 (fun_app$j ?v1 ?v3)) (fun_app$i ?v2 ?v3))))) :named a12))
(assert (! (= (llist_all2$c uu$) uua$) :named a13))
(assert (! (= (llist_all2$b uub$) uuc$) :named a14))
(assert (! (forall ((?v0 A_llist$)) (=> (and (forall ((?v1 A_list$)) (=> (= ?v0 (llist_of$ ?v1)) false)) (forall ((?v1 Nat_a_fun$)) (=> (= ?v0 (inf_llist$a ?v1)) false))) false)) :named a15))
(assert (! (forall ((?v0 B_llist$)) (=> (and (forall ((?v1 B_list$)) (=> (= ?v0 (llist_of$a ?v1)) false)) (forall ((?v1 Nat_b_fun$)) (=> (= ?v0 (inf_llist$ ?v1)) false))) false)) :named a16))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A_llist$) (?v3 B_a_bool_fun_fun$)) (=> (and (fun_app$b (llist_all2$a ?v0 ?v1) ?v2) (forall ((?v4 B$) (?v5 A$)) (=> (fun_app$f (fun_app$h ?v0 ?v4) ?v5) (fun_app$f (fun_app$h ?v3 ?v4) ?v5)))) (fun_app$b (llist_all2$a ?v3 ?v1) ?v2))) :named a17))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$) (?v3 B_b_bool_fun_fun$)) (=> (and (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v1) ?v2) (forall ((?v4 B$) (?v5 B$)) (=> (fun_app$d (fun_app$e ?v0 ?v4) ?v5) (fun_app$d (fun_app$e ?v3 ?v4) ?v5)))) (fun_app$ (fun_app$a (llist_all2$c ?v3) ?v1) ?v2))) :named a18))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_a_bool_fun_fun$)) (=> (and (fun_app$b (fun_app$c (llist_all2$b ?v0) ?v1) ?v2) (forall ((?v4 A$) (?v5 A$)) (=> (fun_app$f (fun_app$g ?v0 ?v4) ?v5) (fun_app$f (fun_app$g ?v3 ?v4) ?v5)))) (fun_app$b (fun_app$c (llist_all2$b ?v3) ?v1) ?v2))) :named a19))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 A_b_bool_fun_fun$)) (=> (and (fun_app$ (llist_all2$ ?v0 ?v1) ?v2) (forall ((?v4 A$) (?v5 B$)) (=> (fun_app$d (fun_app$k ?v0 ?v4) ?v5) (fun_app$d (fun_app$k ?v3 ?v4) ?v5)))) (fun_app$ (llist_all2$ ?v3 ?v1) ?v2))) :named a20))
(assert (! (forall ((?v0 A_list$) (?v1 Nat_a_fun$)) (not (= (llist_of$ ?v0) (inf_llist$a ?v1)))) :named a21))
(assert (! (forall ((?v0 B_list$) (?v1 Nat_b_fun$)) (not (= (llist_of$a ?v0) (inf_llist$ ?v1)))) :named a22))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_list$) (?v2 A_list$)) (= (fun_app$b (llist_all2$a ?v0 (llist_of$a ?v1)) (llist_of$ ?v2)) (list_all2$ ?v0 ?v1 ?v2))) :named a23))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_list$) (?v2 B_list$)) (= (fun_app$ (fun_app$a (llist_all2$c ?v0) (llist_of$a ?v1)) (llist_of$a ?v2)) (list_all2$a ?v0 ?v1 ?v2))) :named a24))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_list$) (?v2 A_list$)) (= (fun_app$b (fun_app$c (llist_all2$b ?v0) (llist_of$ ?v1)) (llist_of$ ?v2)) (list_all2$b ?v0 ?v1 ?v2))) :named a25))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_list$) (?v2 B_list$)) (= (fun_app$ (llist_all2$ ?v0 (llist_of$ ?v1)) (llist_of$a ?v2)) (list_all2$c ?v0 ?v1 ?v2))) :named a26))
(assert (! (forall ((?v0 B_list$)) (= (list_of$ (llist_of$a ?v0)) ?v0)) :named a27))
(assert (! (forall ((?v0 A_list$)) (= (list_of$a (llist_of$ ?v0)) ?v0)) :named a28))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 A_llist$)) (= (lprefix$ (inf_llist$a ?v0) ?v1) (= ?v1 (inf_llist$a ?v0)))) :named a29))
(assert (! (forall ((?v0 Nat_b_fun$) (?v1 B_llist$)) (= (lprefix$a (inf_llist$ ?v0) ?v1) (= ?v1 (inf_llist$ ?v0)))) :named a30))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$) (?v3 B_llist$)) (=> (and (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v1) ?v2) (and (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v2) ?v3) (transp$ ?v0))) (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v1) ?v3))) :named a31))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_llist$)) (=> (and (fun_app$b (fun_app$c (llist_all2$b ?v0) ?v1) ?v2) (and (fun_app$b (fun_app$c (llist_all2$b ?v0) ?v2) ?v3) (transp$a ?v0))) (fun_app$b (fun_app$c (llist_all2$b ?v0) ?v1) ?v3))) :named a32))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 Nat$)) (= (fun_app$j (lnth$ (inf_llist$a ?v0)) ?v1) (fun_app$j ?v0 ?v1))) :named a33))
(assert (! (forall ((?v0 Nat_b_fun$) (?v1 Nat$)) (= (fun_app$i (lnth$a (inf_llist$ ?v0)) ?v1) (fun_app$i ?v0 ?v1))) :named a34))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$b (llist_all2$a ?v0 ?v1) lNil$) (= ?v1 lNil$a)) :pattern ((llist_all2$a ?v0 ?v1)))) :named a35))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v1) lNil$a) (= ?v1 lNil$a)) :pattern ((fun_app$a (llist_all2$c ?v0) ?v1)))) :named a36))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$c (llist_all2$b ?v0) ?v1) lNil$) (= ?v1 lNil$)) :pattern ((fun_app$c (llist_all2$b ?v0) ?v1)))) :named a37))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$ (llist_all2$ ?v0 ?v1) lNil$a) (= ?v1 lNil$)) :pattern ((llist_all2$ ?v0 ?v1)))) :named a38))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (llist_all2$a ?v0 lNil$a) ?v1) (= ?v1 lNil$)) :pattern ((fun_app$b (llist_all2$a ?v0 lNil$a) ?v1)))) :named a39))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a (llist_all2$c ?v0) lNil$a) ?v1) (= ?v1 lNil$a)) :pattern ((fun_app$ (fun_app$a (llist_all2$c ?v0) lNil$a) ?v1)))) :named a40))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$c (llist_all2$b ?v0) lNil$) ?v1) (= ?v1 lNil$)) :pattern ((fun_app$b (fun_app$c (llist_all2$b ?v0) lNil$) ?v1)))) :named a41))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (llist_all2$ ?v0 lNil$) ?v1) (= ?v1 lNil$a)) :pattern ((fun_app$ (llist_all2$ ?v0 lNil$) ?v1)))) :named a42))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 A_llist$)) (= (lappend$ (inf_llist$a ?v0) ?v1) (inf_llist$a ?v0))) :named a43))
(assert (! (forall ((?v0 Nat_b_fun$) (?v1 B_llist$)) (= (lappend$a (inf_llist$ ?v0) ?v1) (inf_llist$ ?v0))) :named a44))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B$) (?v2 B_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$b (llist_all2$a ?v0 (lCons$a ?v1 ?v2)) (lCons$ ?v3 ?v4)) (and (fun_app$f (fun_app$h ?v0 ?v1) ?v3) (fun_app$b (llist_all2$a ?v0 ?v2) ?v4))) :pattern ((fun_app$b (llist_all2$a ?v0 (lCons$a ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a45))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B$) (?v2 B_llist$) (?v3 B$) (?v4 B_llist$)) (! (= (fun_app$ (fun_app$a (llist_all2$c ?v0) (lCons$a ?v1 ?v2)) (lCons$a ?v3 ?v4)) (and (fun_app$d (fun_app$e ?v0 ?v1) ?v3) (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v2) ?v4))) :pattern ((fun_app$ (fun_app$a (llist_all2$c ?v0) (lCons$a ?v1 ?v2)) (lCons$a ?v3 ?v4))))) :named a46))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$b (fun_app$c (llist_all2$b ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v3 ?v4)) (and (fun_app$f (fun_app$g ?v0 ?v1) ?v3) (fun_app$b (fun_app$c (llist_all2$b ?v0) ?v2) ?v4))) :pattern ((fun_app$b (fun_app$c (llist_all2$b ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a47))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 B$) (?v4 B_llist$)) (! (= (fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v2)) (lCons$a ?v3 ?v4)) (and (fun_app$d (fun_app$k ?v0 ?v1) ?v3) (fun_app$ (llist_all2$ ?v0 ?v2) ?v4))) :pattern ((fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v2)) (lCons$a ?v3 ?v4))))) :named a48))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$)) (= (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v1) ?v1) (forall ((?v2 B$)) (=> (member$ ?v2 (lset$ ?v1)) (fun_app$d (fun_app$e ?v0 ?v2) ?v2))))) :named a49))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$)) (= (fun_app$b (fun_app$c (llist_all2$b ?v0) ?v1) ?v1) (forall ((?v2 A$)) (=> (member$a ?v2 (lset$a ?v1)) (fun_app$f (fun_app$g ?v0 ?v2) ?v2))))) :named a50))
(check-sat)
;(get-unsat-core)
