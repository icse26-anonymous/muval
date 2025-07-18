; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 201
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort N$ 0)
(declare-sort N_dtree_fun$ 0)
(declare-sort N_N_list_fun$ 0)
(declare-sort N_list_bool_fun$ 0)
(declare-sort N_N_list_list_fun$ 0)
(declare-sort N_list_N_list_fun$ 0)
(declare-sort N_list_list_bool_fun$ 0)
(declare-sort N_N_list_list_list_fun$ 0)
(declare-sort N_list_N_list_list_fun$ 0)
(declare-sort N_list_list_N_list_fun$ 0)
(declare-sort N_list_list_list_bool_fun$ 0)
(declare-sort N_list_N_list_bool_fun_fun$ 0)
(declare-sort N_list_N_list_list_list_fun$ 0)
(declare-sort N_list_list_N_list_list_fun$ 0)
(declare-sort N_list_N_list_list_bool_fun_fun$ 0)
(declare-sort N_list_list_N_list_bool_fun_fun$ 0)
(declare-sort N_list_list_N_list_list_list_fun$ 0)
(declare-sort N_list_N_list_list_list_bool_fun_fun$ 0)
(declare-sort N_list_list_N_list_list_bool_fun_fun$ 0)
(declare-sort N_list_list_list_N_list_bool_fun_fun$ 0)
(declare-sort N_list_list_list_N_list_list_list_fun$ 0)
(declare-sort N_list_list_N_list_list_list_bool_fun_fun$ 0)
(declare-sort N_list_list_list_N_list_list_bool_fun_fun$ 0)
(declare-sort N_list_list_list_N_list_list_list_bool_fun_fun$ 0)
(declare-datatypes () ((N_list$ (nil$) (cons$ (hd$ N$) (tl$ N_list$)))
  (N_list_list$ (nil$a) (cons$a (hd$a N_list$) (tl$a N_list_list$)))
  (N_list_list_list$ (nil$b) (cons$b (hd$b N_list_list$) (tl$b N_list_list_list$)))
  (N_list_list_list_list$ (nil$c) (cons$c (hd$c N_list_list_list$) (tl$c N_list_list_list_list$)))))
(declare-fun f$ () N_dtree_fun$)
(declare-fun n$ () N$)
(declare-fun nl$ () N_list$)
(declare-fun bind$ (N_list$ N_N_list_list_list_fun$) N_list_list_list$)
(declare-fun path$ (N_dtree_fun$) N_list_bool_fun$)
(declare-fun bind$a (N_list_list$ N_list_N_list_list_list_fun$) N_list_list_list$)
(declare-fun bind$b (N_list_list_list$ N_list_list_N_list_fun$) N_list$)
(declare-fun bind$c (N_list_list_list$ N_list_list_N_list_list_fun$) N_list_list$)
(declare-fun bind$d (N_list_list_list$ N_list_list_N_list_list_list_fun$) N_list_list_list$)
(declare-fun bind$e (N_list$ N_N_list_list_fun$) N_list_list$)
(declare-fun bind$f (N_list_list$ N_list_N_list_fun$) N_list$)
(declare-fun bind$g (N_list_list$ N_list_N_list_list_fun$) N_list_list$)
(declare-fun bind$h (N_list$ N_N_list_fun$) N_list$)
(declare-fun insert$ (N_list_list$) N_list_list_list_N_list_list_list_fun$)
(declare-fun fun_app$ (N_list_bool_fun$ N_list$) Bool)
(declare-fun insert$a (N_list$) N_list_list_N_list_list_fun$)
(declare-fun insert$b (N$) N_list_N_list_fun$)
(declare-fun fun_app$a (N_list_list_list_bool_fun$ N_list_list_list$) Bool)
(declare-fun fun_app$b (N_list_list_bool_fun$ N_list_list$) Bool)
(declare-fun fun_app$c (N_list_N_list_list_list_bool_fun_fun$ N_list$) N_list_list_list_bool_fun$)
(declare-fun fun_app$d (N_list_list_N_list_list_list_bool_fun_fun$ N_list_list$) N_list_list_list_bool_fun$)
(declare-fun fun_app$e (N_list_list_list_N_list_bool_fun_fun$ N_list_list_list$) N_list_bool_fun$)
(declare-fun fun_app$f (N_list_list_list_N_list_list_bool_fun_fun$ N_list_list_list$) N_list_list_bool_fun$)
(declare-fun fun_app$g (N_list_list_list_N_list_list_list_bool_fun_fun$ N_list_list_list$) N_list_list_list_bool_fun$)
(declare-fun fun_app$h (N_list_N_list_list_bool_fun_fun$ N_list$) N_list_list_bool_fun$)
(declare-fun fun_app$i (N_list_list_N_list_bool_fun_fun$ N_list_list$) N_list_bool_fun$)
(declare-fun fun_app$j (N_list_list_N_list_list_bool_fun_fun$ N_list_list$) N_list_list_bool_fun$)
(declare-fun fun_app$k (N_list_N_list_bool_fun_fun$ N_list$) N_list_bool_fun$)
(declare-fun fun_app$l (N_list_list_list_N_list_list_list_fun$ N_list_list_list$) N_list_list_list$)
(declare-fun fun_app$m (N_list_list_N_list_list_fun$ N_list_list$) N_list_list$)
(declare-fun fun_app$n (N_list_N_list_fun$ N_list$) N_list$)
(declare-fun sublists$ (N_list_list_list$) N_list_list_list_list$)
(declare-fun sublists$a (N_list_list$) N_list_list_list$)
(declare-fun sublists$b (N_list$) N_list_list$)
(declare-fun product_lists$ (N_list_list_list_list$) N_list_list_list_list$)
(declare-fun product_lists$a (N_list_list_list$) N_list_list_list$)
(declare-fun product_lists$b (N_list_list$) N_list_list$)
(assert (! (not (not (= (cons$ n$ nil$) nil$))) :named a0))
(assert (! (fun_app$ (path$ f$) nl$) :named a1))
(assert (! (forall ((?v0 N_list_list$) (?v1 N_list_list_list$) (?v2 N_list_list$) (?v3 N_list_list_list$)) (= (= (cons$b ?v0 ?v1) (cons$b ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a2))
(assert (! (forall ((?v0 N_list$) (?v1 N_list_list$) (?v2 N_list$) (?v3 N_list_list$)) (= (= (cons$a ?v0 ?v1) (cons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a3))
(assert (! (forall ((?v0 N$) (?v1 N_list$) (?v2 N$) (?v3 N_list$)) (= (= (cons$ ?v0 ?v1) (cons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a4))
(assert (! (forall ((?v0 N_list_list_list$)) (= (not (= ?v0 nil$b)) (exists ((?v1 N_list_list$) (?v2 N_list_list_list$)) (= ?v0 (cons$b ?v1 ?v2))))) :named a5))
(assert (! (forall ((?v0 N_list_list$)) (= (not (= ?v0 nil$a)) (exists ((?v1 N_list$) (?v2 N_list_list$)) (= ?v0 (cons$a ?v1 ?v2))))) :named a6))
(assert (! (forall ((?v0 N_list$)) (= (not (= ?v0 nil$)) (exists ((?v1 N$) (?v2 N_list$)) (= ?v0 (cons$ ?v1 ?v2))))) :named a7))
(assert (! (forall ((?v0 N_list_list_list$)) (=> (and (=> (= ?v0 nil$b) false) (and (forall ((?v1 N_list_list$)) (=> (= ?v0 (cons$b ?v1 nil$b)) false)) (forall ((?v1 N_list_list$) (?v2 N_list_list$) (?v3 N_list_list_list$)) (=> (= ?v0 (cons$b ?v1 (cons$b ?v2 ?v3))) false)))) false)) :named a8))
(assert (! (forall ((?v0 N_list_list$)) (=> (and (=> (= ?v0 nil$a) false) (and (forall ((?v1 N_list$)) (=> (= ?v0 (cons$a ?v1 nil$a)) false)) (forall ((?v1 N_list$) (?v2 N_list$) (?v3 N_list_list$)) (=> (= ?v0 (cons$a ?v1 (cons$a ?v2 ?v3))) false)))) false)) :named a9))
(assert (! (forall ((?v0 N_list$)) (=> (and (=> (= ?v0 nil$) false) (and (forall ((?v1 N$)) (=> (= ?v0 (cons$ ?v1 nil$)) false)) (forall ((?v1 N$) (?v2 N$) (?v3 N_list$)) (=> (= ?v0 (cons$ ?v1 (cons$ ?v2 ?v3))) false)))) false)) :named a10))
(assert (! (forall ((?v0 N_list_list_list_list$)) (=> (and (=> (= ?v0 nil$c) false) (and (forall ((?v1 N_list_list_list_list$)) (=> (= ?v0 (cons$c nil$b ?v1)) false)) (forall ((?v1 N_list_list$) (?v2 N_list_list_list$) (?v3 N_list_list_list_list$)) (=> (= ?v0 (cons$c (cons$b ?v1 ?v2) ?v3)) false)))) false)) :named a11))
(assert (! (forall ((?v0 N_list_list_list$)) (=> (and (=> (= ?v0 nil$b) false) (and (forall ((?v1 N_list_list_list$)) (=> (= ?v0 (cons$b nil$a ?v1)) false)) (forall ((?v1 N_list$) (?v2 N_list_list$) (?v3 N_list_list_list$)) (=> (= ?v0 (cons$b (cons$a ?v1 ?v2) ?v3)) false)))) false)) :named a12))
(assert (! (forall ((?v0 N_list_list$)) (=> (and (=> (= ?v0 nil$a) false) (and (forall ((?v1 N_list_list$)) (=> (= ?v0 (cons$a nil$ ?v1)) false)) (forall ((?v1 N$) (?v2 N_list$) (?v3 N_list_list$)) (=> (= ?v0 (cons$a (cons$ ?v1 ?v2) ?v3)) false)))) false)) :named a13))
(assert (! (forall ((?v0 N_list_list_list$)) (=> (and (=> (= ?v0 nil$b) false) (forall ((?v1 N_list_list$) (?v2 N_list_list_list$)) (=> (= ?v0 (cons$b ?v1 ?v2)) false))) false)) :named a14))
(assert (! (forall ((?v0 N_list_list$)) (=> (and (=> (= ?v0 nil$a) false) (forall ((?v1 N_list$) (?v2 N_list_list$)) (=> (= ?v0 (cons$a ?v1 ?v2)) false))) false)) :named a15))
(assert (! (forall ((?v0 N_list$)) (=> (and (=> (= ?v0 nil$) false) (forall ((?v1 N$) (?v2 N_list$)) (=> (= ?v0 (cons$ ?v1 ?v2)) false))) false)) :named a16))
(assert (! (forall ((?v0 N_list_list_list$) (?v1 N_list_list$) (?v2 N_list_list_list$)) (=> (= ?v0 (cons$b ?v1 ?v2)) (not (= ?v0 nil$b)))) :named a17))
(assert (! (forall ((?v0 N_list_list$) (?v1 N_list$) (?v2 N_list_list$)) (=> (= ?v0 (cons$a ?v1 ?v2)) (not (= ?v0 nil$a)))) :named a18))
(assert (! (forall ((?v0 N_list$) (?v1 N$) (?v2 N_list$)) (=> (= ?v0 (cons$ ?v1 ?v2)) (not (= ?v0 nil$)))) :named a19))
(assert (! (forall ((?v0 N_list_list_list$) (?v1 N_list_list_list_bool_fun$)) (=> (and (not (= ?v0 nil$b)) (and (forall ((?v2 N_list_list$)) (fun_app$a ?v1 (cons$b ?v2 nil$b))) (forall ((?v2 N_list_list$) (?v3 N_list_list_list$)) (=> (and (not (= ?v3 nil$b)) (fun_app$a ?v1 ?v3)) (fun_app$a ?v1 (cons$b ?v2 ?v3)))))) (fun_app$a ?v1 ?v0))) :named a20))
(assert (! (forall ((?v0 N_list_list$) (?v1 N_list_list_bool_fun$)) (=> (and (not (= ?v0 nil$a)) (and (forall ((?v2 N_list$)) (fun_app$b ?v1 (cons$a ?v2 nil$a))) (forall ((?v2 N_list$) (?v3 N_list_list$)) (=> (and (not (= ?v3 nil$a)) (fun_app$b ?v1 ?v3)) (fun_app$b ?v1 (cons$a ?v2 ?v3)))))) (fun_app$b ?v1 ?v0))) :named a21))
(assert (! (forall ((?v0 N_list$) (?v1 N_list_bool_fun$)) (=> (and (not (= ?v0 nil$)) (and (forall ((?v2 N$)) (fun_app$ ?v1 (cons$ ?v2 nil$))) (forall ((?v2 N$) (?v3 N_list$)) (=> (and (not (= ?v3 nil$)) (fun_app$ ?v1 ?v3)) (fun_app$ ?v1 (cons$ ?v2 ?v3)))))) (fun_app$ ?v1 ?v0))) :named a22))
(assert (! (forall ((?v0 N_list_N_list_list_list_bool_fun_fun$) (?v1 N_list$) (?v2 N_list_list_list$)) (=> (and (fun_app$a (fun_app$c ?v0 nil$) nil$b) (and (forall ((?v3 N$) (?v4 N_list$)) (fun_app$a (fun_app$c ?v0 (cons$ ?v3 ?v4)) nil$b)) (and (forall ((?v3 N_list_list$) (?v4 N_list_list_list$)) (fun_app$a (fun_app$c ?v0 nil$) (cons$b ?v3 ?v4))) (forall ((?v3 N$) (?v4 N_list$) (?v5 N_list_list$) (?v6 N_list_list_list$)) (=> (fun_app$a (fun_app$c ?v0 ?v4) ?v6) (fun_app$a (fun_app$c ?v0 (cons$ ?v3 ?v4)) (cons$b ?v5 ?v6))))))) (fun_app$a (fun_app$c ?v0 ?v1) ?v2))) :named a23))
(assert (! (forall ((?v0 N_list_list_N_list_list_list_bool_fun_fun$) (?v1 N_list_list$) (?v2 N_list_list_list$)) (=> (and (fun_app$a (fun_app$d ?v0 nil$a) nil$b) (and (forall ((?v3 N_list$) (?v4 N_list_list$)) (fun_app$a (fun_app$d ?v0 (cons$a ?v3 ?v4)) nil$b)) (and (forall ((?v3 N_list_list$) (?v4 N_list_list_list$)) (fun_app$a (fun_app$d ?v0 nil$a) (cons$b ?v3 ?v4))) (forall ((?v3 N_list$) (?v4 N_list_list$) (?v5 N_list_list$) (?v6 N_list_list_list$)) (=> (fun_app$a (fun_app$d ?v0 ?v4) ?v6) (fun_app$a (fun_app$d ?v0 (cons$a ?v3 ?v4)) (cons$b ?v5 ?v6))))))) (fun_app$a (fun_app$d ?v0 ?v1) ?v2))) :named a24))
(assert (! (forall ((?v0 N_list_list_list_N_list_bool_fun_fun$) (?v1 N_list_list_list$) (?v2 N_list$)) (=> (and (fun_app$ (fun_app$e ?v0 nil$b) nil$) (and (forall ((?v3 N_list_list$) (?v4 N_list_list_list$)) (fun_app$ (fun_app$e ?v0 (cons$b ?v3 ?v4)) nil$)) (and (forall ((?v3 N$) (?v4 N_list$)) (fun_app$ (fun_app$e ?v0 nil$b) (cons$ ?v3 ?v4))) (forall ((?v3 N_list_list$) (?v4 N_list_list_list$) (?v5 N$) (?v6 N_list$)) (=> (fun_app$ (fun_app$e ?v0 ?v4) ?v6) (fun_app$ (fun_app$e ?v0 (cons$b ?v3 ?v4)) (cons$ ?v5 ?v6))))))) (fun_app$ (fun_app$e ?v0 ?v1) ?v2))) :named a25))
(assert (! (forall ((?v0 N_list_list_list_N_list_list_bool_fun_fun$) (?v1 N_list_list_list$) (?v2 N_list_list$)) (=> (and (fun_app$b (fun_app$f ?v0 nil$b) nil$a) (and (forall ((?v3 N_list_list$) (?v4 N_list_list_list$)) (fun_app$b (fun_app$f ?v0 (cons$b ?v3 ?v4)) nil$a)) (and (forall ((?v3 N_list$) (?v4 N_list_list$)) (fun_app$b (fun_app$f ?v0 nil$b) (cons$a ?v3 ?v4))) (forall ((?v3 N_list_list$) (?v4 N_list_list_list$) (?v5 N_list$) (?v6 N_list_list$)) (=> (fun_app$b (fun_app$f ?v0 ?v4) ?v6) (fun_app$b (fun_app$f ?v0 (cons$b ?v3 ?v4)) (cons$a ?v5 ?v6))))))) (fun_app$b (fun_app$f ?v0 ?v1) ?v2))) :named a26))
(assert (! (forall ((?v0 N_list_list_list_N_list_list_list_bool_fun_fun$) (?v1 N_list_list_list$) (?v2 N_list_list_list$)) (=> (and (fun_app$a (fun_app$g ?v0 nil$b) nil$b) (and (forall ((?v3 N_list_list$) (?v4 N_list_list_list$)) (fun_app$a (fun_app$g ?v0 (cons$b ?v3 ?v4)) nil$b)) (and (forall ((?v3 N_list_list$) (?v4 N_list_list_list$)) (fun_app$a (fun_app$g ?v0 nil$b) (cons$b ?v3 ?v4))) (forall ((?v3 N_list_list$) (?v4 N_list_list_list$) (?v5 N_list_list$) (?v6 N_list_list_list$)) (=> (fun_app$a (fun_app$g ?v0 ?v4) ?v6) (fun_app$a (fun_app$g ?v0 (cons$b ?v3 ?v4)) (cons$b ?v5 ?v6))))))) (fun_app$a (fun_app$g ?v0 ?v1) ?v2))) :named a27))
(assert (! (forall ((?v0 N_list_N_list_list_bool_fun_fun$) (?v1 N_list$) (?v2 N_list_list$)) (=> (and (fun_app$b (fun_app$h ?v0 nil$) nil$a) (and (forall ((?v3 N$) (?v4 N_list$)) (fun_app$b (fun_app$h ?v0 (cons$ ?v3 ?v4)) nil$a)) (and (forall ((?v3 N_list$) (?v4 N_list_list$)) (fun_app$b (fun_app$h ?v0 nil$) (cons$a ?v3 ?v4))) (forall ((?v3 N$) (?v4 N_list$) (?v5 N_list$) (?v6 N_list_list$)) (=> (fun_app$b (fun_app$h ?v0 ?v4) ?v6) (fun_app$b (fun_app$h ?v0 (cons$ ?v3 ?v4)) (cons$a ?v5 ?v6))))))) (fun_app$b (fun_app$h ?v0 ?v1) ?v2))) :named a28))
(assert (! (forall ((?v0 N_list_list_N_list_bool_fun_fun$) (?v1 N_list_list$) (?v2 N_list$)) (=> (and (fun_app$ (fun_app$i ?v0 nil$a) nil$) (and (forall ((?v3 N_list$) (?v4 N_list_list$)) (fun_app$ (fun_app$i ?v0 (cons$a ?v3 ?v4)) nil$)) (and (forall ((?v3 N$) (?v4 N_list$)) (fun_app$ (fun_app$i ?v0 nil$a) (cons$ ?v3 ?v4))) (forall ((?v3 N_list$) (?v4 N_list_list$) (?v5 N$) (?v6 N_list$)) (=> (fun_app$ (fun_app$i ?v0 ?v4) ?v6) (fun_app$ (fun_app$i ?v0 (cons$a ?v3 ?v4)) (cons$ ?v5 ?v6))))))) (fun_app$ (fun_app$i ?v0 ?v1) ?v2))) :named a29))
(assert (! (forall ((?v0 N_list_list_N_list_list_bool_fun_fun$) (?v1 N_list_list$) (?v2 N_list_list$)) (=> (and (fun_app$b (fun_app$j ?v0 nil$a) nil$a) (and (forall ((?v3 N_list$) (?v4 N_list_list$)) (fun_app$b (fun_app$j ?v0 (cons$a ?v3 ?v4)) nil$a)) (and (forall ((?v3 N_list$) (?v4 N_list_list$)) (fun_app$b (fun_app$j ?v0 nil$a) (cons$a ?v3 ?v4))) (forall ((?v3 N_list$) (?v4 N_list_list$) (?v5 N_list$) (?v6 N_list_list$)) (=> (fun_app$b (fun_app$j ?v0 ?v4) ?v6) (fun_app$b (fun_app$j ?v0 (cons$a ?v3 ?v4)) (cons$a ?v5 ?v6))))))) (fun_app$b (fun_app$j ?v0 ?v1) ?v2))) :named a30))
(assert (! (forall ((?v0 N_list_N_list_bool_fun_fun$) (?v1 N_list$) (?v2 N_list$)) (=> (and (fun_app$ (fun_app$k ?v0 nil$) nil$) (and (forall ((?v3 N$) (?v4 N_list$)) (fun_app$ (fun_app$k ?v0 (cons$ ?v3 ?v4)) nil$)) (and (forall ((?v3 N$) (?v4 N_list$)) (fun_app$ (fun_app$k ?v0 nil$) (cons$ ?v3 ?v4))) (forall ((?v3 N$) (?v4 N_list$) (?v5 N$) (?v6 N_list$)) (=> (fun_app$ (fun_app$k ?v0 ?v4) ?v6) (fun_app$ (fun_app$k ?v0 (cons$ ?v3 ?v4)) (cons$ ?v5 ?v6))))))) (fun_app$ (fun_app$k ?v0 ?v1) ?v2))) :named a31))
(assert (! (forall ((?v0 N_list_list$) (?v1 N_list_list_list$)) (not (= nil$b (cons$b ?v0 ?v1)))) :named a32))
(assert (! (forall ((?v0 N_list$) (?v1 N_list_list$)) (not (= nil$a (cons$a ?v0 ?v1)))) :named a33))
(assert (! (forall ((?v0 N$) (?v1 N_list$)) (not (= nil$ (cons$ ?v0 ?v1)))) :named a34))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N$)) (fun_app$ (path$ ?v0) (cons$ ?v1 nil$))) :named a35))
(assert (! (forall ((?v0 N_list_list_list$)) (=> (and (=> (= ?v0 nil$b) false) (=> (not (= ?v0 nil$b)) false)) false)) :named a36))
(assert (! (forall ((?v0 N_list_list$)) (=> (and (=> (= ?v0 nil$a) false) (=> (not (= ?v0 nil$a)) false)) false)) :named a37))
(assert (! (forall ((?v0 N_list$)) (=> (and (=> (= ?v0 nil$) false) (=> (not (= ?v0 nil$)) false)) false)) :named a38))
(assert (! (forall ((?v0 N_list_list$) (?v1 N_list_list_list$)) (not (= (cons$b ?v0 ?v1) ?v1))) :named a39))
(assert (! (forall ((?v0 N_list$) (?v1 N_list_list$)) (not (= (cons$a ?v0 ?v1) ?v1))) :named a40))
(assert (! (forall ((?v0 N$) (?v1 N_list$)) (not (= (cons$ ?v0 ?v1) ?v1))) :named a41))
(assert (! (= (sublists$ nil$b) (cons$c nil$b nil$c)) :named a42))
(assert (! (= (sublists$a nil$a) (cons$b nil$a nil$b)) :named a43))
(assert (! (= (sublists$b nil$) (cons$a nil$ nil$a)) :named a44))
(assert (! (= (product_lists$ nil$c) (cons$c nil$b nil$c)) :named a45))
(assert (! (= (product_lists$a nil$b) (cons$b nil$a nil$b)) :named a46))
(assert (! (= (product_lists$b nil$a) (cons$a nil$ nil$a)) :named a47))
(assert (! (forall ((?v0 N_N_list_list_list_fun$)) (! (= (bind$ nil$ ?v0) nil$b) :pattern ((bind$ nil$ ?v0)))) :named a48))
(assert (! (forall ((?v0 N_list_N_list_list_list_fun$)) (! (= (bind$a nil$a ?v0) nil$b) :pattern ((bind$a nil$a ?v0)))) :named a49))
(assert (! (forall ((?v0 N_list_list_N_list_fun$)) (! (= (bind$b nil$b ?v0) nil$) :pattern ((bind$b nil$b ?v0)))) :named a50))
(assert (! (forall ((?v0 N_list_list_N_list_list_fun$)) (! (= (bind$c nil$b ?v0) nil$a) :pattern ((bind$c nil$b ?v0)))) :named a51))
(assert (! (forall ((?v0 N_list_list_N_list_list_list_fun$)) (! (= (bind$d nil$b ?v0) nil$b) :pattern ((bind$d nil$b ?v0)))) :named a52))
(assert (! (forall ((?v0 N_N_list_list_fun$)) (! (= (bind$e nil$ ?v0) nil$a) :pattern ((bind$e nil$ ?v0)))) :named a53))
(assert (! (forall ((?v0 N_list_N_list_fun$)) (! (= (bind$f nil$a ?v0) nil$) :pattern ((bind$f nil$a ?v0)))) :named a54))
(assert (! (forall ((?v0 N_list_N_list_list_fun$)) (! (= (bind$g nil$a ?v0) nil$a) :pattern ((bind$g nil$a ?v0)))) :named a55))
(assert (! (forall ((?v0 N_N_list_fun$)) (! (= (bind$h nil$ ?v0) nil$) :pattern ((bind$h nil$ ?v0)))) :named a56))
(assert (! (forall ((?v0 N_list_list$)) (! (= (fun_app$l (insert$ ?v0) nil$b) (cons$b ?v0 nil$b)) :pattern ((insert$ ?v0)))) :named a57))
(assert (! (forall ((?v0 N_list$)) (! (= (fun_app$m (insert$a ?v0) nil$a) (cons$a ?v0 nil$a)) :pattern ((insert$a ?v0)))) :named a58))
(assert (! (forall ((?v0 N$)) (! (= (fun_app$n (insert$b ?v0) nil$) (cons$ ?v0 nil$)) :pattern ((insert$b ?v0)))) :named a59))
(check-sat)
;(get-unsat-core)
