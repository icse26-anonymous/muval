; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 297
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort A_list_set$ 0)
(declare-sort A_list_bool_fun$ 0)
(declare-sort A_stream_bool_fun$ 0)
(declare-sort Nat_a_bool_fun_fun$ 0)
(declare-sort A_list_stream_bool_fun$ 0)
(declare-sort A_a_stream_bool_fun_fun$ 0)
(declare-sort A_stream_a_stream_bool_fun_fun$ 0)
(declare-sort A_list_a_list_stream_bool_fun_fun$ 0)
(declare-sort A_list_stream_a_list_stream_bool_fun_fun$ 0)
(declare-codatatypes () ((A_stream$ (sCons$ (shd$ A$) (stl$ A_stream$)))))
(declare-datatypes () ((A_list$ (nil$) (cons$ (hd$ A$) (tl$ A_list$)))))
(declare-codatatypes () ((A_list_stream$ (sCons$a (shd$a A_list$) (stl$a A_list_stream$)))))
(declare-fun n$ () Nat$)
(declare-fun s$ () A_list_stream$)
(declare-fun nth$ (A_list$ Nat$) A$)
(declare-fun flat$ (A_list_stream$) A_stream$)
(declare-fun less$ (Nat$ Nat$) Bool)
(declare-fun size$ (A_list$) Nat$)
(declare-fun snth$ (A_stream$ Nat$) A$)
(declare-fun sset$ (A_list_stream$) A_list_set$)
(declare-fun minus$ (Nat$ Nat$) Nat$)
(declare-fun snth$a (A_list_stream$ Nat$) A_list$)
(declare-fun sset$a (A_stream$) A_set$)
(declare-fun member$ (A_list$ A_list_set$) Bool)
(declare-fun fun_app$ (A_stream_bool_fun$ A_stream$) Bool)
(declare-fun member$a (A$ A_set$) Bool)
(declare-fun fun_app$a (A_a_stream_bool_fun_fun$ A$) A_stream_bool_fun$)
(declare-fun fun_app$b (A_list_stream_bool_fun$ A_list_stream$) Bool)
(declare-fun fun_app$c (A_list_a_list_stream_bool_fun_fun$ A_list$) A_list_stream_bool_fun$)
(declare-fun fun_app$d (A_stream_a_stream_bool_fun_fun$ A_stream$) A_stream_bool_fun$)
(declare-fun fun_app$e (A_list_stream_a_list_stream_bool_fun_fun$ A_list_stream$) A_list_stream_bool_fun$)
(declare-fun fun_app$f (A_bool_fun$ A$) Bool)
(declare-fun fun_app$g (Nat_a_bool_fun_fun$ Nat$) A_bool_fun$)
(declare-fun fun_app$h (A_list_bool_fun$ A_list$) Bool)
(assert (! (not (= (snth$ (flat$ s$) n$) (ite (less$ n$ (size$ (shd$a s$))) (nth$ (shd$a s$) n$) (snth$ (flat$ (stl$a s$)) (minus$ n$ (size$ (shd$a s$))))))) :named a0))
(assert (! (forall ((?v0 A_list$)) (=> (member$ ?v0 (sset$ s$)) (not (= ?v0 nil$)))) :named a1))
(assert (! (forall ((?v0 A_stream$) (?v1 A_stream$)) (=> (and (= (shd$ ?v0) (shd$ ?v1)) (= (stl$ ?v0) (stl$ ?v1))) (= ?v0 ?v1))) :named a2))
(assert (! (forall ((?v0 A_list_stream$) (?v1 A_list_stream$)) (=> (and (= (shd$a ?v0) (shd$a ?v1)) (= (stl$a ?v0) (stl$a ?v1))) (= ?v0 ?v1))) :named a3))
(assert (! (forall ((?v0 A$) (?v1 A_stream$)) (=> (member$a ?v0 (sset$a (stl$ ?v1))) (member$a ?v0 (sset$a ?v1)))) :named a4))
(assert (! (forall ((?v0 A_list$) (?v1 A_list_stream$)) (=> (member$ ?v0 (sset$ (stl$a ?v1))) (member$ ?v0 (sset$ ?v1)))) :named a5))
(assert (! (forall ((?v0 A$) (?v1 A_stream$) (?v2 A_a_stream_bool_fun_fun$)) (=> (and (member$a ?v0 (sset$a ?v1)) (and (forall ((?v3 A_stream$)) (fun_app$ (fun_app$a ?v2 (shd$ ?v3)) ?v3)) (forall ((?v3 A_stream$) (?v4 A$)) (=> (and (member$a ?v4 (sset$a (stl$ ?v3))) (fun_app$ (fun_app$a ?v2 ?v4) (stl$ ?v3))) (fun_app$ (fun_app$a ?v2 ?v4) ?v3))))) (fun_app$ (fun_app$a ?v2 ?v0) ?v1))) :named a6))
(assert (! (forall ((?v0 A_list$) (?v1 A_list_stream$) (?v2 A_list_a_list_stream_bool_fun_fun$)) (=> (and (member$ ?v0 (sset$ ?v1)) (and (forall ((?v3 A_list_stream$)) (fun_app$b (fun_app$c ?v2 (shd$a ?v3)) ?v3)) (forall ((?v3 A_list_stream$) (?v4 A_list$)) (=> (and (member$ ?v4 (sset$ (stl$a ?v3))) (fun_app$b (fun_app$c ?v2 ?v4) (stl$a ?v3))) (fun_app$b (fun_app$c ?v2 ?v4) ?v3))))) (fun_app$b (fun_app$c ?v2 ?v0) ?v1))) :named a7))
(assert (! (forall ((?v0 A_stream_a_stream_bool_fun_fun$) (?v1 A_stream$) (?v2 A_stream$)) (=> (and (fun_app$ (fun_app$d ?v0 ?v1) ?v2) (forall ((?v3 A_stream$) (?v4 A_stream$)) (=> (fun_app$ (fun_app$d ?v0 ?v3) ?v4) (and (= (shd$ ?v3) (shd$ ?v4)) (or (fun_app$ (fun_app$d ?v0 (stl$ ?v3)) (stl$ ?v4)) (= (stl$ ?v3) (stl$ ?v4))))))) (= ?v1 ?v2))) :named a8))
(assert (! (forall ((?v0 A_list_stream_a_list_stream_bool_fun_fun$) (?v1 A_list_stream$) (?v2 A_list_stream$)) (=> (and (fun_app$b (fun_app$e ?v0 ?v1) ?v2) (forall ((?v3 A_list_stream$) (?v4 A_list_stream$)) (=> (fun_app$b (fun_app$e ?v0 ?v3) ?v4) (and (= (shd$a ?v3) (shd$a ?v4)) (or (fun_app$b (fun_app$e ?v0 (stl$a ?v3)) (stl$a ?v4)) (= (stl$a ?v3) (stl$a ?v4))))))) (= ?v1 ?v2))) :named a9))
(assert (! (forall ((?v0 A_stream_a_stream_bool_fun_fun$) (?v1 A_stream$) (?v2 A_stream$)) (=> (and (fun_app$ (fun_app$d ?v0 ?v1) ?v2) (forall ((?v3 A_stream$) (?v4 A_stream$)) (=> (fun_app$ (fun_app$d ?v0 ?v3) ?v4) (and (= (shd$ ?v3) (shd$ ?v4)) (fun_app$ (fun_app$d ?v0 (stl$ ?v3)) (stl$ ?v4)))))) (= ?v1 ?v2))) :named a10))
(assert (! (forall ((?v0 A_list_stream_a_list_stream_bool_fun_fun$) (?v1 A_list_stream$) (?v2 A_list_stream$)) (=> (and (fun_app$b (fun_app$e ?v0 ?v1) ?v2) (forall ((?v3 A_list_stream$) (?v4 A_list_stream$)) (=> (fun_app$b (fun_app$e ?v0 ?v3) ?v4) (and (= (shd$a ?v3) (shd$a ?v4)) (fun_app$b (fun_app$e ?v0 (stl$a ?v3)) (stl$a ?v4)))))) (= ?v1 ?v2))) :named a11))
(assert (! (forall ((?v0 A_stream$) (?v1 Nat$)) (member$a (snth$ ?v0 ?v1) (sset$a ?v0))) :named a12))
(assert (! (forall ((?v0 A_list_stream$) (?v1 Nat$)) (member$ (snth$a ?v0 ?v1) (sset$ ?v0))) :named a13))
(assert (! (forall ((?v0 A_stream$)) (member$a (shd$ ?v0) (sset$a ?v0))) :named a14))
(assert (! (forall ((?v0 A_list_stream$)) (member$ (shd$a ?v0) (sset$ ?v0))) :named a15))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (= (= ?v0 ?v1) (and (= (size$ ?v0) (size$ ?v1)) (forall ((?v2 Nat$)) (=> (less$ ?v2 (size$ ?v0)) (= (nth$ ?v0 ?v2) (nth$ ?v1 ?v2))))))) :named a16))
(assert (! (forall ((?v0 Nat$) (?v1 Nat_a_bool_fun_fun$)) (= (forall ((?v2 Nat$)) (=> (less$ ?v2 ?v0) (exists ((?v3 A$)) (fun_app$f (fun_app$g ?v1 ?v2) ?v3)))) (exists ((?v2 A_list$)) (and (= (size$ ?v2) ?v0) (forall ((?v3 Nat$)) (=> (less$ ?v3 ?v0) (fun_app$f (fun_app$g ?v1 ?v3) (nth$ ?v2 ?v3)))))))) :named a17))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (=> (and (= (size$ ?v0) (size$ ?v1)) (forall ((?v2 Nat$)) (=> (less$ ?v2 (size$ ?v0)) (= (nth$ ?v0 ?v2) (nth$ ?v1 ?v2))))) (= ?v0 ?v1))) :named a18))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (and (less$ ?v0 ?v1) (less$ ?v0 ?v2)) (less$ (minus$ ?v2 ?v1) (minus$ ?v2 ?v0)))) :named a19))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$) (?v2 Nat$)) (=> (less$ ?v0 ?v1) (less$ (minus$ ?v0 ?v2) ?v1))) :named a20))
(assert (! (forall ((?v0 A_list_bool_fun$) (?v1 A_list$)) (=> (forall ((?v2 A_list$)) (=> (forall ((?v3 A_list$)) (=> (less$ (size$ ?v3) (size$ ?v2)) (fun_app$h ?v0 ?v3))) (fun_app$h ?v0 ?v2))) (fun_app$h ?v0 ?v1))) :named a21))
(check-sat)
;(get-unsat-core)
