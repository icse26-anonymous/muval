; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 307
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort A_list_set$ 0)
(declare-sort A_list_bool_fun$ 0)
(declare-sort Nat_a_bool_fun_fun$ 0)
(declare-sort A_list_list_bool_fun$ 0)
(declare-sort Nat_a_list_bool_fun_fun$ 0)
(declare-datatypes () ((A_list$ (nil$) (cons$ (hd$ A$) (tl$ A_list$)))))
(declare-codatatypes () ((A_list_stream$ (sCons$ (shd$ A_list$) (stl$ A_list_stream$)))
  (A_stream$ (sCons$a (shd$a A$) (stl$a A_stream$)))))
(declare-datatypes () ((A_list_list$ (nil$a) (cons$a (hd$a A_list$) (tl$a A_list_list$)))))
(declare-fun m$ () Nat$)
(declare-fun s$ () A_list_stream$)
(declare-fun x$ () A$)
(declare-fun y$ () Nat$)
(declare-fun sa$ () A_list_stream$)
(declare-fun nth$ (A_list$ Nat$) A$)
(declare-fun flat$ (A_list_stream$) A_stream$)
(declare-fun less$ (Nat$ Nat$) Bool)
(declare-fun nth$a (A_list_list$ Nat$) A_list$)
(declare-fun size$ (A_list$) Nat$)
(declare-fun snth$ (A_list_stream$ Nat$) A_list$)
(declare-fun sset$ (A_list_stream$) A_list_set$)
(declare-fun shift$ (A_list_list$ A_list_stream$) A_list_stream$)
(declare-fun size$a (A_list_list$) Nat$)
(declare-fun snth$a (A_stream$ Nat$) A$)
(declare-fun sset$a (A_stream$) A_set$)
(declare-fun member$ (A_list$ A_list_set$) Bool)
(declare-fun shift$a (A_list$ A_stream$) A_stream$)
(declare-fun fun_app$ (A_list_bool_fun$ A_list$) Bool)
(declare-fun member$a (A$ A_set$) Bool)
(declare-fun fun_app$a (Nat_a_list_bool_fun_fun$ Nat$) A_list_bool_fun$)
(declare-fun fun_app$b (A_bool_fun$ A$) Bool)
(declare-fun fun_app$c (Nat_a_bool_fun_fun$ Nat$) A_bool_fun$)
(declare-fun fun_app$d (A_list_list_bool_fun$ A_list_list$) Bool)
(assert (! (not (exists ((?v0 Nat$) (?v1 Nat$)) (and (= x$ (nth$ (snth$ sa$ ?v0) ?v1)) (less$ ?v1 (size$ (snth$ sa$ ?v0)))))) :named a0))
(assert (! (forall ((?v0 A_list$)) (=> (member$ ?v0 (sset$ s$)) (not (= ?v0 nil$)))) :named a1))
(assert (! (forall ((?v0 A_list$)) (=> (member$ ?v0 (sset$ sa$)) (not (= ?v0 nil$)))) :named a2))
(assert (! (= x$ (snth$a (flat$ sa$) y$)) :named a3))
(assert (! (forall ((?v0 Nat$) (?v1 A_list_stream$)) (=> (and (less$ ?v0 y$) (and (forall ((?v2 A_list$)) (=> (member$ ?v2 (sset$ ?v1)) (not (= ?v2 nil$)))) (and (= x$ (snth$a (flat$ ?v1) ?v0)) (and (forall ((?v2 A_list$)) (=> (member$ ?v2 (sset$ ?v1)) (not (= ?v2 nil$)))) (= x$ (snth$a (flat$ ?v1) ?v0)))))) (exists ((?v2 Nat$) (?v3 Nat$)) (and (= x$ (nth$ (snth$ ?v1 ?v2) ?v3)) (less$ ?v3 (size$ (snth$ ?v1 ?v2))))))) :named a4))
(assert (! (= x$ (snth$a (flat$ s$) m$)) :named a5))
(assert (! (forall ((?v0 A_list_list$) (?v1 A_list_list$)) (= (= ?v0 ?v1) (and (= (size$a ?v0) (size$a ?v1)) (forall ((?v2 Nat$)) (=> (less$ ?v2 (size$a ?v0)) (= (nth$a ?v0 ?v2) (nth$a ?v1 ?v2))))))) :named a6))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (= (= ?v0 ?v1) (and (= (size$ ?v0) (size$ ?v1)) (forall ((?v2 Nat$)) (=> (less$ ?v2 (size$ ?v0)) (= (nth$ ?v0 ?v2) (nth$ ?v1 ?v2))))))) :named a7))
(assert (! (forall ((?v0 Nat$) (?v1 Nat_a_list_bool_fun_fun$)) (= (forall ((?v2 Nat$)) (=> (less$ ?v2 ?v0) (exists ((?v3 A_list$)) (fun_app$ (fun_app$a ?v1 ?v2) ?v3)))) (exists ((?v2 A_list_list$)) (and (= (size$a ?v2) ?v0) (forall ((?v3 Nat$)) (=> (less$ ?v3 ?v0) (fun_app$ (fun_app$a ?v1 ?v3) (nth$a ?v2 ?v3)))))))) :named a8))
(assert (! (forall ((?v0 Nat$) (?v1 Nat_a_bool_fun_fun$)) (= (forall ((?v2 Nat$)) (=> (less$ ?v2 ?v0) (exists ((?v3 A$)) (fun_app$b (fun_app$c ?v1 ?v2) ?v3)))) (exists ((?v2 A_list$)) (and (= (size$ ?v2) ?v0) (forall ((?v3 Nat$)) (=> (less$ ?v3 ?v0) (fun_app$b (fun_app$c ?v1 ?v3) (nth$ ?v2 ?v3)))))))) :named a9))
(assert (! (forall ((?v0 A_list_list$) (?v1 A_list_list$)) (=> (and (= (size$a ?v0) (size$a ?v1)) (forall ((?v2 Nat$)) (=> (less$ ?v2 (size$a ?v0)) (= (nth$a ?v0 ?v2) (nth$a ?v1 ?v2))))) (= ?v0 ?v1))) :named a10))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (=> (and (= (size$ ?v0) (size$ ?v1)) (forall ((?v2 Nat$)) (=> (less$ ?v2 (size$ ?v0)) (= (nth$ ?v0 ?v2) (nth$ ?v1 ?v2))))) (= ?v0 ?v1))) :named a11))
(assert (! (=> (forall ((?v0 Nat$)) (=> (= x$ (snth$a (flat$ s$) ?v0)) false)) false) :named a12))
(assert (! (forall ((?v0 A_list_list_bool_fun$) (?v1 A_list_list$)) (=> (forall ((?v2 A_list_list$)) (=> (forall ((?v3 A_list_list$)) (=> (less$ (size$a ?v3) (size$a ?v2)) (fun_app$d ?v0 ?v3))) (fun_app$d ?v0 ?v2))) (fun_app$d ?v0 ?v1))) :named a13))
(assert (! (forall ((?v0 A_list_bool_fun$) (?v1 A_list$)) (=> (forall ((?v2 A_list$)) (=> (forall ((?v3 A_list$)) (=> (less$ (size$ ?v3) (size$ ?v2)) (fun_app$ ?v0 ?v3))) (fun_app$ ?v0 ?v2))) (fun_app$ ?v0 ?v1))) :named a14))
(assert (! (forall ((?v0 A_list_stream$) (?v1 Nat$)) (member$ (snth$ ?v0 ?v1) (sset$ ?v0))) :named a15))
(assert (! (forall ((?v0 A_stream$) (?v1 Nat$)) (member$a (snth$a ?v0 ?v1) (sset$a ?v0))) :named a16))
(assert (! (forall ((?v0 Nat$) (?v1 A_list_list$) (?v2 A_list_stream$)) (=> (less$ ?v0 (size$a ?v1)) (= (snth$ (shift$ ?v1 ?v2) ?v0) (nth$a ?v1 ?v0)))) :named a17))
(assert (! (forall ((?v0 Nat$) (?v1 A_list$) (?v2 A_stream$)) (=> (less$ ?v0 (size$ ?v1)) (= (snth$a (shift$a ?v1 ?v2) ?v0) (nth$ ?v1 ?v0)))) :named a18))
(assert (! (member$a x$ (sset$a (flat$ s$))) :named a19))
(assert (! (forall ((?v0 A_list_list$) (?v1 A_list_list$)) (=> (not (= (size$a ?v0) (size$a ?v1))) (= (= ?v0 ?v1) false))) :named a20))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (=> (not (= (size$ ?v0) (size$ ?v1))) (= (= ?v0 ?v1) false))) :named a21))
(assert (! (forall ((?v0 Nat$)) (exists ((?v1 A_list_list$)) (= (size$a ?v1) ?v0))) :named a22))
(assert (! (forall ((?v0 Nat$)) (exists ((?v1 A_list$)) (= (size$ ?v1) ?v0))) :named a23))
(assert (! (forall ((?v0 A_list_list$) (?v1 A_list_list$)) (=> (not (= (size$a ?v0) (size$a ?v1))) (not (= ?v0 ?v1)))) :named a24))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (=> (not (= (size$ ?v0) (size$ ?v1))) (not (= ?v0 ?v1)))) :named a25))
(assert (! (forall ((?v0 A_list$) (?v1 A_stream$) (?v2 A_stream$)) (= (= (shift$a ?v0 ?v1) (shift$a ?v0 ?v2)) (= ?v1 ?v2))) :named a26))
(assert (! (forall ((?v0 A_list_list$) (?v1 A_list_stream$) (?v2 A_list_stream$)) (= (= (shift$ ?v0 ?v1) (shift$ ?v0 ?v2)) (= ?v1 ?v2))) :named a27))
(check-sat)
;(get-unsat-core)
