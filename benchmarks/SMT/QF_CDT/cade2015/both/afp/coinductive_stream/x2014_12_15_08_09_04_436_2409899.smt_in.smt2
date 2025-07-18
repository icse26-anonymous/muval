; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 385
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_stream_bool_fun$ 0)
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-codatatypes () ((A_stream$ (sCons$ (shd$ A$) (stl$ A_stream$)))))
(declare-datatypes () ((A_list$ (nil$) (cons$ (hd$ A$) (tl$ A_list$)))))
(declare-fun p$ () A_stream_bool_fun$)
(declare-fun ev$ (A_stream_bool_fun$) A_stream_bool_fun$)
(declare-fun alw$ (A_stream_bool_fun$) A_stream_bool_fun$)
(declare-fun omega$ () A_stream$)
(declare-fun sdrop$ (Nat$ A_stream$) A_stream$)
(declare-fun shift$ (A_list$ A_stream$) A_stream$)
(declare-fun scount$ (A_stream_bool_fun$ A_stream$) Enat$)
(declare-fun fun_app$ (A_stream_bool_fun$ A_stream$) Bool)
(declare-fun infinity$ () Enat$)
(assert (! (not (= (= (scount$ p$ omega$) infinity$) (fun_app$ (alw$ (ev$ p$)) omega$))) :named a0))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$)) (! (=> (fun_app$ (alw$ (ev$ ?v0)) ?v1) (= (scount$ ?v0 ?v1) infinity$)) :pattern ((scount$ ?v0 ?v1)))) :named a1))
(assert (! (forall ((?v0 A_stream_bool_fun$)) (= (ev$ (ev$ ?v0)) (ev$ ?v0))) :named a2))
(assert (! (forall ((?v0 A_stream_bool_fun$)) (= (alw$ (alw$ ?v0)) (alw$ ?v0))) :named a3))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$)) (=> (fun_app$ (ev$ (alw$ ?v0)) ?v1) (fun_app$ (alw$ (ev$ ?v0)) ?v1))) :named a4))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$) (?v2 A_stream_bool_fun$) (?v3 A_stream_bool_fun$)) (=> (and (fun_app$ (alw$ ?v0) ?v1) (forall ((?v4 A_stream$)) (=> (fun_app$ ?v0 ?v4) (= (fun_app$ ?v2 ?v4) (fun_app$ ?v3 ?v4))))) (= (fun_app$ (ev$ ?v2) ?v1) (fun_app$ (ev$ ?v3) ?v1)))) :named a5))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$) (?v2 A_stream_bool_fun$)) (=> (and (fun_app$ (ev$ ?v0) ?v1) (forall ((?v3 A_stream$)) (=> (fun_app$ ?v0 ?v3) (fun_app$ ?v2 ?v3)))) (fun_app$ (ev$ ?v2) ?v1))) :named a6))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$)) (=> (fun_app$ ?v0 ?v1) (fun_app$ (ev$ ?v0) ?v1))) :named a7))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$)) (=> (forall ((?v2 A_stream$)) (fun_app$ ?v0 ?v2)) (fun_app$ (alw$ ?v0) ?v1))) :named a8))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$) (?v2 A_stream_bool_fun$) (?v3 A_stream_bool_fun$)) (=> (and (fun_app$ (alw$ ?v0) ?v1) (forall ((?v4 A_stream$)) (=> (fun_app$ ?v0 ?v4) (= (fun_app$ ?v2 ?v4) (fun_app$ ?v3 ?v4))))) (= (fun_app$ (alw$ ?v2) ?v1) (fun_app$ (alw$ ?v3) ?v1)))) :named a9))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$) (?v2 A_stream_bool_fun$)) (=> (and (fun_app$ (alw$ ?v0) ?v1) (forall ((?v3 A_stream$)) (=> (fun_app$ ?v0 ?v3) (fun_app$ ?v2 ?v3)))) (fun_app$ (alw$ ?v2) ?v1))) :named a10))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$)) (=> (fun_app$ (alw$ ?v0) ?v1) (fun_app$ (alw$ (alw$ ?v0)) ?v1))) :named a11))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$)) (=> (fun_app$ (alw$ ?v0) ?v1) (fun_app$ ?v0 ?v1))) :named a12))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 Nat$) (?v2 A_stream$)) (=> (fun_app$ (alw$ (ev$ ?v0)) (sdrop$ ?v1 ?v2)) (fun_app$ (alw$ (ev$ ?v0)) ?v2))) :named a13))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$) (?v2 A_list$)) (=> (fun_app$ (alw$ ?v0) ?v1) (fun_app$ (ev$ (alw$ ?v0)) (shift$ ?v2 ?v1)))) :named a14))
(assert (! (forall ((?v0 A_stream_bool_fun$) (?v1 A_stream$)) (= (fun_app$ (ev$ (alw$ ?v0)) (stl$ ?v1)) (fun_app$ (ev$ (alw$ ?v0)) ?v1))) :named a15))
(check-sat)
;(get-unsat-core)
