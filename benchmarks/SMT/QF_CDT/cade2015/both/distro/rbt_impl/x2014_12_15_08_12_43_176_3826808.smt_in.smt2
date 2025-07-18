; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 146
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort C$ 0)
(declare-sort C_b_fun$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort C_bool_fun$ 0)
(declare-sort A_c_b_fun_fun$ 0)
(declare-sort Bool_bool_fun$ 0)
(declare-sort B_a_b_prod_fun$ 0)
(declare-sort B_a_c_prod_fun$ 0)
(declare-sort C_a_b_prod_fun$ 0)
(declare-sort C_a_c_prod_fun$ 0)
(declare-sort A_b_bool_fun_fun$ 0)
(declare-sort A_c_bool_fun_fun$ 0)
(declare-sort A_b_prod_bool_fun$ 0)
(declare-sort A_c_prod_bool_fun$ 0)
(declare-sort A_b_a_b_prod_fun_fun$ 0)
(declare-sort A_b_a_c_prod_fun_fun$ 0)
(declare-sort A_c_a_b_prod_fun_fun$ 0)
(declare-sort A_c_a_c_prod_fun_fun$ 0)
(declare-sort A_b_prod_a_b_prod_fun$ 0)
(declare-sort A_b_prod_a_c_prod_fun$ 0)
(declare-sort A_c_prod_a_b_prod_fun$ 0)
(declare-sort A_c_prod_a_c_prod_fun$ 0)
(declare-datatypes () ((A_b_prod$ (pair$ (fst$ A$) (snd$ B$)))
  (A_b_prod_list$ (nil$) (cons$ (hd$ A_b_prod$) (tl$ A_b_prod_list$)))
  (Color$ (r$) (b$))
  (A_b_rbt$ (empty$) (branch$ (select$ Color$) (selecta$ A_b_rbt$) (selectb$ A$) (selectc$ B$) (selectd$ A_b_rbt$)))
  (A_c_rbt$ (empty$a) (branch$a (selecte$ Color$) (selectf$ A_c_rbt$) (selectg$ A$) (selecth$ C$) (selecti$ A_c_rbt$)))
  (A_c_prod$ (pair$a (fst$a A$) (snd$a C$)))
  (A_c_prod_list$ (nil$a) (cons$a (hd$a A_c_prod$) (tl$a A_c_prod_list$)))))
(declare-fun f$ () A_c_b_fun_fun$)
(declare-fun t$ () A_c_rbt$)
(declare-fun uu$ () A_c_a_b_prod_fun_fun$)
(declare-fun map$ (A_c_b_fun_fun$ A_c_rbt$) A_b_rbt$)
(declare-fun uua$ (A_b_a_b_prod_fun_fun$ A_c_a_b_prod_fun_fun$) A_c_a_b_prod_fun_fun$)
(declare-fun uub$ (A_c_a_b_prod_fun_fun$ A_c_a_c_prod_fun_fun$) A_c_a_b_prod_fun_fun$)
(declare-fun uuc$ (A_b_bool_fun_fun$ A_c_a_b_prod_fun_fun$) A_c_bool_fun_fun$)
(declare-fun uud$ (A_b_bool_fun_fun$ A_b_a_b_prod_fun_fun$) A_b_bool_fun_fun$)
(declare-fun uue$ (A_b_a_c_prod_fun_fun$ A_c_a_b_prod_fun_fun$) A_c_a_c_prod_fun_fun$)
(declare-fun uuf$ (A_c_a_b_prod_fun_fun$ A_b_a_c_prod_fun_fun$) A_b_a_b_prod_fun_fun$)
(declare-fun uug$ (A_c_a_c_prod_fun_fun$ A_c_a_c_prod_fun_fun$) A_c_a_c_prod_fun_fun$)
(declare-fun uuh$ (A_b_a_b_prod_fun_fun$ A_b_a_b_prod_fun_fun$) A_b_a_b_prod_fun_fun$)
(declare-fun uui$ (A_c_bool_fun_fun$ A_c_a_c_prod_fun_fun$) A_c_bool_fun_fun$)
(declare-fun uuj$ (A_c_bool_fun_fun$ A_b_a_c_prod_fun_fun$) A_b_bool_fun_fun$)
(declare-fun uuk$ () A_c_a_c_prod_fun_fun$)
(declare-fun uul$ () A_b_a_b_prod_fun_fun$)
(declare-fun uum$ (A_c_prod_bool_fun$) A_c_bool_fun_fun$)
(declare-fun uun$ (A_b_prod_a_c_prod_fun$) A_b_a_c_prod_fun_fun$)
(declare-fun uuo$ (A_c_prod_a_c_prod_fun$) A_c_a_c_prod_fun_fun$)
(declare-fun uup$ (A_b_prod_a_b_prod_fun$) A_b_a_b_prod_fun_fun$)
(declare-fun uuq$ (A_b_prod_bool_fun$) A_b_bool_fun_fun$)
(declare-fun uur$ (A_c_prod_a_b_prod_fun$) A_c_a_b_prod_fun_fun$)
(declare-fun map$a (A_c_prod_a_b_prod_fun$ A_c_prod_list$) A_b_prod_list$)
(declare-fun entries$ (A_b_rbt$) A_b_prod_list$)
(declare-fun fun_app$ (C_a_b_prod_fun$ C$) A_b_prod$)
(declare-fun entries$a (A_c_rbt$) A_c_prod_list$)
(declare-fun fun_app$a (A_c_a_b_prod_fun_fun$ A$) C_a_b_prod_fun$)
(declare-fun fun_app$b (C_b_fun$ C$) B$)
(declare-fun fun_app$c (A_c_b_fun_fun$ A$) C_b_fun$)
(declare-fun fun_app$d (C_a_c_prod_fun$ C$) A_c_prod$)
(declare-fun fun_app$e (A_c_a_c_prod_fun_fun$ A$) C_a_c_prod_fun$)
(declare-fun fun_app$f (B_a_b_prod_fun$ B$) A_b_prod$)
(declare-fun fun_app$g (A_b_a_b_prod_fun_fun$ A$) B_a_b_prod_fun$)
(declare-fun fun_app$h (A_c_prod_a_c_prod_fun$ A_c_prod$) A_c_prod$)
(declare-fun fun_app$i (A_c_prod_a_b_prod_fun$ A_c_prod$) A_b_prod$)
(declare-fun fun_app$j (C_bool_fun$ C$) Bool)
(declare-fun fun_app$k (A_c_bool_fun_fun$ A$) C_bool_fun$)
(declare-fun fun_app$l (A_c_prod_bool_fun$ A_c_prod$) Bool)
(declare-fun fun_app$m (B_a_c_prod_fun$ B$) A_c_prod$)
(declare-fun fun_app$n (A_b_a_c_prod_fun_fun$ A$) B_a_c_prod_fun$)
(declare-fun fun_app$o (A_b_prod_a_c_prod_fun$ A_b_prod$) A_c_prod$)
(declare-fun fun_app$p (A_b_prod_a_b_prod_fun$ A_b_prod$) A_b_prod$)
(declare-fun fun_app$q (B_bool_fun$ B$) Bool)
(declare-fun fun_app$r (A_b_bool_fun_fun$ A$) B_bool_fun$)
(declare-fun fun_app$s (A_b_prod_bool_fun$ A_b_prod$) Bool)
(declare-fun fun_app$t (Bool_bool_fun$ Bool) Bool)
(declare-fun case_prod$ (A_c_a_c_prod_fun_fun$) A_c_prod_a_c_prod_fun$)
(declare-fun case_prod$a (A_c_a_b_prod_fun_fun$) A_c_prod_a_b_prod_fun$)
(declare-fun case_prod$b (A_c_bool_fun_fun$) A_c_prod_bool_fun$)
(declare-fun case_prod$c (A_b_a_c_prod_fun_fun$) A_b_prod_a_c_prod_fun$)
(declare-fun case_prod$d (A_b_a_b_prod_fun_fun$) A_b_prod_a_b_prod_fun$)
(declare-fun case_prod$e (A_b_bool_fun_fun$) A_b_prod_bool_fun$)
(assert (! (forall ((?v0 A$) (?v1 C$)) (! (= (fun_app$ (fun_app$a uu$ ?v0) ?v1) (pair$ ?v0 (fun_app$b (fun_app$c f$ ?v0) ?v1))) :pattern ((fun_app$ (fun_app$a uu$ ?v0) ?v1)))) :named a0))
(assert (! (forall ((?v0 A$) (?v1 C$)) (! (= (fun_app$d (fun_app$e uuk$ ?v0) ?v1) (pair$a ?v0 ?v1)) :pattern ((fun_app$d (fun_app$e uuk$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 A$) (?v1 B$)) (! (= (fun_app$f (fun_app$g uul$ ?v0) ?v1) (pair$ ?v0 ?v1)) :pattern ((fun_app$f (fun_app$g uul$ ?v0) ?v1)))) :named a2))
(assert (! (forall ((?v0 A_c_prod_a_c_prod_fun$) (?v1 A$) (?v2 C$)) (! (= (fun_app$d (fun_app$e (uuo$ ?v0) ?v1) ?v2) (fun_app$h ?v0 (pair$a ?v1 ?v2))) :pattern ((fun_app$d (fun_app$e (uuo$ ?v0) ?v1) ?v2)))) :named a3))
(assert (! (forall ((?v0 A_c_prod_a_b_prod_fun$) (?v1 A$) (?v2 C$)) (! (= (fun_app$ (fun_app$a (uur$ ?v0) ?v1) ?v2) (fun_app$i ?v0 (pair$a ?v1 ?v2))) :pattern ((fun_app$ (fun_app$a (uur$ ?v0) ?v1) ?v2)))) :named a4))
(assert (! (forall ((?v0 A_c_prod_bool_fun$) (?v1 A$) (?v2 C$)) (! (= (fun_app$j (fun_app$k (uum$ ?v0) ?v1) ?v2) (fun_app$l ?v0 (pair$a ?v1 ?v2))) :pattern ((fun_app$j (fun_app$k (uum$ ?v0) ?v1) ?v2)))) :named a5))
(assert (! (forall ((?v0 A_b_prod_a_c_prod_fun$) (?v1 A$) (?v2 B$)) (! (= (fun_app$m (fun_app$n (uun$ ?v0) ?v1) ?v2) (fun_app$o ?v0 (pair$ ?v1 ?v2))) :pattern ((fun_app$m (fun_app$n (uun$ ?v0) ?v1) ?v2)))) :named a6))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_fun$) (?v1 A$) (?v2 B$)) (! (= (fun_app$f (fun_app$g (uup$ ?v0) ?v1) ?v2) (fun_app$p ?v0 (pair$ ?v1 ?v2))) :pattern ((fun_app$f (fun_app$g (uup$ ?v0) ?v1) ?v2)))) :named a7))
(assert (! (forall ((?v0 A_b_prod_bool_fun$) (?v1 A$) (?v2 B$)) (! (= (fun_app$q (fun_app$r (uuq$ ?v0) ?v1) ?v2) (fun_app$s ?v0 (pair$ ?v1 ?v2))) :pattern ((fun_app$q (fun_app$r (uuq$ ?v0) ?v1) ?v2)))) :named a8))
(assert (! (forall ((?v0 A_c_a_c_prod_fun_fun$) (?v1 A_c_a_c_prod_fun_fun$) (?v2 A$) (?v3 C$)) (! (= (fun_app$d (fun_app$e (uug$ ?v0 ?v1) ?v2) ?v3) (fun_app$h (case_prod$ ?v0) (fun_app$d (fun_app$e ?v1 ?v2) ?v3))) :pattern ((fun_app$d (fun_app$e (uug$ ?v0 ?v1) ?v2) ?v3)))) :named a9))
(assert (! (forall ((?v0 A_c_a_b_prod_fun_fun$) (?v1 A_c_a_c_prod_fun_fun$) (?v2 A$) (?v3 C$)) (! (= (fun_app$ (fun_app$a (uub$ ?v0 ?v1) ?v2) ?v3) (fun_app$i (case_prod$a ?v0) (fun_app$d (fun_app$e ?v1 ?v2) ?v3))) :pattern ((fun_app$ (fun_app$a (uub$ ?v0 ?v1) ?v2) ?v3)))) :named a10))
(assert (! (forall ((?v0 A_c_a_b_prod_fun_fun$) (?v1 A_b_a_c_prod_fun_fun$) (?v2 A$) (?v3 B$)) (! (= (fun_app$f (fun_app$g (uuf$ ?v0 ?v1) ?v2) ?v3) (fun_app$i (case_prod$a ?v0) (fun_app$m (fun_app$n ?v1 ?v2) ?v3))) :pattern ((fun_app$f (fun_app$g (uuf$ ?v0 ?v1) ?v2) ?v3)))) :named a11))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 A_c_a_c_prod_fun_fun$) (?v2 A$) (?v3 C$)) (! (= (fun_app$j (fun_app$k (uui$ ?v0 ?v1) ?v2) ?v3) (fun_app$l (case_prod$b ?v0) (fun_app$d (fun_app$e ?v1 ?v2) ?v3))) :pattern ((fun_app$j (fun_app$k (uui$ ?v0 ?v1) ?v2) ?v3)))) :named a12))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 A_b_a_c_prod_fun_fun$) (?v2 A$) (?v3 B$)) (! (= (fun_app$q (fun_app$r (uuj$ ?v0 ?v1) ?v2) ?v3) (fun_app$l (case_prod$b ?v0) (fun_app$m (fun_app$n ?v1 ?v2) ?v3))) :pattern ((fun_app$q (fun_app$r (uuj$ ?v0 ?v1) ?v2) ?v3)))) :named a13))
(assert (! (forall ((?v0 A_b_a_c_prod_fun_fun$) (?v1 A_c_a_b_prod_fun_fun$) (?v2 A$) (?v3 C$)) (! (= (fun_app$d (fun_app$e (uue$ ?v0 ?v1) ?v2) ?v3) (fun_app$o (case_prod$c ?v0) (fun_app$ (fun_app$a ?v1 ?v2) ?v3))) :pattern ((fun_app$d (fun_app$e (uue$ ?v0 ?v1) ?v2) ?v3)))) :named a14))
(assert (! (forall ((?v0 A_b_a_b_prod_fun_fun$) (?v1 A_c_a_b_prod_fun_fun$) (?v2 A$) (?v3 C$)) (! (= (fun_app$ (fun_app$a (uua$ ?v0 ?v1) ?v2) ?v3) (fun_app$p (case_prod$d ?v0) (fun_app$ (fun_app$a ?v1 ?v2) ?v3))) :pattern ((fun_app$ (fun_app$a (uua$ ?v0 ?v1) ?v2) ?v3)))) :named a15))
(assert (! (forall ((?v0 A_b_a_b_prod_fun_fun$) (?v1 A_b_a_b_prod_fun_fun$) (?v2 A$) (?v3 B$)) (! (= (fun_app$f (fun_app$g (uuh$ ?v0 ?v1) ?v2) ?v3) (fun_app$p (case_prod$d ?v0) (fun_app$f (fun_app$g ?v1 ?v2) ?v3))) :pattern ((fun_app$f (fun_app$g (uuh$ ?v0 ?v1) ?v2) ?v3)))) :named a16))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_c_a_b_prod_fun_fun$) (?v2 A$) (?v3 C$)) (! (= (fun_app$j (fun_app$k (uuc$ ?v0 ?v1) ?v2) ?v3) (fun_app$s (case_prod$e ?v0) (fun_app$ (fun_app$a ?v1 ?v2) ?v3))) :pattern ((fun_app$j (fun_app$k (uuc$ ?v0 ?v1) ?v2) ?v3)))) :named a17))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_b_a_b_prod_fun_fun$) (?v2 A$) (?v3 B$)) (! (= (fun_app$q (fun_app$r (uud$ ?v0 ?v1) ?v2) ?v3) (fun_app$s (case_prod$e ?v0) (fun_app$f (fun_app$g ?v1 ?v2) ?v3))) :pattern ((fun_app$q (fun_app$r (uud$ ?v0 ?v1) ?v2) ?v3)))) :named a18))
(assert (! (not (= (entries$ (map$ f$ t$)) (map$a (case_prod$a uu$) (entries$a t$)))) :named a19))
(assert (! (forall ((?v0 A_b_a_b_prod_fun_fun$) (?v1 A_c_a_b_prod_fun_fun$) (?v2 A_c_prod$)) (= (fun_app$p (case_prod$d ?v0) (fun_app$i (case_prod$a ?v1) ?v2)) (fun_app$i (case_prod$a (uua$ ?v0 ?v1)) ?v2))) :named a20))
(assert (! (forall ((?v0 A_c_a_b_prod_fun_fun$) (?v1 A_c_a_c_prod_fun_fun$) (?v2 A_c_prod$)) (= (fun_app$i (case_prod$a ?v0) (fun_app$h (case_prod$ ?v1) ?v2)) (fun_app$i (case_prod$a (uub$ ?v0 ?v1)) ?v2))) :named a21))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_c_a_b_prod_fun_fun$) (?v2 A_c_prod$)) (= (fun_app$s (case_prod$e ?v0) (fun_app$i (case_prod$a ?v1) ?v2)) (fun_app$l (case_prod$b (uuc$ ?v0 ?v1)) ?v2))) :named a22))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_b_a_b_prod_fun_fun$) (?v2 A_b_prod$)) (= (fun_app$s (case_prod$e ?v0) (fun_app$p (case_prod$d ?v1) ?v2)) (fun_app$s (case_prod$e (uud$ ?v0 ?v1)) ?v2))) :named a23))
(assert (! (forall ((?v0 A_b_a_c_prod_fun_fun$) (?v1 A_c_a_b_prod_fun_fun$) (?v2 A_c_prod$)) (= (fun_app$o (case_prod$c ?v0) (fun_app$i (case_prod$a ?v1) ?v2)) (fun_app$h (case_prod$ (uue$ ?v0 ?v1)) ?v2))) :named a24))
(assert (! (forall ((?v0 A_c_a_b_prod_fun_fun$) (?v1 A_b_a_c_prod_fun_fun$) (?v2 A_b_prod$)) (= (fun_app$i (case_prod$a ?v0) (fun_app$o (case_prod$c ?v1) ?v2)) (fun_app$p (case_prod$d (uuf$ ?v0 ?v1)) ?v2))) :named a25))
(assert (! (forall ((?v0 A_c_a_c_prod_fun_fun$) (?v1 A_c_a_c_prod_fun_fun$) (?v2 A_c_prod$)) (= (fun_app$h (case_prod$ ?v0) (fun_app$h (case_prod$ ?v1) ?v2)) (fun_app$h (case_prod$ (uug$ ?v0 ?v1)) ?v2))) :named a26))
(assert (! (forall ((?v0 A_b_a_b_prod_fun_fun$) (?v1 A_b_a_b_prod_fun_fun$) (?v2 A_b_prod$)) (= (fun_app$p (case_prod$d ?v0) (fun_app$p (case_prod$d ?v1) ?v2)) (fun_app$p (case_prod$d (uuh$ ?v0 ?v1)) ?v2))) :named a27))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 A_c_a_c_prod_fun_fun$) (?v2 A_c_prod$)) (= (fun_app$l (case_prod$b ?v0) (fun_app$h (case_prod$ ?v1) ?v2)) (fun_app$l (case_prod$b (uui$ ?v0 ?v1)) ?v2))) :named a28))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 A_b_a_c_prod_fun_fun$) (?v2 A_b_prod$)) (= (fun_app$l (case_prod$b ?v0) (fun_app$o (case_prod$c ?v1) ?v2)) (fun_app$s (case_prod$e (uuj$ ?v0 ?v1)) ?v2))) :named a29))
(assert (! (forall ((?v0 A_c_prod$)) (! (= (fun_app$h (case_prod$ uuk$) ?v0) ?v0) :pattern ((fun_app$h (case_prod$ uuk$) ?v0)))) :named a30))
(assert (! (forall ((?v0 A_b_prod$)) (! (= (fun_app$p (case_prod$d uul$) ?v0) ?v0) :pattern ((fun_app$p (case_prod$d uul$) ?v0)))) :named a31))
(assert (! (forall ((?v0 A$) (?v1 C$) (?v2 A$) (?v3 C$)) (= (= (pair$a ?v0 ?v1) (pair$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a32))
(assert (! (forall ((?v0 A$) (?v1 B$) (?v2 A$) (?v3 B$)) (= (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a33))
(assert (! (forall ((?v0 A$) (?v1 C$) (?v2 A$) (?v3 C$)) (= (= (pair$a ?v0 ?v1) (pair$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a34))
(assert (! (forall ((?v0 A$) (?v1 B$) (?v2 A$) (?v3 B$)) (= (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a35))
(assert (! (forall ((?v0 A_c_prod_bool_fun$)) (= (case_prod$b (uum$ ?v0)) ?v0)) :named a36))
(assert (! (forall ((?v0 A_b_prod_a_c_prod_fun$)) (= (case_prod$c (uun$ ?v0)) ?v0)) :named a37))
(assert (! (forall ((?v0 A_c_prod_a_c_prod_fun$)) (= (case_prod$ (uuo$ ?v0)) ?v0)) :named a38))
(assert (! (forall ((?v0 A_b_prod_a_b_prod_fun$)) (= (case_prod$d (uup$ ?v0)) ?v0)) :named a39))
(assert (! (forall ((?v0 A_b_prod_bool_fun$)) (= (case_prod$e (uuq$ ?v0)) ?v0)) :named a40))
(assert (! (forall ((?v0 A_c_prod_a_b_prod_fun$)) (= (case_prod$a (uur$ ?v0)) ?v0)) :named a41))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 A_c_prod_bool_fun$)) (=> (forall ((?v2 A$) (?v3 C$)) (= (fun_app$j (fun_app$k ?v0 ?v2) ?v3) (fun_app$l ?v1 (pair$a ?v2 ?v3)))) (= (case_prod$b ?v0) ?v1))) :named a42))
(assert (! (forall ((?v0 A_b_a_c_prod_fun_fun$) (?v1 A_b_prod_a_c_prod_fun$)) (=> (forall ((?v2 A$) (?v3 B$)) (= (fun_app$m (fun_app$n ?v0 ?v2) ?v3) (fun_app$o ?v1 (pair$ ?v2 ?v3)))) (= (case_prod$c ?v0) ?v1))) :named a43))
(assert (! (forall ((?v0 A_c_a_c_prod_fun_fun$) (?v1 A_c_prod_a_c_prod_fun$)) (=> (forall ((?v2 A$) (?v3 C$)) (= (fun_app$d (fun_app$e ?v0 ?v2) ?v3) (fun_app$h ?v1 (pair$a ?v2 ?v3)))) (= (case_prod$ ?v0) ?v1))) :named a44))
(assert (! (forall ((?v0 A_b_a_b_prod_fun_fun$) (?v1 A_b_prod_a_b_prod_fun$)) (=> (forall ((?v2 A$) (?v3 B$)) (= (fun_app$f (fun_app$g ?v0 ?v2) ?v3) (fun_app$p ?v1 (pair$ ?v2 ?v3)))) (= (case_prod$d ?v0) ?v1))) :named a45))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_b_prod_bool_fun$)) (=> (forall ((?v2 A$) (?v3 B$)) (= (fun_app$q (fun_app$r ?v0 ?v2) ?v3) (fun_app$s ?v1 (pair$ ?v2 ?v3)))) (= (case_prod$e ?v0) ?v1))) :named a46))
(assert (! (forall ((?v0 A_c_a_b_prod_fun_fun$) (?v1 A_c_prod_a_b_prod_fun$)) (=> (forall ((?v2 A$) (?v3 C$)) (= (fun_app$ (fun_app$a ?v0 ?v2) ?v3) (fun_app$i ?v1 (pair$a ?v2 ?v3)))) (= (case_prod$a ?v0) ?v1))) :named a47))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 A$) (?v2 C$)) (! (= (fun_app$l (case_prod$b ?v0) (pair$a ?v1 ?v2)) (fun_app$j (fun_app$k ?v0 ?v1) ?v2)) :pattern ((fun_app$l (case_prod$b ?v0) (pair$a ?v1 ?v2))))) :named a48))
(assert (! (forall ((?v0 A_b_a_c_prod_fun_fun$) (?v1 A$) (?v2 B$)) (! (= (fun_app$o (case_prod$c ?v0) (pair$ ?v1 ?v2)) (fun_app$m (fun_app$n ?v0 ?v1) ?v2)) :pattern ((fun_app$o (case_prod$c ?v0) (pair$ ?v1 ?v2))))) :named a49))
(assert (! (forall ((?v0 A_c_a_c_prod_fun_fun$) (?v1 A$) (?v2 C$)) (! (= (fun_app$h (case_prod$ ?v0) (pair$a ?v1 ?v2)) (fun_app$d (fun_app$e ?v0 ?v1) ?v2)) :pattern ((fun_app$h (case_prod$ ?v0) (pair$a ?v1 ?v2))))) :named a50))
(assert (! (forall ((?v0 A_b_a_b_prod_fun_fun$) (?v1 A$) (?v2 B$)) (! (= (fun_app$p (case_prod$d ?v0) (pair$ ?v1 ?v2)) (fun_app$f (fun_app$g ?v0 ?v1) ?v2)) :pattern ((fun_app$p (case_prod$d ?v0) (pair$ ?v1 ?v2))))) :named a51))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A$) (?v2 B$)) (! (= (fun_app$s (case_prod$e ?v0) (pair$ ?v1 ?v2)) (fun_app$q (fun_app$r ?v0 ?v1) ?v2)) :pattern ((fun_app$s (case_prod$e ?v0) (pair$ ?v1 ?v2))))) :named a52))
(assert (! (forall ((?v0 A_c_a_b_prod_fun_fun$) (?v1 A$) (?v2 C$)) (! (= (fun_app$i (case_prod$a ?v0) (pair$a ?v1 ?v2)) (fun_app$ (fun_app$a ?v0 ?v1) ?v2)) :pattern ((fun_app$i (case_prod$a ?v0) (pair$a ?v1 ?v2))))) :named a53))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 A$) (?v2 C$)) (! (= (fun_app$l (case_prod$b ?v0) (pair$a ?v1 ?v2)) (fun_app$j (fun_app$k ?v0 ?v1) ?v2)) :pattern ((fun_app$l (case_prod$b ?v0) (pair$a ?v1 ?v2))))) :named a54))
(assert (! (forall ((?v0 A_b_a_c_prod_fun_fun$) (?v1 A$) (?v2 B$)) (! (= (fun_app$o (case_prod$c ?v0) (pair$ ?v1 ?v2)) (fun_app$m (fun_app$n ?v0 ?v1) ?v2)) :pattern ((fun_app$o (case_prod$c ?v0) (pair$ ?v1 ?v2))))) :named a55))
(assert (! (forall ((?v0 A_c_a_c_prod_fun_fun$) (?v1 A$) (?v2 C$)) (! (= (fun_app$h (case_prod$ ?v0) (pair$a ?v1 ?v2)) (fun_app$d (fun_app$e ?v0 ?v1) ?v2)) :pattern ((fun_app$h (case_prod$ ?v0) (pair$a ?v1 ?v2))))) :named a56))
(assert (! (forall ((?v0 A_b_a_b_prod_fun_fun$) (?v1 A$) (?v2 B$)) (! (= (fun_app$p (case_prod$d ?v0) (pair$ ?v1 ?v2)) (fun_app$f (fun_app$g ?v0 ?v1) ?v2)) :pattern ((fun_app$p (case_prod$d ?v0) (pair$ ?v1 ?v2))))) :named a57))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A$) (?v2 B$)) (! (= (fun_app$s (case_prod$e ?v0) (pair$ ?v1 ?v2)) (fun_app$q (fun_app$r ?v0 ?v1) ?v2)) :pattern ((fun_app$s (case_prod$e ?v0) (pair$ ?v1 ?v2))))) :named a58))
(assert (! (forall ((?v0 A_c_a_b_prod_fun_fun$) (?v1 A$) (?v2 C$)) (! (= (fun_app$i (case_prod$a ?v0) (pair$a ?v1 ?v2)) (fun_app$ (fun_app$a ?v0 ?v1) ?v2)) :pattern ((fun_app$i (case_prod$a ?v0) (pair$a ?v1 ?v2))))) :named a59))
(assert (! (forall ((?v0 A_c_prod$) (?v1 A_c_bool_fun_fun$) (?v2 A_c_bool_fun_fun$) (?v3 A_c_prod$)) (=> (and (forall ((?v4 A$) (?v5 C$)) (=> (= (pair$a ?v4 ?v5) ?v0) (= (fun_app$j (fun_app$k ?v1 ?v4) ?v5) (fun_app$j (fun_app$k ?v2 ?v4) ?v5)))) (= ?v3 ?v0)) (= (fun_app$l (case_prod$b ?v1) ?v3) (fun_app$l (case_prod$b ?v2) ?v0)))) :named a60))
(assert (! (forall ((?v0 A_b_prod$) (?v1 A_b_a_c_prod_fun_fun$) (?v2 A_b_a_c_prod_fun_fun$) (?v3 A_b_prod$)) (=> (and (forall ((?v4 A$) (?v5 B$)) (=> (= (pair$ ?v4 ?v5) ?v0) (= (fun_app$m (fun_app$n ?v1 ?v4) ?v5) (fun_app$m (fun_app$n ?v2 ?v4) ?v5)))) (= ?v3 ?v0)) (= (fun_app$o (case_prod$c ?v1) ?v3) (fun_app$o (case_prod$c ?v2) ?v0)))) :named a61))
(assert (! (forall ((?v0 A_c_prod$) (?v1 A_c_a_c_prod_fun_fun$) (?v2 A_c_a_c_prod_fun_fun$) (?v3 A_c_prod$)) (=> (and (forall ((?v4 A$) (?v5 C$)) (=> (= (pair$a ?v4 ?v5) ?v0) (= (fun_app$d (fun_app$e ?v1 ?v4) ?v5) (fun_app$d (fun_app$e ?v2 ?v4) ?v5)))) (= ?v3 ?v0)) (= (fun_app$h (case_prod$ ?v1) ?v3) (fun_app$h (case_prod$ ?v2) ?v0)))) :named a62))
(assert (! (forall ((?v0 A_b_prod$) (?v1 A_b_a_b_prod_fun_fun$) (?v2 A_b_a_b_prod_fun_fun$) (?v3 A_b_prod$)) (=> (and (forall ((?v4 A$) (?v5 B$)) (=> (= (pair$ ?v4 ?v5) ?v0) (= (fun_app$f (fun_app$g ?v1 ?v4) ?v5) (fun_app$f (fun_app$g ?v2 ?v4) ?v5)))) (= ?v3 ?v0)) (= (fun_app$p (case_prod$d ?v1) ?v3) (fun_app$p (case_prod$d ?v2) ?v0)))) :named a63))
(assert (! (forall ((?v0 A_b_prod$) (?v1 A_b_bool_fun_fun$) (?v2 A_b_bool_fun_fun$) (?v3 A_b_prod$)) (=> (and (forall ((?v4 A$) (?v5 B$)) (=> (= (pair$ ?v4 ?v5) ?v0) (= (fun_app$q (fun_app$r ?v1 ?v4) ?v5) (fun_app$q (fun_app$r ?v2 ?v4) ?v5)))) (= ?v3 ?v0)) (= (fun_app$s (case_prod$e ?v1) ?v3) (fun_app$s (case_prod$e ?v2) ?v0)))) :named a64))
(assert (! (forall ((?v0 A_c_prod$) (?v1 A_c_a_b_prod_fun_fun$) (?v2 A_c_a_b_prod_fun_fun$) (?v3 A_c_prod$)) (=> (and (forall ((?v4 A$) (?v5 C$)) (=> (= (pair$a ?v4 ?v5) ?v0) (= (fun_app$ (fun_app$a ?v1 ?v4) ?v5) (fun_app$ (fun_app$a ?v2 ?v4) ?v5)))) (= ?v3 ?v0)) (= (fun_app$i (case_prod$a ?v1) ?v3) (fun_app$i (case_prod$a ?v2) ?v0)))) :named a65))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_c_bool_fun_fun$) (?v2 A_c_prod$)) (=> (and (fun_app$t ?v0 (fun_app$l (case_prod$b ?v1) ?v2)) (forall ((?v3 A$) (?v4 C$)) (=> (and (= ?v2 (pair$a ?v3 ?v4)) (fun_app$t ?v0 (fun_app$j (fun_app$k ?v1 ?v3) ?v4))) false))) false)) :named a66))
(assert (! (forall ((?v0 A_c_prod_bool_fun$) (?v1 A_b_a_c_prod_fun_fun$) (?v2 A_b_prod$)) (=> (and (fun_app$l ?v0 (fun_app$o (case_prod$c ?v1) ?v2)) (forall ((?v3 A$) (?v4 B$)) (=> (and (= ?v2 (pair$ ?v3 ?v4)) (fun_app$l ?v0 (fun_app$m (fun_app$n ?v1 ?v3) ?v4))) false))) false)) :named a67))
(assert (! (forall ((?v0 A_c_prod_bool_fun$) (?v1 A_c_a_c_prod_fun_fun$) (?v2 A_c_prod$)) (=> (and (fun_app$l ?v0 (fun_app$h (case_prod$ ?v1) ?v2)) (forall ((?v3 A$) (?v4 C$)) (=> (and (= ?v2 (pair$a ?v3 ?v4)) (fun_app$l ?v0 (fun_app$d (fun_app$e ?v1 ?v3) ?v4))) false))) false)) :named a68))
(assert (! (forall ((?v0 A_b_prod_bool_fun$) (?v1 A_b_a_b_prod_fun_fun$) (?v2 A_b_prod$)) (=> (and (fun_app$s ?v0 (fun_app$p (case_prod$d ?v1) ?v2)) (forall ((?v3 A$) (?v4 B$)) (=> (and (= ?v2 (pair$ ?v3 ?v4)) (fun_app$s ?v0 (fun_app$f (fun_app$g ?v1 ?v3) ?v4))) false))) false)) :named a69))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_b_bool_fun_fun$) (?v2 A_b_prod$)) (=> (and (fun_app$t ?v0 (fun_app$s (case_prod$e ?v1) ?v2)) (forall ((?v3 A$) (?v4 B$)) (=> (and (= ?v2 (pair$ ?v3 ?v4)) (fun_app$t ?v0 (fun_app$q (fun_app$r ?v1 ?v3) ?v4))) false))) false)) :named a70))
(assert (! (forall ((?v0 A_b_prod_bool_fun$) (?v1 A_c_a_b_prod_fun_fun$) (?v2 A_c_prod$)) (=> (and (fun_app$s ?v0 (fun_app$i (case_prod$a ?v1) ?v2)) (forall ((?v3 A$) (?v4 C$)) (=> (and (= ?v2 (pair$a ?v3 ?v4)) (fun_app$s ?v0 (fun_app$ (fun_app$a ?v1 ?v3) ?v4))) false))) false)) :named a71))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 A$) (?v2 C$)) (=> (fun_app$j (fun_app$k ?v0 ?v1) ?v2) (fun_app$l (case_prod$b ?v0) (pair$a ?v1 ?v2)))) :named a72))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A$) (?v2 B$)) (=> (fun_app$q (fun_app$r ?v0 ?v1) ?v2) (fun_app$s (case_prod$e ?v0) (pair$ ?v1 ?v2)))) :named a73))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 A$) (?v2 C$)) (=> (fun_app$j (fun_app$k ?v0 ?v1) ?v2) (fun_app$l (case_prod$b ?v0) (pair$a ?v1 ?v2)))) :named a74))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A$) (?v2 B$)) (=> (fun_app$q (fun_app$r ?v0 ?v1) ?v2) (fun_app$s (case_prod$e ?v0) (pair$ ?v1 ?v2)))) :named a75))
(assert (! (forall ((?v0 A_c_prod$) (?v1 A_c_bool_fun_fun$)) (=> (forall ((?v2 A$) (?v3 C$)) (=> (= ?v0 (pair$a ?v2 ?v3)) (fun_app$j (fun_app$k ?v1 ?v2) ?v3))) (fun_app$l (case_prod$b ?v1) ?v0))) :named a76))
(assert (! (forall ((?v0 A_b_prod$) (?v1 A_b_bool_fun_fun$)) (=> (forall ((?v2 A$) (?v3 B$)) (=> (= ?v0 (pair$ ?v2 ?v3)) (fun_app$q (fun_app$r ?v1 ?v2) ?v3))) (fun_app$s (case_prod$e ?v1) ?v0))) :named a77))
(check-sat)
;(get-unsat-core)
