; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 480
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort C$ 0)
(declare-sort D$ 0)
(declare-sort Nat$ 0)
(declare-sort A_c_fun$ 0)
(declare-sort B_d_fun$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort C_bool_fun$ 0)
(declare-sort D_bool_fun$ 0)
(declare-sort Nat_nat_fun$ 0)
(declare-sort Enat_nat_fun$ 0)
(declare-sort Nat_bool_fun$ 0)
(declare-sort Nat_enat_fun$ 0)
(declare-sort Enat_bool_fun$ 0)
(declare-sort Enat_enat_fun$ 0)
(declare-sort A_a_bool_fun_fun$ 0)
(declare-sort A_c_bool_fun_fun$ 0)
(declare-sort B_b_bool_fun_fun$ 0)
(declare-sort B_d_bool_fun_fun$ 0)
(declare-sort C_a_bool_fun_fun$ 0)
(declare-sort C_c_bool_fun_fun$ 0)
(declare-sort D_b_bool_fun_fun$ 0)
(declare-sort D_d_bool_fun_fun$ 0)
(declare-sort A_b_tllist_bool_fun$ 0)
(declare-sort C_d_tllist_bool_fun$ 0)
(declare-sort A_b_tllist_a_b_tllist_bool_fun_fun$ 0)
(declare-sort C_d_tllist_c_d_tllist_bool_fun_fun$ 0)
(declare-codatatypes () ((C_d_tllist$ (tNil$ (terminal$ D$)) (tCons$ (thd$ C$) (ttl$ C_d_tllist$)))
  (A_b_tllist$ (tNil$a (terminal$a B$)) (tCons$a (thd$a A$) (ttl$a A_b_tllist$)))))
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-fun f$ () A_c_fun$)
(declare-fun g$ () B_d_fun$)
(declare-fun n$ () Nat$)
(declare-fun uu$ () A_a_bool_fun_fun$)
(declare-fun xs$ () A_b_tllist$)
(declare-fun uua$ () B_b_bool_fun_fun$)
(declare-fun uub$ () A_b_tllist_a_b_tllist_bool_fun_fun$)
(declare-fun uuc$ () C_c_bool_fun_fun$)
(declare-fun uud$ () D_d_bool_fun_fun$)
(declare-fun uue$ () C_d_tllist_c_d_tllist_bool_fun_fun$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun less$ (Enat$) Enat_bool_fun$)
(declare-fun tmap$ (A_c_fun$ B_d_fun$ A_b_tllist$) C_d_tllist$)
(declare-fun tnth$ (C_d_tllist$ Nat$) C$)
(declare-fun less$a (Nat$) Nat_bool_fun$)
(declare-fun tnth$a (A_b_tllist$ Nat$) A$)
(declare-fun fun_app$ (C_d_tllist_bool_fun$ C_d_tllist$) Bool)
(declare-fun tlength$ (A_b_tllist$) Enat$)
(declare-fun fun_app$a (C_d_tllist_c_d_tllist_bool_fun_fun$ C_d_tllist$) C_d_tllist_bool_fun$)
(declare-fun fun_app$b (A_b_tllist_bool_fun$ A_b_tllist$) Bool)
(declare-fun fun_app$c (A_b_tllist_a_b_tllist_bool_fun_fun$ A_b_tllist$) A_b_tllist_bool_fun$)
(declare-fun fun_app$d (D_bool_fun$ D$) Bool)
(declare-fun fun_app$e (D_d_bool_fun_fun$ D$) D_bool_fun$)
(declare-fun fun_app$f (C_bool_fun$ C$) Bool)
(declare-fun fun_app$g (C_c_bool_fun_fun$ C$) C_bool_fun$)
(declare-fun fun_app$h (B_bool_fun$ B$) Bool)
(declare-fun fun_app$i (B_b_bool_fun_fun$ B$) B_bool_fun$)
(declare-fun fun_app$j (A_bool_fun$ A$) Bool)
(declare-fun fun_app$k (A_a_bool_fun_fun$ A$) A_bool_fun$)
(declare-fun fun_app$l (A_c_fun$ A$) C$)
(declare-fun fun_app$m (Enat_bool_fun$ Enat$) Bool)
(declare-fun fun_app$n (A_c_bool_fun_fun$ A$) C_bool_fun$)
(declare-fun fun_app$o (C_a_bool_fun_fun$ C$) A_bool_fun$)
(declare-fun fun_app$p (Nat_bool_fun$ Nat$) Bool)
(declare-fun fun_app$q (Enat_enat_fun$ Enat$) Enat$)
(declare-fun fun_app$r (Enat_nat_fun$ Enat$) Nat$)
(declare-fun fun_app$s (Nat_enat_fun$ Nat$) Enat$)
(declare-fun fun_app$t (Nat_nat_fun$ Nat$) Nat$)
(declare-fun fun_app$u (D_b_bool_fun_fun$ D$) B_bool_fun$)
(declare-fun fun_app$v (B_d_bool_fun_fun$ B$) D_bool_fun$)
(declare-fun tlength$a (C_d_tllist$) Enat$)
(declare-fun tllist_all2$ (C_c_bool_fun_fun$ D_d_bool_fun_fun$) C_d_tllist_c_d_tllist_bool_fun_fun$)
(declare-fun tllist_all2$a (A_c_bool_fun_fun$ B_d_bool_fun_fun$ A_b_tllist$ C_d_tllist$) Bool)
(declare-fun tllist_all2$b (C_a_bool_fun_fun$ D_b_bool_fun_fun$ C_d_tllist$ A_b_tllist$) Bool)
(declare-fun tllist_all2$c (A_a_bool_fun_fun$ B_b_bool_fun_fun$) A_b_tllist_a_b_tllist_bool_fun_fun$)
(assert (! (forall ((?v0 C_d_tllist$) (?v1 C_d_tllist$)) (! (= (fun_app$ (fun_app$a uue$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$ (fun_app$a uue$ ?v0) ?v1)))) :named a0))
(assert (! (forall ((?v0 A_b_tllist$) (?v1 A_b_tllist$)) (! (= (fun_app$b (fun_app$c uub$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$b (fun_app$c uub$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 D$) (?v1 D$)) (! (= (fun_app$d (fun_app$e uud$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$d (fun_app$e uud$ ?v0) ?v1)))) :named a2))
(assert (! (forall ((?v0 C$) (?v1 C$)) (! (= (fun_app$f (fun_app$g uuc$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$f (fun_app$g uuc$ ?v0) ?v1)))) :named a3))
(assert (! (forall ((?v0 B$) (?v1 B$)) (! (= (fun_app$h (fun_app$i uua$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$h (fun_app$i uua$ ?v0) ?v1)))) :named a4))
(assert (! (forall ((?v0 A$) (?v1 A$)) (! (= (fun_app$j (fun_app$k uu$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$j (fun_app$k uu$ ?v0) ?v1)))) :named a5))
(assert (! (not (= (tnth$ (tmap$ f$ g$ xs$) n$) (fun_app$l f$ (tnth$a xs$ n$)))) :named a6))
(assert (! (fun_app$m (less$ (enat$ n$)) (tlength$ xs$)) :named a7))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (enat$ ?v0) (enat$ ?v1)) (= ?v0 ?v1))) :named a8))
(assert (! (forall ((?v0 Enat$) (?v1 Nat$)) (=> (fun_app$m (less$ ?v0) (enat$ ?v1)) (exists ((?v2 Nat$)) (= ?v0 (enat$ ?v2))))) :named a9))
(assert (! (forall ((?v0 C_c_bool_fun_fun$) (?v1 D_d_bool_fun_fun$) (?v2 C_d_tllist$) (?v3 C_d_tllist$) (?v4 Nat$)) (=> (and (fun_app$ (fun_app$a (tllist_all2$ ?v0 ?v1) ?v2) ?v3) (fun_app$m (less$ (enat$ ?v4)) (tlength$a ?v3))) (fun_app$f (fun_app$g ?v0 (tnth$ ?v2 ?v4)) (tnth$ ?v3 ?v4)))) :named a10))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 B_d_bool_fun_fun$) (?v2 A_b_tllist$) (?v3 C_d_tllist$) (?v4 Nat$)) (=> (and (tllist_all2$a ?v0 ?v1 ?v2 ?v3) (fun_app$m (less$ (enat$ ?v4)) (tlength$a ?v3))) (fun_app$f (fun_app$n ?v0 (tnth$a ?v2 ?v4)) (tnth$ ?v3 ?v4)))) :named a11))
(assert (! (forall ((?v0 C_a_bool_fun_fun$) (?v1 D_b_bool_fun_fun$) (?v2 C_d_tllist$) (?v3 A_b_tllist$) (?v4 Nat$)) (=> (and (tllist_all2$b ?v0 ?v1 ?v2 ?v3) (fun_app$m (less$ (enat$ ?v4)) (tlength$ ?v3))) (fun_app$j (fun_app$o ?v0 (tnth$ ?v2 ?v4)) (tnth$a ?v3 ?v4)))) :named a12))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_b_bool_fun_fun$) (?v2 A_b_tllist$) (?v3 A_b_tllist$) (?v4 Nat$)) (=> (and (fun_app$b (fun_app$c (tllist_all2$c ?v0 ?v1) ?v2) ?v3) (fun_app$m (less$ (enat$ ?v4)) (tlength$ ?v3))) (fun_app$j (fun_app$k ?v0 (tnth$a ?v2 ?v4)) (tnth$a ?v3 ?v4)))) :named a13))
(assert (! (forall ((?v0 C_c_bool_fun_fun$) (?v1 D_d_bool_fun_fun$) (?v2 C_d_tllist$) (?v3 C_d_tllist$) (?v4 Nat$)) (=> (and (fun_app$ (fun_app$a (tllist_all2$ ?v0 ?v1) ?v2) ?v3) (fun_app$m (less$ (enat$ ?v4)) (tlength$a ?v2))) (fun_app$f (fun_app$g ?v0 (tnth$ ?v2 ?v4)) (tnth$ ?v3 ?v4)))) :named a14))
(assert (! (forall ((?v0 C_a_bool_fun_fun$) (?v1 D_b_bool_fun_fun$) (?v2 C_d_tllist$) (?v3 A_b_tllist$) (?v4 Nat$)) (=> (and (tllist_all2$b ?v0 ?v1 ?v2 ?v3) (fun_app$m (less$ (enat$ ?v4)) (tlength$a ?v2))) (fun_app$j (fun_app$o ?v0 (tnth$ ?v2 ?v4)) (tnth$a ?v3 ?v4)))) :named a15))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 B_d_bool_fun_fun$) (?v2 A_b_tllist$) (?v3 C_d_tllist$) (?v4 Nat$)) (=> (and (tllist_all2$a ?v0 ?v1 ?v2 ?v3) (fun_app$m (less$ (enat$ ?v4)) (tlength$ ?v2))) (fun_app$f (fun_app$n ?v0 (tnth$a ?v2 ?v4)) (tnth$ ?v3 ?v4)))) :named a16))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_b_bool_fun_fun$) (?v2 A_b_tllist$) (?v3 A_b_tllist$) (?v4 Nat$)) (=> (and (fun_app$b (fun_app$c (tllist_all2$c ?v0 ?v1) ?v2) ?v3) (fun_app$m (less$ (enat$ ?v4)) (tlength$ ?v2))) (fun_app$j (fun_app$k ?v0 (tnth$a ?v2 ?v4)) (tnth$a ?v3 ?v4)))) :named a17))
(assert (! (forall ((?v0 Enat_bool_fun$) (?v1 Enat$)) (=> (forall ((?v2 Enat$)) (=> (forall ((?v3 Enat$)) (=> (fun_app$m (less$ ?v3) ?v2) (fun_app$m ?v0 ?v3))) (fun_app$m ?v0 ?v2))) (fun_app$m ?v0 ?v1))) :named a18))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (= (not (= ?v0 ?v1)) (or (fun_app$m (less$ ?v0) ?v1) (fun_app$m (less$ ?v1) ?v0)))) :named a19))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (not (= ?v0 ?v1)) (or (fun_app$p (less$a ?v0) ?v1) (fun_app$p (less$a ?v1) ?v0)))) :named a20))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (= (not (fun_app$m (less$ ?v0) ?v1)) (or (fun_app$m (less$ ?v1) ?v0) (= ?v0 ?v1)))) :named a21))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (not (fun_app$p (less$a ?v0) ?v1)) (or (fun_app$p (less$a ?v1) ?v0) (= ?v0 ?v1)))) :named a22))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (=> (and (=> (fun_app$m (less$ ?v0) ?v1) false) (and (=> (= ?v0 ?v1) false) (=> (fun_app$m (less$ ?v1) ?v0) false))) false)) :named a23))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (and (=> (fun_app$p (less$a ?v0) ?v1) false) (and (=> (= ?v0 ?v1) false) (=> (fun_app$p (less$a ?v1) ?v0) false))) false)) :named a24))
(assert (! (forall ((?v0 Enat_bool_fun$) (?v1 Enat$)) (=> (forall ((?v2 Enat$)) (=> (forall ((?v3 Enat$)) (=> (fun_app$m (less$ ?v3) ?v2) (fun_app$m ?v0 ?v3))) (fun_app$m ?v0 ?v2))) (fun_app$m ?v0 ?v1))) :named a25))
(assert (! (forall ((?v0 Nat_bool_fun$) (?v1 Nat$)) (=> (forall ((?v2 Nat$)) (=> (forall ((?v3 Nat$)) (=> (fun_app$p (less$a ?v3) ?v2) (fun_app$p ?v0 ?v3))) (fun_app$p ?v0 ?v2))) (fun_app$p ?v0 ?v1))) :named a26))
(assert (! (forall ((?v0 Enat$) (?v1 Enat_enat_fun$) (?v2 Enat$) (?v3 Enat$)) (=> (and (= ?v0 (fun_app$q ?v1 ?v2)) (and (fun_app$m (less$ ?v2) ?v3) (forall ((?v4 Enat$) (?v5 Enat$)) (=> (fun_app$m (less$ ?v4) ?v5) (fun_app$m (less$ (fun_app$q ?v1 ?v4)) (fun_app$q ?v1 ?v5)))))) (fun_app$m (less$ ?v0) (fun_app$q ?v1 ?v3)))) :named a27))
(assert (! (forall ((?v0 Nat$) (?v1 Enat_nat_fun$) (?v2 Enat$) (?v3 Enat$)) (=> (and (= ?v0 (fun_app$r ?v1 ?v2)) (and (fun_app$m (less$ ?v2) ?v3) (forall ((?v4 Enat$) (?v5 Enat$)) (=> (fun_app$m (less$ ?v4) ?v5) (fun_app$p (less$a (fun_app$r ?v1 ?v4)) (fun_app$r ?v1 ?v5)))))) (fun_app$p (less$a ?v0) (fun_app$r ?v1 ?v3)))) :named a28))
(assert (! (forall ((?v0 Enat$) (?v1 Nat_enat_fun$) (?v2 Nat$) (?v3 Nat$)) (=> (and (= ?v0 (fun_app$s ?v1 ?v2)) (and (fun_app$p (less$a ?v2) ?v3) (forall ((?v4 Nat$) (?v5 Nat$)) (=> (fun_app$p (less$a ?v4) ?v5) (fun_app$m (less$ (fun_app$s ?v1 ?v4)) (fun_app$s ?v1 ?v5)))))) (fun_app$m (less$ ?v0) (fun_app$s ?v1 ?v3)))) :named a29))
(assert (! (forall ((?v0 Nat$) (?v1 Nat_nat_fun$) (?v2 Nat$) (?v3 Nat$)) (=> (and (= ?v0 (fun_app$t ?v1 ?v2)) (and (fun_app$p (less$a ?v2) ?v3) (forall ((?v4 Nat$) (?v5 Nat$)) (=> (fun_app$p (less$a ?v4) ?v5) (fun_app$p (less$a (fun_app$t ?v1 ?v4)) (fun_app$t ?v1 ?v5)))))) (fun_app$p (less$a ?v0) (fun_app$t ?v1 ?v3)))) :named a30))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (! (= (fun_app$m (less$ (enat$ ?v0)) (enat$ ?v1)) (fun_app$p (less$a ?v0) ?v1)) :pattern ((fun_app$m (less$ (enat$ ?v0)) (enat$ ?v1))))) :named a31))
(assert (! (= (tllist_all2$c uu$ uua$) uub$) :named a32))
(assert (! (= (tllist_all2$ uuc$ uud$) uue$) :named a33))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_b_bool_fun_fun$) (?v2 A_b_tllist$) (?v3 A_b_tllist$) (?v4 A_a_bool_fun_fun$) (?v5 B_b_bool_fun_fun$)) (=> (and (fun_app$b (fun_app$c (tllist_all2$c ?v0 ?v1) ?v2) ?v3) (and (forall ((?v6 A$) (?v7 A$)) (=> (fun_app$j (fun_app$k ?v0 ?v6) ?v7) (fun_app$j (fun_app$k ?v4 ?v6) ?v7))) (forall ((?v6 B$) (?v7 B$)) (=> (fun_app$h (fun_app$i ?v1 ?v6) ?v7) (fun_app$h (fun_app$i ?v5 ?v6) ?v7))))) (fun_app$b (fun_app$c (tllist_all2$c ?v4 ?v5) ?v2) ?v3))) :named a34))
(assert (! (forall ((?v0 C_a_bool_fun_fun$) (?v1 D_b_bool_fun_fun$) (?v2 C_d_tllist$) (?v3 A_b_tllist$) (?v4 C_a_bool_fun_fun$) (?v5 D_b_bool_fun_fun$)) (=> (and (tllist_all2$b ?v0 ?v1 ?v2 ?v3) (and (forall ((?v6 C$) (?v7 A$)) (=> (fun_app$j (fun_app$o ?v0 ?v6) ?v7) (fun_app$j (fun_app$o ?v4 ?v6) ?v7))) (forall ((?v6 D$) (?v7 B$)) (=> (fun_app$h (fun_app$u ?v1 ?v6) ?v7) (fun_app$h (fun_app$u ?v5 ?v6) ?v7))))) (tllist_all2$b ?v4 ?v5 ?v2 ?v3))) :named a35))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 B_d_bool_fun_fun$) (?v2 A_b_tllist$) (?v3 C_d_tllist$) (?v4 A_c_bool_fun_fun$) (?v5 B_d_bool_fun_fun$)) (=> (and (tllist_all2$a ?v0 ?v1 ?v2 ?v3) (and (forall ((?v6 A$) (?v7 C$)) (=> (fun_app$f (fun_app$n ?v0 ?v6) ?v7) (fun_app$f (fun_app$n ?v4 ?v6) ?v7))) (forall ((?v6 B$) (?v7 D$)) (=> (fun_app$d (fun_app$v ?v1 ?v6) ?v7) (fun_app$d (fun_app$v ?v5 ?v6) ?v7))))) (tllist_all2$a ?v4 ?v5 ?v2 ?v3))) :named a36))
(assert (! (forall ((?v0 C_c_bool_fun_fun$) (?v1 D_d_bool_fun_fun$) (?v2 C_d_tllist$) (?v3 C_d_tllist$) (?v4 C_c_bool_fun_fun$) (?v5 D_d_bool_fun_fun$)) (=> (and (fun_app$ (fun_app$a (tllist_all2$ ?v0 ?v1) ?v2) ?v3) (and (forall ((?v6 C$) (?v7 C$)) (=> (fun_app$f (fun_app$g ?v0 ?v6) ?v7) (fun_app$f (fun_app$g ?v4 ?v6) ?v7))) (forall ((?v6 D$) (?v7 D$)) (=> (fun_app$d (fun_app$e ?v1 ?v6) ?v7) (fun_app$d (fun_app$e ?v5 ?v6) ?v7))))) (fun_app$ (fun_app$a (tllist_all2$ ?v4 ?v5) ?v2) ?v3))) :named a37))
(assert (! (forall ((?v0 C_a_bool_fun_fun$) (?v1 D_b_bool_fun_fun$) (?v2 C_d_tllist$) (?v3 A_b_tllist$)) (=> (tllist_all2$b ?v0 ?v1 ?v2 ?v3) (= (tlength$a ?v2) (tlength$ ?v3)))) :named a38))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 B_d_bool_fun_fun$) (?v2 A_b_tllist$) (?v3 C_d_tllist$)) (=> (tllist_all2$a ?v0 ?v1 ?v2 ?v3) (= (tlength$ ?v2) (tlength$a ?v3)))) :named a39))
(assert (! (forall ((?v0 C_c_bool_fun_fun$) (?v1 D_d_bool_fun_fun$) (?v2 C_d_tllist$) (?v3 C_d_tllist$)) (=> (fun_app$ (fun_app$a (tllist_all2$ ?v0 ?v1) ?v2) ?v3) (= (tlength$a ?v2) (tlength$a ?v3)))) :named a40))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_b_bool_fun_fun$) (?v2 A_b_tllist$) (?v3 A_b_tllist$)) (=> (fun_app$b (fun_app$c (tllist_all2$c ?v0 ?v1) ?v2) ?v3) (= (tlength$ ?v2) (tlength$ ?v3)))) :named a41))
(assert (! (forall ((?v0 Enat$) (?v1 Nat$)) (=> (and (fun_app$m (less$ ?v0) (enat$ ?v1)) (forall ((?v2 Nat$)) (=> (and (= ?v0 (enat$ ?v2)) (fun_app$p (less$a ?v2) ?v1)) false))) false)) :named a42))
(check-sat)
;(get-unsat-core)
