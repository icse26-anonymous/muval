; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 331
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort C$ 0)
(declare-sort D$ 0)
(declare-sort Nat$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_c_fun$ 0)
(declare-sort B_b_fun$ 0)
(declare-sort B_d_fun$ 0)
(declare-sort C_a_fun$ 0)
(declare-sort C_c_fun$ 0)
(declare-sort D_b_fun$ 0)
(declare-sort D_d_fun$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort C_bool_fun$ 0)
(declare-sort D_bool_fun$ 0)
(declare-sort A_a_bool_fun_fun$ 0)
(declare-sort A_c_bool_fun_fun$ 0)
(declare-sort B_b_bool_fun_fun$ 0)
(declare-sort B_d_bool_fun_fun$ 0)
(declare-sort C_a_bool_fun_fun$ 0)
(declare-sort C_c_bool_fun_fun$ 0)
(declare-sort D_b_bool_fun_fun$ 0)
(declare-sort D_d_bool_fun_fun$ 0)
(declare-sort C_a_fun_c_a_fun_fun$ 0)
(declare-sort C_c_fun_c_a_fun_fun$ 0)
(declare-sort D_b_fun_d_b_fun_fun$ 0)
(declare-sort D_d_fun_d_b_fun_fun$ 0)
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-codatatypes () ((A_b_tllist$ (tNil$ (terminal$ B$)) (tCons$ (thd$ A$) (ttl$ A_b_tllist$)))
  (C_d_tllist$ (tNil$a (terminal$a D$)) (tCons$a (thd$a C$) (ttl$a C_d_tllist$)))
  (B_a_tllist$ (tNil$b (terminal$b A$)) (tCons$b (thd$b B$) (ttl$b B_a_tllist$)))
  (A_d_tllist$ (tNil$c (terminal$c D$)) (tCons$c (thd$c A$) (ttl$c A_d_tllist$)))
  (A_c_tllist$ (tNil$d (terminal$d C$)) (tCons$d (thd$d A$) (ttl$d A_c_tllist$)))
  (A_a_tllist$ (tNil$e (terminal$e A$)) (tCons$e (thd$e A$) (ttl$e A_a_tllist$)))
  (B_b_tllist$ (tNil$f (terminal$f B$)) (tCons$f (thd$f B$) (ttl$f B_b_tllist$)))
  (B_c_tllist$ (tNil$g (terminal$g C$)) (tCons$g (thd$g B$) (ttl$g B_c_tllist$)))
  (B_d_tllist$ (tNil$h (terminal$h D$)) (tCons$h (thd$h B$) (ttl$h B_d_tllist$)))
  (C_a_tllist$ (tNil$i (terminal$i A$)) (tCons$i (thd$i C$) (ttl$i C_a_tllist$)))
  (C_b_tllist$ (tNil$j (terminal$j B$)) (tCons$j (thd$j C$) (ttl$j C_b_tllist$)))
  (C_c_tllist$ (tNil$k (terminal$k C$)) (tCons$k (thd$k C$) (ttl$k C_c_tllist$)))
  (D_c_tllist$ (tNil$l (terminal$l C$)) (tCons$l (thd$l D$) (ttl$l D_c_tllist$)))
  (D_d_tllist$ (tNil$m (terminal$m D$)) (tCons$m (thd$m D$) (ttl$m D_d_tllist$)))
  (D_a_tllist$ (tNil$n (terminal$n A$)) (tCons$n (thd$n D$) (ttl$n D_a_tllist$)))
  (D_b_tllist$ (tNil$o (terminal$o B$)) (tCons$o (thd$o D$) (ttl$o D_b_tllist$)))))
(declare-fun f$ () C_a_fun$)
(declare-fun g$ () D_b_fun$)
(declare-fun id$ () C_c_fun$)
(declare-fun xs$ () C_d_tllist$)
(declare-fun id$a () D_d_fun$)
(declare-fun id$b () A_a_fun$)
(declare-fun id$c () B_b_fun$)
(declare-fun comp$ (A_a_fun$) C_a_fun_c_a_fun_fun$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun less$ (Enat$ Enat$) Bool)
(declare-fun tmap$ (C_a_fun$ D_b_fun$ C_d_tllist$) A_b_tllist$)
(declare-fun tnth$ (B_a_tllist$ Nat$) B$)
(declare-fun comp$a (B_b_fun$) D_b_fun_d_b_fun_fun$)
(declare-fun comp$b (C_a_fun$) C_c_fun_c_a_fun_fun$)
(declare-fun comp$c (D_b_fun$) D_d_fun_d_b_fun_fun$)
(declare-fun tmap$a (B_b_fun$ A_a_fun$ B_a_tllist$) B_a_tllist$)
(declare-fun tmap$b (A_a_fun$ D_b_fun$ A_d_tllist$) A_b_tllist$)
(declare-fun tmap$c (A_a_fun$ C_a_fun$ A_c_tllist$) A_a_tllist$)
(declare-fun tmap$d (A_a_fun$ A_a_fun$ A_a_tllist$) A_a_tllist$)
(declare-fun tmap$e (A_c_fun$ B_d_fun$ A_b_tllist$) C_d_tllist$)
(declare-fun tmap$f (C_c_fun$ D_d_fun$ C_d_tllist$) C_d_tllist$)
(declare-fun tmap$g (A_a_fun$ B_b_fun$ A_b_tllist$) A_b_tllist$)
(declare-fun tmap$h (A_a_fun$ C_c_fun$ A_c_tllist$) A_c_tllist$)
(declare-fun tmap$i (A_a_fun$ D_d_fun$ A_d_tllist$) A_d_tllist$)
(declare-fun tmap$j (B_b_fun$ B_b_fun$ B_b_tllist$) B_b_tllist$)
(declare-fun tmap$k (B_b_fun$ C_c_fun$ B_c_tllist$) B_c_tllist$)
(declare-fun tmap$l (B_b_fun$ D_d_fun$ B_d_tllist$) B_d_tllist$)
(declare-fun tmap$m (C_c_fun$ A_a_fun$ C_a_tllist$) C_a_tllist$)
(declare-fun tmap$n (C_c_fun$ B_b_fun$ C_b_tllist$) C_b_tllist$)
(declare-fun tmap$o (C_c_fun$ C_c_fun$ C_c_tllist$) C_c_tllist$)
(declare-fun tmap$p (C_a_fun$ C_a_fun$ C_c_tllist$) A_a_tllist$)
(declare-fun tmap$q (C_a_fun$ A_a_fun$ C_a_tllist$) A_a_tllist$)
(declare-fun tmap$r (C_c_fun$ C_a_fun$ C_c_tllist$) C_a_tllist$)
(declare-fun tmap$s (D_b_fun$ C_a_fun$ D_c_tllist$) B_a_tllist$)
(declare-fun tmap$t (D_d_fun$ C_c_fun$ D_c_tllist$) D_c_tllist$)
(declare-fun tmap$u (D_b_fun$ D_b_fun$ D_d_tllist$) B_b_tllist$)
(declare-fun tmap$v (D_d_fun$ D_d_fun$ D_d_tllist$) D_d_tllist$)
(declare-fun tmap$w (D_b_fun$ A_a_fun$ D_a_tllist$) B_a_tllist$)
(declare-fun tmap$x (D_d_fun$ C_a_fun$ D_c_tllist$) D_a_tllist$)
(declare-fun tmap$y (D_b_fun$ B_b_fun$ D_b_tllist$) B_b_tllist$)
(declare-fun tmap$z (D_d_fun$ D_b_fun$ D_d_tllist$) D_b_tllist$)
(declare-fun tnth$a (A_b_tllist$ Nat$) A$)
(declare-fun tnth$b (A_d_tllist$ Nat$) A$)
(declare-fun tnth$c (A_a_tllist$ Nat$) A$)
(declare-fun tnth$d (A_c_tllist$ Nat$) A$)
(declare-fun tnth$e (C_d_tllist$ Nat$) C$)
(declare-fun tmap$aa (C_a_fun$ C_c_fun$ C_c_tllist$) A_c_tllist$)
(declare-fun fun_app$ (B_b_fun$ B$) B$)
(declare-fun is_TNil$ (B_a_tllist$) Bool)
(declare-fun tlength$ (A_b_tllist$) Enat$)
(declare-fun fun_app$a (A_a_fun$ A$) A$)
(declare-fun fun_app$b (C_c_fun$ C$) C$)
(declare-fun fun_app$c (A_c_fun$ A$) C$)
(declare-fun fun_app$d (C_a_fun$ C$) A$)
(declare-fun fun_app$e (D_b_fun$ D$) B$)
(declare-fun fun_app$f (B_d_fun$ B$) D$)
(declare-fun fun_app$g (D_d_fun$ D$) D$)
(declare-fun fun_app$h (C_a_fun_c_a_fun_fun$ C_a_fun$) C_a_fun$)
(declare-fun fun_app$i (D_b_fun_d_b_fun_fun$ D_b_fun$) D_b_fun$)
(declare-fun fun_app$j (C_c_fun_c_a_fun_fun$ C_c_fun$) C_a_fun$)
(declare-fun fun_app$k (D_d_fun_d_b_fun_fun$ D_d_fun$) D_b_fun$)
(declare-fun fun_app$l (C_bool_fun$ C$) Bool)
(declare-fun fun_app$m (C_c_bool_fun_fun$ C$) C_bool_fun$)
(declare-fun fun_app$n (A_bool_fun$ A$) Bool)
(declare-fun fun_app$o (C_a_bool_fun_fun$ C$) A_bool_fun$)
(declare-fun fun_app$p (A_c_bool_fun_fun$ A$) C_bool_fun$)
(declare-fun fun_app$q (A_a_bool_fun_fun$ A$) A_bool_fun$)
(declare-fun fun_app$r (D_bool_fun$ D$) Bool)
(declare-fun fun_app$s (D_d_bool_fun_fun$ D$) D_bool_fun$)
(declare-fun fun_app$t (B_bool_fun$ B$) Bool)
(declare-fun fun_app$u (D_b_bool_fun_fun$ D$) B_bool_fun$)
(declare-fun fun_app$v (B_d_bool_fun_fun$ B$) D_bool_fun$)
(declare-fun fun_app$w (B_b_bool_fun_fun$ B$) B_bool_fun$)
(declare-fun is_TNil$a (A_a_tllist$) Bool)
(declare-fun is_TNil$b (A_c_tllist$) Bool)
(declare-fun is_TNil$c (A_b_tllist$) Bool)
(declare-fun is_TNil$d (A_d_tllist$) Bool)
(declare-fun is_TNil$e (C_d_tllist$) Bool)
(declare-fun tlength$a (C_d_tllist$) Enat$)
(declare-fun tlength$b (B_a_tllist$) Enat$)
(declare-fun tlength$c (A_d_tllist$) Enat$)
(declare-fun tlength$d (A_c_tllist$) Enat$)
(declare-fun tlength$e (A_a_tllist$) Enat$)
(declare-fun tllist_all2$ (A_a_bool_fun_fun$ B_b_bool_fun_fun$ A_b_tllist$ A_b_tllist$) Bool)
(declare-fun tllist_all2$a (A_c_bool_fun_fun$ B_d_bool_fun_fun$ A_b_tllist$ C_d_tllist$) Bool)
(declare-fun tllist_all2$b (C_a_bool_fun_fun$ D_b_bool_fun_fun$ C_d_tllist$ A_b_tllist$) Bool)
(declare-fun tllist_all2$c (C_c_bool_fun_fun$ D_d_bool_fun_fun$ C_d_tllist$ C_d_tllist$) Bool)
(assert (! (not (= (tlength$ (tmap$ f$ g$ xs$)) (tlength$a xs$))) :named a0))
(assert (! (forall ((?v0 B_b_fun$) (?v1 A_a_fun$) (?v2 B_a_tllist$)) (= (ttl$b (tmap$a ?v0 ?v1 ?v2)) (tmap$a ?v0 ?v1 (ttl$b ?v2)))) :named a1))
(assert (! (forall ((?v0 A_a_fun$) (?v1 D_b_fun$) (?v2 A_d_tllist$)) (= (ttl$ (tmap$b ?v0 ?v1 ?v2)) (tmap$b ?v0 ?v1 (ttl$c ?v2)))) :named a2))
(assert (! (forall ((?v0 A_a_fun$) (?v1 C_a_fun$) (?v2 A_c_tllist$)) (= (ttl$e (tmap$c ?v0 ?v1 ?v2)) (tmap$c ?v0 ?v1 (ttl$d ?v2)))) :named a3))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_a_tllist$)) (= (ttl$e (tmap$d ?v0 ?v1 ?v2)) (tmap$d ?v0 ?v1 (ttl$e ?v2)))) :named a4))
(assert (! (forall ((?v0 A_c_fun$) (?v1 B_d_fun$) (?v2 A_b_tllist$)) (= (ttl$a (tmap$e ?v0 ?v1 ?v2)) (tmap$e ?v0 ?v1 (ttl$ ?v2)))) :named a5))
(assert (! (forall ((?v0 C_c_fun$) (?v1 D_d_fun$) (?v2 C_d_tllist$)) (= (ttl$a (tmap$f ?v0 ?v1 ?v2)) (tmap$f ?v0 ?v1 (ttl$a ?v2)))) :named a6))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_b_fun$) (?v2 A_b_tllist$)) (= (ttl$ (tmap$g ?v0 ?v1 ?v2)) (tmap$g ?v0 ?v1 (ttl$ ?v2)))) :named a7))
(assert (! (forall ((?v0 C_a_fun$) (?v1 D_b_fun$) (?v2 C_d_tllist$)) (= (ttl$ (tmap$ ?v0 ?v1 ?v2)) (tmap$ ?v0 ?v1 (ttl$a ?v2)))) :named a8))
(assert (! (forall ((?v0 B_b_fun$) (?v1 A_a_fun$) (?v2 B_a_tllist$)) (= (is_TNil$ (tmap$a ?v0 ?v1 ?v2)) (is_TNil$ ?v2))) :named a9))
(assert (! (forall ((?v0 A_a_fun$) (?v1 C_a_fun$) (?v2 A_c_tllist$)) (= (is_TNil$a (tmap$c ?v0 ?v1 ?v2)) (is_TNil$b ?v2))) :named a10))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_a_tllist$)) (= (is_TNil$a (tmap$d ?v0 ?v1 ?v2)) (is_TNil$a ?v2))) :named a11))
(assert (! (forall ((?v0 A_a_fun$) (?v1 D_b_fun$) (?v2 A_d_tllist$)) (= (is_TNil$c (tmap$b ?v0 ?v1 ?v2)) (is_TNil$d ?v2))) :named a12))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_b_fun$) (?v2 A_b_tllist$)) (= (is_TNil$c (tmap$g ?v0 ?v1 ?v2)) (is_TNil$c ?v2))) :named a13))
(assert (! (forall ((?v0 A_c_fun$) (?v1 B_d_fun$) (?v2 A_b_tllist$)) (= (is_TNil$e (tmap$e ?v0 ?v1 ?v2)) (is_TNil$c ?v2))) :named a14))
(assert (! (forall ((?v0 C_c_fun$) (?v1 D_d_fun$) (?v2 C_d_tllist$)) (= (is_TNil$e (tmap$f ?v0 ?v1 ?v2)) (is_TNil$e ?v2))) :named a15))
(assert (! (forall ((?v0 C_a_fun$) (?v1 D_b_fun$) (?v2 C_d_tllist$)) (= (is_TNil$c (tmap$ ?v0 ?v1 ?v2)) (is_TNil$e ?v2))) :named a16))
(assert (! (forall ((?v0 B_b_fun$) (?v1 A_a_fun$) (?v2 B$) (?v3 B_a_tllist$)) (! (= (tmap$a ?v0 ?v1 (tCons$b ?v2 ?v3)) (tCons$b (fun_app$ ?v0 ?v2) (tmap$a ?v0 ?v1 ?v3))) :pattern ((tmap$a ?v0 ?v1 (tCons$b ?v2 ?v3))))) :named a17))
(assert (! (forall ((?v0 A_a_fun$) (?v1 C_a_fun$) (?v2 A$) (?v3 A_c_tllist$)) (! (= (tmap$c ?v0 ?v1 (tCons$d ?v2 ?v3)) (tCons$e (fun_app$a ?v0 ?v2) (tmap$c ?v0 ?v1 ?v3))) :pattern ((tmap$c ?v0 ?v1 (tCons$d ?v2 ?v3))))) :named a18))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A$) (?v3 A_a_tllist$)) (! (= (tmap$d ?v0 ?v1 (tCons$e ?v2 ?v3)) (tCons$e (fun_app$a ?v0 ?v2) (tmap$d ?v0 ?v1 ?v3))) :pattern ((tmap$d ?v0 ?v1 (tCons$e ?v2 ?v3))))) :named a19))
(assert (! (forall ((?v0 A_a_fun$) (?v1 D_b_fun$) (?v2 A$) (?v3 A_d_tllist$)) (! (= (tmap$b ?v0 ?v1 (tCons$c ?v2 ?v3)) (tCons$ (fun_app$a ?v0 ?v2) (tmap$b ?v0 ?v1 ?v3))) :pattern ((tmap$b ?v0 ?v1 (tCons$c ?v2 ?v3))))) :named a20))
(assert (! (forall ((?v0 C_c_fun$) (?v1 D_d_fun$) (?v2 C$) (?v3 C_d_tllist$)) (! (= (tmap$f ?v0 ?v1 (tCons$a ?v2 ?v3)) (tCons$a (fun_app$b ?v0 ?v2) (tmap$f ?v0 ?v1 ?v3))) :pattern ((tmap$f ?v0 ?v1 (tCons$a ?v2 ?v3))))) :named a21))
(assert (! (forall ((?v0 A_c_fun$) (?v1 B_d_fun$) (?v2 A$) (?v3 A_b_tllist$)) (! (= (tmap$e ?v0 ?v1 (tCons$ ?v2 ?v3)) (tCons$a (fun_app$c ?v0 ?v2) (tmap$e ?v0 ?v1 ?v3))) :pattern ((tmap$e ?v0 ?v1 (tCons$ ?v2 ?v3))))) :named a22))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_b_fun$) (?v2 A$) (?v3 A_b_tllist$)) (! (= (tmap$g ?v0 ?v1 (tCons$ ?v2 ?v3)) (tCons$ (fun_app$a ?v0 ?v2) (tmap$g ?v0 ?v1 ?v3))) :pattern ((tmap$g ?v0 ?v1 (tCons$ ?v2 ?v3))))) :named a23))
(assert (! (forall ((?v0 C_a_fun$) (?v1 D_b_fun$) (?v2 C$) (?v3 C_d_tllist$)) (! (= (tmap$ ?v0 ?v1 (tCons$a ?v2 ?v3)) (tCons$ (fun_app$d ?v0 ?v2) (tmap$ ?v0 ?v1 ?v3))) :pattern ((tmap$ ?v0 ?v1 (tCons$a ?v2 ?v3))))) :named a24))
(assert (! (forall ((?v0 B_b_fun$) (?v1 A_a_fun$) (?v2 B_a_tllist$) (?v3 B$) (?v4 B_a_tllist$)) (= (= (tmap$a ?v0 ?v1 ?v2) (tCons$b ?v3 ?v4)) (exists ((?v5 B$) (?v6 B_a_tllist$)) (and (= ?v2 (tCons$b ?v5 ?v6)) (and (= (fun_app$ ?v0 ?v5) ?v3) (= (tmap$a ?v0 ?v1 ?v6) ?v4)))))) :named a25))
(assert (! (forall ((?v0 A_a_fun$) (?v1 C_a_fun$) (?v2 A_c_tllist$) (?v3 A$) (?v4 A_a_tllist$)) (= (= (tmap$c ?v0 ?v1 ?v2) (tCons$e ?v3 ?v4)) (exists ((?v5 A$) (?v6 A_c_tllist$)) (and (= ?v2 (tCons$d ?v5 ?v6)) (and (= (fun_app$a ?v0 ?v5) ?v3) (= (tmap$c ?v0 ?v1 ?v6) ?v4)))))) :named a26))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_a_tllist$) (?v3 A$) (?v4 A_a_tllist$)) (= (= (tmap$d ?v0 ?v1 ?v2) (tCons$e ?v3 ?v4)) (exists ((?v5 A$) (?v6 A_a_tllist$)) (and (= ?v2 (tCons$e ?v5 ?v6)) (and (= (fun_app$a ?v0 ?v5) ?v3) (= (tmap$d ?v0 ?v1 ?v6) ?v4)))))) :named a27))
(assert (! (forall ((?v0 A_a_fun$) (?v1 D_b_fun$) (?v2 A_d_tllist$) (?v3 A$) (?v4 A_b_tllist$)) (= (= (tmap$b ?v0 ?v1 ?v2) (tCons$ ?v3 ?v4)) (exists ((?v5 A$) (?v6 A_d_tllist$)) (and (= ?v2 (tCons$c ?v5 ?v6)) (and (= (fun_app$a ?v0 ?v5) ?v3) (= (tmap$b ?v0 ?v1 ?v6) ?v4)))))) :named a28))
(assert (! (forall ((?v0 C_c_fun$) (?v1 D_d_fun$) (?v2 C_d_tllist$) (?v3 C$) (?v4 C_d_tllist$)) (= (= (tmap$f ?v0 ?v1 ?v2) (tCons$a ?v3 ?v4)) (exists ((?v5 C$) (?v6 C_d_tllist$)) (and (= ?v2 (tCons$a ?v5 ?v6)) (and (= (fun_app$b ?v0 ?v5) ?v3) (= (tmap$f ?v0 ?v1 ?v6) ?v4)))))) :named a29))
(assert (! (forall ((?v0 A_c_fun$) (?v1 B_d_fun$) (?v2 A_b_tllist$) (?v3 C$) (?v4 C_d_tllist$)) (= (= (tmap$e ?v0 ?v1 ?v2) (tCons$a ?v3 ?v4)) (exists ((?v5 A$) (?v6 A_b_tllist$)) (and (= ?v2 (tCons$ ?v5 ?v6)) (and (= (fun_app$c ?v0 ?v5) ?v3) (= (tmap$e ?v0 ?v1 ?v6) ?v4)))))) :named a30))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_b_fun$) (?v2 A_b_tllist$) (?v3 A$) (?v4 A_b_tllist$)) (= (= (tmap$g ?v0 ?v1 ?v2) (tCons$ ?v3 ?v4)) (exists ((?v5 A$) (?v6 A_b_tllist$)) (and (= ?v2 (tCons$ ?v5 ?v6)) (and (= (fun_app$a ?v0 ?v5) ?v3) (= (tmap$g ?v0 ?v1 ?v6) ?v4)))))) :named a31))
(assert (! (forall ((?v0 C_a_fun$) (?v1 D_b_fun$) (?v2 C_d_tllist$) (?v3 A$) (?v4 A_b_tllist$)) (= (= (tmap$ ?v0 ?v1 ?v2) (tCons$ ?v3 ?v4)) (exists ((?v5 C$) (?v6 C_d_tllist$)) (and (= ?v2 (tCons$a ?v5 ?v6)) (and (= (fun_app$d ?v0 ?v5) ?v3) (= (tmap$ ?v0 ?v1 ?v6) ?v4)))))) :named a32))
(assert (! (forall ((?v0 B_b_fun$) (?v1 A_a_fun$) (?v2 B_a_tllist$) (?v3 A$)) (= (= (tmap$a ?v0 ?v1 ?v2) (tNil$b ?v3)) (exists ((?v4 A$)) (and (= ?v2 (tNil$b ?v4)) (= (fun_app$a ?v1 ?v4) ?v3))))) :named a33))
(assert (! (forall ((?v0 A_a_fun$) (?v1 D_b_fun$) (?v2 A_d_tllist$) (?v3 B$)) (= (= (tmap$b ?v0 ?v1 ?v2) (tNil$ ?v3)) (exists ((?v4 D$)) (and (= ?v2 (tNil$c ?v4)) (= (fun_app$e ?v1 ?v4) ?v3))))) :named a34))
(assert (! (forall ((?v0 A_a_fun$) (?v1 C_a_fun$) (?v2 A_c_tllist$) (?v3 A$)) (= (= (tmap$c ?v0 ?v1 ?v2) (tNil$e ?v3)) (exists ((?v4 C$)) (and (= ?v2 (tNil$d ?v4)) (= (fun_app$d ?v1 ?v4) ?v3))))) :named a35))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_a_tllist$) (?v3 A$)) (= (= (tmap$d ?v0 ?v1 ?v2) (tNil$e ?v3)) (exists ((?v4 A$)) (and (= ?v2 (tNil$e ?v4)) (= (fun_app$a ?v1 ?v4) ?v3))))) :named a36))
(assert (! (forall ((?v0 A_c_fun$) (?v1 B_d_fun$) (?v2 A_b_tllist$) (?v3 D$)) (= (= (tmap$e ?v0 ?v1 ?v2) (tNil$a ?v3)) (exists ((?v4 B$)) (and (= ?v2 (tNil$ ?v4)) (= (fun_app$f ?v1 ?v4) ?v3))))) :named a37))
(assert (! (forall ((?v0 C_c_fun$) (?v1 D_d_fun$) (?v2 C_d_tllist$) (?v3 D$)) (= (= (tmap$f ?v0 ?v1 ?v2) (tNil$a ?v3)) (exists ((?v4 D$)) (and (= ?v2 (tNil$a ?v4)) (= (fun_app$g ?v1 ?v4) ?v3))))) :named a38))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_b_fun$) (?v2 A_b_tllist$) (?v3 B$)) (= (= (tmap$g ?v0 ?v1 ?v2) (tNil$ ?v3)) (exists ((?v4 B$)) (and (= ?v2 (tNil$ ?v4)) (= (fun_app$ ?v1 ?v4) ?v3))))) :named a39))
(assert (! (forall ((?v0 C_a_fun$) (?v1 D_b_fun$) (?v2 C_d_tllist$) (?v3 B$)) (= (= (tmap$ ?v0 ?v1 ?v2) (tNil$ ?v3)) (exists ((?v4 D$)) (and (= ?v2 (tNil$a ?v4)) (= (fun_app$e ?v1 ?v4) ?v3))))) :named a40))
(assert (! (forall ((?v0 B$) (?v1 B_a_tllist$) (?v2 B_b_fun$) (?v3 A_a_fun$) (?v4 B_a_tllist$)) (= (= (tCons$b ?v0 ?v1) (tmap$a ?v2 ?v3 ?v4)) (exists ((?v5 B$) (?v6 B_a_tllist$)) (and (= ?v4 (tCons$b ?v5 ?v6)) (and (= (fun_app$ ?v2 ?v5) ?v0) (= (tmap$a ?v2 ?v3 ?v6) ?v1)))))) :named a41))
(assert (! (forall ((?v0 A$) (?v1 A_a_tllist$) (?v2 A_a_fun$) (?v3 C_a_fun$) (?v4 A_c_tllist$)) (= (= (tCons$e ?v0 ?v1) (tmap$c ?v2 ?v3 ?v4)) (exists ((?v5 A$) (?v6 A_c_tllist$)) (and (= ?v4 (tCons$d ?v5 ?v6)) (and (= (fun_app$a ?v2 ?v5) ?v0) (= (tmap$c ?v2 ?v3 ?v6) ?v1)))))) :named a42))
(assert (! (forall ((?v0 A$) (?v1 A_a_tllist$) (?v2 A_a_fun$) (?v3 A_a_fun$) (?v4 A_a_tllist$)) (= (= (tCons$e ?v0 ?v1) (tmap$d ?v2 ?v3 ?v4)) (exists ((?v5 A$) (?v6 A_a_tllist$)) (and (= ?v4 (tCons$e ?v5 ?v6)) (and (= (fun_app$a ?v2 ?v5) ?v0) (= (tmap$d ?v2 ?v3 ?v6) ?v1)))))) :named a43))
(assert (! (forall ((?v0 A$) (?v1 A_b_tllist$) (?v2 A_a_fun$) (?v3 D_b_fun$) (?v4 A_d_tllist$)) (= (= (tCons$ ?v0 ?v1) (tmap$b ?v2 ?v3 ?v4)) (exists ((?v5 A$) (?v6 A_d_tllist$)) (and (= ?v4 (tCons$c ?v5 ?v6)) (and (= (fun_app$a ?v2 ?v5) ?v0) (= (tmap$b ?v2 ?v3 ?v6) ?v1)))))) :named a44))
(assert (! (forall ((?v0 C$) (?v1 C_d_tllist$) (?v2 C_c_fun$) (?v3 D_d_fun$) (?v4 C_d_tllist$)) (= (= (tCons$a ?v0 ?v1) (tmap$f ?v2 ?v3 ?v4)) (exists ((?v5 C$) (?v6 C_d_tllist$)) (and (= ?v4 (tCons$a ?v5 ?v6)) (and (= (fun_app$b ?v2 ?v5) ?v0) (= (tmap$f ?v2 ?v3 ?v6) ?v1)))))) :named a45))
(assert (! (forall ((?v0 C$) (?v1 C_d_tllist$) (?v2 A_c_fun$) (?v3 B_d_fun$) (?v4 A_b_tllist$)) (= (= (tCons$a ?v0 ?v1) (tmap$e ?v2 ?v3 ?v4)) (exists ((?v5 A$) (?v6 A_b_tllist$)) (and (= ?v4 (tCons$ ?v5 ?v6)) (and (= (fun_app$c ?v2 ?v5) ?v0) (= (tmap$e ?v2 ?v3 ?v6) ?v1)))))) :named a46))
(assert (! (forall ((?v0 A$) (?v1 A_b_tllist$) (?v2 A_a_fun$) (?v3 B_b_fun$) (?v4 A_b_tllist$)) (= (= (tCons$ ?v0 ?v1) (tmap$g ?v2 ?v3 ?v4)) (exists ((?v5 A$) (?v6 A_b_tllist$)) (and (= ?v4 (tCons$ ?v5 ?v6)) (and (= (fun_app$a ?v2 ?v5) ?v0) (= (tmap$g ?v2 ?v3 ?v6) ?v1)))))) :named a47))
(assert (! (forall ((?v0 A$) (?v1 A_b_tllist$) (?v2 C_a_fun$) (?v3 D_b_fun$) (?v4 C_d_tllist$)) (= (= (tCons$ ?v0 ?v1) (tmap$ ?v2 ?v3 ?v4)) (exists ((?v5 C$) (?v6 C_d_tllist$)) (and (= ?v4 (tCons$a ?v5 ?v6)) (and (= (fun_app$d ?v2 ?v5) ?v0) (= (tmap$ ?v2 ?v3 ?v6) ?v1)))))) :named a48))
(assert (! (forall ((?v0 A$) (?v1 B_b_fun$) (?v2 A_a_fun$) (?v3 B_a_tllist$)) (= (= (tNil$b ?v0) (tmap$a ?v1 ?v2 ?v3)) (exists ((?v4 A$)) (and (= ?v3 (tNil$b ?v4)) (= (fun_app$a ?v2 ?v4) ?v0))))) :named a49))
(assert (! (forall ((?v0 B$) (?v1 A_a_fun$) (?v2 D_b_fun$) (?v3 A_d_tllist$)) (= (= (tNil$ ?v0) (tmap$b ?v1 ?v2 ?v3)) (exists ((?v4 D$)) (and (= ?v3 (tNil$c ?v4)) (= (fun_app$e ?v2 ?v4) ?v0))))) :named a50))
(assert (! (forall ((?v0 A$) (?v1 A_a_fun$) (?v2 C_a_fun$) (?v3 A_c_tllist$)) (= (= (tNil$e ?v0) (tmap$c ?v1 ?v2 ?v3)) (exists ((?v4 C$)) (and (= ?v3 (tNil$d ?v4)) (= (fun_app$d ?v2 ?v4) ?v0))))) :named a51))
(assert (! (forall ((?v0 A$) (?v1 A_a_fun$) (?v2 A_a_fun$) (?v3 A_a_tllist$)) (= (= (tNil$e ?v0) (tmap$d ?v1 ?v2 ?v3)) (exists ((?v4 A$)) (and (= ?v3 (tNil$e ?v4)) (= (fun_app$a ?v2 ?v4) ?v0))))) :named a52))
(assert (! (forall ((?v0 D$) (?v1 A_c_fun$) (?v2 B_d_fun$) (?v3 A_b_tllist$)) (= (= (tNil$a ?v0) (tmap$e ?v1 ?v2 ?v3)) (exists ((?v4 B$)) (and (= ?v3 (tNil$ ?v4)) (= (fun_app$f ?v2 ?v4) ?v0))))) :named a53))
(assert (! (forall ((?v0 D$) (?v1 C_c_fun$) (?v2 D_d_fun$) (?v3 C_d_tllist$)) (= (= (tNil$a ?v0) (tmap$f ?v1 ?v2 ?v3)) (exists ((?v4 D$)) (and (= ?v3 (tNil$a ?v4)) (= (fun_app$g ?v2 ?v4) ?v0))))) :named a54))
(assert (! (forall ((?v0 B$) (?v1 A_a_fun$) (?v2 B_b_fun$) (?v3 A_b_tllist$)) (= (= (tNil$ ?v0) (tmap$g ?v1 ?v2 ?v3)) (exists ((?v4 B$)) (and (= ?v3 (tNil$ ?v4)) (= (fun_app$ ?v2 ?v4) ?v0))))) :named a55))
(assert (! (forall ((?v0 B$) (?v1 C_a_fun$) (?v2 D_b_fun$) (?v3 C_d_tllist$)) (= (= (tNil$ ?v0) (tmap$ ?v1 ?v2 ?v3)) (exists ((?v4 D$)) (and (= ?v3 (tNil$a ?v4)) (= (fun_app$e ?v2 ?v4) ?v0))))) :named a56))
(assert (! (forall ((?v0 B_b_fun$) (?v1 A_a_fun$) (?v2 A$)) (! (= (tmap$a ?v0 ?v1 (tNil$b ?v2)) (tNil$b (fun_app$a ?v1 ?v2))) :pattern ((tmap$a ?v0 ?v1 (tNil$b ?v2))))) :named a57))
(assert (! (forall ((?v0 A_a_fun$) (?v1 D_b_fun$) (?v2 D$)) (! (= (tmap$b ?v0 ?v1 (tNil$c ?v2)) (tNil$ (fun_app$e ?v1 ?v2))) :pattern ((tmap$b ?v0 ?v1 (tNil$c ?v2))))) :named a58))
(assert (! (forall ((?v0 A_a_fun$) (?v1 C_a_fun$) (?v2 C$)) (! (= (tmap$c ?v0 ?v1 (tNil$d ?v2)) (tNil$e (fun_app$d ?v1 ?v2))) :pattern ((tmap$c ?v0 ?v1 (tNil$d ?v2))))) :named a59))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A$)) (! (= (tmap$d ?v0 ?v1 (tNil$e ?v2)) (tNil$e (fun_app$a ?v1 ?v2))) :pattern ((tmap$d ?v0 ?v1 (tNil$e ?v2))))) :named a60))
(assert (! (forall ((?v0 A_c_fun$) (?v1 B_d_fun$) (?v2 B$)) (! (= (tmap$e ?v0 ?v1 (tNil$ ?v2)) (tNil$a (fun_app$f ?v1 ?v2))) :pattern ((tmap$e ?v0 ?v1 (tNil$ ?v2))))) :named a61))
(assert (! (forall ((?v0 C_c_fun$) (?v1 D_d_fun$) (?v2 D$)) (! (= (tmap$f ?v0 ?v1 (tNil$a ?v2)) (tNil$a (fun_app$g ?v1 ?v2))) :pattern ((tmap$f ?v0 ?v1 (tNil$a ?v2))))) :named a62))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_b_fun$) (?v2 B$)) (! (= (tmap$g ?v0 ?v1 (tNil$ ?v2)) (tNil$ (fun_app$ ?v1 ?v2))) :pattern ((tmap$g ?v0 ?v1 (tNil$ ?v2))))) :named a63))
(assert (! (forall ((?v0 C_a_fun$) (?v1 D_b_fun$) (?v2 D$)) (! (= (tmap$ ?v0 ?v1 (tNil$a ?v2)) (tNil$ (fun_app$e ?v1 ?v2))) :pattern ((tmap$ ?v0 ?v1 (tNil$a ?v2))))) :named a64))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_b_bool_fun_fun$) (?v2 A_b_tllist$) (?v3 A_b_tllist$)) (=> (tllist_all2$ ?v0 ?v1 ?v2 ?v3) (= (tlength$ ?v2) (tlength$ ?v3)))) :named a65))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 B_d_bool_fun_fun$) (?v2 A_b_tllist$) (?v3 C_d_tllist$)) (=> (tllist_all2$a ?v0 ?v1 ?v2 ?v3) (= (tlength$ ?v2) (tlength$a ?v3)))) :named a66))
(assert (! (forall ((?v0 C_a_bool_fun_fun$) (?v1 D_b_bool_fun_fun$) (?v2 C_d_tllist$) (?v3 A_b_tllist$)) (=> (tllist_all2$b ?v0 ?v1 ?v2 ?v3) (= (tlength$a ?v2) (tlength$ ?v3)))) :named a67))
(assert (! (forall ((?v0 C_c_bool_fun_fun$) (?v1 D_d_bool_fun_fun$) (?v2 C_d_tllist$) (?v3 C_d_tllist$)) (=> (tllist_all2$c ?v0 ?v1 ?v2 ?v3) (= (tlength$a ?v2) (tlength$a ?v3)))) :named a68))
(assert (! (forall ((?v0 C_d_tllist$)) (= (tmap$f id$ id$a ?v0) ?v0)) :named a69))
(assert (! (forall ((?v0 A_b_tllist$)) (= (tmap$g id$b id$c ?v0) ?v0)) :named a70))
(assert (! (forall ((?v0 A_c_tllist$)) (= (tmap$h id$b id$ ?v0) ?v0)) :named a71))
(assert (! (forall ((?v0 A_d_tllist$)) (= (tmap$i id$b id$a ?v0) ?v0)) :named a72))
(assert (! (forall ((?v0 B_b_tllist$)) (= (tmap$j id$c id$c ?v0) ?v0)) :named a73))
(assert (! (forall ((?v0 B_c_tllist$)) (= (tmap$k id$c id$ ?v0) ?v0)) :named a74))
(assert (! (forall ((?v0 B_d_tllist$)) (= (tmap$l id$c id$a ?v0) ?v0)) :named a75))
(assert (! (forall ((?v0 C_a_tllist$)) (= (tmap$m id$ id$b ?v0) ?v0)) :named a76))
(assert (! (forall ((?v0 C_b_tllist$)) (= (tmap$n id$ id$c ?v0) ?v0)) :named a77))
(assert (! (forall ((?v0 C_c_tllist$)) (= (tmap$o id$ id$ ?v0) ?v0)) :named a78))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_b_fun$) (?v2 C_a_fun$) (?v3 D_b_fun$) (?v4 C_d_tllist$)) (= (tmap$g ?v0 ?v1 (tmap$ ?v2 ?v3 ?v4)) (tmap$ (fun_app$h (comp$ ?v0) ?v2) (fun_app$i (comp$a ?v1) ?v3) ?v4))) :named a79))
(assert (! (forall ((?v0 C_a_fun$) (?v1 D_b_fun$) (?v2 C_c_fun$) (?v3 D_d_fun$) (?v4 C_d_tllist$)) (= (tmap$ ?v0 ?v1 (tmap$f ?v2 ?v3 ?v4)) (tmap$ (fun_app$j (comp$b ?v0) ?v2) (fun_app$k (comp$c ?v1) ?v3) ?v4))) :named a80))
(assert (! (forall ((?v0 C_a_fun$) (?v1 C_a_fun$) (?v2 C_c_fun$) (?v3 C_c_fun$) (?v4 C_c_tllist$)) (= (tmap$p ?v0 ?v1 (tmap$o ?v2 ?v3 ?v4)) (tmap$p (fun_app$j (comp$b ?v0) ?v2) (fun_app$j (comp$b ?v1) ?v3) ?v4))) :named a81))
(assert (! (forall ((?v0 C_a_fun$) (?v1 A_a_fun$) (?v2 C_c_fun$) (?v3 C_a_fun$) (?v4 C_c_tllist$)) (= (tmap$q ?v0 ?v1 (tmap$r ?v2 ?v3 ?v4)) (tmap$p (fun_app$j (comp$b ?v0) ?v2) (fun_app$h (comp$ ?v1) ?v3) ?v4))) :named a82))
(assert (! (forall ((?v0 D_b_fun$) (?v1 C_a_fun$) (?v2 D_d_fun$) (?v3 C_c_fun$) (?v4 D_c_tllist$)) (= (tmap$s ?v0 ?v1 (tmap$t ?v2 ?v3 ?v4)) (tmap$s (fun_app$k (comp$c ?v0) ?v2) (fun_app$j (comp$b ?v1) ?v3) ?v4))) :named a83))
(assert (! (forall ((?v0 D_b_fun$) (?v1 D_b_fun$) (?v2 D_d_fun$) (?v3 D_d_fun$) (?v4 D_d_tllist$)) (= (tmap$u ?v0 ?v1 (tmap$v ?v2 ?v3 ?v4)) (tmap$u (fun_app$k (comp$c ?v0) ?v2) (fun_app$k (comp$c ?v1) ?v3) ?v4))) :named a84))
(assert (! (forall ((?v0 D_b_fun$) (?v1 A_a_fun$) (?v2 D_d_fun$) (?v3 C_a_fun$) (?v4 D_c_tllist$)) (= (tmap$w ?v0 ?v1 (tmap$x ?v2 ?v3 ?v4)) (tmap$s (fun_app$k (comp$c ?v0) ?v2) (fun_app$h (comp$ ?v1) ?v3) ?v4))) :named a85))
(assert (! (forall ((?v0 D_b_fun$) (?v1 B_b_fun$) (?v2 D_d_fun$) (?v3 D_b_fun$) (?v4 D_d_tllist$)) (= (tmap$y ?v0 ?v1 (tmap$z ?v2 ?v3 ?v4)) (tmap$u (fun_app$k (comp$c ?v0) ?v2) (fun_app$i (comp$a ?v1) ?v3) ?v4))) :named a86))
(assert (! (forall ((?v0 A_a_fun$) (?v1 C_a_fun$) (?v2 C_a_fun$) (?v3 C_c_fun$) (?v4 C_c_tllist$)) (= (tmap$c ?v0 ?v1 (tmap$aa ?v2 ?v3 ?v4)) (tmap$p (fun_app$h (comp$ ?v0) ?v2) (fun_app$j (comp$b ?v1) ?v3) ?v4))) :named a87))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 C_a_fun$) (?v3 C_a_fun$) (?v4 C_c_tllist$)) (= (tmap$d ?v0 ?v1 (tmap$p ?v2 ?v3 ?v4)) (tmap$p (fun_app$h (comp$ ?v0) ?v2) (fun_app$h (comp$ ?v1) ?v3) ?v4))) :named a88))
(assert (! (forall ((?v0 Nat$) (?v1 B_a_tllist$) (?v2 B_b_fun$) (?v3 A_a_fun$)) (=> (less$ (enat$ ?v0) (tlength$b ?v1)) (= (tnth$ (tmap$a ?v2 ?v3 ?v1) ?v0) (fun_app$ ?v2 (tnth$ ?v1 ?v0))))) :named a89))
(assert (! (forall ((?v0 Nat$) (?v1 A_d_tllist$) (?v2 A_a_fun$) (?v3 D_b_fun$)) (=> (less$ (enat$ ?v0) (tlength$c ?v1)) (= (tnth$a (tmap$b ?v2 ?v3 ?v1) ?v0) (fun_app$a ?v2 (tnth$b ?v1 ?v0))))) :named a90))
(assert (! (forall ((?v0 Nat$) (?v1 A_c_tllist$) (?v2 A_a_fun$) (?v3 C_a_fun$)) (=> (less$ (enat$ ?v0) (tlength$d ?v1)) (= (tnth$c (tmap$c ?v2 ?v3 ?v1) ?v0) (fun_app$a ?v2 (tnth$d ?v1 ?v0))))) :named a91))
(assert (! (forall ((?v0 Nat$) (?v1 A_a_tllist$) (?v2 A_a_fun$) (?v3 A_a_fun$)) (=> (less$ (enat$ ?v0) (tlength$e ?v1)) (= (tnth$c (tmap$d ?v2 ?v3 ?v1) ?v0) (fun_app$a ?v2 (tnth$c ?v1 ?v0))))) :named a92))
(assert (! (forall ((?v0 Nat$) (?v1 A_b_tllist$) (?v2 A_c_fun$) (?v3 B_d_fun$)) (=> (less$ (enat$ ?v0) (tlength$ ?v1)) (= (tnth$e (tmap$e ?v2 ?v3 ?v1) ?v0) (fun_app$c ?v2 (tnth$a ?v1 ?v0))))) :named a93))
(assert (! (forall ((?v0 Nat$) (?v1 C_d_tllist$) (?v2 C_c_fun$) (?v3 D_d_fun$)) (=> (less$ (enat$ ?v0) (tlength$a ?v1)) (= (tnth$e (tmap$f ?v2 ?v3 ?v1) ?v0) (fun_app$b ?v2 (tnth$e ?v1 ?v0))))) :named a94))
(assert (! (forall ((?v0 Nat$) (?v1 A_b_tllist$) (?v2 A_a_fun$) (?v3 B_b_fun$)) (=> (less$ (enat$ ?v0) (tlength$ ?v1)) (= (tnth$a (tmap$g ?v2 ?v3 ?v1) ?v0) (fun_app$a ?v2 (tnth$a ?v1 ?v0))))) :named a95))
(assert (! (forall ((?v0 Nat$) (?v1 C_d_tllist$) (?v2 C_a_fun$) (?v3 D_b_fun$)) (=> (less$ (enat$ ?v0) (tlength$a ?v1)) (= (tnth$a (tmap$ ?v2 ?v3 ?v1) ?v0) (fun_app$d ?v2 (tnth$e ?v1 ?v0))))) :named a96))
(assert (! (forall ((?v0 C$) (?v1 C_d_tllist$) (?v2 C$) (?v3 C_d_tllist$)) (= (= (tCons$a ?v0 ?v1) (tCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a97))
(assert (! (forall ((?v0 A$) (?v1 A_b_tllist$) (?v2 A$) (?v3 A_b_tllist$)) (= (= (tCons$ ?v0 ?v1) (tCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a98))
(assert (! (forall ((?v0 B$) (?v1 B$)) (= (= (tNil$ ?v0) (tNil$ ?v1)) (= ?v0 ?v1))) :named a99))
(assert (! (forall ((?v0 D$) (?v1 D$)) (= (= (tNil$a ?v0) (tNil$a ?v1)) (= ?v0 ?v1))) :named a100))
(assert (! (forall ((?v0 C_c_bool_fun_fun$) (?v1 D_d_bool_fun_fun$) (?v2 C$) (?v3 C_d_tllist$) (?v4 C$) (?v5 C_d_tllist$)) (! (= (tllist_all2$c ?v0 ?v1 (tCons$a ?v2 ?v3) (tCons$a ?v4 ?v5)) (and (fun_app$l (fun_app$m ?v0 ?v2) ?v4) (tllist_all2$c ?v0 ?v1 ?v3 ?v5))) :pattern ((tllist_all2$c ?v0 ?v1 (tCons$a ?v2 ?v3) (tCons$a ?v4 ?v5))))) :named a101))
(assert (! (forall ((?v0 C_a_bool_fun_fun$) (?v1 D_b_bool_fun_fun$) (?v2 C$) (?v3 C_d_tllist$) (?v4 A$) (?v5 A_b_tllist$)) (! (= (tllist_all2$b ?v0 ?v1 (tCons$a ?v2 ?v3) (tCons$ ?v4 ?v5)) (and (fun_app$n (fun_app$o ?v0 ?v2) ?v4) (tllist_all2$b ?v0 ?v1 ?v3 ?v5))) :pattern ((tllist_all2$b ?v0 ?v1 (tCons$a ?v2 ?v3) (tCons$ ?v4 ?v5))))) :named a102))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 B_d_bool_fun_fun$) (?v2 A$) (?v3 A_b_tllist$) (?v4 C$) (?v5 C_d_tllist$)) (! (= (tllist_all2$a ?v0 ?v1 (tCons$ ?v2 ?v3) (tCons$a ?v4 ?v5)) (and (fun_app$l (fun_app$p ?v0 ?v2) ?v4) (tllist_all2$a ?v0 ?v1 ?v3 ?v5))) :pattern ((tllist_all2$a ?v0 ?v1 (tCons$ ?v2 ?v3) (tCons$a ?v4 ?v5))))) :named a103))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_b_bool_fun_fun$) (?v2 A$) (?v3 A_b_tllist$) (?v4 A$) (?v5 A_b_tllist$)) (! (= (tllist_all2$ ?v0 ?v1 (tCons$ ?v2 ?v3) (tCons$ ?v4 ?v5)) (and (fun_app$n (fun_app$q ?v0 ?v2) ?v4) (tllist_all2$ ?v0 ?v1 ?v3 ?v5))) :pattern ((tllist_all2$ ?v0 ?v1 (tCons$ ?v2 ?v3) (tCons$ ?v4 ?v5))))) :named a104))
(assert (! (forall ((?v0 C_c_bool_fun_fun$) (?v1 D_d_bool_fun_fun$) (?v2 D$) (?v3 D$)) (! (= (tllist_all2$c ?v0 ?v1 (tNil$a ?v2) (tNil$a ?v3)) (fun_app$r (fun_app$s ?v1 ?v2) ?v3)) :pattern ((tllist_all2$c ?v0 ?v1 (tNil$a ?v2) (tNil$a ?v3))))) :named a105))
(assert (! (forall ((?v0 C_a_bool_fun_fun$) (?v1 D_b_bool_fun_fun$) (?v2 D$) (?v3 B$)) (! (= (tllist_all2$b ?v0 ?v1 (tNil$a ?v2) (tNil$ ?v3)) (fun_app$t (fun_app$u ?v1 ?v2) ?v3)) :pattern ((tllist_all2$b ?v0 ?v1 (tNil$a ?v2) (tNil$ ?v3))))) :named a106))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 B_d_bool_fun_fun$) (?v2 B$) (?v3 D$)) (! (= (tllist_all2$a ?v0 ?v1 (tNil$ ?v2) (tNil$a ?v3)) (fun_app$r (fun_app$v ?v1 ?v2) ?v3)) :pattern ((tllist_all2$a ?v0 ?v1 (tNil$ ?v2) (tNil$a ?v3))))) :named a107))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_b_bool_fun_fun$) (?v2 B$) (?v3 B$)) (! (= (tllist_all2$ ?v0 ?v1 (tNil$ ?v2) (tNil$ ?v3)) (fun_app$t (fun_app$w ?v1 ?v2) ?v3)) :pattern ((tllist_all2$ ?v0 ?v1 (tNil$ ?v2) (tNil$ ?v3))))) :named a108))
(assert (! (forall ((?v0 C_c_bool_fun_fun$) (?v1 D_d_bool_fun_fun$) (?v2 C$) (?v3 C_d_tllist$) (?v4 C_d_tllist$)) (= (tllist_all2$c ?v0 ?v1 (tCons$a ?v2 ?v3) ?v4) (exists ((?v5 C$) (?v6 C_d_tllist$)) (and (= ?v4 (tCons$a ?v5 ?v6)) (and (fun_app$l (fun_app$m ?v0 ?v2) ?v5) (tllist_all2$c ?v0 ?v1 ?v3 ?v6)))))) :named a109))
(assert (! (forall ((?v0 C_a_bool_fun_fun$) (?v1 D_b_bool_fun_fun$) (?v2 C$) (?v3 C_d_tllist$) (?v4 A_b_tllist$)) (= (tllist_all2$b ?v0 ?v1 (tCons$a ?v2 ?v3) ?v4) (exists ((?v5 A$) (?v6 A_b_tllist$)) (and (= ?v4 (tCons$ ?v5 ?v6)) (and (fun_app$n (fun_app$o ?v0 ?v2) ?v5) (tllist_all2$b ?v0 ?v1 ?v3 ?v6)))))) :named a110))
(assert (! (forall ((?v0 A_c_bool_fun_fun$) (?v1 B_d_bool_fun_fun$) (?v2 A$) (?v3 A_b_tllist$) (?v4 C_d_tllist$)) (= (tllist_all2$a ?v0 ?v1 (tCons$ ?v2 ?v3) ?v4) (exists ((?v5 C$) (?v6 C_d_tllist$)) (and (= ?v4 (tCons$a ?v5 ?v6)) (and (fun_app$l (fun_app$p ?v0 ?v2) ?v5) (tllist_all2$a ?v0 ?v1 ?v3 ?v6)))))) :named a111))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 B_b_bool_fun_fun$) (?v2 A$) (?v3 A_b_tllist$) (?v4 A_b_tllist$)) (= (tllist_all2$ ?v0 ?v1 (tCons$ ?v2 ?v3) ?v4) (exists ((?v5 A$) (?v6 A_b_tllist$)) (and (= ?v4 (tCons$ ?v5 ?v6)) (and (fun_app$n (fun_app$q ?v0 ?v2) ?v5) (tllist_all2$ ?v0 ?v1 ?v3 ?v6)))))) :named a112))
(check-sat)
;(get-unsat-core)
