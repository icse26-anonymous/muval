; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 505
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort Nat$ 0)
(declare-datatypes () ((A_b_prod$ (pair$ (fst$ A$) (snd$ B$)))))
(declare-codatatypes () ((A_b_prod_llist$ (lNil$) (lCons$ (lhd$ A_b_prod$) (ltl$ A_b_prod_llist$)))
  (A_llist$ (lNil$a) (lCons$a (lhd$a A$) (ltl$a A_llist$)))
  (B_llist$ (lNil$b) (lCons$b (lhd$b B$) (ltl$b B_llist$)))))
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))
  (A_a_prod$ (pair$a (fst$a A$) (snd$a A$)))))
(declare-codatatypes () ((A_a_prod_llist$ (lNil$c) (lCons$c (lhd$c A_a_prod$) (ltl$c A_a_prod_llist$)))))
(declare-datatypes () ((B_a_prod$ (pair$b (fst$b B$) (snd$b A$)))))
(declare-codatatypes () ((B_a_prod_llist$ (lNil$d) (lCons$d (lhd$d B_a_prod$) (ltl$d B_a_prod_llist$)))))
(declare-datatypes () ((B_b_prod$ (pair$c (fst$c B$) (snd$c B$)))))
(declare-codatatypes () ((B_b_prod_llist$ (lNil$e) (lCons$e (lhd$e B_b_prod$) (ltl$e B_b_prod_llist$)))))
(declare-datatypes () ((A_b_b_prod_prod$ (pair$d (fst$d A$) (snd$d B_b_prod$)))))
(declare-codatatypes () ((A_b_b_prod_prod_llist$ (lNil$f) (lCons$f (lhd$f A_b_b_prod_prod$) (ltl$f A_b_b_prod_prod_llist$)))))
(declare-datatypes () ((A_b_a_prod_prod$ (pair$e (fst$e A$) (snd$e B_a_prod$)))))
(declare-codatatypes () ((A_b_a_prod_prod_llist$ (lNil$g) (lCons$g (lhd$g A_b_a_prod_prod$) (ltl$g A_b_a_prod_prod_llist$)))))
(declare-datatypes () ((A_a_b_prod_prod$ (pair$f (fst$f A$) (snd$f A_b_prod$)))))
(declare-codatatypes () ((A_a_b_prod_prod_llist$ (lNil$h) (lCons$h (lhd$h A_a_b_prod_prod$) (ltl$h A_a_b_prod_prod_llist$)))))
(declare-datatypes () ((A_a_a_prod_prod$ (pair$g (fst$g A$) (snd$g A_a_prod$)))))
(declare-codatatypes () ((A_a_a_prod_prod_llist$ (lNil$i) (lCons$i (lhd$i A_a_a_prod_prod$) (ltl$i A_a_a_prod_prod_llist$)))))
(declare-datatypes () ((B_b_b_prod_prod$ (pair$h (fst$h B$) (snd$h B_b_prod$)))))
(declare-codatatypes () ((B_b_b_prod_prod_llist$ (lNil$j) (lCons$j (lhd$j B_b_b_prod_prod$) (ltl$j B_b_b_prod_prod_llist$)))))
(declare-datatypes () ((B_b_a_prod_prod$ (pair$i (fst$i B$) (snd$i B_a_prod$)))))
(declare-codatatypes () ((B_b_a_prod_prod_llist$ (lNil$k) (lCons$k (lhd$k B_b_a_prod_prod$) (ltl$k B_b_a_prod_prod_llist$)))))
(declare-datatypes () ((B_a_b_prod_prod$ (pair$j (fst$j B$) (snd$j A_b_prod$)))))
(declare-codatatypes () ((B_a_b_prod_prod_llist$ (lNil$l) (lCons$l (lhd$l B_a_b_prod_prod$) (ltl$l B_a_b_prod_prod_llist$)))))
(declare-datatypes () ((B_a_a_prod_prod$ (pair$k (fst$k B$) (snd$k A_a_prod$)))))
(declare-codatatypes () ((B_a_a_prod_prod_llist$ (lNil$m) (lCons$m (lhd$m B_a_a_prod_prod$) (ltl$m B_a_a_prod_prod_llist$)))))
(declare-datatypes () ((A_b_prod_a_prod$ (pair$l (fst$l A_b_prod$) (snd$l A$)))))
(declare-codatatypes () ((A_b_prod_a_prod_llist$ (lNil$n) (lCons$n (lhd$n A_b_prod_a_prod$) (ltl$n A_b_prod_a_prod_llist$)))))
(declare-datatypes () ((A_b_prod_b_prod$ (pair$m (fst$m A_b_prod$) (snd$m B$)))))
(declare-codatatypes () ((A_b_prod_b_prod_llist$ (lNil$o) (lCons$o (lhd$o A_b_prod_b_prod$) (ltl$o A_b_prod_b_prod_llist$)))))
(declare-datatypes () ((A_b_prod_a_b_prod_prod$ (pair$n (fst$n A_b_prod$) (snd$n A_b_prod$)))))
(declare-codatatypes () ((A_b_prod_a_b_prod_prod_llist$ (lNil$p) (lCons$p (lhd$p A_b_prod_a_b_prod_prod$) (ltl$p A_b_prod_a_b_prod_prod_llist$)))))
(declare-fun us$ () A_b_prod_llist$)
(declare-fun vs$ () A_b_prod_llist$)
(declare-fun xs$ () A_llist$)
(declare-fun ys$ () B_llist$)
(declare-fun min$ (Enat$ Enat$) Enat$)
(declare-fun lzip$ (A_llist$ B_llist$) A_b_prod_llist$)
(declare-fun ldrop$ (Enat$ A_llist$) A_llist$)
(declare-fun ltake$ (Enat$ A_llist$) A_llist$)
(declare-fun lzip$a (A_llist$ A_llist$) A_a_prod_llist$)
(declare-fun lzip$b (B_llist$ A_llist$) B_a_prod_llist$)
(declare-fun lzip$c (B_llist$ B_llist$) B_b_prod_llist$)
(declare-fun lzip$d (A_llist$ B_b_prod_llist$) A_b_b_prod_prod_llist$)
(declare-fun lzip$e (A_llist$ B_a_prod_llist$) A_b_a_prod_prod_llist$)
(declare-fun lzip$f (A_llist$ A_b_prod_llist$) A_a_b_prod_prod_llist$)
(declare-fun lzip$g (A_llist$ A_a_prod_llist$) A_a_a_prod_prod_llist$)
(declare-fun lzip$h (B_llist$ B_b_prod_llist$) B_b_b_prod_prod_llist$)
(declare-fun lzip$i (B_llist$ B_a_prod_llist$) B_b_a_prod_prod_llist$)
(declare-fun lzip$j (A_b_prod_llist$ A_llist$) A_b_prod_a_prod_llist$)
(declare-fun lzip$k (A_b_prod_llist$ B_llist$) A_b_prod_b_prod_llist$)
(declare-fun lzip$l (B_llist$ A_b_prod_llist$) B_a_b_prod_prod_llist$)
(declare-fun lzip$m (A_b_prod_llist$ A_b_prod_llist$) A_b_prod_a_b_prod_prod_llist$)
(declare-fun ldrop$a (Enat$ B_llist$) B_llist$)
(declare-fun ldrop$b (Enat$ A_b_prod_llist$) A_b_prod_llist$)
(declare-fun ldrop$c (Enat$ B_b_prod_llist$) B_b_prod_llist$)
(declare-fun ldrop$d (Enat$ B_a_prod_llist$) B_a_prod_llist$)
(declare-fun ldrop$e (Enat$ A_a_prod_llist$) A_a_prod_llist$)
(declare-fun ldrop$f (Enat$ B_a_b_prod_prod_llist$) B_a_b_prod_prod_llist$)
(declare-fun ldrop$g (Enat$ A_a_b_prod_prod_llist$) A_a_b_prod_prod_llist$)
(declare-fun ldrop$h (Enat$ B_a_a_prod_prod_llist$) B_a_a_prod_prod_llist$)
(declare-fun ldrop$i (Enat$ A_b_b_prod_prod_llist$) A_b_b_prod_prod_llist$)
(declare-fun ltake$a (Enat$ B_llist$) B_llist$)
(declare-fun ltake$b (Enat$ A_a_prod_llist$) A_a_prod_llist$)
(declare-fun ltake$c (Enat$ A_b_prod_llist$) A_b_prod_llist$)
(declare-fun ltake$d (Enat$ B_a_prod_llist$) B_a_prod_llist$)
(declare-fun ltake$e (Enat$ B_b_prod_llist$) B_b_prod_llist$)
(declare-fun ltake$f (Enat$ A_b_b_prod_prod_llist$) A_b_b_prod_prod_llist$)
(declare-fun ltake$g (Enat$ A_b_a_prod_prod_llist$) A_b_a_prod_prod_llist$)
(declare-fun ltake$h (Enat$ A_a_b_prod_prod_llist$) A_a_b_prod_prod_llist$)
(declare-fun ltake$i (Enat$ A_a_a_prod_prod_llist$) A_a_a_prod_prod_llist$)
(declare-fun ltake$j (Enat$ B_b_b_prod_prod_llist$) B_b_b_prod_prod_llist$)
(declare-fun ltake$k (Enat$ B_b_a_prod_prod_llist$) B_b_a_prod_prod_llist$)
(declare-fun ltake$l (Enat$ B_a_b_prod_prod_llist$) B_a_b_prod_prod_llist$)
(declare-fun ltake$m (Enat$ B_a_a_prod_prod_llist$) B_a_a_prod_prod_llist$)
(declare-fun lappend$ (A_b_prod_llist$ A_b_prod_llist$) A_b_prod_llist$)
(declare-fun less_eq$ (Enat$ Enat$) Bool)
(declare-fun llength$ (A_b_prod_llist$) Enat$)
(declare-fun lappend$a (A_llist$ A_llist$) A_llist$)
(declare-fun lappend$b (B_llist$ B_llist$) B_llist$)
(declare-fun lappend$c (B_b_prod_llist$ B_b_prod_llist$) B_b_prod_llist$)
(declare-fun lappend$d (B_a_prod_llist$ B_a_prod_llist$) B_a_prod_llist$)
(declare-fun lappend$e (A_a_prod_llist$ A_a_prod_llist$) A_a_prod_llist$)
(declare-fun lappend$f (B_a_b_prod_prod_llist$ B_a_b_prod_prod_llist$) B_a_b_prod_prod_llist$)
(declare-fun lappend$g (A_a_b_prod_prod_llist$ A_a_b_prod_prod_llist$) A_a_b_prod_prod_llist$)
(declare-fun lappend$h (B_a_a_prod_prod_llist$ B_a_a_prod_prod_llist$) B_a_a_prod_prod_llist$)
(declare-fun lappend$i (A_b_b_prod_prod_llist$ A_b_b_prod_prod_llist$) A_b_b_prod_prod_llist$)
(declare-fun lappend$j (A_b_prod_a_prod_llist$ A_b_prod_a_prod_llist$) A_b_prod_a_prod_llist$)
(declare-fun lappend$k (A_b_prod_b_prod_llist$ A_b_prod_b_prod_llist$) A_b_prod_b_prod_llist$)
(declare-fun lappend$l (A_b_prod_a_b_prod_prod_llist$ A_b_prod_a_b_prod_prod_llist$) A_b_prod_a_b_prod_prod_llist$)
(declare-fun llength$a (A_llist$) Enat$)
(declare-fun llength$b (B_llist$) Enat$)
(declare-fun llength$c (B_b_prod_llist$) Enat$)
(declare-fun llength$d (B_a_prod_llist$) Enat$)
(declare-fun llength$e (A_a_prod_llist$) Enat$)
(declare-fun llength$f (B_a_b_prod_prod_llist$) Enat$)
(declare-fun llength$g (A_a_b_prod_prod_llist$) Enat$)
(declare-fun llength$h (B_a_a_prod_prod_llist$) Enat$)
(declare-fun llength$i (A_b_b_prod_prod_llist$) Enat$)
(declare-fun llength$j (A_b_prod_a_prod_llist$) Enat$)
(declare-fun llength$k (A_b_prod_b_prod_llist$) Enat$)
(declare-fun llength$l (A_b_prod_a_b_prod_prod_llist$) Enat$)
(assert (! (not (= us$ (lzip$ (ltake$ (llength$ us$) xs$) (ltake$a (llength$ us$) ys$)))) :named a0))
(assert (! (less_eq$ (llength$ us$) (llength$a xs$)) :named a1))
(assert (! (less_eq$ (llength$ us$) (llength$b ys$)) :named a2))
(assert (! (= (lzip$ xs$ ys$) (lappend$ us$ vs$)) :named a3))
(assert (! (= (lappend$ us$ vs$) (lappend$ (lzip$ (ltake$ (llength$ us$) xs$) (ltake$a (llength$ us$) ys$)) (lzip$ (ldrop$ (llength$ us$) xs$) (ldrop$a (llength$ us$) ys$)))) :named a4))
(assert (! (= (llength$ (lzip$ xs$ ys$)) (llength$ (lappend$ us$ vs$))) :named a5))
(assert (! (= (llength$a (ltake$ (llength$ us$) xs$)) (llength$b (ltake$a (llength$ us$) ys$))) :named a6))
(assert (! (forall ((?v0 Enat$) (?v1 A_llist$) (?v2 A_llist$)) (= (ltake$b ?v0 (lzip$a ?v1 ?v2)) (lzip$a (ltake$ ?v0 ?v1) (ltake$ ?v0 ?v2)))) :named a7))
(assert (! (forall ((?v0 Enat$) (?v1 A_llist$) (?v2 B_llist$)) (= (ltake$c ?v0 (lzip$ ?v1 ?v2)) (lzip$ (ltake$ ?v0 ?v1) (ltake$a ?v0 ?v2)))) :named a8))
(assert (! (forall ((?v0 Enat$) (?v1 B_llist$) (?v2 A_llist$)) (= (ltake$d ?v0 (lzip$b ?v1 ?v2)) (lzip$b (ltake$a ?v0 ?v1) (ltake$ ?v0 ?v2)))) :named a9))
(assert (! (forall ((?v0 Enat$) (?v1 B_llist$) (?v2 B_llist$)) (= (ltake$e ?v0 (lzip$c ?v1 ?v2)) (lzip$c (ltake$a ?v0 ?v1) (ltake$a ?v0 ?v2)))) :named a10))
(assert (! (forall ((?v0 Enat$) (?v1 A_llist$) (?v2 B_b_prod_llist$)) (= (ltake$f ?v0 (lzip$d ?v1 ?v2)) (lzip$d (ltake$ ?v0 ?v1) (ltake$e ?v0 ?v2)))) :named a11))
(assert (! (forall ((?v0 Enat$) (?v1 A_llist$) (?v2 B_a_prod_llist$)) (= (ltake$g ?v0 (lzip$e ?v1 ?v2)) (lzip$e (ltake$ ?v0 ?v1) (ltake$d ?v0 ?v2)))) :named a12))
(assert (! (forall ((?v0 Enat$) (?v1 A_llist$) (?v2 A_b_prod_llist$)) (= (ltake$h ?v0 (lzip$f ?v1 ?v2)) (lzip$f (ltake$ ?v0 ?v1) (ltake$c ?v0 ?v2)))) :named a13))
(assert (! (forall ((?v0 Enat$) (?v1 A_llist$) (?v2 A_a_prod_llist$)) (= (ltake$i ?v0 (lzip$g ?v1 ?v2)) (lzip$g (ltake$ ?v0 ?v1) (ltake$b ?v0 ?v2)))) :named a14))
(assert (! (forall ((?v0 Enat$) (?v1 B_llist$) (?v2 B_b_prod_llist$)) (= (ltake$j ?v0 (lzip$h ?v1 ?v2)) (lzip$h (ltake$a ?v0 ?v1) (ltake$e ?v0 ?v2)))) :named a15))
(assert (! (forall ((?v0 Enat$) (?v1 B_llist$) (?v2 B_a_prod_llist$)) (= (ltake$k ?v0 (lzip$i ?v1 ?v2)) (lzip$i (ltake$a ?v0 ?v1) (ltake$d ?v0 ?v2)))) :named a16))
(assert (! (forall ((?v0 A_llist$) (?v1 Enat$)) (! (=> (less_eq$ (llength$a ?v0) ?v1) (= (ltake$ ?v1 ?v0) ?v0)) :pattern ((ltake$ ?v1 ?v0)))) :named a17))
(assert (! (forall ((?v0 B_llist$) (?v1 Enat$)) (! (=> (less_eq$ (llength$b ?v0) ?v1) (= (ltake$a ?v1 ?v0) ?v0)) :pattern ((ltake$a ?v1 ?v0)))) :named a18))
(assert (! (forall ((?v0 A_b_prod_llist$) (?v1 Enat$)) (! (=> (less_eq$ (llength$ ?v0) ?v1) (= (ltake$c ?v1 ?v0) ?v0)) :pattern ((ltake$c ?v1 ?v0)))) :named a19))
(assert (! (forall ((?v0 B_b_prod_llist$) (?v1 Enat$)) (! (=> (less_eq$ (llength$c ?v0) ?v1) (= (ltake$e ?v1 ?v0) ?v0)) :pattern ((ltake$e ?v1 ?v0)))) :named a20))
(assert (! (forall ((?v0 B_a_prod_llist$) (?v1 Enat$)) (! (=> (less_eq$ (llength$d ?v0) ?v1) (= (ltake$d ?v1 ?v0) ?v0)) :pattern ((ltake$d ?v1 ?v0)))) :named a21))
(assert (! (forall ((?v0 A_a_prod_llist$) (?v1 Enat$)) (! (=> (less_eq$ (llength$e ?v0) ?v1) (= (ltake$b ?v1 ?v0) ?v0)) :pattern ((ltake$b ?v1 ?v0)))) :named a22))
(assert (! (forall ((?v0 B_a_b_prod_prod_llist$) (?v1 Enat$)) (! (=> (less_eq$ (llength$f ?v0) ?v1) (= (ltake$l ?v1 ?v0) ?v0)) :pattern ((ltake$l ?v1 ?v0)))) :named a23))
(assert (! (forall ((?v0 A_a_b_prod_prod_llist$) (?v1 Enat$)) (! (=> (less_eq$ (llength$g ?v0) ?v1) (= (ltake$h ?v1 ?v0) ?v0)) :pattern ((ltake$h ?v1 ?v0)))) :named a24))
(assert (! (forall ((?v0 B_a_a_prod_prod_llist$) (?v1 Enat$)) (! (=> (less_eq$ (llength$h ?v0) ?v1) (= (ltake$m ?v1 ?v0) ?v0)) :pattern ((ltake$m ?v1 ?v0)))) :named a25))
(assert (! (forall ((?v0 A_b_b_prod_prod_llist$) (?v1 Enat$)) (! (=> (less_eq$ (llength$i ?v0) ?v1) (= (ltake$f ?v1 ?v0) ?v0)) :pattern ((ltake$f ?v1 ?v0)))) :named a26))
(assert (! (= xs$ (lappend$a (ltake$ (llength$ us$) xs$) (ldrop$ (llength$ us$) xs$))) :named a27))
(assert (! (= ys$ (lappend$b (ltake$a (llength$ us$) ys$) (ldrop$a (llength$ us$) ys$))) :named a28))
(assert (! (forall ((?v0 Enat$) (?v1 A_llist$) (?v2 A_llist$) (?v3 Enat$)) (=> (and (= (ltake$ ?v0 ?v1) (ltake$ ?v0 ?v2)) (less_eq$ ?v3 ?v0)) (= (ltake$ ?v3 ?v1) (ltake$ ?v3 ?v2)))) :named a29))
(assert (! (forall ((?v0 Enat$) (?v1 B_llist$) (?v2 B_llist$) (?v3 Enat$)) (=> (and (= (ltake$a ?v0 ?v1) (ltake$a ?v0 ?v2)) (less_eq$ ?v3 ?v0)) (= (ltake$a ?v3 ?v1) (ltake$a ?v3 ?v2)))) :named a30))
(assert (! (forall ((?v0 Enat$) (?v1 B_b_prod_llist$) (?v2 B_b_prod_llist$) (?v3 Enat$)) (=> (and (= (ltake$e ?v0 ?v1) (ltake$e ?v0 ?v2)) (less_eq$ ?v3 ?v0)) (= (ltake$e ?v3 ?v1) (ltake$e ?v3 ?v2)))) :named a31))
(assert (! (forall ((?v0 Enat$) (?v1 B_a_prod_llist$) (?v2 B_a_prod_llist$) (?v3 Enat$)) (=> (and (= (ltake$d ?v0 ?v1) (ltake$d ?v0 ?v2)) (less_eq$ ?v3 ?v0)) (= (ltake$d ?v3 ?v1) (ltake$d ?v3 ?v2)))) :named a32))
(assert (! (forall ((?v0 Enat$) (?v1 A_b_prod_llist$) (?v2 A_b_prod_llist$) (?v3 Enat$)) (=> (and (= (ltake$c ?v0 ?v1) (ltake$c ?v0 ?v2)) (less_eq$ ?v3 ?v0)) (= (ltake$c ?v3 ?v1) (ltake$c ?v3 ?v2)))) :named a33))
(assert (! (forall ((?v0 Enat$) (?v1 A_a_prod_llist$) (?v2 A_a_prod_llist$) (?v3 Enat$)) (=> (and (= (ltake$b ?v0 ?v1) (ltake$b ?v0 ?v2)) (less_eq$ ?v3 ?v0)) (= (ltake$b ?v3 ?v1) (ltake$b ?v3 ?v2)))) :named a34))
(assert (! (forall ((?v0 Enat$) (?v1 B_a_a_prod_prod_llist$) (?v2 B_a_a_prod_prod_llist$) (?v3 Enat$)) (=> (and (= (ltake$m ?v0 ?v1) (ltake$m ?v0 ?v2)) (less_eq$ ?v3 ?v0)) (= (ltake$m ?v3 ?v1) (ltake$m ?v3 ?v2)))) :named a35))
(assert (! (forall ((?v0 Enat$) (?v1 A_b_b_prod_prod_llist$) (?v2 A_b_b_prod_prod_llist$) (?v3 Enat$)) (=> (and (= (ltake$f ?v0 ?v1) (ltake$f ?v0 ?v2)) (less_eq$ ?v3 ?v0)) (= (ltake$f ?v3 ?v1) (ltake$f ?v3 ?v2)))) :named a36))
(assert (! (forall ((?v0 Enat$) (?v1 A_b_a_prod_prod_llist$) (?v2 A_b_a_prod_prod_llist$) (?v3 Enat$)) (=> (and (= (ltake$g ?v0 ?v1) (ltake$g ?v0 ?v2)) (less_eq$ ?v3 ?v0)) (= (ltake$g ?v3 ?v1) (ltake$g ?v3 ?v2)))) :named a37))
(assert (! (forall ((?v0 Enat$) (?v1 A_a_b_prod_prod_llist$) (?v2 A_a_b_prod_prod_llist$) (?v3 Enat$)) (=> (and (= (ltake$h ?v0 ?v1) (ltake$h ?v0 ?v2)) (less_eq$ ?v3 ?v0)) (= (ltake$h ?v3 ?v1) (ltake$h ?v3 ?v2)))) :named a38))
(assert (! (less_eq$ (llength$ us$) (min$ (llength$a xs$) (llength$b ys$))) :named a39))
(assert (! (= (lappend$ us$ vs$) (lzip$ (lappend$a (ltake$ (llength$ us$) xs$) (ldrop$ (llength$ us$) xs$)) (lappend$b (ltake$a (llength$ us$) ys$) (ldrop$a (llength$ us$) ys$)))) :named a40))
(assert (! (forall ((?v0 Enat$) (?v1 A_llist$) (?v2 A_llist$)) (=> (less_eq$ ?v0 (llength$a ?v1)) (= (ltake$ ?v0 (lappend$a ?v1 ?v2)) (ltake$ ?v0 ?v1)))) :named a41))
(assert (! (forall ((?v0 Enat$) (?v1 B_llist$) (?v2 B_llist$)) (=> (less_eq$ ?v0 (llength$b ?v1)) (= (ltake$a ?v0 (lappend$b ?v1 ?v2)) (ltake$a ?v0 ?v1)))) :named a42))
(assert (! (forall ((?v0 Enat$) (?v1 A_b_prod_llist$) (?v2 A_b_prod_llist$)) (=> (less_eq$ ?v0 (llength$ ?v1)) (= (ltake$c ?v0 (lappend$ ?v1 ?v2)) (ltake$c ?v0 ?v1)))) :named a43))
(assert (! (forall ((?v0 Enat$) (?v1 B_b_prod_llist$) (?v2 B_b_prod_llist$)) (=> (less_eq$ ?v0 (llength$c ?v1)) (= (ltake$e ?v0 (lappend$c ?v1 ?v2)) (ltake$e ?v0 ?v1)))) :named a44))
(assert (! (forall ((?v0 Enat$) (?v1 B_a_prod_llist$) (?v2 B_a_prod_llist$)) (=> (less_eq$ ?v0 (llength$d ?v1)) (= (ltake$d ?v0 (lappend$d ?v1 ?v2)) (ltake$d ?v0 ?v1)))) :named a45))
(assert (! (forall ((?v0 Enat$) (?v1 A_a_prod_llist$) (?v2 A_a_prod_llist$)) (=> (less_eq$ ?v0 (llength$e ?v1)) (= (ltake$b ?v0 (lappend$e ?v1 ?v2)) (ltake$b ?v0 ?v1)))) :named a46))
(assert (! (forall ((?v0 Enat$) (?v1 B_a_b_prod_prod_llist$) (?v2 B_a_b_prod_prod_llist$)) (=> (less_eq$ ?v0 (llength$f ?v1)) (= (ltake$l ?v0 (lappend$f ?v1 ?v2)) (ltake$l ?v0 ?v1)))) :named a47))
(assert (! (forall ((?v0 Enat$) (?v1 A_a_b_prod_prod_llist$) (?v2 A_a_b_prod_prod_llist$)) (=> (less_eq$ ?v0 (llength$g ?v1)) (= (ltake$h ?v0 (lappend$g ?v1 ?v2)) (ltake$h ?v0 ?v1)))) :named a48))
(assert (! (forall ((?v0 Enat$) (?v1 B_a_a_prod_prod_llist$) (?v2 B_a_a_prod_prod_llist$)) (=> (less_eq$ ?v0 (llength$h ?v1)) (= (ltake$m ?v0 (lappend$h ?v1 ?v2)) (ltake$m ?v0 ?v1)))) :named a49))
(assert (! (forall ((?v0 Enat$) (?v1 A_b_b_prod_prod_llist$) (?v2 A_b_b_prod_prod_llist$)) (=> (less_eq$ ?v0 (llength$i ?v1)) (= (ltake$f ?v0 (lappend$i ?v1 ?v2)) (ltake$f ?v0 ?v1)))) :named a50))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_llist$)) (=> (= (llength$a ?v0) (llength$a ?v1)) (= (lzip$a (lappend$a ?v0 ?v2) (lappend$a ?v1 ?v3)) (lappend$e (lzip$a ?v0 ?v1) (lzip$a ?v2 ?v3))))) :named a51))
(assert (! (forall ((?v0 A_llist$) (?v1 B_llist$) (?v2 A_llist$) (?v3 B_llist$)) (=> (= (llength$a ?v0) (llength$b ?v1)) (= (lzip$ (lappend$a ?v0 ?v2) (lappend$b ?v1 ?v3)) (lappend$ (lzip$ ?v0 ?v1) (lzip$ ?v2 ?v3))))) :named a52))
(assert (! (forall ((?v0 B_llist$) (?v1 A_llist$) (?v2 B_llist$) (?v3 A_llist$)) (=> (= (llength$b ?v0) (llength$a ?v1)) (= (lzip$b (lappend$b ?v0 ?v2) (lappend$a ?v1 ?v3)) (lappend$d (lzip$b ?v0 ?v1) (lzip$b ?v2 ?v3))))) :named a53))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$) (?v2 B_llist$) (?v3 B_llist$)) (=> (= (llength$b ?v0) (llength$b ?v1)) (= (lzip$c (lappend$b ?v0 ?v2) (lappend$b ?v1 ?v3)) (lappend$c (lzip$c ?v0 ?v1) (lzip$c ?v2 ?v3))))) :named a54))
(assert (! (forall ((?v0 A_b_prod_llist$) (?v1 A_llist$) (?v2 A_b_prod_llist$) (?v3 A_llist$)) (=> (= (llength$ ?v0) (llength$a ?v1)) (= (lzip$j (lappend$ ?v0 ?v2) (lappend$a ?v1 ?v3)) (lappend$j (lzip$j ?v0 ?v1) (lzip$j ?v2 ?v3))))) :named a55))
(assert (! (forall ((?v0 A_b_prod_llist$) (?v1 B_llist$) (?v2 A_b_prod_llist$) (?v3 B_llist$)) (=> (= (llength$ ?v0) (llength$b ?v1)) (= (lzip$k (lappend$ ?v0 ?v2) (lappend$b ?v1 ?v3)) (lappend$k (lzip$k ?v0 ?v1) (lzip$k ?v2 ?v3))))) :named a56))
(assert (! (forall ((?v0 A_llist$) (?v1 A_b_prod_llist$) (?v2 A_llist$) (?v3 A_b_prod_llist$)) (=> (= (llength$a ?v0) (llength$ ?v1)) (= (lzip$f (lappend$a ?v0 ?v2) (lappend$ ?v1 ?v3)) (lappend$g (lzip$f ?v0 ?v1) (lzip$f ?v2 ?v3))))) :named a57))
(assert (! (forall ((?v0 B_llist$) (?v1 A_b_prod_llist$) (?v2 B_llist$) (?v3 A_b_prod_llist$)) (=> (= (llength$b ?v0) (llength$ ?v1)) (= (lzip$l (lappend$b ?v0 ?v2) (lappend$ ?v1 ?v3)) (lappend$f (lzip$l ?v0 ?v1) (lzip$l ?v2 ?v3))))) :named a58))
(assert (! (forall ((?v0 A_b_prod_llist$) (?v1 A_b_prod_llist$) (?v2 A_b_prod_llist$) (?v3 A_b_prod_llist$)) (=> (= (llength$ ?v0) (llength$ ?v1)) (= (lzip$m (lappend$ ?v0 ?v2) (lappend$ ?v1 ?v3)) (lappend$l (lzip$m ?v0 ?v1) (lzip$m ?v2 ?v3))))) :named a59))
(assert (! (forall ((?v0 A_llist$) (?v1 B_b_prod_llist$) (?v2 A_llist$) (?v3 B_b_prod_llist$)) (=> (= (llength$a ?v0) (llength$c ?v1)) (= (lzip$d (lappend$a ?v0 ?v2) (lappend$c ?v1 ?v3)) (lappend$i (lzip$d ?v0 ?v1) (lzip$d ?v2 ?v3))))) :named a60))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (llength$e (lzip$a ?v0 ?v1)) (min$ (llength$a ?v0) (llength$a ?v1)))) :named a61))
(assert (! (forall ((?v0 B_llist$) (?v1 A_llist$)) (= (llength$d (lzip$b ?v0 ?v1)) (min$ (llength$b ?v0) (llength$a ?v1)))) :named a62))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (= (llength$c (lzip$c ?v0 ?v1)) (min$ (llength$b ?v0) (llength$b ?v1)))) :named a63))
(assert (! (forall ((?v0 A_llist$) (?v1 B_llist$)) (= (llength$ (lzip$ ?v0 ?v1)) (min$ (llength$a ?v0) (llength$b ?v1)))) :named a64))
(assert (! (forall ((?v0 A_b_prod_llist$) (?v1 A_llist$)) (= (llength$j (lzip$j ?v0 ?v1)) (min$ (llength$ ?v0) (llength$a ?v1)))) :named a65))
(assert (! (forall ((?v0 A_b_prod_llist$) (?v1 B_llist$)) (= (llength$k (lzip$k ?v0 ?v1)) (min$ (llength$ ?v0) (llength$b ?v1)))) :named a66))
(assert (! (forall ((?v0 A_llist$) (?v1 A_b_prod_llist$)) (= (llength$g (lzip$f ?v0 ?v1)) (min$ (llength$a ?v0) (llength$ ?v1)))) :named a67))
(assert (! (forall ((?v0 B_llist$) (?v1 A_b_prod_llist$)) (= (llength$f (lzip$l ?v0 ?v1)) (min$ (llength$b ?v0) (llength$ ?v1)))) :named a68))
(assert (! (forall ((?v0 A_b_prod_llist$) (?v1 A_b_prod_llist$)) (= (llength$l (lzip$m ?v0 ?v1)) (min$ (llength$ ?v0) (llength$ ?v1)))) :named a69))
(assert (! (forall ((?v0 A_llist$) (?v1 B_b_prod_llist$)) (= (llength$i (lzip$d ?v0 ?v1)) (min$ (llength$a ?v0) (llength$c ?v1)))) :named a70))
(assert (! (forall ((?v0 Enat$) (?v1 A_llist$)) (= (lappend$a (ltake$ ?v0 ?v1) (ldrop$ ?v0 ?v1)) ?v1)) :named a71))
(assert (! (forall ((?v0 Enat$) (?v1 B_llist$)) (= (lappend$b (ltake$a ?v0 ?v1) (ldrop$a ?v0 ?v1)) ?v1)) :named a72))
(assert (! (forall ((?v0 Enat$) (?v1 A_b_prod_llist$)) (= (lappend$ (ltake$c ?v0 ?v1) (ldrop$b ?v0 ?v1)) ?v1)) :named a73))
(assert (! (forall ((?v0 Enat$) (?v1 B_b_prod_llist$)) (= (lappend$c (ltake$e ?v0 ?v1) (ldrop$c ?v0 ?v1)) ?v1)) :named a74))
(assert (! (forall ((?v0 Enat$) (?v1 B_a_prod_llist$)) (= (lappend$d (ltake$d ?v0 ?v1) (ldrop$d ?v0 ?v1)) ?v1)) :named a75))
(assert (! (forall ((?v0 Enat$) (?v1 A_a_prod_llist$)) (= (lappend$e (ltake$b ?v0 ?v1) (ldrop$e ?v0 ?v1)) ?v1)) :named a76))
(assert (! (forall ((?v0 Enat$) (?v1 B_a_b_prod_prod_llist$)) (= (lappend$f (ltake$l ?v0 ?v1) (ldrop$f ?v0 ?v1)) ?v1)) :named a77))
(assert (! (forall ((?v0 Enat$) (?v1 A_a_b_prod_prod_llist$)) (= (lappend$g (ltake$h ?v0 ?v1) (ldrop$g ?v0 ?v1)) ?v1)) :named a78))
(assert (! (forall ((?v0 Enat$) (?v1 B_a_a_prod_prod_llist$)) (= (lappend$h (ltake$m ?v0 ?v1) (ldrop$h ?v0 ?v1)) ?v1)) :named a79))
(assert (! (forall ((?v0 Enat$) (?v1 A_b_b_prod_prod_llist$)) (= (lappend$i (ltake$f ?v0 ?v1) (ldrop$i ?v0 ?v1)) ?v1)) :named a80))
(check-sat)
;(get-unsat-core)
