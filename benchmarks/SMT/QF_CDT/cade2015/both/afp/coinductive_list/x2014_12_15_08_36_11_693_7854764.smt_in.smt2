; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 509
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort Nat$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_b_fun$ 0)
(declare-sort B_a_fun$ 0)
(declare-sort B_b_fun$ 0)
(declare-sort A_nat_fun$ 0)
(declare-sort B_nat_fun$ 0)
(declare-sort Nat_a_fun$ 0)
(declare-sort Nat_b_fun$ 0)
(declare-sort Nat_nat_fun$ 0)
(declare-sort A_b_prod_b_fun$ 0)
(declare-sort Nat_a_b_prod_fun$ 0)
(declare-sort Nat_b_a_prod_fun$ 0)
(declare-sort Nat_b_b_prod_fun$ 0)
(declare-sort Nat_a_b_prod_a_prod_fun$ 0)
(declare-sort Nat_b_a_b_prod_prod_fun$ 0)
(declare-sort A_list_b_a_prod_list_fun$ 0)
(declare-sort B_list_a_b_prod_list_fun$ 0)
(declare-sort B_list_b_b_prod_list_fun$ 0)
(declare-sort A_list_a_b_prod_a_prod_list_fun$ 0)
(declare-sort B_list_a_b_prod_b_prod_list_fun$ 0)
(declare-sort A_b_prod_list_b_a_b_prod_prod_list_fun$ 0)
(declare-datatypes () ((A_b_prod$ (pair$ (fst$ A$) (snd$ B$)))))
(declare-codatatypes () ((A_b_prod_llist$ (lNil$) (lCons$ (lhd$ A_b_prod$) (ltl$ A_b_prod_llist$)))
  (A_llist$ (lNil$a) (lCons$a (lhd$a A$) (ltl$a A_llist$)))
  (B_llist$ (lNil$b) (lCons$b (lhd$b B$) (ltl$b B_llist$)))))
(declare-datatypes () ((B_list$ (nil$) (cons$ (hd$ B$) (tl$ B_list$)))
  (A_b_prod_list$ (nil$a) (cons$a (hd$a A_b_prod$) (tl$a A_b_prod_list$)))
  (A_list$ (nil$b) (cons$b (hd$b A$) (tl$b A_list$)))
  (Nat_list$ (nil$c) (cons$c (hd$c Nat$) (tl$c Nat_list$)))))
(declare-codatatypes () ((Nat_llist$ (lNil$c) (lCons$c (lhd$c Nat$) (ltl$c Nat_llist$)))))
(declare-datatypes () ((A_b_prod_a_prod$ (pair$a (fst$a A_b_prod$) (snd$a A$)))
  (A_b_prod_a_prod_list$ (nil$d) (cons$d (hd$d A_b_prod_a_prod$) (tl$d A_b_prod_a_prod_list$)))))
(declare-codatatypes () ((A_b_prod_a_prod_llist$ (lNil$d) (lCons$d (lhd$d A_b_prod_a_prod$) (ltl$d A_b_prod_a_prod_llist$)))))
(declare-datatypes () ((B_a_b_prod_prod$ (pair$b (fst$b B$) (snd$b A_b_prod$)))
  (B_a_b_prod_prod_list$ (nil$e) (cons$e (hd$e B_a_b_prod_prod$) (tl$e B_a_b_prod_prod_list$)))))
(declare-codatatypes () ((B_a_b_prod_prod_llist$ (lNil$e) (lCons$e (lhd$e B_a_b_prod_prod$) (ltl$e B_a_b_prod_prod_llist$)))))
(declare-datatypes () ((B_b_prod$ (pair$c (fst$c B$) (snd$c B$)))
  (B_b_prod_list$ (nil$f) (cons$f (hd$f B_b_prod$) (tl$f B_b_prod_list$)))))
(declare-codatatypes () ((B_b_prod_llist$ (lNil$f) (lCons$f (lhd$f B_b_prod$) (ltl$f B_b_prod_llist$)))))
(declare-datatypes () ((B_a_prod$ (pair$d (fst$d B$) (snd$d A$)))
  (B_a_prod_list$ (nil$g) (cons$g (hd$g B_a_prod$) (tl$g B_a_prod_list$)))))
(declare-codatatypes () ((B_a_prod_llist$ (lNil$g) (lCons$g (lhd$g B_a_prod$) (ltl$g B_a_prod_llist$)))))
(declare-datatypes () ((A_b_prod_b_prod$ (pair$e (fst$e A_b_prod$) (snd$e B$)))))
(declare-codatatypes () ((A_b_prod_b_prod_llist$ (lNil$h) (lCons$h (lhd$h A_b_prod_b_prod$) (ltl$h A_b_prod_b_prod_llist$)))))
(declare-datatypes () ((A_b_prod_b_prod_list$ (nil$h) (cons$h (hd$h A_b_prod_b_prod$) (tl$h A_b_prod_b_prod_list$)))
  (A_b_prod_a_b_prod_prod$ (pair$f (fst$f A_b_prod$) (snd$f A_b_prod$)))))
(declare-codatatypes () ((A_b_prod_a_b_prod_prod_llist$ (lNil$i) (lCons$i (lhd$i A_b_prod_a_b_prod_prod$) (ltl$i A_b_prod_a_b_prod_prod_llist$)))))
(declare-datatypes () ((A_b_prod_a_b_prod_prod_list$ (nil$i) (cons$i (hd$i A_b_prod_a_b_prod_prod$) (tl$i A_b_prod_a_b_prod_prod_list$)))
  (A_a_prod$ (pair$g (fst$g A$) (snd$g A$)))))
(declare-codatatypes () ((A_a_prod_llist$ (lNil$j) (lCons$j (lhd$j A_a_prod$) (ltl$j A_a_prod_llist$)))))
(declare-datatypes () ((A_a_prod_list$ (nil$j) (cons$j (hd$j A_a_prod$) (tl$j A_a_prod_list$)))
  (B_b_b_prod_prod$ (pair$h (fst$h B$) (snd$h B_b_prod$)))))
(declare-codatatypes () ((B_b_b_prod_prod_llist$ (lNil$k) (lCons$k (lhd$k B_b_b_prod_prod$) (ltl$k B_b_b_prod_prod_llist$)))))
(declare-datatypes () ((B_b_b_prod_prod_list$ (nil$k) (cons$k (hd$k B_b_b_prod_prod$) (tl$k B_b_b_prod_prod_list$)))
  (B_b_a_prod_prod$ (pair$i (fst$i B$) (snd$i B_a_prod$)))))
(declare-codatatypes () ((B_b_a_prod_prod_llist$ (lNil$l) (lCons$l (lhd$l B_b_a_prod_prod$) (ltl$l B_b_a_prod_prod_llist$)))))
(declare-datatypes () ((B_b_a_prod_prod_list$ (nil$l) (cons$l (hd$l B_b_a_prod_prod$) (tl$l B_b_a_prod_prod_list$)))
  (Nat_a_prod$ (pair$j (fst$j Nat$) (snd$j A$)))))
(declare-codatatypes () ((Nat_a_prod_llist$ (lNil$m) (lCons$m (lhd$m Nat_a_prod$) (ltl$m Nat_a_prod_llist$)))))
(declare-datatypes () ((Nat_a_prod_list$ (nil$m) (cons$m (hd$m Nat_a_prod$) (tl$m Nat_a_prod_list$)))
  (Nat_b_prod$ (pair$k (fst$k Nat$) (snd$k B$)))))
(declare-codatatypes () ((Nat_b_prod_llist$ (lNil$n) (lCons$n (lhd$n Nat_b_prod$) (ltl$n Nat_b_prod_llist$)))))
(declare-datatypes () ((Nat_b_prod_list$ (nil$n) (cons$n (hd$n Nat_b_prod$) (tl$n Nat_b_prod_list$)))
  (B_b_prod_a_prod$ (pair$l (fst$l B_b_prod$) (snd$l A$)))))
(declare-codatatypes () ((B_b_prod_a_prod_llist$ (lNil$o) (lCons$o (lhd$o B_b_prod_a_prod$) (ltl$o B_b_prod_a_prod_llist$)))))
(declare-datatypes () ((B_b_prod_a_prod_list$ (nil$o) (cons$o (hd$o B_b_prod_a_prod$) (tl$o B_b_prod_a_prod_list$)))
  (B_a_prod_a_prod$ (pair$m (fst$m B_a_prod$) (snd$m A$)))))
(declare-codatatypes () ((B_a_prod_a_prod_llist$ (lNil$p) (lCons$p (lhd$p B_a_prod_a_prod$) (ltl$p B_a_prod_a_prod_llist$)))))
(declare-datatypes () ((B_a_prod_a_prod_list$ (nil$p) (cons$p (hd$p B_a_prod_a_prod$) (tl$p B_a_prod_a_prod_list$)))))
(declare-fun fa$ () Nat_a_fun$)
(declare-fun uu$ () B_b_fun$)
(declare-fun map$ (Nat_a_fun$ Nat_list$) A_list$)
(declare-fun upt$ (Nat$ Nat$) Nat_list$)
(declare-fun zip$ (A_list$) B_list_a_b_prod_list_fun$)
(declare-fun lzip$ (A_llist$ B_llist$) A_b_prod_llist$)
(declare-fun map$a (Nat_b_fun$ Nat_list$) B_list$)
(declare-fun map$b (B_b_fun$ B_list$) B_list$)
(declare-fun map$c (A_b_fun$ A_list$) B_list$)
(declare-fun map$d (B_a_fun$ B_list$) A_list$)
(declare-fun map$e (A_a_fun$ A_list$) A_list$)
(declare-fun map$f (B_nat_fun$ B_list$) Nat_list$)
(declare-fun map$g (A_nat_fun$ A_list$) Nat_list$)
(declare-fun map$h (Nat_nat_fun$ Nat_list$) Nat_list$)
(declare-fun map$i (A_b_prod_b_fun$ A_b_prod_list$) B_list$)
(declare-fun size$ (B_list$) Nat$)
(declare-fun zero$ () Nat$)
(declare-fun zip$a (B_list$) B_list_b_b_prod_list_fun$)
(declare-fun zip$b (B_list$) A_b_prod_list_b_a_b_prod_prod_list_fun$)
(declare-fun zip$c (A_b_prod_list$) B_list_a_b_prod_b_prod_list_fun$)
(declare-fun zip$d (A_b_prod_list$ A_b_prod_list$) A_b_prod_a_b_prod_prod_list$)
(declare-fun zip$e (B_list$) A_list_b_a_prod_list_fun$)
(declare-fun zip$f (A_list$ A_list$) A_a_prod_list$)
(declare-fun zip$g (B_list$ B_b_prod_list$) B_b_b_prod_prod_list$)
(declare-fun zip$h (B_list$ B_a_prod_list$) B_b_a_prod_prod_list$)
(declare-fun zip$i (A_b_prod_list$) A_list_a_b_prod_a_prod_list_fun$)
(declare-fun zip$j (Nat_list$ A_list$) Nat_a_prod_list$)
(declare-fun zip$k (Nat_list$ B_list$) Nat_b_prod_list$)
(declare-fun zip$l (B_b_prod_list$ A_list$) B_b_prod_a_prod_list$)
(declare-fun zip$m (B_a_prod_list$ A_list$) B_a_prod_a_prod_list$)
(declare-fun lzip$a (B_llist$ B_llist$) B_b_prod_llist$)
(declare-fun lzip$b (B_llist$ A_b_prod_llist$) B_a_b_prod_prod_llist$)
(declare-fun lzip$c (A_b_prod_llist$ B_llist$) A_b_prod_b_prod_llist$)
(declare-fun lzip$d (A_b_prod_llist$ A_b_prod_llist$) A_b_prod_a_b_prod_prod_llist$)
(declare-fun lzip$e (B_llist$ A_llist$) B_a_prod_llist$)
(declare-fun lzip$f (A_llist$ A_llist$) A_a_prod_llist$)
(declare-fun lzip$g (B_llist$ B_b_prod_llist$) B_b_b_prod_prod_llist$)
(declare-fun lzip$h (B_llist$ B_a_prod_llist$) B_b_a_prod_prod_llist$)
(declare-fun lzip$i (A_b_prod_llist$ A_llist$) A_b_prod_a_prod_llist$)
(declare-fun lzip$j (Nat_llist$ A_llist$) Nat_a_prod_llist$)
(declare-fun lzip$k (Nat_llist$ B_llist$) Nat_b_prod_llist$)
(declare-fun lzip$l (B_b_prod_llist$ A_llist$) B_b_prod_a_prod_llist$)
(declare-fun lzip$m (B_a_prod_llist$ A_llist$) B_a_prod_a_prod_llist$)
(declare-fun size$a (A_list$) Nat$)
(declare-fun size$b (A_b_prod_list$) Nat$)
(declare-fun size$c (Nat_list$) Nat$)
(declare-fun size$d (B_b_prod_list$) Nat$)
(declare-fun size$e (B_a_prod_list$) Nat$)
(declare-fun fun_app$ (B_b_fun$ B$) B$)
(declare-fun fun_app$a (B_list_a_b_prod_list_fun$ B_list$) A_b_prod_list$)
(declare-fun fun_app$b (B_list_b_b_prod_list_fun$ B_list$) B_b_prod_list$)
(declare-fun fun_app$c (A_b_prod_list_b_a_b_prod_prod_list_fun$ A_b_prod_list$) B_a_b_prod_prod_list$)
(declare-fun fun_app$d (B_list_a_b_prod_b_prod_list_fun$ B_list$) A_b_prod_b_prod_list$)
(declare-fun fun_app$e (A_list_b_a_prod_list_fun$ A_list$) B_a_prod_list$)
(declare-fun fun_app$f (A_list_a_b_prod_a_prod_list_fun$ A_list$) A_b_prod_a_prod_list$)
(declare-fun llist_of$ (B_list$) B_llist$)
(declare-fun inf_llist$ (Nat_a_fun$) A_llist$)
(declare-fun llist_of$a (A_b_prod_list$) A_b_prod_llist$)
(declare-fun llist_of$b (Nat_list$) Nat_llist$)
(declare-fun llist_of$c (A_b_prod_a_prod_list$) A_b_prod_a_prod_llist$)
(declare-fun llist_of$d (B_a_b_prod_prod_list$) B_a_b_prod_prod_llist$)
(declare-fun llist_of$e (B_b_prod_list$) B_b_prod_llist$)
(declare-fun llist_of$f (B_a_prod_list$) B_a_prod_llist$)
(declare-fun llist_of$g (A_list$) A_llist$)
(declare-fun llist_of$h (A_b_prod_b_prod_list$) A_b_prod_b_prod_llist$)
(declare-fun llist_of$i (A_b_prod_a_b_prod_prod_list$) A_b_prod_a_b_prod_prod_llist$)
(declare-fun llist_of$j (A_a_prod_list$) A_a_prod_llist$)
(declare-fun llist_of$k (B_b_b_prod_prod_list$) B_b_b_prod_prod_llist$)
(declare-fun llist_of$l (B_b_a_prod_prod_list$) B_b_a_prod_prod_llist$)
(declare-fun llist_of$m (Nat_a_prod_list$) Nat_a_prod_llist$)
(declare-fun llist_of$n (Nat_b_prod_list$) Nat_b_prod_llist$)
(declare-fun llist_of$o (B_b_prod_a_prod_list$) B_b_prod_a_prod_llist$)
(declare-fun llist_of$p (B_a_prod_a_prod_list$) B_a_prod_a_prod_llist$)
(declare-fun inf_llist$a (Nat_b_fun$) B_llist$)
(declare-fun inf_llist$b (Nat_a_b_prod_fun$) A_b_prod_llist$)
(declare-fun inf_llist$c (Nat_a_b_prod_a_prod_fun$) A_b_prod_a_prod_llist$)
(declare-fun inf_llist$d (Nat_b_a_b_prod_prod_fun$) B_a_b_prod_prod_llist$)
(declare-fun inf_llist$e (Nat_b_b_prod_fun$) B_b_prod_llist$)
(declare-fun inf_llist$f (Nat_b_a_prod_fun$) B_a_prod_llist$)
(assert (! (forall ((?v0 B$)) (! (= (fun_app$ uu$ ?v0) ?v0) :pattern ((fun_app$ uu$ ?v0)))) :named a0))
(assert (! (not (= (lzip$ (inf_llist$ fa$) (llist_of$ nil$)) (llist_of$a (fun_app$a (zip$ (map$ fa$ (upt$ zero$ (size$ nil$)))) nil$)))) :named a1))
(assert (! (forall ((?v0 Nat_list$) (?v1 Nat_list$)) (= (= (llist_of$b ?v0) (llist_of$b ?v1)) (= ?v0 ?v1))) :named a2))
(assert (! (forall ((?v0 A_b_prod_a_prod_list$) (?v1 A_b_prod_a_prod_list$)) (= (= (llist_of$c ?v0) (llist_of$c ?v1)) (= ?v0 ?v1))) :named a3))
(assert (! (forall ((?v0 B_a_b_prod_prod_list$) (?v1 B_a_b_prod_prod_list$)) (= (= (llist_of$d ?v0) (llist_of$d ?v1)) (= ?v0 ?v1))) :named a4))
(assert (! (forall ((?v0 B_b_prod_list$) (?v1 B_b_prod_list$)) (= (= (llist_of$e ?v0) (llist_of$e ?v1)) (= ?v0 ?v1))) :named a5))
(assert (! (forall ((?v0 B_a_prod_list$) (?v1 B_a_prod_list$)) (= (= (llist_of$f ?v0) (llist_of$f ?v1)) (= ?v0 ?v1))) :named a6))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (= (= (llist_of$g ?v0) (llist_of$g ?v1)) (= ?v0 ?v1))) :named a7))
(assert (! (forall ((?v0 B_list$) (?v1 B_list$)) (= (= (llist_of$ ?v0) (llist_of$ ?v1)) (= ?v0 ?v1))) :named a8))
(assert (! (forall ((?v0 A_b_prod_list$) (?v1 A_b_prod_list$)) (= (= (llist_of$a ?v0) (llist_of$a ?v1)) (= ?v0 ?v1))) :named a9))
(assert (! (forall ((?v0 Nat_b_fun$) (?v1 Nat_b_fun$)) (= (= (inf_llist$a ?v0) (inf_llist$a ?v1)) (= ?v0 ?v1))) :named a10))
(assert (! (forall ((?v0 Nat_a_b_prod_fun$) (?v1 Nat_a_b_prod_fun$)) (= (= (inf_llist$b ?v0) (inf_llist$b ?v1)) (= ?v0 ?v1))) :named a11))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 Nat_a_fun$)) (= (= (inf_llist$ ?v0) (inf_llist$ ?v1)) (= ?v0 ?v1))) :named a12))
(assert (! (forall ((?v0 A_list$) (?v1 B_list$)) (= (lzip$ (llist_of$g ?v0) (llist_of$ ?v1)) (llist_of$a (fun_app$a (zip$ ?v0) ?v1)))) :named a13))
(assert (! (forall ((?v0 B_list$) (?v1 B_list$)) (= (lzip$a (llist_of$ ?v0) (llist_of$ ?v1)) (llist_of$e (fun_app$b (zip$a ?v0) ?v1)))) :named a14))
(assert (! (forall ((?v0 B_list$) (?v1 A_b_prod_list$)) (= (lzip$b (llist_of$ ?v0) (llist_of$a ?v1)) (llist_of$d (fun_app$c (zip$b ?v0) ?v1)))) :named a15))
(assert (! (forall ((?v0 A_b_prod_list$) (?v1 B_list$)) (= (lzip$c (llist_of$a ?v0) (llist_of$ ?v1)) (llist_of$h (fun_app$d (zip$c ?v0) ?v1)))) :named a16))
(assert (! (forall ((?v0 A_b_prod_list$) (?v1 A_b_prod_list$)) (= (lzip$d (llist_of$a ?v0) (llist_of$a ?v1)) (llist_of$i (zip$d ?v0 ?v1)))) :named a17))
(assert (! (forall ((?v0 B_list$) (?v1 A_list$)) (= (lzip$e (llist_of$ ?v0) (llist_of$g ?v1)) (llist_of$f (fun_app$e (zip$e ?v0) ?v1)))) :named a18))
(assert (! (forall ((?v0 A_list$) (?v1 A_list$)) (= (lzip$f (llist_of$g ?v0) (llist_of$g ?v1)) (llist_of$j (zip$f ?v0 ?v1)))) :named a19))
(assert (! (forall ((?v0 B_list$) (?v1 B_b_prod_list$)) (= (lzip$g (llist_of$ ?v0) (llist_of$e ?v1)) (llist_of$k (zip$g ?v0 ?v1)))) :named a20))
(assert (! (forall ((?v0 B_list$) (?v1 B_a_prod_list$)) (= (lzip$h (llist_of$ ?v0) (llist_of$f ?v1)) (llist_of$l (zip$h ?v0 ?v1)))) :named a21))
(assert (! (forall ((?v0 A_b_prod_list$) (?v1 A_list$)) (= (lzip$i (llist_of$a ?v0) (llist_of$g ?v1)) (llist_of$c (fun_app$f (zip$i ?v0) ?v1)))) :named a22))
(assert (! (forall ((?v0 A_list$) (?v1 Nat_b_fun$)) (= (lzip$ (llist_of$g ?v0) (inf_llist$a ?v1)) (llist_of$a (fun_app$a (zip$ ?v0) (map$a ?v1 (upt$ zero$ (size$a ?v0))))))) :named a23))
(assert (! (forall ((?v0 B_list$) (?v1 Nat_a_fun$)) (= (lzip$e (llist_of$ ?v0) (inf_llist$ ?v1)) (llist_of$f (fun_app$e (zip$e ?v0) (map$ ?v1 (upt$ zero$ (size$ ?v0))))))) :named a24))
(assert (! (forall ((?v0 A_b_prod_list$) (?v1 Nat_a_fun$)) (= (lzip$i (llist_of$a ?v0) (inf_llist$ ?v1)) (llist_of$c (fun_app$f (zip$i ?v0) (map$ ?v1 (upt$ zero$ (size$b ?v0))))))) :named a25))
(assert (! (forall ((?v0 Nat_list$) (?v1 Nat_a_fun$)) (= (lzip$j (llist_of$b ?v0) (inf_llist$ ?v1)) (llist_of$m (zip$j ?v0 (map$ ?v1 (upt$ zero$ (size$c ?v0))))))) :named a26))
(assert (! (forall ((?v0 A_list$) (?v1 Nat_a_fun$)) (= (lzip$f (llist_of$g ?v0) (inf_llist$ ?v1)) (llist_of$j (zip$f ?v0 (map$ ?v1 (upt$ zero$ (size$a ?v0))))))) :named a27))
(assert (! (forall ((?v0 Nat_list$) (?v1 Nat_b_fun$)) (= (lzip$k (llist_of$b ?v0) (inf_llist$a ?v1)) (llist_of$n (zip$k ?v0 (map$a ?v1 (upt$ zero$ (size$c ?v0))))))) :named a28))
(assert (! (forall ((?v0 B_list$) (?v1 Nat_b_fun$)) (= (lzip$a (llist_of$ ?v0) (inf_llist$a ?v1)) (llist_of$e (fun_app$b (zip$a ?v0) (map$a ?v1 (upt$ zero$ (size$ ?v0))))))) :named a29))
(assert (! (forall ((?v0 B_b_prod_list$) (?v1 Nat_a_fun$)) (= (lzip$l (llist_of$e ?v0) (inf_llist$ ?v1)) (llist_of$o (zip$l ?v0 (map$ ?v1 (upt$ zero$ (size$d ?v0))))))) :named a30))
(assert (! (forall ((?v0 B_a_prod_list$) (?v1 Nat_a_fun$)) (= (lzip$m (llist_of$f ?v0) (inf_llist$ ?v1)) (llist_of$p (zip$m ?v0 (map$ ?v1 (upt$ zero$ (size$e ?v0))))))) :named a31))
(assert (! (forall ((?v0 A_b_prod_list$) (?v1 Nat_b_fun$)) (= (lzip$c (llist_of$a ?v0) (inf_llist$a ?v1)) (llist_of$h (fun_app$d (zip$c ?v0) (map$a ?v1 (upt$ zero$ (size$b ?v0))))))) :named a32))
(assert (! (forall ((?v0 A_b_prod_a_prod_llist$)) (=> (and (forall ((?v1 A_b_prod_a_prod_list$)) (=> (= ?v0 (llist_of$c ?v1)) false)) (forall ((?v1 Nat_a_b_prod_a_prod_fun$)) (=> (= ?v0 (inf_llist$c ?v1)) false))) false)) :named a33))
(assert (! (forall ((?v0 B_a_b_prod_prod_llist$)) (=> (and (forall ((?v1 B_a_b_prod_prod_list$)) (=> (= ?v0 (llist_of$d ?v1)) false)) (forall ((?v1 Nat_b_a_b_prod_prod_fun$)) (=> (= ?v0 (inf_llist$d ?v1)) false))) false)) :named a34))
(assert (! (forall ((?v0 B_b_prod_llist$)) (=> (and (forall ((?v1 B_b_prod_list$)) (=> (= ?v0 (llist_of$e ?v1)) false)) (forall ((?v1 Nat_b_b_prod_fun$)) (=> (= ?v0 (inf_llist$e ?v1)) false))) false)) :named a35))
(assert (! (forall ((?v0 B_a_prod_llist$)) (=> (and (forall ((?v1 B_a_prod_list$)) (=> (= ?v0 (llist_of$f ?v1)) false)) (forall ((?v1 Nat_b_a_prod_fun$)) (=> (= ?v0 (inf_llist$f ?v1)) false))) false)) :named a36))
(assert (! (forall ((?v0 B_llist$)) (=> (and (forall ((?v1 B_list$)) (=> (= ?v0 (llist_of$ ?v1)) false)) (forall ((?v1 Nat_b_fun$)) (=> (= ?v0 (inf_llist$a ?v1)) false))) false)) :named a37))
(assert (! (forall ((?v0 A_b_prod_llist$)) (=> (and (forall ((?v1 A_b_prod_list$)) (=> (= ?v0 (llist_of$a ?v1)) false)) (forall ((?v1 Nat_a_b_prod_fun$)) (=> (= ?v0 (inf_llist$b ?v1)) false))) false)) :named a38))
(assert (! (forall ((?v0 A_llist$)) (=> (and (forall ((?v1 A_list$)) (=> (= ?v0 (llist_of$g ?v1)) false)) (forall ((?v1 Nat_a_fun$)) (=> (= ?v0 (inf_llist$ ?v1)) false))) false)) :named a39))
(assert (! (forall ((?v0 A_b_prod_a_prod_list$) (?v1 Nat_a_b_prod_a_prod_fun$)) (not (= (llist_of$c ?v0) (inf_llist$c ?v1)))) :named a40))
(assert (! (forall ((?v0 B_a_b_prod_prod_list$) (?v1 Nat_b_a_b_prod_prod_fun$)) (not (= (llist_of$d ?v0) (inf_llist$d ?v1)))) :named a41))
(assert (! (forall ((?v0 B_b_prod_list$) (?v1 Nat_b_b_prod_fun$)) (not (= (llist_of$e ?v0) (inf_llist$e ?v1)))) :named a42))
(assert (! (forall ((?v0 B_a_prod_list$) (?v1 Nat_b_a_prod_fun$)) (not (= (llist_of$f ?v0) (inf_llist$f ?v1)))) :named a43))
(assert (! (forall ((?v0 B_list$) (?v1 Nat_b_fun$)) (not (= (llist_of$ ?v0) (inf_llist$a ?v1)))) :named a44))
(assert (! (forall ((?v0 A_b_prod_list$) (?v1 Nat_a_b_prod_fun$)) (not (= (llist_of$a ?v0) (inf_llist$b ?v1)))) :named a45))
(assert (! (forall ((?v0 A_list$) (?v1 Nat_a_fun$)) (not (= (llist_of$g ?v0) (inf_llist$ ?v1)))) :named a46))
(assert (! (forall ((?v0 A_b_prod_list$)) (= (= (size$b ?v0) zero$) (= ?v0 nil$a))) :named a47))
(assert (! (forall ((?v0 A_list$)) (= (= (size$a ?v0) zero$) (= ?v0 nil$b))) :named a48))
(assert (! (forall ((?v0 Nat_list$)) (= (= (size$c ?v0) zero$) (= ?v0 nil$c))) :named a49))
(assert (! (forall ((?v0 B_list$)) (= (= (size$ ?v0) zero$) (= ?v0 nil$))) :named a50))
(assert (! (= (size$b nil$a) zero$) :named a51))
(assert (! (= (size$a nil$b) zero$) :named a52))
(assert (! (= (size$c nil$c) zero$) :named a53))
(assert (! (= (size$ nil$) zero$) :named a54))
(assert (! (forall ((?v0 A_b_prod_list$)) (! (= (fun_app$c (zip$b nil$) ?v0) nil$e) :pattern ((fun_app$c (zip$b nil$) ?v0)))) :named a55))
(assert (! (forall ((?v0 B_list$)) (! (= (fun_app$b (zip$a nil$) ?v0) nil$f) :pattern ((fun_app$b (zip$a nil$) ?v0)))) :named a56))
(assert (! (forall ((?v0 A_list$)) (! (= (fun_app$e (zip$e nil$) ?v0) nil$g) :pattern ((fun_app$e (zip$e nil$) ?v0)))) :named a57))
(assert (! (forall ((?v0 B_list$)) (! (= (fun_app$d (zip$c nil$a) ?v0) nil$h) :pattern ((fun_app$d (zip$c nil$a) ?v0)))) :named a58))
(assert (! (forall ((?v0 A_list$)) (! (= (fun_app$f (zip$i nil$a) ?v0) nil$d) :pattern ((fun_app$f (zip$i nil$a) ?v0)))) :named a59))
(assert (! (forall ((?v0 B_list$)) (! (= (fun_app$a (zip$ nil$b) ?v0) nil$a) :pattern ((fun_app$a (zip$ nil$b) ?v0)))) :named a60))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 Nat_list$)) (= (size$a (map$ ?v0 ?v1)) (size$c ?v1))) :named a61))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_list$)) (= (size$ (map$b ?v0 ?v1)) (size$ ?v1))) :named a62))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_list$)) (= (size$ (map$c ?v0 ?v1)) (size$a ?v1))) :named a63))
(assert (! (forall ((?v0 Nat_b_fun$) (?v1 Nat_list$)) (= (size$ (map$a ?v0 ?v1)) (size$c ?v1))) :named a64))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_list$)) (= (size$a (map$d ?v0 ?v1)) (size$ ?v1))) :named a65))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_list$)) (= (size$a (map$e ?v0 ?v1)) (size$a ?v1))) :named a66))
(assert (! (forall ((?v0 B_nat_fun$) (?v1 B_list$)) (= (size$c (map$f ?v0 ?v1)) (size$ ?v1))) :named a67))
(assert (! (forall ((?v0 A_nat_fun$) (?v1 A_list$)) (= (size$c (map$g ?v0 ?v1)) (size$a ?v1))) :named a68))
(assert (! (forall ((?v0 Nat_nat_fun$) (?v1 Nat_list$)) (= (size$c (map$h ?v0 ?v1)) (size$c ?v1))) :named a69))
(assert (! (forall ((?v0 A_b_prod_b_fun$) (?v1 A_b_prod_list$)) (= (size$ (map$i ?v0 ?v1)) (size$b ?v1))) :named a70))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_list$)) (= (= (map$b ?v0 ?v1) nil$) (= ?v1 nil$))) :named a71))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 Nat_list$)) (= (= (map$ ?v0 ?v1) nil$b) (= ?v1 nil$c))) :named a72))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_list$)) (= (= (map$c ?v0 ?v1) nil$) (= ?v1 nil$b))) :named a73))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_list$)) (= (= (map$e ?v0 ?v1) nil$b) (= ?v1 nil$b))) :named a74))
(assert (! (forall ((?v0 B_nat_fun$) (?v1 B_list$)) (= (= (map$f ?v0 ?v1) nil$c) (= ?v1 nil$))) :named a75))
(assert (! (forall ((?v0 A_nat_fun$) (?v1 A_list$)) (= (= (map$g ?v0 ?v1) nil$c) (= ?v1 nil$b))) :named a76))
(assert (! (forall ((?v0 Nat_nat_fun$) (?v1 Nat_list$)) (= (= (map$h ?v0 ?v1) nil$c) (= ?v1 nil$c))) :named a77))
(assert (! (forall ((?v0 Nat_b_fun$) (?v1 Nat_list$)) (= (= (map$a ?v0 ?v1) nil$) (= ?v1 nil$c))) :named a78))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_list$)) (= (= (map$d ?v0 ?v1) nil$b) (= ?v1 nil$))) :named a79))
(assert (! (forall ((?v0 A_b_prod_b_fun$) (?v1 A_b_prod_list$)) (= (= (map$i ?v0 ?v1) nil$) (= ?v1 nil$a))) :named a80))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_list$)) (= (= (map$b ?v0 ?v1) nil$) (= ?v1 nil$))) :named a81))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 Nat_list$)) (= (= (map$ ?v0 ?v1) nil$b) (= ?v1 nil$c))) :named a82))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_list$)) (= (= (map$c ?v0 ?v1) nil$) (= ?v1 nil$b))) :named a83))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_list$)) (= (= (map$e ?v0 ?v1) nil$b) (= ?v1 nil$b))) :named a84))
(assert (! (forall ((?v0 B_nat_fun$) (?v1 B_list$)) (= (= (map$f ?v0 ?v1) nil$c) (= ?v1 nil$))) :named a85))
(assert (! (forall ((?v0 A_nat_fun$) (?v1 A_list$)) (= (= (map$g ?v0 ?v1) nil$c) (= ?v1 nil$b))) :named a86))
(assert (! (forall ((?v0 Nat_nat_fun$) (?v1 Nat_list$)) (= (= (map$h ?v0 ?v1) nil$c) (= ?v1 nil$c))) :named a87))
(assert (! (forall ((?v0 Nat_b_fun$) (?v1 Nat_list$)) (= (= (map$a ?v0 ?v1) nil$) (= ?v1 nil$c))) :named a88))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_list$)) (= (= (map$d ?v0 ?v1) nil$b) (= ?v1 nil$))) :named a89))
(assert (! (forall ((?v0 A_b_prod_b_fun$) (?v1 A_b_prod_list$)) (= (= (map$i ?v0 ?v1) nil$) (= ?v1 nil$a))) :named a90))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_list$)) (= (= nil$ (map$b ?v0 ?v1)) (= ?v1 nil$))) :named a91))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 Nat_list$)) (= (= nil$b (map$ ?v0 ?v1)) (= ?v1 nil$c))) :named a92))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_list$)) (= (= nil$ (map$c ?v0 ?v1)) (= ?v1 nil$b))) :named a93))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_list$)) (= (= nil$b (map$e ?v0 ?v1)) (= ?v1 nil$b))) :named a94))
(assert (! (forall ((?v0 B_nat_fun$) (?v1 B_list$)) (= (= nil$c (map$f ?v0 ?v1)) (= ?v1 nil$))) :named a95))
(assert (! (forall ((?v0 A_nat_fun$) (?v1 A_list$)) (= (= nil$c (map$g ?v0 ?v1)) (= ?v1 nil$b))) :named a96))
(assert (! (forall ((?v0 Nat_nat_fun$) (?v1 Nat_list$)) (= (= nil$c (map$h ?v0 ?v1)) (= ?v1 nil$c))) :named a97))
(assert (! (forall ((?v0 Nat_b_fun$) (?v1 Nat_list$)) (= (= nil$ (map$a ?v0 ?v1)) (= ?v1 nil$c))) :named a98))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_list$)) (= (= nil$b (map$d ?v0 ?v1)) (= ?v1 nil$))) :named a99))
(assert (! (forall ((?v0 A_b_prod_b_fun$) (?v1 A_b_prod_list$)) (= (= nil$ (map$i ?v0 ?v1)) (= ?v1 nil$a))) :named a100))
(assert (! (forall ((?v0 B_list$)) (= (map$b uu$ ?v0) ?v0)) :named a101))
(assert (! (forall ((?v0 A_b_prod_list$)) (! (= (fun_app$d (zip$c ?v0) nil$) nil$h) :pattern ((zip$c ?v0)))) :named a102))
(assert (! (forall ((?v0 B_list$)) (! (= (fun_app$b (zip$a ?v0) nil$) nil$f) :pattern ((zip$a ?v0)))) :named a103))
(assert (! (forall ((?v0 A_b_prod_list$)) (! (= (fun_app$f (zip$i ?v0) nil$b) nil$d) :pattern ((zip$i ?v0)))) :named a104))
(assert (! (forall ((?v0 B_list$)) (! (= (fun_app$e (zip$e ?v0) nil$b) nil$g) :pattern ((zip$e ?v0)))) :named a105))
(assert (! (forall ((?v0 B_list$)) (! (= (fun_app$c (zip$b ?v0) nil$a) nil$e) :pattern ((zip$b ?v0)))) :named a106))
(assert (! (forall ((?v0 A_list$)) (! (= (fun_app$a (zip$ ?v0) nil$) nil$a) :pattern ((zip$ ?v0)))) :named a107))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 Nat_list$) (?v2 Nat_a_fun$) (?v3 Nat_list$)) (=> (= (map$ ?v0 ?v1) (map$ ?v2 ?v3)) (= (size$c ?v1) (size$c ?v3)))) :named a108))
(assert (! (forall ((?v0 Nat_a_fun$) (?v1 Nat_list$) (?v2 B_a_fun$) (?v3 B_list$)) (=> (= (map$ ?v0 ?v1) (map$d ?v2 ?v3)) (= (size$c ?v1) (size$ ?v3)))) :named a109))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_list$) (?v2 Nat_a_fun$) (?v3 Nat_list$)) (=> (= (map$d ?v0 ?v1) (map$ ?v2 ?v3)) (= (size$ ?v1) (size$c ?v3)))) :named a110))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_list$) (?v2 B_b_fun$) (?v3 B_list$)) (=> (= (map$b ?v0 ?v1) (map$b ?v2 ?v3)) (= (size$ ?v1) (size$ ?v3)))) :named a111))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_list$) (?v2 B_a_fun$) (?v3 B_list$)) (=> (= (map$d ?v0 ?v1) (map$d ?v2 ?v3)) (= (size$ ?v1) (size$ ?v3)))) :named a112))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_list$) (?v2 A_b_fun$) (?v3 A_list$)) (=> (= (map$b ?v0 ?v1) (map$c ?v2 ?v3)) (= (size$ ?v1) (size$a ?v3)))) :named a113))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_list$) (?v2 A_a_fun$) (?v3 A_list$)) (=> (= (map$d ?v0 ?v1) (map$e ?v2 ?v3)) (= (size$ ?v1) (size$a ?v3)))) :named a114))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_list$) (?v2 Nat_b_fun$) (?v3 Nat_list$)) (=> (= (map$b ?v0 ?v1) (map$a ?v2 ?v3)) (= (size$ ?v1) (size$c ?v3)))) :named a115))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_list$) (?v2 B_b_fun$) (?v3 B_list$)) (=> (= (map$c ?v0 ?v1) (map$b ?v2 ?v3)) (= (size$a ?v1) (size$ ?v3)))) :named a116))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_list$) (?v2 B_a_fun$) (?v3 B_list$)) (=> (= (map$e ?v0 ?v1) (map$d ?v2 ?v3)) (= (size$a ?v1) (size$ ?v3)))) :named a117))
(check-sat)
;(get-unsat-core)
