; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 630
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort Nat$ 0)
(declare-sort Rat$ 0)
(declare-sort Nat_rat_fun$ 0)
(declare-sort Rat_rat_fun$ 0)
(declare-sort Nat_nat_rat_fun_fun$ 0)
(declare-sort Nat_nat_nat_prod_fun$ 0)
(declare-sort Nat_nat_prod_rat_fun$ 0)
(declare-sort Rat_nat_nat_prod_fun$ 0)
(declare-sort Nat_nat_nat_nat_prod_fun_fun$ 0)
(declare-sort Nat_nat_prod_nat_nat_prod_fun$ 0)
(declare-datatypes () ((Dir$ (l$) (r$))
  (Nat_nat_prod$ (pair$ (fst$ Nat$) (snd$ Nat$)))
  (Nat_nat_prod_nat_nat_prod_prod$ (pair$a (fst$a Nat_nat_prod$) (snd$a Nat_nat_prod$)))))
(declare-fun d$ () Dir$)
(declare-fun m$ () Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun d$a () Dir$)
(declare-fun pm$ () Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun uu$ () Nat_nat_rat_fun_fun$)
(declare-fun det$ (Nat_nat_prod_nat_nat_prod_prod$) Nat$)
(declare-fun one$ () Nat$)
(declare-fun pm$a () Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun uua$ (Nat_nat_nat_nat_prod_fun_fun$ Nat_nat_nat_nat_prod_fun_fun$) Nat_nat_nat_nat_prod_fun_fun$)
(declare-fun uub$ (Nat_nat_rat_fun_fun$ Nat_nat_nat_nat_prod_fun_fun$) Nat_nat_rat_fun_fun$)
(declare-fun uuc$ (Rat_nat_nat_prod_fun$ Nat_nat_rat_fun_fun$) Nat_nat_nat_nat_prod_fun_fun$)
(declare-fun uud$ (Nat_nat_prod_rat_fun$ Nat_nat_nat_nat_prod_fun_fun$) Nat_nat_rat_fun_fun$)
(declare-fun uue$ (Nat_nat_prod_nat_nat_prod_fun$ Nat_nat_nat_nat_prod_fun_fun$) Nat_nat_nat_nat_prod_fun_fun$)
(declare-fun uuf$ (Rat_rat_fun$ Nat_nat_rat_fun_fun$) Nat_nat_rat_fun_fun$)
(declare-fun less$ (Rat$ Rat$) Bool)
(declare-fun fract$ (Int Int) Rat$)
(declare-fun lLmat$ () Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun less$a (Nat$ Nat$) Bool)
(declare-fun uRmat$ () Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun mulmat$ (Nat_nat_prod_nat_nat_prod_prod$ Nat_nat_prod_nat_nat_prod_prod$) Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun of_nat$ (Nat$) Int)
(declare-fun fun_app$ (Nat_rat_fun$ Nat$) Rat$)
(declare-fun mediant$ (Nat_nat_prod_nat_nat_prod_prod$) Nat_nat_prod$)
(declare-fun of_nat$a (Nat$) Nat$)
(declare-fun of_nat$b (Nat$) Rat$)
(declare-fun case_dir$ (Bool Bool Dir$) Bool)
(declare-fun fun_app$a (Nat_nat_rat_fun_fun$ Nat$) Nat_rat_fun$)
(declare-fun fun_app$b (Nat_nat_nat_prod_fun$ Nat$) Nat_nat_prod$)
(declare-fun fun_app$c (Nat_nat_nat_nat_prod_fun_fun$ Nat$) Nat_nat_nat_prod_fun$)
(declare-fun fun_app$d (Nat_nat_prod_nat_nat_prod_fun$ Nat_nat_prod$) Nat_nat_prod$)
(declare-fun fun_app$e (Nat_nat_prod_rat_fun$ Nat_nat_prod$) Rat$)
(declare-fun fun_app$f (Rat_nat_nat_prod_fun$ Rat$) Nat_nat_prod$)
(declare-fun fun_app$g (Rat_rat_fun$ Rat$) Rat$)
(declare-fun case_dir$a (Nat_nat_prod_nat_nat_prod_prod$ Nat_nat_prod_nat_nat_prod_prod$ Dir$) Nat_nat_prod_nat_nat_prod_prod$)
(declare-fun case_prod$ (Nat_nat_nat_nat_prod_fun_fun$) Nat_nat_prod_nat_nat_prod_fun$)
(declare-fun case_prod$a (Nat_nat_rat_fun_fun$) Nat_nat_prod_rat_fun$)
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (! (= (fun_app$ (fun_app$a uu$ ?v0) ?v1) (fract$ (of_nat$ ?v0) (of_nat$ ?v1))) :pattern ((fun_app$ (fun_app$a uu$ ?v0) ?v1)))) :named a0))
(assert (! (forall ((?v0 Nat_nat_nat_nat_prod_fun_fun$) (?v1 Nat_nat_nat_nat_prod_fun_fun$) (?v2 Nat$) (?v3 Nat$)) (! (= (fun_app$b (fun_app$c (uua$ ?v0 ?v1) ?v2) ?v3) (fun_app$d (case_prod$ ?v0) (fun_app$b (fun_app$c ?v1 ?v2) ?v3))) :pattern ((fun_app$b (fun_app$c (uua$ ?v0 ?v1) ?v2) ?v3)))) :named a1))
(assert (! (forall ((?v0 Nat_nat_rat_fun_fun$) (?v1 Nat_nat_nat_nat_prod_fun_fun$) (?v2 Nat$) (?v3 Nat$)) (! (= (fun_app$ (fun_app$a (uub$ ?v0 ?v1) ?v2) ?v3) (fun_app$e (case_prod$a ?v0) (fun_app$b (fun_app$c ?v1 ?v2) ?v3))) :pattern ((fun_app$ (fun_app$a (uub$ ?v0 ?v1) ?v2) ?v3)))) :named a2))
(assert (! (forall ((?v0 Nat_nat_prod_nat_nat_prod_fun$) (?v1 Nat_nat_nat_nat_prod_fun_fun$) (?v2 Nat$) (?v3 Nat$)) (! (= (fun_app$b (fun_app$c (uue$ ?v0 ?v1) ?v2) ?v3) (fun_app$d ?v0 (fun_app$b (fun_app$c ?v1 ?v2) ?v3))) :pattern ((fun_app$b (fun_app$c (uue$ ?v0 ?v1) ?v2) ?v3)))) :named a3))
(assert (! (forall ((?v0 Nat_nat_prod_rat_fun$) (?v1 Nat_nat_nat_nat_prod_fun_fun$) (?v2 Nat$) (?v3 Nat$)) (! (= (fun_app$ (fun_app$a (uud$ ?v0 ?v1) ?v2) ?v3) (fun_app$e ?v0 (fun_app$b (fun_app$c ?v1 ?v2) ?v3))) :pattern ((fun_app$ (fun_app$a (uud$ ?v0 ?v1) ?v2) ?v3)))) :named a4))
(assert (! (forall ((?v0 Rat_nat_nat_prod_fun$) (?v1 Nat_nat_rat_fun_fun$) (?v2 Nat$) (?v3 Nat$)) (! (= (fun_app$b (fun_app$c (uuc$ ?v0 ?v1) ?v2) ?v3) (fun_app$f ?v0 (fun_app$ (fun_app$a ?v1 ?v2) ?v3))) :pattern ((fun_app$b (fun_app$c (uuc$ ?v0 ?v1) ?v2) ?v3)))) :named a5))
(assert (! (forall ((?v0 Rat_rat_fun$) (?v1 Nat_nat_rat_fun_fun$) (?v2 Nat$) (?v3 Nat$)) (! (= (fun_app$ (fun_app$a (uuf$ ?v0 ?v1) ?v2) ?v3) (fun_app$g ?v0 (fun_app$ (fun_app$a ?v1 ?v2) ?v3))) :pattern ((fun_app$ (fun_app$a (uuf$ ?v0 ?v1) ?v2) ?v3)))) :named a6))
(assert (! (not (case_dir$ (less$ (fun_app$e (case_prod$a uu$) (mediant$ pm$)) (fun_app$e (case_prod$a uu$) (mediant$ m$))) (less$ (fun_app$e (case_prod$a uu$) (mediant$ m$)) (fun_app$e (case_prod$a uu$) (mediant$ pm$))) d$)) :named a7))
(assert (! (not (= d$ d$a)) :named a8))
(assert (! (= (mulmat$ (case_dir$a (mulmat$ m$ lLmat$) (mulmat$ m$ uRmat$) d$) pm$a) pm$) :named a9))
(assert (! (= (det$ m$) one$) :named a10))
(assert (! (= (det$ pm$) one$) :named a11))
(assert (! (=> (forall ((?v0 Nat_nat_prod_nat_nat_prod_prod$)) (=> (and (= (mulmat$ (case_dir$a (mulmat$ m$ lLmat$) (mulmat$ m$ uRmat$) d$) ?v0) pm$) (= (det$ ?v0) one$)) false)) false) :named a12))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (less$a (of_nat$a ?v0) (of_nat$a ?v1)) (less$a ?v0 ?v1))) :named a13))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (less$ (of_nat$b ?v0) (of_nat$b ?v1)) (less$a ?v0 ?v1))) :named a14))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (< (of_nat$ ?v0) (of_nat$ ?v1)) (less$a ?v0 ?v1))) :named a15))
(assert (! (forall ((?v0 Nat_nat_prod_nat_nat_prod_prod$) (?v1 Nat_nat_prod_nat_nat_prod_prod$) (?v2 Nat_nat_prod_nat_nat_prod_prod$)) (= (mulmat$ (mulmat$ ?v0 ?v1) ?v2) (mulmat$ ?v0 (mulmat$ ?v1 ?v2)))) :named a16))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (of_nat$a ?v0) (of_nat$a ?v1)) (= ?v0 ?v1))) :named a17))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (of_nat$b ?v0) (of_nat$b ?v1)) (= ?v0 ?v1))) :named a18))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (of_nat$ ?v0) (of_nat$ ?v1)) (= ?v0 ?v1))) :named a19))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (less$a (of_nat$a ?v0) (of_nat$a ?v1)) (less$a ?v0 ?v1))) :named a20))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (less$ (of_nat$b ?v0) (of_nat$b ?v1)) (less$a ?v0 ?v1))) :named a21))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (< (of_nat$ ?v0) (of_nat$ ?v1)) (less$a ?v0 ?v1))) :named a22))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (less$a ?v0 ?v1) (less$a (of_nat$a ?v0) (of_nat$a ?v1)))) :named a23))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (less$a ?v0 ?v1) (less$ (of_nat$b ?v0) (of_nat$b ?v1)))) :named a24))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (less$a ?v0 ?v1) (< (of_nat$ ?v0) (of_nat$ ?v1)))) :named a25))
(assert (! (forall ((?v0 Rat$)) (exists ((?v1 Nat$)) (less$ ?v0 (of_nat$b ?v1)))) :named a26))
(assert (! (forall ((?v0 Nat_nat_nat_nat_prod_fun_fun$) (?v1 Nat_nat_nat_nat_prod_fun_fun$) (?v2 Nat_nat_prod$)) (= (fun_app$d (case_prod$ ?v0) (fun_app$d (case_prod$ ?v1) ?v2)) (fun_app$d (case_prod$ (uua$ ?v0 ?v1)) ?v2))) :named a27))
(assert (! (forall ((?v0 Nat_nat_rat_fun_fun$) (?v1 Nat_nat_nat_nat_prod_fun_fun$) (?v2 Nat_nat_prod$)) (= (fun_app$e (case_prod$a ?v0) (fun_app$d (case_prod$ ?v1) ?v2)) (fun_app$e (case_prod$a (uub$ ?v0 ?v1)) ?v2))) :named a28))
(assert (! (forall ((?v0 Rat_nat_nat_prod_fun$) (?v1 Nat_nat_rat_fun_fun$) (?v2 Nat_nat_prod$)) (= (fun_app$f ?v0 (fun_app$e (case_prod$a ?v1) ?v2)) (fun_app$d (case_prod$ (uuc$ ?v0 ?v1)) ?v2))) :named a29))
(assert (! (forall ((?v0 Nat_nat_prod_rat_fun$) (?v1 Nat_nat_nat_nat_prod_fun_fun$) (?v2 Nat_nat_prod$)) (= (fun_app$e ?v0 (fun_app$d (case_prod$ ?v1) ?v2)) (fun_app$e (case_prod$a (uud$ ?v0 ?v1)) ?v2))) :named a30))
(assert (! (forall ((?v0 Nat_nat_prod_nat_nat_prod_fun$) (?v1 Nat_nat_nat_nat_prod_fun_fun$) (?v2 Nat_nat_prod$)) (= (fun_app$d ?v0 (fun_app$d (case_prod$ ?v1) ?v2)) (fun_app$d (case_prod$ (uue$ ?v0 ?v1)) ?v2))) :named a31))
(assert (! (forall ((?v0 Rat_rat_fun$) (?v1 Nat_nat_rat_fun_fun$) (?v2 Nat_nat_prod$)) (= (fun_app$g ?v0 (fun_app$e (case_prod$a ?v1) ?v2)) (fun_app$e (case_prod$a (uuf$ ?v0 ?v1)) ?v2))) :named a32))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (of_nat$ ?v0) (of_nat$ ?v1)) (= ?v0 ?v1))) :named a33))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (of_nat$ ?v0) (of_nat$ ?v1)) (= ?v0 ?v1))) :named a34))
(assert (! (= (det$ pm$a) one$) :named a35))
(check-sat)
;(get-unsat-core)
