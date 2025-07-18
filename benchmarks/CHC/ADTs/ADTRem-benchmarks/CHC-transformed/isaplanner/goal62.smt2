; Automatically generated by map2smt

(set-logic HORN)




(declare-fun new8 (Int Int) Bool)
(declare-fun new5 (Int Int) Bool)
(declare-fun new42 (Int Int) Bool)
(declare-fun new41 (Int Int) Bool)
(declare-fun new40 (Int Int) Bool)
(declare-fun new4 (Int Int Int Int) Bool)
(declare-fun new39 (Int Int) Bool)
(declare-fun new35 (Int Int) Bool)
(declare-fun new31 (Int Int) Bool)
(declare-fun new3 (Int Int Int Int) Bool)
(declare-fun new27 (Int Int Int Int Int) Bool)
(declare-fun new26 (Int Int Int Int Int) Bool)
(declare-fun new24 (Int Int) Bool)
(declare-fun new23 (Int Int) Bool)
(declare-fun new2 (Int Int) Bool)
(declare-fun new19 (Int Int Int Int Int) Bool)
(declare-fun new18 (Int Int Int Int Int) Bool)
(declare-fun new16 (Int Int) Bool)
(declare-fun new15 (Int Int) Bool)
(declare-fun new1 (Int Int) Bool)
(declare-fun diff_new7 (Int Int Int) Bool)
(declare-fun diff_new37 () Bool)
(declare-fun diff_new33 () Bool)
(declare-fun diff_new14 (Int Int Int Int Int Int) Bool)
(declare-fun diff_new12 (Int Int Int Int Int Int) Bool)
(declare-fun diff_new10 (Int Int Int) Bool)
(declare-fun ff () Bool)

(assert
  (forall ( (A Int) )
    (new42 A A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new42 C B)
      (new42 A B)
    )
  )
)
(assert
  (forall ( (A Int) )
    (new41 A A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new41 C B)
      (new41 A B)
    )
  )
)
(assert
  (forall ( (A Int) )
    (new40 A A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new40 C B)
      (new40 A B)
    )
  )
)
(assert
  (forall ( (A Int) )
    (new39 A A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new39 C B)
      (new39 A B)
    )
  )
)
(assert
    diff_new37
)
(assert
  (forall ( (A Int) )
    (new35 A A)
  )
)
(assert
    diff_new33
)
(assert
  (forall ( (A Int) )
    (new31 A A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new39 B C)
      (new27 A B C B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new40 B C)
      (new26 A B C B C)
    )
  )
)
(assert
  (forall ( (A Int) )
    (new24 A A)
  )
)
(assert
  (forall ( (A Int) )
    (new23 A A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new41 B C)
      (new19 A B C B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new42 B C)
      (new18 A B C B C)
    )
  )
)
(assert
  (forall ( (A Int) )
    (new16 A A)
  )
)
(assert
  (forall ( (A Int) )
    (new15 A A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (new15 C D)
        (new16 B E)
      )
      (diff_new14 A A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (new15 C D)
        (new18 F G E G B)
      )
      (diff_new14 A A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (new19 F G D G C)
        (new16 B E)
      )
      (diff_new14 A A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) )
    (=>
      (and
        (new19 F G D G C)
        (new18 H I E I B)
      )
      (diff_new14 A A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (new23 C D)
        (new24 B E)
      )
      (diff_new12 A A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (new23 C D)
        (new26 F G E G B)
      )
      (diff_new12 A A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (new27 F G D G C)
        (new24 B E)
      )
      (diff_new12 A A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) )
    (=>
      (and
        (new27 F G D G C)
        (new26 H I E I B)
      )
      (diff_new12 A A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new31 A C)
      (diff_new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        diff_new33
        (diff_new10 A D C)
      )
      (diff_new10 A B C)
    )
  )
)
(assert
  (forall ( (A Int) )
    (new8 A A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new8 C B)
      (new8 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new35 A C)
      (diff_new7 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        diff_new37
        (diff_new7 A D C)
      )
      (diff_new7 A B C)
    )
  )
)
(assert
  (forall ( (A Int) )
    (new5 A A)
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (new5 C B)
      (new5 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (new5 A B)
      (new4 A B A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (diff_new7 D E B)
        (new4 A D A C)
      )
      (new4 A B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (new8 A B)
      (new3 A B A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (diff_new10 D E B)
        (new3 A D A C)
      )
      (new3 A B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and
        (diff_new12 C D E F B A)
        (new2 E F)
      )
      (new2 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and
        (diff_new14 C D E F B A)
        (new1 E F)
      )
      (new1 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (>= (- A B) 1)
        (new1 B A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (<= (- A B) (- 1))
        (new2 B A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (>= (- A B) 1)
        (new3 C B C A)
      )
      ff
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (<= (- A B) (- 1))
        (new4 C B C A)
      )
      ff
    )
  )
)

(assert (not ff))
(check-sat)
