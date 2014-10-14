Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.

Notation vec := Vector.t.
Notation LB := (list bool).
Notation ll := List.length.
Notation Bnil := (nil (A := bool)).
Notation VecLB := (vec LB).

Notation Byte := (vec bool 8).

Notation LByte := (list Byte).

Notation Vnth := Vector.nth.

Notation Vnil := Vector.nil.
Notation Vcons := Vector.cons.
Notation Vmap := Vector.map.

Notation fin_rect2 := Fin.rect2.
Notation FS_inj := Fin.FS_inj.
Notation fin := Fin.t.
Notation FinLR := Fin.L_R.
Notation FinFS := Fin.FS.
Notation FinF1 := Fin.F1.